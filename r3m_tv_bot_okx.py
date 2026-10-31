"""
zetro(ath.zetro.io) 신호 자동매매 봇 (OKX)

동작 방식
---------
ath.zetro.io 의 신호 API(/api/pub/v1/signals)를 5초마다 조회해서
새 신호가 뜨면 OKX에서 바로 진입합니다. 청산은 진입할 때 같이 걸어두는
익절(TP)/손절(SL)로 자동 처리됩니다.

안전장치
--------
- 봇을 켤 때 이미 떠 있던 신호로는 진입하지 않음
- 3분 넘게 지난 신호는 진입하지 않음
- 같은 신호로 두 번 진입하지 않음 (재시작해도 기억)
- ZETRO_API_KEY 가 없으면 신호 조회만 꺼진 채로 봇은 정상 실행

중요한 전제
------------
OKX 계정의 포지션 모드가 반드시 "단방향(one-way/net)" 모드여야 합니다.

필요 패키지
------------
pip install requests

환경 변수 (Railway Variables)
-----------------------------
OKX_API_KEY, OKX_API_SECRET, OKX_API_PASSPHRASE : OKX API 키 (Trade 권한 필요)
ZETRO_API_KEY                                    : zetro API 키 (ztk_로 시작)
TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID             : (선택) 텔레그램 알림용
"""

from __future__ import annotations

import base64
import hmac
import hashlib
import json
import logging
import math
import os
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Optional

import requests

# ----------------------------------------------------------------------------
# 진입 설정 — 여기를 원하는 값으로 바꾸세요
# ----------------------------------------------------------------------------

# 포지션 규모 기준 (실제 증거금 = 포지션 규모 / 레버리지)
POSITION_NOTIONAL_USDT = 500.0   # 증거금 100 USDT × 5배
LEVERAGE = 5
TAKE_PROFIT_PCT = 0.06   # 증거금 대비 +6% 익절 (가격 +1.2%)
STOP_LOSS_PCT = 0.08     # 증거금 대비 -8% 손절 (가격 -1.6%)

# 종목별로 포지션 규모를 다르게 하고 싶을 때만 추가
SYMBOL_NOTIONAL_OVERRIDE = {
    # "BTC-USDT-SWAP": 1000.0,
}

MAX_STACK_POSITIONS = 1   # 같은 종목에 이미 포지션이 있으면 추가 진입 안 함
SYMBOL_MAX_STACK_OVERRIDE = {}
MAX_DAILY_SL_COUNT = 10   # 하루(한국시간 0시 기준) 손절 10회가 되면 그날은 신규 진입 중지

# ----------------------------------------------------------------------------
# zetro 신호 설정
# ----------------------------------------------------------------------------

ZETRO_API_KEY = os.environ.get("ZETRO_API_KEY", "")
ZETRO_SIGNALS_URL = "https://ath.zetro.io/api/pub/v1/signals"
ZETRO_POLL_SECONDS = 5            # 5초마다 조회 (분당 12회, 한도 60회)
ZETRO_MAX_SIGNAL_AGE_SEC = 180    # 기본: 3분보다 오래된 신호는 진입 안 함

# 진입할 신호 규칙
#   keywords   : 신호 종류(type) 이름에 이 단어가 들어가면 해당 신호로 인식 (대소문자 무시)
#   symbols    : 진입 허용 종목 (None이면 전 종목)
#   max_age_sec: 신호가 뜬 뒤 이 시간(초) 안에만 진입
ZETRO_SIGNAL_RULES = {
    "아트로포스": {
        "keywords": ["atropos", "아트로포스"],
        "symbols": None,            # BTC 포함 전 종목
        "max_age_sec": 60,          # 뜬 지 1분 이내만
    },
    "스퀘어": {
        "keywords": ["square", "스퀘어"],
        "symbols": {"BTCUSDT"},     # BTC만
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
    },
}

# ----------------------------------------------------------------------------
# 기타
# ----------------------------------------------------------------------------

PORT = int(os.environ.get("PORT", 8789))   # Railway 상태 확인용
STATE_FILE = Path("r3m_tv_okx_state.json")
OKX_BASE_URL = "https://www.okx.com"
TD_MODE = "cross"  # 교차 마진. 격리 원하면 "isolated"

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("zetro_okx_bot")


class OkxApiError(RuntimeError):
    def __init__(self, data: dict):
        self.data = data
        first = (data.get("data") or [{}])[0]
        self.scode = str(first.get("sCode", ""))
        self.smsg = first.get("sMsg", "")
        super().__init__(f"OKX API 오류: {data}")


OKX_ERROR_MESSAGES = {
    "50001": "거래소 시스템 점검 중",
    "50004": "요청 시간 초과 (체결 여부 불확실 — 포지션 확인 필요)",
    "50005": "OKX API 일시 중단",
    "50011": "요청이 너무 잦음 (레이트 리밋)",
    "50013": "거래소 시스템 혼잡, 잠시 후 재시도 필요",
    "51000": "요청 파라미터 오류",
    "51001": "존재하지 않는 종목",
    "51004": "주문 수량이 한도 초과",
    "51006": "주문 가격이 허용 범위를 벗어남",
    "51008": "증거금(USDT) 부족",
    "51009": "주문 기능이 일시적으로 제한됨(거래소 측)",
    "51119": "잔고 부족으로 주문 실패",
    "51127": "사용 가능한 잔고가 0",
    "51131": "잔고 부족",
    "59100": "미체결 포지션이 있어 레버리지 변경 불가",
    "59101": "격리 모드 미체결 주문이 있어 레버리지 변경 불가",
    "59102": "설정한 레버리지가 최대 허용치 초과",
    "59103": "레버리지 대비 증거금 부족",
    "59108": "레버리지가 낮고 증거금도 부족함",
}


def format_okx_error(e: Exception) -> str:
    if isinstance(e, OkxApiError):
        known = OKX_ERROR_MESSAGES.get(e.scode)
        if known:
            return known
        if e.smsg:
            return e.smsg.strip()
    return str(e)


def notify(title: str, message: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": f"{title}\n{message}"},
            timeout=10,
        )
    except Exception as e:  # noqa: BLE001
        log.warning("텔레그램 알림 전송 실패: %s", e)


# ----------------------------------------------------------------------------
# 상태 저장 / 일일 통계
# ----------------------------------------------------------------------------

_state: Optional[dict] = None
_state_lock = threading.Lock()


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            log.warning("상태 파일이 손상되어 새로 시작합니다.")
    return {"positions": {}}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


KST = timezone(timedelta(hours=9))


def _today() -> str:
    # 하루 기준을 한국시간 0시로 (손절 횟수, 승패, 누적 손익 모두)
    return datetime.now(KST).strftime("%Y-%m-%d")


def _daily(key: str, defaults: dict) -> dict:
    today = _today()
    d = _state.setdefault(key, {"date": today, **defaults})
    if d.get("date") != today:
        d.clear()
        d.update({"date": today, **defaults})
    return d


def check_daily_sl_limit() -> bool:
    return _daily("daily_sl", {"count": 0})["count"] >= MAX_DAILY_SL_COUNT


def record_sl_hit() -> None:
    d = _daily("daily_sl", {"count": 0})
    d["count"] += 1
    save_state(_state)
    log.warning("오늘 손절 %d회째 발생 (한도 %d회)", d["count"], MAX_DAILY_SL_COUNT)
    if d["count"] == MAX_DAILY_SL_COUNT:
        notify("⛔ 오늘 자동매매 중지",
               f"오늘 손절 {MAX_DAILY_SL_COUNT}회에 도달해서 신규 진입을 멈춥니다.\n"
               f"이미 열린 포지션은 익절/손절 그대로 유지되고,\n"
               f"내일 한국시간 0시에 자동으로 다시 시작해요.")


def record_trade_result(success: bool) -> dict:
    d = _daily("daily_trade_stats", {"success": 0, "fail": 0})
    d["success" if success else "fail"] += 1
    save_state(_state)
    return d


def get_trade_stats() -> dict:
    return _daily("daily_trade_stats", {"success": 0, "fail": 0})


def record_win_loss(is_win: bool) -> dict:
    d = _daily("daily_win_loss", {"win": 0, "loss": 0})
    d["win" if is_win else "loss"] += 1
    save_state(_state)
    return d


def record_daily_pnl(pnl: float) -> dict:
    d = _daily("daily_pnl", {"total": 0.0})
    d["total"] += pnl
    save_state(_state)
    return d


def normalize_symbol(sym: str) -> str:
    """'BTCUSDT', 'BTCUSDT.P', 'BTC-USDT-SWAP' 등을 'BTC-USDT-SWAP'으로 통일."""
    sym = (sym or "").upper().strip()
    if sym.endswith(".P"):
        sym = sym[:-2]
    if sym.endswith("-SWAP"):
        return sym
    if "-" in sym:
        base, quote = sym.split("-")[:2]
    elif sym.endswith("USDT"):
        base, quote = sym[:-4], "USDT"
    else:
        base, quote = sym, "USDT"
    return f"{base}-{quote}-SWAP"


# ----------------------------------------------------------------------------
# OKX 실행 래퍼
# ----------------------------------------------------------------------------

@dataclass
class OkxExecutor:
    api_key: str
    api_secret: str
    passphrase: str
    _inst_cache: dict = field(default_factory=dict, init=False)

    def _timestamp(self) -> str:
        now = datetime.now(timezone.utc)
        return now.strftime("%Y-%m-%dT%H:%M:%S.") + f"{now.microsecond // 1000:03d}Z"

    def _sign(self, ts: str, method: str, path: str, body: str) -> str:
        msg = f"{ts}{method}{path}{body}"
        mac = hmac.new(self.api_secret.encode(), msg.encode(), hashlib.sha256)
        return base64.b64encode(mac.digest()).decode()

    def _request(self, method: str, path: str, params: dict | None = None, body: dict | None = None) -> dict:
        body_str = json.dumps(body) if body else ""
        query = ""
        if params:
            query = "?" + "&".join(f"{k}={v}" for k, v in params.items())
        ts = self._timestamp()
        headers = {
            "OK-ACCESS-KEY": self.api_key,
            "OK-ACCESS-SIGN": self._sign(ts, method, path + query, body_str),
            "OK-ACCESS-TIMESTAMP": ts,
            "OK-ACCESS-PASSPHRASE": self.passphrase,
            "Content-Type": "application/json",
        }
        resp = requests.request(method, OKX_BASE_URL + path + query, headers=headers,
                                data=body_str if body else None, timeout=15)
        data = resp.json()
        if data.get("code") not in ("0", 0):
            raise OkxApiError(data)
        return data

    def get_instrument(self, inst_id: str) -> dict:
        if inst_id in self._inst_cache:
            return self._inst_cache[inst_id]
        data = self._request("GET", "/api/v5/public/instruments", params={"instType": "SWAP", "instId": inst_id})
        info = data["data"][0]
        self._inst_cache[inst_id] = info
        return info

    def get_mark_price(self, inst_id: str) -> float:
        data = self._request("GET", "/api/v5/market/ticker", params={"instId": inst_id})
        return float(data["data"][0]["last"])

    def calc_qty(self, inst_id: str, notional_usdt: float, ref_price: float) -> float:
        inst = self.get_instrument(inst_id)
        ct_val = float(inst["ctVal"])
        lot_sz = float(inst["lotSz"])
        min_sz = float(inst["minSz"])
        qty = math.floor(notional_usdt / (ref_price * ct_val) / lot_sz) * lot_sz
        decimals = max(0, -int(math.floor(math.log10(lot_sz)))) if lot_sz < 1 else 0
        qty = round(qty, decimals)
        return qty if qty >= min_sz else 0.0

    def set_leverage(self, inst_id: str, leverage: int) -> None:
        try:
            self._request("POST", "/api/v5/account/set-leverage",
                          body={"instId": inst_id, "lever": str(leverage), "mgnMode": TD_MODE})
        except Exception as e:  # noqa: BLE001
            log.info("레버리지 설정 스킵/실패(무시): %s", e)

    def open_position(self, inst_id: str, side: str, notional_usdt: float, ref_price: float,
                      leverage: int, tp_margin_pct: float, sl_margin_pct: float) -> Optional[float]:
        order_side = "sell" if side == "S" else "buy"
        label = "SHORT" if side == "S" else "LONG"

        qty = self.calc_qty(inst_id, notional_usdt, ref_price)
        if qty <= 0:
            log.error("계산된 수량이 0 이하입니다: %s", inst_id)
            return None

        tp_price_pct = tp_margin_pct / leverage
        sl_price_pct = sl_margin_pct / leverage
        if side == "S":
            tp_price = ref_price * (1 - tp_price_pct)
            sl_price = ref_price * (1 + sl_price_pct)
        else:
            tp_price = ref_price * (1 + tp_price_pct)
            sl_price = ref_price * (1 - sl_price_pct)

        self.set_leverage(inst_id, leverage)

        body = {
            "instId": inst_id,
            "tdMode": TD_MODE,
            "side": order_side,
            "ordType": "market",
            "sz": str(qty),
            "attachAlgoOrds": [{
                "tpTriggerPx": str(round(tp_price, 6)),
                "tpOrdPx": "-1",
                "slTriggerPx": str(round(sl_price, 6)),
                "slOrdPx": "-1",
            }],
        }
        data = self._request("POST", "/api/v5/trade/order", body=body)
        log.info("%s OPEN 주문 전송: %s qty=%s TP=%.6f SL=%.6f -> %s", label, inst_id, qty, tp_price, sl_price, data)
        return qty

    def get_account_summary(self) -> dict:
        data = self._request("GET", "/api/v5/account/balance", params={"ccy": "USDT"})
        detail = data["data"][0]["details"][0] if data["data"][0]["details"] else {}
        return {
            "usdt_balance": float(detail.get("eq", 0) or 0),
            "unrealized_pnl": float(detail.get("upl", 0) or 0),
        }

    def get_open_positions(self) -> list:
        data = self._request("GET", "/api/v5/account/positions")
        return [p for p in data.get("data", []) if float(p.get("pos", 0)) != 0]


_executor: Optional[OkxExecutor] = None


def sync_positions_from_exchange() -> None:
    """시작할 때 OKX 실제 포지션 기준으로 로컬 상태를 다시 맞춤."""
    try:
        open_positions = _executor.get_open_positions()
    except Exception as e:  # noqa: BLE001
        log.warning("시작 시 포지션 동기화 실패: %s", e)
        return

    with _state_lock:
        new_positions: dict = {}
        for p in open_positions:
            inst_id = p.get("instId")
            pos_val = float(p.get("pos", 0) or 0)
            if not inst_id or pos_val == 0:
                continue
            new_positions[inst_id] = [{
                "side": "L" if pos_val > 0 else "S",
                "qty": abs(pos_val),
                "entry": float(p.get("avgPx", 0) or 0),
            }]
        _state["positions"] = new_positions
        save_state(_state)

    if new_positions:
        log.info("시작 시 OKX 실제 포지션과 동기화 완료: %s", ", ".join(new_positions.keys()))
    else:
        log.info("시작 시 OKX에 열려있는 포지션이 없습니다.")


# ----------------------------------------------------------------------------
# 진입 처리
# ----------------------------------------------------------------------------

def enter_position(symbol: str, side_raw: str) -> None:
    inst_id = normalize_symbol(symbol)
    side = "S" if side_raw == "short" else "L"

    with _state_lock:
        if check_daily_sl_limit():
            log.info("오늘 손절 한도(%d회) 도달로 신규 진입 스킵: %s", MAX_DAILY_SL_COUNT, inst_id)
            return

        max_stack = SYMBOL_MAX_STACK_OVERRIDE.get(inst_id, MAX_STACK_POSITIONS)
        positions: dict = _state.setdefault("positions", {})
        entries = positions.setdefault(inst_id, [])

        # 반대 방향 신호는 단방향 모드에서 기존 포지션을 상쇄시키므로 스킵
        if entries and entries[0].get("side") != side:
            log.info("%s 반대 방향 신호라 진입 스킵 — 기존 포지션 보호", inst_id)
            return
        if len(entries) >= max_stack:
            log.info("%s 이미 포지션 %d개 보유 중(한도 %d개)이라 진입 스킵", inst_id, len(entries), max_stack)
            return

        # 자리 예약 (동시에 같은 종목 신호가 와도 중복 진입 방지)
        pending_entry = {"side": side, "qty": None, "entry": None, "pending": True}
        entries.append(pending_entry)
        save_state(_state)

    def _release():
        with _state_lock:
            ents = _state.setdefault("positions", {}).get(inst_id, [])
            if pending_entry in ents:
                ents.remove(pending_entry)
            save_state(_state)
            return get_trade_stats()

    notional = SYMBOL_NOTIONAL_OVERRIDE.get(inst_id, POSITION_NOTIONAL_USDT)
    try:
        ref_price = _executor.get_mark_price(inst_id)
        qty = _executor.open_position(inst_id, side, notional, ref_price,
                                      LEVERAGE, TAKE_PROFIT_PCT, STOP_LOSS_PCT)
    except Exception as e:  # noqa: BLE001
        stats = _release()
        log.warning("%s 진입 중 예외 발생: %s", inst_id, e)
        notify("⚠️ 진입 실패 (OKX)",
               f"📊 종목: {inst_id}\n❗ 사유: {format_okx_error(e)}\n━━━━━━━━━━\n"
               f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")
        return

    if not qty:
        stats = _release()
        log.warning("%s 진입 실패", inst_id)
        notify("⚠️ 진입 실패 (OKX)",
               f"📊 종목: {inst_id}\n━━━━━━━━━━\n"
               f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")
        return

    with _state_lock:
        pending_entry["qty"] = qty
        pending_entry["entry"] = ref_price
        pending_entry.pop("pending", None)
        save_state(_state)
        stats = record_trade_result(True)

    label = "🔴 숏" if side == "S" else "🟢 롱"
    notify("🚀 신규 진입 (OKX)",
           f"{label} 진입 완료\n━━━━━━━━━━\n📊 종목: {inst_id}\n📦 수량: {qty}\n"
           f"💰 진입가: {ref_price}\n━━━━━━━━━━\n"
           f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")


# ----------------------------------------------------------------------------
# zetro 신호 조회 루프
# ----------------------------------------------------------------------------

def _zetro_signal_key(sig: dict) -> str:
    return f"{sig.get('symbol')}|{sig.get('type')}|{sig.get('tf')}|{sig.get('at')}|{sig.get('side')}"


def _match_rule(sig_type: str) -> Optional[str]:
    t = sig_type.lower()
    for name, rule in ZETRO_SIGNAL_RULES.items():
        if any(k.lower() in t for k in rule["keywords"]):
            return name
    return None


def _plain_symbol(sym: str) -> str:
    """'BTC-USDT-SWAP', 'BTCUSDT.P' 등을 'BTCUSDT'로."""
    return normalize_symbol(sym).replace("-SWAP", "").replace("-", "")


def _zetro_fetch() -> list:
    params = {}
    resp = requests.get(ZETRO_SIGNALS_URL,
                        headers={"Authorization": f"Bearer {ZETRO_API_KEY}"},
                        params=params, timeout=10)
    if resp.status_code != 200:
        raise RuntimeError(f"zetro 응답 {resp.status_code}: {resp.text[:200]}")
    return resp.json().get("items", []) or []


def zetro_poll_loop():
    with _state_lock:
        seen_list = _state.setdefault("zetro_seen", [])
    seen = set(seen_list)
    first_run = not seen   # 처음 켰을 때 이미 떠 있던 신호는 기록만 하고 진입 안 함
    error_streak = 0

    log.info("zetro 신호 조회 시작 (%s초 간격)", ZETRO_POLL_SECONDS)

    while True:
        try:
            items = _zetro_fetch()
            if error_streak >= 3:
                notify("✅ zetro 연결 복구", "신호 조회가 다시 정상 작동합니다.")
            error_streak = 0
            now_ms = time.time() * 1000
            new_keys = []

            for sig in sorted(items, key=lambda s: s.get("at") or 0):
                key = _zetro_signal_key(sig)
                if key in seen:
                    continue   # 같은 신호로 두 번 진입 안 함
                seen.add(key)
                new_keys.append(key)

                if first_run:
                    continue

                sig_type = str(sig.get("type", ""))
                tf = str(sig.get("tf", ""))
                side = str(sig.get("side", "")).lower()
                symbol = sig.get("symbol", "")
                at = sig.get("at") or 0

                log.info("zetro 새 신호: %s %s type=%s tf=%s", symbol, side, sig_type, tf)

                rule_name = _match_rule(sig_type)
                if not rule_name:
                    continue   # 아트로포스/스퀘어가 아니면 진입 안 함
                rule = ZETRO_SIGNAL_RULES[rule_name]
                if rule["symbols"] and _plain_symbol(symbol) not in rule["symbols"]:
                    log.info("%s 신호는 %s 종목 진입 안 함: %s", rule_name, symbol, sig)
                    continue
                if side not in ("long", "short") or not symbol:
                    log.info("zetro 신호 형식 불명확(스킵): %s", sig)
                    continue
                age_sec = (now_ms - at) / 1000 if at else None
                if age_sec is None or age_sec > rule["max_age_sec"]:
                    log.info("%s 신호가 %s초 지나서 스킵: %s", rule_name,
                             f"{age_sec:.0f}" if age_sec is not None else "?", sig)
                    continue

                log.info("zetro %s 신호로 진입 시도: %s %s (%s)", rule_name, symbol, side, tf)
                try:
                    enter_position(symbol, side)
                except Exception as e:  # noqa: BLE001
                    log.error("zetro 신호 진입 처리 실패: %s", e)

            first_run = False
            if new_keys:
                with _state_lock:
                    seen_list = _state.setdefault("zetro_seen", [])
                    seen_list.extend(new_keys)
                    if len(seen_list) > 2000:
                        del seen_list[:-2000]
                        seen.intersection_update(seen_list)
                    save_state(_state)
        except Exception as e:  # noqa: BLE001
            error_streak += 1
            log.warning("zetro 신호 조회 실패(%d회 연속): %s", error_streak, e)
            if error_streak == 3:
                notify("⚠️ zetro 신호 조회 실패", f"3회 연속 실패\n사유: {str(e)[:200]}")
        time.sleep(ZETRO_POLL_SECONDS)


# ----------------------------------------------------------------------------
# 정기 리포트 / 익절·손절 감시
# ----------------------------------------------------------------------------

def heartbeat_loop():
    while True:
        time.sleep(5 * 60)
        try:
            summary = _executor.get_account_summary()
            upl = summary["unrealized_pnl"]
            open_positions = _executor.get_open_positions()
            if open_positions:
                lines = []
                for p in open_positions:
                    pos_val = float(p.get("pos", 0))
                    p_pnl = float(p.get("upl", 0) or 0)
                    lines.append(
                        f"{'🟢 롱' if pos_val > 0 else '🔴 숏'} {p['instId']}\n"
                        f"   수량: {abs(pos_val)} | 손익: {p_pnl:+.2f} USDT"
                    )
                pos_text = "\n\n".join(lines)
            else:
                pos_text = "보유 포지션 없음"

            with _state_lock:
                wl = dict(_daily("daily_win_loss", {"win": 0, "loss": 0}))
                pnl_today = _daily("daily_pnl", {"total": 0.0})["total"]
                sl_count = _daily("daily_sl", {"count": 0})["count"]
            stopped = "\n⛔ 오늘 손절 한도 도달 — 신규 진입 중지 중" if sl_count >= MAX_DAILY_SL_COUNT else ""

            notify("📊 정기 리포트 (OKX)",
                   f"━━━━━━━━━━\n💰 USDT 잔고: {summary['usdt_balance']:.2f}\n"
                   f"{'📈' if upl >= 0 else '📉'} 미실현 손익: {upl:+.2f}\n━━━━━━━━━━\n"
                   f"🗓 오늘 성적 (한국시간 0시 기준)\n"
                   f"🏆 {wl['win']}승 {wl['loss']}패\n"
                   f"💵 당일 실현손익: {pnl_today:+.2f} USDT{stopped}\n━━━━━━━━━━\n\n"
                   f"📌 보유 포지션\n{pos_text}")
        except Exception as e:  # noqa: BLE001
            log.warning("하트비트 알림 실패: %s", e)


def sl_watch_loop():
    while True:
        time.sleep(120)
        try:
            open_inst_ids = {p["instId"] for p in _executor.get_open_positions()}

            with _state_lock:
                positions_state: dict = _state.setdefault("positions", {})
                closed_inst_ids = [i for i, v in positions_state.items() if v and i not in open_inst_ids]

            for inst_id in closed_inst_ids:
                with _state_lock:
                    entries = _state.setdefault("positions", {}).get(inst_id) or []
                    has_real_entry = any(e.get("qty") for e in entries)
                    if not has_real_entry:
                        # 주문 진행 중인 예약 자리는 건드리지 않음
                        if not any(e.get("pending") for e in entries):
                            _state["positions"][inst_id] = []
                            save_state(_state)
                        continue

                hist = _executor._request("GET", "/api/v5/account/positions-history",
                                          params={"instId": inst_id, "limit": "1"})
                rows = hist.get("data", [])
                pnl = float(rows[0].get("pnl", 0) or 0) if rows else 0.0
                is_win = pnl >= 0

                with _state_lock:
                    if not is_win:
                        record_sl_hit()
                    win_loss = record_win_loss(is_win)
                    daily_pnl = record_daily_pnl(pnl)
                    _state.setdefault("positions", {})[inst_id] = []
                    save_state(_state)

                notify(f"{'✅ 익절' if is_win else '🛑 손절'} (OKX)",
                       f"📊 종목: {inst_id}\n💰 손익: {pnl:+.2f} USDT\n━━━━━━━━━━\n"
                       f"🏆 오늘 {win_loss['win']}승 {win_loss['loss']}패\n"
                       f"💵 당일 실현손익: {daily_pnl['total']:+.2f} USDT")
        except Exception as e:  # noqa: BLE001
            log.warning("손절 감시 루프 오류: %s", e)


# ----------------------------------------------------------------------------
# Railway 상태 확인용 (주문 기능 없음, 접속하면 ok만 응답)
# ----------------------------------------------------------------------------

class HealthHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def do_GET(self):
        body = b'{"ok":true}'
        self.send_response(200)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    global _executor, _state

    api_key = os.environ.get("OKX_API_KEY", "")
    api_secret = os.environ.get("OKX_API_SECRET", "")
    passphrase = os.environ.get("OKX_API_PASSPHRASE", "")
    if not api_key or not api_secret or not passphrase:
        raise SystemExit("OKX_API_KEY / OKX_API_SECRET / OKX_API_PASSPHRASE 환경변수를 설정해야 합니다.")

    _executor = OkxExecutor(api_key=api_key, api_secret=api_secret, passphrase=passphrase)
    _state = load_state()
    sync_positions_from_exchange()

    log.info("zetro OKX 봇 시작 | notional=%sUSDT leverage=%sx TP=+%.0f%% SL=-%.0f%%",
             POSITION_NOTIONAL_USDT, LEVERAGE, TAKE_PROFIT_PCT * 100, STOP_LOSS_PCT * 100)

    threading.Thread(target=heartbeat_loop, daemon=True).start()
    threading.Thread(target=sl_watch_loop, daemon=True).start()
    if ZETRO_API_KEY:
        threading.Thread(target=zetro_poll_loop, daemon=True).start()
    else:
        log.warning("ZETRO_API_KEY가 없어서 zetro 신호 조회는 꺼둔 상태로 시작합니다.")
        notify("⚠️ zetro 신호 조회 꺼짐", "Railway Variables에 ZETRO_API_KEY를 넣어주세요.")

    server = ThreadingHTTPServer(("0.0.0.0", PORT), HealthHandler)
    server.daemon_threads = True
    server.serve_forever()


if __name__ == "__main__":
    main()
