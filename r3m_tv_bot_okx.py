"""
TradingView Webhook Auto-Trading Bot (OKX) — 바이비트 봇(r3m_tv_bot.py)과
완전히 독립적인 프로그램입니다. 구조와 웹훅 형식은 동일하고, 거래소만
OKX로 바뀐 버전입니다.

동작 방식
---------
트레이딩뷰 알림의 "메시지(Message)" 칸에 아래와 같은 JSON을 넣어두면,
그 알림이 울릴 때마다 이 봇이 받아서 그대로 진입/청산합니다.

  진입(롱): {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "side": "long", "action": "entry"}
  진입(숏): {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "side": "short", "action": "entry"}
  청산    : {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "action": "exit"}

symbol은 "BTCUSDT" 형태로 보내면 내부적으로 OKX 표기법인 "BTC-USDT-SWAP"으로
자동 변환합니다.

중요한 전제
------------
1. OKX 계정의 포지션 모드가 반드시 "단방향(one-way/net)" 모드여야 합니다.
   OKX 웹/앱 -> 선물(Perpetual) 설정에서 확인/변경하세요. 헤지 모드면 주문이
   거부됩니다.
2. 이 컴�터/서버가 외부에서 접속 가능한 주소를 가지고 있어야 트레이딩뷰
   웹훅을 받을 수 있습니다. Railway에 배포했다면 자동으로 공개 주소가
   생깁니다.

필요 패키지
------------
pip install requests

환경 변수
----------
OKX_API_KEY, OKX_API_SECRET, OKX_API_PASSPHRASE : OKX API 키 (Trade 권한 필요)
TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID             : (선택) 텔레그램 알림용
"""

from __future__ import annotations

import base64
import hmac
import hashlib
import json
import re
import logging
import math
import os
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Optional

import requests

# ----------------------------------------------------------------------------
# 설정 — 여기를 원하는 값으로 바꾸세요 (바이비트 봇과 동일한 기본값)
# ----------------------------------------------------------------------------

WEBHOOK_PORT = int(os.environ.get("PORT", 8789))
WEBHOOK_SECRET = "0413"   # 반드시 본인만 아는 값으로 바꾸세요
POSITION_NOTIONAL_USDT = 3000.0
LEVERAGE = 20
TAKE_PROFIT_PCT = 0.07   # 익절: 증거금 대비 수익률 +0.7%
STOP_LOSS_PCT = 0.005    # 손절: 진입가 대비 -0.5%

STATE_FILE = Path("r3m_tv_okx_state.json")
OKX_BASE_URL = "https://www.okx.com"
TD_MODE = "cross"  # 교차 마진. 격리 원하면 "isolated"

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("r3m_tv_okx_bot")


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


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            log.warning("상태 파일이 손상되어 새로 시작합니다.")
    return {"positions": {}}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


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
  
def extract_json_block(text: str) -> Optional[str]:
    """
    문자열 안에서 제일 처음 나오는 '{' 부터, 그것과 짝이 맞는 '}' 까지를
    정확히 찾아서 돌려줍니다. "{{ticker}}" 처럼 중괄호가 중첩된 경우에도
    괄호 개수를 세어가며 짝을 맞추기 때문에 안전합니다.
    짝이 맞는 '}'를 못 찾으면 None을 돌려줍니다.
    """
    start = text.find("{")
    if start == -1:
        return None
    depth = 0
    for i in range(start, len(text)):
        ch = text[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    return None
def parse_panterra_text(text: str) -> Optional[dict]:
    """
    JSON이 아예 없이 순수 텍스트로만 오는 알람(판테라 / ATH Ultimate)을
    위한 파서입니다. secret 값은 텍스트에 없으므로 자동으로 채워 넣습니다.
    """
    # 1) 종목 판단: "종목 : BYBIT:XXXUSDT.P" 형태가 있으면 그 심볼을 쓰고,
    #    없으면 BTCUSDT 전용 알람이므로 무조건 BTCUSDT로 간주합니다.
    m = re.search(r"종목\s*[:：]\s*[A-Z]*:?([A-Z0-9]+?)(?:\.P)?(?:\s|$)", text)
    symbol = m.group(1) if m else "BTCUSDT"

    # 2) 방향 판단
    if "매수" in text or "파랑빔" in text or "LONG" in text.upper():
        side = "long"
    elif "매도" in text or "노랑빔" in text or "SHORT" in text.upper():
        side = "short"
    else:
        return None

    return {"secret": WEBHOOK_SECRET, "symbol": symbol, "side": side, "action": "entry"}
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
        return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.") + \
            f"{datetime.now(timezone.utc).microsecond // 1000:03d}Z"

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
        sign = self._sign(ts, method, path + query, body_str)
        headers = {
            "OK-ACCESS-KEY": self.api_key,
            "OK-ACCESS-SIGN": sign,
            "OK-ACCESS-TIMESTAMP": ts,
            "OK-ACCESS-PASSPHRASE": self.passphrase,
            "Content-Type": "application/json",
        }
        url = OKX_BASE_URL + path + query
        resp = requests.request(method, url, headers=headers, data=body_str if body else None, timeout=15)
        data = resp.json()
        if data.get("code") not in ("0", 0):
            raise RuntimeError(f"OKX API 오류: {data}")
        return data

    # -- 공개 데이터 --------------------------------------------------------

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
        raw_qty = notional_usdt / (ref_price * ct_val)
        qty = math.floor(raw_qty / lot_sz) * lot_sz
        decimals = max(0, -int(math.floor(math.log10(lot_sz)))) if lot_sz < 1 else 0
        qty = round(qty, decimals)
        return qty if qty >= min_sz else 0.0

    # -- 계정/주문 ------------------------------------------------------------

    def set_leverage(self, inst_id: str) -> None:
        try:
            self._request(
                "POST", "/api/v5/account/set-leverage",
                body={"instId": inst_id, "lever": str(LEVERAGE), "mgnMode": TD_MODE},
            )
        except Exception as e:  # noqa: BLE001
            log.info("레버리지 설정 스킵/실패(무시): %s", e)

    def open_position(self, inst_id: str, side: str, notional_usdt: float, ref_price: float) -> Optional[float]:
        order_side = "sell" if side == "S" else "buy"
        label = "SHORT" if side == "S" else "LONG"

        qty = self.calc_qty(inst_id, notional_usdt, ref_price)
        if qty <= 0:
            log.error("계산된 수량이 0 이하입니다: %s", inst_id)
            return None

        tp_price_pct = TAKE_PROFIT_PCT / LEVERAGE
        if side == "S":
            tp_price = ref_price * (1 - tp_price_pct)
            sl_price = ref_price * (1 + STOP_LOSS_PCT)
        else:
            tp_price = ref_price * (1 + tp_price_pct)
            sl_price = ref_price * (1 - STOP_LOSS_PCT)

        self.set_leverage(inst_id)

        body = {
            "instId": inst_id,
            "tdMode": TD_MODE,
            "side": order_side,
            "ordType": "market",
            "sz": str(qty),
            "attachAlgoOrds": [
                {
                    "tpTriggerPx": str(round(tp_price, 6)),
                    "tpOrdPx": "-1",
                    "slTriggerPx": str(round(sl_price, 6)),
                    "slOrdPx": "-1",
                }
            ],
        }
        data = self._request("POST", "/api/v5/trade/order", body=body)
        log.info("%s OPEN 주문 전송: %s qty=%s TP=%.4f SL=%.4f -> %s", label, inst_id, qty, tp_price, sl_price, data)
        return qty

    def close_position(self, inst_id: str, side: str) -> Optional[dict]:
        label = "SHORT" if side == "S" else "LONG"

        # 청산 전 미실현 손익 조회 (알림용)
        pos_data = self._request("GET", "/api/v5/account/positions", params={"instId": inst_id})
        pos_list = pos_data.get("data", [])
        pnl = 0.0
        size = 0.0
        for p in pos_list:
            if float(p.get("pos", 0)) != 0:
                pnl = float(p.get("upl", 0) or 0)
                size = abs(float(p["pos"]))
                break

        if size <= 0:
            log.warning("OKX에 %s %s 포지션이 이미 없습니다(스킵).", inst_id, label)
            return None

        data = self._request(
            "POST", "/api/v5/trade/close-position",
            body={"instId": inst_id, "mgnMode": TD_MODE},
        )
        log.info("%s CLOSE 주문 전송: %s -> %s", label, inst_id, data)
        return {"qty": size, "pnl": pnl}

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


# ----------------------------------------------------------------------------
# 하트비트(5분 정기 리포트)
# ----------------------------------------------------------------------------

def heartbeat_loop():
    while True:
        time.sleep(5 * 60)
        try:
            summary = _executor.get_account_summary()
            usdt_balance = summary["usdt_balance"]
            unrealized_pnl = summary["unrealized_pnl"]
            pnl_emoji = "📈" if unrealized_pnl >= 0 else "📉"
            pnl_sign = "+" if unrealized_pnl >= 0 else ""

            open_positions = _executor.get_open_positions()
            if open_positions:
                lines = []
                for p in open_positions:
                    pos_val = float(p.get("pos", 0))
                    side_label = "🟢 롱" if pos_val > 0 else "🔴 숏"
                    p_pnl = float(p.get("upl", 0) or 0)
                    p_sign = "+" if p_pnl >= 0 else ""
                    lines.append(
                        f"{side_label} {p['instId']}\n"
                        f"   수량: {abs(pos_val)} | 손익: {p_sign}{p_pnl:.2f} USDT"
                    )
                pos_text = "\n\n".join(lines)
            else:
                pos_text = "보유 포지션 없음"

            msg = (
                f"━━━━━━━━━━\n"
                f"💰 USDT 잔고: {usdt_balance:.2f}\n"
                f"{pnl_emoji} 미실현 손익: {pnl_sign}{unrealized_pnl:.2f}\n"
                f"━━━━━━━━━━\n\n"
                f"📌 보유 포지션\n{pos_text}"
            )
            notify("📊 정기 리포트 (OKX)", msg)
        except Exception as e:  # noqa: BLE001
            log.warning("하트비트 알림 실패: %s", e)


# ----------------------------------------------------------------------------
# 웹훅 처리
# ----------------------------------------------------------------------------

_executor: Optional[OkxExecutor] = None
_state: Optional[dict] = None


def handle_alert(payload: dict) -> None:
    inst_id = normalize_symbol(payload.get("symbol", ""))
    side_raw = str(payload.get("side", "")).lower()
    action = str(payload.get("action", "entry")).lower()
    side = "S" if side_raw in ("short", "sell", "s") else "L"

    if not inst_id or action not in ("entry", "exit"):
        raise ValueError("symbol 또는 action 값이 올바르지 않습니다")

    positions: dict = _state.setdefault("positions", {})

    if action == "entry":
        if inst_id in positions:
            log.info("%s 이미 포지션 보유 중이라 진입 스킵", inst_id)
            return

        ref_price = None
        try:
            if payload.get("price"):
                ref_price = float(payload["price"])
        except (TypeError, ValueError):
            ref_price = None

        if not ref_price:
            ref_price = _executor.get_mark_price(inst_id)

        qty = _executor.open_position(inst_id, side, POSITION_NOTIONAL_USDT, ref_price)
        if qty:
            positions[inst_id] = {"side": side, "qty": qty, "entry": ref_price}
            save_state(_state)
            label = "🔴 숏" if side == "S" else "🟢 롱"
            notify(
                "🚀 신규 진입 (OKX)",
                f"{label} 진입 완료\n"
                f"━━━━━━━━━━\n"
                f"📊 종목: {inst_id}\n"
                f"📦 수량: {qty}\n"
                f"💰 진입가: {ref_price}"
            )
        else:
            log.warning("%s 진입 실패", inst_id)

    else:  # exit
        pos = positions.get(inst_id)
        if not pos:
            log.info("%s 추적 중인 포지션이 없어 청산 스킵", inst_id)
            return
        close_side = pos.get("side", "S")
        result = _executor.close_position(inst_id, close_side)
        positions.pop(inst_id, None)
        save_state(_state)
        label = "🔴 숏" if close_side == "S" else "🟢 롱"
        if result:
            pnl = result["pnl"]
            emoji = "💰" if pnl >= 0 else "💸"
            sign = "+" if pnl >= 0 else ""
            notify(
                "✅ 포지션 청산 (OKX)",
                f"{label} 청산 완료\n"
                f"━━━━━━━━━━\n"
                f"📊 종목: {inst_id}\n"
                f"{emoji} 손익: {sign}{pnl:.2f} USDT"
            )
        else:
            notify("✅ 포지션 청산 (OKX)", f"{label} 청산 완료\n📊 종목: {inst_id}")


class WebhookHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass

    def do_POST(self):
        self.close_connection = True
        if self.path.rstrip("/") != "/webhook":
            self.send_response(404)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return

        length = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(length) if length else b""

        raw_text = raw.decode("utf-8", errors="ignore")
        try:
            json_block = extract_json_block(raw_text)
            if json_block:
                payload = json.loads(json_block)
            else:
                payload = parse_panterra_text(raw_text)
                if payload is None:
                    raise ValueError("JSON도 없고 텍스트 파싱도 실패했습니다")
        except Exception:  # noqa: BLE001
            log.warning("JSON 파싱 실패, 원문: %s", raw_text[:200])
            body = b'{"error":"invalid json"}'
            self.send_response(400)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
           

        if re.search(r"매도|숏|SHORT|SELL", raw_text, re.IGNORECASE):
            payload["side"] = "short"
        elif re.search(r"매수|롱|LONG|BUY", raw_text, re.IGNORECASE):
            payload["side"] = "long"

        raw_upper = raw_text.upper()
        is_square = "스퀘어" in raw_text or "SQUARE" in raw_upper
        is_panterra = "판테라" in raw_text or "PANTERRA" in raw_upper
        if not is_square and not is_panterra:
            log.info("스퀘어/판테라 신호가 아니라서 진입 스킵: %s", raw_text[:100])
            body = b'{"ok":true,"skipped":"not allowed signal"}'
            self.send_response(200)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if payload.get("secret") != WEBHOOK_SECRET:
            log.warning("잘못된 secret 값으로 접근 시도가 있었습니다.")
            body = b'{"error":"unauthorized"}'
            self.send_response(401)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        try:
            handle_alert(payload)
            body = b'{"ok":true}'
            self.send_response(200)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except Exception as e:  # noqa: BLE001
            log.error("웹훅 처리 실패: %s", e)
            body = json.dumps({"error": str(e)}).encode("utf-8")
            self.send_response(500)
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

    log.info(
        "TV 웹훅 봇(OKX) 시작 | notional=%sUSDT leverage=%sx port=%s",
        POSITION_NOTIONAL_USDT, LEVERAGE, WEBHOOK_PORT,
    )
    threading.Thread(target=heartbeat_loop, daemon=True).start()
    server = HTTPServer(("0.0.0.0", WEBHOOK_PORT), WebhookHandler)
    log.info("웹훅 서버 실행 중 -> 0.0.0.0:%s/webhook", WEBHOOK_PORT)
    server.serve_forever()


if __name__ == "__main__":
    main()
