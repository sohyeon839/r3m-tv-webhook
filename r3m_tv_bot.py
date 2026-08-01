"""
TradingView Webhook Auto-Trading Bot (Bybit) — R3M 봇과 완전히 독립적인 프로그램
=================================================================

트레이딩뷰(TradingView)에서 보내는 웹훅 알림(HTTP POST)을 받아서, 알림에
담긴 방향(롱/숏)으로 즉시 바이비트에 시장가 진입/청산하는 봇입니다.

R3M-BASIC 복사매매 봇(r3m_copy_bot.py)과는 완전히 별개의 프로그램이라,
서로 영향을 주지 않습니다. 따로 실행하고 따로 꺼도 됩니다.

동작 방식
---------
트레이딩뷰 알림의 "메시지(Message)" 칸에 아래와 같은 JSON을 넣어두면,
그 알림이 울릴 때마다 이 봇이 받아서 그대로 진입/청산합니다.

  진입(롱): {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "side": "long", "action": "entry"}
  진입(숏): {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "side": "short", "action": "entry"}
  청산    : {"secret": "본인이_정한_값", "symbol": "{{ticker}}", "action": "exit"}
            (청산 시 side는 안 넣어도 됩니다 — 진입 때 기록해둔 방향으로 알아서 청산)

action을 아예 안 보내면 기본값은 "entry"로 처리됩니다.

중요한 전제
------------
트레이딩뷰의 서버가 이 컴퓨터로 알림을 보내려면, 이 컴퓨터가 인터넷에서
접속 가능한 주소를 가지고 있어야 합니다. localhost 주소로는 절대 안 됩니다.
ngrok 같은 도구로 이 프로그램이 쓰는 포트(기본 8788)를 공개해서, 그 공개
주소 + "/webhook" 을 트레이딩뷰 알림의 웹훅 URL 칸에 넣어주세요.
  예: https://xxxx-xxxx.ngrok-free.app/webhook

보안: TV_WEBHOOK_SECRET 값을 반드시 본인만 아는 값으로 바꿔두세요. 이 값이
없거나 틀리면 요청을 거부합니다. URL만 알면 누구나 위조 신호를 보내
무단으로 매매를 일으킬 수 있으므로 꼭 설정하세요.

필요 패키지
------------
pip install pybit requests

환경 변수
----------
BYBIT_API_KEY, BYBIT_API_SECRET       : 바이비트 API 키 (Contract Trade 권한)
TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID  : (선택) 텔레그램 알림용
"""

from __future__ import annotations

import json
import re
import logging
import math
import os
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Optional

import requests
import threading
import time

try:
    from pybit.unified_trading import HTTP
except ImportError:  # pragma: no cover
    HTTP = None


# ----------------------------------------------------------------------------
# 설정 — 여기를 원하는 값으로 바꾸세요
# ----------------------------------------------------------------------------

WEBHOOK_PORT = int(os.environ.get("PORT", 8788))  # Railway 등 클라우드는 PORT 환경변수를 자동 지정함
WEBHOOK_SECRET = "0413"   # 반드시 본인만 아는 값으로 바꾸세요
POSITION_NOTIONAL_USDT = 2500.0         # 알림 1건당 진입 명목가치(USDT)
LEVERAGE = 10    
TAKE_PROFIT_PCT = 0.10   # 익절: 증거금 대비 수익률 +10% (레버리지 반영해서 자동 계산)
STOP_LOSS_PCT = 0.007    # 손절: 진입가 대비 -0.7% (증거금 기준 10배 레버리지 시 -7%)

STATE_FILE = Path("r3m_tv_state.json")
CATEGORY = "linear"

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("r3m_tv_bot")


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
def heartbeat_loop():
    while True:
        time.sleep(5 * 60)  # 5분마다
        try:
            wallet = _executor.session.get_wallet_balance(accountType="UNIFIED", coin="USDT")
            coin_info = wallet["result"]["list"][0]["coin"][0]
            usdt_balance = coin_info.get("walletBalance", "?")
            unrealized_pnl = coin_info.get("unrealisedPnl", "?")

            pos_resp = _executor.session.get_positions(category=CATEGORY, settleCoin="USDT")
            pos_list = pos_resp.get("result", {}).get("list", [])
            open_positions = [p for p in pos_list if float(p.get("size", 0)) > 0]

            if open_positions:
                lines = []
                for p in open_positions:
                    lines.append(
                        f"- {p['symbol']} {p['side']} 수량:{p['size']} PNL:{p.get('unrealisedPnl', '?')}"
                    )
                pos_text = "\n".join(lines)
            else:
                pos_text = "보유 포지션 없음"

            msg = (
                f"USDT 잔고: {usdt_balance}\n"
                f"미실현 손익 합계: {unrealized_pnl}\n\n"
                f"포지션:\n{pos_text}"
            )
            notify("📊 5분 정기 리포트", msg)
        except Exception as e:  # noqa: BLE001
            log.warning("하트비트 알림 실패: %s", e)

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
    sym = (sym or "").upper().strip()
    if not sym.endswith("USDT"):
        sym += "USDT"
    return sym
def parse_panterra_text(text: str) -> Optional[dict]:
    m = re.search(r"종목\s*[:：]\s*[A-Z]*:?([A-Z0-9]+?)(?:\.P)?\s", text)
    if not m:
        return None
    symbol = m.group(1)

    if "매수" in text:
        side = "long"
    elif "매도" in text:
        side = "short"
    else:
        return None

    return {"secret": WEBHOOK_SECRET, "symbol": symbol, "side": side, "action": "entry"}

# ----------------------------------------------------------------------------
# 바이비트 실행 래퍼
# ----------------------------------------------------------------------------

@dataclass
class BybitExecutor:
    api_key: str
    api_secret: str
    session: Optional["HTTP"] = field(default=None, init=False)
    _qty_step_cache: dict = field(default_factory=dict, init=False)

    def __post_init__(self):
        if HTTP is None:
            raise RuntimeError("pybit 이 설치되어 있지 않습니다. `pip install pybit` 후 다시 실행하세요.")
        self.session = HTTP(
            api_key=self.api_key,
            api_secret=self.api_secret,
            recv_window=20000,  # 컴퓨터 시계 오차에 좀 더 관대하게 처리
        )

    def get_qty_step(self, symbol: str) -> float:
        if symbol in self._qty_step_cache:
            return self._qty_step_cache[symbol]
        info = self.session.get_instruments_info(category=CATEGORY, symbol=symbol)
        lot = info["result"]["list"][0]["lotSizeFilter"]
        step = float(lot["qtyStep"])
        self._qty_step_cache[symbol] = step
        return step

    def round_qty(self, symbol: str, raw_qty: float) -> float:
        step = self.get_qty_step(symbol)
        if step <= 0:
            return raw_qty
        decimals = max(0, -int(math.floor(math.log10(step))))
        qty = math.floor(raw_qty / step) * step
        return round(qty, decimals)

    def get_mark_price(self, symbol: str) -> float:
        tick = self.session.get_tickers(category=CATEGORY, symbol=symbol)
        return float(tick["result"]["list"][0]["lastPrice"])

    def set_leverage(self, symbol: str) -> None:
        try:
            self.session.set_leverage(
                category=CATEGORY, symbol=symbol,
                buyLeverage=str(LEVERAGE), sellLeverage=str(LEVERAGE),
            )
        except Exception as e:  # noqa: BLE001
            log.debug("레버리지 설정 스킵/무시: %s", e)

    def ensure_one_way_mode(self, symbol: str) -> None:
        """
        계좌가 헤지 모드(Hedge Mode)로 되어있으면 positionIdx=0 주문이
        거부된다(ErrCode 10001). 이 봇은 원웨이 모드 기준으로 동작하므로,
        주문 전에 해당 심볼을 원웨이 모드로 맞춰준다. 이미 원웨이면 그냥
        무시되는 호출이라 매번 불러도 안전하다.
        """
        try:
            self.session.switch_position_mode(category=CATEGORY, symbol=symbol, mode=0)
        except Exception as e:  # noqa: BLE001
            log.debug("포지션 모드 전환 스킵/무시: %s", e)

    def open_position(self, symbol: str, side: str, notional_usdt: float, ref_price: float) -> Optional[float]:
            order_side = "Sell" if side == "S" else "Buy"
            label = "SHORT" if side == "S" else "LONG"

            raw_qty = notional_usdt / ref_price
            qty = self.round_qty(symbol, raw_qty)
            if qty <= 0:
                log.error("계산된 수량이 0 이하입니다: %s", symbol)
                return None

            tp_price_pct = TAKE_PROFIT_PCT / LEVERAGE

            if side == "S":
                take_profit = ref_price * (1 - tp_price_pct)
                stop_loss = ref_price * (1 + STOP_LOSS_PCT)
            else:
                take_profit = ref_price * (1 + tp_price_pct)
                stop_loss = ref_price * (1 - STOP_LOSS_PCT)
            self.set_leverage(symbol)
            self.ensure_one_way_mode(symbol)
            order = self.session.place_order(
                category=CATEGORY, symbol=symbol, side=order_side, orderType="Market",
                qty=str(qty), positionIdx=0, reduceOnly=False,
                takeProfit=str(round(take_profit, 6)),
                stopLoss=str(round(stop_loss, 6)),
            )
            log.info(
                "%s OPEN 주문 전송: %s qty=%s TP=%.4f SL=%.4f -> %s",
                label, symbol, qty, take_profit, stop_loss, order.get("retMsg"),
            )
            return qty

    def close_position(self, symbol: str, side: str) -> Optional[dict]:
            entry_bybit_side = "Sell" if side == "S" else "Buy"
            close_order_side = "Buy" if side == "S" else "Sell"
            label = "SHORT" if side == "S" else "LONG"

            pos_resp = self.session.get_positions(category=CATEGORY, symbol=symbol)
            pos_list = pos_resp.get("result", {}).get("list", [])
            size = 0.0
            pnl = 0.0
            for p in pos_list:
                if p.get("side") == entry_bybit_side and float(p.get("size", 0)) > 0:
                    size = float(p["size"])
                    pnl = float(p.get("unrealisedPnl", 0) or 0)
                    break

            if size <= 0:
                log.warning("바이비트에 %s %s 포지션이 이미 없습니다(스킵).", symbol, label)
                return None

            order = self.session.place_order(
                category=CATEGORY, symbol=symbol, side=close_order_side, orderType="Market",
                qty=str(size), positionIdx=0, reduceOnly=True,
            )
            log.info("%s CLOSE 주문 전송: %s qty=%s -> %s", label, symbol, size, order.get("retMsg"))
            return {"qty": size, "pnl": pnl}


# ----------------------------------------------------------------------------
# 웹훅 처리
# ----------------------------------------------------------------------------

_executor: Optional[BybitExecutor] = None
_state: Optional[dict] = None


def handle_alert(payload: dict) -> None:
    symbol = normalize_symbol(payload.get("symbol", ""))
    side_raw = str(payload.get("side", "")).lower()
    action = str(payload.get("action", "entry")).lower()  # 안 보내면 기본 entry
    side = "S" if side_raw in ("short", "sell", "s") else "L"

    if not symbol or action not in ("entry", "exit"):
        raise ValueError("symbol 또는 action 값이 올바르지 않습니다")

    positions: dict = _state.setdefault("positions", {})

    if action == "entry":
        if symbol in positions:
            log.info("%s 이미 포지션 보유 중이라 진입 스킵", symbol)
            return

        ref_price = None
        try:
            if payload.get("price"):
                ref_price = float(payload["price"])
        except (TypeError, ValueError):
                ref_price = None
            if not ref_price:
                ref_price = _executor.get_mark_price(symbol)

            qty = _executor.open_position(symbol, side, POSITION_NOTIONAL_USDT, ref_price)
            if qty:
                positions[symbol] = {"side": side, "qty": qty, "entry": ref_price}
                save_state(_state)
                label = "🔴 숏" if side == "S" else "🟢 롱"
                notify(
                    "🚀 신규 진입",
                    f"{label} 진입 완료\n"
                    f"━━━━━━━━━━\n"
                    f"📊 종목: {symbol}\n"
                    f"📦 수량: {qty}\n"
                    f"💰 진입가: {ref_price}"
                )
            else:
                log.warning("%s 진입 실패", symbol)

        else:  # exit
            pos = positions.get(symbol)
            if not pos:
                log.info("%s 추적 중인 포지션이 없어 청산 스킵", symbol)
                return
            close_side = pos.get("side", "S")
            result = _executor.close_position(symbol, close_side)
            positions.pop(symbol, None)
            save_state(_state)
            label = "🔴 숏" if close_side == "S" else "🟢 롱"
            if result:
                pnl = result["pnl"]
                emoji = "💰" if pnl >= 0 else "💸"
                sign = "+" if pnl >= 0 else ""
                notify(
                    "✅ 포지션 청산",
                    f"{label} 청산 완료\n"
                    f"━━━━━━━━━━\n"
                    f"📊 종목: {symbol}\n"
                    f"{emoji} 손익: {sign}{pnl:.2f} USDT"
                )
            else:
                notify("✅ 포지션 청산", f"{label} 청산 완료\n📊 종목: {symbol}")

class WebhookHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"  # 외부 터널 서비스와의 연결 호환성을 위해 명시

    def log_message(self, fmt, *args):
        pass

    def do_POST(self):
        self.close_connection = True  # 단일 스레드 서버가 유지연결로 막히는 것 방지
        if self.path.rstrip("/") != "/webhook":
            self.send_response(404)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return

        length = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(length) if length else b""

        try:
            raw_text = raw.decode("utf-8", errors="ignore")
            try:
                payload = json.loads(raw_text)
            except Exception:  # noqa: BLE001
                payload = parse_panterra_text(raw_text)
                if payload is None:
                    raise ValueError("파싱 실패")
        except Exception:  # noqa: BLE001
            body = b'{"error":"invalid json"}'
            self.send_response(400)
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

    api_key = os.environ.get("BYBIT_API_KEY", "")
    api_secret = os.environ.get("BYBIT_API_SECRET", "")
    if not api_key or not api_secret:
        raise SystemExit("BYBIT_API_KEY / BYBIT_API_SECRET 환경변수를 설정해야 합니다.")

    if WEBHOOK_SECRET == "change-me-please":
        log.warning("⚠ WEBHOOK_SECRET 이 기본값 그대로입니다. 실제 사용 전 꼭 본인만 아는 값으로 바꾸세요!")

    _executor = BybitExecutor(api_key=api_key, api_secret=api_secret)
    _state = load_state()

    log.info(
        "TV 웹훅 봇 시작 | notional=%sUSDT leverage=%sx port=%s",
        POSITION_NOTIONAL_USDT, LEVERAGE, WEBHOOK_PORT,
    )
    threading.Thread(target=heartbeat_loop, daemon=True).start()
    server = HTTPServer(("0.0.0.0", WEBHOOK_PORT), WebhookHandler)
    log.info("웹훅 서버 실행 중 -> 0.0.0.0:%s/webhook (외부에서 받으려면 ngrok 등으로 공개 필요)", WEBHOOK_PORT)
    server.serve_forever()


if __name__ == "__main__":
    main()
