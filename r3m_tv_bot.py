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
            usdt_balance = float(coin_info.get("walletBalance", 0) or 0)
            unrealized_pnl = float(coin_info.get("unrealisedPnl", 0) or 0)
            pnl_emoji = "📈" if unrealized_pnl >= 0 else "📉"
            pnl_sign = "+" if unrealized_pnl >= 0 else ""

            pos_resp = _executor.session.get_positions(category=CATEGORY, settleCoin="USDT")
            pos_list = pos_resp.get("result", {}).get("list", [])
            open_positions = [p for p in pos_list if float(p.get("size", 0)) > 0]

            if open_positions:
                lines = []
                for p in open_positions:
                    side_label = "🟢 롱" if p["side"] == "Buy" else "🔴 숏"
                    p_pnl = float(p.get("unrealisedPnl", 0) or 0)
                    p_sign = "+" if p_pnl >= 0 else ""
                    lines.append(
                        f"{side_label} {p['symbol']}\n"
                        f"   수량: {p['size']} | 손익: {p_sign}{p_pnl:.2f} USDT"
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
            notify("📊 정기 리포트", msg)
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
        self._qty_
