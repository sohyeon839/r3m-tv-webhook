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
import html
import json
import re
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

# 증거금 기준 (포지션 규모 = 증거금 × 레버리지)
MARGIN_USDT = 200.0      # 진입 1번당 증거금 (모든 신호 공통)
LEVERAGE = 3             # 기본 레버리지 (신호별로 아래 규칙에서 따로 지정 가능)

# 방향별 배율 (모든 신호 공통으로 우선 적용). None이면 신호별 설정을 따름.
# 익절·손절은 "가격 기준 거리"가 같게 자동으로 맞춰져요.
# 봇이 절대 안 들어가는 종목 (직접 거래하는 종목). 예: {"BTC-USDT-SWAP", "ETH-USDT-SWAP"}
BOT_EXCLUDE_SYMBOLS: set = {"BTC-USDT-SWAP", "ETH-USDT-SWAP"}

LONG_ENTRY_ENABLED = True   # 롱 진입 켬 (끄려면 False)
LONG_LEVERAGE = 3        # 롱 3배 (증거금 200 → 포지션 600)
SHORT_LEVERAGE = 3       # 숏 3배 (증거금 200 → 포지션 600)
TAKE_PROFIT_PCT = 0.10   # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
STOP_LOSS_PCT = 0.05     # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)

# 종목별로 증거금을 다르게 하고 싶을 때만 추가
SYMBOL_MARGIN_OVERRIDE = {
    # "BTC-USDT-SWAP": 200.0,
}

MAX_STACK_POSITIONS = 1   # 같은 종목에 이미 포지션이 있으면 추가 진입 안 함
SYMBOL_MAX_STACK_OVERRIDE = {}
# 누적 성적 집계 시작 시각 (한국시간). 이 시각 이후 봇이 진입한 거래만 집계해요.
# 새로 처음부터 세고 싶으면 이 값을 바꾸세요.
STATS_START_KST = "2026-11-19 21:26"

# 누적 성적에서 빼버릴 신호 (기록을 지우고 합계에서도 뺌)
STATS_EXCLUDE_SOURCES = {"클러스터"}

# ----------------------------------------------------------------------------
# 포지션 관리: 본절 손절 + 분할 익절 (모두 "가격 기준" %)
# ----------------------------------------------------------------------------
MANAGE_ENABLED = True
MANAGE_POLL_SECONDS = 3            # 3초마다 포지션 확인

# 1) 본절 손절: 가격이 +1.0% 유리하게 가면 손절을 진입가 근처로 올림
BREAKEVEN_TRIGGER_PCT = 0.012     # 분할 익절과 같은 시점(+1.2%)에 본절로
BREAKEVEN_BUFFER_PCT = 0.001       # 진입가보다 0.1% 유리한 곳에 손절 (수수료 정도는 남게)

# 2) 분할 익절: 가격이 +1.2% 유리하게 가면 절반을 먼저 청산
PARTIAL_TP_TRIGGER_PCT = 0.012
PARTIAL_TP_RATIO = 0.5             # 0.5 = 절반 먼저 청산

# 3) 단계 손절: 가격이 +2.0% 유리하게 가면 손절을 +1.0% 수익 자리로 올림
#    (3배 기준 OKX 화면: +6% 도달 → 손절을 +3%로)
STEP_TRIGGER_PCT = 0.020
STEP_LOCK_PCT = 0.010

MAX_DAILY_SL_COUNT = 0    # 손절 "횟수" 한도 (0 = 사용 안 함, 아래 손실 % 한도를 사용)
# 하루(한국시간 0시 기준) 봇 실현손실이 그날 시작 잔고의 5%가 되면 신규 진입 중지, 0시 지나면 자동 재개
MAX_DAILY_LOSS_PCT = 0.05

# ----------------------------------------------------------------------------
# zetro 신호 설정
# ----------------------------------------------------------------------------

ZETRO_API_KEY = os.environ.get("ZETRO_API_KEY", "")
ZETRO_SIGNALS_URL = "https://ath.zetro.io/api/pub/v1/signals"
ZETRO_POLL_SECONDS = 5            # 5초마다 조회 (분당 12회, 한도 60회)
ZETRO_MAX_SIGNAL_AGE_SEC = 180    # 기본: 3분보다 오래된 신호는 진입 안 함

# 거래대금 필터 (zetro 스크리너의 "거래대금 100만 달러 이상"과 같은 기준)
# OKX 해당 종목의 최근 24시간 거래대금이 이보다 작으면 진입 안 함
MIN_24H_VOLUME_USD = 1_000_000

# API 조회로 들어온 신호의 실제 진입 ON/OFF
# False: 신호는 계속 조회해서 로그에만 남기고 진입은 안 함 (웹훅 확인 중이라 꺼둔 상태)
# True여도 아래 규칙 중 "api_entry": True 인 신호만 API로 진입 (지금은 아트로포스만)
ZETRO_API_ENTRY_ENABLED = True

# zetro 웹훅 수신 주소 (zetro 웹훅 설정에 넣을 주소의 뒷부분)
ZETRO_HOOK_PATH = "/zetro-hook/5472118043e07db5"

# 매매 기록지 페이지 주소 (폰 브라우저로 열기). 뒤 글자는 비밀번호 역할이라 공유하지 마세요.
REPORT_PATH = "/report/5472118043e07db5"
DAILY_TARGET_USD = 100.0   # 기록지에 표시할 하루 목표 수익

# ----------------------------------------------------------------------------
# zetro 웹훅 진입 규칙 (zetro 알림 만들기에서 거래대금·위험/주의 코인 등 필터를 걸어둔 알림만 옴)
# zetro 알림 메시지에 넣는 "rule" 값과 아래 이름이 같아야 합니다.
# ----------------------------------------------------------------------------
HOOK_ENTRY_ENABLED = True

# ----------------------------------------------------------------------------
# zetro 스크리너(/screener) 진입 — 홈페이지 스크리너 화면과 같은 결과만 받음
# ----------------------------------------------------------------------------
SCREENER_ENTRY_ENABLED = True
ZETRO_SCREENER_URL = "https://ath.zetro.io/api/pub/v1/screener"
SCREENER_POLL_SECONDS = 10       # 스크리너는 15초마다 갱신 → 10초마다 확인 (분당 6회)

# 화면 스크리너 설정과 똑같이
SCREENER_FILTERS = {
    "minTurnover": "1e6",    # 거래대금 100만 달러 이상
    "weak": "hide",          # 힘 없는 장 거르기
    "noise": "hide",         # 노이즈 제거 (보통)
    "ex": "okx",             # OKX에 있는 종목만
    # show 를 안 넣으면 위험·주의 코인은 기본으로 빠짐
}

SCREENER_RULES = {
    "아트로포스": {
        "find": "atropos",          # 스크리너 조건 id에 이 글자가 들어간 것 (시작할 때 자동으로 찾음)
        "id": None,                 # 자동으로 못 찾으면 여기에 정확한 id를 적으세요
        "tf": "5m",
        "symbols": None,            # 전 종목
        "max_age_sec": 60,          # 뜬 지 1분 이내만
        "margin": 200,              # 증거금 200 USDT (× 3배 = 포지션 600)
        "leverage": 3,
        "tp_pct": 0.06,             # 증거금 대비 +6% 익절 (3배 → 가격 +2.0%) — 스크리너 최대수익 분석 반영
        "sl_pct": 0.05,             # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
    },
    "오라클 저항": {
        "find": "oracle",           # 오라클 선 닿음 (oracle_touch)
        "id": None,
        "kinds": {"l3r", "s4r"},    # 3차 저항선(l3r) · 보조 4차 저항선(s4r) 닿음만 → 숏
                                    # 지지선도 넣으려면 "l3s", "s4s" 추가 (→ 롱)
        "tf": "5m",
        "symbols": None,            # 전 종목
        "max_age_sec": 180,         # 뜬 지 3분 이내만
        "margin": 200,              # 증거금 200 USDT (× 3배 = 포지션 600)
        "leverage": 3,
        "tp_pct": 0.10,             # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
        "sl_pct": 0.05,             # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
    },
}

HOOK_NAMES = {"cluster": "클러스터", "atropos": "아트로포스", "oracle": "오라클 저항",
              "dip_diamond": "급락매수다이아", "square": "스퀘어"}

HOOK_RULES = {
    "cluster": {            # 클러스터 저항/지지 닿음
        "enabled": False,   # ⛔ 성적 부진으로 꺼둠 (다시 켜려면 True)
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": 3,      # 증거금 300 × 3배 = 포지션 900 USDT
        "tp_pct": 0.10,     # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
        "sl_pct": 0.05,     # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
    },
    "atropos": {            # 아트로포스 (API 키가 멈췄을 때 zetro 알림으로 대신 받기)
        "margin": 200,
        "tp_pct": 0.06,     # 가격 +2.0% (3배 기준)
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": LEVERAGE,
    },
    "oracle": {             # 오라클 저항 (API 키가 멈췄을 때 zetro 알림으로 대신 받기)
        "margin": 200,
        "symbols": None,
        "intervals": {"5"},
        "sides": {"short"},   # 저항 닿음 → 숏만
        "max_age_sec": 600,
        "leverage": LEVERAGE,
    },
    "dip_diamond": {        # 급락 매수 다이아
        "enabled": False,
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": 3,
    },
    "square": {             # 스퀘어 (BTC만)
        "enabled": False,
        "symbols": {"BTCUSDT"},
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": LEVERAGE,
    },
}

# 진입할 신호 규칙
#   symbols    : 진입 허용 종목 (None이면 전 종목)
#   max_age_sec: 신호가 뜬 뒤 이 시간(초) 안에만 진입
# zetro API 신호 코드 (시작 시 받은 신호 종류 목록으로 확인한 값)
#   atropos            = 아트로포스
#   square             = 스퀘어 (kind: buy=롱 / sell=숏)
#   diamond            = 다이아 (kind: blue=급락 매수 다이아, rocket=급락 매수 로켓,
#                                 green, pink, skull 등은 다른 다이아)
#   cluster_touch      = 클러스터 (kind: res=저항 닿음, sup=지지 닿음)
#
#   type : 신호 코드 (정확히 일치)
#   kinds: 그 안의 세부 종류 (None이면 전부)
ZETRO_SIGNAL_RULES = {
    "급락매수다이아": {
        "type": "diamond",
        "kinds": {"blue"},          # 급락 매수 다이아만
        "symbols": None,            # 전 종목
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": 3,              # 증거금 300 × 3배 = 포지션 900 USDT
    },
    "아트로포스": {
        "type": "atropos",
        "kinds": None,
        "symbols": None,            # BTC 포함 전 종목
        "tfs": {"5m"},
        "max_age_sec": 60,          # 뜬 지 1분 이내만
        "leverage": 3,              # 증거금 300 × 3배 = 포지션 900 USDT
        "tp_pct": 0.10,             # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
        "sl_pct": 0.05,             # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
        "api_entry": False,         # 아트로포스는 아래 스크리너(/screener)로 진입
    },
    "스퀘어": {
        "type": "square",
        "kinds": None,
        "symbols": {"BTCUSDT"},     # BTC만
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
    "클러스터 저항": {
        "type": "cluster_touch",
        "kinds": {"res"},
        "symbols": None,
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
    "클러스터 지지": {
        "type": "cluster_touch",
        "kinds": {"sup"},
        "symbols": None,
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
}

# ----------------------------------------------------------------------------
# 기타
# ----------------------------------------------------------------------------

PORT = int(os.environ.get("PORT", 8789))   # Railway 상태 확인용
# Railway에 Volume을 붙이면 RAILWAY_VOLUME_MOUNT_PATH(예: /data)가 자동으로 생기고,
# 상태 파일(누적 성적, 처리한 신호 등)을 거기에 저장해서 재배포해도 안 지워져요.
STATE_DIR = Path(os.environ.get("RAILWAY_VOLUME_MOUNT_PATH") or ".")
STATE_DIR.mkdir(parents=True, exist_ok=True)
STATE_FILE = STATE_DIR / "r3m_tv_okx_state.json"
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


def reset_sl_on_new_commit() -> None:
    """GitHub에서 코드를 수정해 새로 배포됐을 때만 오늘 손절 횟수를 0으로 초기화.
    (서버 재시작·Railway 재시작처럼 코드가 그대로면 초기화 안 함)"""
    commit = os.environ.get("RAILWAY_GIT_COMMIT_SHA", "")
    if not commit:
        log.info("커밋 정보가 없어 손절 횟수 초기화 여부를 판단하지 않음")
        return
    last = _state.get("last_commit")
    _state["last_commit"] = commit
    if last and last != commit:
        d = _daily("daily_sl", {"count": 0})
        before = d.get("count", 0)
        d["count"] = 0
        base = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
        base["eq"] = None          # 다음 리포트 때 현재 잔고로 기준 다시 잡음
        base["notified"] = False
        save_state(_state)
        log.info("새 코드 배포(%s → %s) — 오늘 손절 횟수 %d회 → 0회로 초기화", last[:7], commit[:7], before)
        if before:
            notify("🔄 오늘 손실 한도 초기화",
                   f"코드가 새로 배포돼서 오늘 손실 한도를 다시 시작했어요.\n"
                   f"오늘 승패·실현손익·누적 성적은 그대로예요.")
    else:
        save_state(_state)


def ensure_daily_base(eq: Optional[float] = None) -> None:
    """오늘 손실 한도 기준이 될 '오늘 시작 잔고'를 하루 한 번 기록."""
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if d.get("eq") is None and eq:
        d["eq"] = float(eq)
        d["anchor_pnl"] = _daily("daily_pnl", {"total": 0.0})["total"]
        save_state(_state)
        log.info("오늘 손실 한도 기준 잔고: %.2f USDT (한도 -%.2f)", eq, eq * MAX_DAILY_LOSS_PCT)


def daily_loss_info() -> tuple:
    """(오늘 손실액, 한도액) — 한도액이 없으면 None"""
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if not d.get("eq") or not MAX_DAILY_LOSS_PCT:
        return 0.0, None
    total = _daily("daily_pnl", {"total": 0.0})["total"] - d.get("anchor_pnl", 0.0)
    return total, d["eq"] * MAX_DAILY_LOSS_PCT


def check_daily_sl_limit() -> bool:
    if MAX_DAILY_SL_COUNT and _daily("daily_sl", {"count": 0})["count"] >= MAX_DAILY_SL_COUNT:
        return True
    loss, limit = daily_loss_info()
    return limit is not None and loss <= -limit


def maybe_notify_loss_limit() -> None:
    loss, limit = daily_loss_info()
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if limit is not None and loss <= -limit and not d.get("notified"):
        d["notified"] = True
        save_state(_state)
        notify("⛔ 오늘 자동매매 중지",
               f"오늘 손실 {loss:+.2f} USDT로 한도(-{limit:.2f}, 시작 잔고의 {MAX_DAILY_LOSS_PCT * 100:.0f}%)에 도달했어요.\n"
               f"이미 열린 포지션은 익절/손절 그대로 유지되고,\n"
               f"내일 한국시간 0시에 자동으로 다시 시작해요.")


def record_sl_hit() -> None:
    d = _daily("daily_sl", {"count": 0})
    d["count"] += 1
    save_state(_state)
    log.warning("오늘 손절 %d회째 발생", d["count"])
    if MAX_DAILY_SL_COUNT and d["count"] == MAX_DAILY_SL_COUNT:
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


def _stats_start_ms() -> int:
    dt = datetime.strptime(STATS_START_KST, "%Y-%m-%d %H:%M").replace(tzinfo=KST)
    return int(dt.timestamp() * 1000)


def _cum_stats() -> dict:
    """누적 성적. 시작 시각을 바꾸면 자동으로 새로 시작."""
    st = _state.setdefault("cum_stats", {})
    if st.get("start") != STATS_START_KST:
        st.clear()
        st.update({"start": STATS_START_KST, "win": 0, "loss": 0, "pnl": 0.0,
                   "best": None, "worst": None, "by_source": {}})
    return st


def merge_split_sources() -> None:
    """'아트로포스 롱', '아트로포스 숏', '아트로포스 (나누기 전)' 처럼 나뉜 기록을 신호별로 다시 합침."""
    st = _cum_stats()
    bs = st.get("by_source", {})
    for name in list(bs):
        base = name
        for suf in (" (나누기 전)", " 롱", " 숏"):
            if base.endswith(suf):
                base = base[: -len(suf)]
        if base != name:
            src = bs.pop(name)
            dst = bs.setdefault(base, {"win": 0, "loss": 0, "pnl": 0.0})
            dst["win"] += src.get("win", 0)
            dst["loss"] += src.get("loss", 0)
            dst["pnl"] += src.get("pnl", 0.0)
    save_state(_state)


def purge_excluded_sources() -> None:
    """STATS_EXCLUDE_SOURCES 에 있는 신호 기록을 누적 성적에서 지우고 합계에서도 뺌 (한 번만 적용됨)."""
    st = _cum_stats()
    for name in list(st.get("by_source", {})):
        if name in STATS_EXCLUDE_SOURCES:
            src = st["by_source"].pop(name)
            st["win"] -= src.get("win", 0)
            st["loss"] -= src.get("loss", 0)
            st["pnl"] -= src.get("pnl", 0.0)
            log.info("누적 성적에서 %s 기록 삭제 (%d승 %d패, %+.2f USDT)",
                     name, src.get("win", 0), src.get("loss", 0), src.get("pnl", 0.0))
    save_state(_state)


def record_cum_trade(source: str, pnl: float) -> dict:
    st = _cum_stats()
    if source in STATS_EXCLUDE_SOURCES:
        return st
    key = "win" if pnl >= 0 else "loss"
    st[key] += 1
    st["pnl"] += pnl
    st["best"] = pnl if st["best"] is None else max(st["best"], pnl)
    st["worst"] = pnl if st["worst"] is None else min(st["worst"], pnl)
    src = st["by_source"].setdefault(source, {"win": 0, "loss": 0, "pnl": 0.0})
    src[key] += 1
    src["pnl"] += pnl
    save_state(_state)
    return st


def format_cum_stats() -> str:
    st = _cum_stats()
    n = st["win"] + st["loss"]
    if n == 0:
        return f"📒 누적 성적 ({st['start']} 부터)\n아직 종료된 거래 없음"
    rate = st["win"] / n * 100
    lines = [
        f"📒 누적 성적 ({st['start']} 부터)",
        f"🏆 {st['win']}승 {st['loss']}패 (승률 {rate:.0f}%)",
        f"💵 누적 실현손익: {st['pnl']:+.2f} USDT",
        f"📊 거래당 평균: {st['pnl'] / n:+.2f} USDT",
        f"⬆️ 최고 {st['best']:+.2f} / ⬇️ 최저 {st['worst']:+.2f}",
    ]
    for name, src in st["by_source"].items():
        m = src["win"] + src["loss"]
        lines.append(f"  · {name}: {src['win']}승 {src['loss']}패, {src['pnl']:+.2f} USDT"
                     f" (승률 {src['win'] / m * 100:.0f}%)" if m else f"  · {name}: -")
    return "\n".join(lines)


# ----------------------------------------------------------------------------
# 매매 기록지
# ----------------------------------------------------------------------------

def _journal_day(date: str) -> dict:
    j = _state.setdefault("journal", {})
    return j.setdefault(date, {"win": 0, "be": 0, "loss": 0, "pnl": 0.0, "by_source": {},
                               "start_eq": None, "end_eq": None})


BE_MOVE_PCT = 0.009   # 평균 청산가가 진입가에서 0.9% 안쪽이면 "본절" (분할 익절 후 나머지가 진입가 근처에서 끝난 경우)


def classify_close(pnl: float, row: Optional[dict]) -> str:
    """OKX 포지션 기록으로 익절/본절/손절 구분."""
    if pnl < 0:
        return "loss"
    if pnl < 1.0:
        return "be"
    try:
        o = float(row.get("openAvgPx") or 0)
        c = float(row.get("closeAvgPx") or 0)
        if o and c:
            long_ = str(row.get("direction", "")).lower() == "long"
            move = (c - o) / o if long_ else (o - c) / o
            if move < BE_MOVE_PCT:
                return "be"
    except Exception:  # noqa: BLE001
        pass
    return "win"


def journal_record(inst_id: str, source: str, side: Optional[str], pnl: float,
                   kind: Optional[str] = None) -> str:
    """거래 1건을 기록지에 남김. 결과 종류(익절/본절/손절)를 돌려줌."""
    kind = kind or ("loss" if pnl < 0 else ("be" if pnl < 1.0 else "win"))
    day = _journal_day(_today())
    day[kind] += 1
    day["pnl"] += pnl
    src = day["by_source"].setdefault(source, {"win": 0, "be": 0, "loss": 0, "pnl": 0.0})
    src[kind] += 1
    src["pnl"] += pnl
    log_list = _state.setdefault("trade_log", [])
    log_list.append({"t": int(time.time() * 1000), "inst": inst_id, "src": source,
                     "side": side, "pnl": round(pnl, 4), "kind": kind})
    if len(log_list) > 1000:
        del log_list[:-1000]
    j = _state["journal"]
    if len(j) > 400:
        for k in sorted(j)[:-400]:
            j.pop(k, None)
    save_state(_state)
    return kind


def journal_set_equity(cash: float) -> None:
    day = _journal_day(_today())
    if day.get("start_eq") is None:
        day["start_eq"] = round(cash, 2)
    day["end_eq"] = round(cash, 2)
    save_state(_state)


def sync_transfers() -> None:
    """OKX 이체 내역을 읽어서 입금(거래 계정으로 들어옴)·출금(나감)을 날짜별 기록지에 남김."""
    try:
        bills = _executor.get_transfer_bills()
    except Exception as e:  # noqa: BLE001
        if not _state.get("_transfer_warned"):
            log.warning("이체 내역 조회 실패(API 키에 읽기 권한이 있는지 확인): %s", format_okx_error(e))
            _state["_transfer_warned"] = True
        return
    new_items = []
    with _state_lock:
        seen = _state.setdefault("transfer_seen", [])
        first = not seen and not _state.get("transfer_init")
        today = _today()
        for b in sorted(bills, key=lambda x: int(x.get("ts", 0) or 0)):
            bid = str(b.get("billId", ""))
            if not bid or bid in seen:
                continue
            seen.append(bid)
            amt = float(b.get("balChg", 0) or 0)
            ts = int(b.get("ts", 0) or 0)
            date = datetime.fromtimestamp(ts / 1000, KST).strftime("%Y-%m-%d")
            if first and date != today:
                continue   # 처음 켰을 때는 오늘 것만 기록
            day = _journal_day(date)
            if amt >= 0:
                day["dep"] = round(day.get("dep", 0.0) + amt, 2)
            else:
                day["wd"] = round(day.get("wd", 0.0) + amt, 2)
            new_items.append((date, amt))
        _state["transfer_init"] = True
        if len(seen) > 500:
            del seen[:-500]
        save_state(_state)
    for date, amt in new_items:
        if amt < 0:
            notify("🏦 출금 기록 (OKX)", f"거래 계정에서 {amt:.2f} USDT 나갔어요.\n기록지 {date} 칸에 출금으로 남겼어요.")
        else:
            notify("🏦 입금 기록 (OKX)", f"거래 계정으로 +{amt:.2f} USDT 들어왔어요.\n기록지 {date} 칸에 입금으로 남겼어요.")


# 지난 날짜를 OKX 거래 내역으로 다시 계산해서 기록지에 채움 (한 번만 실행)
BACKFILL_DATES = ["2026-11-19"]


def backfill_journal() -> None:
    with _state_lock:
        done = set(_state.get("backfilled_v2", []))
    todo = [d for d in BACKFILL_DATES if d not in done]
    if not todo:
        return
    oldest = min(todo)
    start_ms = int(datetime.strptime(oldest, "%Y-%m-%d").replace(tzinfo=KST).timestamp() * 1000)
    rows, after = [], None
    try:
        for _ in range(30):   # 최대 3,000건
            page = _executor.get_positions_history(after)
            if not page:
                break
            rows.extend(page)
            last = min(int(r.get("uTime", 0) or 0) for r in page)
            if last < start_ms:
                break
            after = last
    except Exception as e:  # noqa: BLE001
        log.warning("지난 기록 불러오기 실패: %s", format_okx_error(e))
        return

    agg = {d: {"win": 0, "be": 0, "loss": 0, "pnl": 0.0} for d in todo}
    seen = set()
    for r in rows:
        key = (r.get("posId"), r.get("uTime"))
        if key in seen:
            continue
        seen.add(key)
        if str(r.get("type", "")) == "1":      # 부분 청산 중인 기록은 제외 (완전히 끝난 것만)
            continue
        if r.get("instId") in BOT_EXCLUDE_SYMBOLS:   # 수동 거래 종목 제외
            continue
        date = datetime.fromtimestamp(int(r.get("uTime", 0) or 0) / 1000, KST).strftime("%Y-%m-%d")
        if date not in agg:
            continue
        pnl = float(r.get("pnl", 0) or 0)
        kind = classify_close(pnl, r)
        agg[date][kind] += 1
        agg[date]["pnl"] += pnl

    with _state_lock:
        for d, a in agg.items():
            day = _journal_day(d)
            day.update(win=a["win"], be=a["be"], loss=a["loss"], pnl=round(a["pnl"], 4))
            day["backfilled"] = True
            log.info("기록지 %s 다시 계산: 익절 %d / 본절 %d / 손절 %d, %+.2f (BTC·ETH 제외)",
                     d, a["win"], a["be"], a["loss"], a["pnl"])
        _state["backfilled_v2"] = sorted(done | set(todo))
        save_state(_state)


def seed_journal_today() -> None:
    """기록지가 처음 생길 때, 오늘 이미 쌓인 성적을 오늘 칸에 넣어둠."""
    if _state.get("journal"):
        return
    wl = _daily("daily_win_loss", {"win": 0, "loss": 0})
    pnl = _daily("daily_pnl", {"total": 0.0})["total"]
    day = _journal_day(_today())
    day["win"] = wl.get("win", 0)
    day["loss"] = wl.get("loss", 0)
    day["pnl"] = pnl
    save_state(_state)


def report_url() -> str:
    domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN") or "r3m-tv-webhook-production-abf1.up.railway.app"
    return f"https://{domain}{REPORT_PATH}"


def format_day_summary(date: str) -> str:
    day = _state.get("journal", {}).get(date)
    if not day:
        return f"🗓 {date}\n거래 없음"
    n = day["win"] + day["be"] + day["loss"]
    pct = (day["pnl"] / DAILY_TARGET_USD * 100) if DAILY_TARGET_USD else 0
    lines = [
        f"🗓 {date} 하루 정산",
        f"🔢 거래 {n}번",
        f"✅ 익절 {day['win']}회",
        f"➖ 본절 {day['be']}회",
        f"🛑 손절 {day['loss']}회",
        f"💵 실현손익: {day['pnl']:+.2f} USDT",
        f"🎯 목표 {DAILY_TARGET_USD:.0f} 대비 {pct:.0f}%",
    ]
    dep, wd = day.get("dep", 0.0), day.get("wd", 0.0)
    if dep or wd:
        lines.append(f"🏦 입출금: 입금 +{dep:.2f} / 출금 {wd:.2f} → 합계 {dep + wd:+.2f}")
    if day.get("start_eq") is not None and day.get("end_eq") is not None:
        net = day["end_eq"] - day["start_eq"] - dep - wd
        lines.append(f"💼 잔고(현금): {day['start_eq']:.2f} → {day['end_eq']:.2f}"
                     f" (입출금 빼면 {net:+.2f})")
    acct = _state.get("last_account")
    if acct:
        lines.append(f"💰 총 잔액: {acct['eq']:.2f} USDT (미실현 {acct['upl']:+.2f})")
    for name, src in day["by_source"].items():
        lines.append(f"  · {name}: 익절 {src['win']}회 · 본절 {src['be']}회 · 손절 {src['loss']}회, {src['pnl']:+.2f}")
    lines.append(f"📒 기록지: {report_url()}")
    return "\n".join(lines)


def daily_close_loop():
    """한국시간 0시가 지나면 어제 하루 정산을 텔레그램으로 보냄."""
    while True:
        try:
            today = _today()
            with _state_lock:
                last = _state.get("journal_last_day")
                if last is None:
                    _state["journal_last_day"] = today
                    save_state(_state)
                    last = today
            if last != today:
                with _state_lock:
                    text = format_day_summary(last)
                    _state["journal_last_day"] = today
                    save_state(_state)
                notify("📒 하루 정산 (OKX)", text)
        except Exception as e:  # noqa: BLE001
            log.warning("하루 정산 오류: %s", e)
        time.sleep(60)


def render_report_html() -> bytes:
    with _state_lock:
        journal = json.loads(json.dumps(_state.get("journal", {})))
        trades = list(_state.get("trade_log", []))[-60:]
    days = sorted(journal.items(), reverse=True)
    esc = html.escape
    with _state_lock:
        acct = dict(_state.get("last_account") or {})

    def money(v):
        cls = "pos" if v > 0 else ("neg" if v < 0 else "")
        return f'<span class="{cls}">{v:+.2f}</span>'

    # 합계 (전체 / 이번 주 / 이번 달)
    now = datetime.now(KST)
    week_start = (now - timedelta(days=now.weekday())).strftime("%Y-%m-%d")
    month = now.strftime("%Y-%m")
    def total(filter_fn):
        t = {"n": 0, "win": 0, "be": 0, "loss": 0, "pnl": 0.0, "days": 0, "dep": 0.0, "wd": 0.0}
        for d, v in journal.items():
            if filter_fn(d):
                t["days"] += 1
                for k in ("win", "be", "loss"):
                    t[k] += v[k]
                t["pnl"] += v["pnl"]
                t["dep"] += v.get("dep", 0.0)
                t["wd"] += v.get("wd", 0.0)
        t["n"] = t["win"] + t["be"] + t["loss"]
        return t
    cards = [("이번 주", total(lambda d: d >= week_start)),
             ("이번 달", total(lambda d: d.startswith(month))),
             ("전체 기록", total(lambda d: True))]
    card_html = ""
    if acct:
        upd = datetime.fromtimestamp(acct["t"] / 1000, KST).strftime("%m-%d %H:%M")
        card_html += (f'<div class="card main"><div class="ct">💰 총 잔액 (평가 기준)</div>'
                      f'<div class="cv">{acct["eq"]:,.2f} <small>USDT</small></div>'
                      f'<div class="cs">현금 {acct["eq"] - acct["upl"]:,.2f} · 미실현 {money(acct["upl"])}'
                      f'<br>{upd} 기준</div></div>')
    for title, t in cards:
        avg = t["pnl"] / t["days"] if t["days"] else 0
        card_html += (f'<div class="card"><div class="ct">{title}</div>'
                      f'<div class="cv">{money(t["pnl"])} <small>USDT</small></div>'
                      f'<div class="cs">{t["days"]}일 · 거래 {t["n"]}번'
                      f'<br>✅ 익절 {t["win"]}회<br>➖ 본절 {t["be"]}회<br>🛑 손절 {t["loss"]}회'
                      f'<br>하루 평균 {avg:+.2f}'
                      + '</div></div>')

    rows = ""
    for d, v in days:
        n = v["win"] + v["be"] + v["loss"]
        pct = (v["pnl"] / DAILY_TARGET_USD * 100) if DAILY_TARGET_USD else 0
        bar = max(0, min(100, pct))
        eq = (f'{v["start_eq"]:.0f} → {v["end_eq"]:.0f}'
              if v.get("start_eq") is not None and v.get("end_eq") is not None else "-")
        tr = []
        if v.get("dep"):
            tr.append(f'<span class="pos">입금 +{v["dep"]:.0f}</span>')
        if v.get("wd"):
            tr.append(f'<span class="neg">출금 {v["wd"]:.0f}</span>')
        if v.get("dep") and v.get("wd"):
            net_tr = v["dep"] + v["wd"]
            tr.append(f'<b>합계 {money(net_tr)}</b>')
        tr_html = "<br>".join(tr) or '<span class="muted">-</span>'
        srcs = " · ".join(f'{esc(k)} {x["pnl"]:+.1f}' for k, x in v["by_source"].items())
        rows += (f'<tr><td>{esc(d[5:])}</td><td>{n}</td><td>✅ 익절 {v["win"]}회<br>➖ 본절 {v["be"]}회<br>🛑 손절 {v["loss"]}회</td>'
                 f'<td>{money(v["pnl"])}</td>'
                 f'<td><div class="bar"><i style="width:{bar:.0f}%"></i></div>{pct:.0f}%</td>'
                 f'<td class="muted">{eq}</td><td class="small">{tr_html}</td><td class="muted small">{srcs}</td></tr>')
    if not rows:
        rows = '<tr><td colspan="8" class="muted">아직 기록이 없어요</td></tr>'

    trows = ""
    for t in reversed(trades):
        ts = datetime.fromtimestamp(t["t"] / 1000, KST).strftime("%m-%d %H:%M")
        kind = {"win": "✅ 익절", "be": "➖ 본절", "loss": "🛑 손절"}.get(t["kind"], "")
        side = {"L": "롱", "S": "숏"}.get(t.get("side"), "")
        trows += (f'<tr><td>{ts}</td><td>{esc(t["inst"].replace("-USDT-SWAP", ""))}</td>'
                  f'<td>{esc(t["src"] or "")} {side}</td><td>{kind}</td><td>{money(t["pnl"])}</td></tr>')
    if not trows:
        trows = '<tr><td colspan="5" class="muted">아직 거래가 없어요</td></tr>'

    page = f"""<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="60"><title>매매 기록지</title>
<style>
:root{{--bg:#f6f7f9;--fg:#15171a;--card:#fff;--muted:#6b7280;--line:#e5e7eb;--pos:#0f9d58;--neg:#d93025;--acc:#3b6cff}}
@media (prefers-color-scheme:dark){{:root{{--bg:#0f1115;--fg:#e8eaed;--card:#181b21;--muted:#9aa0a6;--line:#2a2e36;--pos:#34c77b;--neg:#ff6b6b;--acc:#7b9bff}}}}
body{{margin:0;background:var(--bg);color:var(--fg);font:14px/1.5 -apple-system,BlinkMacSystemFont,"Apple SD Gothic Neo","Noto Sans KR",sans-serif}}
.wrap{{max-width:900px;margin:0 auto;padding:16px}}
h1{{font-size:20px;margin:4px 0 2px}} .sub{{color:var(--muted);font-size:12px;margin-bottom:14px}}
.cards{{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:10px;margin-bottom:18px}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px}}
.ct{{color:var(--muted);font-size:12px}} .card.main{{border-color:var(--acc)}} .cv{{font-size:22px;font-weight:700;margin:2px 0}} .cs{{color:var(--muted);font-size:12px}}
h2{{font-size:15px;margin:18px 0 8px}}
.tbl{{background:var(--card);border:1px solid var(--line);border-radius:12px;overflow-x:auto}}
table{{width:100%;border-collapse:collapse;white-space:nowrap}}
th,td{{padding:9px 10px;border-bottom:1px solid var(--line);text-align:left}} th{{color:var(--muted);font-weight:600;font-size:12px}}
tr:last-child td{{border-bottom:0}} .pos{{color:var(--pos);font-weight:600}} .neg{{color:var(--neg);font-weight:600}}
.muted{{color:var(--muted)}} .small{{font-size:12px}}
.bar{{display:inline-block;width:60px;height:6px;background:var(--line);border-radius:3px;margin-right:6px;vertical-align:middle;overflow:hidden}}
.bar i{{display:block;height:100%;background:var(--acc)}}
</style></head><body><div class="wrap">
<h1>📒 매매 기록지</h1>
<div class="sub">봇 거래만 기록 (수동 거래 제외) · 하루 기준 한국시간 0시 · 목표 하루 {DAILY_TARGET_USD:.0f} USDT · 1분마다 새로고침</div>
<div class="cards">{card_html}</div>
<h2>일별 기록</h2>
<div class="tbl"><table><tr><th>날짜</th><th>거래</th><th>결과</th><th>실현손익</th><th>목표 달성</th><th>잔고(현금)</th><th>입출금</th><th>신호별</th></tr>{rows}</table></div>
<h2>최근 거래</h2>
<div class="tbl"><table><tr><th>시간</th><th>종목</th><th>신호</th><th>결과</th><th>손익</th></tr>{trows}</table></div>
</div></body></html>"""
    return page.encode("utf-8")


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

    def get_24h_volume_usd(self, inst_id: str) -> float:
        """최근 24시간 거래대금(USD). volCcy24h(코인 수량) × 현재가."""
        data = self._request("GET", "/api/v5/market/ticker", params={"instId": inst_id})
        t = data["data"][0]
        return float(t.get("volCcy24h") or 0) * float(t.get("last") or 0)

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

    def get_positions_history(self, after_ms: Optional[int] = None) -> list:
        params = {"instType": "SWAP", "limit": "100"}
        if after_ms:
            params["after"] = str(after_ms)   # 이 시각보다 이전 기록
        data = self._request("GET", "/api/v5/account/positions-history", params=params)
        return data.get("data", []) or []

    def get_transfer_bills(self) -> list:
        """거래 계정 USDT 이체 내역 (자금 계정 ↔ 거래 계정). 최근 7일, 최신순."""
        data = self._request("GET", "/api/v5/account/bills",
                             params={"ccy": "USDT", "type": "1", "limit": "100"})
        return data.get("data", []) or []

    def get_position_size(self, inst_id: str) -> float:
        data = self._request("GET", "/api/v5/account/positions", params={"instId": inst_id})
        return sum(abs(float(p.get("pos", 0) or 0)) for p in data.get("data", []))

    def get_open_positions(self) -> list:
        data = self._request("GET", "/api/v5/account/positions")
        return [p for p in data.get("data", []) if float(p.get("pos", 0)) != 0]

    # -- 포지션 관리용 ------------------------------------------------------

    def round_px(self, inst_id: str, px: float) -> str:
        tick = float(self.get_instrument(inst_id)["tickSz"])
        n = round(px / tick) * tick
        decimals = max(0, -int(math.floor(math.log10(tick)))) if tick < 1 else 0
        return f"{n:.{decimals}f}"

    def round_sz_down(self, inst_id: str, sz: float) -> float:
        inst = self.get_instrument(inst_id)
        lot = float(inst["lotSz"])
        q = math.floor(sz / lot + 1e-9) * lot
        decimals = max(0, -int(math.floor(math.log10(lot)))) if lot < 1 else 0
        q = round(q, decimals)
        return q if q >= float(inst["minSz"]) else 0.0

    def pending_tpsl_ids(self, inst_id: str) -> list:
        data = self._request("GET", "/api/v5/trade/orders-algo-pending",
                             params={"instType": "SWAP", "instId": inst_id, "ordType": "conditional,oco"})
        return [d["algoId"] for d in data.get("data", []) if d.get("algoId")]

    def cancel_algos(self, inst_id: str, algo_ids: list) -> None:
        if not algo_ids:
            return
        self._request("POST", "/api/v5/trade/cancel-algos",
                      body=[{"algoId": a, "instId": inst_id} for a in algo_ids])

    def replace_tpsl(self, inst_id: str, side: str, tp_px: float, sl_px: float) -> str:
        """포지션 전체에 걸리는 익절/손절 주문을 새로 걸고, 기존 익절/손절 주문은 취소."""
        old = self.pending_tpsl_ids(inst_id)
        body = {
            "instId": inst_id,
            "tdMode": TD_MODE,
            "side": "buy" if side == "S" else "sell",
            "ordType": "oco",
            "closeFraction": "1",
            "reduceOnly": True,
            "tpTriggerPx": self.round_px(inst_id, tp_px),
            "tpOrdPx": "-1",
            "slTriggerPx": self.round_px(inst_id, sl_px),
            "slOrdPx": "-1",
        }
        data = self._request("POST", "/api/v5/trade/order-algo", body=body)
        new_id = data["data"][0].get("algoId", "")
        try:
            self.cancel_algos(inst_id, [a for a in old if a != new_id])
        except Exception as e:  # noqa: BLE001
            log.warning("%s 기존 익절/손절 주문 취소 실패(새 주문은 정상): %s", inst_id, e)
        return new_id

    def close_partial(self, inst_id: str, side: str, sz: float) -> None:
        self._request("POST", "/api/v5/trade/order", body={
            "instId": inst_id, "tdMode": TD_MODE,
            "side": "buy" if side == "S" else "sell",
            "ordType": "market", "sz": str(sz), "reduceOnly": True,
        })


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
            prev = (_state.get("positions", {}).get(inst_id) or [{}])[0]
            new_positions[inst_id] = [{
                "side": "L" if pos_val > 0 else "S",
                "qty": abs(pos_val),
                "entry": float(p.get("avgPx", 0) or 0),
                "source": prev.get("source"),
                "opened_at": prev.get("opened_at"),
                "tp_px": prev.get("tp_px"),
                "be_done": prev.get("be_done", False),
                "partial_done": prev.get("partial_done", False),
                "step_done": prev.get("step_done", False),
                # 봇이 진입한 기록(tp_px)이 없으면 수동 포지션으로 보고 성적·손절 횟수에서 제외
                "manual": (not prev.get("tp_px")) or inst_id in BOT_EXCLUDE_SYMBOLS,
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

def enter_position(symbol: str, side_raw: str, leverage: int = LEVERAGE,
                   tp_pct: float = TAKE_PROFIT_PCT, sl_pct: float = STOP_LOSS_PCT,
                   source: str = "기타", margin: Optional[float] = None) -> None:
    inst_id = normalize_symbol(symbol)
    side = "S" if side_raw == "short" else "L"
    if side == "L" and not LONG_ENTRY_ENABLED:
        log.info("롱 진입 꺼짐 — %s %s 롱 신호 무시", source, inst_id)
        return
    if inst_id in BOT_EXCLUDE_SYMBOLS:
        log.info("%s 은 수동 전용 종목이라 봇 진입 안 함", inst_id)
        return

    # OKX에 이미 이 종목 포지션이 있으면(직접 들어간 수동 포지션 등) 봇은 들어가지 않음
    # → 같은 종목은 OKX에서 하나로 합쳐져서, 봇 손절·익절이 수동 물량까지 정리해버리기 때문
    try:
        live_sz = _executor.get_position_size(inst_id)
    except Exception as e:  # noqa: BLE001
        log.warning("%s 포지션 확인 실패 — 안전하게 진입 안 함: %s", inst_id, format_okx_error(e))
        return
    if live_sz > 0:
        with _state_lock:
            ents = _state.get("positions", {}).get(inst_id) or []
            if not any(x.get("tp_px") for x in ents):
                _state.setdefault("positions", {})[inst_id] = [{
                    "side": None, "qty": live_sz, "manual": True}]
                save_state(_state)
                log.info("%s 에 직접 들어간 포지션이 있어서 봇 진입 안 함", inst_id)
                return

    with _state_lock:
        if check_daily_sl_limit():
            log.info("오늘 손실 한도 도달로 신규 진입 스킵: %s", inst_id)
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
        pending_entry = {"side": side, "qty": None, "entry": None, "pending": True,
                         "source": source, "opened_at": int(time.time() * 1000)}
        entries.append(pending_entry)
        save_state(_state)

    def _release():
        with _state_lock:
            ents = _state.setdefault("positions", {}).get(inst_id, [])
            if pending_entry in ents:
                ents.remove(pending_entry)
            save_state(_state)
            return get_trade_stats()

    # 방향별 배율 적용 (가격 기준 익절·손절 거리는 그대로 유지)
    forced = LONG_LEVERAGE if side == "L" else SHORT_LEVERAGE
    if forced and forced != leverage:
        tp_pct = tp_pct * forced / leverage
        sl_pct = sl_pct * forced / leverage
        leverage = forced
    base_margin = margin if margin else MARGIN_USDT
    notional = SYMBOL_MARGIN_OVERRIDE.get(inst_id, base_margin) * leverage
    try:
        ref_price = _executor.get_mark_price(inst_id)
        qty = _executor.open_position(inst_id, side, notional, ref_price,
                                      leverage, tp_pct, sl_pct)
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
        if side == "S":
            pending_entry["tp_px"] = ref_price * (1 - tp_pct / leverage)
        else:
            pending_entry["tp_px"] = ref_price * (1 + tp_pct / leverage)
        pending_entry["be_done"] = False
        pending_entry["partial_done"] = False
        pending_entry["step_done"] = False
        pending_entry.pop("pending", None)
        save_state(_state)
        stats = record_trade_result(True)

    label = "🔴 숏" if side == "S" else "🟢 롱"
    notify("🚀 신규 진입 (OKX)",
           f"{label} 진입 완료 · {source}\n━━━━━━━━━━\n📊 종목: {inst_id}\n📦 수량: {qty}\n"
           f"💰 진입가: {ref_price}\n━━━━━━━━━━\n"
           f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")


# ----------------------------------------------------------------------------
# zetro 신호 조회 루프
# ----------------------------------------------------------------------------

def _zetro_signal_key(sig: dict) -> str:
    return f"{sig.get('symbol')}|{sig.get('type')}|{sig.get('tf')}|{sig.get('at')}|{sig.get('side')}"


def _match_rule(sig: dict) -> Optional[str]:
    t = str(sig.get("type", "")).lower()
    k = str(sig.get("kind", "")).lower()
    for name, rule in ZETRO_SIGNAL_RULES.items():
        if t != rule["type"]:
            continue
        if rule["kinds"] and k not in rule["kinds"]:
            continue
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


def zetro_log_types() -> None:
    """시작할 때 zetro 신호 종류 목록을 한 번 받아서 로그에 남김 (type 이름 확인용)."""
    try:
        resp = requests.get(ZETRO_SIGNALS_URL.replace("/signals", "/types"),
                            headers={"Authorization": f"Bearer {ZETRO_API_KEY}"}, timeout=10)
        log.info("zetro 신호 종류 목록(%s): %s", resp.status_code, resp.text[:3000])
    except Exception as e:  # noqa: BLE001
        log.info("zetro 신호 종류 목록 조회 실패(무시): %s", e)


def zetro_poll_loop():
    zetro_log_types()
    with _state_lock:
        seen_list = _state.setdefault("zetro_seen", [])
    seen = set(seen_list)
    first_run = not seen   # 처음 켰을 때 이미 떠 있던 신호는 기록만 하고 진입 안 함
    error_streak = 0

    log.info("zetro 신호 조회 시작 (%s초 간격, API 진입: %s)", ZETRO_POLL_SECONDS,
             "ON" if ZETRO_API_ENTRY_ENABLED else "OFF(기록만)")

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

                log.info("zetro 새 신호: %s %s type=%s tf=%s | 원본=%s", symbol, side, sig_type, tf,
                         json.dumps(sig, ensure_ascii=False)[:500])

                rule_name = _match_rule(sig)
                if not rule_name:
                    continue   # 정한 신호가 아니면 진입 안 함
                rule = ZETRO_SIGNAL_RULES[rule_name]
                if rule["symbols"] and _plain_symbol(symbol) not in rule["symbols"]:
                    log.info("%s 신호는 %s 종목 진입 안 함: %s", rule_name, symbol, sig)
                    continue
                if rule.get("tfs") and tf.lower() not in rule["tfs"]:
                    log.info("%s 신호가 %s봉이라 진입 안 함 (5분봉만): %s", rule_name, tf, sig)
                    continue
                if side not in ("long", "short") or not symbol:
                    log.info("zetro 신호 형식 불명확(스킵): %s", sig)
                    continue
                age_sec = (now_ms - at) / 1000 if at else None
                if age_sec is None or age_sec > rule["max_age_sec"]:
                    log.info("%s 신호가 %s초 지나서 스킵: %s", rule_name,
                             f"{age_sec:.0f}" if age_sec is not None else "?", sig)
                    continue

                inst_id = normalize_symbol(symbol)
                try:
                    vol_usd = _executor.get_24h_volume_usd(inst_id)
                except Exception as e:  # noqa: BLE001
                    log.info("%s 거래대금 조회 실패(OKX에 없는 종목일 수 있음) — 진입 안 함: %s", inst_id, format_okx_error(e))
                    continue
                if vol_usd < MIN_24H_VOLUME_USD:
                    log.info("%s 24시간 거래대금 $%s < $%s 이라 진입 안 함", inst_id,
                             f"{vol_usd:,.0f}", f"{MIN_24H_VOLUME_USD:,.0f}")
                    continue

                if not ZETRO_API_ENTRY_ENABLED or not rule.get("api_entry"):
                    log.info("API 진입 꺼짐 — %s %s %s 신호 기록만 함", rule_name, symbol, side)
                    continue

                log.info("zetro %s 신호로 진입 시도: %s %s (%s)", rule_name, symbol, side, tf)
                try:
                    enter_position(symbol, side, rule.get("leverage", LEVERAGE),
                                   rule.get("tp_pct", TAKE_PROFIT_PCT), rule.get("sl_pct", STOP_LOSS_PCT),
                                   source=rule_name)
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
# zetro 스크리너 조회 루프
# ----------------------------------------------------------------------------

def _collect_screener_ids(obj, out: set, under_screener: bool = False) -> None:
    """/types 응답에서 'screener' 칸 아래에 있는 조건 id들을 모음."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            flag = under_screener or str(k).lower() == "screener"
            if flag and str(k).lower() in ("id", "screener") and isinstance(v, str):
                out.add(v)
            _collect_screener_ids(v, out, flag)
    elif isinstance(obj, list):
        for v in obj:
            if under_screener and isinstance(v, str):
                out.add(v)
            _collect_screener_ids(v, out, under_screener)


def resolve_screener_ids() -> None:
    try:
        resp = requests.get(ZETRO_SIGNALS_URL.replace("/signals", "/types"),
                            headers={"Authorization": f"Bearer {ZETRO_API_KEY}"}, timeout=10)
        data = resp.json()
    except Exception as e:  # noqa: BLE001
        log.warning("스크리너 조건 목록 조회 실패: %s", e)
        data = {}
    ids: set = set()
    _collect_screener_ids(data, ids)
    log.info("스크리너 조건 id 목록: %s", ", ".join(sorted(ids)) or "(못 찾음)")
    for name, rule in SCREENER_RULES.items():
        if rule.get("id"):
            continue
        matches = sorted(i for i in ids if rule["find"].lower() in i.lower())
        # 롱/숏이 따로 있어도 같이 받도록 쉼표로 묶음 (최대 4개)
        rule["id"] = ",".join(matches[:4]) if matches else rule["find"]
        log.info("스크리너 %s 조건 id = %s%s", name, rule["id"], "" if matches else " (목록에 없어 기본값 사용)")


def _screener_fetch(cond_id: str, tf: str) -> list:
    params = {"type": cond_id, "tf": tf, "limit": "100", **SCREENER_FILTERS}
    resp = requests.get(ZETRO_SCREENER_URL, headers={"Authorization": f"Bearer {ZETRO_API_KEY}"},
                        params=params, timeout=10)
    if resp.status_code != 200:
        raise RuntimeError(f"스크리너 응답 {resp.status_code}: {resp.text[:200]}")
    return resp.json().get("items", []) or []


def screener_poll_loop():
    resolve_screener_ids()
    with _state_lock:
        seen_list = _state.setdefault("screener_seen", [])
    seen = set(seen_list)
    first_run = {name: True for name in SCREENER_RULES}
    error_streak = 0
    log.info("스크리너 조회 시작 (%s초 간격, 필터: %s)", SCREENER_POLL_SECONDS, SCREENER_FILTERS)

    while True:
        try:
            new_keys = []
            now_ms = time.time() * 1000
            for name, rule in SCREENER_RULES.items():
                items = _screener_fetch(rule["id"], rule["tf"])
                for it in sorted(items, key=lambda x: x.get("at") or 0):
                    symbol = str(it.get("symbol", "")).upper()
                    side = str(it.get("side", "")).lower()
                    at = it.get("at") or 0
                    key = f"{name}|{symbol}|{it.get('kind')}|{it.get('tf')}|{at}"
                    if key in seen:
                        continue
                    seen.add(key)
                    new_keys.append(key)
                    if first_run[name]:
                        continue   # 봇 켤 때 이미 떠 있던 건 진입 안 함

                    log.info("스크리너 %s 새 종목: %s %s | 원본=%s", name, symbol, side,
                             json.dumps(it, ensure_ascii=False)[:400])
                    if rule.get("kinds") and str(it.get("kind", "")).lower() not in rule["kinds"]:
                        log.info("스크리너 %s: %s kind=%s 라 진입 안 함", name, symbol, it.get("kind"))
                        continue
                    if rule["symbols"] and symbol not in rule["symbols"]:
                        continue
                    if side not in ("long", "short") or not symbol:
                        continue
                    age = (now_ms - at) / 1000 if at else None
                    if age is None or age > rule["max_age_sec"]:
                        log.info("스크리너 %s: %s 뜬 지 %s초라 진입 안 함", name, symbol,
                                 f"{age:.0f}" if age is not None else "?")
                        continue
                    if not SCREENER_ENTRY_ENABLED:
                        log.info("스크리너 진입 꺼짐 — %s %s %s 기록만 함", name, symbol, side)
                        continue
                    log.info("스크리너 %s 신호로 진입 시도: %s %s", name, symbol, side)
                    try:
                        enter_position(symbol, side, rule["leverage"], rule["tp_pct"], rule["sl_pct"],
                                       source=name, margin=rule.get("margin"))
                    except Exception as e:  # noqa: BLE001
                        log.error("스크리너 진입 처리 실패: %s", e)
                first_run[name] = False

            if new_keys:
                with _state_lock:
                    seen_list = _state.setdefault("screener_seen", [])
                    seen_list.extend(new_keys)
                    if len(seen_list) > 2000:
                        del seen_list[:-2000]
                        seen.intersection_update(seen_list)
                    save_state(_state)
            if error_streak >= 3:
                notify("✅ 스크리너 연결 복구", "스크리너 조회가 다시 정상 작동합니다.")
            error_streak = 0
        except Exception as e:  # noqa: BLE001
            error_streak += 1
            log.warning("스크리너 조회 실패(%d회 연속): %s", error_streak, e)
            if error_streak == 3:
                notify("⚠️ 스크리너 조회 실패", f"3회 연속 실패\n사유: {str(e)[:200]}")
        time.sleep(SCREENER_POLL_SECONDS)


# ----------------------------------------------------------------------------
# zetro 웹훅 신호 처리
# ----------------------------------------------------------------------------

_hook_lock = threading.Lock()


def _hook_side(p: dict) -> Optional[str]:
    v = str(p.get("side", "")).lower().strip()
    if v in ("up", "long", "buy", "롱", "매수"):
        return "long"
    if v in ("down", "short", "sell", "숏", "매도"):
        return "short"
    return None


def _hook_age_sec(p: dict) -> Optional[float]:
    t = str(p.get("time", "")).strip()
    if not t:
        return None
    try:
        if t.isdigit():
            ts = int(t) / (1000 if len(t) > 10 else 1)
        else:
            ts = datetime.fromisoformat(t.replace("Z", "+00:00")).timestamp()
        return time.time() - ts
    except Exception:  # noqa: BLE001
        return None


def handle_zetro_hook(text: str) -> None:
    try:
        payload = json.loads(text)
    except Exception:  # noqa: BLE001
        log.info("웹훅 내용이 JSON이 아니라 무시 (zetro 알림 메시지 칸 확인 필요): %s", text[:200])
        return

    rule_name = str(payload.get("rule", "")).strip()
    rule = HOOK_RULES.get(rule_name)
    if rule is not None and not rule.get("enabled", True):
        log.info("웹훅 %s: 이 신호는 꺼져 있어서 진입 안 함", rule_name)
        return
    if not rule:
        log.info("웹훅: 진입 규칙에 없는 알림이라 무시 (rule=%s)", rule_name or "-")
        return

    ticker = str(payload.get("ticker", "")).upper().strip()
    symbol = ticker if ticker.endswith("USDT") else f"{ticker}USDT"
    side = _hook_side(payload)
    interval = re.sub(r"[^0-9]", "", str(payload.get("interval", "")))   # "5", "5m", "5분" → "5"
    age = _hook_age_sec(payload)

    if not ticker or not side:
        log.info("웹훅: 종목/방향을 알 수 없어 무시: %s", text[:300])
        return
    if rule.get("sides") and side not in rule["sides"]:
        log.info("웹훅 %s: %s 방향이라 진입 안 함", rule_name, side)
        return
    if rule["intervals"] and interval not in rule["intervals"]:
        log.info("웹훅 %s: %s봉이라 무시 (5분봉만)", rule_name, interval)
        return
    if rule["symbols"] and symbol not in rule["symbols"]:
        log.info("웹훅 %s: %s 종목은 진입 안 함", rule_name, symbol)
        return
    if age is not None and age > rule["max_age_sec"]:
        log.info("웹훅 %s: %s 신호가 %.0f초 지나서 무시", rule_name, symbol, age)
        return

    # 같은 신호 중복 진입 방지
    key = str(payload.get("id") or f"{rule_name}|{symbol}|{side}|{payload.get('time')}")
    with _hook_lock:
        with _state_lock:
            seen = _state.setdefault("hook_seen", [])
            if key in seen:
                log.info("웹훅: 이미 처리한 신호라 무시 (%s)", key)
                return
            seen.append(key)
            if len(seen) > 2000:
                del seen[:-2000]
            save_state(_state)

    if not HOOK_ENTRY_ENABLED:
        log.info("웹훅 진입 꺼짐 — %s %s %s 기록만 함", rule_name, symbol, side)
        return

    inst_id = normalize_symbol(symbol)
    try:
        vol_usd = _executor.get_24h_volume_usd(inst_id)
    except Exception as e:  # noqa: BLE001
        log.info("웹훅 %s: %s 조회 실패(OKX에 없는 종목일 수 있음) — 진입 안 함: %s",
                 rule_name, inst_id, format_okx_error(e))
        return
    if vol_usd < MIN_24H_VOLUME_USD:
        log.info("웹훅 %s: %s OKX 24시간 거래대금 $%s 부족 — 진입 안 함", rule_name, inst_id, f"{vol_usd:,.0f}")
        return

    log.info("웹훅 %s 신호로 진입 시도: %s %s", rule_name, symbol, side)
    enter_position(symbol, side, rule["leverage"],
                   rule.get("tp_pct", TAKE_PROFIT_PCT), rule.get("sl_pct", STOP_LOSS_PCT),
                   source=HOOK_NAMES.get(rule_name, rule_name), margin=rule.get("margin"))


# ----------------------------------------------------------------------------
# 정기 리포트 / 익절·손절 감시
# ----------------------------------------------------------------------------

HEARTBEAT_MINUTES = 10   # 정기 리포트 주기(분)


def heartbeat_loop():
    time.sleep(20)   # 시작 직후 포지션 동기화가 끝나길 잠깐 기다렸다가 첫 리포트 전송
    while True:
        try:
            sync_transfers()
            summary = _executor.get_account_summary()
            upl = summary["unrealized_pnl"]
            with _state_lock:
                ensure_daily_base(summary["usdt_balance"] - upl)
                journal_set_equity(summary["usdt_balance"] - upl)
                _state["last_account"] = {"eq": round(summary["usdt_balance"], 2), "upl": round(upl, 2),
                                          "t": int(time.time() * 1000)}
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
                cum_text = format_cum_stats()
            with _state_lock:
                loss_now, loss_limit = daily_loss_info()
                stopped_flag = check_daily_sl_limit()
            stopped = "\n⛔ 오늘 손실 한도 도달 — 신규 진입 중지 중" if stopped_flag else ""
            if loss_limit is not None:
                room = loss_now + loss_limit
                stopped = (f"\n🧯 오늘 멈춤 기준: 손익 -{loss_limit:.2f} USDT 되면 중지"
                           f"\n    (지금 {loss_now:+.2f} → 앞으로 {max(room, 0):.2f} 더 잃으면 멈춤)") + stopped

            notify("📊 정기 리포트 (OKX)",
                   f"━━━━━━━━━━\n💰 USDT 잔고: {summary['usdt_balance']:.2f}\n"
                   f"{'📈' if upl >= 0 else '📉'} 미실현 손익: {upl:+.2f}\n━━━━━━━━━━\n"
                   f"🗓 오늘 성적 (한국시간 0시 기준)\n"
                   f"🏆 {wl['win']}승 {wl['loss']}패\n"
                   f"💵 당일 실현손익: {pnl_today:+.2f} USDT{stopped}\n━━━━━━━━━━\n"
                   f"{cum_text}\n━━━━━━━━━━\n\n"
                   f"📌 보유 포지션\n{pos_text}")
        except Exception as e:  # noqa: BLE001
            log.warning("하트비트 알림 실패: %s", e)
        time.sleep(HEARTBEAT_MINUTES * 60)


def manage_positions_loop():
    """봇이 진입한 포지션을 보면서 본절 손절·분할 익절을 처리."""
    log.info("포지션 관리 시작: 본절 +%.1f%% / 분할익절 +%.1f%%에서 %d%% 청산 / +%.1f%%에서 손절을 +%.1f%%로",
             BREAKEVEN_TRIGGER_PCT * 100, PARTIAL_TP_TRIGGER_PCT * 100, int(PARTIAL_TP_RATIO * 100),
             STEP_TRIGGER_PCT * 100, STEP_LOCK_PCT * 100)
    while True:
        time.sleep(MANAGE_POLL_SECONDS)
        if not MANAGE_ENABLED:
            continue
        try:
            live = {p["instId"]: p for p in _executor.get_open_positions()}
            with _state_lock:
                targets = []
                for inst_id, entries in _state.get("positions", {}).items():
                    if not entries or inst_id not in live:
                        continue
                    e = entries[0]
                    if e.get("manual") or not e.get("tp_px") or (e.get("be_done") and e.get("partial_done") and e.get("step_done")):
                        continue   # 봇이 진입한 게 아니거나(수동) 이미 다 처리함
                    targets.append((inst_id, e))

            for inst_id, e in targets:
                p = live[inst_id]
                side = e["side"]
                entry = float(p.get("avgPx") or e.get("entry") or 0)
                mark = float(p.get("markPx") or p.get("last") or 0)
                if not entry or not mark:
                    continue
                gain = (mark - entry) / entry if side == "L" else (entry - mark) / entry

                # 1) 본절 손절
                if not e.get("be_done") and gain >= BREAKEVEN_TRIGGER_PCT:
                    be_px = entry * (1 + BREAKEVEN_BUFFER_PCT) if side == "L" else entry * (1 - BREAKEVEN_BUFFER_PCT)
                    try:
                        _executor.replace_tpsl(inst_id, side, e["tp_px"], be_px)
                        with _state_lock:
                            e["be_done"] = True
                            save_state(_state)
                        log.info("%s 본절 손절 설정: 손절 → %s (현재 +%.2f%%)", inst_id, be_px, gain * 100)
                        notify("🛡 본절 손절 설정 (OKX)",
                               f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                               f"가격이 +{gain * 100:.2f}% 가서 손절을 진입가로 올렸어요.\n"
                               f"이제 다시 내려와도 손실 없이 끝나요.")
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 본절 손절 설정 실패: %s", inst_id, format_okx_error(ex))

                # 2) 분할 익절
                if not e.get("partial_done") and gain >= PARTIAL_TP_TRIGGER_PCT:
                    pos_sz = abs(float(p.get("pos", 0) or 0))
                    sz = _executor.round_sz_down(inst_id, pos_sz * PARTIAL_TP_RATIO)
                    try:
                        if sz > 0 and sz < pos_sz:
                            _executor.close_partial(inst_id, side, sz)
                            log.info("%s 분할 익절: %s / %s 청산 (현재 +%.2f%%)", inst_id, sz, pos_sz, gain * 100)
                            ct_val = float(_executor.get_instrument(inst_id).get("ctVal", 1))
                            upl = gain * entry * sz * ct_val
                            notify("💰 분할 익절 (OKX)",
                                   f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                                   f"가격 +{gain * 100:.2f}%에서 {int(PARTIAL_TP_RATIO * 100)}% 청산 (약 {upl:+.2f} USDT)\n"
                                   f"나머지는 익절가까지 가져가요.")
                        else:
                            log.info("%s 수량이 너무 적어 분할 익절은 건너뜀", inst_id)
                        with _state_lock:
                            e["partial_done"] = True
                            save_state(_state)
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 분할 익절 실패: %s", inst_id, format_okx_error(ex))

                # 3) 단계 손절: 수익 일부 확보 (최종 익절이 이 지점보다 가까우면 필요 없음)
                tp_dist = abs(e["tp_px"] - entry) / entry if entry else 0
                if not e.get("step_done") and tp_dist <= STEP_TRIGGER_PCT + 0.002:
                    with _state_lock:
                        e["step_done"] = True
                        save_state(_state)
                if not e.get("step_done") and gain >= STEP_TRIGGER_PCT:
                    lock_px = entry * (1 + STEP_LOCK_PCT) if side == "L" else entry * (1 - STEP_LOCK_PCT)
                    try:
                        _executor.replace_tpsl(inst_id, side, e["tp_px"], lock_px)
                        with _state_lock:
                            e["step_done"] = True
                            e["be_done"] = True
                            save_state(_state)
                        log.info("%s 단계 손절: 손절 → %s (현재 +%.2f%%)", inst_id, lock_px, gain * 100)
                        notify("🔒 수익 확보 (OKX)",
                               f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                               f"가격이 +{gain * 100:.2f}% 가서 손절을 +{STEP_LOCK_PCT * 100:.1f}% 자리로 올렸어요.\n"
                               f"이제 돌아와도 수익을 챙기고 끝나요.")
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 단계 손절 설정 실패: %s", inst_id, format_okx_error(ex))
        except Exception as ex:  # noqa: BLE001
            log.warning("포지션 관리 루프 오류: %s", ex)


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
                    tracked = [e for e in entries if e.get("qty") and (e.get("opened_at") or 0) >= _stats_start_ms()]
                    source = (tracked[0].get("source") or "기타") if tracked else None
                    is_manual = bool(entries) and (entries[0].get("manual") or not entries[0].get("tp_px"))
                    if has_real_entry and is_manual:
                        _state["positions"][inst_id] = []
                        save_state(_state)
                        log.info("%s 수동 포지션 종료 — 성적·손절 횟수에 넣지 않음", inst_id)
                        continue
                    if not has_real_entry:
                        # 주문 진행 중인 예약 자리는 건드리지 않음
                        if not any(e.get("pending") for e in entries):
                            _state["positions"][inst_id] = []
                            save_state(_state)
                        continue

                with _state_lock:
                    j_entries = _state.get("positions", {}).get(inst_id) or []
                    j_source = (j_entries[0].get("source") if j_entries else None) or "기타"
                    j_side = j_entries[0].get("side") if j_entries else None
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
                    close_kind = journal_record(inst_id, j_source, j_side, pnl,
                                                kind=classify_close(pnl, rows[0] if rows else None))
                    maybe_notify_loss_limit()
                    if source:
                        record_cum_trade(source, pnl)
                    cum_text = format_cum_stats()
                    _state.setdefault("positions", {})[inst_id] = []
                    save_state(_state)

                if not is_win:
                    title = "🛑 손절"
                elif close_kind == "be":
                    title = "➖ 본절 종료 (분할 익절분 포함)" if pnl >= 1.0 else "➖ 본절 종료"
                else:
                    title = "✅ 익절"
                notify(f"{title} (OKX)",
                       f"📊 종목: {inst_id}{' · ' + source if source else ''}\n💰 손익: {pnl:+.2f} USDT\n━━━━━━━━━━\n"
                       f"🏆 오늘 {win_loss['win']}승 {win_loss['loss']}패\n"
                       f"💵 당일 실현손익: {daily_pnl['total']:+.2f} USDT\n━━━━━━━━━━\n"
                       f"{cum_text}")
        except Exception as e:  # noqa: BLE001
            log.warning("손절 감시 루프 오류: %s", e)


# ----------------------------------------------------------------------------
# Railway 상태 확인용 (주문 기능 없음, 접속하면 ok만 응답)
# ----------------------------------------------------------------------------

class HealthHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    @staticmethod
    def _safe_handle(text: str) -> None:
        try:
            handle_zetro_hook(text)
        except Exception as e:  # noqa: BLE001
            log.error("웹훅 처리 실패: %s", e)

    def do_POST(self):
        # zetro 웹훅 수신 → 응답은 바로 하고 진입 처리는 따로 진행
        length = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(length) if length else b""
        path_only = self.path.split("?", 1)[0].rstrip("/")
        text = raw.decode("utf-8", errors="ignore")[:2000]
        if path_only == ZETRO_HOOK_PATH:
            log.info("zetro 웹훅 수신: %s", text)
            threading.Thread(target=self._safe_handle, args=(text,), daemon=True).start()
            code, body = 200, b'{"ok":true}'
        else:
            # 주소가 달라도 무엇이 왔는지 확인할 수 있게 기록
            log.info("웹훅 수신(주소 불일치) path=%s body=%s", self.path[:200], text[:500])
            code, body = 404, b""
        self.send_response(code)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path_only = self.path.split("?", 1)[0].rstrip("/")
        if path_only == REPORT_PATH:
            try:
                body = render_report_html()
                ctype = "text/html; charset=utf-8"
            except Exception as e:  # noqa: BLE001
                log.warning("기록지 페이지 오류: %s", e)
                body, ctype = "기록지를 만드는 중 오류가 났어요".encode("utf-8"), "text/plain; charset=utf-8"
        else:
            body, ctype = b'{"ok":true}', "application/json"
        self.send_response(200)
        self.send_header("Content-Type", ctype)
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
    reset_sl_on_new_commit()
    purge_excluded_sources()
    merge_split_sources()
    sync_positions_from_exchange()
    seed_journal_today()
    threading.Thread(target=backfill_journal, daemon=True).start()

    log.info("상태 파일 위치: %s (%s)", STATE_FILE.resolve(),
             "Volume 사용 중 — 재배포해도 기록 유지" if os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")
             else "Volume 없음 — 재배포하면 기록 초기화")
    log.info("zetro OKX 봇 시작 | 증거금=%sUSDT 기본레버리지=%sx TP=+%.0f%% SL=-%.0f%%",
             MARGIN_USDT, LEVERAGE, TAKE_PROFIT_PCT * 100, STOP_LOSS_PCT * 100)

    threading.Thread(target=heartbeat_loop, daemon=True).start()
    threading.Thread(target=sl_watch_loop, daemon=True).start()
    threading.Thread(target=manage_positions_loop, daemon=True).start()
    threading.Thread(target=daily_close_loop, daemon=True).start()
    log.info("매매 기록지: %s", report_url())
    if ZETRO_API_KEY:
        threading.Thread(target=zetro_poll_loop, daemon=True).start()
        threading.Thread(target=screener_poll_loop, daemon=True).start()
    else:
        log.warning("ZETRO_API_KEY가 없어서 zetro 신호 조회는 꺼둔 상태로 시작합니다.")
        notify("⚠️ zetro 신호 조회 꺼짐", "Railway Variables에 ZETRO_API_KEY를 넣어주세요.")

    server = ThreadingHTTPServer(("0.0.0.0", PORT), HealthHandler)
    server.daemon_threads = True
    server.serve_forever()


if __name__ == "__main__":
    main()
