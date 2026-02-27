"""
GSA Live Paper Trader
=====================
Direct REST integration with Alpaca paper trading.
No SDK required — pure requests + yfinance.

Runs a full daily cycle:
  1. Fetch account state from Alpaca
  2. Download market data via yfinance
  3. Generate GSA signals
  4. Execute paper orders via Alpaca REST
  5. Log everything to PostgreSQL

Usage:
  python gsa_live_trader.py          # full daily run
  python gsa_live_trader.py --status # account status only
  python gsa_live_trader.py --dry    # signals only, no orders
"""

import os
import sys
import json
import time
import datetime
import argparse
import requests
import numpy as np
import pandas as pd
import yfinance as yf
import psycopg2
from psycopg2.extras import Json
from gsa_core import GSACore, MarketRegime

# ─── Alpaca REST Client ──────────────────────────────────────────────────────

class AlpacaClient:
    """Minimal Alpaca paper trading REST client."""

    PAPER_BASE = "https://paper-api.alpaca.markets"
    DATA_BASE  = "https://data.alpaca.markets"

    def __init__(self):
        self.api_key = os.environ.get("APCA_API_KEY_ID", "")
        self.secret  = os.environ.get("APCA_API_SECRET_KEY", "")
        if not self.api_key or not self.secret:
            raise RuntimeError("Alpaca credentials not found. Check APCA_API_KEY_ID and APCA_API_SECRET_KEY.")
        self.headers = {
            "APCA-API-KEY-ID":     self.api_key,
            "APCA-API-SECRET-KEY": self.secret,
            "Content-Type":        "application/json",
        }

    def _get(self, path: str, base: str = None) -> dict:
        url = (base or self.PAPER_BASE) + path
        r = requests.get(url, headers=self.headers, timeout=10)
        r.raise_for_status()
        return r.json()

    def _post(self, path: str, body: dict) -> dict:
        url = self.PAPER_BASE + path
        r = requests.post(url, headers=self.headers, json=body, timeout=10)
        r.raise_for_status()
        return r.json()

    def _delete(self, path: str) -> bool:
        url = self.PAPER_BASE + path
        r = requests.delete(url, headers=self.headers, timeout=10)
        return r.status_code in (200, 204)

    # ── Account ────────────────────────────────────────────────────────────
    def get_account(self) -> dict:
        return self._get("/v2/account")

    def get_positions(self) -> list:
        return self._get("/v2/positions")

    def get_orders(self, status: str = "open") -> list:
        return self._get(f"/v2/orders?status={status}&limit=100")

    # ── Trading ────────────────────────────────────────────────────────────
    def place_order(self, ticker: str, side: str, qty: float,
                    order_type: str = "market", time_in_force: str = "day") -> dict:
        body = {
            "symbol":        ticker,
            "qty":           str(round(qty, 4)),
            "side":          side,
            "type":          order_type,
            "time_in_force": time_in_force,
        }
        return self._post("/v2/orders", body)

    def cancel_order(self, order_id: str) -> bool:
        return self._delete(f"/v2/orders/{order_id}")

    def cancel_all_orders(self) -> bool:
        return self._delete("/v2/orders")

    def close_position(self, ticker: str) -> dict:
        return self._delete(f"/v2/positions/{ticker}")


# ─── Database Logger ─────────────────────────────────────────────────────────

class TradeLogger:
    def __init__(self):
        self.conn = psycopg2.connect(os.environ["DATABASE_URL"])
        self.conn.autocommit = True

    def log_signal(self, ticker: str, action: str, confidence: float,
                   gile: float, xi_pd: float, regime: str,
                   price: float, tralse_ratio: float = 0.0):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_signals
                  (ticker, action, confidence, gile_score, xi_pd, regime, price, tralse_ratio)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
            """, (ticker, action, confidence, gile, xi_pd, regime, price, tralse_ratio))

    def log_trade(self, ticker: str, side: str, shares: float,
                  price: float, position_value: float,
                  order_id: str = "", status: str = "pending"):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_paper_trades
                  (ticker, side, shares, price, position_value, alpaca_order_id, status)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
            """, (ticker, side, shares, price, position_value, order_id, status))

    def log_portfolio(self, equity: float, cash: float, buying_power: float,
                      unrealized_pl: float, portfolio_value: float,
                      day_pl: float, n_positions: int):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_portfolio_snapshots
                  (equity, cash, buying_power, unrealized_pl, portfolio_value, day_pl, n_positions)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
            """, (equity, cash, buying_power, unrealized_pl,
                  portfolio_value, day_pl, n_positions))

    def log_run(self, notes: str, n_signals: int, n_trades: int,
                top_signals: list, portfolio: dict):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_performance_log
                  (run_notes, signals_generated, trades_executed, top_signals, portfolio_json)
                VALUES (%s, %s, %s, %s, %s)
            """, (notes, n_signals, n_trades,
                  Json(top_signals), Json(portfolio)))

    def get_recent_signals(self, n: int = 50) -> pd.DataFrame:
        return pd.read_sql("""
            SELECT * FROM gsa_signals
            ORDER BY recorded_at DESC LIMIT %s
        """, self.conn, params=(n,))

    def get_performance_history(self) -> pd.DataFrame:
        return pd.read_sql("""
            SELECT snapshot_at, equity, day_pl, n_positions, unrealized_pl
            FROM gsa_portfolio_snapshots
            ORDER BY snapshot_at DESC LIMIT 90
        """, self.conn)


# ─── Market Data ─────────────────────────────────────────────────────────────

def download_market_data(tickers: list, period: str = "90d") -> dict:
    """Download OHLCV data for all tickers via yfinance."""
    print(f"  Downloading {len(tickers)} tickers ({period})...")
    data = {}
    for ticker in tickers:
        try:
            df = yf.download(ticker, period=period, progress=False, auto_adjust=True)
            if df is not None and len(df) >= 60:
                data[ticker] = df
        except Exception as e:
            print(f"    {ticker}: {e}")
    print(f"  Got data for {len(data)}/{len(tickers)} tickers")
    return data


# ─── Signal Generation ────────────────────────────────────────────────────────

def generate_signals(market_data: dict, gsa: GSACore) -> dict:
    """Run GSA on each ticker's price data."""
    signals = {}
    for ticker, df in market_data.items():
        try:
            close_vals = df["Close"].values
            closes = np.array(close_vals.flatten()
                              if hasattr(close_vals, "flatten") else close_vals,
                              dtype=float)
            if len(closes) < 61:
                continue

            returns = np.diff(closes) / closes[:-1] * 100

            xi     = gsa.compute_xi_metrics(returns[-60:], closes[-60:])
            gile   = gsa.compute_gile(returns[-60:], closes[-60:])
            regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, 1.0)
            signal = gsa.generate_signal(xi, gile, regime, conf)
            signal = gsa.enhance_with_fractal(closes, signal)

            # TI Sigma tralse_ratio on recent returns
            recent_tb = np.clip(
                (returns[-30:] - np.mean(returns[-30:])) /
                (np.std(returns[-30:]) * 3 + 1e-9), -1, 1)
            tralse_ratio = float(np.mean(
                (np.abs(recent_tb) >= 0.4142) & (np.abs(recent_tb) <= 0.85)))

            signals[ticker] = {
                "action":       signal.action,
                "confidence":   float(signal.confidence),
                "gile":         float(signal.gile),
                "xi_pd":        float(xi.pd),
                "regime":       regime.value,
                "price":        float(closes[-1]),
                "tralse_ratio": tralse_ratio,
                "reasons":      signal.reasons,
            }
        except Exception as e:
            print(f"    Signal error {ticker}: {e}")
    return signals


# ─── Portfolio Sizing ─────────────────────────────────────────────────────────

def rank_and_size(signals: dict, buying_power: float,
                  max_positions: int = 8,
                  max_position_pct: float = 0.12) -> list:
    """
    Rank signals by GILE × confidence, return buy orders sized by Kelly-lite.
    Only BUY signals are actioned. SELL signals trigger position close.
    """
    buys  = [(t, s) for t, s in signals.items()
             if s["action"] in ("strong_buy", "buy") and s["confidence"] > 0.40]
    sells = [(t, s) for t, s in signals.items()
             if s["action"] in ("strong_sell", "sell")]

    # Rank buys: GILE × confidence × tralse_ratio bonus
    scored = sorted(
        buys,
        key=lambda x: x[1]["gile"] * x[1]["confidence"] * (1 + x[1]["tralse_ratio"]),
        reverse=True
    )[:max_positions]

    orders = []
    per_position = min(buying_power * max_position_pct,
                       buying_power / max(len(scored), 1))

    for ticker, sig in scored:
        if sig["price"] > 0:
            qty = per_position / sig["price"]
            if qty >= 0.001:
                orders.append({
                    "ticker": ticker,
                    "side":   "buy",
                    "qty":    qty,
                    "price":  sig["price"],
                    "value":  qty * sig["price"],
                    "signal": sig,
                })

    for ticker, sig in sells:
        orders.append({
            "ticker": ticker,
            "side":   "sell",
            "qty":    0,  # close entire position
            "price":  sig["price"],
            "value":  0,
            "signal": sig,
        })

    return orders


# ─── Main Runner ─────────────────────────────────────────────────────────────

GREEN_LIGHT = [
    "GOOGL", "NVDA", "MSFT", "META",   # Tech
    "CAT",   "GE",                      # Industrials
    "GS",    "MS",                      # Financials
    "XOM",   "CVX",   "COP",           # Energy
    "WMT",   "TJX",                    # Consumer
    "AMZN",  "TSLA",  "COST",  "JPM",  # Additions
]


def print_header(title: str):
    print(f"\n{'='*62}")
    print(f"  {title}")
    print(f"{'='*62}")


def run_daily_cycle(dry_run: bool = False, status_only: bool = False):
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print_header(f"GSA PAPER TRADER  —  {now}")

    # ── Connect ────────────────────────────────────────────────────────────
    print("\n[1/5] Connecting to Alpaca paper account...")
    try:
        alpaca = AlpacaClient()
        account = alpaca.get_account()
    except Exception as e:
        print(f"  ERROR: {e}")
        return

    equity        = float(account.get("equity", 0))
    cash          = float(account.get("cash", 0))
    buying_power  = float(account.get("buying_power", 0))
    day_trade_bp  = float(account.get("daytrading_buying_power", 0))
    unrealized_pl = float(account.get("unrealized_pl", 0))
    day_pl        = float(account.get("equity", 0)) - float(account.get("last_equity", account.get("equity", 0)))

    print(f"  Account:      {account.get('account_number', 'N/A')}")
    print(f"  Equity:       ${equity:>12,.2f}")
    print(f"  Cash:         ${cash:>12,.2f}")
    print(f"  Buying Power: ${buying_power:>12,.2f}")
    print(f"  Unrealized P&L: ${unrealized_pl:>+10,.2f}")
    print(f"  Day P&L:        ${day_pl:>+10,.2f}")

    positions = alpaca.get_positions()
    n_pos = len(positions)
    print(f"\n  Open Positions: {n_pos}")
    for p in positions:
        pl     = float(p.get("unrealized_pl", 0))
        pl_pct = float(p.get("unrealized_plpc", 0)) * 100
        print(f"    {p['symbol']:8s}  {float(p['qty']):8.4f} shares  "
              f"@ ${float(p['current_price']):8.2f}  P&L: ${pl:+8.2f} ({pl_pct:+5.2f}%)")

    if status_only:
        return

    # ── Log portfolio snapshot ─────────────────────────────────────────────
    try:
        logger = TradeLogger()
        logger.log_portfolio(equity, cash, buying_power, unrealized_pl,
                             equity, day_pl, n_pos)
    except Exception as e:
        print(f"  DB log warning: {e}")
        logger = None

    # ── Market Data ────────────────────────────────────────────────────────
    print("\n[2/5] Downloading market data...")
    market_data = download_market_data(GREEN_LIGHT, period="90d")

    # ── Generate Signals ───────────────────────────────────────────────────
    print("\n[3/5] Generating GSA signals...")
    gsa     = GSACore(lookback_short=7, lookback_long=60)
    signals = generate_signals(market_data, gsa)

    if logger:
        for ticker, sig in signals.items():
            try:
                logger.log_signal(
                    ticker, sig["action"], sig["confidence"],
                    sig["gile"], sig["xi_pd"], sig["regime"],
                    sig["price"], sig["tralse_ratio"])
            except Exception:
                pass

    # Print signal table
    print(f"\n  {'Ticker':<8} {'Action':<14} {'GILE':>6} {'Conf':>6} {'PD':>6} {'Tralse':>7} {'Price':>8}")
    print(f"  {'-'*65}")
    sorted_sigs = sorted(signals.items(),
                         key=lambda x: x[1]["gile"] * x[1]["confidence"],
                         reverse=True)
    for ticker, sig in sorted_sigs:
        print(f"  {ticker:<8} {sig['action']:<14} "
              f"{sig['gile']:>6.3f} {sig['confidence']:>6.3f} "
              f"{sig['xi_pd']:>6.2f} {sig['tralse_ratio']:>7.4f} "
              f"${sig['price']:>8.2f}")

    # ── Rank and Size Orders ───────────────────────────────────────────────
    print("\n[4/5] Sizing orders...")
    orders = rank_and_size(signals, buying_power, max_positions=8,
                           max_position_pct=0.12)

    buy_orders  = [o for o in orders if o["side"] == "buy"]
    sell_orders = [o for o in orders if o["side"] == "sell"]

    current_tickers = {p["symbol"] for p in positions}
    sell_orders = [o for o in sell_orders if o["ticker"] in current_tickers]

    print(f"\n  Buy orders:  {len(buy_orders)}")
    for o in buy_orders:
        print(f"    BUY  {o['ticker']:8s}  {o['qty']:8.4f} shares  "
              f"@ ${o['price']:8.2f}  = ${o['value']:>10,.2f}")

    print(f"  Sell orders: {len(sell_orders)}")
    for o in sell_orders:
        print(f"    SELL {o['ticker']:8s}  (close full position)")

    if dry_run:
        print("\n  [DRY RUN] No orders placed.")
        if logger:
            logger.log_run(
                f"DRY RUN — signals={len(signals)}", len(signals), 0,
                [{"ticker": t, **s} for t, s in sorted_sigs[:8]],
                {"equity": equity, "cash": cash, "positions": n_pos})
        return

    # ── Execute Orders ─────────────────────────────────────────────────────
    print("\n[5/5] Executing paper orders...")
    n_trades = 0

    for o in sell_orders:
        try:
            result = alpaca.close_position(o["ticker"])
            print(f"  CLOSED {o['ticker']}: {result.get('status', 'OK')}")
            if logger:
                logger.log_trade(o["ticker"], "sell", 0,
                                 o["price"], 0, "", "closed")
            n_trades += 1
        except Exception as e:
            print(f"  CLOSE ERROR {o['ticker']}: {e}")

    time.sleep(1)  # brief pause between sell and buy

    already_held = {p["symbol"] for p in alpaca.get_positions()}
    for o in buy_orders:
        if o["ticker"] in already_held:
            print(f"  SKIP {o['ticker']} (already held)")
            continue
        if o["qty"] < 0.001:
            continue
        try:
            result = alpaca.place_order(o["ticker"], "buy", o["qty"])
            order_id = result.get("id", "")
            status   = result.get("status", "")
            print(f"  BUY  {o['ticker']:8s}  {o['qty']:.4f} shares  "
                  f"→ order {order_id[:8]}... [{status}]")
            if logger:
                logger.log_trade(o["ticker"], "buy", o["qty"],
                                 o["price"], o["value"], order_id, status)
            n_trades += 1
        except requests.HTTPError as e:
            print(f"  ORDER ERROR {o['ticker']}: {e.response.text[:100]}")
        except Exception as e:
            print(f"  ORDER ERROR {o['ticker']}: {e}")

    # ── Final Summary ──────────────────────────────────────────────────────
    print_header("RUN COMPLETE")
    print(f"  Signals generated:  {len(signals)}")
    print(f"  Orders executed:    {n_trades}")
    print(f"  Portfolio equity:   ${equity:,.2f}")
    print(f"  Unrealized P&L:     ${unrealized_pl:+,.2f}")
    print()
    print("  Next step: run again tomorrow (or schedule via cron).")
    print("  Track record accumulates automatically in the database.")

    if logger:
        logger.log_run(
            f"Live run — {n_trades} trades",
            len(signals), n_trades,
            [{"ticker": t, **s} for t, s in sorted_sigs[:8]],
            {"equity": equity, "cash": cash, "unrealized_pl": unrealized_pl,
             "positions": n_pos, "n_trades": n_trades})


def show_track_record():
    """Print performance history from DB."""
    print_header("GSA PAPER TRADING — TRACK RECORD")
    try:
        logger = TradeLogger()
        perf = logger.get_performance_history()
        if perf.empty:
            print("  No snapshots yet. Run the trader first.")
            return
        perf = perf.sort_values("snapshot_at")
        start_equity = perf.iloc[0]["equity"]
        end_equity   = perf.iloc[-1]["equity"]
        total_return = (end_equity - start_equity) / start_equity * 100
        n_days       = len(perf)

        print(f"  Snapshots logged:   {n_days}")
        print(f"  Starting equity:    ${start_equity:,.2f}")
        print(f"  Current equity:     ${end_equity:,.2f}")
        print(f"  Total return:       {total_return:+.2f}%")
        print()
        print(f"  {'Date':<22} {'Equity':>12} {'Day P&L':>10} {'Pos':>5}")
        print(f"  {'-'*55}")
        for _, row in perf.tail(15).iterrows():
            print(f"  {str(row['snapshot_at'])[:19]:<22} "
                  f"${row['equity']:>11,.2f} "
                  f"${row['day_pl']:>+9,.2f} "
                  f"{int(row['n_positions']):>5}")

        sigs = logger.get_recent_signals(20)
        if not sigs.empty:
            print(f"\n  Recent Signals (last {len(sigs)}):")
            print(f"  {'Time':<20} {'Ticker':<8} {'Action':<14} {'GILE':>6}")
            print(f"  {'-'*55}")
            for _, row in sigs.iterrows():
                print(f"  {str(row['recorded_at'])[:19]:<20} "
                      f"{row['ticker']:<8} {row['action']:<14} "
                      f"{row['gile_score']:>6.3f}")
    except Exception as e:
        print(f"  Error: {e}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="GSA Paper Trader")
    parser.add_argument("--status",  action="store_true", help="Account status only")
    parser.add_argument("--dry",     action="store_true", help="Signals only, no orders")
    parser.add_argument("--record",  action="store_true", help="Show track record")
    args = parser.parse_args()

    if args.record:
        show_track_record()
    else:
        run_daily_cycle(dry_run=args.dry, status_only=args.status)
