"""
GSA Live Paper Trader v2 — BOK 8-Mode + Dual-Confidence
=========================================================
Direct REST integration with Alpaca paper trading.
No SDK required — pure requests + yfinance.

Daily cycle:
  1. Fetch account state from Alpaca
  2. Download market data via yfinance
  3. Generate BOK 8-mode signals with Dual-Confidence (EC + EpC)
  4. Execute only tradeable signals (EC > 0.65 AND EpC > 0.50)
  5. Log everything to PostgreSQL

Usage:
  python gsa_live_trader.py          # full daily run
  python gsa_live_trader.py --status # account status only
  python gsa_live_trader.py --dry    # signals only, no orders
  python gsa_live_trader.py --record # show full performance report
  python gsa_live_trader.py --report # alias for --record
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
from gsa_core import (
    GSACore, MarketRegime, Signal,
    C_EMERICK, LCC_HIGH, PHI, SQRT2
)

# ─── Alpaca REST Client ──────────────────────────────────────────────────────

class AlpacaClient:
    PAPER_BASE = "https://paper-api.alpaca.markets"
    DATA_BASE  = "https://data.alpaca.markets"

    def __init__(self):
        self.api_key = os.environ.get("APCA_API_KEY_ID", "")
        self.secret  = os.environ.get("APCA_API_SECRET_KEY", "")
        if not self.api_key or not self.secret:
            raise RuntimeError("Alpaca credentials not found.")
        self.headers = {
            "APCA-API-KEY-ID":     self.api_key,
            "APCA-API-SECRET-KEY": self.secret,
            "Content-Type":        "application/json",
        }

    def _get(self, path, base=None):
        r = requests.get((base or self.PAPER_BASE) + path, headers=self.headers, timeout=10)
        r.raise_for_status()
        return r.json()

    def _post(self, path, body):
        r = requests.post(self.PAPER_BASE + path, headers=self.headers, json=body, timeout=10)
        r.raise_for_status()
        return r.json()

    def _delete(self, path):
        r = requests.delete(self.PAPER_BASE + path, headers=self.headers, timeout=10)
        return r.status_code in (200, 204)

    def get_account(self):     return self._get("/v2/account")
    def get_positions(self):   return self._get("/v2/positions")
    def get_orders(self, status="open"): return self._get(f"/v2/orders?status={status}&limit=100")

    def place_order(self, ticker, side, qty, order_type="market", tif="day"):
        return self._post("/v2/orders", {
            "symbol": ticker, "qty": str(round(qty, 4)),
            "side": side, "type": order_type, "time_in_force": tif,
        })

    def cancel_all_orders(self): return self._delete("/v2/orders")
    def close_position(self, ticker): return self._delete(f"/v2/positions/{ticker}")


# ─── Database Logger ─────────────────────────────────────────────────────────

class TradeLogger:
    def __init__(self):
        self.conn = psycopg2.connect(os.environ["DATABASE_URL"])
        self.conn.autocommit = True
        self._migrate()

    def _migrate(self):
        """Add v2 columns to gsa_signals if they don't exist yet."""
        migrations = [
            "ALTER TABLE gsa_signals ADD COLUMN IF NOT EXISTS ec DOUBLE PRECISION DEFAULT 0.5",
            "ALTER TABLE gsa_signals ADD COLUMN IF NOT EXISTS epc DOUBLE PRECISION DEFAULT 0.5",
            "ALTER TABLE gsa_signals ADD COLUMN IF NOT EXISTS tral_state BOOLEAN DEFAULT FALSE",
            "ALTER TABLE gsa_signals ADD COLUMN IF NOT EXISTS bok_regime VARCHAR(32) DEFAULT ''",
            "ALTER TABLE gsa_portfolio_snapshots ADD COLUMN IF NOT EXISTS run_timestamp TIMESTAMP WITH TIME ZONE DEFAULT NOW()",
        ]
        with self.conn.cursor() as cur:
            for sql in migrations:
                try:
                    cur.execute(sql)
                except Exception:
                    pass

    def log_signal(self, ticker, action, confidence, gile, xi_pd, regime,
                   price, tralse_ratio=0.0, ec=None, epc=None,
                   tral_state=False, bok_regime=""):
        ec  = ec  if ec  is not None else confidence
        epc = epc if epc is not None else confidence
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_signals
                  (ticker, action, confidence, gile_score, xi_pd, regime, price,
                   tralse_ratio, ec, epc, tral_state, bok_regime)
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
            """, (ticker, action, confidence, gile, xi_pd, regime, price,
                  tralse_ratio, ec, epc, tral_state, bok_regime))

    def log_trade(self, ticker, side, shares, price, position_value,
                  order_id="", status="pending"):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_paper_trades
                  (ticker, side, shares, price, position_value, alpaca_order_id, status)
                VALUES (%s,%s,%s,%s,%s,%s,%s)
            """, (ticker, side, shares, price, position_value, order_id, status))

    def log_portfolio(self, equity, cash, buying_power, unrealized_pl,
                      portfolio_value, day_pl, n_positions):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_portfolio_snapshots
                  (equity, cash, buying_power, unrealized_pl,
                   portfolio_value, day_pl, n_positions)
                VALUES (%s,%s,%s,%s,%s,%s,%s)
            """, (equity, cash, buying_power, unrealized_pl,
                  portfolio_value, day_pl, n_positions))

    def log_run(self, notes, n_signals, n_trades, top_signals, portfolio):
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO gsa_performance_log
                  (run_notes, signals_generated, trades_executed,
                   top_signals, portfolio_json)
                VALUES (%s,%s,%s,%s,%s)
            """, (notes, n_signals, n_trades,
                  Json(top_signals), Json(portfolio)))

    def get_performance_history(self):
        return pd.read_sql("""
            SELECT snapshot_at, equity, day_pl, n_positions, unrealized_pl
            FROM gsa_portfolio_snapshots
            ORDER BY snapshot_at DESC LIMIT 90
        """, self.conn)

    def get_recent_signals(self, n=50):
        return pd.read_sql("""
            SELECT * FROM gsa_signals
            ORDER BY recorded_at DESC LIMIT %s
        """, self.conn, params=(n,))

    def get_signal_stats(self):
        return pd.read_sql("""
            SELECT
                action,
                COUNT(*) AS count,
                AVG(confidence) AS avg_conf,
                AVG(ec)  AS avg_ec,
                AVG(epc) AS avg_epc,
                SUM(CASE WHEN tral_state THEN 1 ELSE 0 END) AS tral_count
            FROM gsa_signals
            GROUP BY action ORDER BY count DESC
        """, self.conn)

    def get_all_trades(self):
        return pd.read_sql("""
            SELECT ticker, side, shares, price, position_value, executed_at
            FROM gsa_paper_trades ORDER BY executed_at DESC
        """, self.conn)


# ─── Market Data ─────────────────────────────────────────────────────────────

def download_market_data(tickers, period="90d"):
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

def generate_signals(market_data, gsa):
    """Run GSA v2 on each ticker. Returns dict with full dual-confidence data."""
    signals = {}
    for ticker, df in market_data.items():
        try:
            close_vals = df["Close"].values
            closes = np.array(
                close_vals.flatten() if hasattr(close_vals, "flatten") else close_vals,
                dtype=float
            )
            if len(closes) < 61:
                continue

            returns = np.diff(closes) / closes[:-1] * 100

            xi      = gsa.compute_xi_metrics(returns[-60:], closes[-60:])
            gile    = gsa.compute_gile(returns[-60:], closes[-60:])
            vol_ratio = float(np.std(returns[-7:]) / max(np.std(returns[-60:]), 0.01))
            regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, vol_ratio)
            bif     = gsa.detect_bifurcation(gsa.constraint_history)
            signal  = gsa.generate_signal(xi, gile, regime, conf, bif)
            signal  = gsa.enhance_with_fractal(closes, signal)

            # Tralse ratio: fraction of recent z-scored returns in Tralse zone [C_E, LCC_H]
            recent_tb = np.clip(
                (returns[-30:] - np.mean(returns[-30:])) /
                (np.std(returns[-30:]) * 3 + 1e-9), -1, 1
            )
            tralse_ratio = float(np.mean(
                (np.abs(recent_tb) >= C_EMERICK) & (np.abs(recent_tb) <= LCC_HIGH)
            ))

            signals[ticker] = {
                "action":       signal.action,
                "confidence":   float(signal.confidence),
                "ec":           float(signal.ec),
                "epc":          float(signal.epc),
                "tral_state":   bool(signal.tral_state),
                "tradeable":    bool(signal.tradeable),
                "gile":         float(signal.gile),
                "xi_pd":        float(xi.pd),
                "regime":       regime.value,
                "price":        float(closes[-1]),
                "tralse_ratio": tralse_ratio,
                "reasons":      signal.reasons,
                "bif_meta":     float(bif.metastability),
                "bif_depth":    float(bif.basin_depth),
            }
        except Exception as e:
            print(f"    Signal error {ticker}: {e}")
    return signals


# ─── Portfolio Sizing ─────────────────────────────────────────────────────────

def rank_and_size(signals, buying_power, max_positions=8, max_position_pct=0.12):
    """
    Rank and size orders using Dual-Confidence gate.
    Only BUY signals that are tradeable (EC > 0.65 AND EpC > 0.50) are executed.
    Tral-state signals are listed but sized at 50%.
    SELL signals are always executed (exit is unconditional).
    """
    buys  = [(t, s) for t, s in signals.items()
             if s["action"] in ("strong_buy", "buy") and s["ec"] > 0.40]
    sells = [(t, s) for t, s in signals.items()
             if s["action"] in ("strong_sell", "sell")]

    # Rank: GILE × EC × (1 + tralse_ratio)
    scored = sorted(
        buys,
        key=lambda x: x[1]["gile"] * x[1]["ec"] * (1 + x[1]["tralse_ratio"]),
        reverse=True
    )[:max_positions]

    orders = []
    per_position = min(buying_power * max_position_pct,
                       buying_power / max(len(scored), 1))

    for ticker, sig in scored:
        if sig["price"] <= 0:
            continue
        # Dual-confidence gate: tral-state gets half size
        size_mult = 1.0
        if not sig["tradeable"]:
            if sig["tral_state"]:
                size_mult = 0.50   # Half-size for Tral-state (directional, not validated)
            else:
                continue           # Skip if neither tradeable nor tral-state

        qty = (per_position * size_mult) / sig["price"]
        if qty >= 0.001:
            orders.append({
                "ticker":     ticker,
                "side":       "buy",
                "qty":        qty,
                "price":      sig["price"],
                "value":      qty * sig["price"],
                "signal":     sig,
                "size_note":  "HALF (tral-state)" if size_mult < 1.0 else "FULL",
            })

    for ticker, sig in sells:
        orders.append({
            "ticker": ticker, "side": "sell",
            "qty": 0, "price": sig["price"],
            "value": 0, "signal": sig, "size_note": "CLOSE",
        })

    return orders


# ─── Performance Report ───────────────────────────────────────────────────────

def show_performance_report(alpaca=None):
    """Full track record: positions, P&L, signal stats, trade history."""
    print_header("GSA v2 — PERFORMANCE REPORT")
    print(f"  Generated: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"  Constants: C_EMERICK={C_EMERICK:.4f}  φ={PHI:.4f}  √2={SQRT2:.4f}")
    print(f"  LCC Thresholds: TRALSE={C_EMERICK:.3f}  HIGH={LCC_HIGH:.3f}")

    # Live account data
    if alpaca:
        try:
            account   = alpaca.get_account()
            positions = alpaca.get_positions()
            equity       = float(account.get("equity", 0))
            cash         = float(account.get("cash", 0))
            last_equity  = float(account.get("last_equity", equity))
            unrealized   = float(account.get("unrealized_pl", 0))
            total_return = (equity - 100000.0) / 100000.0 * 100

            print(f"\n  ── LIVE ACCOUNT ────────────────────────────────")
            print(f"  Account:        PA3J364R5XU9")
            print(f"  Start Capital:  $100,000.00  (Feb 27, 2026)")
            print(f"  Current Equity: ${equity:>12,.2f}")
            print(f"  Cash:           ${cash:>12,.2f}")
            print(f"  Unrealized P&L: ${unrealized:>+10,.2f}")
            print(f"  Total Return:   {total_return:>+8.3f}%  (9 trading days)")

            if positions:
                print(f"\n  ── OPEN POSITIONS ──────────────────────────────")
                print(f"  {'Ticker':<8} {'Shares':>10} {'Entry':>10} {'Current':>10} {'P&L':>10} {'%':>7}")
                print(f"  {'-'*60}")
                for p in positions:
                    pl     = float(p.get("unrealized_pl", 0))
                    pl_pct = float(p.get("unrealized_plpc", 0)) * 100
                    avg_px = float(p.get("avg_entry_price", 0))
                    cur_px = float(p.get("current_price", 0))
                    shares = float(p.get("qty", 0))
                    flag   = "✅" if pl > 0 else "❌"
                    print(f"  {p['symbol']:<8} {shares:>10.4f} "
                          f"${avg_px:>9.2f} ${cur_px:>9.2f} "
                          f"${pl:>+9.2f} {pl_pct:>+6.2f}% {flag}")
        except Exception as e:
            print(f"  Alpaca error: {e}")

    # Database stats
    try:
        logger = TradeLogger()

        # Portfolio snapshot history
        perf = logger.get_performance_history()
        if not perf.empty:
            perf = perf.sort_values("snapshot_at")
            print(f"\n  ── EQUITY SNAPSHOTS ({len(perf)} logged) ──────────────")
            print(f"  {'Date':<22} {'Equity':>12} {'Day P&L':>10} {'Pos':>5} {'Unrealized':>12}")
            print(f"  {'-'*65}")
            for _, row in perf.tail(10).iterrows():
                print(f"  {str(row['snapshot_at'])[:19]:<22} "
                      f"${row['equity']:>11,.2f} "
                      f"${row['day_pl']:>+9,.2f} "
                      f"{int(row['n_positions']):>5} "
                      f"${row['unrealized_pl']:>+10,.2f}")

        # Signal breakdown
        stats = logger.get_signal_stats()
        if not stats.empty:
            print(f"\n  ── SIGNAL STATISTICS (all time) ────────────────")
            print(f"  {'Action':<14} {'Count':>6} {'Avg Conf':>9} {'Avg EC':>8} {'Avg EpC':>8} {'Tral':>6}")
            print(f"  {'-'*55}")
            for _, row in stats.iterrows():
                print(f"  {row['action']:<14} {int(row['count']):>6} "
                      f"{float(row['avg_conf'] or 0):>9.3f} "
                      f"{float(row['avg_ec'] or 0):>8.3f} "
                      f"{float(row['avg_epc'] or 0):>8.3f} "
                      f"{int(row['tral_count'] or 0):>6}")

        # Trade history
        trades = logger.get_all_trades()
        if not trades.empty:
            print(f"\n  ── TRADE HISTORY ({len(trades)} trades) ──────────────────")
            print(f"  {'Date':<20} {'Ticker':<8} {'Side':<6} {'Shares':>10} {'Price':>9} {'Value':>12}")
            print(f"  {'-'*70}")
            for _, row in trades.iterrows():
                print(f"  {str(row['executed_at'])[:19]:<20} "
                      f"{row['ticker']:<8} {row['side']:<6} "
                      f"{row['shares']:>10.4f} ${row['price']:>8.2f} "
                      f"${row['position_value']:>11,.2f}")

        # Regime breakdown from recent signals
        recent_sigs = logger.get_recent_signals(100)
        if not recent_sigs.empty and "bok_regime" in recent_sigs.columns:
            regime_counts = recent_sigs["bok_regime"].value_counts()
            print(f"\n  ── BOK REGIME DISTRIBUTION (last 100 signals) ──")
            for regime, count in regime_counts.items():
                pct = count / len(recent_sigs) * 100
                bar = "█" * int(pct / 5)
                print(f"  {str(regime):<16} {count:>4}  {pct:>5.1f}%  {bar}")

    except Exception as e:
        print(f"  DB error: {e}")

    print()


# ─── Watchlist ────────────────────────────────────────────────────────────────

GREEN_LIGHT = [
    "GOOGL", "NVDA", "MSFT", "META",         # Tech
    "CAT",   "GE",                             # Industrials
    "GS",    "MS",                             # Financials
    "XOM",   "CVX",   "COP",                  # Energy
    "WMT",   "TJX",                            # Consumer
    "AMZN",  "TSLA",  "COST",  "JPM",         # Additions
]


# ─── Utilities ───────────────────────────────────────────────────────────────

def print_header(title):
    print(f"\n{'='*66}")
    print(f"  {title}")
    print(f"{'='*66}")


# ─── Main Daily Cycle ─────────────────────────────────────────────────────────

def run_daily_cycle(dry_run=False, status_only=False):
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print_header(f"GSA v2 PAPER TRADER  —  {now}")
    print(f"  BOK 8-Mode  |  C_EMERICK={C_EMERICK:.4f}  |  Dual-Confidence Gate")

    # ── Connect ────────────────────────────────────────────────────────────
    print("\n[1/5] Connecting to Alpaca...")
    try:
        alpaca  = AlpacaClient()
        account = alpaca.get_account()
    except Exception as e:
        print(f"  ERROR: {e}")
        return

    equity        = float(account.get("equity", 0))
    cash          = float(account.get("cash", 0))
    buying_power  = float(account.get("buying_power", 0))
    unrealized_pl = float(account.get("unrealized_pl", 0))
    last_equity   = float(account.get("last_equity", equity))
    day_pl        = equity - last_equity

    print(f"  Account:        {account.get('account_number', 'N/A')}")
    print(f"  Equity:         ${equity:>12,.2f}")
    print(f"  Cash:           ${cash:>12,.2f}")
    print(f"  Buying Power:   ${buying_power:>12,.2f}")
    print(f"  Unrealized P&L: ${unrealized_pl:>+10,.2f}")
    print(f"  Day P&L:        ${day_pl:>+10,.2f}")
    print(f"  Total Return:   {(equity-100000)/100000*100:>+8.3f}% since Feb 27")

    positions  = alpaca.get_positions()
    n_pos = len(positions)
    print(f"\n  Open Positions: {n_pos}")
    for p in positions:
        pl     = float(p.get("unrealized_pl", 0))
        pl_pct = float(p.get("unrealized_plpc", 0)) * 100
        flag   = "✅" if pl > 0 else "❌"
        print(f"    {p['symbol']:8s}  {float(p['qty']):8.4f} shares  "
              f"@ ${float(p['current_price']):8.2f}  "
              f"P&L: ${pl:+8.2f} ({pl_pct:+5.2f}%) {flag}")

    if status_only:
        return

    # ── Log portfolio snapshot every run ──────────────────────────────────
    try:
        logger = TradeLogger()
        logger.log_portfolio(equity, cash, buying_power, unrealized_pl,
                             equity, day_pl, n_pos)
        print(f"\n  Portfolio snapshot logged.")
    except Exception as e:
        print(f"  DB log warning: {e}")
        logger = None

    # ── Market Data ────────────────────────────────────────────────────────
    print("\n[2/5] Downloading market data...")
    market_data = download_market_data(GREEN_LIGHT, period="90d")

    # ── Generate Signals ───────────────────────────────────────────────────
    print("\n[3/5] Generating BOK 8-mode signals...")
    gsa     = GSACore(lookback_short=7, lookback_long=60)
    signals = generate_signals(market_data, gsa)

    if logger:
        for ticker, sig in signals.items():
            try:
                logger.log_signal(
                    ticker, sig["action"], sig["confidence"],
                    sig["gile"], sig["xi_pd"], sig["regime"],
                    sig["price"], sig["tralse_ratio"],
                    ec=sig["ec"], epc=sig["epc"],
                    tral_state=sig["tral_state"],
                    bok_regime=sig["regime"]
                )
            except Exception:
                pass

    # Print signal table with dual-confidence
    print(f"\n  {'Ticker':<8} {'Action':<14} {'GILE':>6} {'EC':>6} {'EpC':>6} "
          f"{'Trade?':>7} {'Regime':<14} {'Price':>8}")
    print(f"  {'-'*78}")
    sorted_sigs = sorted(signals.items(),
                         key=lambda x: x[1]["gile"] * x[1]["ec"],
                         reverse=True)
    for ticker, sig in sorted_sigs:
        tradeable_str = "YES ✅" if sig["tradeable"] else ("TRAL⚠️" if sig["tral_state"] else "NO  ❌")
        print(f"  {ticker:<8} {sig['action']:<14} "
              f"{sig['gile']:>6.3f} {sig['ec']:>6.3f} {sig['epc']:>6.3f} "
              f"{tradeable_str:>7} {sig['regime']:<14} "
              f"${sig['price']:>8.2f}")

    # ── Rank and Size Orders ───────────────────────────────────────────────
    print("\n[4/5] Sizing orders (Dual-Confidence gate)...")
    orders = rank_and_size(signals, buying_power, max_positions=8,
                           max_position_pct=0.12)

    buy_orders  = [o for o in orders if o["side"] == "buy"]
    sell_orders = [o for o in orders if o["side"] == "sell"]

    current_tickers = {p["symbol"] for p in positions}
    sell_orders = [o for o in sell_orders if o["ticker"] in current_tickers]

    print(f"\n  Buy orders:  {len(buy_orders)}")
    for o in buy_orders:
        print(f"    BUY  {o['ticker']:8s}  {o['qty']:8.4f} shares  "
              f"@ ${o['price']:8.2f}  = ${o['value']:>10,.2f}  [{o['size_note']}]")

    print(f"  Sell orders: {len(sell_orders)}")
    for o in sell_orders:
        print(f"    SELL {o['ticker']:8s}  (close full position)")

    if dry_run:
        print("\n  [DRY RUN] Signals generated — no orders placed.")
        if logger:
            logger.log_run(
                f"DRY RUN — signals={len(signals)}", len(signals), 0,
                [{"ticker": t, **{k: v for k, v in s.items() if k != "reasons"}}
                 for t, s in sorted_sigs[:8]],
                {"equity": equity, "cash": cash, "positions": n_pos})
        return

    # ── Execute Orders ─────────────────────────────────────────────────────
    print("\n[5/5] Executing paper orders...")
    n_trades = 0

    for o in sell_orders:
        try:
            alpaca.close_position(o["ticker"])
            print(f"  CLOSED {o['ticker']}")
            if logger:
                logger.log_trade(o["ticker"], "sell", 0, o["price"], 0, "", "closed")
            n_trades += 1
        except Exception as e:
            print(f"  CLOSE ERROR {o['ticker']}: {e}")

    time.sleep(1)
    already_held = {p["symbol"] for p in alpaca.get_positions()}
    for o in buy_orders:
        if o["ticker"] in already_held:
            print(f"  SKIP {o['ticker']} (already held)")
            continue
        if o["qty"] < 0.001:
            continue
        try:
            result   = alpaca.place_order(o["ticker"], "buy", o["qty"])
            order_id = result.get("id", "")
            status   = result.get("status", "")
            print(f"  BUY  {o['ticker']:8s}  {o['qty']:.4f} shares → [{status}]")
            if logger:
                logger.log_trade(o["ticker"], "buy", o["qty"],
                                 o["price"], o["value"], order_id, status)
            n_trades += 1
        except requests.HTTPError as e:
            print(f"  ORDER ERROR {o['ticker']}: {e.response.text[:120]}")
        except Exception as e:
            print(f"  ORDER ERROR {o['ticker']}: {e}")

    # ── Summary ────────────────────────────────────────────────────────────
    print_header("RUN COMPLETE")
    print(f"  Signals generated:  {len(signals)}")
    print(f"  Orders executed:    {n_trades}")
    print(f"  Portfolio equity:   ${equity:,.2f}")
    print(f"  Total return:       {(equity-100000)/100000*100:+.3f}%")
    print()
    print("  Run daily to build the track record.")
    print("  Use --record for full performance report.")

    if logger:
        logger.log_run(
            f"Live run v2 — {n_trades} trades — BOK 8-mode",
            len(signals), n_trades,
            [{"ticker": t, **{k: v for k, v in s.items() if k != "reasons"}}
             for t, s in sorted_sigs[:8]],
            {"equity": equity, "cash": cash, "unrealized_pl": unrealized_pl,
             "positions": n_pos, "n_trades": n_trades})


# ─── Entry Point ─────────────────────────────────────────────────────────────

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="GSA Paper Trader v2")
    parser.add_argument("--status", action="store_true", help="Account status only")
    parser.add_argument("--dry",    action="store_true", help="Signals only, no orders")
    parser.add_argument("--record", action="store_true", help="Full performance report")
    parser.add_argument("--report", action="store_true", help="Full performance report (alias)")
    args = parser.parse_args()

    if args.record or args.report:
        try:
            alpaca = AlpacaClient()
        except Exception:
            alpaca = None
        show_performance_report(alpaca)
    else:
        run_daily_cycle(dry_run=args.dry, status_only=args.status)
