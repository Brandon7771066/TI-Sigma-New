"""
LCC Program A v2 — multi-horizon + φ-transform retry (Pass 17).

Pass-16 (d16) Brandon-decision menu offered three readings of the
0/8-cleared-C result:
  R-1: framework-consistent (need intraday or weekly horizon)
  R-2: revisionist (threshold too high to ever clear on returns)
  R-3: methodological (need φ-transform spec, not raw returns)

This v2 runner tests R-1 and R-3 simultaneously without prejudging:
  (a) Same 8 pairs at WEEKLY horizon over 5 years (R-1 weekly).
  (b) Same 8 pairs at DAILY horizon over 5 years (control).
  (c) Same 8 pairs with a φ-transform proxy: rolling-20-day Pearson
      correlation between log-returns, sampled daily — i.e. Φ(t) is
      treated as a "coherence amplitude" between A and B at time t,
      and we then run R(Φ_A, Φ_B) where Φ_A is derived from A vs
      market (SPY) and Φ_B from B vs market (R-3 φ-transform).

C_EMERICK = 0.4370 is the gating threshold throughout.

Per #69:
  - R-2 cannot be tested affirmatively (you can't prove a threshold
    is "too high" — you can only fail to clear it across many trials).
    Successive non-clearing strengthens R-2's plausibility.
  - φ-transform proxy is one specific operationalization. Other
    operationalizations exist; this is a first-cut, not the only one.
  - Intraday data not used this Pass (yfinance free tier rate-limits;
    Pass-18 candidate if Brandon wants minute-bar data).

Seed: 20260509.
"""
import math, sys, warnings
from pathlib import Path

import numpy as np
import pandas as pd

warnings.filterwarnings("ignore")

PHI = (1 + math.sqrt(5)) / 2
C_EMERICK = 1 / (PHI * math.sqrt(2))
SIGMA_LAG = 5.0
LAG_WINDOW = 20
ROLLING_WINDOW = 20

PAIRS = [("AAPL","MSFT"),("JPM","GS"),("XOM","CVX"),("KO","PEP"),
         ("AAPL","JPM"),("XOM","AAPL"),("XLE","USO"),("SPY","AAPL")]


def fetch(tickers, period="5y", interval="1d"):
    import yfinance as yf
    df = yf.download(tickers, period=period, interval=interval,
                     progress=False, auto_adjust=True, threads=False)["Close"]
    return df.dropna()


def gauss_lag_xcorr(x, y, sigma=SIGMA_LAG, max_lag=LAG_WINDOW):
    x = np.asarray(x, float); y = np.asarray(y, float)
    x = (x - x.mean()) / (x.std() if x.std() > 0 else 1.0)
    y = (y - y.mean()) / (y.std() if y.std() > 0 else 1.0)
    lags = np.arange(-max_lag, max_lag + 1)
    w = np.exp(-0.5 * (lags / sigma) ** 2); w /= w.sum()
    rs = []
    for tau in lags:
        if tau >= 0: xt = x[: len(x) - tau]; yt = y[tau:]
        else: xt = x[-tau:]; yt = y[: len(y) + tau]
        if len(xt) < 5: rs.append(0.0); continue
        c = np.corrcoef(xt, yt)[0, 1]
        rs.append(c if not math.isnan(c) else 0.0)
    return float(np.dot(w, rs))


def phi_transform(returns_a, returns_mkt, window=ROLLING_WINDOW):
    """Rolling Pearson(A, market) over window — proxy for coherence Φ_A."""
    s_a = pd.Series(returns_a); s_m = pd.Series(returns_mkt)
    return s_a.rolling(window).corr(s_m).dropna().values


def run_horizon(label, period, interval):
    print(f"\n## {label}: period={period}, interval={interval}")
    print(f"  C_EMERICK = {C_EMERICK:.5f}")
    rows = []
    for a, b in PAIRS:
        try:
            df = fetch([a, b], period=period, interval=interval)
        except Exception as e:
            print(f"  {a}/{b}: fetch FAILED -> {e}"); continue
        if df is None or len(df) < 30:
            print(f"  {a}/{b}: insufficient data"); continue
        ret = np.log(df).diff().dropna()
        x = ret[a].values; y = ret[b].values
        R = gauss_lag_xcorr(x, y)
        above = "ABOVE" if R >= C_EMERICK else "below"
        rows.append({"pair": f"{a}/{b}", "n": len(x), "R": R, "above": R >= C_EMERICK})
        print(f"  {a:>5}/{b:<5}  N={len(x):4d}  R_lcc={R:+.4f}  {above} C")
    above_n = sum(1 for r in rows if r["above"])
    print(f"  Summary: {above_n}/{len(rows)} pairs above C")
    return rows


def run_phi_transform():
    print(f"\n## phi-transform R-3: rolling-{ROLLING_WINDOW}-day Pearson(asset, SPY)")
    print(f"  C_EMERICK = {C_EMERICK:.5f}")
    # Fetch all assets + SPY at daily, 5y
    tickers = list({t for pair in PAIRS for t in pair} | {"SPY"})
    try:
        df = fetch(tickers, period="5y", interval="1d")
    except Exception as e:
        print(f"  fetch FAILED -> {e}"); return []
    ret = np.log(df).diff().dropna()
    spy = ret["SPY"].values
    # Compute Φ_A for each ticker
    phis = {}
    for t in tickers:
        if t == "SPY": continue
        phis[t] = phi_transform(ret[t].values, spy)
    rows = []
    for a, b in PAIRS:
        if a not in phis or b not in phis: continue
        # Align lengths
        m = min(len(phis[a]), len(phis[b]))
        x = phis[a][-m:]; y = phis[b][-m:]
        R = gauss_lag_xcorr(x, y)
        above = "ABOVE" if R >= C_EMERICK else "below"
        rows.append({"pair": f"{a}/{b}", "n": m, "R": R, "above": R >= C_EMERICK})
        print(f"  {a:>5}/{b:<5}  N={m:4d}  R_lcc(Φ_A,Φ_B)={R:+.4f}  {above} C")
    above_n = sum(1 for r in rows if r["above"])
    print(f"  Summary: {above_n}/{len(rows)} pairs above C")
    return rows


def main():
    print("=" * 72)
    print("LCC Program A v2 — multi-horizon + phi-transform (Pass 17)")
    print("=" * 72)
    daily = run_horizon("R-1 control: DAILY 5y", "5y", "1d")
    weekly = run_horizon("R-1 weekly: WEEKLY 5y", "5y", "1wk")
    phi = run_phi_transform()
    # Combined verdict
    print()
    print("=" * 72)
    print("VERDICT — Pass 17 LCC v2")
    print("=" * 72)
    for label, r in [("daily 5y", daily), ("weekly 5y", weekly), ("phi-transform", phi)]:
        if r: print(f"  {label}: {sum(1 for x in r if x['above'])}/{len(r)} above C")
    return 0


if __name__ == "__main__":
    sys.exit(main())
