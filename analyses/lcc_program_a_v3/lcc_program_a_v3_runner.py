"""
LCC Program A v3 — second φ-transform proxy (Pass 18, d17 directive).

Pass 17 result: Pearson-rolling φ-transform R-3 cleared 5/7 pairs above
C_EMERICK = 0.4370. Brandon Pass-18 directive: "Require triangulating
proxy if better results can be obtained. Otherwise, accept phi
transform as is."

This v3 runner:
  (a) recomputes the Pass-17 Pearson-rolling proxy as control;
  (b) computes a SECOND, INDEPENDENT proxy: rolling-20-day mutual
      information between asset and SPY, normalized to [0, 1] via
      I(X;Y)/min(H(X), H(Y));
  (c) compares: did MI proxy clear MORE pairs than Pearson?
      - if yes: triangulation REQUIRED (R-3 needs both proxies)
      - if no:  Pearson-rolling RATIFIED as canonical R-3 spec

Per #69:
  - MI proxy uses K=8 quantile bins per series; bin-count is a
    hyperparameter (Pass-19 candidate to test K=4,16,32 sensitivity).
  - "Better" defined operationally as "more pairs above C". Other
    "better" definitions exist (higher mean R, fewer false-positives
    on a control basket); this is the simplest decision rule that
    matches Brandon's directive.
  - Both proxies derive from the same daily-log-returns window, so
    they are not fully independent — MI captures non-linear
    dependence Pearson misses, but they share the same *data*. A
    truly independent proxy would use a different data source
    (e.g. options-IV cross-section).

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
MI_BINS = 8

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


def normalized_mi(x, y, bins=MI_BINS):
    """Normalized MI: I(X;Y) / min(H(X), H(Y)), in [0, 1]."""
    if len(x) < bins * 2: return 0.0
    # Quantile bins for each series independently
    try:
        x_b = pd.qcut(x, bins, labels=False, duplicates="drop")
        y_b = pd.qcut(y, bins, labels=False, duplicates="drop")
    except Exception:
        return 0.0
    if x_b is None or y_b is None: return 0.0
    # Joint hist
    nx = int(x_b.max()) + 1; ny = int(y_b.max()) + 1
    if nx < 2 or ny < 2: return 0.0
    joint = np.zeros((nx, ny))
    for a, b in zip(x_b, y_b):
        joint[int(a), int(b)] += 1
    joint /= joint.sum()
    px = joint.sum(axis=1); py = joint.sum(axis=0)
    # H(X), H(Y)
    def H(p):
        p = p[p > 0]; return float(-(p * np.log2(p)).sum())
    Hx, Hy = H(px), H(py)
    if min(Hx, Hy) <= 0: return 0.0
    # I(X;Y) = sum p(x,y) log2 p(x,y)/(p(x)p(y))
    mi = 0.0
    for i in range(nx):
        for j in range(ny):
            if joint[i, j] > 0:
                mi += joint[i, j] * np.log2(joint[i, j] / (px[i] * py[j]))
    return float(max(0.0, mi / min(Hx, Hy)))


def rolling_pearson_phi(returns_a, returns_mkt, window=ROLLING_WINDOW):
    s_a = pd.Series(returns_a); s_m = pd.Series(returns_mkt)
    return s_a.rolling(window).corr(s_m).dropna().values


def rolling_mi_phi(returns_a, returns_mkt, window=ROLLING_WINDOW):
    out = []
    for i in range(window, len(returns_a) + 1):
        out.append(normalized_mi(returns_a[i-window:i], returns_mkt[i-window:i]))
    return np.asarray(out, dtype=float)


def run_proxy(label, phi_fn, ret, spy):
    print(f"\n## {label}")
    print(f"  C_EMERICK = {C_EMERICK:.5f}")
    phis = {}
    for t in ret.columns:
        if t == "SPY": continue
        phis[t] = phi_fn(ret[t].values, spy)
    rows = []
    for a, b in PAIRS:
        if a not in phis or b not in phis: continue
        m = min(len(phis[a]), len(phis[b]))
        if m < 30: continue
        x = phis[a][-m:]; y = phis[b][-m:]
        # NaN-safe
        mask = ~(np.isnan(x) | np.isnan(y))
        x = x[mask]; y = y[mask]
        if len(x) < 30: continue
        R = gauss_lag_xcorr(x, y)
        verdict = "ABOVE" if R >= C_EMERICK else "below"
        rows.append({"pair": f"{a}/{b}", "n": len(x), "R": R, "above": R >= C_EMERICK})
        print(f"  {a:>5}/{b:<5}  N={len(x):4d}  R_lcc={R:+.4f}  {verdict} C")
    above = sum(1 for r in rows if r["above"])
    mean_R = np.mean([r["R"] for r in rows]) if rows else float("nan")
    print(f"  Summary: {above}/{len(rows)} pairs above C  (mean R = {mean_R:+.4f})")
    return rows, above, mean_R


def main():
    print("=" * 72)
    print("LCC Program A v3 — second φ-transform proxy (Pass 18)")
    print("=" * 72)
    tickers = list({t for pair in PAIRS for t in pair} | {"SPY"})
    df = fetch(tickers, period="5y", interval="1d")
    ret = np.log(df).diff().dropna()
    spy = ret["SPY"].values

    rows_p, above_p, mean_p = run_proxy(
        "Proxy A: rolling-20-day Pearson(asset, SPY) (Pass-17 R-3 control)",
        rolling_pearson_phi, ret, spy)

    rows_m, above_m, mean_m = run_proxy(
        "Proxy B: rolling-20-day normalized MI(asset, SPY) (Pass-18 NEW)",
        rolling_mi_phi, ret, spy)

    print()
    print("=" * 72)
    print("VERDICT — Pass 18 LCC v3")
    print("=" * 72)
    print(f"  Proxy A (Pearson-rolling): {above_p}/{len(rows_p)} above C, mean R = {mean_p:+.4f}")
    print(f"  Proxy B (MI-rolling):      {above_m}/{len(rows_m)} above C, mean R = {mean_m:+.4f}")
    print()
    if above_m > above_p:
        print("  → Proxy B (MI) clears MORE pairs than Proxy A (Pearson).")
        print("  → DIRECTIVE: TRIANGULATION REQUIRED.")
        print("    R-3 canonical spec must combine both proxies (e.g. require")
        print("    pair to clear C under BOTH or under a fused metric).")
    elif above_m == above_p and abs(mean_m - mean_p) < 0.05:
        print("  → Proxies cleared the SAME pair-count and mean R is close.")
        print("  → DIRECTIVE: Pass-17 Pearson-rolling RATIFIED as canonical R-3,")
        print("    with MI as a confirmed-but-redundant cross-check.")
    else:
        print("  → Proxy A clears as many or more pairs than Proxy B.")
        print("  → DIRECTIVE: Pearson-rolling RATIFIED as canonical R-3.")
        print("    MI proxy did not produce 'better results' per Brandon's bar.")

    # Pair-level agreement matrix
    print()
    print("## Pair-level agreement (above-C)")
    print(f"  {'pair':<12} {'Pearson':>8} {'MI':>8} {'agree':>8}")
    by_pair = {}
    for r in rows_p: by_pair.setdefault(r["pair"], {})["P"] = r
    for r in rows_m: by_pair.setdefault(r["pair"], {})["M"] = r
    agree_n = 0; total = 0
    for pair, d in by_pair.items():
        if "P" not in d or "M" not in d: continue
        p_above = d["P"]["above"]; m_above = d["M"]["above"]
        agree = p_above == m_above
        if agree: agree_n += 1
        total += 1
        print(f"  {pair:<12} {'YES' if p_above else 'no':>8} "
              f"{'YES' if m_above else 'no':>8} {'YES' if agree else 'NO':>8}")
    print(f"  Agreement: {agree_n}/{total} pairs")


if __name__ == "__main__":
    main()
