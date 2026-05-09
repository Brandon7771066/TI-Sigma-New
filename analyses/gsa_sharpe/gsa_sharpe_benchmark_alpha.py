"""
GSA Sharpe + SPY-benchmark + max-drawdown + framework-vs-conventional
alpha decomposition (Pass 17).

Per Brandon's Pass-16 (c16) directive (executed Pass 17):
  (a) compute SPY benchmark return over the EXACT same 63-day window;
  (b) compute Sharpe + max drawdown on the GSA daily-equity series;
  (c) decompose alpha into framework-component vs conventional-
      component contributions using the GSA layer architecture in
      GSA_TI_LAYER_SEPARATION.py;
  (d) optional C_EMERICK-gated entry/exit instrumentation (defer to
      Pass 18 if not enough order metadata).

Inputs:
  - analyses/gsa_sharpe/alpaca_portfolio_3M.json (Pass-17 fetch)
  - yfinance SPY for the same window

Per #69:
  - The "alpha decomposition" here is approximate. Without per-trade
    layer-attribution metadata, the best we can do is a *signal-
    overlap* analysis: how much of the GSA's daily return is
    explained by SPY beta (conventional) vs residual (which COULD
    be framework alpha, but COULD also be sector-tilt, idiosyncratic
    risk, or noise).
  - 63 trading days is a SMALL sample; Sharpe and beta estimates
    have wide CIs at this n. We report numbers, not certainties.
  - GSA on Alpaca is paper-trading; no transaction-cost drag.

Seed: 20260509.
"""
import json
import math
from pathlib import Path

import numpy as np

DATA = Path("analyses/gsa_sharpe/alpaca_portfolio_3M.json")
OUT = Path("analyses/gsa_sharpe/results.txt")


def load_alpaca():
    d = json.loads(DATA.read_text())
    eq = np.array(d["equity"], dtype=float)
    ts = np.array(d["timestamp"], dtype=float)
    return eq, ts, d["first_date"], d["last_date"]


def load_spy(first_date, last_date, n_target):
    import yfinance as yf
    df = yf.download("SPY", start=first_date, end=last_date,
                     progress=False, auto_adjust=True, threads=False)
    df = df.dropna()
    closes = df["Close"].values.flatten()
    return closes


def daily_returns(eq):
    return np.diff(eq) / eq[:-1]


def sharpe(returns, periods_per_year=252, rf_annual=0.04):
    """Annualized Sharpe ratio."""
    daily_rf = (1 + rf_annual) ** (1 / periods_per_year) - 1
    excess = returns - daily_rf
    mu = excess.mean(); sd = excess.std(ddof=1)
    if sd == 0:
        return float("nan")
    return float(mu / sd * math.sqrt(periods_per_year))


def max_drawdown(eq):
    peak = np.maximum.accumulate(eq)
    dd = (eq - peak) / peak
    return float(dd.min())


def beta_alpha(asset_returns, mkt_returns):
    """OLS beta + alpha (intercept) of asset vs market.
    Returns (alpha_daily, beta, r2)."""
    x = mkt_returns; y = asset_returns
    x_mean = x.mean(); y_mean = y.mean()
    cov = ((x - x_mean) * (y - y_mean)).mean()
    var = ((x - x_mean) ** 2).mean()
    beta = cov / var if var else float("nan")
    alpha = y_mean - beta * x_mean
    y_pred = alpha + beta * x
    ss_res = ((y - y_pred) ** 2).sum()
    ss_tot = ((y - y_mean) ** 2).sum()
    r2 = 1 - ss_res / ss_tot if ss_tot else float("nan")
    return float(alpha), float(beta), float(r2)


def main():
    eq, ts, first_date, last_date = load_alpaca()
    n = len(eq)
    print("=" * 70)
    print("GSA Sharpe + SPY-benchmark + alpha decomposition (Pass 17)")
    print("=" * 70)
    print(f"Window: {first_date} -> {last_date}  N={n} trading days")
    print(f"GSA equity: ${eq[0]:,.2f} -> ${eq[-1]:,.2f}  "
          f"total {(eq[-1]/eq[0]-1)*100:+.2f}%")

    # GSA returns
    gsa_r = daily_returns(eq)

    # SPY benchmark
    try:
        spy_close = load_spy(first_date, last_date, n)
        spy_r = daily_returns(spy_close)
        # Align lengths (yfinance and Alpaca calendars may differ by 0-2 days)
        m = min(len(gsa_r), len(spy_r))
        gsa_r_a = gsa_r[-m:]; spy_r_a = spy_r[-m:]
        spy_total = (spy_close[-1] / spy_close[0] - 1) * 100
        print(f"SPY: ${spy_close[0]:,.2f} -> ${spy_close[-1]:,.2f}  "
              f"total {spy_total:+.2f}%   (N_aligned={m})")
    except Exception as e:
        print(f"SPY fetch FAILED: {e}")
        spy_r_a = None
        spy_total = float("nan")

    # GSA Sharpe + drawdown
    gsa_sharpe = sharpe(gsa_r)
    gsa_dd = max_drawdown(eq)
    print()
    print("## GSA risk metrics")
    print(f"  Annualized Sharpe (rf=4%):  {gsa_sharpe:+.3f}")
    print(f"  Max drawdown:               {gsa_dd*100:+.2f}%")
    print(f"  Daily return mean:          {gsa_r.mean()*100:+.4f}%")
    print(f"  Daily return std:           {gsa_r.std(ddof=1)*100:.4f}%")
    print(f"  Annualized volatility:      {gsa_r.std(ddof=1)*math.sqrt(252)*100:.2f}%")

    if spy_r_a is not None:
        spy_sharpe = sharpe(spy_r_a)
        # Reconstruct SPY equity for DD calc
        spy_eq = np.cumprod(np.concatenate([[1.0], 1 + spy_r_a]))
        spy_dd = max_drawdown(spy_eq)
        print()
        print("## SPY benchmark risk metrics (same window)")
        print(f"  Annualized Sharpe (rf=4%):  {spy_sharpe:+.3f}")
        print(f"  Max drawdown:               {spy_dd*100:+.2f}%")
        print(f"  Daily return mean:          {spy_r_a.mean()*100:+.4f}%")
        print(f"  Daily return std:           {spy_r_a.std(ddof=1)*100:.4f}%")

        # Alpha / beta decomposition
        alpha_d, beta, r2 = beta_alpha(gsa_r_a, spy_r_a)
        alpha_ann = ((1 + alpha_d) ** 252 - 1) * 100
        print()
        print("## Alpha / beta decomposition (GSA vs SPY)")
        print(f"  Beta:                       {beta:+.3f}")
        print(f"  Alpha (daily):              {alpha_d*100:+.4f}%")
        print(f"  Alpha (annualized):         {alpha_ann:+.2f}%")
        print(f"  R^2:                        {r2:.3f}")

        # Decomposition reading
        print()
        print("## Framework-vs-conventional reading")
        explained_by_beta = beta * spy_r_a.mean() * len(spy_r_a) * 100
        unexplained = (gsa_r_a.mean() - beta * spy_r_a.mean()) * len(gsa_r_a) * 100
        print(f"  Total return:               {(eq[-1]/eq[0]-1)*100:+.2f}%")
        print(f"  Explained by SPY beta:      ~{explained_by_beta:+.2f}%")
        print(f"  Residual (alpha-portion):   ~{unexplained:+.2f}%")
        gsa_v_spy = (eq[-1]/eq[0] - 1) - (spy_total/100)
        print(f"  GSA - SPY total:            {gsa_v_spy*100:+.2f}%")

        print()
        print("## #69 caveats")
        print("  - N=63 trading days is small; Sharpe/beta CIs are wide.")
        print(f"  - Sharpe SE ~ sqrt(2/N) for unit-Sharpe sample => "
              f"~{math.sqrt(2/n):.2f}; reported Sharpe is point estimate.")
        print("  - Alpha decomposition is signal-overlap only, not")
        print("    per-layer GSA attribution; the residual could be")
        print("    framework-alpha OR sector-tilt OR luck.")
        print("  - Paper trading: no slippage / commission / borrow drag.")

    # Save numbers
    out = {
        "window_first_date": first_date, "window_last_date": last_date,
        "n_days": n,
        "gsa_total_return_pct": float((eq[-1]/eq[0]-1)*100),
        "gsa_sharpe_annualized": float(gsa_sharpe),
        "gsa_max_drawdown_pct": float(gsa_dd*100),
        "gsa_daily_mean_pct": float(gsa_r.mean()*100),
        "gsa_daily_std_pct": float(gsa_r.std(ddof=1)*100),
    }
    if spy_r_a is not None:
        out.update({
            "spy_total_return_pct": float(spy_total),
            "spy_sharpe_annualized": float(spy_sharpe),
            "spy_max_drawdown_pct": float(spy_dd*100),
            "alpha_annualized_pct": float(alpha_ann),
            "beta": float(beta), "r2": float(r2),
            "gsa_minus_spy_total_pct": float((eq[-1]/eq[0]-1)*100 - spy_total),
        })
    Path("analyses/gsa_sharpe/results.json").write_text(json.dumps(out, indent=2))
    print()
    print(f"Saved results.json ({len(out)} keys)")


if __name__ == "__main__":
    main()
