"""
GSA Residual Sharpe — canonical performance metric per Pass 19 s18
(ratified by Brandon: "s18 affirmed!").

Residual Sharpe = Sharpe of the SPY-beta-stripped GSA return series.
Operationally: alpha / std(residual) * sqrt(252) - daily_rf adjustment.

This implements UOP §3.5 — the "Sharpe-on-uncorrelated-return" that the
diversifier policy is supposed to be measured on. Raw Sharpe rewards
passive market exposure; for a diversifier whose entire reason for
existing is beta ≈ 0, raw Sharpe is the wrong metric.

Inputs:
  - analyses/gsa_sharpe/alpaca_portfolio_3M.json (Pass 17 fetch)
  - yfinance SPY for the same window

Per #69:
  - When beta ≈ 0 (current GSA snapshot), residual Sharpe will be
    very close to raw Sharpe by construction. The metric matters most
    when beta drifts non-zero in future windows.
  - N=63 days has wide Sharpe CIs (~ sqrt(2/N) ≈ 0.18 SE for unit-
    Sharpe sample). Point estimates only.
  - Paper-trading data, no slippage / commission / borrow drag.

Seed: 20260509.
"""
import json
import math
from pathlib import Path

import numpy as np

DATA = Path("analyses/gsa_sharpe/alpaca_portfolio_3M.json")
OUT_TXT = Path("analyses/gsa_residual_sharpe/results.txt")
OUT_JSON = Path("analyses/gsa_residual_sharpe/results.json")


def load_alpaca():
    d = json.loads(DATA.read_text())
    eq = np.array(d["equity"], dtype=float)
    return eq, d["first_date"], d["last_date"]


def load_spy(first_date, last_date):
    import yfinance as yf
    df = yf.download("SPY", start=first_date, end=last_date,
                     progress=False, auto_adjust=True, threads=False)
    return df.dropna()["Close"].values.flatten()


def daily_returns(eq):
    return np.diff(eq) / eq[:-1]


def sharpe(returns, periods_per_year=252, rf_annual=0.04):
    daily_rf = (1 + rf_annual) ** (1 / periods_per_year) - 1
    excess = returns - daily_rf
    mu = excess.mean(); sd = excess.std(ddof=1)
    if sd == 0:
        return float("nan")
    return float(mu / sd * math.sqrt(periods_per_year))


def beta_alpha(asset_r, mkt_r):
    x = mkt_r; y = asset_r
    x_mean = x.mean(); y_mean = y.mean()
    cov = ((x - x_mean) * (y - y_mean)).mean()
    var = ((x - x_mean) ** 2).mean()
    beta = cov / var if var else float("nan")
    alpha = y_mean - beta * x_mean
    return float(alpha), float(beta)


def residual_sharpe(asset_r, mkt_r, periods_per_year=252, rf_annual=0.04):
    """Sharpe of the OLS residual after stripping market beta.

    Returns dict with:
        residual_sharpe   - alpha-only Sharpe (canonical s18 metric)
        residual_std      - std of residual returns (annualized)
        alpha_daily       - OLS intercept
        beta              - OLS slope
        alpha_annualized  - geometric annualization of alpha
    """
    alpha, beta = beta_alpha(asset_r, mkt_r)
    residual = asset_r - alpha - beta * mkt_r
    daily_rf = (1 + rf_annual) ** (1 / periods_per_year) - 1
    sd_res = residual.std(ddof=1)

    # alpha-only Sharpe: numerator is alpha (residual mean is ~0 by OLS)
    if sd_res == 0:
        sharpe_alpha = float("nan")
    else:
        sharpe_alpha = (alpha - daily_rf) / sd_res * math.sqrt(periods_per_year)

    return {
        "alpha_daily": alpha,
        "beta": beta,
        "residual_std_daily": float(sd_res),
        "residual_std_annualized_pct": float(sd_res * math.sqrt(periods_per_year) * 100),
        "alpha_annualized_pct": float(((1 + alpha) ** periods_per_year - 1) * 100),
        "residual_sharpe_annualized": sharpe_alpha,
    }


def main():
    OUT_TXT.parent.mkdir(parents=True, exist_ok=True)
    eq, first_date, last_date = load_alpaca()
    n = len(eq)

    lines = []
    def p(s=""):
        print(s); lines.append(s)

    p("=" * 70)
    p("GSA Residual Sharpe — canonical s18 metric (Pass 19)")
    p("=" * 70)
    p(f"Window: {first_date} -> {last_date}  N={n} trading days")

    gsa_r = daily_returns(eq)
    raw_sh = sharpe(gsa_r)

    try:
        spy_close = load_spy(first_date, last_date)
        spy_r = daily_returns(spy_close)
        m = min(len(gsa_r), len(spy_r))
        gsa_r_a = gsa_r[-m:]; spy_r_a = spy_r[-m:]
        spy_sh = sharpe(spy_r_a)
        p(f"SPY aligned N={m}")
    except Exception as e:
        p(f"SPY fetch FAILED: {e} — cannot compute residual Sharpe.")
        return

    res = residual_sharpe(gsa_r_a, spy_r_a)

    p("")
    p("## Comparison: raw Sharpe vs residual Sharpe (canonical)")
    p(f"  Raw Sharpe (GSA, vs cash):       {raw_sh:+.4f}")
    p(f"  Raw Sharpe (SPY, vs cash):       {spy_sh:+.4f}")
    p(f"  RESIDUAL Sharpe (alpha-only):    {res['residual_sharpe_annualized']:+.4f}  <- s18 canonical")
    p("")
    p("## Decomposition")
    p(f"  Beta (GSA vs SPY):               {res['beta']:+.6f}")
    p(f"  Alpha (daily):                   {res['alpha_daily']*100:+.6f}%")
    p(f"  Alpha (annualized):              {res['alpha_annualized_pct']:+.2f}%")
    p(f"  Residual return std (annual.):   {res['residual_std_annualized_pct']:.2f}%")
    p("")
    p("## Reading")
    delta = res["residual_sharpe_annualized"] - raw_sh
    if abs(res["beta"]) < 0.05:
        p(f"  Beta ≈ 0 (|{res['beta']:+.4f}| < 0.05) — true diversifier;")
        p(f"  residual Sharpe ({res['residual_sharpe_annualized']:+.3f}) ≈ raw Sharpe")
        p(f"  ({raw_sh:+.3f}) by construction (delta={delta:+.4f}).")
        p(f"  Going forward, this metric will diverge from raw Sharpe")
        p(f"  if beta drifts non-zero — that drift is what residual")
        p(f"  Sharpe correctly strips out per UOP §3.5.")
    else:
        p(f"  Beta = {res['beta']:+.3f} is materially non-zero;")
        p(f"  residual Sharpe ({res['residual_sharpe_annualized']:+.3f}) differs")
        p(f"  from raw Sharpe ({raw_sh:+.3f}) by {delta:+.4f}.")
        p(f"  This delta is the metric correction UOP requires.")
    p("")
    p("## #69 caveats")
    p(f"  - N={m} → Sharpe SE ~ sqrt(2/N) ≈ {math.sqrt(2/m):.3f}; CI is wide.")
    p(f"  - Paper trading data; no transaction-cost drag.")
    p(f"  - Residual Sharpe assumes OLS linearity; if GSA has non-")
    p(f"    linear market exposure, OLS residual is approximate.")

    out = {
        "window_first_date": first_date, "window_last_date": last_date,
        "n_aligned": int(m),
        "raw_sharpe_gsa": float(raw_sh),
        "raw_sharpe_spy": float(spy_sh),
        **res,
        "residual_minus_raw_sharpe": float(delta),
        "metric_role": "canonical_GSA_performance_metric_per_Pass19_s18",
    }
    OUT_JSON.write_text(json.dumps(out, indent=2))
    OUT_TXT.write_text("\n".join(lines) + "\n")
    p(""); p(f"Saved {OUT_JSON} and {OUT_TXT}")


if __name__ == "__main__":
    main()
