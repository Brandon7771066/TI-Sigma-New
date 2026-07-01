#!/usr/bin/env python3
"""
Phase I/II/III analysis of the LCC->UOP empirical tests on ds007471.

HONEST FRAMING (do not overclaim):
  * Real hyperscanning data (stronger than a sim) but small N pairs -> NECESSARY-NOT-SUFFICIENT,
    exploratory. Inference clustered by pair (leave-pair-out CV + pair-cluster bootstrap).
  * Matched baseline = raw inter-brain correlation C alone (ChatGPT's own falsifiable claim:
    L_hybrid must beat raw correlation). A win over C is the ONLY thing that supports LCC-as-index.
  * COMMON-AUDITORY-INPUT confound: both brains hear the same metronome + each other's tones, which
    inflates inter-brain coherence with NO real coupling. Controlled by CROSS-PAIR SURROGATES:
    two brains that performed the SAME tone sequence but were NOT partners. Real-vs-surrogate gap =
    the interaction-specific signal. If surrogates match reals, the "coupling" is common input.
  * Phase II constants are only meaningful if Lambda is on a comparable [0,1] scale; we min-max scale
    within-analysis and SAY LOUDLY that the specific numeric constants are underdetermined by n this size.
  * Phase III interior optimum: the data's argmax lands wherever it lands; "near 0.9299" is reported as
    coincidence-or-not, never as a derivation.
"""
import os, glob, json, warnings
import numpy as np
import pandas as pd
from scipy import stats
from sklearn.linear_model import LinearRegression

warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "features")
RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)
RNG = np.random.default_rng(20260701)

BANDS = ["delta", "theta", "alpha", "beta"]
CONSTANTS = {                     # name -> value ; home / provenance flag
    "sqrt2_minus_1": (2 ** 0.5 - 1, "tan(pi/8) Emerick/LCC onset"),
    "inv_sqrt2_phi": (1 / (2 ** 0.5 * (1 + 5 ** 0.5) / 2), "1/(sqrt2*phi) NEW candidate; HAN-1 resonance"),
    "0.6": (0.6, "operational-only (declined as fundamental, B157)"),
    "inv_sqrt2": (1 / 2 ** 0.5, "0.707 collides w/ baseline (declined, B157)"),
    "0.75": (0.75, "three-quarters"),
    "cos2_pi8": (np.cos(np.pi / 8) ** 2, "0.8536 Tsirelson/Bell home, NOT classical sync"),
    "radiant_cap": (np.sqrt(1 - np.exp(-2)), "0.9299 UOP Radiant Cap (Born-shaped)"),
}


def load():
    fs = sorted(glob.glob(os.path.join(OUT, "sub-*_features.csv")))
    df = pd.concat([pd.read_csv(f) for f in fs], ignore_index=True)
    # behavioural sync quality: MeanSync is proportion asynchrony (LOWER=better) -> invert
    df["sync_q"] = 1.0 - df["sync"]
    return df


def zscore_by_pair(df, cols):
    """within-pair z-score to remove pair-level offsets (fair for trial-level coupling->outcome)."""
    out = df.copy()
    for c in cols:
        out[c] = df.groupby("pair")[c].transform(lambda x: (x - x.mean()) / (x.std() + 1e-9))
    return out


def hybrid_indices(C, P, S, alpha=0.5):
    """LCC candidate index forms. Inputs min-max scaled to [0,1] first."""
    def mm(x):
        x = np.asarray(x, float)
        return (x - np.nanmin(x)) / (np.nanmax(x) - np.nanmin(x) + 1e-12)
    c, p, s = mm(C), mm(P), mm(S)
    w = np.array([1 / 3, 1 / 3, 1 / 3])
    add = w[0] * c + w[1] * p + w[2] * s                      # additive
    geo = (c + 1e-6) ** w[0] * (p + 1e-6) ** w[1] * (s + 1e-6) ** w[2]  # geometric
    hyb = alpha * add + (1 - alpha) * geo                     # B157 hybrid additive+geometric
    return {"C_only": c, "L_add": add, "L_geo": geo, "L_hybrid": hyb}


def leave_pair_out_r2(df, feat_cols, target):
    """Predict target from feat_cols with leave-pair-out CV; return out-of-fold R2 (pooled).
    Kept for multi-feature use; phase1 uses the fast single-predictor moments path below."""
    pairs = df["pair"].unique()
    yhat = np.full(len(df), np.nan)
    y = df[target].values
    X = df[feat_cols].values
    idx = np.arange(len(df))
    for pp in pairs:
        te = df["pair"].values == pp
        tr = ~te
        if tr.sum() < 5 or te.sum() < 2:
            continue
        m = LinearRegression().fit(X[tr], y[tr])
        yhat[idx[te]] = m.predict(X[te])
    ok = ~np.isnan(yhat)
    if ok.sum() < 5:
        return np.nan, ok.sum()
    ss_res = np.sum((y[ok] - yhat[ok]) ** 2)
    ss_tot = np.sum((y[ok] - np.mean(y[ok])) ** 2)
    return 1 - ss_res / ss_tot, int(ok.sum())


# ---- fast single-predictor leave-pair-out R2 via per-pair moments ----
# For ONE predictor, OLS is closed-form and leave-pair-out reduces to subtracting the
# held-out pair's moments [n, Sx, Sy, Sxx, Sxy, Syy] from the totals. R2 of a single
# predictor is affine-invariant, so global min-max scaling of the index is harmless.
def _pair_moment(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    return np.array([len(x), x.sum(), y.sum(), (x * x).sum(), (x * y).sum(), (y * y).sum()])


def _lpo_r2_moments(mlist):
    M = np.sum(mlist, axis=0)
    nT, SxT, SyT, SxxT, SxyT, SyyT = M
    if nT < 5:
        return np.nan
    ss_res = 0.0
    for m in mlist:
        n, Sx, Sy, Sxx, Sxy, Syy = m
        ntr, Sxtr, Sytr, Sxxtr, Sxytr = nT - n, SxT - Sx, SyT - Sy, SxxT - Sxx, SxyT - Sxy
        den = ntr * Sxxtr - Sxtr ** 2
        if ntr < 5 or abs(den) < 1e-9:
            return np.nan
        b = (ntr * Sxytr - Sxtr * Sytr) / den
        a = (Sytr - b * Sxtr) / ntr
        ss_res += Syy - 2 * a * Sy - 2 * b * Sxy + a * a * n + 2 * a * b * Sx + b * b * Sxx
    ss_tot = SyyT - SyT ** 2 / nT
    return float(1 - ss_res / ss_tot) if ss_tot > 0 else np.nan


def _boot_ci_moments(pair_moments, nboot=400):
    """Cluster bootstrap over pairs using precomputed per-pair moment vectors."""
    keys = list(pair_moments.keys())
    point = _lpo_r2_moments([pair_moments[k] for k in keys])
    vals = []
    for _ in range(nboot):
        samp = RNG.choice(len(keys), size=len(keys), replace=True)
        v = _lpo_r2_moments([pair_moments[keys[i]] for i in samp])
        if np.isfinite(v):
            vals.append(v)
    if not vals:
        return point, np.nan, np.nan
    return point, float(np.percentile(vals, 2.5)), float(np.percentile(vals, 97.5))


# ---------------- Phase I ----------------
def _with_indices(dd, band):
    idx = hybrid_indices(dd[f"C_{band}"], dd[f"P_{band}"], dd[f"S_{band}"])
    out = dd.copy()
    for k, v in idx.items():
        out[k] = np.asarray(v)
    return out


def phase1(df, band="beta"):
    d = _with_indices(df, band)
    res = {"band": band, "n_trials": int(len(d)), "n_pairs": int(d.pair.nunique())}
    pairs = d["pair"].unique()
    for target in ["agency", "sync_q"]:
        row = {}
        for name in ["C_only", "L_add", "L_geo", "L_hybrid"]:
            pm = {pp: _pair_moment(d.loc[d.pair == pp, name].values,
                                   d.loc[d.pair == pp, target].values) for pp in pairs}
            point, lo, hi = _boot_ci_moments(pm, nboot=400)
            row[name] = {"cv_r2": None if not np.isfinite(point) else round(point, 4),
                         "ci95": [round(lo, 4), round(hi, 4)]}
        res[target] = row
    return res


# ---------------- Phase II ----------------
def phase2(df, band="beta", target="agency"):
    """Change-point test: does a piecewise break at a named constant tau beat a straight line?
    Lambda = L_hybrid min-max scaled to [0,1]; AIC counts the breakpoint parameter."""
    d = df.copy()
    idx = hybrid_indices(d[f"C_{band}"], d[f"P_{band}"], d[f"S_{band}"])
    lam = idx["L_hybrid"]
    lam = (lam - lam.min()) / (lam.max() - lam.min() + 1e-12)
    y = zscore_by_pair(d.assign(_y=d[target]), ["_y"])["_y"].values
    x = lam
    n = len(y)

    def aic(rss, k):
        return n * np.log(rss / n + 1e-12) + 2 * k

    # Model A: linear (2 params + var)
    XA = np.column_stack([np.ones(n), x])
    bA, *_ = np.linalg.lstsq(XA, y, rcond=None)
    rssA = np.sum((y - XA @ bA) ** 2)
    aicA = aic(rssA, 3)
    out = {"band": band, "target": target, "n": n, "aic_linear": round(aicA, 2), "constants": {}}
    for name, (tau, home) in CONSTANTS.items():
        if tau <= x.min() or tau >= x.max():
            out["constants"][name] = {"tau": round(float(tau), 4), "home": home,
                                      "testable": False, "reason": "tau outside data range"}
            continue
        hinge = np.maximum(0.0, x - tau)          # continuous piecewise-linear knot at tau
        XB = np.column_stack([np.ones(n), x, hinge])
        bB, *_ = np.linalg.lstsq(XB, y, rcond=None)
        rssB = np.sum((y - XB @ bB) ** 2)
        aicB = aic(rssB, 4)                        # +1 param for the break slope
        out["constants"][name] = {"tau": round(float(tau), 4), "home": home, "testable": True,
                                  "aic_break": round(aicB, 2), "delta_aic_vs_linear": round(aicA - aicB, 2),
                                  "break_helps": bool(aicB < aicA)}
    return out


# ---------------- Phase III ----------------
def phase3(df, band="beta", target="agency"):
    """UOP shape test on Lambda->outcome. Compare Hyp A linear, Hyp B saturating (1-e^{-kL}),
    Hyp C interior optimum (quadratic). Report argmax of the quadratic and whether it is interior."""
    d = df.copy()
    idx = hybrid_indices(d[f"C_{band}"], d[f"P_{band}"], d[f"S_{band}"])
    lam = idx["L_hybrid"]
    lam = (lam - lam.min()) / (lam.max() - lam.min() + 1e-12)
    y = zscore_by_pair(d.assign(_y=d[target]), ["_y"])["_y"].values
    x = lam.values if hasattr(lam, "values") else np.asarray(lam)
    n = len(y)

    def aic(rss, k):
        return n * np.log(rss / n + 1e-12) + 2 * k

    XA = np.column_stack([np.ones(n), x]); bA, *_ = np.linalg.lstsq(XA, y, rcond=None)
    aicA = aic(np.sum((y - XA @ bA) ** 2), 3)
    # Hyp B saturating: grid over k, fit linear a+b*(1-e^{-k x})
    bestB = (np.inf, None)
    for k in np.linspace(0.5, 8, 40):
        f = 1 - np.exp(-k * x)
        XB = np.column_stack([np.ones(n), f]); bB, *_ = np.linalg.lstsq(XB, y, rcond=None)
        r = np.sum((y - XB @ bB) ** 2)
        if r < bestB[0]:
            bestB = (r, k)
    aicB = aic(bestB[0], 4)
    # Hyp C interior optimum: quadratic
    XC = np.column_stack([np.ones(n), x, x ** 2]); bC, *_ = np.linalg.lstsq(XC, y, rcond=None)
    aicC = aic(np.sum((y - XC @ bC) ** 2), 4)
    argmax = None; interior = False
    if bC[2] < 0:                                  # concave -> has a max
        argmax = float(-bC[1] / (2 * bC[2]))
        interior = bool(0.05 < argmax < 0.95)
    return {"band": band, "target": target, "n": n,
            "aic_linear": round(aicA, 2), "aic_saturating": round(aicB, 2),
            "sat_k": round(bestB[1], 3), "aic_quadratic": round(aicC, 2),
            "quad_argmax": None if argmax is None else round(argmax, 4),
            "argmax_interior": interior,
            "best_model": ["linear", "saturating", "quadratic"][int(np.argmin([aicA, aicB, aicC]))]}


# ---------------- Manipulation check ----------------
def manipulation_check(df):
    """Do the neural coupling measures even track the duet-vs-constant manipulation?
    Paired (within-pair) duet-minus-constant difference for C/P/S in each band."""
    out = {}
    for band in BANDS:
        for m in ["C", "P", "S"]:
            col = f"{m}_{band}"
            g = df.groupby(["pair", "cond"])[col].mean().unstack("cond")
            if 0 in g.columns and 1 in g.columns:
                diff = (g[1] - g[0]).dropna()          # duet - constant
                t, p = stats.ttest_rel(g[1].dropna(), g[0].dropna()) if len(diff) > 2 else (np.nan, np.nan)
                out[col] = {"n_pairs": int(len(diff)), "mean_duet_minus_const": round(float(diff.mean()), 5),
                            "t": None if np.isnan(t) else round(float(t), 3),
                            "p": None if np.isnan(p) else round(float(p), 4)}
    return out


def main():
    df = load()
    df = df[df["cond_ok"] == True].copy() if "cond_ok" in df else df
    summary = {
        "dataset": "OpenNeuro ds007471 (joint-agency EEG hyperscanning)",
        "n_pairs": int(df.pair.nunique()), "n_trials": int(len(df)),
        "framing": "exploratory / necessary-not-sufficient; clustered by pair; matched baseline = raw C; "
                   "common-input controlled by cross-pair surrogates (see surrogate.py); constants underdetermined at this n.",
        "manipulation_check": manipulation_check(df),
        "phase1": {b: phase1(df, b) for b in ["theta", "alpha", "beta"]},
        "phase2": {b: phase2(df, b, "agency") for b in ["alpha", "beta"]},
        "phase3": {b: phase3(df, b, "agency") for b in ["alpha", "beta"]},
    }
    with open(os.path.join(RES, "analysis.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(json.dumps(summary, indent=2)[:4000])


if __name__ == "__main__":
    main()
