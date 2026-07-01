"""
Gate-first LCC / UOP empirical test on the Depresjon actigraphy dataset.

Dataset: Garcia-Ceja et al. 2018 (Simula), 23 depressed (condition_*) + 32 control
(control_*), per-minute wrist actigraphy, ~2 weeks each; scores.csv carries afftype
and MADRS (madrs1 start, madrs2 end) for the depressed group.

Pipeline (per ChatGPT gate-first guidance, adapted to WITHIN-PERSON rhythm coupling):
    manipulation/group-signal gate -> surrogate control gate -> LCC index (CV) ->
    threshold/constant test -> UOP/Radiant-Cap interior-optimum test.
Constants are tested ONLY if the first two gates pass (revised decision rule).

Within-person LCC family (all from per-minute -> hourly activity):
    C = day-to-day circadian coherence (mean corr of each day's 24h profile to the
        subject template)                                   [the "raw coupling" C]
    P = cross-validated AR(3) predictive gain on the hourly series (activity_t ->
        future state), R^2 over held-out days vs mean baseline
    S = interdaily stability IS (Van Someren nonparametric circadian stability)
Also reports IV (intradaily variability), RA (relative amplitude, M10/L5).

Outcome: depressed (1) vs control (0); and MADRS severity within the depressed group.

Honesty rails (EVD-1 / #69): REAL data only; surrogate-corrected; small-n; report
BOTH theory- and measurement-limitation readings; candidate constants are graded
resonance tests, never derivations; decline numerology.
"""
import json, os, warnings
import numpy as np
import pandas as pd
from pathlib import Path
from scipy import stats
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import LeaveOneOut
from sklearn.preprocessing import StandardScaler

warnings.filterwarnings("ignore")
RNG = np.random.default_rng(20260701)
DATA = Path(__file__).resolve().parent / "data" / "data"
RES = Path(__file__).resolve().parent / "results"
RES.mkdir(exist_ok=True)
N_SURR = 300


# ----------------------------- feature helpers -----------------------------
def load_subject(fp):
    df = pd.read_csv(fp)
    df["timestamp"] = pd.to_datetime(df["timestamp"])
    df = df.set_index("timestamp").sort_index()
    # hourly mean activity
    hourly = df["activity"].resample("1h").mean().dropna()
    return hourly


def day_matrix(hourly):
    """Return (n_days x 24) matrix of complete days only."""
    h = hourly.copy()
    grp = h.groupby([h.index.date, h.index.hour]).mean()
    piv = grp.unstack()  # rows=date, cols=hour
    piv = piv.reindex(columns=range(24))
    full = piv.dropna(axis=0, how="any")  # complete days
    return full.values


def coherence_C(dm):
    """Mean correlation of each day's 24h profile to the subject mean template."""
    if dm.shape[0] < 3:
        return np.nan
    tmpl = dm.mean(axis=0)
    if np.std(tmpl) == 0:
        return np.nan
    cs = []
    for row in dm:
        if np.std(row) == 0:
            continue
        cs.append(np.corrcoef(row, tmpl)[0, 1])
    return float(np.nanmean(cs)) if cs else np.nan


def interdaily_stability(hourly):
    """Van Someren IS on hourly series (0..1)."""
    x = hourly.values.astype(float)
    n = len(x)
    if n < 48:
        return np.nan
    hours = hourly.index.hour
    xbar = x.mean()
    denom = np.sum((x - xbar) ** 2)
    if denom == 0:
        return np.nan
    # per-hour-of-day mean
    hourly_means = pd.Series(x).groupby(hours.values).mean()
    p = 24
    num = n * np.sum((hourly_means.values - xbar) ** 2)
    return float(num / (p * denom))


def intradaily_variability(hourly):
    x = hourly.values.astype(float)
    n = len(x)
    if n < 48:
        return np.nan
    xbar = x.mean()
    denom = np.sum((x - xbar) ** 2)
    if denom == 0:
        return np.nan
    num = n * np.sum(np.diff(x) ** 2)
    return float(num / ((n - 1) * denom))


def relative_amplitude(hourly):
    """RA = (M10 - L5)/(M10 + L5) using hourly rolling windows."""
    x = hourly.values.astype(float)
    if len(x) < 24:
        return np.nan
    m10 = pd.Series(x).rolling(10).mean().max()
    l5 = pd.Series(x).rolling(5).mean().min()
    if (m10 + l5) == 0:
        return np.nan
    return float((m10 - l5) / (m10 + l5))


def ar_predictive_gain(hourly, p=3):
    """CV R^2 of AR(p) predicting next-hour activity vs mean baseline (block CV)."""
    x = hourly.values.astype(float)
    x = np.log1p(x)  # stabilise heavy-tailed counts
    n = len(x)
    if n < 120:
        return np.nan
    # build design
    X = np.column_stack([x[p - 1 - k: n - 1 - k] for k in range(p)])
    y = x[p:n]
    m = len(y)
    # 5-fold contiguous block CV (acausal leakage avoided: train blocks separate)
    folds = np.array_split(np.arange(m), 5)
    r2s = []
    for i in range(5):
        te = folds[i]
        tr = np.concatenate([folds[j] for j in range(5) if j != i])
        if len(tr) < p + 5 or len(te) < 3:
            continue
        Xtr = np.column_stack([np.ones(len(tr)), X[tr]])
        Xte = np.column_stack([np.ones(len(te)), X[te]])
        beta, *_ = np.linalg.lstsq(Xtr, y[tr], rcond=None)
        pred = Xte @ beta
        base = y[tr].mean()
        ss_res = np.sum((y[te] - pred) ** 2)
        ss_tot = np.sum((y[te] - base) ** 2)
        if ss_tot > 0:
            r2s.append(1 - ss_res / ss_tot)
    return float(np.mean(r2s)) if r2s else np.nan


# ----------------------------- surrogates -----------------------------
def dayshuffle_IS_null(hourly, n=N_SURR):
    """Null IS from shuffling whole days (destroys interdaily stability)."""
    h = hourly.copy()
    dates = np.array([d for d in h.index.date])
    uniq = pd.unique(dates)
    if len(uniq) < 3:
        return np.nan
    # group values by day preserving within-day order
    byday = {d: h[h.index.date == d].values for d in uniq}
    lens = [len(byday[d]) for d in uniq]
    vals = []
    for _ in range(n):
        perm = RNG.permutation(uniq)
        cat = np.concatenate([byday[d] for d in perm])
        # rebuild hourly index of same length starting at original start
        idx = pd.date_range(h.index[0], periods=len(cat), freq="1h")
        s = pd.Series(cat, index=idx)
        vals.append(interdaily_stability(s))
    return float(np.nanmean(vals))


def phase_random_C_null(hourly, n=120):
    """IAAFT-lite phase-randomised surrogate: preserves power spectrum, destroys
    phase structure; recompute coherence_C on the surrogate day-matrix."""
    x = hourly.values.astype(float)
    n_t = len(x)
    if n_t < 48:
        return np.nan
    Xf = np.fft.rfft(x - x.mean())
    amp = np.abs(Xf)
    out = []
    for _ in range(n):
        ph = RNG.uniform(0, 2 * np.pi, len(Xf))
        ph[0] = 0
        surr = np.fft.irfft(amp * np.exp(1j * ph), n=n_t) + x.mean()
        s = pd.Series(surr, index=hourly.index)
        out.append(coherence_C(day_matrix(s)))
    return float(np.nanmean(out))


# ----------------------------- build feature table -----------------------------
def build():
    scores = pd.read_csv(DATA / "scores.csv").set_index("number")
    rows = []
    for grp, folder, label in [("cond", "condition", 1), ("ctrl", "control", 0)]:
        for fp in sorted((DATA / folder).glob("*.csv")):
            sid = fp.stem
            hourly = load_subject(fp)
            dm = day_matrix(hourly)
            C = coherence_C(dm)
            P = ar_predictive_gain(hourly)
            S = interdaily_stability(hourly)
            IV = intradaily_variability(hourly)
            RA = relative_amplitude(hourly)
            IS_null = dayshuffle_IS_null(hourly)
            C_null = phase_random_C_null(hourly)
            madrs = np.nan
            afftype = np.nan
            if sid in scores.index:
                madrs = scores.loc[sid, "madrs1"]
                afftype = scores.loc[sid, "afftype"]
            rows.append(dict(sid=sid, group=label, C=C, P=P, S=S, IV=IV, RA=RA,
                             dC=C - C_null if (C == C and C_null == C_null) else np.nan,
                             dS=S - IS_null if (S == S and IS_null == IS_null) else np.nan,
                             C_null=C_null, IS_null=IS_null,
                             madrs=pd.to_numeric(madrs, errors="coerce"),
                             afftype=pd.to_numeric(afftype, errors="coerce")))
            print(f"  {sid:14s} C={C:.3f} P={P if P==P else float('nan'):.3f} "
                  f"S={S:.3f} dS={rows[-1]['dS'] if rows[-1]['dS']==rows[-1]['dS'] else float('nan'):+.3f}")
    df = pd.DataFrame(rows)
    df.to_csv(RES / "features.csv", index=False)
    return df


# ----------------------------- gates -----------------------------
def norm01(s):
    s = s.astype(float)
    lo, hi = np.nanmin(s), np.nanmax(s)
    return (s - lo) / (hi - lo) if hi > lo else s * 0


def gate1_group_signal(df):
    out = {}
    dep = df[df.group == 1]
    con = df[df.group == 0]
    feats = ["C", "P", "S", "IV", "RA"]
    pvals = {}
    for f in feats:
        a = dep[f].dropna().values
        b = con[f].dropna().values
        u, p = stats.mannwhitneyu(a, b, alternative="two-sided")
        # rank-biserial effect size
        rbc = 1 - 2 * u / (len(a) * len(b))
        pvals[f] = dict(dep_med=float(np.median(a)), con_med=float(np.median(b)),
                        U=float(u), p=float(p), rank_biserial=float(rbc),
                        n_dep=len(a), n_con=len(b))
    # BH-FDR
    ps = np.array([pvals[f]["p"] for f in feats])
    order = np.argsort(ps)
    m = len(ps)
    passed = {}
    thr = 0.05
    bh = ps[order] * m / (np.arange(1, m + 1))
    for rank, idx in enumerate(order):
        passed[feats[idx]] = bool(bh[rank] <= thr)
    for f in feats:
        pvals[f]["fdr_pass"] = passed[f]
    out["per_feature"] = pvals
    out["any_pass_fdr"] = bool(any(passed.values()))
    return out


def gate2_surrogate(df):
    out = {}
    # (a) real IS exceeds day-shuffled null (rhythm structure above chance)
    dS = df["dS"].dropna().values
    w = stats.wilcoxon(dS, alternative="greater")
    out["IS_vs_dayshuffle"] = dict(median_dS=float(np.median(dS)),
                                   frac_positive=float(np.mean(dS > 0)),
                                   wilcoxon_p=float(w.pvalue), n=len(dS))
    # (b) real coherence C vs phase-randomised null (beyond-linear structure)
    dC = df["dC"].dropna().values
    w2 = stats.wilcoxon(dC, alternative="greater")
    out["C_vs_phaserandom"] = dict(median_dC=float(np.median(dC)),
                                   frac_positive=float(np.mean(dC > 0)),
                                   wilcoxon_p=float(w2.pvalue), n=len(dC))
    # (c) does the surrogate-CORRECTED signal still separate groups?
    for col in ["dS", "dC"]:
        dep = df[df.group == 1][col].dropna().values
        con = df[df.group == 0][col].dropna().values
        u, p = stats.mannwhitneyu(dep, con, alternative="two-sided")
        out[f"{col}_group_sep_p"] = float(p)
    # Gate passes iff BOTH surrogate reality checks confirm above-chance structure
    # (IS-vs-dayshuffle AND coherence-vs-phaserandom) AND the surrogate-CORRECTED
    # signal (dS or dC) still carries a group difference in >=1 channel. The
    # surrogate-corrected group separation is the decisive sub-test.
    real_structure = bool(out["IS_vs_dayshuffle"]["wilcoxon_p"] < 0.05 and
                          out["C_vs_phaserandom"]["wilcoxon_p"] < 0.05)
    corrected_separates = bool(min(out["dS_group_sep_p"], out["dC_group_sep_p"]) < 0.05)
    out["real_structure_above_chance"] = real_structure
    out["surrogate_corrected_separates_groups"] = corrected_separates
    out["pass"] = bool(real_structure and corrected_separates)
    return out


def gate3_index_vs_rawC(df):
    """LOO-CV AUC: does L_hybrid beat raw C at classifying depressed vs control?"""
    d = df.dropna(subset=["C", "P", "S"]).copy()
    y = d["group"].values
    raw = np.column_stack([d["C"].values, d["P"].values, d["S"].values]).astype(float)
    a, w = 0.5, np.array([1 / 3, 1 / 3, 1 / 3])  # hybrid additive+geometric (B157)

    def fold_transform(train_rows, rows):
        """min/max fit on TRAIN only -> normalise -> return (Cn, L) for `rows`."""
        lo = train_rows.min(axis=0)
        hi = train_rows.max(axis=0)
        rng = np.where(hi > lo, hi - lo, 1.0)
        norm = ((rows - lo) / rng).clip(1e-6, 1)
        add = norm @ w
        geo = np.exp(np.log(norm) @ w)
        L = a * add + (1 - a) * geo
        return norm, L

    def loo_auc(kind):
        """kind in {'C','L','full'} — all preprocessing fit on train folds only."""
        preds = np.zeros(len(y))
        for tr, te in LeaveOneOut().split(raw):
            ntr, Ltr = fold_transform(raw[tr], raw[tr])
            nte, Lte = fold_transform(raw[tr], raw[te])
            if kind == "C":
                Xtr, Xte = ntr[:, [0]], nte[:, [0]]
            elif kind == "L":
                Xtr, Xte = Ltr.reshape(-1, 1), Lte.reshape(-1, 1)
            else:
                Xtr, Xte = ntr, nte
            sc = StandardScaler().fit(Xtr)
            clf = LogisticRegression(max_iter=1000).fit(sc.transform(Xtr), y[tr])
            preds[te] = clf.predict_proba(sc.transform(Xte))[:, 1]
        return float(roc_auc_score(y, preds))

    auc_C = loo_auc("C")
    auc_L = loo_auc("L")
    auc_full = loo_auc("full")
    return dict(auc_rawC=auc_C, auc_Lhybrid=auc_L, auc_CPS_full=auc_full,
                L_beats_C=bool(auc_L > auc_C + 0.02), n=len(y),
                note="all normalisation + index construction fit on train folds only")


def constants_test(df):
    """Only meaningful if gates pass. Threshold in C separating groups (AIC change
    point) + interior-optimum of MADRS vs coupling. Candidate constants graded."""
    d = df.dropna(subset=["C"]).copy()
    Cn = norm01(d["C"]).values
    y = d["group"].values
    cands = {"sqrt2m1": np.sqrt(2) - 1, "c437": 1 / (np.sqrt(2) * (1 + np.sqrt(5)) / 2),
             "cos2_pi8": np.cos(np.pi / 8) ** 2, "radiant_cap": np.sqrt(1 - np.exp(-2))}
    # logistic with linear C vs step at each candidate; compare AIC
    def aic_logit(X):
        X = np.column_stack([np.ones(len(y)), X])
        clf = LogisticRegression(penalty=None, max_iter=2000).fit(X[:, 1:], y)
        p = clf.predict_proba(X[:, 1:])[:, 1].clip(1e-9, 1 - 1e-9)
        ll = np.sum(y * np.log(p) + (1 - y) * np.log(1 - p))
        k = X.shape[1]
        return 2 * k - 2 * ll
    aic_lin = aic_logit(Cn.reshape(-1, 1))
    steps = {}
    for name, c in cands.items():
        steps[name] = dict(value=float(c),
                           aic_step=float(aic_logit((Cn > c).astype(float).reshape(-1, 1))),
                           delta_vs_linear=float(aic_logit((Cn > c).astype(float).reshape(-1, 1)) - aic_lin))
    # interior optimum: MADRS vs C among depressed
    dep = df.dropna(subset=["C", "madrs"])
    dep = dep[dep.group == 1]
    quad = {}
    if len(dep) >= 8:
        cc = norm01(dep["C"]).values
        mm = dep["madrs"].values.astype(float)
        A = np.column_stack([np.ones_like(cc), cc, cc ** 2])
        beta, *_ = np.linalg.lstsq(A, mm, rcond=None)
        argmax = -beta[1] / (2 * beta[2]) if beta[2] != 0 else np.nan
        pred = A @ beta
        ss_res = np.sum((mm - pred) ** 2)
        ss_tot = np.sum((mm - mm.mean()) ** 2)
        quad = dict(beta=beta.tolist(), argmax=float(argmax),
                    concave=bool(beta[2] < 0), r2=float(1 - ss_res / ss_tot), n=len(dep))
    return dict(aic_linear=float(aic_lin), step_candidates=steps, madrs_quadratic=quad)


def main():
    print("Building feature table (this parses 55 subjects + surrogates)...")
    df = build()
    g1 = gate1_group_signal(df)
    g2 = gate2_surrogate(df)
    g3 = gate3_index_vs_rawC(df)
    gates_pass = bool(g1["any_pass_fdr"] and g2["pass"])
    result = dict(dataset="Depresjon (Garcia-Ceja 2018)", n_dep=int((df.group == 1).sum()),
                  n_con=int((df.group == 0).sum()),
                  gate1_group_signal=g1, gate2_surrogate=g2, gate3_index=g3,
                  gates_1_and_2_pass=gates_pass)
    # constants tested regardless but flagged by gate status (honesty: report but gate)
    result["constants_test"] = constants_test(df)
    result["constants_admissible"] = gates_pass and g3["L_beats_C"]
    with open(RES / "results.json", "w") as f:
        json.dump(result, f, indent=2)
    print(json.dumps({k: result[k] for k in
                      ["gate1_group_signal", "gate2_surrogate", "gate3_index",
                       "gates_1_and_2_pass", "constants_admissible"]}, indent=2))


if __name__ == "__main__":
    main()
