"""
Independent UGI-1 non-redundancy test for the GILE coordinates.

QUESTION
--------
Does each GILE coordinate carry RISKY, NON-REDUNDANT predictive information about
real-world success Y that the other three coordinates do NOT already carry?
Formally, the target is a positive conditional dependence, e.g. I(Y ; G | I,L,E) > 0
for each coordinate in turn.

This is the empirical half of "is GILE substantive rather than tautological" (the
other half, a vNM-style representation theorem = the corpus's open frontier R1, is NOT
attempted here). Under UGI-1 a POSITIVE result here is *suggestive, single-domain,
proxy-dependent, necessary-not-sufficient* evidence -- never a proof of universal
non-redundancy.

HONEST OPERATIONALIZATION (one defensible choice among several; tree-based model family
so the Elegance/complexity axis is comparable across configs):
  - Intuition  I : calibrated accuracy via a STRICTLY PROPER SCORING RULE
                   (negative log-loss on a validation split).
  - Elegance   E : compression / MDL proxy = -log(total decision-tree node count)
                   (simpler model = more elegant). Structural, not performance-based.
  - Goodness   G : coherence/stability (a Four-C proxy) = -mean std of predicted
                   probabilities across bootstrap-retrained copies of the SAME config.
  - Love       L : cooperative welfare gradient = marginal contribution of the model to
                   a reference ENSEMBLE's score (leave-one-in log-loss gain). A model can
                   be individually good yet redundant (low L) or mediocre yet
                   complementary (high L) -- genuinely relational, distinct from solo I.
  - Outcome    Y : REAL held-out generalization = negative log-loss on a TEST split that
                   is DISJOINT from everything used to compute the four coordinates
                   (no leakage).

PIPELINE (identical for the synthetic controls and the real data):
  For each coordinate c, the conditional contribution is measured three ways:
    (1) Delta-R^2 with GROUPED (leave-one-dataset-out) cross-validation:
        CV_R2(Y ~ all four) - CV_R2(Y ~ the other three), for a LINEAR and a
        nonlinear (random-forest) regressor.
    (2) A PERMUTATION null: shuffle column c (within group) and recompute the linear
        Delta-R^2 many times -> p = P(null Delta-R^2 >= observed). Confound control:
        the naive point estimate is meaningless without this null.
    (3) Partial correlation of c with Y controlling for the other three.

ESTIMATOR-VALIDATION CONTROLS (run FIRST, because a pipeline that always says
"non-redundant" proves nothing):
  - NEGATIVE control: one coordinate is a near-deterministic function of the others and
    carries no independent information about Y. The pipeline MUST read it ~0 / non-sig.
  - POSITIVE control: all four coordinates independently drive Y. All MUST read sig.

No external data, no network, no secrets. Real sklearn datasets only.
"""

from __future__ import annotations

import json
import os
import time
import warnings
from dataclasses import dataclass, field

import numpy as np
from numpy.random import default_rng

from sklearn.datasets import (
    load_breast_cancer,
    load_wine,
    load_digits,
    make_classification,
)
from sklearn.tree import DecisionTreeClassifier
from sklearn.ensemble import (
    RandomForestClassifier,
    ExtraTreesClassifier,
    GradientBoostingClassifier,
    RandomForestRegressor,
)
from sklearn.linear_model import LinearRegression
from sklearn.metrics import log_loss
from sklearn.model_selection import train_test_split

warnings.filterwarnings("ignore")

RNG_SEED = 20260628
COORDS = ["G", "I", "L", "E"]
HERE = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------------------
# Core statistics: grouped Delta-R^2, permutation null, partial correlation
# --------------------------------------------------------------------------------------
def grouped_cv_r2(X, y, groups, regressor="linear"):
    """Leave-one-group-out CV R^2 (pooled out-of-fold predictions)."""
    uniq = np.unique(groups)
    preds = np.full_like(y, np.nan, dtype=float)
    for g in uniq:
        tr = groups != g
        te = groups == g
        if tr.sum() < 5 or te.sum() < 2:
            continue
        if regressor == "linear":
            mdl = LinearRegression()
        else:
            mdl = RandomForestRegressor(
                n_estimators=80, max_depth=4, random_state=RNG_SEED, n_jobs=-1
            )
        mdl.fit(X[tr], y[tr])
        preds[te] = mdl.predict(X[te])
    ok = ~np.isnan(preds)
    if ok.sum() < 3:
        return np.nan
    ss_res = np.sum((y[ok] - preds[ok]) ** 2)
    ss_tot = np.sum((y[ok] - np.mean(y[ok])) ** 2)
    if ss_tot <= 0:
        return np.nan
    return 1.0 - ss_res / ss_tot


def delta_r2(df_X, y, groups, drop_idx, regressor="linear"):
    full = grouped_cv_r2(df_X, y, groups, regressor)
    keep = [i for i in range(df_X.shape[1]) if i != drop_idx]
    reduced = grouped_cv_r2(df_X[:, keep], y, groups, regressor)
    if np.isnan(full) or np.isnan(reduced):
        return np.nan
    return full - reduced


def permutation_pvalue(df_X, y, groups, c_idx, observed, n_perm=1000, seed=RNG_SEED):
    """Within-group shuffle of column c_idx; p = P(null delta_r2 >= observed)."""
    rng = default_rng(seed)
    null = np.empty(n_perm)
    Xp = df_X.copy()
    uniq = np.unique(groups)
    for k in range(n_perm):
        for g in uniq:
            mask = groups == g
            idx = np.where(mask)[0]
            Xp[idx, c_idx] = df_X[rng.permutation(idx), c_idx]
        null[k] = delta_r2(Xp, y, groups, c_idx, regressor="linear")
    null = null[~np.isnan(null)]
    if null.size == 0:
        return np.nan, np.nan
    p = (1.0 + np.sum(null >= observed)) / (1.0 + null.size)
    return float(p), float(np.nanmean(null))


def partial_corr(X, y, c_idx):
    """Partial correlation of column c_idx with y, controlling for all other columns."""
    others = [i for i in range(X.shape[1]) if i != c_idx]
    Z = np.column_stack([np.ones(len(y)), X[:, others]])
    # residualize c and y on the other coordinates
    beta_c, *_ = np.linalg.lstsq(Z, X[:, c_idx], rcond=None)
    beta_y, *_ = np.linalg.lstsq(Z, y, rcond=None)
    rc = X[:, c_idx] - Z @ beta_c
    ry = y - Z @ beta_y
    if np.std(rc) < 1e-12 or np.std(ry) < 1e-12:
        return 0.0
    return float(np.corrcoef(rc, ry)[0, 1])


def run_pipeline(X, y, groups, label, n_perm=1000):
    """Run the full non-redundancy battery and return a per-coordinate report."""
    out = {}
    for i, name in enumerate(COORDS):
        d_lin = delta_r2(X, y, groups, i, "linear")
        d_rf = delta_r2(X, y, groups, i, "rf")
        p, nullmean = permutation_pvalue(X, y, groups, i, d_lin, n_perm=n_perm)
        pc = partial_corr(X, y, i)
        out[name] = {
            "delta_r2_linear": _round(d_lin),
            "delta_r2_rf": _round(d_rf),
            "perm_pvalue": _round(p),
            "perm_null_mean": _round(nullmean),
            "partial_corr": _round(pc),
            "nonredundant_sig": bool((not np.isnan(p)) and p < 0.05 and d_lin > 0),
        }
    return {"label": label, "n_rows": int(len(y)), "coords": out}


def _round(x, n=4):
    if x is None or (isinstance(x, float) and np.isnan(x)):
        return None
    return round(float(x), n)


def zscore_within(values, groups):
    out = np.array(values, dtype=float)
    for g in np.unique(groups):
        m = groups == g
        col = out[m]
        sd = col.std()
        out[m] = (col - col.mean()) / (sd if sd > 1e-12 else 1.0)
    return out


# --------------------------------------------------------------------------------------
# PART 1 -- synthetic estimator-validation controls
# --------------------------------------------------------------------------------------
def synthetic_controls(n_per_group=400, n_groups=4, n_perm=1000):
    rng = default_rng(RNG_SEED)
    results = {}

    # NEGATIVE control: E is a near-deterministic function of (G,I,L); carries no
    # independent info about Y. Pipeline MUST flag E as redundant (~0, non-sig).
    Xs, ys, gs = [], [], []
    for g in range(n_groups):
        G = rng.normal(size=n_per_group)
        I = rng.normal(size=n_per_group)
        L = rng.normal(size=n_per_group)
        E = 0.7 * G + 0.5 * I - 0.4 * L + 0.02 * rng.normal(size=n_per_group)
        Y = 1.0 * G + 0.8 * I + 0.6 * L + 0.5 * rng.normal(size=n_per_group)
        Xs.append(np.column_stack([G, I, L, E]))
        ys.append(Y)
        gs.append(np.full(n_per_group, g))
    X = np.vstack(Xs)
    y = np.concatenate(ys)
    groups = np.concatenate(gs)
    for i in range(4):
        X[:, i] = zscore_within(X[:, i], groups)
    y = zscore_within(y, groups)
    results["negative_control_E_redundant"] = run_pipeline(
        X, y, groups, "NEG control: E := f(G,I,L), no independent Y info", n_perm
    )

    # POSITIVE control: all four independently drive Y -> all MUST read significant.
    Xs, ys, gs = [], [], []
    for g in range(n_groups):
        G = rng.normal(size=n_per_group)
        I = rng.normal(size=n_per_group)
        L = rng.normal(size=n_per_group)
        E = rng.normal(size=n_per_group)
        Y = 0.9 * G + 0.9 * I + 0.9 * L + 0.9 * E + 0.5 * rng.normal(size=n_per_group)
        Xs.append(np.column_stack([G, I, L, E]))
        ys.append(Y)
        gs.append(np.full(n_per_group, g))
    X = np.vstack(Xs)
    y = np.concatenate(ys)
    groups = np.concatenate(gs)
    for i in range(4):
        X[:, i] = zscore_within(X[:, i], groups)
    y = zscore_within(y, groups)
    results["positive_control_all_informative"] = run_pipeline(
        X, y, groups, "POS control: all four independently drive Y", n_perm
    )
    return results


# --------------------------------------------------------------------------------------
# PART 2 -- real-data GILE coordinates from model selection
# --------------------------------------------------------------------------------------
def model_family(rng):
    """A tree-based family so the Elegance (node-count) axis is comparable.

    Kept deliberately compact for runtime; still spans a wide complexity/performance
    range (shallow stumps -> deep unpruned trees -> forests -> boosting).
    """
    cfgs = []
    for d in [2, 3, 5, 8, None]:
        cfgs.append(("dt", DecisionTreeClassifier(max_depth=d, random_state=0)))
    for d in [3, 6, None]:
        cfgs.append(("rf", RandomForestClassifier(n_estimators=40, max_depth=d,
                                                  random_state=0, n_jobs=-1)))
        cfgs.append(("et", ExtraTreesClassifier(n_estimators=40, max_depth=d,
                                                random_state=0, n_jobs=-1)))
    for d in [2, 3]:
        cfgs.append(("gb", GradientBoostingClassifier(
            n_estimators=50, max_depth=d, learning_rate=0.1, random_state=0)))
    return cfgs


def node_count(model):
    if hasattr(model, "tree_"):
        return int(model.tree_.node_count)
    if hasattr(model, "estimators_"):
        total = 0
        for e in np.ravel(np.asarray(model.estimators_, dtype=object)):
            if hasattr(e, "tree_"):
                total += int(e.tree_.node_count)
        return max(total, 1)
    return 1


def fit_predict_proba(model, Xtr, ytr, Xeval, classes):
    from sklearn.base import clone
    m = clone(model)
    m.fit(Xtr, ytr)
    proba = m.predict_proba(Xeval)
    # align columns to global class order
    aligned = np.zeros((proba.shape[0], len(classes)))
    for j, c in enumerate(m.classes_):
        aligned[:, list(classes).index(c)] = proba[:, j]
    aligned = np.clip(aligned, 1e-12, 1.0)
    aligned /= aligned.sum(axis=1, keepdims=True)
    return aligned, m


def coordinates_for_dataset(name, X, yc, rng, n_boot=4):
    classes = np.unique(yc)
    # train (fit) / val (coordinates) / test (outcome Y) -- all disjoint
    Xtr, Xtmp, ytr, ytmp = train_test_split(
        X, yc, test_size=0.5, random_state=RNG_SEED, stratify=yc
    )
    Xval, Xte, yval, yte = train_test_split(
        Xtmp, ytmp, test_size=0.5, random_state=RNG_SEED, stratify=ytmp
    )
    cfgs = model_family(rng)

    rows = []
    val_probas = []
    for tag, mdl in cfgs:
        # I: proper-scoring-rule accuracy on val
        pval, fitted = fit_predict_proba(mdl, Xtr, ytr, Xval, classes)
        I = -log_loss(yval, pval, labels=classes)
        # E: elegance = -log(node count)
        E = -np.log(node_count(fitted))
        # Y: real generalization on disjoint test split
        pte, _ = fit_predict_proba(mdl, Xtr, ytr, Xte, classes)
        Y = -log_loss(yte, pte, labels=classes)
        # G: stability across bootstrap-retrained copies (std of val proba)
        boot_probas = []
        for b in range(n_boot):
            idx = rng.integers(0, len(Xtr), size=len(Xtr))
            try:
                pb, _ = fit_predict_proba(mdl, Xtr[idx], ytr[idx], Xval, classes)
                boot_probas.append(pb)
            except Exception:
                continue
        if len(boot_probas) >= 3:
            stk = np.stack(boot_probas, axis=0)
            G = -float(np.mean(np.std(stk, axis=0)))
        else:
            G = np.nan
        rows.append({"tag": tag, "I": I, "E": E, "G": G, "Y": Y})
        val_probas.append(pval)

    # L: cooperative welfare gradient = leave-one-in ensemble log-loss gain
    P = np.stack(val_probas, axis=0)  # (n_models, n_samples, n_classes)
    n_models = P.shape[0]
    ens_all = P.mean(axis=0)
    ll_all = log_loss(yval, ens_all, labels=classes)
    for k in range(n_models):
        if n_models > 1:
            ens_wo = (P.sum(axis=0) - P[k]) / (n_models - 1)
            ll_wo = log_loss(yval, ens_wo, labels=classes)
            rows[k]["L"] = ll_wo - ll_all  # positive => including model k helps the group
        else:
            rows[k]["L"] = 0.0
    for r in rows:
        r["dataset"] = name
    return rows


def compute_real_rows():
    """Compute (and cache) the GILE coordinate rows -- the expensive step."""
    cache = os.path.join(HERE, "coords_cache.json")
    if os.path.exists(cache) and os.environ.get("GILE_FORCE") != "1":
        with open(cache) as f:
            print(f"[gile-nonredundancy] loaded cached coordinates from {cache}")
            return json.load(f)
    rng = default_rng(RNG_SEED)
    datasets = []
    bc = load_breast_cancer()
    datasets.append(("breast_cancer", bc.data, bc.target))
    wn = load_wine()
    datasets.append(("wine", wn.data, wn.target))
    dg = load_digits()
    # subsample digits for runtime (stratified) -- keeps a real 10-class problem
    dg_idx = default_rng(RNG_SEED).choice(len(dg.target), size=800, replace=False)
    datasets.append(("digits", dg.data[dg_idx], dg.target[dg_idx]))
    Xs, ys = make_classification(
        n_samples=1200, n_features=20, n_informative=8, n_redundant=4,
        n_classes=3, n_clusters_per_class=2, class_sep=1.1, random_state=RNG_SEED,
    )
    datasets.append(("synthetic_clf", Xs, ys))

    all_rows = []
    for name, X, yc in datasets:
        t = time.time()
        all_rows.extend(coordinates_for_dataset(name, X, yc, rng))
        print(f"[gile-nonredundancy] coords {name}: {round(time.time()-t,1)}s")
    with open(cache, "w") as f:
        json.dump(all_rows, f)
    print(f"[gile-nonredundancy] cached coordinates -> {cache}")
    return all_rows


def real_data_test(n_perm=1000):
    all_rows = compute_real_rows()

    # drop any row with a NaN coordinate
    clean = [r for r in all_rows if all(np.isfinite(r[c]) for c in COORDS + ["Y"])]
    groups = np.array([r["dataset"] for r in clean])
    Xmat = np.column_stack([
        zscore_within([r[c] for r in clean], groups) for c in COORDS
    ])
    yv = zscore_within([r["Y"] for r in clean], groups)

    # raw pooled correlations (descriptive only)
    raw_corr = {c: _round(float(np.corrcoef(Xmat[:, i], yv)[0, 1]))
                for i, c in enumerate(COORDS)}
    pair_corr = {}
    for i, a in enumerate(COORDS):
        for j, b in enumerate(COORDS):
            if i < j:
                pair_corr[f"{a}-{b}"] = _round(float(np.corrcoef(Xmat[:, i], Xmat[:, j])[0, 1]))

    report = run_pipeline(Xmat, yv, groups, "REAL: GILE coords vs held-out test perf", n_perm)
    report["n_models_per_dataset"] = {n: int(np.sum(groups == n)) for n in np.unique(groups)}
    report["marginal_corr_with_Y"] = raw_corr
    report["coordinate_pair_corr"] = pair_corr
    return report


# --------------------------------------------------------------------------------------
def main():
    t0 = time.time()
    n_perm = int(os.environ.get("GILE_NPERM", "1000"))
    print(f"[gile-nonredundancy] seed={RNG_SEED} n_perm={n_perm}")

    print("\n=== PART 1: estimator-validation controls (synthetic) ===")
    controls = synthetic_controls(n_perm=n_perm)
    for key, rep in controls.items():
        print(f"\n-- {rep['label']}")
        for c in COORDS:
            r = rep["coords"][c]
            print(f"   {c}: dR2_lin={r['delta_r2_linear']}  p={r['perm_pvalue']}  "
                  f"pcorr={r['partial_corr']}  sig={r['nonredundant_sig']}")

    print("\n=== PART 2: real-data GILE non-redundancy ===")
    real = real_data_test(n_perm=n_perm)
    print(f"   models per dataset: {real['n_models_per_dataset']}")
    print(f"   marginal corr with Y: {real['marginal_corr_with_Y']}")
    print(f"   coordinate pair corr: {real['coordinate_pair_corr']}")
    for c in COORDS:
        r = real["coords"][c]
        print(f"   {c}: dR2_lin={r['delta_r2_linear']}  dR2_rf={r['delta_r2_rf']}  "
              f"p={r['perm_pvalue']}  pcorr={r['partial_corr']}  "
              f"NONREDUNDANT={r['nonredundant_sig']}")

    out = {
        "seed": RNG_SEED,
        "n_perm": n_perm,
        "runtime_sec": round(time.time() - t0, 1),
        "controls": controls,
        "real_data": real,
        "honest_scope": (
            "Single domain (supervised model selection, tree-based family). Proxies are "
            "one defensible choice among several. Positive results are SUGGESTIVE and "
            "necessary-not-sufficient (UGI-1): they support non-redundancy in THIS domain "
            "with THESE proxies, not universal non-redundancy. The representation-theorem "
            "half of 'substantive' (corpus R1) is NOT addressed here."
        ),
    }
    path = os.path.join(HERE, "results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n[gile-nonredundancy] wrote {path}  ({out['runtime_sec']}s)")


if __name__ == "__main__":
    main()
