#!/usr/bin/env python3
"""
OET (Organizational Emergence Theorem, CANDIDATE) — first executed test on real data.

Claim under test (B177):
    above a coupling threshold tau,  Error(O) < sum_i Error(C_i)
i.e. a WHOLE-organization model predicts the near future better than the SUM of
independent per-cluster ("part") models -- and the whole-beats-parts *gain* is
gated/indexed by the LCC coupling crossing tau.

Established core (credit, NOT claimed as novel here):
    macro-beats-micro / synergy / whole-predicts-better is standard:
      Hoel, Albantakis & Tononi, PNAS 2013 (causal emergence);
      Williams & Beer 2010 (partial information decomposition / synergy);
      transfer entropy / joint-Granger > 0 (Schreiber 2000, Granger 1969).
    The ONLY new delta OET asserts is the LCC-threshold-INDEXING of that gain.

Test bed: OpenNeuro ds007471 dual-EEG hyperscanning (32 interacting pairs).
    Two brains = two causal clusters C_R, C_L (per-trial ROI-mean band signals,
    125 Hz, cached in ../lcc_uop_openneuro/features/sub-*_sig.npz).

Operationalization (per trial, per band):
    PART model  C_i : AR(p) -- predict brain i's next sample from i's OWN past only.
    WHOLE model O   : VAR(p) -- predict each brain's next sample from BOTH brains' past.
    All fits are OUT-OF-SAMPLE (fit on first 60% of the trial, score one-step-ahead
    prediction MSE on the last 40%), z-scored on the train split so MSE is comparable.
    Error(O)     = MSE_R(joint)  + MSE_L(joint)
    sum Error(C) = MSE_R(own)    + MSE_L(own)
    Delta = sum Error(C) - Error(O)   ( >0  <=>  OET inequality holds )
    Coupling C   = inter-brain PLV (the LCC measure), per trial.

HONESTY / #69 confound control (decisive):
    Both brains hear the SAME tone sequence, so a joint model can beat independent
    models purely from COMMON AUDITORY INPUT, with no organizational coupling at all.
    So the raw inequality Delta>0 is necessary-not-sufficient. We therefore also
    compute Delta on CROSS-PAIR SURROGATES (brain-R of pair A + brain-L of pair B,
    matched on tone+condition, never partners). The interaction-specific effect is
    Delta_real - Delta_surrogate. Only that survives the confound.

Usage:  python oet_test.py
"""
import os, glob, json, warnings
import numpy as np
from scipy.signal import hilbert

warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
FEAT = os.path.join(HERE, "..", "lcc_uop_openneuro", "features")
RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)

RNG = np.random.default_rng(20260702)
BANDS = ["theta", "beta"]        # motor/attention bands most relevant to joint action
ORDER = 5                        # VAR order ~40 ms at 125 Hz (matches feature extractor)
TRAIN_FRAC = 0.6
NS = 10                          # surrogate draws per trial
# LCC candidate constants to test as the indexing threshold tau (on PLV coupling C)
TAU_CANDIDATES = [0.414, 0.437, 0.6, 0.707, 0.854, 0.930]


def zscore_train(x, n_tr):
    mu = x[:n_tr].mean()
    sd = x[:n_tr].std()
    if sd <= 0:
        sd = 1.0
    return (x - mu) / sd


def _design(target, others, order):
    """Rows aligned so row t predicts target[order+t] from lag-1..order of target and each 'others'."""
    n = target.size
    cols = [target[order - k - 1:n - k - 1] for k in range(order)]
    for src in others:
        cols += [src[order - k - 1:n - k - 1] for k in range(order)]
    cols.append(np.ones(n - order))
    X = np.column_stack(cols)
    y = target[order:]
    return X, y


def _oos_mse(target, others, order, n_tr):
    """Fit lstsq on train rows, return one-step-ahead MSE on test rows."""
    X, y = _design(target, others, order)
    # a design row index r corresponds to sample (order+r); split by sample position
    split_row = max(order + 1, n_tr) - order
    if split_row < order + 2 or (X.shape[0] - split_row) < 5:
        return None
    Xtr, ytr = X[:split_row], y[:split_row]
    Xte, yte = X[split_row:], y[split_row:]
    beta, *_ = np.linalg.lstsq(Xtr, ytr, rcond=None)
    resid = yte - Xte @ beta
    return float(np.mean(resid ** 2))


def delta_for_pair(xr, xl, order=ORDER):
    """Return (Delta, err_whole, err_parts) for two 1-D signals; None if too short."""
    n = min(xr.size, xl.size)
    if n < 60:
        return None
    xr = xr[:n]; xl = xl[:n]
    n_tr = int(TRAIN_FRAC * n)
    xr = zscore_train(xr, n_tr)
    xl = zscore_train(xl, n_tr)
    r_own = _oos_mse(xr, [], order, n_tr)
    l_own = _oos_mse(xl, [], order, n_tr)
    r_both = _oos_mse(xr, [xl], order, n_tr)
    l_both = _oos_mse(xl, [xr], order, n_tr)
    if None in (r_own, l_own, r_both, l_both):
        return None
    err_parts = r_own + l_own
    err_whole = r_both + l_both
    return (err_parts - err_whole, err_whole, err_parts)


def plv(pa, pb):
    n = min(pa.size, pb.size)
    return float(np.abs(np.mean(np.exp(1j * (pa[:n] - pb[:n])))))


def load_trials():
    recs = []
    for f in sorted(glob.glob(os.path.join(FEAT, "sub-*_sig.npz"))):
        z = np.load(f, allow_pickle=True)
        meta = json.loads(str(z["meta"]))
        pair, tone, cond = meta["pair"], meta["tone"], meta["cond"]
        for t in range(len(tone)):
            item = {"pair": int(pair), "tone": int(tone[t]), "cond": int(cond[t])}
            for b in BANDS:
                item[f"{b}_R"] = np.asarray(z[f"{b}_R"][t], float)
                item[f"{b}_L"] = np.asarray(z[f"{b}_L"][t], float)
            recs.append(item)
    return recs


def boot_ci(x, nb=2000):
    x = np.asarray(x, float)
    if x.size == 0:
        return (None, None, None)
    bs = [x[RNG.integers(0, x.size, x.size)].mean() for _ in range(nb)]
    return float(x.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def perm_p_greater(a, b, nb=5000):
    """Two-sample permutation p that mean(a) > mean(b)."""
    a = np.asarray(a, float); b = np.asarray(b, float)
    if a.size == 0 or b.size == 0:
        return None
    obs = a.mean() - b.mean()
    pool = np.concatenate([a, b]); na = a.size
    cnt = 0
    for _ in range(nb):
        RNG.shuffle(pool)
        if (pool[:na].mean() - pool[na:].mean()) >= obs:
            cnt += 1
    return (cnt + 1) / (nb + 1)


def main():
    recs = load_trials()
    if not recs:
        print("no signal caches found in", FEAT); return
    by_key = {}
    for i, r in enumerate(recs):
        by_key.setdefault((r["tone"], r["cond"]), []).append(i)

    out = {
        "dataset": "OpenNeuro ds007471 dual-EEG (32 interacting pairs)",
        "n_trials": len(recs),
        "n_pairs": len(set(r["pair"] for r in recs)),
        "order": ORDER, "train_frac": TRAIN_FRAC,
        "model": "PART=AR(own past); WHOLE=VAR(both brains past); OOS one-step MSE",
        "bands": {},
    }

    for b in BANDS:
        real_delta, coupl = [], []
        surr_delta = []
        for i, r in enumerate(recs):
            res = delta_for_pair(r[f"{b}_R"], r[f"{b}_L"])
            if res is None:
                continue
            d, _, _ = res
            real_delta.append(d)
            pa = np.angle(hilbert(r[f"{b}_R"]))
            pb = np.angle(hilbert(r[f"{b}_L"]))
            coupl.append(plv(pa, pb))
            # cross-pair surrogates: same tone+cond, different pair, R_i vs L_j
            cand = [j for j in by_key[(r["tone"], r["cond"])] if recs[j]["pair"] != r["pair"]]
            if cand:
                js = RNG.choice(cand, size=min(NS, len(cand)), replace=len(cand) < NS)
                for j in js:
                    sres = delta_for_pair(r[f"{b}_R"], recs[j][f"{b}_L"])
                    if sres is not None:
                        surr_delta.append(sres[0])
        real_delta = np.array(real_delta)
        surr_delta = np.array(surr_delta)
        coupl = np.array(coupl)

        rd_mean, rd_lo, rd_hi = boot_ci(real_delta)
        sd_mean, sd_lo, sd_hi = boot_ci(surr_delta)
        # raw OET inequality: Delta_real > 0 ?
        p_raw = float(np.mean([real_delta[RNG.integers(0, real_delta.size, real_delta.size)].mean() <= 0
                               for _ in range(2000)])) if real_delta.size else None
        # interaction-specific: Delta_real > Delta_surrogate ?
        p_interaction = perm_p_greater(real_delta, surr_delta)
        # frac of trials satisfying the inequality
        frac_pos = float(np.mean(real_delta > 0)) if real_delta.size else None

        # LCC-threshold-INDEXING (the actual novelty): does Delta rise above tau?
        # (a) linear corr(Delta, C); (b) best split t-contrast at each candidate tau
        idx = {}
        if real_delta.size == coupl.size and real_delta.size > 5:
            cc = np.corrcoef(coupl, real_delta)[0, 1]
            idx["corr_delta_vs_coupling"] = round(float(cc), 4)
            tau_tab = {}
            for tau in TAU_CANDIDATES:
                hi = real_delta[coupl >= tau]
                lo = real_delta[coupl < tau]
                if hi.size >= 5 and lo.size >= 5:
                    tau_tab[str(tau)] = {
                        "n_above": int(hi.size), "n_below": int(lo.size),
                        "mean_above": round(float(hi.mean()), 5),
                        "mean_below": round(float(lo.mean()), 5),
                        "p_above_gt_below": round(perm_p_greater(hi, lo, 2000), 4),
                    }
                else:
                    tau_tab[str(tau)] = {"n_above": int(hi.size), "n_below": int(lo.size),
                                         "note": "insufficient trials on one side"}
            idx["threshold_indexing"] = tau_tab

        out["bands"][b] = {
            "n_real_trials": int(real_delta.size),
            "n_surrogate_deltas": int(surr_delta.size),
            "coupling_C_mean": round(float(coupl.mean()), 4) if coupl.size else None,
            "delta_real_mean": round(rd_mean, 6) if rd_mean is not None else None,
            "delta_real_ci95": [round(rd_lo, 6), round(rd_hi, 6)] if rd_mean is not None else None,
            "frac_trials_inequality_holds": round(frac_pos, 4) if frac_pos is not None else None,
            "p_delta_real_le_0": round(p_raw, 4) if p_raw is not None else None,
            "delta_surrogate_mean": round(sd_mean, 6) if sd_mean is not None else None,
            "delta_surrogate_ci95": [round(sd_lo, 6), round(sd_hi, 6)] if sd_mean is not None else None,
            "interaction_specific_gain": round(rd_mean - sd_mean, 6) if (rd_mean is not None and sd_mean is not None) else None,
            "p_real_gt_surrogate": round(p_interaction, 4) if p_interaction is not None else None,
            "lcc_indexing": idx,
        }

    with open(os.path.join(RES, "oet_results.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
