#!/usr/bin/env python3
"""
Cross-pair SURROGATE null for the common-auditory-input confound.

Both brains in a pair hear the same metronome + each other's tones, so inter-brain PHASE
coupling (PLV, the measure C) is partly driven by shared stimulus, not genuine interaction.
We recompute C for PSEUDO-PAIRS: brain-R of pair A vs brain-L of pair B, matched on the SAME
tone sequence + condition (so they heard the same stimulus structure) but were NEVER partners.
If real pairs do not exceed these surrogates, the "coupling" is common input, not interaction.

We test C (PLV) only: it is the measure most directly inflated by shared stimulus, and phases
are precomputed once per trial so the null is cheap. (Directional Granger P is not a common-input
measure in the same way and is omitted here.)

Uses the per-trial per-brain ROI-mean band signals cached in features/sub-*_sig.npz.
"""
import os, glob, json, warnings
import numpy as np
from scipy.signal import hilbert

warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "features")
RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)
RNG = np.random.default_rng(20260701)
BANDS = ["delta", "theta", "alpha", "beta"]
NS = 10  # surrogate draws per trial


def plv_from_phase(pa, pb):
    n = min(pa.size, pb.size)
    return float(np.abs(np.mean(np.exp(1j * (pa[:n] - pb[:n])))))


def load_phases():
    """Return list of trial dicts with precomputed analytic-signal phases per band/brain."""
    recs = []
    for f in sorted(glob.glob(os.path.join(OUT, "sub-*_sig.npz"))):
        z = np.load(f, allow_pickle=True)
        meta = json.loads(str(z["meta"]))
        pair, tone, cond = meta["pair"], meta["tone"], meta["cond"]
        for t in range(len(tone)):
            item = {"pair": pair, "tone": int(tone[t]), "cond": int(cond[t])}
            for b in BANDS:
                item[f"{b}_R"] = np.angle(hilbert(np.asarray(z[f"{b}_R"][t], float)))
                item[f"{b}_L"] = np.angle(hilbert(np.asarray(z[f"{b}_L"][t], float)))
            recs.append(item)
    return recs


def main():
    recs = load_phases()
    if not recs:
        print("no signal caches yet"); return
    by_key = {}
    for i, r in enumerate(recs):
        by_key.setdefault((r["tone"], r["cond"]), []).append(i)

    out = {"n_trials": len(recs), "n_pairs": len(set(r["pair"] for r in recs)),
           "measure": "C = inter-brain PLV (phase-coupling)", "n_surrogate_draws": NS, "bands": {}}
    for b in BANDS:
        real, surr = [], []
        for i, r in enumerate(recs):
            real.append(plv_from_phase(r[f"{b}_R"], r[f"{b}_L"]))
            cand = [j for j in by_key[(r["tone"], r["cond"])] if recs[j]["pair"] != r["pair"]]
            if not cand:
                continue
            js = RNG.choice(cand, size=min(NS, len(cand)), replace=len(cand) < NS)
            for j in js:
                surr.append(plv_from_phase(r[f"{b}_R"], recs[j][f"{b}_L"]))
        real = np.array(real); surr = np.array(surr)
        # one-sided permutation-style p: fraction of surrogate means >= real mean
        # via bootstrap over surrogate draws for a mean CI
        bs = [surr[RNG.integers(0, surr.size, surr.size)].mean() for _ in range(1000)] if surr.size else []
        gap = float(real.mean() - surr.mean()) if surr.size else None
        p_one = (float(np.mean(np.array(bs) >= real.mean())) if bs else None)
        out["bands"][b] = {
            "real_C_mean": round(float(real.mean()), 4),
            "surr_C_mean": round(float(surr.mean()), 4) if surr.size else None,
            "real_minus_surr": None if gap is None else round(gap, 4),
            "surr_mean_ci95": [round(float(np.percentile(bs, 2.5)), 4),
                               round(float(np.percentile(bs, 97.5)), 4)] if bs else None,
            "real_exceeds_surr": None if gap is None else bool(gap > 0),
            "p_one_sided_real_gt_surr": p_one,
        }
    with open(os.path.join(RES, "surrogate.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
