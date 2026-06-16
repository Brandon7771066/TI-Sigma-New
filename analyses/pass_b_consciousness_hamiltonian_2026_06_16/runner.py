"""Retrieval-operator benchmark runner.

Cross-channel hidden-state RETRIEVAL task:
  - latent H defined from a held-out channel group (group A);
  - operators retrieve H from a DISJOINT group (group B).
Coupling across groups is real (resonance necessary); H is not directly visible
(retrieval operator needed). Temporal-block split (no leakage). Metrics:
balanced accuracy, chance, bootstrap 95% CI, paired bootstrap delta vs passive.
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from features import window_features, passive_resonance_feature  # noqa: E402
from simulate import simulate  # noqa: E402
from operators import all_operators  # noqa: E402

RNG = np.random.default_rng(20260616)


def kmeans_centroids(X, k=3, iters=50, seed=0):
    """Fit k-means and return centroids (Lloyd's). Caller assigns labels."""
    rng = np.random.default_rng(seed)
    c = X[rng.choice(len(X), k, replace=False)].copy()
    lab = np.zeros(len(X), dtype=int)
    for _ in range(iters):
        d = np.linalg.norm(X[:, None, :] - c[None, :, :], axis=2)
        new = np.argmin(d, axis=1)
        if np.all(new == lab):
            break
        lab = new
        for j in range(k):
            if np.any(lab == j):
                c[j] = X[lab == j].mean(0)
    return c


def assign_nearest(X, c):
    d = np.linalg.norm(X[:, None, :] - c[None, :, :], axis=2)
    return np.argmin(d, axis=1)


def standardize_fit(X):
    mu = X.mean(0)
    sd = X.std(0) + 1e-9
    return mu, sd


def balanced_accuracy(y, yhat, K):
    recs = []
    for c in range(K):
        m = y == c
        if np.any(m):
            recs.append(np.mean(yhat[m] == c))
    return float(np.mean(recs)) if recs else 0.0


def bootstrap_ci(y, yhat, K, B=1000):
    n = len(y)
    accs = np.empty(B)
    for b in range(B):
        idx = RNG.integers(0, n, n)
        accs[b] = balanced_accuracy(y[idx], yhat[idx], K)
    return float(np.percentile(accs, 2.5)), float(np.percentile(accs, 97.5))


def paired_delta_ci(y, yhat_op, yhat_base, K, B=1000):
    n = len(y)
    d = np.empty(B)
    for b in range(B):
        idx = RNG.integers(0, n, n)
        d[b] = (balanced_accuracy(y[idx], yhat_op[idx], K)
                - balanced_accuracy(y[idx], yhat_base[idx], K))
    lo, hi = float(np.percentile(d, 2.5)), float(np.percentile(d, 97.5))
    return float(np.mean(d)), lo, hi, bool(lo > 0)


def build_features(src, split_sample):
    """Compute group-B observed features + resonance scalar (+ group-A features
    for real data). Filtering is block-split at split_sample (leakage-safe). NO
    target is built here; H is constructed split-aware in run_source."""
    sig, fs = src["sig"], src["fs"]
    starts, w = src["starts"], src["w"]
    Xb = window_features(sig, fs, src["groupB"], starts, w, split_sample=split_sample)
    r = passive_resonance_feature(sig, fs, src["groupB"], starts, w, split_sample=split_sample)
    Xa = None
    if src["H"] is None:                          # real data: needs group-A features
        Xa = window_features(sig, fs, src["groupA"], starts, w, split_sample=split_sample)
    return Xb, r, Xa


def run_source(src):
    K = src["n_states"]
    starts = src["starts"]
    n = len(starts)
    cut = int(0.6 * n)                            # temporal block split
    split_sample = int(starts[cut])              # first test-window start sample
    Xb, r, Xa = build_features(src, split_sample)
    tr = slice(0, cut)
    te = slice(cut, n)

    # Build the latent H WITHOUT leakage:
    if src["H"] is not None:                       # sim: ground truth
        H = np.asarray(src["H"])
        latent_kind = "ground-truth (simulated)"
    else:                                          # real: cluster on TRAIN ONLY
        amu, asd = standardize_fit(Xa[tr])
        Xa_s = (Xa - amu) / asd
        cent = kmeans_centroids(Xa_s[tr], k=K)     # centroids fit on train group-A
        H = assign_nearest(Xa_s, cent)             # all windows by nearest TRAIN centroid
        latent_kind = ("cross-group k-means fit on TRAIN-ONLY group A; "
                       "test labeled by nearest train centroid (label-free)")

    mu, sd = standardize_fit(Xb[tr])
    Xs = (Xb - mu) / sd
    Xtr, Xte = Xs[tr], Xs[te]
    rtr, rte = r[tr], r[te]
    Htr, Hte = H[tr], H[te]

    chance = 1.0 / K
    base_pred = None        # P0 resonance-magnitude baseline
    matched_pred = None     # P0b matched-feature nearest-centroid baseline
    rows = []
    for op in all_operators(K):
        op.fit(Xtr, Htr, rtr)
        pred = op.predict(Xte, rte)
        acc = balanced_accuracy(Hte, pred, K)
        lo, hi = bootstrap_ci(Hte, pred, K)
        row = {"operator": op.name, "bal_acc": acc, "ci95": [lo, hi],
               "chance": chance, "above_chance": bool(lo > chance)}
        if op.name == "P0_passive_resonance":
            base_pred = pred
        elif op.name == "P0b_nearest_centroid_matched":
            matched_pred = pred
        rows.append((row, pred))

    # paired improvement vs BOTH baselines (resonance-magnitude P0 + matched P0b)
    for row, pred in rows:
        if row["operator"].startswith("P0"):
            continue
        if base_pred is not None:
            md, dlo, dhi, sig = paired_delta_ci(Hte, pred, base_pred, K)
            row["delta_vs_passive"] = md
            row["delta_ci95"] = [dlo, dhi]
            row["beats_passive"] = sig
        if matched_pred is not None:
            mmd, mlo, mhi, msig = paired_delta_ci(Hte, pred, matched_pred, K)
            row["delta_vs_matched"] = mmd
            row["delta_matched_ci95"] = [mlo, mhi]
            row["beats_matched"] = msig

    results = [r for r, _ in rows]
    return {
        "label": src["label"],
        "source": src["source"],
        "latent_kind": latent_kind,
        "n_windows": int(n),
        "n_train": int(cut),
        "n_test": int(n - cut),
        "n_states": K,
        "fs": float(src["fs"]),
        "n_obs_channels": len(src["groupB"]),
        "class_balance_test": [int(np.sum(Hte == c)) for c in range(K)],
        "results": results,
    }


def main():
    sources = [simulate(seed=0), simulate(seed=7)]
    real = []
    try:
        from data_dandi import load_first_available
        real = load_first_available(max_sources=2)
    except Exception as e:
        print(f"[runner] DANDI load error: {type(e).__name__}: {e}")
    if real:
        sources += real
    else:
        print("[runner] No live DANDI source available -> sim-only FALLBACK "
              "(adding extra sim seed as real-stand-in, flagged in output)")
        fb = simulate(seed=101)
        fb["source"] = "sim_FALLBACK_for_real"
        fb["label"] = "sim(seed=101) [REAL-DATA FALLBACK]"
        sources.append(fb)

    all_out = []
    for src in sources:
        print(f"\n=== {src['label']} ({src['source']}) ===")
        out = run_source(src)
        all_out.append(out)
        ranked = sorted(out["results"], key=lambda r: r["bal_acc"], reverse=True)
        print(f"  latent: {out['latent_kind']} | windows={out['n_windows']} "
              f"(train {out['n_train']}/test {out['n_test']}) | chance={1.0/out['n_states']:.3f}")
        for r in ranked:
            beat = ""
            if "beats_passive" in r:
                beat += (f"  dP0={r['delta_vs_passive']:+.3f}"
                         f"{'*' if r['beats_passive'] else ''}")
            if "beats_matched" in r:
                beat += (f"  dP0b={r['delta_vs_matched']:+.3f}"
                         f"{'*' if r['beats_matched'] else ''}")
            print(f"    {r['operator']:32s} acc={r['bal_acc']:.3f} "
                  f"CI[{r['ci95'][0]:.3f},{r['ci95'][1]:.3f}] "
                  f"{'>chance' if r['above_chance'] else '~chance'}{beat}")

    out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
    with open(out_path, "w") as f:
        json.dump({"sources": all_out}, f, indent=2)
    print(f"\n[runner] wrote {out_path}")
    return all_out


if __name__ == "__main__":
    main()
