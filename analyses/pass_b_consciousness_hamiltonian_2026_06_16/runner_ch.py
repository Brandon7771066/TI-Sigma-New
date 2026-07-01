"""Experiment A — does the Consciousness-Hamiltonian feature block improve
UNSUPERVISED state decoding over the matched baseline?

Leakage discipline (identical to the retrieval benchmark):
  - latent H built leakage-safe (sim: ground truth; real: TRAIN-ONLY k-means on a
    DISJOINT channel group A, test labeled by nearest train centroid);
  - every feature set standardized on TRAIN ONLY;
  - decoder = class-centroid nearest-neighbour fit on TRAIN labels only
    (this is exactly the P0b matched-baseline readout);
  - balanced accuracy + 95% bootstrap CI; paired bootstrap delta vs BASE.

Feature sets compared on the SAME readout:
  BASE     = group-B window_features (the matched P0b features)
  GILEHEM  = 8-D HEM-GILE block only
  CH       = full Consciousness-Hamiltonian block (HEM-GILE + PD + H_TSC spectrum + graph)
  BASE+CH  = concatenation
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from features import window_features  # noqa: E402
from simulate import simulate  # noqa: E402
from ch_features import ch_window_features  # noqa: E402
from runner import (  # noqa: E402  (reuse vetted leakage-safe helpers)
    kmeans_centroids, assign_nearest, standardize_fit,
    balanced_accuracy, bootstrap_ci, paired_delta_ci,
)

RNG = np.random.default_rng(20260616)


def centroid_fit(Xtr, ytr, K):
    cents = np.zeros((K, Xtr.shape[1]))
    for c in range(K):
        m = ytr == c
        cents[c] = Xtr[m].mean(0) if np.any(m) else Xtr.mean(0)
    return cents


def eval_featureset(X, H, tr, te, K, base_pred=None):
    Xtr = X[tr]
    mu, sd = standardize_fit(Xtr)
    Xs = (X - mu) / sd
    cents = centroid_fit(Xs[tr], H[tr], K)
    pred = assign_nearest(Xs, cents)
    pte, Hte = pred[te], H[te]
    acc = balanced_accuracy(Hte, pte, K)
    lo, hi = bootstrap_ci(Hte, pte, K)
    row = {"bal_acc": acc, "ci95": [lo, hi], "chance": 1.0 / K,
           "above_chance": bool(lo > 1.0 / K)}
    if base_pred is not None:
        md, dlo, dhi, sigf = paired_delta_ci(Hte, pte, base_pred[te], K)
        row["delta_vs_base"] = md
        row["delta_ci95"] = [dlo, dhi]
        row["beats_base"] = sigf
    return row, pred


def run_source(src):
    K = src["n_states"]
    starts, w, fs, sig = src["starts"], src["w"], src["fs"], src["sig"]
    n = len(starts)
    cut = int(0.6 * n)
    split_sample = int(starts[cut])
    tr, te = slice(0, cut), slice(cut, n)

    # ---- leakage-safe latent H ----
    if src["H"] is not None:
        H = np.asarray(src["H"])
        latent_kind = "ground-truth (simulated)"
    else:
        Xa = window_features(sig, fs, src["groupA"], starts, w, split_sample=split_sample)
        amu, asd = standardize_fit(Xa[tr])
        Xa_s = (Xa - amu) / asd
        cent = kmeans_centroids(Xa_s[tr], k=K)
        H = assign_nearest(Xa_s, cent)
        latent_kind = "TRAIN-ONLY k-means on disjoint group A; test=nearest train centroid"

    # ---- feature sets ----
    BASE = window_features(sig, fs, src["groupB"], starts, w, split_sample=split_sample)
    CH = ch_window_features(sig, fs, src["groupB"], starts, w)
    GILEHEM = CH[:, :8]
    BASECH = np.hstack([BASE, CH])

    base_row, base_pred = eval_featureset(BASE, H, tr, te, K)
    sets = {"BASE": base_row}
    preds = {"BASE": base_pred}
    for name, X in [("GILEHEM", GILEHEM), ("CH", CH), ("BASE+CH", BASECH)]:
        row, pred = eval_featureset(X, H, tr, te, K, base_pred=base_pred)
        sets[name] = row
        preds[name] = pred

    return {
        "label": src["label"], "source": src["source"],
        "latent_kind": latent_kind, "n_windows": int(n),
        "n_train": int(cut), "n_test": int(n - cut), "n_states": K,
        "n_obs_channels": len(src["groupB"]),
        "feature_dims": {"BASE": BASE.shape[1], "GILEHEM": 8,
                         "CH": CH.shape[1], "BASE+CH": BASECH.shape[1]},
        "sets": sets,
    }


def main():
    sources = [simulate(seed=0), simulate(seed=7)]
    try:
        from data_dandi import load_first_available
        real = load_first_available(max_sources=2)
        sources += real
        if not real:
            print("[runner_ch] no live DANDI -> sim-only")
    except Exception as e:
        print(f"[runner_ch] DANDI load error: {type(e).__name__}: {e}")

    out = []
    for src in sources:
        print(f"\n=== {src['label']} ({src['source']}) ===")
        r = run_source(src)
        out.append(r)
        print(f"  latent: {r['latent_kind']} | windows={r['n_windows']} "
              f"(tr {r['n_train']}/te {r['n_test']}) | chance={1.0/r['n_states']:.3f}")
        for name in ["BASE", "GILEHEM", "CH", "BASE+CH"]:
            s = r["sets"][name]
            d = ""
            if "delta_vs_base" in s:
                d = f"  dBASE={s['delta_vs_base']:+.3f}{'*' if s['beats_base'] else ''}"
            print(f"    {name:10s} acc={s['bal_acc']:.3f} "
                  f"CI[{s['ci95'][0]:.3f},{s['ci95'][1]:.3f}] "
                  f"{'>chance' if s['above_chance'] else '~chance'}{d}")

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_expA.json")
    with open(path, "w") as f:
        json.dump({"sources": out}, f, indent=2)
    print(f"\n[runner_ch] wrote {path}")
    return out


if __name__ == "__main__":
    main()
