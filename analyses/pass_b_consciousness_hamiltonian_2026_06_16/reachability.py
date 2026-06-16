"""Live-mouse OBSERVATIONAL reachability proxy (NECESSARY CONDITION, NOT an
intervention).

#69 HONESTY: the DANDI recordings are pre-recorded; we cannot intervene on the
animals' mood. A closed-loop efficacy PROOF is therefore impossible on this data
(it lives in Experiment B, in simulation). What we CAN ask observationally is a
necessary precondition for any future Mood Amplifier: in the unsupervised latent
state graph, is the high-coupling ("positive mood") target state REACHABLE from
the other states, and how well-mixed is the chain? If the target were an absorbing
sink unreachable from elsewhere, no amplifier could ever steer toward it. Reaching
this bar does NOT demonstrate efficacy -- it only fails to rule it out.

Pipeline (leakage-safe latent identical to Experiment A):
  - latent states H from TRAIN-ONLY k-means on the disjoint channel group A;
  - target = state with the highest mean GILE-L coupling (the "positive mood");
  - empirical transition matrix P (row-normalized counts, Laplace-smoothed);
  - report: reachability (target reachable from every state), stationary prob of
    target, mean first-passage time to target, and the spectral-gap mixing rate.
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from features import window_features  # noqa: E402
from ch_features import ch_window_features, CH_FEATURE_NAMES  # noqa: E402
from runner import kmeans_centroids, assign_nearest, standardize_fit  # noqa: E402

L_IDX = CH_FEATURE_NAMES.index("L")


def transition_matrix(states, K, smooth=0.5):
    P = np.full((K, K), smooth)
    for a, b in zip(states[:-1], states[1:]):
        P[a, b] += 1.0
    return P / P.sum(1, keepdims=True)


def reachable_from_all(P, target, thresh=1e-6):
    """Is `target` reachable from every state via positive-probability paths?"""
    K = P.shape[0]
    adj = P > thresh
    for s in range(K):
        seen, stack = set(), [s]
        while stack:
            u = stack.pop()
            for v in range(K):
                if adj[u, v] and v not in seen:
                    seen.add(v)
                    stack.append(v)
        if target not in seen and s != target:
            return False
    return True


def mean_first_passage(P, target):
    """Expected steps to first reach `target` from each other state."""
    K = P.shape[0]
    others = [s for s in range(K) if s != target]
    Q = P[np.ix_(others, others)]
    try:
        m = np.linalg.solve(np.eye(len(others)) - Q, np.ones(len(others)))
    except np.linalg.LinAlgError:
        return None
    out = {target: 0.0}
    for i, s in enumerate(others):
        out[s] = float(m[i])
    return out


def stationary(P):
    w, v = np.linalg.eig(P.T)
    i = int(np.argmin(np.abs(w - 1.0)))
    p = np.real(v[:, i])
    p = p / p.sum()
    return p


def analyze(src):
    K = src["n_states"]
    sig, fs, starts, w = src["sig"], src["fs"], src["starts"], src["w"]
    n = len(starts)
    cut = int(0.6 * n)
    split_sample = int(starts[cut])

    if src["H"] is not None:
        H = np.asarray(src["H"])
    else:
        Xa = window_features(sig, fs, src["groupA"], starts, w, split_sample=split_sample)
        amu, asd = standardize_fit(Xa[:cut])
        Xa_s = (Xa - amu) / asd
        cent = kmeans_centroids(Xa_s[:cut], k=K)
        H = assign_nearest(Xa_s, cent)

    CH = ch_window_features(sig, fs, src["groupB"], starts, w)
    Lcol = CH[:, L_IDX]
    mean_L = [float(Lcol[H == s].mean()) if np.any(H == s) else 0.0 for s in range(K)]
    target = int(np.argmax(mean_L))

    P = transition_matrix(H, K)
    reach = reachable_from_all(P, target)
    mfpt = mean_first_passage(P, target)
    stat = stationary(P)
    ev = np.sort(np.abs(np.linalg.eigvals(P)))[::-1]
    gap = float(1.0 - ev[1]) if len(ev) > 1 else 1.0

    return {
        "label": src["label"], "source": src["source"], "n_windows": int(n),
        "n_states": K, "mean_gile_L_per_state": [round(x, 4) for x in mean_L],
        "target_state": target, "target_reachable_from_all": bool(reach),
        "stationary_target_prob": round(float(stat[target]), 4),
        "mean_first_passage_to_target": (
            {int(k): round(v, 2) for k, v in mfpt.items()} if mfpt else None),
        "spectral_gap_mixing": round(gap, 4),
    }


def main():
    sources = []
    try:
        from data_dandi import load_first_available
        sources = load_first_available(max_sources=2)
    except Exception as e:
        print(f"[reachability] DANDI load error: {type(e).__name__}: {e}")
    if not sources:
        print("[reachability] no live DANDI source; reachability proxy needs live data.")
        return []

    out = []
    print("OBSERVATIONAL reachability proxy (necessary-condition-only; NO intervention):\n")
    for src in sources:
        r = analyze(src)
        out.append(r)
        print(f"=== {r['label']} ===")
        print(f"  mean GILE-L per state: {r['mean_gile_L_per_state']} "
              f"-> target(positive-mood)=state {r['target_state']}")
        print(f"  target reachable from ALL states: {r['target_reachable_from_all']}")
        print(f"  stationary P(target)={r['stationary_target_prob']}  "
              f"mixing spectral gap={r['spectral_gap_mixing']}")
        print(f"  mean first-passage to target: {r['mean_first_passage_to_target']}\n")

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_reachability.json")
    with open(path, "w") as f:
        json.dump({"sources": out}, f, indent=2)
    print(f"[reachability] wrote {path}")
    return out


if __name__ == "__main__":
    main()
