"""Vetted leakage-safe benchmark helpers — ported verbatim from
analyses/pass_b_consciousness_hamiltonian_2026_06_16/runner.py so the
hemodynamic replication uses the SAME decoding/CI machinery (no re-derivation)."""
import numpy as np

RNG = np.random.default_rng(20260616)


def kmeans_centroids(X, k=3, iters=50, seed=0):
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
