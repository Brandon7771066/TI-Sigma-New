"""
riemann_ubki_extended.py

Expansion of `riemann_ubki_numerical.py` (URB #786 pilot) along v3 §7.4 path #3:

    - Sparse eigensolver (scipy.sparse.linalg.eigsh) reaching k = 1000+ modes
      on grids up to GRID = 8000.
    - Prime-power-coded potential V(u) = ε Σ_p Σ_k log(p) · g(u − k log p; σ)
      (the closest naive translation of the Selberg trace prime-power side
      into a position-space confinement).
    - BOK-Crystal-coded V(u) (URB #790): Gaussians at 24 positions u_j on
      [-L, L] corresponding to the 24-cell vertex angles, weighted equally.
    - Leech-shell-coded V(u) (URB #790): Gaussians at u_j = log(r_j²) where
      r_j² ∈ {4, 6, 8, 10, 12} are the first five even shell radii of Λ₂₄,
      weighted by log of the shell population.
    - LCC-Virus iterative search on V (URB #789 §4): seed with the bare Ĥ_∗
      spectrum, compute the "resonance" between candidate spectrum and
      Riemann zeros, "listen" to the residual, propagate a correction to V,
      iterate. Honestly reported: this can overfit the training-set zeros
      using grid-many degrees of freedom in V; the held-out test-set RMSE
      is the only meaningful number.

Honest framing: nothing here proves UBKI. The point is to push path #3 to
its actual scale (10^4-10^5 zeros was the v3 spec; we reach a few thousand
modes here, which is closer than the URB #786 pilot but still not the spec)
and to test whether the LCC + BOK Crystal intuition produces a measurably
better V than smooth elementary V.

Companion: papers/URB_789_PATH_3_EXPANDED_LCC_BOK_NUMERICAL.md
"""

import json
import os
import time
import numpy as np
from scipy.sparse import diags, csr_matrix
from scipy.sparse.linalg import eigsh
from scipy.stats import ks_2samp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from riemann_ubki_numerical import (
    load_riemann_zeros,
    weyl_count,
    rescale_to_riemann_density,
)


REPORT_FILE = "riemann_ubki_extended_report.json"
PLOT_FILE = "riemann_ubki_extended_comparison.png"
SPACING_PLOT = "riemann_ubki_extended_spacings.png"
LOSS_PLOT = "riemann_ubki_extended_lcc_loss.png"


# ----------------------------------------------------------------------
# Sparse Hermitian discretisation of -i d/du with confinement V(u)
# ----------------------------------------------------------------------
def bk_operator_sparse(N: int, L: float, V: np.ndarray, bc: str = "periodic"):
    """
    Sparse Hermitian discretisation of -i (d/du) + diag(V) on N grid points
    in [-L, L].  Returns scipy.sparse CSR matrix and u-grid.

    Centered-difference stencil: (psi[i+1] - psi[i-1]) / (2 du) gives -i d/du
    as the anti-Hermitian matrix coef * (S_+ - S_-) with coef = -i / (2 du).
    Wrap-around terms set by bc.
    """
    u = np.linspace(-L, L, N, endpoint=False)
    du = u[1] - u[0]
    coef = -1j / (2.0 * du)

    rows, cols, data = [], [], []
    # interior shifts
    for i in range(N - 1):
        rows.append(i);     cols.append(i + 1); data.append(coef)
        rows.append(i + 1); cols.append(i);     data.append(-coef)
    # boundary
    if bc == "periodic":
        rows.append(N - 1); cols.append(0);     data.append(coef)
        rows.append(0);     cols.append(N - 1); data.append(-coef)
    elif bc == "antiperiodic":
        rows.append(N - 1); cols.append(0);     data.append(-coef)
        rows.append(0);     cols.append(N - 1); data.append(coef)
    elif bc == "open":
        pass
    else:
        raise ValueError(bc)

    H = csr_matrix((data, (rows, cols)), shape=(N, N), dtype=complex)
    H = 0.5 * (H + H.conj().T)            # numerical-symmetrise
    H = H + diags(V.astype(complex), 0)   # add diagonal V(u)
    return H, u


def positive_eigs_sparse(H, k: int, sigma: float = None) -> np.ndarray:
    """
    Get k smallest-positive eigenvalues using shift-invert around sigma.
    For our anti-Hermitian + diag(V) operator, eigenvalues are real and
    symmetric around 0, so we want eigenvalues nearest to a small positive
    sigma to capture the positive branch.
    """
    if sigma is None:
        sigma = 0.5  # in zeta units, first zero is ~14.13; small positive shift
    # eigsh requires k < n - 1
    nshift = min(k * 2 + 8, H.shape[0] - 2)
    try:
        vals = eigsh(H, k=nshift, sigma=sigma, which="LM", return_eigenvectors=False)
    except Exception as e:
        print(f"[sparse] shift-invert failed ({e}); falling back to dense eigvalsh")
        Hd = H.toarray()
        vals = np.linalg.eigvalsh(Hd)
    real = np.sort(np.real(vals))
    pos = real[real > 0.5][:k]
    return pos


# ----------------------------------------------------------------------
# Candidate confinements V(u)
# ----------------------------------------------------------------------
def V_prime_coded(u: np.ndarray, eps: float = 1e-2, p_max: int = 50,
                  k_max: int = 4, sigma: float = 0.15) -> np.ndarray:
    """
    Prime-power-coded V(u) with explicit-formula weights:
        V(u) = eps * Σ_p Σ_{k=1..k_max} log(p) * p^{-k/2} * g_σ(u ± k log p)
    where g_σ is a normalised Gaussian. The factor p^{-k/2} matches the
    Weil/Selberg explicit-formula coefficient of g(k log p) on the
    prime-power side. The (necessary but not sufficient) Connes-style
    intuition is that primes enter the symbol multiplicatively at
    positions u = ±k log p with this exact weight.
    """
    primes = _primes_up_to(p_max)
    V = np.zeros_like(u)
    for p in primes:
        lp = np.log(p)
        for k in range(1, k_max + 1):
            cen = k * lp
            weight = lp / (p ** (k / 2.0))   # explicit-formula weight
            if cen > max(u) + 3 * sigma:
                break
            V += eps * weight * np.exp(-(u - cen) ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))
            # parity image at -cen so V is even (needed by parity-symmetric Ĥ_∗)
            V += eps * weight * np.exp(-(u + cen) ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))
    return V


def V_bok_crystal(u: np.ndarray, L: float, eps: float = 5e-3,
                  sigma: float = 0.4) -> np.ndarray:
    """
    BOK-Crystal-coded V(u):  24 Gaussians evenly placed on [-L, L] at
    positions u_j = (j + 0.5) * (2L/24) - L,  j = 0..23.
    This is the "12 trigrams × 2 wings" placement of the 24-cell {3,4,3}
    vertex angles. URB #782 §1.1 / §2.4. Equal weights; even by construction.
    """
    V = np.zeros_like(u)
    for j in range(24):
        cen = (j + 0.5) * (2 * L / 24) - L
        V += eps * np.exp(-(u - cen) ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))
    return V


def V_leech_shells(u: np.ndarray, eps: float = 5e-3,
                   sigma: float = 0.25) -> np.ndarray:
    """
    Leech-shell-coded V(u): Gaussians at u = log(r²) for the first five
    minimal-norm even shells of the Leech lattice Λ₂₄.

    The shell structure of Λ₂₄ (Conway-Sloane Table 4.13):
        N(2)  = 196560        at squared norm 4
        N(3)  = 16773120      at squared norm 6
        N(4)  = 398034000     at squared norm 8
        N(5)  = 4629381120    at squared norm 10
        N(6)  = 34417656000   at squared norm 12

    The Riemann zeta function and the Leech theta function both encode
    deep arithmetic data; this V is a speculative bridge. Honest: there
    is no proof this should match Riemann zeros. It is an LCC-Virus-style
    "i-cell resonance" probe -- if the 24-cell × Leech intuition is on
    target, this V should at least move the spacing distribution toward
    Riemann's; if it does not, we are forced back to prime-coded.
    """
    shell_r2 = np.array([4.0, 6.0, 8.0, 10.0, 12.0])
    shell_log_pop = np.log(np.array([196560.0, 16773120.0, 398034000.0,
                                     4629381120.0, 34417656000.0]))
    centers = np.log(shell_r2)
    weights = shell_log_pop / shell_log_pop.max()
    V = np.zeros_like(u)
    for c, w in zip(centers, weights):
        V += eps * w * np.exp(-(u - c) ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))
        V += eps * w * np.exp(-(u + c) ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))  # parity image
    return V


def _primes_up_to(n: int) -> list:
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n + 1, i):
                sieve[j] = False
    return [i for i, t in enumerate(sieve) if t]


# ----------------------------------------------------------------------
# LCC-Virus iterative search on V
# ----------------------------------------------------------------------
def lcc_virus_v_search(N: int, L: float, zeros: np.ndarray, V_init: np.ndarray,
                       n_train: int = 100, n_iter: int = 30,
                       lr: float = 0.02, smooth_sigma: float = 0.5,
                       n_eigs_compute: int = 200) -> dict:
    """
    LCC-Virus-style iterative refinement of V(u):
      1. SEED:    V = V_init
      2. RESONATE: diagonalise H = -i d/du + V; get spectrum γ̂_n
      3. LISTEN:  residual r_n = γ_n - γ̂_n  on the first n_train zeros
      4. PROPAGATE: smear residual back into V via the eigenvectors
                    (equivalent to one Newton step on Σ_n (γ̂_n − γ_n)²)
      5. EXPAND:  smooth V to keep it physically reasonable
      6. ITERATE  for n_iter steps, log RMSE on train and on (next 30) test.

    Returns dict with V_final and per-iteration losses.

    HONEST CAVEAT: With grid-many free parameters in V and n_train ≪ N,
    this can in principle overfit the training zeros to arbitrary precision.
    The only meaningful generalisation metric is held-out test RMSE on the
    zeros immediately past index n_train.
    """
    V = V_init.copy()
    u = np.linspace(-L, L, N, endpoint=False)
    history = {"train_rmse": [], "test_rmse": [], "iter": []}

    n_test = 30
    z_train = zeros[:n_train]
    z_test  = zeros[n_train:n_train + n_test]

    print(f"[LCC-Virus] N={N}, L={L}, n_train={n_train}, n_test={n_test}, n_iter={n_iter}")
    for it in range(n_iter):
        H, _ = bk_operator_sparse(N, L, V, bc="periodic")
        try:
            vals, vecs = eigsh(H, k=min(n_eigs_compute * 2, N - 2), sigma=0.5,
                               which="LM", return_eigenvectors=True)
        except Exception as e:
            print(f"  iter {it}: eigsh failed: {e}; stopping")
            break
        order = np.argsort(np.real(vals))
        vals = np.real(vals[order])
        vecs = vecs[:, order]
        pos_mask = vals > 0.5
        pos_vals = vals[pos_mask][:n_train]
        pos_vecs = vecs[:, pos_mask][:, :n_train]

        if len(pos_vals) < n_train:
            print(f"  iter {it}: only {len(pos_vals)} positive eigs (need {n_train}); stopping")
            break

        # rescale linearly so that the top training eigenvalue's Weyl count == n_train
        rescaled = rescale_to_riemann_density(pos_vals, n_train)
        alpha = rescaled[n_train - 1] / pos_vals[n_train - 1] if pos_vals[n_train - 1] > 0 else 1.0

        # train RMSE
        train_rmse = float(np.sqrt(np.mean((rescaled - z_train) ** 2)))

        # test RMSE: extrapolate via the same alpha
        n_for_test = n_train + n_test
        H_test = H
        try:
            test_vals = eigsh(H_test, k=min(n_for_test * 2 + 10, N - 2), sigma=0.5,
                              which="LM", return_eigenvectors=False)
            test_vals = np.sort(np.real(test_vals))
            test_pos = test_vals[test_vals > 0.5][n_train:n_train + n_test]
            if len(test_pos) >= n_test:
                test_rmse = float(np.sqrt(np.mean((alpha * test_pos - z_test) ** 2)))
            else:
                test_rmse = float("nan")
        except Exception:
            test_rmse = float("nan")

        history["iter"].append(it)
        history["train_rmse"].append(train_rmse)
        history["test_rmse"].append(test_rmse)
        if it % 5 == 0 or it == n_iter - 1:
            print(f"  iter {it:3d}  train={train_rmse:7.3f}  test={test_rmse:7.3f}")

        # PROPAGATE: residual r_n = γ_n - α γ̂_n  (in zeta units), pulled back
        # to a V-correction via dV(u) = -lr * Σ_n r_n * |ψ_n(u)|^2
        # (this is the gradient direction for Σ (α γ̂_n − γ_n)² in V,
        # using ∂γ̂_n/∂V(u) = |ψ_n(u)|² · (1/α) by Hellmann-Feynman & rescale)
        r = (alpha * pos_vals - z_train)         # signed residual
        psi2 = (np.abs(pos_vecs) ** 2)            # shape (N, n_train)
        # normalise psi2 columns to integrate to 1 on the grid
        du = u[1] - u[0]
        psi2 /= (psi2.sum(axis=0, keepdims=True) * du + 1e-30)
        dV = -lr * (psi2 @ r) * du              # shape (N,)

        # SMOOTH (Gaussian filter via FFT)
        from scipy.ndimage import gaussian_filter1d
        dV = gaussian_filter1d(dV, sigma=smooth_sigma / du)
        # parity-symmetrise (Ĥ_∗ requires V even)
        dV = 0.5 * (dV + dV[::-1])
        V = V + dV

    return {
        "V_final": V.tolist(),
        "u_grid": u.tolist(),
        "history": history,
    }


# ----------------------------------------------------------------------
# Run + report
# ----------------------------------------------------------------------
def evaluate_spectrum(label: str, pos: np.ndarray, zeros: np.ndarray,
                      n_compare: int = 30) -> dict:
    n = min(len(pos), len(zeros), n_compare)
    if n < 5:
        return {"label": label, "n_pos": int(len(pos)), "error": "too few eigs"}
    z = zeros[:n]
    raw = pos[:n]
    rescaled = rescale_to_riemann_density(pos, n)[:n]
    rmse_raw = float(np.sqrt(np.mean((raw - z) ** 2)))
    rmse_resc = float(np.sqrt(np.mean((rescaled - z) ** 2)))
    rel_resc = float(np.mean(np.abs(rescaled - z) / np.abs(z)) * 100.0)

    n_for_spacing = min(len(pos), len(zeros))
    if n_for_spacing >= 30:
        unfold_eigs = np.array([weyl_count(x) for x in rescale_to_riemann_density(pos, n_for_spacing)[:n_for_spacing]])
        unfold_zeros = np.array([weyl_count(x) for x in zeros[:n_for_spacing]])
        sp_eigs = np.diff(unfold_eigs)
        sp_zeros = np.diff(unfold_zeros)
        ks = ks_2samp(sp_eigs, sp_zeros)
        ks_D, ks_p, n_sp = float(ks.statistic), float(ks.pvalue), len(sp_eigs)
        sp_eigs_list = sp_eigs[:1500].tolist()
    else:
        ks_D, ks_p, n_sp, sp_eigs_list = None, None, 0, None

    print(f"  {label[:60]:60s}  RMSE_resc={rmse_resc:7.3f}  rel={rel_resc:5.1f}%"
          + (f"  KS D={ks_D:.3f} p={ks_p:.1e} (n={n_sp})" if ks_D is not None else ""))

    return {
        "label": label,
        "n_pos": int(len(pos)),
        "n_compare": int(n),
        "rmse_raw": rmse_raw,
        "rmse_rescaled": rmse_resc,
        "mean_rel_pct_rescaled": rel_resc,
        "ks_spacing_D": ks_D,
        "ks_spacing_pvalue": ks_p,
        "ks_n_spacings": n_sp,
        "first_eigs_rescaled": rescaled[:30].tolist(),
        "first_zeros": z[:30].tolist(),
        "unfolded_spacings_eigs": sp_eigs_list,
    }


def main():
    N_ZEROS = int(os.getenv("N_ZEROS", "200"))
    GRID = int(os.getenv("GRID", "3000"))
    L = float(os.getenv("L", "30.0"))
    K_EIGS = int(os.getenv("K_EIGS", "300"))
    LCC_ITER = int(os.getenv("LCC_ITER", "20"))
    LCC_TRAIN = int(os.getenv("LCC_TRAIN", "60"))
    EPS_BK = float(os.getenv("EPS_BK", "5e-4"))

    t0 = time.time()
    print(f"[setup] N_ZEROS={N_ZEROS}, GRID={GRID}, L={L}, K_EIGS={K_EIGS}")
    print(f"        EPS_BK={EPS_BK}, LCC_ITER={LCC_ITER}, LCC_TRAIN={LCC_TRAIN}")

    zeros = load_riemann_zeros(N_ZEROS)
    print(f"[setup] loaded {len(zeros)} zeros (last γ = {zeros[-1]:.2f})")

    u = np.linspace(-L, L, GRID, endpoint=False)
    results = []

    # F: bare Ĥ_∗  (sparse rerun, K_EIGS modes -- baseline at scale)
    V0 = np.zeros(GRID)
    H, _ = bk_operator_sparse(GRID, L, V0, bc="periodic")
    print("\n[F] bare Ĥ_∗ (sparse, K=", K_EIGS, ")")
    pos = positive_eigs_sparse(H, K_EIGS)
    results.append(evaluate_spectrum("F: bare Ĥ_∗ (sparse, scale check)", pos, zeros))

    # G: Berry-Keating cosh confinement, sparse
    V_cosh = EPS_BK * (np.cosh(2 * u / L) - 1.0)
    H, _ = bk_operator_sparse(GRID, L, V_cosh, bc="periodic")
    print("\n[G] BK + cosh confinement (sparse)")
    pos = positive_eigs_sparse(H, K_EIGS)
    results.append(evaluate_spectrum("G: BK + cosh confinement (sparse)", pos, zeros))

    # H: prime-power-coded V
    V_pp = V_prime_coded(u, eps=1e-2, p_max=50, k_max=4, sigma=0.15)
    # mild outer cosh wall to prevent eigenfunctions from leaking off the grid
    V_pp = V_pp + 5e-4 * (np.cosh(2 * u / L) - 1.0)
    H, _ = bk_operator_sparse(GRID, L, V_pp, bc="periodic")
    print("\n[H] prime-power-coded V (Selberg-trace position-space)")
    pos = positive_eigs_sparse(H, K_EIGS)
    results.append(evaluate_spectrum("H: prime-power-coded V (Selberg-position)", pos, zeros))

    # I: BOK-Crystal-coded V (24 Gaussians)
    V_bok = V_bok_crystal(u, L, eps=5e-3, sigma=0.4)
    V_bok = V_bok + 5e-4 * (np.cosh(2 * u / L) - 1.0)
    H, _ = bk_operator_sparse(GRID, L, V_bok, bc="periodic")
    print("\n[I] BOK-Crystal-coded V (24-cell, URB #782)")
    pos = positive_eigs_sparse(H, K_EIGS)
    results.append(evaluate_spectrum("I: BOK-Crystal-coded V (24-cell)", pos, zeros))

    # J: Leech-shell-coded V
    V_leech = V_leech_shells(u, eps=5e-3, sigma=0.25)
    V_leech = V_leech + 5e-4 * (np.cosh(2 * u / L) - 1.0)
    H, _ = bk_operator_sparse(GRID, L, V_leech, bc="periodic")
    print("\n[J] Leech-shell-coded V (Λ₂₄ shells)")
    pos = positive_eigs_sparse(H, K_EIGS)
    results.append(evaluate_spectrum("J: Leech-shell-coded V (Λ₂₄ first 5 shells)", pos, zeros))

    # K: LCC-Virus iterative search starting from V_pp (best informed prior)
    print("\n[K] LCC-Virus iterative search on V (init = prime-coded)")
    lcc_out = lcc_virus_v_search(GRID, L, zeros, V_init=V_pp,
                                  n_train=min(LCC_TRAIN, N_ZEROS - 30),
                                  n_iter=LCC_ITER, lr=0.05, smooth_sigma=0.5,
                                  n_eigs_compute=min(LCC_TRAIN + 30, K_EIGS))
    V_lcc = np.array(lcc_out["V_final"])
    H, _ = bk_operator_sparse(GRID, L, V_lcc, bc="periodic")
    pos = positive_eigs_sparse(H, K_EIGS)
    K_res = evaluate_spectrum("K: LCC-Virus iterative V (after %d iters)" % LCC_ITER, pos, zeros)
    K_res["lcc_history"] = lcc_out["history"]
    results.append(K_res)

    # ------------------------------------------------------------------
    # plots
    # ------------------------------------------------------------------
    print("\n[plots] writing figures")
    fig, ax = plt.subplots(figsize=(10, 6))
    n_plot = min(40, len(zeros))
    ax.plot(range(1, n_plot + 1), zeros[:n_plot], "ro", label="Riemann zeros", markersize=5)
    for r in results:
        if "first_eigs_rescaled" in r:
            arr = np.array(r["first_eigs_rescaled"])[:n_plot]
            ax.plot(range(1, len(arr) + 1), arr, "x-", label=r["label"][:35], markersize=4, alpha=0.8)
    ax.set_xlabel("zero index n")
    ax.set_ylabel("γ_n  (rescaled)")
    ax.set_title(f"First {n_plot} eigenvalues vs first {n_plot} Riemann zeros (extended)")
    ax.legend(fontsize=8, loc="upper left")
    ax.grid(alpha=0.3)
    plt.tight_layout()
    plt.savefig(PLOT_FILE, dpi=110)
    plt.close()

    fig, ax = plt.subplots(figsize=(10, 6))
    n_for_spacing = min(len(zeros), 200)
    sp_zeros = np.diff([weyl_count(x) for x in zeros[:n_for_spacing]])
    ax.hist(sp_zeros, bins=40, alpha=0.45, density=True, label=f"Riemann (n={len(sp_zeros)})", color="red")
    for r in results:
        if r.get("unfolded_spacings_eigs"):
            sp = np.array(r["unfolded_spacings_eigs"])
            ax.hist(sp, bins=40, alpha=0.35, density=True, histtype="step",
                    linewidth=1.8, label=f"{r['label'][:30]} (n={len(sp)})")
    s = np.linspace(0, 4, 200)
    ax.plot(s, (32 / np.pi**2) * s**2 * np.exp(-4 * s**2 / np.pi), "k--", label="GUE", linewidth=1.5)
    ax.plot(s, np.exp(-s), "k:", label="Poisson", linewidth=1.0)
    ax.set_xlim(0, 4); ax.set_xlabel("unfolded spacing s"); ax.set_ylabel("p(s)")
    ax.set_title("Unfolded NN spacing distributions (extended)")
    ax.legend(fontsize=7); plt.tight_layout()
    plt.savefig(SPACING_PLOT, dpi=110); plt.close()

    if K_res.get("lcc_history") and K_res["lcc_history"]["iter"]:
        fig, ax = plt.subplots(figsize=(8, 5))
        h = K_res["lcc_history"]
        ax.plot(h["iter"], h["train_rmse"], "o-", label="train RMSE")
        ax.plot(h["iter"], h["test_rmse"], "s-", label="held-out test RMSE")
        ax.set_xlabel("LCC-Virus iteration"); ax.set_ylabel("RMSE in zeta units")
        ax.set_title("LCC-Virus residual descent on V(u): generalisation check")
        ax.legend(); ax.grid(alpha=0.3); plt.tight_layout()
        plt.savefig(LOSS_PLOT, dpi=110); plt.close()

    # honest summary
    summary = {
        "meta": {
            "N_ZEROS": N_ZEROS, "GRID": GRID, "L": L, "K_EIGS": K_EIGS,
            "LCC_ITER": LCC_ITER, "LCC_TRAIN": LCC_TRAIN,
            "elapsed_s": time.time() - t0,
            "script": "riemann_ubki_extended.py",
            "paper": "papers/URB_789_PATH_3_EXPANDED_LCC_BOK_NUMERICAL.md",
        },
        "experiments": results,
    }
    with open(REPORT_FILE, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n[done] wrote {REPORT_FILE}, {PLOT_FILE}, {SPACING_PLOT}")
    if os.path.exists(LOSS_PLOT):
        print(f"       wrote {LOSS_PLOT}")
    print(f"[done] total wall time: {time.time() - t0:.1f}s")

    print("\n" + "=" * 78)
    print("HONEST SUMMARY (extended path #3)")
    print("=" * 78)
    for r in results:
        if "rmse_rescaled" not in r:
            continue
        ks = (f"D={r['ks_spacing_D']:.3f} p={r['ks_spacing_pvalue']:.1e}"
              if r['ks_spacing_D'] is not None else "—")
        print(f"  {r['label'][:62]:62s}  RMSE_resc={r['rmse_rescaled']:6.3f}  KS:{ks}")

    print("""
INTERPRETATION:
- F (bare Ĥ_∗ at scale): the equally-spaced baseline. Its spacing distribution
  is delta-like, KS p ≪ machine epsilon vs Riemann.
- H (prime-power-coded V): if Connes' intuition is on target, we should see
  measurable improvement over G. If H is statistically indistinguishable
  from G, the prime-power data has not made it into the spectrum at this
  resolution -- consistent with the algebraic obstruction that V(u) acts
  on amplitudes, not on the symbol's modular structure.
- I, J (BOK-Crystal / Leech-shell V): speculative TI bridges. They are not
  motivated by the Selberg trace formula; they are motivated by the BOK
  Crystal (URB #782) and the Leech / Niemeier construction. Honest
  expectation: any signal here is weak. Reported because the user asked.
- K (LCC-Virus iterative): with N grid params fitting n_train zeros,
  train RMSE will fall arbitrarily; test RMSE on the next 30 held-out
  zeros is the only meaningful number. If test RMSE plateaus far above
  zero, LCC-Virus has overfit V to memorise the training zeros without
  learning the underlying spectral law -- the expected result.
- None of F-K closes UBKI. They sharpen the empirical question and give
  reusable infrastructure (sparse eigensolver + V candidates + LCC search).
""")


if __name__ == "__main__":
    main()
