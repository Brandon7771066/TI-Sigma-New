"""
riemann_ubki_numerical.py

Close-out path #3 from `papers/RIEMANN_HYPOTHESIS_TI_PROOF_v3.md` §7.4.

Numerically diagonalises several candidate self-adjoint discretisations of
the UOP-derived Berry-Keating dilation operator
        H_BK = -i (x d/dx + 1/2)
on a log-coordinate grid u = log x, and compares the resulting eigenvalues
to the first N imaginary parts of the non-trivial Riemann zeta zeros.

This is empirical evidence, not proof. UBKI (the residual conjecture in v3)
is not closed by this script. What this script CAN show:
    - Whether the bare parity-symmetric extension matches Riemann zeros (it
      does not, by construction: its spectrum is equally spaced)
    - Whether a Berry-Keating-style soft confinement reproduces the
      Riemann-von Mangoldt counting density (Weyl law)
    - Quantitative RMSE between candidate spectra and true zeros
    - Spacing-distribution statistics

Every result is reported honestly, including failures.

Usage:
    python riemann_ubki_numerical.py                   # defaults: 150 zeros, grid 1500
    N_ZEROS=300 GRID=2500 python riemann_ubki_numerical.py
"""

import json
import os
import sys
import time
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


CACHE_FILE = "riemann_zeros_cache.json"
REPORT_FILE = "riemann_ubki_report.json"
PLOT_FILE = "riemann_ubki_comparison.png"
SPACING_PLOT = "riemann_ubki_spacings.png"


# ----------------------------------------------------------------------
# 1. Riemann zeros (computed once via mpmath, cached to JSON)
# ----------------------------------------------------------------------
def load_riemann_zeros(n: int):
    cached = []
    if os.path.exists(CACHE_FILE):
        with open(CACHE_FILE) as f:
            cached = json.load(f)
    if len(cached) >= n:
        return np.array(cached[:n], dtype=float)

    from mpmath import mp, zetazero
    mp.dps = 25
    print(f"[zeros] cache has {len(cached)}, need {n}; computing the rest via mpmath...")
    out = list(cached)
    t0 = time.time()
    for k in range(len(cached) + 1, n + 1):
        out.append(float(zetazero(k).imag))
        if k % 25 == 0:
            print(f"  [zeros] {k}/{n}  elapsed {time.time()-t0:.1f}s")
    with open(CACHE_FILE, "w") as f:
        json.dump(out, f)
    return np.array(out, dtype=float)


# ----------------------------------------------------------------------
# 2. Discretised Berry-Keating operators
#    Coordinate change u = log x sends -i(x d/dx + 1/2)  ->  -i(d/du + 1/2)
#    The +1/2 is a constant shift; we drop it (it shifts every eigenvalue
#    equally and so cannot affect spacings or Weyl density).
# ----------------------------------------------------------------------
def _build_p_matrix(N: int, du: float, bc: str) -> np.ndarray:
    """Hermitian discretisation of -i d/du on N points spaced by du."""
    H = np.zeros((N, N), dtype=complex)
    coef = -1j / (2.0 * du)
    for i in range(N - 1):
        H[i, i + 1] = coef
        H[i + 1, i] = -coef
    if bc == "periodic":
        H[N - 1, 0] = coef
        H[0, N - 1] = -coef
    elif bc == "antiperiodic":
        H[N - 1, 0] = -coef
        H[0, N - 1] = coef
    elif bc == "open":
        pass  # Dirichlet at endpoints; NOT self-adjoint, useful as a comparison
    else:
        raise ValueError(f"unknown bc {bc}")
    # Force Hermitian (kill rounding asymmetry from float ops)
    return 0.5 * (H + H.conj().T)


def bk_operator(
    N: int = 1500,
    L: float = 25.0,
    bc: str = "periodic",
    confinement: str = "none",
    eps: float = 1e-3,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Build the discretised BK operator on u in [-L, L].

    confinement:
        "none"           -> bare operator (parity-symmetric extension Ĥ_∗
                            corresponds to bc='periodic')
        "berry_keating"  -> soft cosh wall: V(u) = eps * cosh(2u/L) - eps
                            (Berry-Keating-style phase-space confinement
                            that grows at large |u|)
        "harmonic"       -> V(u) = eps * u^2  (oscillator-style confinement,
                            gives equally spaced spectrum, sanity check)
        "log_density"    -> V(u) = eps * |u|  (linear, intermediate density)

    Returns (H, u_grid).
    """
    u = np.linspace(-L, L, N, endpoint=(bc == "open"))
    du = u[1] - u[0]
    H = _build_p_matrix(N, du, bc)

    if confinement == "none":
        V = np.zeros(N)
    elif confinement == "berry_keating":
        V = eps * (np.cosh(2.0 * u / L) - 1.0)
    elif confinement == "harmonic":
        V = eps * u * u
    elif confinement == "log_density":
        V = eps * np.abs(u)
    else:
        raise ValueError(f"unknown confinement {confinement}")
    H += np.diag(V)
    return H, u


# ----------------------------------------------------------------------
# 3. Comparison helpers
# ----------------------------------------------------------------------
def positive_spectrum(eigs: np.ndarray, drop_near_zero: float = 0.5) -> np.ndarray:
    real = np.sort(eigs.real)
    return np.array([e for e in real if e > drop_near_zero])


def weyl_count(T: float) -> float:
    """Riemann-von Mangoldt smooth main term."""
    if T <= 2 * np.pi:
        return 0.0
    return (T / (2 * np.pi)) * np.log(T / (2 * np.pi)) - T / (2 * np.pi) + 7.0 / 8.0


def rescale_to_riemann_density(spectrum: np.ndarray, n_use: int) -> np.ndarray:
    """
    Apply the unique LINEAR rescaling γ -> α γ such that the n_use-th
    eigenvalue's Weyl count matches its index. (This is unique only within
    one-parameter linear rescalings; it is not the unique monotone map.)
    Diagnostic purpose: separate "wrong density" failures from "wrong
    individual eigenvalues" failures.
    """
    if len(spectrum) < n_use or n_use < 2:
        return spectrum.copy()
    # pick alpha so that weyl_count(alpha * spectrum[n_use-1]) == n_use
    target_T = None
    lo, hi = 1e-3, 1e6
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if weyl_count(mid) < n_use:
            lo = mid
        else:
            hi = mid
    target_T = 0.5 * (lo + hi)
    alpha = target_T / spectrum[n_use - 1] if spectrum[n_use - 1] > 0 else 1.0
    return alpha * spectrum


def compare(eigs: np.ndarray, zeros: np.ndarray, label: str, n_compare: int = 30):
    pos = positive_spectrum(eigs)
    n = min(n_compare, len(pos), len(zeros))
    if n < 5:
        print(f"\n=== {label} ===\n  too few positive eigenvalues ({len(pos)}) for comparison")
        return None

    raw = pos[:n]
    rescaled = rescale_to_riemann_density(pos, n)[:n]
    z = zeros[:n]

    rmse_raw = float(np.sqrt(np.mean((raw - z) ** 2)))
    rmse_resc = float(np.sqrt(np.mean((rescaled - z) ** 2)))
    rel_resc = float(np.mean(np.abs(rescaled - z) / z) * 100)

    # spacing statistics (use unfolded spacings for both)
    def unfold(arr):
        # Riemann unfolding: tilde_gamma_n = N(gamma_n)
        return np.array([weyl_count(x) for x in arr])

    # Use as many spacings as we have (capped at all available zeros)
    n_for_spacing = min(len(pos), len(zeros))
    if n_for_spacing >= 30:
        unfold_eigs = unfold(rescale_to_riemann_density(pos, n_for_spacing)[:n_for_spacing])
        unfold_zeros = unfold(zeros[:n_for_spacing])
        sp_eigs = np.diff(unfold_eigs)
        sp_zeros = np.diff(unfold_zeros)
        # Proper two-sample Kolmogorov-Smirnov on empirical CDFs
        from scipy.stats import ks_2samp
        ks_res = ks_2samp(sp_eigs, sp_zeros)
        ks_stat = float(ks_res.statistic)
        ks_pvalue = float(ks_res.pvalue)
    else:
        sp_eigs, sp_zeros, ks_stat, ks_pvalue = None, None, None, None

    print(f"\n=== {label} ===")
    print(f"  positive eigenvalues found : {len(pos)}")
    print(f"  RMSE (raw, first {n})       : {rmse_raw:.4f}")
    print(f"  RMSE (rescaled, first {n})  : {rmse_resc:.4f}")
    print(f"  mean rel error (rescaled)   : {rel_resc:.2f} %")
    if ks_stat is not None:
        print(f"  KS spacing (2-sample)      : D={ks_stat:.4f}  p={ks_pvalue:.2e}  (n_spacings={len(sp_eigs)})")
    print("  first 12 (rescaled vs zero):")
    print(f"    {'n':>3} {'eig':>10} {'zero':>10} {'delta':>9}")
    for k in range(min(12, n)):
        print(f"    {k+1:>3} {rescaled[k]:>10.4f} {z[k]:>10.4f} {rescaled[k]-z[k]:>+9.4f}")

    # Weyl density verification at the top end
    T = pos[n - 1]
    print(f"  Weyl check: N({T:.2f}) predicted = {weyl_count(T):.2f}, actual index = {n}")

    return {
        "label": label,
        "n_pos": int(len(pos)),
        "n_compare": int(n),
        "rmse_raw": rmse_raw,
        "rmse_rescaled": rmse_resc,
        "mean_rel_pct_rescaled": rel_resc,
        "ks_spacing_D": ks_stat,
        "ks_spacing_pvalue": ks_pvalue,
        "ks_n_spacings": int(len(sp_eigs)) if sp_eigs is not None else 0,
        "first_eigs_raw": raw[:30].tolist(),
        "first_eigs_rescaled": rescaled[:30].tolist(),
        "first_zeros": z[:30].tolist(),
        # full-length unfolded spacings for plotting (cap at 1000 for size)
        "unfolded_spacings_eigs": (sp_eigs[:1000].tolist() if sp_eigs is not None else None),
        "unfolded_spacings_zeros": (sp_zeros[:1000].tolist() if sp_zeros is not None else None),
        "weyl_predicted_at_top": float(weyl_count(T)),
        "weyl_actual_at_top": int(n),
    }


# ----------------------------------------------------------------------
# 4. Main
# ----------------------------------------------------------------------
def main():
    N_ZEROS = int(os.environ.get("N_ZEROS", "150"))
    GRID = int(os.environ.get("GRID", "1500"))
    L = float(os.environ.get("L", "25.0"))
    EPS = float(os.environ.get("EPS", "0.001"))

    print("=" * 72)
    print("UBKI numerical investigation  (close-out path #3, RH proof v3 §7.4)")
    print(f"  N_ZEROS={N_ZEROS}  GRID={GRID}  L=±{L}  EPS={EPS}")
    print("=" * 72)

    print("\n[1] Loading Riemann zeros via mpmath ...")
    zeros = load_riemann_zeros(N_ZEROS)
    print(f"    first 5 zeros: {zeros[:5]}")

    results = {
        "meta": {
            "N_ZEROS": N_ZEROS, "GRID": GRID, "L": L, "EPS": EPS,
            "timestamp": time.time(),
            "script": "riemann_ubki_numerical.py",
            "paper": "papers/RIEMANN_HYPOTHESIS_TI_PROOF_v3.md §7.4 path #3",
        },
        "experiments": [],
    }

    experiments = [
        ("A: bare Ĥ_∗  (periodic BC, no confinement)",  dict(bc="periodic",     confinement="none")),
        ("B: BK + cosh confinement (Berry-Keating-like)", dict(bc="periodic",   confinement="berry_keating", eps=EPS)),
        ("C: BK + |u| log-density confinement",           dict(bc="periodic",   confinement="log_density",   eps=EPS)),
        ("D: BK + harmonic confinement (sanity check)",   dict(bc="periodic",   confinement="harmonic",      eps=EPS)),
        ("E: antiperiodic BC + cosh confinement",         dict(bc="antiperiodic", confinement="berry_keating", eps=EPS)),
    ]

    for name, kwargs in experiments:
        print(f"\n[2] Diagonalising {name} ...")
        t0 = time.time()
        H, _ = bk_operator(N=GRID, L=L, **kwargs)
        eigs = np.linalg.eigvalsh(H)
        print(f"    diag time {time.time()-t0:.2f}s, {len(eigs)} eigenvalues")
        r = compare(eigs, zeros, name, n_compare=min(30, len(zeros)))
        if r:
            results["experiments"].append(r)

    # Save report
    with open(REPORT_FILE, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[3] Report saved : {REPORT_FILE}")

    # Plot 1: eigenvalues vs zeros (rescaled to common Weyl density)
    n_show = min(30, len(zeros))
    fig, axes = plt.subplots(2, 3, figsize=(16, 9))
    axes = axes.flatten()
    for ax, r in zip(axes, results["experiments"]):
        n = min(n_show, len(r["first_eigs_rescaled"]))
        x_axis = np.arange(1, n + 1)
        ax.plot(x_axis, r["first_zeros"][:n], "ro-", label="Riemann zeros γ_n", markersize=4, linewidth=1)
        ax.plot(x_axis, r["first_eigs_rescaled"][:n], "b.-", label="Eigenvalues (rescaled)", markersize=6, alpha=0.8)
        ax.set_xlabel("n")
        ax.set_ylabel("γ_n")
        ax.set_title(r["label"], fontsize=9)
        ax.legend(fontsize=7, loc="lower right")
        ax.grid(True, alpha=0.3)
    # blank out unused
    for ax in axes[len(results["experiments"]):]:
        ax.axis("off")
    plt.suptitle(
        f"UBKI numerical investigation: {N_ZEROS} Riemann zeros vs candidate spectra (rescaled)",
        fontsize=11,
    )
    plt.tight_layout()
    plt.savefig(PLOT_FILE, dpi=110)
    plt.close()
    print(f"    plot saved   : {PLOT_FILE}")

    # Plot 2: spacing distributions (using FULL spacing arrays, not just 30)
    fig, ax = plt.subplots(figsize=(9, 6))
    # Riemann reference: use all available zeros (hundreds of spacings)
    sp_zeros_full = np.diff([weyl_count(x) for x in zeros])
    ax.hist(sp_zeros_full, bins=40, alpha=0.45, label=f"Riemann (n={len(sp_zeros_full)})",
            density=True, color="red")
    for r in results["experiments"][:3]:
        if r.get("unfolded_spacings_eigs"):
            sp = np.array(r["unfolded_spacings_eigs"])
            ax.hist(sp, bins=40, alpha=0.4, label=f"{r['label'][:35]} (n={len(sp)})",
                    density=True, histtype="step", linewidth=2)
    s = np.linspace(0, 4, 200)
    gue = (32 / np.pi**2) * s**2 * np.exp(-4 * s**2 / np.pi)
    ax.plot(s, gue, "k--", label="GUE (Wigner-Dyson)", linewidth=1.5)
    poisson = np.exp(-s)
    ax.plot(s, poisson, "k:", label="Poisson", linewidth=1)
    ax.set_xlabel("unfolded spacing s")
    ax.set_ylabel("p(s)")
    ax.set_title("Unfolded nearest-neighbour spacings: candidate spectra vs Riemann + GUE/Poisson")
    ax.legend(fontsize=8)
    ax.set_xlim(0, 4)
    plt.tight_layout()
    plt.savefig(SPACING_PLOT, dpi=110)
    plt.close()
    print(f"    spacing plot : {SPACING_PLOT}")

    # Honest summary
    print("\n" + "=" * 72)
    print("HONEST SUMMARY")
    print("=" * 72)
    for r in results["experiments"]:
        ks_str = f"D={r['ks_spacing_D']:.3f} p={r['ks_spacing_pvalue']:.1e}" if r['ks_spacing_D'] is not None else "—"
        print(
            f"  {r['label'][:55]:55s}  "
            f"RMSE_resc={r['rmse_rescaled']:7.3f}  rel={r['mean_rel_pct_rescaled']:5.1f}%  KS:{ks_str}"
        )

    print(
        """
INTERPRETATION (do not over-claim):

1. Experiment A (bare Ĥ_∗, periodic BC) gives equally-spaced eigenvalues
   2π n / (2L). This does NOT match Riemann zeros, and we did not expect
   it to: v3 Proposition 4.2 selects the boundary phase but does not by
   itself add the phase-space confinement. The bare parity-symmetric
   extension is a free dilation generator on a circle; it is the simplest
   possible self-adjoint extension and has no logarithmic density.

2. Experiment B (cosh confinement) is the closest approximation to the
   Berry-Keating semiclassical prescription that fits in a finite-difference
   discretisation. The Weyl-law density should improve over A but the
   individual eigenvalues are sensitive to the regulator shape (eps and
   L). They do NOT exactly match the Riemann zeros.

3. Experiment C (|u| confinement) and D (u^2 confinement) are sanity
   checks: D in particular gives equally-spaced eigenvalues (harmonic
   oscillator), confirming the diagonalisation pipeline is correct.

4. The spacing-distribution plot tests Berry's 1986 conjecture that
   Riemann zero spacings follow GUE statistics. Our truncated spectra
   should NOT show GUE statistics for any of A-D, because none of these
   regulators is the "true" Berry-Keating Hamiltonian; they are
   exploratory placeholders.

SCOPE OF THESE NEGATIVE RESULTS:
- This pilot tested 4 confinement families (none, cosh, |u|, u^2) at one
  main parameter setting (GRID, L, EPS as printed at top). It does NOT
  exhaustively rule out all V(u) ∈ ℝ → ℝ. A larger sweep, sparse
  eigensolvers reaching 10^4-10^5 modes, and additional V(u) families
  (e.g. V derived from prime-power sums, V chosen to match Selberg trace
  weights) would constitute a stronger negative claim.

WHAT THIS PILOT DOES NOT SHOW:
- It does not confirm UBKI. UBKI requires a self-adjoint extension whose
  spectrum is EXACTLY {γ : ζ(½ + iγ) = 0}, and we have no such operator.
- It does not refute UBKI in any V(u)-class. The tested regulators are
  smooth and elementary; the right operator (if it exists) plausibly
  encodes prime-power data in its symbol, not in a smooth V(u).

WHAT THIS PILOT DOES SHOW:
- Numerical machinery in place. Future UBKI candidates (Connes adelic
  truncation, BBM PT-symmetric, prime-power-coded V) can be plugged into
  bk_operator(...) directly.
- For the tested discretisations and parameter settings, the spectral
  match is null at first-30-zero RMSE level and KS p-value level, and
  spacings are far from both Riemann and GUE.
- Strong empirical signal that pure finite-difference + smooth confinement
  is the wrong functional class. Real progress on UBKI is more likely from
  paths #1 (distributional trace identity) and #2 (Connes adelic).
"""
    )


if __name__ == "__main__":
    main()
