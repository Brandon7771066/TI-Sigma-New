"""
lattice_fhs.py — Fractal Harmonic Systems test on E8 roots and Leech shells.

Two numerical experiments:
  (A) E8 root system: 240 unit-norm vectors in R^8. Compute the empirical
      angular distribution as projected to spherical harmonics on S^7 by
      Monte Carlo, compute power spectrum vs harmonic order ell, and test
      whether the spectrum follows a 1/f^alpha law (FHS criterion).

  (B) Leech lattice: shell populations a_{2k} = |Lambda_24 cap shell of
      squared-norm 4k| for k = 1..K. Computed exactly from the theta
      identity theta_Lambda_24 = E_4^3 - 720 Delta. Test whether the
      log-log slope of a_{2k} vs k follows the FHS prediction (1/f^alpha
      with alpha matching ZetaZ-zero density growth alpha ~ 1).

Honest reporting: any negative result is reported as such. No claims
beyond what the data supports.

Reuses no external API; pure NumPy/SciPy. Output: lattice_fhs_report.json,
lattice_fhs_e8.png, lattice_fhs_leech.png.

URB #791 companion script.
"""

from __future__ import annotations
import json
import time
from typing import List, Tuple
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.stats import linregress


# ----------------------------------------------------------------------
# (A) E8 root system construction
# ----------------------------------------------------------------------
def e8_roots() -> np.ndarray:
    """Standard E8 root system: 240 vectors in R^8.

       (i) 112 D8 roots: all permutations of (+/-1, +/-1, 0, 0, 0, 0, 0, 0).
      (ii) 128 half-integer roots: (+/-1/2)^8 with even number of minuses.

    Returns array of shape (240, 8).
    """
    roots = []
    # (i) D8 roots
    for i in range(8):
        for j in range(i + 1, 8):
            for s1 in (-1, 1):
                for s2 in (-1, 1):
                    v = np.zeros(8)
                    v[i] = s1
                    v[j] = s2
                    roots.append(v)
    # (ii) half-integer roots, even # of minuses
    for mask in range(256):
        bits = [(mask >> b) & 1 for b in range(8)]
        if sum(bits) % 2 == 0:  # even number of '1's = even number of minuses
            v = np.array([0.5 if b == 0 else -0.5 for b in bits])
            roots.append(v)
    R = np.array(roots)
    assert R.shape == (240, 8)
    # all squared norm = 2
    norms2 = np.sum(R * R, axis=1)
    assert np.allclose(norms2, 2.0)
    return R


def e8_angular_power_spectrum(roots: np.ndarray, L_max: int = 30,
                              n_samples: int = 4000, seed: int = 1) -> np.ndarray:
    """
    Compute a proxy 'angular power spectrum' of the E8 root point measure on
    S^7 via the variance-of-counts test:
      For each ell in 1..L_max, draw n_samples random spherical caps of
      angular radius theta_ell = pi / ell. Count roots inside each cap.
      power[ell] = variance of the count divided by mean count.
      For an isotropic Poisson sphere measure this is ~1; deviations encode
      structure at angular scale 1/ell.

    Not a true spherical-harmonic decomposition, but a robust proxy that
    captures angular-scale-dependent clustering, which is what FHS tests.
    """
    rng = np.random.default_rng(seed)
    R_unit = roots / np.linalg.norm(roots, axis=1, keepdims=True)
    n_roots = R_unit.shape[0]
    spectrum = np.zeros(L_max + 1)
    for ell in range(1, L_max + 1):
        theta = np.pi / ell
        cos_thresh = np.cos(theta)
        # random unit vectors on S^7
        x = rng.standard_normal((n_samples, 8))
        x /= np.linalg.norm(x, axis=1, keepdims=True)
        # count roots in cap around each x
        cos_ang = R_unit @ x.T  # (240, n_samples)
        counts = np.sum(cos_ang > cos_thresh, axis=0)  # (n_samples,)
        mu = counts.mean()
        var = counts.var()
        spectrum[ell] = var / max(mu, 1e-12)
    return spectrum


# ----------------------------------------------------------------------
# (B) Leech lattice theta-function shell populations
# ----------------------------------------------------------------------
def divisor_sigma_3(n_max: int) -> np.ndarray:
    """sigma_3(n) = sum_{d | n} d^3 for n = 0..n_max. sigma_3(0):=0."""
    s = np.zeros(n_max + 1, dtype=np.int64)
    for d in range(1, n_max + 1):
        cubes = d ** 3
        for k in range(d, n_max + 1, d):
            s[k] += cubes
    return s


def eisenstein_e4_coeffs(N: int) -> np.ndarray:
    """E_4(q) = 1 + 240 sum_{n>=1} sigma_3(n) q^n, coefficients up to q^N."""
    e4 = np.zeros(N + 1, dtype=object)
    sig = divisor_sigma_3(N)
    e4[0] = 1
    for n in range(1, N + 1):
        e4[n] = 240 * int(sig[n])
    return e4


def power_series_mul(a: np.ndarray, b: np.ndarray, N: int) -> np.ndarray:
    """Multiply two truncated power series (object dtype, big ints)."""
    out = np.zeros(N + 1, dtype=object)
    for i in range(N + 1):
        ai = a[i]
        if ai == 0:
            continue
        # range j in [0, N - i]
        for j in range(0, N + 1 - i):
            bj = b[j]
            if bj == 0:
                continue
            out[i + j] += ai * bj
    return out


def delta_coeffs(N: int) -> np.ndarray:
    """Delta(q) = q * prod_{n>=1} (1 - q^n)^24, coefficients up to q^N."""
    eta24 = np.zeros(N + 1, dtype=object)
    eta24[0] = 1
    for n in range(1, N + 1):
        # multiply by (1 - q^n)^24 truncated to q^N
        fac = np.zeros(N + 1, dtype=object)
        fac[0] = 1
        if n <= N:
            fac[n] = -24
        # higher binomial coefficients of (1-q^n)^24
        from math import comb
        for k in range(2, 25):
            kn = k * n
            if kn > N:
                break
            fac[kn] = ((-1) ** k) * comb(24, k)
        eta24 = power_series_mul(eta24, fac, N)
    # Delta has factor q at the front
    out = np.zeros(N + 1, dtype=object)
    for n in range(1, N + 1):
        out[n] = eta24[n - 1]
    return out


def leech_theta_coeffs(N: int) -> np.ndarray:
    """theta_Lambda_24(q) = E_4(q)^3 - 720 Delta(q), coefficients up to q^N."""
    e4 = eisenstein_e4_coeffs(N)
    e4sq = power_series_mul(e4, e4, N)
    e4cu = power_series_mul(e4sq, e4, N)
    d = delta_coeffs(N)
    out = np.zeros(N + 1, dtype=object)
    for n in range(N + 1):
        out[n] = e4cu[n] - 720 * d[n]
    return out


# ----------------------------------------------------------------------
# (C) Power-law / FHS analysis
# ----------------------------------------------------------------------
def loglog_slope(x: np.ndarray, y: np.ndarray) -> Tuple[float, float, float]:
    """Return (slope, intercept, R^2) of log y vs log x."""
    mask = (x > 0) & (y > 0)
    lx = np.log(x[mask])
    ly = np.log(y[mask])
    res = linregress(lx, ly)
    return float(res.slope), float(res.intercept), float(res.rvalue ** 2)


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------
def main() -> None:
    t0 = time.time()
    report = {"meta": {"script": "lattice_fhs.py", "paper": "papers/URB_791_FHS_E8_LEECH.md"}}

    # (A) E8 angular power spectrum
    print("[A] E8 root system: 240 roots in R^8")
    R = e8_roots()
    print(f"    Constructed {R.shape[0]} roots, all |v|^2 = 2.")
    L_max = 24
    spec = e8_angular_power_spectrum(R, L_max=L_max, n_samples=4000, seed=1)
    ells = np.arange(1, L_max + 1)
    s_e8 = spec[1:L_max + 1]
    slope_e8, _, r2_e8 = loglog_slope(ells, s_e8)
    print(f"    Angular variance/mean spectrum, log-log slope on ell=1..{L_max}:")
    print(f"      slope = {slope_e8:.3f}, R^2 = {r2_e8:.3f}")
    print(f"      (FHS prediction would be slope ~ -1; isotropic Poisson would be slope ~ 0)")
    report["e8"] = {
        "L_max": L_max,
        "n_samples": 4000,
        "spectrum_var_over_mean": s_e8.tolist(),
        "loglog_slope": slope_e8,
        "loglog_r2": r2_e8,
    }

    # (B) Leech shell populations
    print("\n[B] Leech lattice: shell populations a_{2k} via E_4^3 - 720*Delta")
    N = 24  # compute up to q^24 ~ shells with squared-norm up to 24*2=48
    th = leech_theta_coeffs(N)
    a = [int(th[n]) for n in range(N + 1)]
    print(f"    First {N+1} coefficients of theta_Lambda_24:")
    for n in range(N + 1):
        if a[n] != 0:
            print(f"      a_{n} = {a[n]:,}")
    # FHS test: log-log slope of a_{2k} vs k for k=1..N//2
    ks = np.arange(1, N // 2 + 1)
    a_2k = np.array([a[2 * k] for k in ks], dtype=float)
    slope_leech, intercept_leech, r2_leech = loglog_slope(ks, a_2k)
    print(f"\n    log-log slope of a_{{2k}} vs k on k=1..{N//2}:")
    print(f"      slope = {slope_leech:.3f}, R^2 = {r2_leech:.4f}")
    print(f"      (modular-form theory predicts slope = 11 since a_{{2k}} ~ k^11 sigma_11(k))")
    report["leech"] = {
        "N_q": N,
        "shell_pops_2k": a_2k.tolist(),
        "loglog_slope": slope_leech,
        "loglog_r2": r2_leech,
    }

    # (C) Riemann zeros density log-log slope (control comparison)
    print("\n[C] Reference: Riemann zero counting density N(T) ~ T log T / 2pi")
    print("    Density growth slope (in log-log of N(T)/T vs log T) is approx 1.")
    report["control"] = {
        "riemann_density_loglog_slope_predicted": 1.0,
        "note": "FHS criterion as stated in replit.md is three-level synchronization "
                "between brain 1/f, zeta-zero density, and toroidal consciousness; "
                "we only check whether E8 angular spectrum and Leech shell growth "
                "share a power-law signature, not full FHS synchronization.",
    }

    # Plots
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.loglog(ells, s_e8, "o-", label="E8 angular var/mean")
    ax.loglog(ells, ells.astype(float) ** slope_e8 * np.exp(np.log(s_e8[0])), "k--",
              label=f"power-law fit, slope={slope_e8:.2f}")
    ax.set_xlabel("angular harmonic order ell")
    ax.set_ylabel("var(count) / mean(count)")
    ax.set_title("E8 root-system angular spectrum (variance-of-counts proxy)")
    ax.legend()
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    fig.savefig("lattice_fhs_e8.png", dpi=120)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.loglog(ks, a_2k, "o-", label="Leech a_{2k}")
    ax.loglog(ks, np.exp(intercept_leech) * ks.astype(float) ** slope_leech, "k--",
              label=f"power-law fit, slope={slope_leech:.2f}")
    ax.set_xlabel("k (shell index, squared-norm = 4k)")
    ax.set_ylabel("a_{2k} (shell population)")
    ax.set_title("Leech lattice shell populations (modular-form predicted slope = 11)")
    ax.legend()
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    fig.savefig("lattice_fhs_leech.png", dpi=120)
    plt.close(fig)

    report["meta"]["elapsed_s"] = time.time() - t0
    with open("lattice_fhs_report.json", "w") as f:
        json.dump(report, f, indent=2)
    print(f"\n[done] wrote lattice_fhs_report.json, lattice_fhs_e8.png, lattice_fhs_leech.png")
    print(f"[done] total wall time: {time.time()-t0:.1f}s")

    print("\n" + "=" * 78)
    print("HONEST SUMMARY (lattice FHS pilot)")
    print("=" * 78)
    print(f"E8 angular spectrum log-log slope: {slope_e8:+.3f} (R^2 = {r2_e8:.3f})")
    print(f"Leech shell-population log-log slope: {slope_leech:+.3f} (R^2 = {r2_leech:.4f})")
    print()
    print("INTERPRETATION:")
    print("- E8: a slope near 0 means roots are isotropically distributed at the")
    print("  angular scales tested (no fractal signature). A slope near -1 would")
    print("  indicate FHS-style 1/f angular structure. Report what we got.")
    print("- Leech: slope ~ 11 is the modular-form prediction (Eisenstein/Delta")
    print("  growth rate). It is not '1/f fractal' in the FHS sense; it is the")
    print("  rigid arithmetic growth of an even unimodular lattice in 24D.")
    print("- Neither alone establishes FHS three-level synchronization; this is")
    print("  a baseline / null-hypothesis check.")


if __name__ == "__main__":
    main()
