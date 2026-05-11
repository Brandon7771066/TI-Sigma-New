"""
T45-6 — PD = (-3, 2) Riemann-zero KS test (Pass-45 §6, frozen pre-reg).

Pre-reg (literal): filter Odlyzko zeros to γ ∈ (-3, 2). Compute nearest-neighbor
spacing distribution, KS-test against GUE Wigner surmise p(s) = (32/π²)·s²·exp(-4s²/π).
  CONFIRM:   KS p-value < 0.05  (PD-canonical-final survives empirical test)
  KILL:      KS p-value ≥ 0.05  (PD-Riemann claim same fate as Pass-38 §F-2 disconfirm)

#69 BRUTAL HONESTY DISCLOSURE (logged BEFORE running):
  Odlyzko's tabulated zeros are imaginary parts γ_n of nontrivial zeros, ALL > 0,
  with γ_1 ≈ 14.1347 the smallest. The literal filter γ ∈ (-3, 2) captures
  ZERO zeros. The pre-reg as written in Pass-45 §6 is therefore VACUOUS — it
  cannot be evaluated under the literal filter.

  Per Pass-45 §11 anti-cheat rule: post-hoc threshold/spec changes require
  explicit amendment paper. Per Pass-33 A1-qc25 architect-style precedent,
  the cleanest honesty move is:
    (1) Report the literal verdict as INDETERMINATE (vacuous filter).
    (2) Run TWO well-defined amendment-tests (A1-T6 and A2-T6) with explicit
        timestamp + clearly-labeled status (NOT pre-registered, exploratory),
        whose results are reportable but DO NOT count as CONFIRM/KILL of the
        original Pass-45 §6 claim.
    (3) Mark the original Pass-45 §6 claim "REQUIRES SPEC CLARIFICATION FROM
        BRANDON" — until PD = (-3, 2) is unambiguously mapped to a Riemann
        coordinate system (γ scale? σ scale? log-spacing index?), the claim
        is OPERATIONALLY UN-PRE-REGISTRABLE.

Amendment A1-T6 (exploratory, not part of pre-reg):
  Take ALL 10⁵ Odlyzko zeros. Compute nearest-neighbor unfolded spacings
  (normalized by mean local spacing per the standard Riemann-zero unfolding
  procedure: s_n = (γ_{n+1} - γ_n) · log(γ_n/(2π)) / (2π)). KS-test
  against GUE Wigner surmise. This tests the Montgomery pair correlation /
  Hilbert-Pólya conjecture, which is well-established to give
  GUE-consistent statistics (KS p typically > 0.10 for large n). REJECT
  here means PD claim incompatible with established Riemann-zero ↔ GUE
  agreement; CONFIRM means departure from GUE detected (which would be a
  major result independent of TI Sigma).

Amendment A2-T6 (exploratory, not part of pre-reg):
  Take the FIRST C(5,3)=10 zeros (γ_1..γ_10 — chosen because |PD support|
  = (-3, 2) has length 5 and PD is suggested as Perfect-Fifth-derived;
  this is a STRETCH interpretation flagged as such). KS-test their
  unfolded spacings against GUE. Small-n caveat: KS test has very low
  power at n=10. Result reportable as exploratory only.

Source: Odlyzko zero table https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1
        (downloaded to ./zeros1.txt; 100,000 zeros, smallest γ_1 ≈ 14.1347).
"""
import json, os, time, hashlib
import numpy as np
from scipy import stats

ROOT = os.path.dirname(os.path.abspath(__file__))
ZEROS_PATH = os.path.join(ROOT, "zeros1.txt")
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def load_zeros():
    """Load Odlyzko zeros (one per line, leading whitespace, decimal γ values)."""
    gammas = []
    with open(ZEROS_PATH) as f:
        for line in f:
            line = line.strip()
            if line:
                gammas.append(float(line))
    return np.array(gammas)


def gue_wigner_surmise_cdf(s):
    """CDF of the GUE Wigner surmise p(s) = (32/π²)·s²·exp(-4s²/π).
    Computed numerically via cumulative trapezoid on dense grid (closed-form
    is messy)."""
    grid = np.linspace(0, 10, 100001)
    p = (32.0 / np.pi**2) * grid**2 * np.exp(-4.0 * grid**2 / np.pi)
    cdf_grid = np.concatenate([[0.0], np.cumsum((p[:-1] + p[1:]) / 2 * np.diff(grid))])
    return np.interp(s, grid, cdf_grid)


def unfolded_spacings(gammas):
    """Standard Riemann-zero unfolding (Odlyzko 1987):
    s_n = (γ_{n+1} - γ_n) · log(γ_n / (2π)) / (2π)
    This normalizes so that mean spacing → 1, comparable to GUE."""
    if len(gammas) < 2:
        return np.array([])
    diffs = np.diff(gammas)
    g = gammas[:-1]
    safe = g > 2 * np.pi
    s = np.zeros_like(diffs)
    s[safe] = diffs[safe] * np.log(g[safe] / (2 * np.pi)) / (2 * np.pi)
    return s[safe]


def ks_against_gue(spacings):
    if len(spacings) < 2:
        return {"n": int(len(spacings)), "ks_stat": None, "p_value": None,
                "verdict": "INDETERMINATE_INSUFFICIENT_DATA"}
    ks_stat, p = stats.kstest(spacings, gue_wigner_surmise_cdf)
    return {"n": int(len(spacings)),
            "ks_stat": float(ks_stat),
            "p_value": float(p),
            "mean_spacing": float(np.mean(spacings)),
            "median_spacing": float(np.median(spacings)),
            "min_spacing": float(np.min(spacings)),
            "max_spacing": float(np.max(spacings))}


def main():
    results = {
        "pass": 45,
        "test_id": "T45-6_pd_riemann",
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "prereg": "see runner.py docstring (frozen at commit-time)",
        "honesty_disclosure": (
            "Literal pre-reg filter γ ∈ (-3, 2) yields 0 zeros from "
            "Odlyzko (smallest γ_1 ≈ 14.1347). LITERAL VERDICT = "
            "INDETERMINATE_VACUOUS_FILTER. Two amendment-tests run as "
            "exploratory, NOT counting as CONFIRM/KILL of original claim."
        ),
    }

    gammas = load_zeros()
    results["n_zeros_loaded"] = int(len(gammas))
    results["gamma_min"] = float(gammas.min())
    results["gamma_max"] = float(gammas.max())

    # ── Literal pre-reg test ──────────────────────────────────────────
    pd_filtered = gammas[(gammas > -3.0) & (gammas < 2.0)]
    results["literal_prereg"] = {
        "filter": "γ ∈ (-3, 2)",
        "n_in_filter": int(len(pd_filtered)),
        "verdict": "INDETERMINATE_VACUOUS_FILTER",
        "note": ("Odlyzko zeros are positive imaginary parts ≥ 14.1347; "
                 "no Riemann zeros lie in (-3, 2) under standard γ "
                 "convention. Pass-45 §6 spec underdetermined."),
    }

    # ── Amendment A1-T6: ALL zeros, unfolded GUE test ─────────────────
    s_all = unfolded_spacings(gammas)
    a1 = ks_against_gue(s_all)
    a1["amendment_id"] = "A1-T6"
    a1["amendment_status"] = "EXPLORATORY_NOT_PREREG"
    a1["amendment_timestamp"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    a1["interpretation"] = (
        "Tests Hilbert-Pólya / Montgomery conjecture: Riemann zero spacings "
        "should be GUE-consistent. Established literature finds GUE agreement "
        "for large n. KS p > 0.05 → spacings consistent with GUE → standard "
        "physics. KS p < 0.05 → departure from GUE → would be a major result "
        "independent of TI Sigma."
    )
    results["amendment_A1_all_zeros_vs_GUE"] = a1

    # ── Amendment A2-T6: first 10 zeros ───────────────────────────────
    s_10 = unfolded_spacings(gammas[:10])
    a2 = ks_against_gue(s_10)
    a2["amendment_id"] = "A2-T6"
    a2["amendment_status"] = "EXPLORATORY_NOT_PREREG_VERY_LOW_POWER"
    a2["amendment_timestamp"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    a2["interpretation"] = (
        "Stretch interpretation of 'Perfect-Fifth' as 'first 5-related cluster'. "
        "n=9 spacings → KS power very low. Reportable but not actionable."
    )
    results["amendment_A2_first10_zeros_vs_GUE"] = a2

    # ── Combined verdict ──────────────────────────────────────────────
    results["overall_verdict"] = (
        "LITERAL_PREREG_INDETERMINATE_VACUOUS_FILTER. "
        "Recommend Brandon clarify PD=(-3,2) ↔ Riemann-coordinate mapping "
        "before re-running. Per Pass-45 §11, original §6 claim is now "
        "marked REQUIRES_SPEC_CLARIFICATION rather than KILL/CONFIRM."
    )
    results["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)

    print("=== T45-6 PD-Riemann KS test ===")
    print(f"Zeros loaded: {results['n_zeros_loaded']} "
          f"(γ range [{results['gamma_min']:.4f}, {results['gamma_max']:.4f}])")
    print(f"LITERAL pre-reg verdict: {results['literal_prereg']['verdict']} "
          f"(n_in_filter={results['literal_prereg']['n_in_filter']})")
    print(f"A1-T6 (all {a1['n']} unfolded spacings vs GUE): "
          f"KS={a1['ks_stat']:.4f} p={a1['p_value']:.4g}")
    print(f"A2-T6 (first 9 spacings vs GUE):                 "
          f"KS={a2['ks_stat']:.4f} p={a2['p_value']:.4g}")
    print(f"Overall: {results['overall_verdict']}")


if __name__ == "__main__":
    main()
