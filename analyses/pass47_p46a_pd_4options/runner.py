"""
p46-A — All 4 PD = (-3, 2) coordinate-mapping interpretations operationalized
        as fresh pre-registered tests.

This runner addresses Brandon's "go ahead with all 4" directive on p46-A by
running each of the 4 candidate Riemann-coordinate interpretations as its OWN
pre-registered test, with FROZEN kill/promote thresholds. Brandon picks which
verdict counts after seeing all 4.

Pre-reg (frozen at commit; SHA256 in results.json["runner_sha256"]):

OPTION A — γ-COORDINATE WINDOW (most natural Riemann reading)
  Operationalization: PD support has length 5 ((-3, 2)). Take the FIRST 5 Riemann
  zeros (γ_1..γ_5). Compute their 4 unfolded spacings. KS-test against GUE
  Wigner surmise.
  CONFIRM: KS p < 0.05 AND median spacing inside (-3, 2) when unfolded
  KILL:    KS p > 0.50 (consistent with GUE = no PD signal at small-n)
  INDETERMINATE: 0.05 ≤ p ≤ 0.50

OPTION B — σ-COORDINATE (real-axis shift)
  Operationalization: PD = (-3, 2) on σ-axis means real part of zeros lies
  in (-2.5, 2.5) after centering on σ=1/2. By RH (assumed for Odlyzko table),
  ALL listed zeros have σ=1/2, trivially in any (-3, 2)-derived window.
  CONFIRM: 100% of zeros have σ ∈ (1/2 - 3, 1/2 + 2) = (-2.5, 2.5)
           AND any non-trivial zero with σ ≠ 1/2 in this window would
           refute RH (would require Odlyzko-extension data we don't have).
  KILL:    Any zero in table has σ ∉ (-2.5, 2.5).
  HONEST CAVEAT: this is CONFIRM-vacuous: trivially holds, says nothing
  about PD's structural content. Logged as such.

OPTION C — UNFOLDED-SPACING LOG-WINDOW
  Operationalization: take all 99,999 unfolded nearest-neighbor spacings.
  Filter to those with log_10(s) ∈ (-3, 2), i.e. s ∈ (0.001, 100). KS-test
  against GUE Wigner surmise restricted to that window.
  CONFIRM: KS p > 0.50 AND filter-fraction > 0.95 (PD-window contains
           essentially all GUE mass = consistent rather than contradictory)
  KILL:    KS p < 0.001 OR filter-fraction < 0.50
  INDETERMINATE: between thresholds

OPTION D — PERFECT-FIFTH MUSICAL (NOT Riemann-coordinate)
  Operationalization: PD = (-3, 2) as semitone interval (-3 semitones below
  reference to +2 semitones above). The width 5 = perfect fifth (7 semitones
  via complement) or minor sixth depending on convention.
  This is NOT-RIEMANN-TESTABLE. Verdict: NOT_APPLICABLE_NOT_A_RIEMANN_CLAIM.
  Reportable as "Brandon must specify ANY Riemann-coordinate interpretation
  for the Riemann-connection claim to be empirically testable; under D, the
  Riemann-connection claim is a categorical mismatch and should be
  REWITHDRAWN from §7.7.40 PD-canonical-final."

Anti-HARK: this docstring frozen at commit-time. SHA256 logged. Verdicts
mechanically follow thresholds. No post-hoc reframing.

Honest meta-note: I (the agent) am operationalizing these 4 options without
Brandon's explicit pick of A/B/C/D. He said "go ahead with all 4" — I read
that as "run all 4 and let me see." If any verdict surprises Brandon, he
can challenge the operationalization and we re-run.
"""
import json, os, time, hashlib
import numpy as np
from scipy import stats

ROOT = os.path.dirname(os.path.abspath(__file__))
ZEROS_PATH = os.path.join(os.path.dirname(ROOT), "pass45_t6_pd_riemann", "zeros1.txt")
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def load_zeros():
    return np.array([float(l.strip()) for l in open(ZEROS_PATH) if l.strip()])


def gue_wigner_cdf(s):
    grid = np.linspace(0, 10, 100001)
    p = (32.0 / np.pi**2) * grid**2 * np.exp(-4.0 * grid**2 / np.pi)
    cdf = np.concatenate([[0.0], np.cumsum((p[:-1] + p[1:]) / 2 * np.diff(grid))])
    return np.interp(s, grid, cdf)


def unfolded_spacings(gammas):
    if len(gammas) < 2:
        return np.array([])
    diffs = np.diff(gammas)
    g = gammas[:-1]
    safe = g > 2 * np.pi
    s = np.zeros_like(diffs)
    s[safe] = diffs[safe] * np.log(g[safe] / (2 * np.pi)) / (2 * np.pi)
    return s[safe]


def option_A(gammas):
    """First 5 zeros, 4 unfolded spacings, KS vs GUE."""
    s = unfolded_spacings(gammas[:5])
    if len(s) < 2:
        return {"verdict": "INSUFFICIENT_DATA"}
    ks, p = stats.kstest(s, gue_wigner_cdf)
    median_in_window = -3.0 < float(np.median(s)) < 2.0
    if p < 0.05 and median_in_window:
        verdict = "CONFIRM"
    elif p > 0.50:
        verdict = "KILL"
    else:
        verdict = "INDETERMINATE"
    return {
        "n_spacings": int(len(s)),
        "spacings": s.tolist(),
        "ks_stat": float(ks), "p_value": float(p),
        "median_spacing": float(np.median(s)),
        "median_in_window": median_in_window,
        "verdict": verdict,
        "interpretation": "γ-window: first 5 zeros' unfolded spacings vs GUE (small-n)",
    }


def option_B(gammas):
    """σ-coordinate trivial check."""
    # All Odlyzko zeros assumed σ = 1/2 by RH. Window (-3, 2) on shifted σ.
    sigma = 0.5
    in_window = -3.0 < (sigma - 0.5) < 2.0  # trivially True
    return {
        "all_zeros_have_sigma_one_half": True,
        "in_PD_window": in_window,
        "fraction_in_window": 1.0,
        "verdict": "CONFIRM_VACUOUS",
        "interpretation": (
            "σ-axis interpretation. RH-respecting zeros all have σ=1/2 "
            "which is trivially inside any (-3, 2)-derived window. CONFIRM "
            "is content-free; this interpretation says nothing structural "
            "about PD."
        ),
    }


def option_C(gammas):
    """Unfolded-spacing log-window filter."""
    s_all = unfolded_spacings(gammas)
    log_s = np.log10(np.maximum(s_all, 1e-300))
    in_window = (log_s > -3.0) & (log_s < 2.0)
    s_filt = s_all[in_window]
    fraction = float(in_window.mean())
    if len(s_filt) < 2:
        return {"verdict": "INSUFFICIENT_DATA", "fraction_in_window": fraction}
    ks, p = stats.kstest(s_filt, gue_wigner_cdf)
    if p > 0.50 and fraction > 0.95:
        verdict = "CONFIRM"
    elif p < 0.001 or fraction < 0.50:
        verdict = "KILL"
    else:
        verdict = "INDETERMINATE"
    return {
        "n_total_spacings": int(len(s_all)),
        "n_in_window": int(len(s_filt)),
        "fraction_in_window": fraction,
        "log10_s_range_in_window": [-3.0, 2.0],
        "ks_stat": float(ks), "p_value": float(p),
        "verdict": verdict,
        "interpretation": "Log-window: spacings with log_10(s) ∈ (-3, 2) vs GUE",
    }


def option_D(gammas):
    """Perfect-Fifth musical interpretation: NOT Riemann-testable."""
    return {
        "verdict": "NOT_APPLICABLE_NOT_A_RIEMANN_CLAIM",
        "interpretation": (
            "PD = (-3, 2) interpreted as semitone interval (musical Perfect-Fifth-related). "
            "Under interpretation D, the Riemann-connection claim of Pass-37 PD-canonical-final "
            "is categorically mismatched (musical-interval ≠ Riemann-coordinate). "
            "Recommendation: if Brandon picks D, retract the Riemann-connection clause from "
            "PD-canonical-final and re-spec PD as a musical-interval claim with separate "
            "(non-Riemann) operationalization."
        ),
        "implication_for_pass37": "PARTIAL_RETRACTION_OF_RIEMANN_CLAUSE_NEEDED_IF_D_CHOSEN",
    }


def main():
    gammas = load_zeros()
    results = {
        "pass": 47,
        "test_id": "p46a_pd_4options",
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_zeros_loaded": int(len(gammas)),
        "prereg": "see runner.py docstring; thresholds frozen at commit-time",
        "options": {
            "A_gamma_window_first5": option_A(gammas),
            "B_sigma_coordinate":    option_B(gammas),
            "C_log_window_filter":   option_C(gammas),
            "D_perfect_fifth_musical": option_D(gammas),
        },
        "summary": {},
    }
    for k, v in results["options"].items():
        results["summary"][k] = v.get("verdict")
    results["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print("=== p46-A: 4 PD interpretations ===")
    for k, v in results["summary"].items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
