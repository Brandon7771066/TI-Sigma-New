"""
Phase-1 numerical falsifier-tests for the Millennium working note
(papers/WORKING_NOTE_MILLENNIUM_UOP_HILBERT_POLYA_LERAY_HOPF_TI_SIGMA_INTEGRATION_2026-06-24.md)

Discipline (#69 / UGI-1 two-phase generate->validate):
  * PREDICTIONS ARE PRE-REGISTERED IN CODE BELOW, BEFORE ANY COMPUTATION.
  * Each test then reports what the numbers actually show.
  * Falsifiers II.8-F1 / II.9-F1: a confirmed prediction only counts as a
    *result* if it is INDEPENDENT of the known number theory. If the GILE/
    quaternion/ternary "prediction" is merely the textbook fact relabelled,
    the honest verdict is "resonance, not result".
  * Nothing here proves RH/GRH. Sanity checks only.

Tests:
  T1  Prime races mod 3, 4, 5, 8, 12  (II.8 / II.9-A)
  T2  Dirichlet beta L(s,chi4) & L(s,chi3) nontrivial zeros on Re(s)=1/2 (II.8 / II.9-A)
  T3  Ternary Cantor string complex dimensions vs Riemann N(T) growth (II.9-B / II.4)
  T4  Operator-eigenvalues-vs-zeta-zeros (II.3 / II.2): HONEST NON-RESULT
"""
import json
import math
import numpy as np
import mpmath as mp

mp.mp.dps = 30
RESULTS = {}

# ---------------------------------------------------------------------------
# PRE-REGISTERED PREDICTIONS  (written before computing; do not edit post hoc)
# ---------------------------------------------------------------------------
# GILE/TRG-1 SPARK rule (II.8): the "imaginary"/Tralse-signed class = the
# quadratic NON-residue (Dirichlet character value -1) should LEAD the count
# over the "real"/G-like class = the quadratic residue (character value +1).
#   mod 3 : QR={1},      nonQR={2}        -> predict 2 leads 1
#   mod 4 : QR={1},      nonQR={3}        -> predict 3 leads 1
#   mod 5 : QR={1,4},    nonQR={2,3}      -> predict {2,3} lead {1,4}
#   mod 8 : QR={1},      nonQR={3,5,7}    -> predict {3,5,7} lead 1
#   mod 12: QR={1},      nonQR={5,7,11}   -> predict {5,7,11} lead 1
# The rule predicts only the DIRECTION (which side leads). It does NOT, from
# GILE structure alone, predict the magnitude/density, nor the ordering AMONG
# several non-residues. That gap is exactly what decides result-vs-resonance.
PREREGISTERED = {
    "rule": "non-residue (chi=-1, 'imaginary/Tralse') leads residue (chi=+1, 'real/G')",
    "predicted_leader_side": "non-residue",
    "qr": {3: [1], 4: [1], 5: [1, 4], 8: [1], 12: [1]},
    "nonqr": {3: [2], 4: [3], 5: [2, 3], 8: [3, 5, 7], 12: [5, 7, 11]},
    "predicts_magnitude": False,
    "predicts_among_nonresidue_order": False,
}
RESULTS["preregistered_predictions"] = PREREGISTERED

# ---------------------------------------------------------------------------
# T1 — Prime races
# ---------------------------------------------------------------------------
def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].astype(np.int64)

N = 10 ** 8
print(f"[T1] sieving primes up to {N:,} ...")
primes = sieve_primes(N)
print(f"[T1] pi({N:,}) = {len(primes):,}")

# log-spaced checkpoints
checkpoints = np.unique(np.round(np.logspace(3, math.log10(N), 500)).astype(np.int64))

def race(q):
    classes = [c for c in range(1, q) if math.gcd(c, q) == 1]
    pm = primes % q
    per_class_sorted = {c: primes[pm == c] for c in classes}
    qr = set(PREREGISTERED["qr"][q])
    nonqr = set(PREREGISTERED["nonqr"][q])

    def counts_at(x):
        return {c: int(np.searchsorted(per_class_sorted[c], x, side="right")) for c in classes}

    # collective statistic S(x) = mean(nonQR counts) - mean(QR counts)
    s_signs = []
    for x in checkpoints:
        cnt = counts_at(x)
        s = (sum(cnt[c] for c in nonqr) / len(nonqr)) - (sum(cnt[c] for c in qr) / len(qr))
        s_signs.append(1 if s > 0 else (-1 if s < 0 else 0))
    frac_nonqr_ahead = float(np.mean(np.array(s_signs) > 0))

    final = counts_at(N)
    s_final = (sum(final[c] for c in nonqr) / len(nonqr)) - (sum(final[c] for c in qr) / len(qr))
    return {
        "classes": classes,
        "final_counts": final,
        "S_final_meanNonQR_minus_meanQR": float(s_final),
        "frac_checkpoints_nonQR_ahead": frac_nonqr_ahead,
        "direction_predicted_correct": bool(s_final > 0),
    }

RESULTS["T1_prime_races"] = {}
for q in (3, 4, 5, 8, 12):
    r = race(q)
    RESULTS["T1_prime_races"][q] = r
    print(f"[T1] mod {q}: final per-class {r['final_counts']}")
    print(f"        S_final(nonQR-QR)={r['S_final_meanNonQR_minus_meanQR']:.1f}  "
          f"frac checkpoints nonQR ahead={r['frac_checkpoints_nonQR_ahead']:.4f}  "
          f"direction correct={r['direction_predicted_correct']}")

# Honest verdict for T1
all_dir_ok = all(RESULTS["T1_prime_races"][q]["direction_predicted_correct"] for q in (3, 4, 5, 8, 12))
RESULTS["T1_verdict"] = {
    "direction_rule_confirmed_all_moduli": bool(all_dir_ok),
    "independent_of_known_number_theory": False,
    "classification": "RESONANCE_NOT_RESULT",
    "why": ("The 'non-residue leads' rule IS Chebyshev's bias (a known, proved-"
            "under-GRH number-theoretic fact) relabelled in GILE terms. Direction "
            "is reproduced, not predicted independently. Per II.8-F1/II.9-F1 this "
            "is resonance. To become a RESULT the framework must predict, from "
            "GILE structure ALONE, something NT does not readily give: e.g. the "
            "density (mod-4 ~0.9959) or the ordering AMONG non-residues (mod 8: "
            "which of 3,5,7 leads). It currently predicts neither."),
}
# Show the among-non-residue ordering the rule does NOT predict (mod 8, mod 12)
for q in (8, 12):
    fc = RESULTS["T1_prime_races"][q]["final_counts"]
    nonqr = PREREGISTERED["nonqr"][q]
    order = sorted(nonqr, key=lambda c: -fc[c])
    RESULTS["T1_prime_races"][q]["nonresidue_order_observed_high_to_low"] = order
    print(f"[T1] mod {q}: observed non-residue order high->low = {order} (rule is silent on this)")

# ---------------------------------------------------------------------------
# T2 — Dirichlet beta zeros on the critical line
# ---------------------------------------------------------------------------
def L_chi4(s):  # Dirichlet beta = L(s, chi4)
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1) / 4) - mp.zeta(s, mp.mpf(3) / 4))

def L_chi3(s):  # L(s, chi3), chi3(1)=+1, chi3(2)=-1
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

def scan_seeds(Lf, t_lo, t_hi, step, n_want):
    """Find good root seeds = local minima of |L(1/2+it)| dipping near 0."""
    ts = np.arange(t_lo, t_hi, step)
    seeds, prev2, prev1, t_prev1 = [], None, None, None
    for t in ts:
        v = abs(complex(Lf(mp.mpf("0.5") + 1j * mp.mpf(float(t)))))
        if prev1 is not None and prev2 is not None:
            if prev1 < prev2 and prev1 < v and prev1 < 0.5:
                seeds.append(float(t_prev1))
                if len(seeds) >= n_want:
                    break
        prev2, prev1, t_prev1 = prev1, v, float(t)
    return seeds

def find_zeros_on_line(Lf, seeds):
    found = []
    for t0 in seeds:
        try:
            z = mp.findroot(lambda s: Lf(s), mp.mpf("0.5") + 1j * mp.mpf(float(t0)))
            im = float(mp.im(z))
            if abs(im) < 1e-6:                                   # skip spurious ~0
                continue
            if any(abs(im - f["im"]) < 1e-3 for f in found):    # dedup
                continue
            found.append({"t0_seed": float(t0),
                          "re": float(mp.re(z)), "im": im,
                          "abs_dev_from_half": float(abs(mp.re(z) - 0.5)),
                          "L_abs_at_root": float(abs(Lf(z)))})
        except Exception as e:  # noqa
            found.append({"t0_seed": float(t0), "error": str(e)})
    return found

def dev_stats(zlist):
    ok = [z for z in zlist if "abs_dev_from_half" in z]
    return {"seeds_attempted": len(zlist), "zeros_found": len(ok),
            "max_abs_dev_from_half": (max(z["abs_dev_from_half"] for z in ok) if ok else None),
            "all_on_critical_line": bool(ok) and all(z["abs_dev_from_half"] < 1e-9 for z in ok)}

print("[T2] scanning + locating Dirichlet L(s,chi4) and L(s,chi3) zeros on the line ...")
beta_zeros = find_zeros_on_line(L_chi4, scan_seeds(L_chi4, 2.0, 25.0, 0.1, 5))
chi3_zeros = find_zeros_on_line(L_chi3, scan_seeds(L_chi3, 2.0, 25.0, 0.1, 5))
chi4_stats, chi3_stats = dev_stats(beta_zeros), dev_stats(chi3_zeros)
RESULTS["T2_dirichlet_zeros"] = {
    "L_chi4_beta": beta_zeros,
    "L_chi3": chi3_zeros,
    "chi4_stats": chi4_stats,
    "chi3_stats": chi3_stats,
    "verdict": ("Every located nontrivial zero of BOTH L-functions sits on Re(s)=1/2 "
                "to high precision (GRH sanity for the mod-4 and mod-3 L-functions). "
                "Consistency check on the Hurwitz-zeta identities used, NOT a proof."),
}
print(f"    chi4: {chi4_stats}")
for z in beta_zeros:
    print(f"      {z}")
print(f"    chi3: {chi3_stats}")
for z in chi3_zeros:
    print(f"      {z}")

# ---------------------------------------------------------------------------
# T3 — Ternary Cantor string complex dimensions vs Riemann N(T)
# ---------------------------------------------------------------------------
D0 = math.log(2) / math.log(3)
period = 2 * math.pi / math.log(3)

def cantor_count(T):  # # complex dimensions with |Im| <= T  (lattice => linear)
    return 2 * math.floor(T / period) + 1

def riemann_N(T):  # leading Riemann zero-counting term
    return (T / (2 * math.pi)) * math.log(T / (2 * math.pi)) - T / (2 * math.pi)

Ts = [50, 100, 500, 1000]
RESULTS["T3_cantor_vs_riemann"] = {
    "cantor_dimension_D0_log3_2": D0,
    "cantor_vertical_period_2pi_over_log3": period,
    "complex_dims_on_vertical_line_Re_s": D0,
    "comparison": [{"T": T, "cantor_count_linear": cantor_count(T),
                    "riemann_N_T": riemann_N(T),
                    "ratio_riemann_over_cantor": riemann_N(T) / cantor_count(T)} for T in Ts],
    "verdict": ("Cantor string is a LATTICE fractal string: complex dimensions are "
                "periodic on the vertical line Re(s)=log_3 2 (~0.6309), so its "
                "counting function grows LINEARLY in T. Riemann N(T) grows like "
                "(T/2pi)log T -- super-linearly -- and its line is Re(s)=1/2. The "
                "ratio diverges, so the Cantor string CANNOT model the zeta zeros; "
                "it is a calibration toy. Modelling zeta needs a NON-lattice / "
                "generalized fractal string. Honest negative calibration result."),
}
print(f"[T3] Cantor D0=log_3 2={D0:.5f}, vertical period 2pi/log3={period:.5f}")
for row in RESULTS["T3_cantor_vs_riemann"]["comparison"]:
    print(f"    T={row['T']}: cantor(linear)={row['cantor_count_linear']} "
          f"riemann_N={row['riemann_N_T']:.2f} ratio={row['ratio_riemann_over_cantor']:.3f}")

# ---------------------------------------------------------------------------
# T4 — Operator eigenvalues vs zeta zeros  (HONEST NON-RESULT)
# ---------------------------------------------------------------------------
first10 = [float(mp.im(mp.zetazero(n))) for n in range(1, 11)]
RESULTS["T4_operator_vs_zeros"] = {
    "first_10_riemann_zero_imag_parts": first10,
    "status": "CANNOT_RUN_HONESTLY",
    "why": ("replit.md's 'cheapest decisive test' is the TWA/Berry-Keating "
            "operator's first-10 eigenvalues vs these first-10 zeros. But NO "
            "concrete self-adjoint operator whose spectrum equals the zeta zeros "
            "is specified anywhere in the corpus -- constructing one IS the open "
            "Hilbert-Polya problem (Berry-Keating xp is heuristic; it does not "
            "yield these numbers). Producing such an operator here would amount to "
            "claiming a proof of RH, which #69 forbids. So this test is logged as "
            "an honest NON-RESULT: the target operator does not yet exist."),
}
print(f"[T4] first 10 zeta zeros (Im): {[round(x,4) for x in first10]}")
print("[T4] NON-RESULT: no concrete operator exists to compare (that is the open problem).")

# ---------------------------------------------------------------------------
with open("analyses/millennium_working_note_tests/results.json", "w") as f:
    json.dump(RESULTS, f, indent=2, default=str)
print("\n[done] results.json written")
