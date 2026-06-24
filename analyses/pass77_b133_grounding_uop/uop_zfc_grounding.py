"""B133 — Grounding the UOP (honest, #69 both ways).

Three computational checks behind the B133 paper. No empirical claims;
pure model-level mathematics. Budget $0 (numpy/scipy local).

PART 1 — The Interior-Optimum Theorem (a ZFC-expressible statement, verified).
  Two rival UOP functionals appear in the corpus:
    (a) squared-error  TF(TT,G) = (1-TT)^2 + (1-G)^2   -> MINIMIZED at the
        CORNER (TT=G=1): NO interior optimum, no 0.93 cap. (B132 step-1 hazard.)
    (b) interior-optimum  J(G,H) = rho*f_cap(G) + g(H), with a tradeoff
        H = 1 - k*G (existence falls as truth is pushed), f_cap log-concave with
        an over-reach penalty above G* = 1 - 1/(2 e^2) ~ 0.9323, g log-concave.
  We confirm (a) has its optimum on the boundary and (b) has a UNIQUE maximizer
  that is INTERIOR whenever the truth-incentive exceeds the existence-cost slope
  at the origin (rho > k/2, with H = 1 - k*G); for high rho (truth-dominant) the
  interior optimum is PINNED AT the cap G*, for intermediate rho it sits strictly
  below, and for rho <= k/2 (truth incentive too weak) it collapses to the LOWER
  boundary G=0. The interior-optimum CLAIM is a CONDITIONAL theorem about (b)
  given stated concavity conditions AND rho > k/2; the FORMS and lambda=2 are posits.

PART 2 — An axiom Bayes/Kolmogorov needs that the UOP does NOT.
  Kolmogorov probability presupposes a SINGLE sample space (Omega, F, P) on
  which ALL observables are jointly measurable -> a global joint distribution
  exists. Fine's theorem (1982): a joint distribution returning the measured
  marginals exists IFF the Bell/CHSH inequalities hold. We compute the classical
  joint-distribution polytope's max CHSH by LP (= 2, the Bell bound) and compare
  to the quantum (Tsirelson) value 2*sqrt(2) ~ 2.828. The quantum statistics lie
  OUTSIDE the joint-distribution polytope => NO single global joint reproduces
  them => the single-joint-measure axiom is the one that fails. The UOP objective
  is defined per measurement context (an optimization of a functional, not the
  conditioning of one global prior), so it does NOT require that axiom:
  "contextual admissibility". This is a DEFINABILITY/consistency advantage, NOT
  an empirical proof that the UOP is correct.

PART 3 — Why mathematics "coincides with 0.93" (B75 reanalysis, de-mystified).
  In the B75 discipline survey, theoretical mathematics is the ONLY field whose
  optimal truth-aggregate A* reaches ~0.93. We show this is NOT an independent
  numerical coincidence: the 0.93 cap is identical for every field; A* reaches it
  ONLY when rho (GILE:HEM dominance) is large enough for the unconstrained
  optimum to exceed the cap, so the cap BINDS. Math has the highest rho (2.4),
  so it alone saturates the cap. A rho-sweep makes the mechanism explicit. The
  defensible claim is the ORDERING ("in math, GILE-truth is THE priority"), not a
  significance test (A* is a single derived archetype, pinned by construction).

PART 4 — HEM-as-residual + supererogatory above-cap GILE (Brandon, this batch).
  Two linked refinements of the cap, demonstrated on a transparent effort-
  allocation model (no over-reach penalty on truth itself):
    maximize  rho*u(G) + v(H)   s.t.  G + H <= 1,  G,H in [0,1],
    u(G)=log(1+G) STRICTLY increasing (truth's marginal value u'(G)=1/(1+G) > 0
    EVERYWHERE -> "you cannot have too much GILE Truth"; no intrinsic ceiling).
  (i) HEM IS THE RESIDUAL: at the joint optimum H* = 1 - G* falls out as the
      LEFTOVER once truth+Myrion (the balance rho*u'(G*) = v'(H*)) are targeted.
      You do NOT separately optimize HEM; it is the residual of pursuing Ultimate
      + Truth -> a "mere identity" with an enlightening property.
  (ii) SUPEREROGATORY ABOVE-CAP: with existence ACTIVE (v'>0) the trade-off
      optimum is interior at G* (we calibrate rho so G* == the 0.9323 cap), so the
      0.93 cap is the SHADOW of the existence opportunity-cost, NOT an intrinsic
      disvalue of truth. In an instance where existence does NOT need to come into
      play (v' == 0), the objective is monotone in G and the optimum is G = 1.0 >
      cap: exceeding 0.93 is PERMISSIBLE (intrinsic-motivation / supererogatory).
  (iii) PERMISSIBLE-BUT-NOT-SUSTAINABLE: a CONSTANT above-cap policy loses to the
      state-contingent policy whenever existence is at stake a positive fraction
      phi of the time; the deficit grows with phi -> above-cap is per-instance
      optimal only when existence is moot, not as a standing policy. Reconciles
      with Part 1: f_cap's over-reach penalty is the reduced-form PROJECTION of
      this trade-off, not an intrinsic penalty on truth.

Run:
    python analyses/pass77_b133_grounding_uop/uop_zfc_grounding.py
"""
from __future__ import annotations

import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

# Canonical constants (URB #523 / #521).
E2_INV = math.exp(-2.0)
L_FLOOR = 1.0 - E2_INV            # existence floor (LCC)              ~ 0.864665
G_STAR = 1.0 - 0.5 * E2_INV       # truth floor / Radiant cap (GILE)   ~ 0.932332
ALPHA = 10.0                      # over-reach penalty (B75 setting)
ORDER = ["G", "I", "L", "E"]
C_FRAG = {"G": 0.30, "I": 0.00, "L": 0.30, "E": 0.15}   # B72 fragility costs


# --------------------------------------------------------------------------- #
# PART 1 — Interior-Optimum Theorem.
# --------------------------------------------------------------------------- #
def f_cap(x: float) -> float:
    return math.log(1.0 + x) if x <= G_STAR else math.log(1.0 + G_STAR) - ALPHA * (x - G_STAR) ** 2


def g_hem(h: float) -> float:
    return math.log(1.0 + max(h, 0.0))


def part1_interior_optimum() -> dict:
    # (a) squared-error functional: minimize (1-TT)^2 + (1-G)^2 on [0,1]^2.
    grid = np.linspace(0.0, 1.0, 501)
    best = (None, None, math.inf)
    for tt in grid:
        for gg in grid:
            tf = (1 - tt) ** 2 + (1 - gg) ** 2
            if tf < best[2]:
                best = (float(tt), float(gg), float(tf))
    sq_corner = abs(best[0] - 1.0) < 1e-6 and abs(best[1] - 1.0) < 1e-6

    # (b) interior-optimum functional J(G) = rho*f_cap(G) + g(1 - k*G), k=0.22.
    k = 0.22
    Gg = np.linspace(0.0, 1.0, 4001)

    def argmax_J(rho: float) -> tuple[float, float]:
        vals = [rho * f_cap(x) + g_hem(1.0 - k * x) for x in Gg]
        i = int(np.argmax(vals))
        return float(Gg[i]), float(vals[i])

    rho_interior_threshold = k / 2.0   # J'(0) = rho - k/2; interior iff rho > k/2
    rows = []
    for rho in [0.05, 0.1, 0.2, 0.4, 0.6, 1.0, 1.4, 2.0, 2.4, 3.0]:
        gopt, jopt = argmax_J(rho)
        rows.append({
            "rho": rho,
            "argmax_G": round(gopt, 4),
            "J": round(jopt, 4),
            "interior": 1e-6 < gopt < 1.0 - 1e-6,
            "lower_boundary_G0": gopt <= 1e-6,
            "at_cap": abs(gopt - G_STAR) < 5e-3,
            "below_cap": 1e-6 < gopt < G_STAR - 5e-3,
        })

    # smallest rho for which the optimum reaches the cap (cap starts to bind).
    rho_scan = np.linspace(0.2, 4.0, 381)
    rho_bind = None
    for rho in rho_scan:
        gopt, _ = argmax_J(float(rho))
        if gopt >= G_STAR - 5e-3:
            rho_bind = round(float(rho), 3)
            break

    return {
        "squared_error_form": {
            "argmin_TT": best[0], "argmin_G": best[1], "min_value": round(best[2], 6),
            "optimum_at_corner_(1,1)": sq_corner,
            "note": "squared-error TF is minimized at the boundary corner; NO interior optimum, NO cap. "
                    "Pin J (interior-optimum), retire squared-error to presentation gloss (B132 step 1).",
        },
        "interior_optimum_form": {
            "tradeoff": "H = 1 - 0.22*G",
            "rows": rows,
            "rho_at_which_cap_binds": rho_bind,
            "rho_interior_threshold_k_over_2": round(rho_interior_threshold, 6),
            "theorem": "Given f_cap log-concave on [0,G*] with a strict over-reach penalty above G*, and g "
                       "increasing & concave, J(G)=rho*f_cap(G)+g(H(G)) is concave on [0,G*] and strictly "
                       "decreasing above G* => UNIQUE maximizer. CONDITIONAL interiority: since J'(0)=rho-k/2, "
                       "the maximizer is INTERIOR (0<G*_opt<1) iff rho>k/2; for rho<=k/2 the truth incentive "
                       "is too weak and the maximizer is the LOWER boundary G=0. When interior it sits AT the "
                       "Radiant cap G* iff rho is large enough that the unconstrained stationary point exceeds "
                       "G*, else strictly below. This statement is first-order ZFC-expressible over (R,<,+,*,exp).",
            "honesty_69": "The THEOREM holds GIVEN the posited concave forms and the cap location G*; it does "
                          "NOT derive those forms. Grounding-in-ZFC = a precise set-theoretic statement + a "
                          "provable interior-optimum lemma, NOT a derivation of the functional from nothing.",
        },
    }


# --------------------------------------------------------------------------- #
# PART 2 — The axiom Bayes needs and the UOP does not (Fine's theorem / CHSH).
# --------------------------------------------------------------------------- #
def part2_axiom_bayes_lacks() -> dict:
    # Classical joint-distribution polytope for a (2-setting, 2-outcome)^2 Bell
    # scenario. 16 deterministic local strategies s assign +/-1 to A0,A1,B0,B1.
    # Any global joint P is a mixture of these. We MAXIMIZE the CHSH functional
    #   S = E(A0 B0) + E(A0 B1) + E(A1 B0) - E(A1 B1)
    # over all such mixtures via LP. Max over the polytope = the Bell bound 2.
    strategies = list(itertools.product([1, -1], repeat=4))  # (a0,a1,b0,b1)
    chsh_coeffs = []
    for (a0, a1, b0, b1) in strategies:
        chsh_coeffs.append(a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1)
    chsh = np.array(chsh_coeffs, float)

    # maximize chsh . p  s.t.  sum p = 1, p >= 0   (linprog minimizes -> negate).
    n = len(strategies)
    res = linprog(
        c=-chsh,
        A_eq=np.ones((1, n)), b_eq=np.array([1.0]),
        bounds=[(0.0, 1.0)] * n, method="highs",
    )
    classical_max_chsh = float(-res.fun)

    tsirelson = 2.0 * math.sqrt(2.0)  # quantum max ~ 2.8284

    # Confirm the quantum point is OUTSIDE the polytope: is there ANY global joint
    # reproducing the four quantum correlations E(Ai Bj)? Set them to the standard
    # singlet values at the CHSH-optimal angles: E = +/- 1/sqrt(2).
    q = 1.0 / math.sqrt(2.0)
    targets = {"A0B0": q, "A0B1": q, "A1B0": q, "A1B1": -q}  # gives S = 2*sqrt2

    def corr_vec(which: str) -> np.ndarray:
        idx = {"A0B0": (0, 2), "A0B1": (0, 3), "A1B0": (1, 2), "A1B1": (1, 3)}[which]
        i, j = idx
        return np.array([s[i] * s[j] for s in strategies], float)

    A_eq = [np.ones(n)]
    b_eq = [1.0]
    for key, val in targets.items():
        A_eq.append(corr_vec(key))
        b_eq.append(val)
    feas = linprog(
        c=np.zeros(n),
        A_eq=np.array(A_eq), b_eq=np.array(b_eq),
        bounds=[(0.0, 1.0)] * n, method="highs",
    )
    joint_exists_for_quantum = bool(feas.success)

    return {
        "scenario": "CHSH (2 settings x 2 outcomes per side); global joint = mixture of 16 local strategies",
        "classical_polytope_max_CHSH": round(classical_max_chsh, 6),
        "quantum_Tsirelson_CHSH": round(tsirelson, 6),
        "quantum_exceeds_classical": tsirelson > classical_max_chsh + 1e-9,
        "global_joint_exists_for_quantum_correlations": joint_exists_for_quantum,
        "fine_theorem": "Fine (1982): a single joint distribution returning the measured marginals exists IFF "
                        "the CHSH inequalities hold. Quantum stats violate them (2.828 > 2) => NO global joint.",
        "the_failing_axiom": "Kolmogorov presupposes ONE sample space (Omega,F,P) carrying ALL observables "
                             "jointly (a global joint measure / non-contextuality). That is the axiom quantum "
                             "reality refutes (Bell 1964; Kochen-Specker 1967; Fine 1982).",
        "uop_advantage": "The UOP objective J is defined per measurement CONTEXT (an optimization of a "
                         "functional, not the conditioning of one global prior); it does NOT require a global "
                         "joint => it satisfies 'contextual admissibility', an axiom Kolmogorov/Bayes violates. "
                         "DEFINABILITY/consistency advantage only — NOT an empirical proof the UOP is correct.",
    }


# --------------------------------------------------------------------------- #
# PART 3 — Math saturates the cap (B75 reanalysis, de-mystified).
# --------------------------------------------------------------------------- #
LEVEL = {"VH": 4, "H": 3, "M": 2, "L": 1}


def _weights(profile: dict) -> dict:
    raw = {k: LEVEL[profile[k]] for k in ORDER}
    s = sum(raw.values())
    return {k: raw[k] / s for k in ORDER}


def _aggregate(w: dict, x: dict) -> float:
    return sum(w[t] * x[t] for t in ORDER)


def _existence(x: dict) -> float:
    return 1.0 - sum(C_FRAG[t] * x[t] for t in ORDER)


def _J(w: dict, x: dict, rho: float) -> float:
    return rho * f_cap(_aggregate(w, x)) + g_hem(_existence(x))


def _optimize(w: dict, rho: float, restarts: int = 80) -> dict:
    best = None
    for _ in range(restarts):
        r = minimize(
            lambda v: -_J(w, {t: v[i] for i, t in enumerate(ORDER)}, rho),
            np.random.rand(4), bounds=[(0, 1)] * 4, method="L-BFGS-B",
        )
        if best is None or r.fun < best.fun:
            best = r
    return {t: float(best.x[i]) for i, t in enumerate(ORDER)}


def part3_math_cap_binding() -> dict:
    np.random.seed(0)
    math_profile = {"G": "H", "I": "VH", "L": "M", "E": "L"}
    w = _weights(math_profile)

    # rho-sweep: A* vs rho -> show the cap begins to bind as rho grows.
    sweep = []
    rho_bind = None
    for rho in np.linspace(0.4, 3.2, 29):
        xstar = _optimize(w, float(rho), restarts=40)
        a = _aggregate(w, xstar)
        binds = a >= G_STAR - 5e-3
        sweep.append({"rho": round(float(rho), 3), "A_star": round(a, 4), "at_cap": binds})
        if binds and rho_bind is None:
            rho_bind = round(float(rho), 3)

    # math at its canonical rho = 2.4.
    x_math = _optimize(w, 2.4, restarts=120)
    a_math = _aggregate(w, x_math)
    per_dim = {t: round(x_math[t], 3) for t in ORDER}
    per_dim_at_cap = {t: abs(x_math[t] - G_STAR) < 5e-3 for t in ORDER}

    return {
        "math_rho": 2.4,
        "math_A_star": round(a_math, 4),
        "gap_to_cap": round(a_math - G_STAR, 4),
        "rho_at_which_cap_binds": rho_bind,
        "rho_sweep": sweep,
        "per_dimension_GILE_allocation": per_dim,
        "per_dimension_each_at_cap": per_dim_at_cap,
        "holistic_scope": "The 0.93 cap is applied HOLISTICALLY to the single GILE AGGREGATE A* = sum_t w_t*x_t "
                          "(one number combining all four dimensions G/I/L/E), NOT to each dimension separately. "
                          "The per-dimension allocation x* is DELIBERATELY AGNOSTIC / problem-specific: here it "
                          "is " + str(per_dim) + " (three dims at 1.0, one far below) while the AGGREGATE sits "
                          "exactly at the cap 0.9323. We claim ~0.93 is ideal for the OVERALL truth-aggregate of "
                          "any given problem; we do NOT claim a per-dimension ideal, and do not extrapolate one.",
        "mechanism": "The 0.93 cap is IDENTICAL for every discipline. A* reaches it ONLY when rho is large "
                     "enough that the unconstrained optimum exceeds the cap => the cap BINDS. Math has the "
                     "highest rho (2.4 across the 12 surveyed), so it ALONE saturates the cap. For NEARLY ALL "
                     "other fields the 0.93 optimum does NOT apply (they optimize below the cap); math is one "
                     "of the only fields for which it does. The 'math = 0.93' match is the cap binding for the "
                     "most truth-dominant field, NOT an independent numerical coincidence.",
        "honesty_69": "A* is a single DERIVED archetype value pinned AT the cap by construction once rho is "
                      "high; there is no sampling distribution, so a frequentist significance test of "
                      "'0.93 vs 0.93-0.95' is not well-defined. The defensible claim is the ORDERING: among "
                      "fields, mathematics is uniquely truth-priority (GILE-truth IS the objective), while "
                      "other fields optimize below the cap (more HEM tradeoff).",
    }


# --------------------------------------------------------------------------- #
# PART 4 — HEM-as-residual + supererogatory above-cap GILE (Brandon refinement).
# --------------------------------------------------------------------------- #
def part4_hem_residual_supererogatory() -> dict:
    # Effort-allocation model: split a unit budget between truth G and existence H.
    #   u(G) = log(1+G)  (truth value; u'(G) = 1/(1+G) > 0 everywhere => no ceiling)
    #   v(H) = log(1+H)  (existence value when ACTIVE)
    #   maximize rho*u(G) + active*v(1-G) over G in [0,1].
    grid = np.linspace(0.0, 1.0, 100001)

    def argmax(rho: float, active: bool) -> float:
        if active:
            vals = rho * np.log1p(grid) + np.log1p(1.0 - grid)
        else:
            vals = rho * np.log1p(grid)            # existence not at stake: v' == 0
        return float(grid[int(np.argmax(vals))])

    # Calibrate rho so the ACTIVE (existence-at-stake) trade-off optimum == cap.
    # Interior FOC: rho/(1+G) = 1/(2-G) => G* = (2 rho - 1)/(1 + rho).
    # Solve for rho giving G* = G_STAR:  rho = (1 + G_STAR) / (2 - G_STAR).
    rho_cal = (1.0 + G_STAR) / (2.0 - G_STAR)
    g_active = argmax(rho_cal, active=True)         # ~ 0.9323 (cap emerges)
    g_inactive = argmax(rho_cal, active=False)      # 1.0 (exceeds cap)
    h_residual = 1.0 - g_active                     # HEM = residual identity

    # Truth's marginal value is strictly positive across the whole range.
    truth_marginal_positive = bool(np.all(1.0 / (1.0 + grid) > 0.0))

    # Sustainability: a CONSTANT above-cap policy (always G=1) vs the state-
    # contingent policy (G=1 when existence moot, G* when existence at stake),
    # over a mix where existence is at stake a fraction phi of the time.
    def obj(rho: float, g: float, active: bool) -> float:
        return rho * math.log1p(g) + (math.log1p(1.0 - g) if active else 0.0)

    sustain = []
    for phi in [0.0, 0.1, 0.25, 0.5, 0.75, 1.0]:
        # always-above-cap plays G=1 in BOTH states.
        always_max = phi * obj(rho_cal, 1.0, True) + (1 - phi) * obj(rho_cal, 1.0, False)
        # contingent plays G* when active, G=1 when inactive (per-instance optimal).
        contingent = phi * obj(rho_cal, g_active, True) + (1 - phi) * obj(rho_cal, 1.0, False)
        sustain.append({
            "phi_existence_at_stake": phi,
            "always_above_cap": round(always_max, 5),
            "state_contingent": round(contingent, 5),
            "above_cap_deficit": round(contingent - always_max, 5),
        })
    deficit_increases_with_phi = all(
        sustain[i + 1]["above_cap_deficit"] >= sustain[i]["above_cap_deficit"] - 1e-9
        for i in range(len(sustain) - 1)
    )

    return {
        "model": "maximize rho*log(1+G) + active*log(1+(1-G)) over G in [0,1]; unit effort budget",
        "rho_calibrated_to_cap": round(rho_cal, 6),
        "G_opt_existence_active": round(g_active, 5),
        "cap_G_star": round(G_STAR, 5),
        "active_optimum_equals_cap": abs(g_active - G_STAR) < 1e-3,
        "G_opt_existence_inactive": round(g_inactive, 5),
        "inactive_optimum_exceeds_cap": g_inactive > G_STAR + 1e-3,
        "hem_residual_H_star": round(h_residual, 5),
        "hem_is_residual": "H* = 1 - G* falls out as the leftover once truth+Myrion are targeted; "
                           "HEM is NOT separately optimized (mere identity, enlightening property).",
        "truth_marginal_value_positive_everywhere": truth_marginal_positive,
        "no_such_thing_as_too_much_truth": "u'(G)=1/(1+G) > 0 for all G in [0,1]; truth's marginal value "
                                           "never turns negative => no INTRINSIC ceiling on GILE-truth. The "
                                           "0.93 cap is the SHADOW of the existence opportunity-cost, present "
                                           "ONLY when existence has a live marginal claim (v' > 0).",
        "supererogatory": "When existence does NOT need to come into play in an instance (v' == 0), the "
                          "objective is monotone in G and the optimum is G=1.0 > 0.93: exceeding the cap is "
                          "PERMISSIBLE (intrinsic-motivation / supererogatory action toward GILE).",
        "sustainability_sweep": sustain,
        "above_cap_deficit_increases_with_phi": deficit_increases_with_phi,
        "permissible_not_sustainable": "A CONSTANT above-cap policy is dominated by the state-contingent "
                                       "policy whenever existence is at stake (phi>0), and the deficit grows "
                                       "with phi => above-cap is per-instance optimal only when existence is "
                                       "moot, NOT as a standing policy (consistent with SUP-1 / UOP cap).",
        "honesty_69": "Model-level illustration only. 'Existence not at stake' (v'==0) is an idealization; "
                      "rho is CALIBRATED (not derived) to make the active optimum coincide with the cap, "
                      "showing the cap CAN arise purely as a trade-off shadow without an intrinsic truth "
                      "penalty. It does NOT prove the cap's numeric value; it reconciles 'no too-much-truth' "
                      "with the established penalty-above-0.93 (the latter = reduced-form projection).",
    }


def main() -> None:
    out = {
        "constants": {
            "e^-2": round(E2_INV, 6),
            "L_existence_floor": round(L_FLOOR, 6),
            "G*_radiant_cap": round(G_STAR, 6),
            "G*_equals_(1+L)/2": abs(G_STAR - (1 + L_FLOOR) / 2) < 1e-12,
        },
        "part1_interior_optimum_theorem": part1_interior_optimum(),
        "part2_axiom_bayes_lacks": part2_axiom_bayes_lacks(),
        "part3_math_cap_binding": part3_math_cap_binding(),
        "part4_hem_residual_supererogatory": part4_hem_residual_supererogatory(),
    }
    here = Path(__file__).resolve().parent
    (here / "results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
