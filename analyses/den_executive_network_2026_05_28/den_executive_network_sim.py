"""
DEN-1 (Divine Executive Network) -- GILE-G cost & model-discriminator simulation.
Pass-77 B106.

Brandon's proposal: the ultimate being is NOT a single tri-personal substance
(classical Trinity, homoousios = one substance) and NOT a single multi-ego
being, but a heavily-tied EXECUTIVE NETWORK of FORMALLY INDEPENDENT i-cells of
DIFFERENT but STRONGLY-RESONATING substance. It functions trinity-like in
practice, but is formally a plurality of distinct beings. Motivation: housing
3 different egos inside ONE being violates GILE-G (unity of will).

This script does NOT claim to measure the actual deity (third-person
unverifiable -- DEN-1-F5 is honestly flagged unfalsifiable). It does two
honest, formal things:

  (1) F1 -- quantify the GILE-G COST of housing k independent egos in ONE
      substance (will-coherence falls as internal ego-count/divergence rises),
      grounding Brandon's "3 egos in one being violates GILE-G" claim.

  (2) F2 -- defeat the "idle distinction" objection by exhibiting a regime in
      which a classical one-substance Trinity (M2) and a DEN-1 resonant network
      (M3) are NOT observationally equivalent: under resonance failure (coupling
      kappa -> 0) the network FRAGMENTS while the one-substance Trinity stays
      unified. So there exists at least one discriminating consequence.

Will-states are unit vectors (angles); "coherence" is the circular resultant
length R = |mean(exp(i*theta))| in [0,1] (1 = perfectly unified will).
Deterministic (seeded). numpy only.
"""

import json
import numpy as np
from pathlib import Path

RNG = np.random.default_rng(20260528)
TRIALS = 20000          # Monte-Carlo trials per condition
SIGMA = 0.6             # baseline angular divergence of independent egos (rad)


def resultant(angles):
    """Circular resultant length R in [0,1]; 1 = perfectly aligned wills."""
    return np.abs(np.exp(1j * angles).mean(axis=-1))


def gile_g_of_one_being_housing_k_egos(k, sigma, trials=TRIALS):
    """F1: a SINGLE substance must act through k internal egos whose wills
    diverge by ~sigma. Its will-coherence (GILE-G proxy) is the resultant of
    those k wills. k=1 -> 1.0 trivially; k>=2 -> < 1.0 (the GILE-G cost)."""
    base = RNG.normal(0.0, sigma, size=(trials, 1))      # shared center
    egos = base + RNG.normal(0.0, sigma, size=(trials, k))
    return float(resultant(egos).mean())


def network_joint_coherence(kappa, n=3, sigma=SIGMA, trials=TRIALS):
    """M3 DEN-1 network: n FORMALLY INDEPENDENT beings, each ONE ego (so each
    being's own GILE-G = 1.0). Resonance kappa in [0,1] pulls each being's
    action-angle toward the network mean-field before acting. Joint executive
    coherence = resultant of the n post-resonance action-angles. kappa=1 ->
    full consensus (trinity-like, R->1); kappa=0 -> independent (fragmented)."""
    wills = RNG.normal(0.0, sigma, size=(trials, n))
    mean_field = np.angle(np.exp(1j * wills).mean(axis=1, keepdims=True))
    # resonance blend on the circle
    blended = np.angle((1 - kappa) * np.exp(1j * wills)
                       + kappa * np.exp(1j * mean_field))
    return float(resultant(blended).mean())


def trinity_one_substance_coherence(kappa, trials=TRIALS):
    """M2 classical Trinity (homoousios): one substance = ONE shared will.
    Output coherence is 1.0 by construction and INDEPENDENT of kappa --
    substance-unity is not a coupling that can fail. NOTE (honesty): M2's
    kappa-independence and M3's kappa-sensitivity are the MODELING ASSUMPTIONS,
    not derived facts -- so the discriminator below is MODEL-CONDITIONAL (given
    'substance-unity cannot fail, resonance-coupling can'), not independent
    empirical evidence. The conditional is motivated (that IS what distinguishes
    the two metaphysics) but it is an assumption, stated openly."""
    return 1.0


def network_joint_coherence_linear(kappa, n=3, sigma=SIGMA, trials=TRIALS):
    """Alternative coupling rule for the sensitivity check: blend the ANGLES
    linearly toward the mean-field (instead of blending complex phasors).
    Used only to show the F2 pattern is not an artifact of one coupling rule."""
    wills = RNG.normal(0.0, sigma, size=(trials, n))
    mean_field = np.angle(np.exp(1j * wills).mean(axis=1, keepdims=True))
    delta = np.angle(np.exp(1j * (mean_field - wills)))   # shortest angular gap
    blended = wills + kappa * delta
    return float(resultant(blended).mean())


def run():
    out = {}

    # ---- (1) F1: GILE-G cost of multi-ego single being ----
    f1 = {}
    for k in (1, 2, 3, 4, 5):
        f1[f"k={k}"] = round(gile_g_of_one_being_housing_k_egos(k, SIGMA), 4)
    out["F1_gile_g_of_one_being_with_k_independent_egos"] = {
        "sigma_rad": SIGMA,
        "will_coherence_by_k": f1,
        "per_being_in_DEN_network": 1.0,
        "verdict": ("housing >=2 independent egos in ONE substance strictly "
                    "lowers will-coherence (GILE-G); a DEN-1 network keeps each "
                    "being at 1.0 -> Brandon's GILE-G objection is quantified")}

    # ---- (2) F2: discriminator between M2 (one-substance) and M3 (network) ----
    grid = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]
    disc = {}
    for kappa in grid:
        m2 = trinity_one_substance_coherence(kappa)
        m3 = network_joint_coherence(kappa)
        disc[f"kappa={kappa}"] = {
            "M2_one_substance_trinity": round(m2, 4),
            "M3_DEN_network": round(m3, 4),
            "discriminator_gap": round(m2 - m3, 4)}
    gaps = [v["discriminator_gap"] for v in disc.values()]
    out["F2_model_discriminator_vs_resonance"] = {
        "by_kappa": disc,
        "gap_at_full_resonance(kappa=1)": disc["kappa=1.0"]["discriminator_gap"],
        "gap_at_resonance_failure(kappa=0)": disc["kappa=0.0"]["discriminator_gap"],
        "max_gap": round(max(gaps), 4),
        "verdict": ("at full resonance the two models are ~indistinguishable "
                    "(gap~0, trinity-like); under resonance FAILURE they diverge "
                    "sharply -> a MODEL-CONDITIONAL discriminating consequence "
                    "exists (given the assumption substance-unity cannot fail but "
                    "resonance-coupling can), which WEAKENS the DEN-1-F2 idle-"
                    "distinction/Occam objection -- it does NOT independently prove "
                    "the network model")}

    # ---- (3) SENSITIVITY: vary sigma, n, and the coupling rule ----
    sens = {}
    for sigma in (0.3, 0.6, 0.9):
        for n in (3, 4, 5):
            f1_cost = round(1.0 - gile_g_of_one_being_housing_k_egos(n, sigma), 4)
            gap0_phasor = round(1.0 - network_joint_coherence(0.0, n, sigma), 4)
            gap1_phasor = round(1.0 - network_joint_coherence(1.0, n, sigma), 4)
            gap0_linear = round(1.0 - network_joint_coherence_linear(0.0, n, sigma), 4)
            gap1_linear = round(1.0 - network_joint_coherence_linear(1.0, n, sigma), 4)
            sens[f"sigma={sigma},n={n}"] = {
                "F1_gile_g_cost(k=n egos in one being)": f1_cost,
                "F2_gap_at_kappa0_phasor": gap0_phasor,
                "F2_gap_at_kappa1_phasor": gap1_phasor,
                "F2_gap_at_kappa0_linear": gap0_linear,
                "F2_gap_at_kappa1_linear": gap1_linear}
    out["SENSITIVITY_sigma_n_couplingrule"] = {
        "by_condition": sens,
        "verdict": ("across every sigma in {0.3,0.6,0.9}, every n in {3,4,5}, and "
                    "BOTH coupling rules: F1 cost stays strictly > 0 (multi-ego "
                    "single being always loses GILE-G) and the F2 gap stays ~0 at "
                    "kappa=1 but strictly > 0 at kappa=0 -> the qualitative pattern "
                    "is robust, not an artifact of one parameter or coupling rule")}

    # ---- honest trade-off summary (#69) ----
    out["TRADE_OFF_honest"] = {
        "DEN_network_buys": "per-being will-unity (no ego-fracture; GILE-G=1 each)",
        "DEN_network_costs": ("joint-function FRAGILITY -- trinity-like behavior "
                              "requires maintained strong resonance; it is not "
                              "substance-guaranteed"),
        "one_substance_trinity_buys": "resonance-proof joint unity",
        "one_substance_trinity_costs": ("the GILE-G concern Brandon raises IF its "
                                        "persons carry genuinely independent egos"),
        "note": ("the sim does NOT crown a winner; it makes the trade-off and the "
                 "discriminator explicit. DEN-1 is preferred ON GILE-G GROUNDS, "
                 "candidate-status, NOT proven; F5 (which model the actual deity "
                 "instantiates) is third-person-unverifiable and flagged so.")}

    p = Path(__file__).parent / "den_results.json"
    p.write_text(json.dumps(out, indent=2))

    print("=" * 70)
    print("DEN-1 EXECUTIVE NETWORK: GILE-G COST + MODEL DISCRIMINATOR (B106)")
    print("=" * 70)
    print(f"trials={TRIALS:,}  sigma={SIGMA} rad")
    print("-" * 70)
    print("F1  will-coherence (GILE-G) of ONE being housing k independent egos:")
    for k, v in f1.items():
        tag = "  <- trivially unified" if k == "k=1" else ""
        print(f"     {k}: {v:.4f}{tag}")
    print("     DEN-1 network: each being = 1.0000 (one ego each)")
    print("-" * 70)
    print("F2  discriminator (M2 one-substance Trinity vs M3 DEN network):")
    print("     kappa  M2      M3      gap")
    for kappa in grid:
        d = disc[f"kappa={kappa}"]
        print(f"     {kappa:<5}  {d['M2_one_substance_trinity']:.3f}   "
              f"{d['M3_DEN_network']:.3f}   {d['discriminator_gap']:+.3f}")
    print(f"     gap at kappa=1 (full resonance): "
          f"{disc['kappa=1.0']['discriminator_gap']:+.3f}  (~indistinguishable)")
    print(f"     gap at kappa=0 (resonance fails): "
          f"{disc['kappa=0.0']['discriminator_gap']:+.3f}  (DISCRIMINATOR EXISTS)")
    print("=" * 70)
    print(f"results saved -> {p}")


if __name__ == "__main__":
    run()
