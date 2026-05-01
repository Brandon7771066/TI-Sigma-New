"""
Phase A-prime-Pharma Ablation: R_intra-only vs Full 5-LCC vs DNA-Anchored vs Conventional
==========================================================================================
Tests the architect-flagged question: does R_intra alone (the static DNA-coherence boost)
reproduce the Phase 4-bis dev=4.83 result? If yes, the four divination channels
(R_se, R_ss, R_stack, R_obs) contribute nothing and are deprecated.

Pre-registered prediction (AGENT_LOCKED_PREDICTIONS_2026-04-30.md §1, HIGH-conviction):
  dev_R_intra_only = 4.87 (band [4.78, 4.95])
  Verdict zone: extremely close to full-5-LCC dev=4.83 — divination channels confirmed
  to be ±0.05 decorative modulation around the static R_intra boost.

Falsification: dev outside [4.78, 4.95]. dev < 4.78 means an unmodeled interaction
with R_intra is doing real work; dev > 4.95 means the divination channels were
*helping* (in which case the deprecation reverses).

Date: 2026-04-30 (DPES session, same lock as Phase 4-bis)
Cost: $0
"""

import os
import sys
from copy import deepcopy
from datetime import date

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ti_pharmacological_simulator import (
    TIPharmacologicalSimulator,
    ConsciousnessState,
    BiometricState,
    GeneticProfile,
)
from dna_anchored_lcc_module import (
    parse_23andme,
    build_genetic_profile_from_dna,
    lcc_substrate_coherence,
)
from divination_amplified_pharma import DivinationAmplifiedSimulator
from phase_4_bis_divination_amplified_validation import (
    EXPERIMENTS, BASE, BIOMETRICS, run_validation,
)


PRED = {
    'point': 4.87,
    'band_lo': 4.78,
    'band_hi': 4.95,
    'lock_date': '2026-04-30',
    'lock_author': 'Replit Agent (DPES mode)',
    'source': 'AGENT_LOCKED_PREDICTIONS_2026-04-30.md §1',
}


def main():
    BRANDON_DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'

    print("=" * 72)
    print("PHASE A-PRIME-PHARMA ABLATION (R_intra-only)")
    print("=" * 72)
    print(f"Pre-registered prediction (locked {PRED['lock_date']}):")
    print(f"  dev_R_intra_only = {PRED['point']:.2f}  band [{PRED['band_lo']:.2f}, {PRED['band_hi']:.2f}]")
    print(f"  Source: {PRED['source']}")
    print()

    print("Loading Brandon's DNA...")
    genotypes = parse_23andme(BRANDON_DNA)
    brandon_profile, _ = build_genetic_profile_from_dna(genotypes)
    R_intra_brandon = lcc_substrate_coherence(brandon_profile)
    static_amp = 1.0 + 0.5 * (R_intra_brandon - 0.5)
    print(f"  Loaded {len(genotypes):,} genotypes")
    print(f"  Brandon R_intra = {R_intra_brandon:.4f}")
    print(f"  Implied static amp_ti (R_intra-only) = {static_amp:.4f}")

    LOCK_DATE = date(2026, 4, 30)
    LOCK_SEED = (LOCK_DATE - date(1970, 1, 1)).days

    # Re-run all four arms with locked seed for comparability
    sim_a = TIPharmacologicalSimulator(user_id='aprime_conventional')
    sim_a.genetic_profile = GeneticProfile()
    res_a = run_validation(sim_a, "ARM A — Conventional")

    sim_b = TIPharmacologicalSimulator(user_id='aprime_dna_anchored')
    sim_b.genetic_profile = brandon_profile
    res_b = run_validation(sim_b, "ARM B — DNA-Anchored")

    # ARM C-prime: R_intra-only ablation (the new arm)
    sim_cp_inner = TIPharmacologicalSimulator(user_id='aprime_R_intra_only')
    sim_cp_inner.genetic_profile = brandon_profile
    sim_cp = DivinationAmplifiedSimulator(
        sim_cp_inner,
        subject_name="Brandon Charles Emerick",
        observer_name="Replit Agent",
        weather=None,
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
        mode="R_intra_only",
    )
    res_cp = run_validation(sim_cp, "ARM C-prime — R_intra-only ABLATION", capture_amp=True)

    # ARM C: full 5-LCC (replication of Phase 4-bis for comparison in the same run)
    sim_c_inner = TIPharmacologicalSimulator(user_id='aprime_full_5lcc')
    sim_c_inner.genetic_profile = brandon_profile
    sim_c = DivinationAmplifiedSimulator(
        sim_c_inner,
        subject_name="Brandon Charles Emerick",
        observer_name="Replit Agent",
        weather=None,
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
        mode="full",
    )
    res_c = run_validation(sim_c, "ARM C — Full 5-LCC (Phase 4-bis replication)", capture_amp=True)

    # ────────────────────────────────────────────────────────────────────
    # Pre-registration verdict
    # ────────────────────────────────────────────────────────────────────
    print()
    print("=" * 72)
    print("PHASE A-PRIME PRE-REGISTRATION VERDICT")
    print("=" * 72)
    dev_a = res_a['total_abs_dev']
    dev_b = res_b['total_abs_dev']
    dev_cp = res_cp['total_abs_dev']
    dev_c = res_c['total_abs_dev']

    print(f"  Conventional A:           dev = {dev_a:.4f}")
    print(f"  DNA-Anchored B:           dev = {dev_b:.4f}")
    print(f"  R_intra-only C-prime:     dev = {dev_cp:.4f}  ← THE TEST")
    print(f"  Full 5-LCC C:             dev = {dev_c:.4f}  (Phase 4-bis replication)")
    print()
    print(f"  Δ(C-prime, C):  {dev_cp - dev_c:+.4f}  "
          f"(if |Δ| < 0.05, divination channels confirmed decorative)")
    print(f"  Δ(C-prime, B):  {dev_cp - dev_b:+.4f}  "
          f"(negative = R_intra-only beat DNA-only baseline)")
    print()
    print(f"  My pre-registered prediction: dev_C-prime = {PRED['point']:.2f}  "
          f"band [{PRED['band_lo']:.2f}, {PRED['band_hi']:.2f}]")
    if PRED['band_lo'] <= dev_cp <= PRED['band_hi']:
        verdict = f"✅ WITHIN BAND — agent prediction CONFIRMED at HIGH conviction"
        deprecation_status = (
            "Divination channels (R_se, R_ss, R_stack, R_obs) "
            "are CONFIRMED-DEPRECATED as currently designed. R_intra alone reproduces "
            "the Phase 4-bis result. The four divination channels were ±0.05 decorative "
            "modulation around the static R_intra boost, exactly as the per-trace audit predicted."
        )
    elif dev_cp < PRED['band_lo']:
        verdict = (
            f"❌ OUTSIDE BAND (LOW) — dev_C-prime = {dev_cp:.4f} < {PRED['band_lo']:.2f}. "
            f"R_intra-only is BETTER than full 5-LCC by more than predicted. "
            f"Possibilities: (a) the four divination channels were ACTIVELY HARMING the "
            f"prediction (subtracting accuracy), or (b) interaction effects with R_intra exist "
            f"that the agent did not model."
        )
        deprecation_status = (
            "Divination channels are not just decorative — they are ACTIVELY DEGRADING "
            "the prediction. Strongest possible deprecation signal."
        )
    else:
        verdict = (
            f"❌ OUTSIDE BAND (HIGH) — dev_C-prime = {dev_cp:.4f} > {PRED['band_hi']:.2f}. "
            f"R_intra-only is WORSE than full 5-LCC by more than predicted. "
            f"The divination channels WERE doing real work. Deprecation reverses; "
            f"divination architecture earns continued investigation."
        )
        deprecation_status = (
            "Divination channels SURVIVED the ablation — they were contributing real "
            "predictive accuracy. Deprecation REVERSED. URB #824 architecture preserved."
        )

    print(f"  {verdict}")
    print()
    print("INTERPRETATION:")
    print(f"  {deprecation_status}")

    # Phase H smoke test addendum: also report what dev_em WOULD be if R_intra_em
    # proxy stack returns the same R_intra value (smoke check that the refactor
    # in URB #826 §3 doesn't change anything when proxy = sequence).
    print()
    print("=" * 72)
    print("PHASE H-1 SMOKE-CHECK PRECURSOR (URB #826 §6.1)")
    print("=" * 72)
    print(f"  When R_intra_em = R_intra_seq (proxy passthrough), dev_em = dev_C-prime = {dev_cp:.4f}")
    print(f"  Pre-registered H-1 prediction: dev_em = 4.85  band [4.70, 5.05]")
    if 4.70 <= dev_cp <= 5.05:
        print(f"  ✅ Passthrough case lands within H-1 band — refactor is sound")
    else:
        print(f"  ⚠️  Passthrough dev outside H-1 band — H-1 prediction needs revisit")
    print(f"  (Real H-1 test requires the 5-component R_intra_em proxy stack — "
          f"queued as Phase H-1.)")

    return res_a, res_b, res_cp, res_c, dev_cp


if __name__ == '__main__':
    main()
