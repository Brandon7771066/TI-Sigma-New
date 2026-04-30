"""
Phase 4 Execution: DNA-Anchored vs Conventional LCC Validation
==============================================================
Compares the existing pharma simulator (conventional) against the same simulator
WITH Brandon's actual DNA-derived GeneticProfile injected.

Pre-registration: papers/PRE_REGISTRATION_DNA_ANCHORED_LCC_VALIDATION.md
Date: 2026-04-30
Cost: $0
"""

import os
import sys
import math
from copy import deepcopy

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


# Same N=12 experiment registry as pharma_simulator_validation.py
# (abbreviated to essential fields for comparison)
EXPERIMENTS = [
    {"id": "E01", "stack": ["curcubrain"], "endpoint": "gile_l", "empirical": 62.0, "dir": "+"},
    {"id": "E02", "stack": ["curcubrain", "macamides_5pct"], "endpoint": "gile_l", "empirical": 57.0, "dir": "+"},
    {"id": "E03", "stack": ["curcubrain", "transdermal_cbd"], "endpoint": "gile_l", "empirical": 45.0, "dir": "+"},
    {"id": "E04", "stack": ["curcubrain", "transdermal_cbd", "omega3_high_epa"], "endpoint": "gile_l", "empirical": 35.0, "dir": "+"},
    {"id": "E05", "stack": ["curcubrain", "macamides_5pct", "transdermal_cbd", "bromelain_quercetin", "green_tea_egcg"], "endpoint": "gile_l", "empirical": 100.0, "dir": "+"},
    {"id": "E06", "stack": ["saffron_extract"], "endpoint": "gile_l", "empirical": 62.0, "dir": "+"},
    {"id": "E07", "stack": ["htp_5", "vitamin_b6_p5p"], "endpoint": "gile_l", "empirical": 62.6, "dir": "+"},
    {"id": "E08", "stack": ["mood_probiotic"], "endpoint": "gile_l", "empirical": 21.0, "dir": "+"},
    {"id": "E09", "stack": ["omega3_high_epa"], "endpoint": "gile_l", "empirical": 27.0, "dir": "+"},
    {"id": "E10", "stack": ["l_methylfolate", "vitamin_b6_p5p"], "endpoint": "gile_l", "empirical": 23.0, "dir": "+"},
    {"id": "E11", "stack": ["pqq", "ubiquinone_coq10"], "endpoint": "gile_i", "empirical": 12.0, "dir": "+"},
    {"id": "E12", "stack": ["ketamine_troche", "lithium"], "endpoint": "gile_l", "empirical": 50.0, "dir": "+"},
]


BASE = ConsciousnessState(
    gile_g=0.42, gile_i=0.38, gile_l=0.35, gile_e=0.33,
    lcc=0.48, coherence=0.52
)
BIOMETRICS = BiometricState(
    heart_rate=72.0, rmssd=55.0, sdnn=65.0,
    alpha_power=0.48, beta_power=0.32, theta_power=0.42, gamma_power=0.22
)


def get_endpoint_change_pct(result, endpoint: str, base: ConsciousnessState) -> float:
    """Extract % change in the target GILE endpoint from a PredictionResult.
    Mirrors pharma_simulator_validation.py: gile_l_change is an absolute delta
    on the 0-1 scale; we convert to percent via (delta / base_value) × 100.
    """
    field_map = {
        'gile_l': ('gile_l_change', base.gile_l),
        'gile_g': ('gile_g_change', base.gile_g),
        'gile_i': ('gile_i_change', base.gile_i),
        'gile_e': ('gile_e_change', base.gile_e),
    }
    attr, base_val = field_map.get(endpoint, (f'{endpoint}_change', 0.5))
    delta = getattr(result, attr, 0.0)
    if base_val <= 0:
        return 0.0
    return (delta / base_val) * 100.0


def run_validation(sim: TIPharmacologicalSimulator, label: str):
    """Run all N=12 experiments through a configured simulator."""
    print(f"\n{'='*70}")
    print(f"Running: {label}")
    print(f"{'='*70}")

    results = []
    dir_correct = 0
    mag_within_2x = 0
    total_abs_dev = 0.0

    for exp in EXPERIMENTS:
        try:
            result = sim.simulate(
                supplements=exp['stack'],
                current_consciousness=deepcopy(BASE),
                current_biometrics=deepcopy(BIOMETRICS),
            )
            ti_pct = get_endpoint_change_pct(result, exp['endpoint'], BASE)
        except Exception as e:
            ti_pct = 0.0
            print(f"  {exp['id']}: ERROR {type(e).__name__}: {str(e)[:80]}")

        ti_dir = "+" if ti_pct >= 0 else "-"
        is_dir_correct = (ti_dir == exp['dir'])
        if is_dir_correct:
            dir_correct += 1

        if exp['empirical'] != 0:
            ratio = ti_pct / exp['empirical']
            abs_dev = abs(ratio - 1.0)
        else:
            ratio = float('inf')
            abs_dev = 1.0
        total_abs_dev += abs_dev

        is_mag_ok = (0.5 <= ratio <= 2.0)
        if is_mag_ok:
            mag_within_2x += 1

        d_sym = "✓" if is_dir_correct else "✗"
        m_sym = "✓" if is_mag_ok else "✗"
        print(f"  {exp['id']}: TI={ti_pct:+6.1f}% Emp={exp['empirical']:+6.1f}% Ratio={ratio:5.2f}x  Dir{d_sym} Mag{m_sym}")

        results.append({
            'id': exp['id'], 'ti_pct': ti_pct, 'empirical': exp['empirical'],
            'ratio': ratio, 'dir_correct': is_dir_correct, 'mag_ok': is_mag_ok,
            'abs_dev': abs_dev,
        })

    n = len(EXPERIMENTS)
    print(f"\n  {label} SUMMARY:")
    print(f"  Directional accuracy: {dir_correct}/{n} = {dir_correct/n*100:.1f}%")
    print(f"  Magnitude accuracy:   {mag_within_2x}/{n} = {mag_within_2x/n*100:.1f}%")
    print(f"  Total |ratio-1.0|:    {total_abs_dev:.2f}")

    return {
        'label': label,
        'dir_correct': dir_correct,
        'mag_ok': mag_within_2x,
        'total_abs_dev': total_abs_dev,
        'n': n,
        'results': results,
    }


def main():
    BRANDON_DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'

    print("Loading Brandon's actual DNA...")
    genotypes = parse_23andme(BRANDON_DNA)
    brandon_profile, evidence = build_genetic_profile_from_dna(genotypes)
    coherence = lcc_substrate_coherence(brandon_profile)
    print(f"  Loaded {len(genotypes):,} genotypes")
    print(f"  Brandon LCC substrate coherence R(A,B) = {coherence:.4f}")
    print(f"  Brandon FAAH={brandon_profile.faah_activity}, COMT={brandon_profile.comt_activity}, "
          f"CB1={brandon_profile.cb1_receptor_density:.3f}, BDNF={brandon_profile.bdnf_expression}")

    # Conventional baseline — default GeneticProfile (all activities = 1.0)
    sim_conv = TIPharmacologicalSimulator(user_id='conventional_baseline_phase4')
    sim_conv.genetic_profile = GeneticProfile()
    conv_result = run_validation(sim_conv, "BASELINE A — Conventional (default GeneticProfile)")

    # DNA-anchored — Brandon's actual DNA-derived GeneticProfile
    sim_dna = TIPharmacologicalSimulator(user_id='brandon_dna_anchored_phase4')
    sim_dna.genetic_profile = brandon_profile
    dna_result = run_validation(sim_dna, "BASELINE B — DNA-Anchored (Brandon's actual genotypes)")

    # Comparison vs pre-registered thresholds
    print(f"\n{'='*70}")
    print(f"PRE-REGISTERED FALSIFICATION COMPARISON")
    print(f"{'='*70}")

    print(f"\nPrediction 3.1 — Magnitude accuracy ≥11/12 (improvement ≥8.4pp):")
    mag_improvement = (dna_result['mag_ok'] - conv_result['mag_ok']) / conv_result['n'] * 100
    print(f"  Conventional: {conv_result['mag_ok']}/{conv_result['n']}  DNA-anchored: {dna_result['mag_ok']}/{dna_result['n']}")
    print(f"  Improvement: {mag_improvement:+.1f}pp")
    print(f"  Threshold (≥11/12): {'PASS' if dna_result['mag_ok'] >= 11 else 'FAIL'}")

    print(f"\nPrediction 3.2 — Total absolute deviation ≤5.94 (≥20% reduction):")
    dev_reduction = (conv_result['total_abs_dev'] - dna_result['total_abs_dev']) / conv_result['total_abs_dev'] * 100
    print(f"  Conventional: {conv_result['total_abs_dev']:.2f}  DNA-anchored: {dna_result['total_abs_dev']:.2f}")
    print(f"  Reduction: {dev_reduction:+.1f}%")
    print(f"  Threshold (≤5.94): {'PASS' if dna_result['total_abs_dev'] <= 5.94 else 'FAIL'}")

    print(f"\nPrediction 3.3 — Brandon-specific phenotype scaling:")
    print(f"  Brandon FAAH=CC (standard, faah_activity=1.0)")
    print(f"  → Predictions for FAAH-relevant E01-E04 should NOT be amplified beyond conventional")
    e01_04_conv = sum(r['ti_pct'] for r in conv_result['results'][:4])
    e01_04_dna = sum(r['ti_pct'] for r in dna_result['results'][:4])
    print(f"  Σ E01-E04 conventional: {e01_04_conv:+.1f}%   DNA-anchored: {e01_04_dna:+.1f}%")
    if abs(e01_04_dna - e01_04_conv) < 0.01:
        print(f"  Result: NO DIFFERENCE (Brandon's standard FAAH = canonical default)")
    else:
        delta = e01_04_dna - e01_04_conv
        print(f"  Delta: {delta:+.1f}% — DNA anchor produces measurable shift")

    print(f"\n{'='*70}")
    print(f"OVERALL VERDICT (Pre-Registered Thresholds)")
    print(f"{'='*70}")
    p31_pass = dna_result['mag_ok'] >= 11
    p32_pass = dna_result['total_abs_dev'] <= 5.94
    if p31_pass and p32_pass:
        print(f"  ✅ POSITIVE — DNA anchor adds meaningful precision; proceed to Phase 5")
    elif p31_pass or p32_pass:
        print(f"  🟡 MIXED — partial improvement; recalibration suggested before Phase 5")
    else:
        print(f"  ❌ NEGATIVE — DNA anchor adds NO improvement to Tier-A baseline")
        print(f"     Honest result: write falsification paper; do NOT proceed to Phase 5 as currently designed")
        print(f"     Possible explanations: (a) ceiling effect (baseline already at 100% directional);")
        print(f"     (b) Brandon's substrate coherence (0.847) too close to canonical to differentiate;")
        print(f"     (c) DNA anchor needs to be tested on cohort with more genotype variance, not Brandon alone")

    return conv_result, dna_result


if __name__ == '__main__':
    main()
