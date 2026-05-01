"""
Phase 4-bis Execution: Divination-Amplified vs DNA-Anchored vs Conventional
============================================================================
Three-arm head-to-head per pre-registration:
  papers/PRE_REGISTRATION_DIVINATION_AMPLIFIED_PHARMA.md (locked 2026-04-30)

Same N=12, same BASE state, same biometrics. Only difference is the simulator
configuration:
  Baseline A — Conventional: default GeneticProfile, no amplification
  Baseline B — DNA-Anchored: Brandon's DNA-derived GeneticProfile
  Baseline C — Divination-Amplified: B + 5-LCC amplifier per URB #824

Date: 2026-04-30 (DPES session)
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
from divination_amplified_pharma import (
    DivinationAmplifiedSimulator,
    compute_lcc_amplifier,
)


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
    gile_g=0.42, gile_i=0.38, gile_l=0.35, gile_e=0.33, lcc=0.48, coherence=0.52
)
BIOMETRICS = BiometricState(
    heart_rate=72.0, rmssd=55.0, sdnn=65.0,
    alpha_power=0.48, beta_power=0.32, theta_power=0.42, gamma_power=0.22
)


def get_endpoint_change_pct(result, endpoint: str, base: ConsciousnessState) -> float:
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


def run_validation(sim, label: str, capture_amp: bool = False):
    print(f"\n{'='*72}")
    print(f"Running: {label}")
    print(f"{'='*72}")
    dir_correct, mag_within_2x, total_abs_dev = 0, 0, 0.0
    amp_log, results = [], []

    for exp in EXPERIMENTS:
        result = sim.simulate(
            supplements=exp['stack'],
            current_consciousness=deepcopy(BASE),
            current_biometrics=deepcopy(BIOMETRICS),
        )
        ti_pct = get_endpoint_change_pct(result, exp['endpoint'], BASE)
        ti_dir = "+" if ti_pct >= 0 else "-"
        is_dir_correct = (ti_dir == exp['dir'])
        if is_dir_correct:
            dir_correct += 1

        ratio = ti_pct / exp['empirical'] if exp['empirical'] != 0 else float('inf')
        abs_dev = abs(ratio - 1.0) if exp['empirical'] != 0 else 1.0
        total_abs_dev += abs_dev
        is_mag_ok = (0.5 <= ratio <= 2.0)
        if is_mag_ok:
            mag_within_2x += 1

        amp = "    "
        trace_record = None
        if capture_amp and hasattr(sim, 'last_trace') and sim.last_trace:
            amp = f"×{sim.last_trace.amp_ti:.2f}"
            amp_log.append(sim.last_trace.amp_ti)
            t = sim.last_trace
            # Dominant-contributor audit: which |R_i| moved the amplifier most off 1.0
            contributions = {
                'R_intra': abs(t.R_intra - 0.5) * 0.5,
                'R_ss':    abs(t.R_ss) * 0.5,
                'R_se':    abs(t.R_se) * 0.5,
                'R_stack': abs(t.R_stack) * 0.3,
                'R_obs':   abs(t.R_obs) * 0.2,
            }
            dominant = max(contributions, key=contributions.get)
            trace_record = {
                'R_intra': t.R_intra, 'R_ss': t.R_ss, 'R_se': t.R_se,
                'R_stack': t.R_stack, 'R_obs': t.R_obs, 'amp_ti': t.amp_ti,
                'dominant': dominant, 'dominant_contribution': contributions[dominant],
            }

        d_sym = "✓" if is_dir_correct else "✗"
        m_sym = "✓" if is_mag_ok else "✗"
        print(f"  {exp['id']}: TI={ti_pct:+6.1f}% Emp={exp['empirical']:+6.1f}% Ratio={ratio:5.2f}x  Dir{d_sym} Mag{m_sym}  Amp={amp}")

        results.append({
            'id': exp['id'], 'ti_pct': ti_pct, 'empirical': exp['empirical'],
            'ratio': ratio, 'dir_correct': is_dir_correct, 'mag_ok': is_mag_ok,
            'abs_dev': abs_dev, 'amp': sim.last_trace.amp_ti if (capture_amp and sim.last_trace) else 1.0,
            'trace': trace_record,
        })

    n = len(EXPERIMENTS)
    print(f"\n  {label} SUMMARY:")
    print(f"  Directional accuracy: {dir_correct}/{n} = {dir_correct/n*100:.1f}%")
    print(f"  Magnitude accuracy:   {mag_within_2x}/{n} = {mag_within_2x/n*100:.1f}%")
    print(f"  Total |ratio-1.0|:    {total_abs_dev:.2f}")
    if capture_amp and amp_log:
        mean_amp = sum(amp_log) / len(amp_log)
        print(f"  Mean Amp_TI:          ×{mean_amp:.4f}  (range [{min(amp_log):.3f}, {max(amp_log):.3f}])")

    return {
        'label': label, 'dir_correct': dir_correct, 'mag_ok': mag_within_2x,
        'total_abs_dev': total_abs_dev, 'n': n, 'results': results,
        'mean_amp': (sum(amp_log) / len(amp_log)) if amp_log else 1.0,
    }


def main():
    BRANDON_DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'

    print("Loading Brandon's DNA...")
    genotypes = parse_23andme(BRANDON_DNA)
    brandon_profile, _ = build_genetic_profile_from_dna(genotypes)
    print(f"  Loaded {len(genotypes):,} genotypes")
    print(f"  Brandon LCC substrate coherence R(A,B) = {lcc_substrate_coherence(brandon_profile):.4f}")

    # Baseline A — Conventional
    sim_a = TIPharmacologicalSimulator(user_id='phase4bis_conventional')
    sim_a.genetic_profile = GeneticProfile()
    res_a = run_validation(sim_a, "BASELINE A — Conventional")

    # Baseline B — DNA-Anchored
    sim_b = TIPharmacologicalSimulator(user_id='phase4bis_dna_anchored')
    sim_b.genetic_profile = brandon_profile
    res_b = run_validation(sim_b, "BASELINE B — DNA-Anchored")

    # Baseline C — Divination-Amplified
    sim_c_inner = TIPharmacologicalSimulator(user_id='phase4bis_divination_amplified')
    sim_c_inner.genetic_profile = brandon_profile
    # LOCKED reproducibility: seed and today fixed to lock-date 2026-04-30.
    # This makes every rerun produce identical numbers regardless of system clock.
    LOCK_DATE = date(2026, 4, 30)
    LOCK_SEED = (LOCK_DATE - date(1970, 1, 1)).days  # 20573
    sim_c = DivinationAmplifiedSimulator(
        sim_c_inner,
        subject_name="Brandon Charles Emerick",
        observer_name="Replit Agent",
        weather=None,
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
    )
    res_c = run_validation(sim_c, "BASELINE C — Divination-Amplified (5-LCC)", capture_amp=True)

    # Pre-registered comparison
    print(f"\n{'='*72}")
    print(f"PRE-REGISTERED FALSIFICATION COMPARISON (Phase 4-bis vs Phase 4)")
    print(f"{'='*72}")

    print(f"\nP3.1 — Magnitude accuracy ≥8/12 (improvement ≥2 over B):")
    delta_31 = res_c['mag_ok'] - res_b['mag_ok']
    print(f"  Conventional A: {res_a['mag_ok']}/{res_a['n']}")
    print(f"  DNA-Anchored B: {res_b['mag_ok']}/{res_b['n']}")
    print(f"  Divination-Amplified C: {res_c['mag_ok']}/{res_c['n']}  (Δ from B: {delta_31:+d})")
    p31 = "PASS" if res_c['mag_ok'] >= 8 else ("MIXED" if delta_31 >= 1 else "FAIL")
    print(f"  Verdict: {p31}")

    print(f"\nP3.2 — Total deviation ≤4.44 (≥15% reduction vs B's 5.22):")
    print(f"  Conventional A: {res_a['total_abs_dev']:.2f}")
    print(f"  DNA-Anchored B: {res_b['total_abs_dev']:.2f}")
    print(f"  Divination-Amplified C: {res_c['total_abs_dev']:.2f}")
    if res_b['total_abs_dev'] > 0:
        reduction = (res_b['total_abs_dev'] - res_c['total_abs_dev']) / res_b['total_abs_dev'] * 100
        print(f"  Reduction C vs B: {reduction:+.1f}%")
    else:
        reduction = 0.0
    if res_c['total_abs_dev'] <= 4.44:
        p32 = "PASS"
    elif reduction >= 5.0:
        p32 = "MIXED"
    else:
        p32 = "FAIL"
    print(f"  Verdict: {p32}")

    print(f"\nP3.3 — Mean Amp_TI in [0.8, 1.6]:")
    print(f"  Mean Amp_TI: ×{res_c['mean_amp']:.4f}")
    p33 = "PASS" if 0.8 <= res_c['mean_amp'] <= 1.6 else "FAIL"
    print(f"  Verdict: {p33}")

    print(f"\nP3.4 — Directional accuracy maintained at 12/12 (any regression = AUTO FAIL):")
    print(f"  C directional: {res_c['dir_correct']}/{res_c['n']}")
    p34 = "PASS" if res_c['dir_correct'] == 12 else "AUTO-FAIL"
    print(f"  Verdict: {p34}")

    print(f"\nP3.5 — LCC trace causal-attribution sanity (per-experiment audit):")
    improvements = []
    for rb, rc in zip(res_b['results'], res_c['results']):
        delta_dev = rb['abs_dev'] - rc['abs_dev']  # positive = improvement
        if delta_dev > 0.01 and rc.get('trace'):
            improvements.append((rc['id'], delta_dev, rc['amp'], rc['trace']))
    if improvements:
        for exp_id, delta, amp, tr in improvements:
            print(f"  {exp_id}: improved {delta:+.3f}  amp ×{amp:.3f}  dominant={tr['dominant']} (contrib={tr['dominant_contribution']:.3f})")
        p35 = "PASS"
    else:
        print(f"  No experiment improved by >0.01 in C vs B. P3.5 FAIL.")
        p35 = "FAIL"

    # Overall gate
    print(f"\n{'='*72}")
    print(f"OVERALL VERDICT (Phase 5 Gate)")
    print(f"{'='*72}")
    passes = sum(1 for v in [p31, p32, p33, p34, p35] if v == "PASS")
    if p34 == "AUTO-FAIL":
        verdict = "🔴 RED — directional regression broke the baseline; Phase 5 STAYS GATED"
    elif p31 == "PASS" and p32 == "PASS" and p33 == "PASS" and p34 == "PASS" and p35 == "PASS":
        verdict = "🟢 GREEN — all gates passed; Phase 5 PROCEEDS with divination-amplified pathway"
    elif p34 == "PASS" and (p31 == "PASS" or p32 == "PASS") and p33 == "PASS":
        verdict = "🟡 YELLOW — partial; redesign on held-out cohort with weight learning before Phase 5"
    else:
        verdict = "🔴 RED — pre-registered gates not met; Phase 5 STAYS GATED, document falsification"
    print(f"  P3.1 Magnitude: {p31}")
    print(f"  P3.2 Deviation: {p32}")
    print(f"  P3.3 Amp range: {p33}")
    print(f"  P3.4 Directional: {p34}")
    print(f"  P3.5 Attribution: {p35}")
    print(f"  Passes: {passes}/5")
    print(f"  {verdict}")

    return res_a, res_b, res_c, {'p31': p31, 'p32': p32, 'p33': p33, 'p34': p34, 'p35': p35, 'verdict': verdict}


if __name__ == '__main__':
    main()
