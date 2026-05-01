"""
Phase H-1 FULL-4-of-5 — execute URB #826 Phase H-1 with all four
genome-derivable + sleep-efficiency components REAL, plus Oura overnight
HRV as the daytime-HRV substitute.

Pre-registered in AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.4.
Outcome will be written to §8.7 (FROZEN after run).

Locked seed: LOCK_DATE=2026-04-30 (matches §8.6 / §10.3 for direct
comparability of dev values).

Cost: $0 (all data already in repo or already-paid integrations).
"""

from __future__ import annotations
import os
import sys
import statistics
from datetime import date

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from oura_ring_integration import OuraRingIntegration
from divination_amplified_pharma import (
    DivinationAmplifiedSimulator,
    compute_lcc_amplifier,
)
from ti_pharmacological_simulator import TIPharmacologicalSimulator, GeneticProfile
from dna_anchored_lcc_module import parse_23andme, build_genetic_profile_from_dna
from phase_4_bis_divination_amplified_validation import run_validation
from phase_h1_5_genome_derivation import derive_all_three


LOCK_DATE = date(2026, 4, 30)
LOCK_SEED = (LOCK_DATE - date(1970, 1, 1)).days
BRANDON_DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'

PRED_104 = {
    'r_intra_em': 0.7001,
    'dev_point': 4.85,
    'dev_band_lo': 4.78,
    'dev_band_hi': 4.92,
    'direction_vs_86': 'strictly_less_than_4.9285',
    'shift_band_lo': 0.00,
    'shift_band_hi': 0.16,
    'lock_date': '2026-05-01',
    'source': 'AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.4',
}


def main():
    print("=" * 76)
    print("PHASE H-1 FULL-4-of-5 — Phase H-1.5 derivations + Oura, $0 morning")
    print("=" * 76)
    print(f"Pre-registered (locked {PRED_104['lock_date']}, BEFORE running):")
    print(f"  R_intra_em (computed pre-lock): {PRED_104['r_intra_em']:.4f}")
    print(f"  dev_em_full4of5 point: {PRED_104['dev_point']:.2f}, "
          f"band [{PRED_104['dev_band_lo']:.2f}, {PRED_104['dev_band_hi']:.2f}]")
    print(f"  Direction vs §8.6 (4.9285): {PRED_104['direction_vs_86']}")
    print(f"  Shift band: [{PRED_104['shift_band_lo']:.2f}, "
          f"{PRED_104['shift_band_hi']:.2f}]")
    print(f"  Source: {PRED_104['source']}")
    print()

    # ────────────────────────────────────────────────────────────────────
    # STEP 1: Compute the 5 R_intra_em components (4 real + 1 substitute)
    # ────────────────────────────────────────────────────────────────────
    print("─" * 76)
    print("STEP 1: Compute R_intra_em — 4 of 5 REAL (Phase H-1.5 + Oura)")
    print("─" * 76)

    print("\n  [a] Phase H-1.5 genome derivations from existing 23andMe...")
    geno_out = derive_all_three(BRANDON_DNA)
    mito = geno_out['mito_snp_score']
    tel = geno_out['telomere_proxy']
    cpg = geno_out['cpg_promoter_density']
    print(f"      mito_snp_score     = {mito:.4f}  ✅ REAL "
          f"(call_rate={geno_out['mito_diagnostics']['call_rate']:.4f})")
    print(f"      telomere_proxy     = {tel:.4f}  ✅ REAL "
          f"({geno_out['telomere_diagnostics']['n_snps_found']}/7 SNPs)")
    print(f"      cpg_promoter_density = {cpg:.4f}  ✅ REAL "
          f"(ratio={geno_out['cpg_diagnostics']['ratio_brandon_to_baseline']:.4f})")

    print("\n  [b] Live Oura sleep + HRV (last 7 valid long-sleep nights)...")
    oura = OuraRingIntegration()
    from datetime import timedelta as _td
    _today = date.today()
    _start = (_today - _td(days=21)).isoformat()
    _end = _today.isoformat()
    sessions = oura.get_sleep_sessions(start_date=_start, end_date=_end) or []
    long_sleeps = [s for s in sessions
                   if (s.total_sleep_duration or 0) >= 4 * 3600]
    long_sleeps.sort(key=lambda s: s.day)
    last7 = long_sleeps[-7:] if len(long_sleeps) >= 7 else long_sleeps
    if not last7:
        raise RuntimeError("No Oura sleep sessions available; cannot proceed.")
    eff_vals = [s.efficiency / 100.0 for s in last7]
    hrv_vals = [s.average_hrv for s in last7
                if s.average_hrv is not None and s.average_hrv > 0]
    sleep_eff_7day = statistics.mean(eff_vals)
    hrv_mean = statistics.mean(hrv_vals)
    # HRV normalization: SAME as §8.6 phase_h1_partial.py — min(hrv, 100) / 100
    # (preserved exactly to keep §10.4 pre-registration honest)
    hrv_norm_per_night = [min(v, 100.0) / 100.0 for v in hrv_vals]
    hrv_norm = statistics.mean(hrv_norm_per_night)
    print(f"      hrv_coherence_7day  = {hrv_norm:.4f}  ✅ REAL "
          f"(Oura overnight HRV substitute, raw mean {hrv_mean:.2f} ms)")
    print(f"      sleep_efficiency_7day = {sleep_eff_7day:.4f}  ✅ REAL "
          f"(raw mean {sleep_eff_7day*100:.2f}%)")

    components = [mito, tel, cpg, hrv_norm, sleep_eff_7day]
    r_intra_em = sum(components) / len(components)
    print(f"\n  [c] R_intra_em (mean of 5) = {r_intra_em:.4f}")
    print(f"      §10.4 pre-registered value: {PRED_104['r_intra_em']:.4f}")
    delta_r = abs(r_intra_em - PRED_104['r_intra_em'])
    print(f"      |actual − pre-reg| = {delta_r:.6f}")
    if delta_r > 0.001:
        print("      ❌ R_intra_em differs from pre-reg by >0.001 — Oura "
              "window has drifted or chip parser changed.")
        print("      Per §8.7.a corrigendum, this run is INVALID — refusing "
              "to write verdict.")
        print("      Either (a) re-lock §10.5 with new R_intra_em, or "
              "(b) restore Oura window to 2026-04-21..2026-04-28 / "
              "verify Phase H-1.5 derivations.")
        sys.exit(2)
    else:
        print("      ✅ R_intra_em matches pre-reg to 3 decimal places.")

    # ────────────────────────────────────────────────────────────────────
    # STEP 2: Run Phase 4-bis with R_intra_em SUBSTITUTED
    # ────────────────────────────────────────────────────────────────────
    print()
    print("─" * 76)
    print("STEP 2: Run Phase 4-bis with R_intra_em substituted")
    print("─" * 76)

    print("\n  Loading Brandon's GeneticProfile (sequence-derived, for "
          "amplifier substrate context)...")
    genotypes = parse_23andme(BRANDON_DNA)
    brandon_profile, _ = build_genetic_profile_from_dna(genotypes)
    print(f"  Loaded {len(genotypes):,} genotypes")

    sim_inner = TIPharmacologicalSimulator(user_id='h1_full4of5')
    sim_inner.genetic_profile = brandon_profile
    sim = DivinationAmplifiedSimulator(
        sim_inner,
        subject_name="Brandon Charles Emerick",
        observer_name="Replit Agent",
        weather=None,
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
        mode="R_intra_em_substituted",
        r_intra_em_override=r_intra_em,
    )
    res = run_validation(
        sim,
        "ARM H-1 FULL-4-of-5 — R_intra_em substituted (4 real + Oura HRV)",
        capture_amp=True,
    )

    dev_em_full = res['total_abs_dev']
    shift_vs_passthrough = abs(dev_em_full - 4.7719)
    direction_vs_86 = dev_em_full < 4.9285

    print()
    print(f"  dev_em_full4of5 = {dev_em_full:.4f}")
    print(f"  shift vs §8.4 passthrough (4.7719) = {shift_vs_passthrough:.4f}")
    print(f"  direction vs §8.6 (4.9285): "
          f"{'LESS ✅' if direction_vs_86 else 'NOT-LESS ❌'} "
          f"(actual − §8.6 = {dev_em_full - 4.9285:+.4f})")

    # ────────────────────────────────────────────────────────────────────
    # STEP 3: §10.4 Verdict
    # ────────────────────────────────────────────────────────────────────
    print()
    print("=" * 76)
    print("§10.4 VERDICT")
    print("=" * 76)

    in_dev_band = PRED_104['dev_band_lo'] <= dev_em_full <= PRED_104['dev_band_hi']
    in_shift_band = PRED_104['shift_band_lo'] <= shift_vs_passthrough \
        <= PRED_104['shift_band_hi']
    less_than_86 = direction_vs_86

    print(f"  dev in §10.4 band [{PRED_104['dev_band_lo']:.2f}, "
          f"{PRED_104['dev_band_hi']:.2f}]:    "
          f"{'✅ YES' if in_dev_band else '❌ NO'}")
    print(f"  Direction strictly < §8.6 (4.9285):                "
          f"{'✅ YES' if less_than_86 else '❌ NO'}")
    print(f"  Shift in §10.4 band [{PRED_104['shift_band_lo']:.2f}, "
          f"{PRED_104['shift_band_hi']:.2f}]:    "
          f"{'✅ YES' if in_shift_band else '❌ NO'}")

    print()
    if in_dev_band and less_than_86 and in_shift_band:
        print("  ✅ ALL THREE §10.4 CRITERIA HIT.")
        print("     Architecture monotonicity confirmed end-to-end with 4-of-5 "
              "real components.")
        print("     Phase H-1 pipeline VALIDATED for forward Phase B (weight "
              "learning).")
        print()
        print("     Honest scope reminder: this is deterministic architectural "
              "verification,")
        print("     NOT a Bayesian update on URB #826 truth. The biophoton/EM-"
              "DNA hypothesis")
        print("     itself is unfalsifiable at N=1 with proxy components; "
              "needs §5.1/§5.2")
        print("     differential cross-subject data.")
    elif in_dev_band and (not less_than_86 or not in_shift_band):
        print("  ⚠️  PARTIAL PASS — dev in band but direction/distance failed.")
        print("     Investigate why simulator deviates from architect's "
              "deterministic sweep.")
    else:
        print("  ❌ DEV OUTSIDE BAND — architecture has a bug OR Phase H-1.5 "
              "derivation values")
        print("     produce unexpected interaction with the amp_ti formula. "
              "Block full H-1")
        print("     until diagnosed. Compare to §8.6 architect sweep "
              "interpolation.")

    # ────────────────────────────────────────────────────────────────────
    # STEP 4: What is unblocked / still-blocked
    # ────────────────────────────────────────────────────────────────────
    print()
    print("─" * 76)
    print("FORWARD PATH AT $0")
    print("─" * 76)
    print("  ✅ Genome derivations: working from existing 23andMe file")
    print("  ✅ Oura sleep + HRV: live, $0")
    print("  ⚠️  Daytime HRV (Pulsoid premium / Polar H10): substituted by "
          "Oura overnight HRV")
    print()
    print("  Next blocker: w_em learning. Phase B (URB #826 §6.2) needs:")
    print("    - Multiple subjects (N≥10) OR multiple time-points for Brandon")
    print("    - Empirical outcome data per subject/time-point")
    print("    - Iterative weight optimization (gradient descent on dev)")
    print()
    print("  At $0/N=1 today, this is the maximum achievable Phase H-1 result.")

    # Return for programmatic inspection
    return {
        'r_intra_em': r_intra_em,
        'r_intra_em_components': {
            'mito_snp_score': mito,
            'telomere_proxy': tel,
            'cpg_promoter_density': cpg,
            'hrv_coherence_7day': hrv_norm,
            'sleep_efficiency_7day': sleep_eff_7day,
        },
        'dev_em_full4of5': dev_em_full,
        'shift_vs_passthrough': shift_vs_passthrough,
        'direction_less_than_86': direction_vs_86,
        'in_dev_band': in_dev_band,
        'in_shift_band': in_shift_band,
        'all_pass': in_dev_band and less_than_86 and in_shift_band,
    }


if __name__ == '__main__':
    main()
