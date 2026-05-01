"""
Phase H-1 PARTIAL — R_intra_em proxy stack with 2-of-5 real components ($0 tonight)
====================================================================================
Pre-registered at AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.3 (LOCKED 2026-04-30
BEFORE running).

Authority: Brandon's directive 2026-04-30 — "Let's do whatever we can to confirm
or deny H1 tonight. If we can't do anything yet, we'll pursue something else in
the meantime while we set up the full test."

URB #826 §3.1 R_intra_em proxy stack:
  R_intra_em = mean([
      mito_snp_score,          # ❌ stub @ 0.5 — needs Brandon 23andMe
      telomere_proxy,          # ❌ stub @ 0.5 — needs Brandon 23andMe
      cpg_promoter_density,    # ❌ stub @ 0.5 — needs Brandon 23andMe
      hrv_coherence_7day,      # ✅ REAL — Oura overnight HRV (Pulsoid premium $)
      sleep_efficiency_7day,   # ✅ REAL — Oura sleep efficiency
  ])

Pre-registered band: dev_em_partial = 4.85, [4.70, 5.10]
Compare to: §8.4 passthrough dev = 4.7719  (R_intra_seq mode)
            §6.1 H-1 full prediction band = [4.70, 5.05]

This is NOT full Phase H-1. It is an architecture-piping smoke test #2 with
40% real biometric data substituted into the R_intra channel.

Date: 2026-04-30 DPES window
Cost: $0
"""

import os
import sys
import statistics
from datetime import date, timedelta
from typing import Optional, List, Dict, Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from oura_ring_integration import OuraRingIntegration
from divination_amplified_pharma import (
    DivinationAmplifiedSimulator,
    compute_lcc_amplifier,
    lcc_substrate_coherence,
)
from ti_pharmacological_simulator import TIPharmacologicalSimulator, GeneticProfile
from dna_anchored_lcc_module import parse_23andme, build_genetic_profile_from_dna
# Phase 4-bis validation harness — only run_validation is exported at module scope
from phase_4_bis_divination_amplified_validation import run_validation


LOCK_DATE = date(2026, 4, 30)
LOCK_SEED = (LOCK_DATE - date(1970, 1, 1)).days
BRANDON_DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'


def load_brandon_profile():
    genotypes = parse_23andme(BRANDON_DNA)
    profile, _ = build_genetic_profile_from_dna(genotypes)
    return profile


# ────────────────────────────────────────────────────────────────────────────
# §10.3 locked prediction
# ────────────────────────────────────────────────────────────────────────────
PRED = {
    'point': 4.85,
    'band_lo': 4.70,
    'band_hi': 5.10,
    'shift_max': 0.30,
    'passthrough_baseline': 4.7719,  # §8.4
    'lock_date': '2026-04-30',
    'source': 'AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.3',
}

POPULATION_STUB = 0.5  # neutral default for genome-derived components


# ────────────────────────────────────────────────────────────────────────────
# §1 — Compute R_intra_em proxy stack from live Oura + stubs
# ────────────────────────────────────────────────────────────────────────────

def compute_r_intra_em_partial(
    days: int = 7,
) -> Dict[str, Any]:
    """
    Pull Oura sleep sessions for the last `days` valid nights, compute the
    HRV and sleep-efficiency components of R_intra_em. Stub the three
    genome-derived components at 0.5.

    Normalization conventions (locked):
      - sleep_efficiency_7day = mean(efficiency / 100) over valid nights
      - hrv_coherence_7day    = mean(min(average_hrv, 100) / 100) over valid nights
                                (caps HRV at 100 ms; Brandon's range is 60-90 ms,
                                so this is well-behaved)

    Returns a dict with R_intra_em + diagnostic component values.
    """
    oura = OuraRingIntegration()
    if not oura.is_connected:
        raise RuntimeError("Oura not connected — OURA_PERSONAL_ACCESS_TOKEN missing")

    end = date.today()
    start = end - timedelta(days=days + 7)  # buffer in case of missing nights

    sessions = oura.get_sleep_sessions(start.isoformat(), end.isoformat())
    valid_long = [
        s for s in sessions
        if s.type == 'long_sleep' and s.efficiency is not None and s.average_hrv is not None
    ]
    valid_long.sort(key=lambda s: s.day)
    last_n = valid_long[-days:]

    if len(last_n) < 4:
        raise RuntimeError(
            f"Insufficient Oura sleep data: only {len(last_n)} valid long-sleep "
            f"nights with both efficiency and HRV in last {days+7} days. "
            f"Need ≥ 4 to compute a stable 7-day mean."
        )

    eff_norm = [s.efficiency / 100.0 for s in last_n]
    hrv_norm = [min(s.average_hrv, 100.0) / 100.0 for s in last_n]

    sleep_efficiency_7day = sum(eff_norm) / len(eff_norm)
    hrv_coherence_7day = sum(hrv_norm) / len(hrv_norm)

    components = {
        'mito_snp_score':         POPULATION_STUB,
        'telomere_proxy':         POPULATION_STUB,
        'cpg_promoter_density':   POPULATION_STUB,
        'hrv_coherence_7day':     hrv_coherence_7day,
        'sleep_efficiency_7day':  sleep_efficiency_7day,
    }
    R_intra_em = sum(components.values()) / len(components)

    return {
        'R_intra_em': R_intra_em,
        'components': components,
        'oura_nights_used': [
            {'day': s.day, 'efficiency': s.efficiency, 'average_hrv': s.average_hrv}
            for s in last_n
        ],
    }


# ────────────────────────────────────────────────────────────────────────────
# §2 — Run Phase 4-bis with R_intra_em substituted
# ────────────────────────────────────────────────────────────────────────────

def main():
    print("=" * 76)
    print("PHASE H-1 PARTIAL — R_intra_em proxy stack (2-of-5 real, $0 tonight)")
    print("=" * 76)
    print(f"Pre-registered (locked {PRED['lock_date']}, BEFORE running):")
    print(f"  dev_em_partial point: {PRED['point']:.2f}, band [{PRED['band_lo']:.2f}, "
          f"{PRED['band_hi']:.2f}]")
    print(f"  shift |dev - {PRED['passthrough_baseline']:.4f}| max: {PRED['shift_max']:.2f}")
    print(f"  Source: {PRED['source']}")
    print()

    # ── Step 1: Pull live Oura data
    print("─" * 76)
    print("STEP 1: Compute R_intra_em proxy stack (live Oura + stubs)")
    print("─" * 76)
    r = compute_r_intra_em_partial(days=7)
    print(f"  Oura nights used (last 7 valid):")
    for n in r['oura_nights_used']:
        print(f"    {n['day']}  efficiency={n['efficiency']}%  HRV={n['average_hrv']} ms")
    print()
    for k, v in r['components'].items():
        flag = "✅ REAL" if k in ('hrv_coherence_7day', 'sleep_efficiency_7day') else "❌ stub"
        print(f"  {k:25s} = {v:.4f}  {flag}")
    print(f"  R_intra_em (mean of 5)  = {r['R_intra_em']:.4f}")
    print()

    # ── Step 2: Compare to R_intra_seq baseline
    print("─" * 76)
    print("STEP 2: Compare to R_intra_seq baseline (URB #824 Phase 4)")
    print("─" * 76)
    brandon_profile = load_brandon_profile()
    seq_trace = compute_lcc_amplifier(
        profile=brandon_profile,
        supplements=['curcubrain', 'transdermal_cbd'],
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
        mode='R_intra_only',
    )
    print(f"  R_intra_seq (sequence-only):  {seq_trace.R_intra:.4f}")
    print(f"  R_intra_em (partial proxy):   {r['R_intra_em']:.4f}")
    print(f"  Δ (em - seq):                 {r['R_intra_em'] - seq_trace.R_intra:+.4f}")
    print()

    # ── Step 3: Run Phase 4-bis with R_intra_em substituted
    print("─" * 76)
    print("STEP 3: Run Phase 4-bis with R_intra_em SUBSTITUTED")
    print("─" * 76)

    sim_em_inner = TIPharmacologicalSimulator(user_id='h1_partial_em_substituted')
    sim_em_inner.genetic_profile = brandon_profile
    sim_em = DivinationAmplifiedSimulator(
        sim_em_inner,
        subject_name="Brandon Charles Emerick",
        observer_name="Replit Agent",
        weather=None,
        iching_seed=LOCK_SEED,
        today=LOCK_DATE,
        mode="R_intra_em_substituted",
        r_intra_em_override=r['R_intra_em'],
    )
    res_em = run_validation(
        sim_em, "ARM H-1 PARTIAL — R_intra_em substituted (2-of-5 real)",
        capture_amp=True,
    )
    dev_em = res_em['total_abs_dev']
    print()
    print(f"  dev_em_partial = {dev_em:.4f}")
    print(f"  shift vs §8.4 passthrough ({PRED['passthrough_baseline']:.4f}) = "
          f"{abs(dev_em - PRED['passthrough_baseline']):.4f}")
    print()

    # ── Step 4: Verdict
    print("=" * 76)
    print("§10.3 PHASE H-1 PARTIAL VERDICT")
    print("=" * 76)
    in_band = PRED['band_lo'] <= dev_em <= PRED['band_hi']
    shift = abs(dev_em - PRED['passthrough_baseline'])
    shift_ok = shift <= PRED['shift_max']
    in_full_h1_band = 4.70 <= dev_em <= 5.05  # §6.1 original H-1 band

    print(f"  In §10.3 partial-H-1 band [{PRED['band_lo']:.2f}, "
          f"{PRED['band_hi']:.2f}]:           {'✅ YES' if in_band else '❌ NO'}")
    print(f"  Shift from passthrough ≤ {PRED['shift_max']:.2f}:                          "
          f"{'✅ YES' if shift_ok else '❌ NO'}  (shift = {shift:.4f})")
    print(f"  Also in §6.1 original H-1 band [4.70, 5.05]:           "
          f"{'✅ YES' if in_full_h1_band else '❌ NO'}")
    print()

    if in_band and shift_ok:
        verdict = (
            "✅ ARCHITECTURE PIPES CORRECTLY. Real partial H-1 result is within "
            "predicted band. Does NOT confirm H-1 (60% of stack is stubbed); only "
            "validates infrastructure. Forward path: collect 23andMe + Pulsoid "
            "premium (or Polar H10 hardware) to enable full H-1."
        )
    elif in_band and not shift_ok:
        verdict = (
            "⚠️  Architecture pipes but proxy substitution moves dev more than "
            "expected. Investigate amp non-linearity before treating any future "
            "full-H-1 result as valid."
        )
    elif not in_band and shift > 0.30:
        verdict = (
            "❌ OUTSIDE BAND with large shift. Architecture has bug OR proxy stack "
            "has unexpected interaction with simulator. BLOCK full H-1 until diagnosed."
        )
    else:
        verdict = (
            f"❌ OUTSIDE BAND ({dev_em:.4f}) but shift modest ({shift:.4f}). "
            f"Investigate prediction calibration before full H-1."
        )
    print(f"  {verdict}")
    print()

    # ── What needs to happen next
    print("─" * 76)
    print("WHAT WE NEED TO UNLOCK FULL H-1")
    print("─" * 76)
    print("  1. mito_snp_score:        Brandon uploads 23andMe raw data → MitoMap lookup")
    print("  2. telomere_proxy:        Brandon uploads 23andMe → open-source TL estimator")
    print("  3. cpg_promoter_density:  Brandon uploads 23andMe → UCSC Genome Browser query")
    print("  4. hrv_coherence_7day:    Pulsoid premium ($) OR Polar H10 hardware")
    print("                            (Oura overnight HRV substitute used tonight)")
    print()
    print(f"  At $0, tonight's run is the most that can be said about H-1 with N=1.")
    print(f"  Per asymmetric-standards #69, the architecture-piping check is the only")
    print(f"  honest claim available without the genome and daytime-HRV inputs.")

    return r, dev_em, in_band, shift


if __name__ == '__main__':
    main()
