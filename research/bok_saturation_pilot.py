#!/usr/bin/env python3
"""
BOK Biometric Saturation Pilot — T1-A
TI Sigma Empirical Research Program (URB #614, Prediction 10)

Usage (real Oura data):
  1. In the Oura app: Profile → Settings → Data Export → Download CSV
  2. Place the CSV file as: research/oura_export.csv
  3. Run: python3 research/bok_saturation_pilot.py --real

Usage (simulated data):
  python3 research/bok_saturation_pilot.py --demo

Required CSV columns (Oura export):
  date, average_hrv, sleep_phase_5_delta (or rem_sleep_duration),
  readiness_score, temperature_deviation

Author: TI Sigma / BlissGene Therapeutics
Date: April 7, 2026
"""

import sys
import math
import csv
from datetime import datetime, timedelta
from collections import Counter
import random


def percentile(data, p):
    """Compute p-th percentile of data."""
    sorted_d = sorted(data)
    k = (len(sorted_d) - 1) * p / 100
    f = math.floor(k)
    c = math.ceil(k)
    if f == c:
        return sorted_d[int(k)]
    return sorted_d[f] * (c - k) + sorted_d[c] * (k - f)


def run_analysis(records, label=""):
    """
    Run BOK saturation analysis on a list of records.
    Each record must have: hrv_rmssd, rem_pct, readiness_score, temp_deviation
    """
    days = len(records)
    print(f"\n{'='*60}")
    print(f"BOK BIOMETRIC SATURATION PILOT (T1-A) {label}")
    print(f"{'='*60}")
    print(f"Days analyzed: {days}")

    # Compute personal thresholds (70th percentile)
    hrv_thresh = percentile([r['hrv_rmssd'] for r in records], 70)
    rem_thresh = percentile([r['rem_pct'] for r in records], 70)
    ready_thresh = 80      # absolute threshold from protocol
    temp_thresh = 0.10     # < 0.10°C = high E-coherence

    print(f"\nPersonal thresholds:")
    print(f"  G-proxy (HRV RMSSD):    > {hrv_thresh:.1f} ms  (70th pct)")
    print(f"  I-proxy (REM sleep %):  > {rem_thresh:.1f}%  (70th pct)")
    print(f"  L-proxy (Readiness):    > {ready_thresh}")
    print(f"  E-proxy (Temp dev):     < {temp_thresh:.2f}°C")

    # Flag saturation per dimension per day
    for r in records:
        r['G_sat'] = 1 if r['hrv_rmssd'] > hrv_thresh else 0
        r['I_sat'] = 1 if r['rem_pct'] > rem_thresh else 0
        r['L_sat'] = 1 if r['readiness_score'] > ready_thresh else 0
        r['E_sat'] = 1 if r['temp_deviation'] < temp_thresh else 0
        r['bok_saturation'] = r['G_sat'] + r['I_sat'] + r['L_sat'] + r['E_sat']

    # Saturation distribution
    sat_counts = Counter(r['bok_saturation'] for r in records)

    print(f"\n{'Score':>6} | {'Count':>6} | {'Observed%':>10} | {'Expected% (ind.)':>18}")
    for score in range(5):
        count = sat_counts.get(score, 0)
        pct = count / days * 100
        expected = math.comb(4, score) * (0.30**score) * (0.70**(4-score)) * 100
        marker = " ◄" if score == 4 else ""
        print(f"{score:>6} | {count:>6} | {pct:>9.1f}% | {expected:>17.1f}%{marker}")

    # Key result: full BOK saturation
    full_sat = sat_counts.get(4, 0)
    full_sat_rate = full_sat / days
    base_rate_30 = 0.30 ** 4
    base_rate_50 = 0.50 ** 4

    print(f"\n{'='*60}")
    print(f"KEY RESULT: Full BOK Saturation (all 4 dimensions)")
    print(f"{'='*60}")
    print(f"  Observed:              {full_sat}/{days} days = {full_sat_rate*100:.2f}%")
    print(f"  Base rate (p=0.30^4):  {base_rate_30*100:.2f}%")
    print(f"  Base rate (p=0.50^4):  {base_rate_50*100:.2f}%")
    if base_rate_30 > 0:
        print(f"  Ratio vs. p=0.30:      {full_sat_rate/base_rate_30:.1f}×")

    # Chi-square test
    expected_count = base_rate_30 * days
    if expected_count > 0:
        chi2 = (full_sat - expected_count)**2 / expected_count
        print(f"  χ² vs. base rate:      {chi2:.2f}")
        if chi2 > 6.63:
            print(f"  → p < 0.01 ✅ SIGNIFICANT")
        elif chi2 > 3.84:
            print(f"  → p < 0.05 ✅ SIGNIFICANT")
        else:
            print(f"  → p > 0.05 (not yet significant; extend to ≥180 days)")
            needed = math.ceil(3.84 * base_rate_30 / ((full_sat_rate - base_rate_30)**2))
            print(f"  → Days needed for p<0.05 at current rate: ~{max(needed, days+30)}")

    # Dimension pairings
    print(f"\n{'='*60}")
    print(f"Pairwise Co-Saturation Rates (expected: ~9% if independent)")
    print(f"{'='*60}")
    pairs = [('G','I'), ('G','L'), ('G','E'), ('I','L'), ('I','E'), ('L','E')]
    for d1, d2 in pairs:
        count = sum(1 for r in records if r[f'{d1}_sat'] and r[f'{d2}_sat'])
        pct = count / days * 100
        ratio = pct / 9.0
        bar = '█' * int(ratio)
        print(f"  {d1}+{d2}: {count:>3}/{days} = {pct:>5.1f}%  ({ratio:.1f}× expected)  {bar}")

    # Triple co-saturation
    print(f"\nTriple Co-Saturation (expected: ~2.7% if independent)")
    triples = [('G','I','L'), ('G','I','E'), ('G','L','E'), ('I','L','E')]
    for d1, d2, d3 in triples:
        count = sum(1 for r in records if r[f'{d1}_sat'] and r[f'{d2}_sat'] and r[f'{d3}_sat'])
        pct = count / days * 100
        print(f"  {d1}+{d2}+{d3}: {count:>3}/{days} = {pct:>5.1f}%")

    # Spectre balance (L+E = √2)
    l_norms = [r['readiness_score'] / 100 for r in records]
    e_norms = [max(0.0, 1.0 - r['temp_deviation'] / 0.20) for r in records]
    lxe_asym = [abs(l - e) for l, e in zip(l_norms, e_norms)]
    l_plus_e = [l + e for l, e in zip(l_norms, e_norms)]

    spectre_days = sum(1 for a, m in zip(lxe_asym, l_plus_e) if a < 0.10 and m > 0.80)
    print(f"\n{'='*60}")
    print(f"Spectre Balance (L+E = √2 ≈ 1.414 condition, URB #616)")
    print(f"{'='*60}")
    print(f"  Days in spectre condition (|L-E|<0.10, L+E>0.80): {spectre_days}/{days} = {spectre_days/days*100:.1f}%")
    print(f"  Mean L×E asymmetry:  {sum(lxe_asym)/len(lxe_asym):.3f}  (target: → 0)")
    print(f"  Mean L+E magnitude:  {sum(l_plus_e)/len(l_plus_e):.3f}  (target: √2 = {math.sqrt(2):.4f})")
    print(f"  L+E magnitude deviation from √2: {abs(sum(l_plus_e)/len(l_plus_e) - math.sqrt(2)):.4f}")

    # Days with highest saturation
    best_days = sorted(records, key=lambda r: (r['bok_saturation'], r['readiness_score']), reverse=True)[:5]
    print(f"\n{'='*60}")
    print(f"Top 5 BOK-Saturation Days")
    print(f"{'='*60}")
    for r in best_days:
        print(f"  {r['date']}: BOK_sat={r['bok_saturation']}, "
              f"HRV={r['hrv_rmssd']:.1f}ms, REM={r['rem_pct']:.1f}%, "
              f"Ready={r['readiness_score']:.0f}, Temp_dev={r['temp_deviation']:.3f}°C")

    print(f"\n✅ Analysis complete.")
    return records


def load_real_oura_csv(filepath):
    """Load real Oura Ring data from CSV export."""
    records = []
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                records.append({
                    'date': row['date'],
                    'hrv_rmssd': float(row.get('average_hrv', 0) or 0),
                    'rem_pct': float(row.get('rem_sleep_percentage', row.get('sleep_phase_5_delta', 0)) or 0),
                    'readiness_score': float(row.get('readiness_score', row.get('score', 0)) or 0),
                    'temp_deviation': abs(float(row.get('temperature_deviation', 0.05) or 0.05))
                })
            except (ValueError, KeyError):
                continue
    return [r for r in records if r['hrv_rmssd'] > 0]


def generate_demo_data(n=90, seed=42):
    """Generate simulated Oura-like data for demonstration."""
    random.seed(seed)
    start = datetime(2026, 1, 7)
    records = []
    for i in range(n):
        date = (start + timedelta(days=i)).strftime('%Y-%m-%d')
        records.append({
            'date': date,
            'hrv_rmssd': max(20, random.gauss(65, 12)),
            'rem_pct': max(5, min(40, random.gauss(22, 5))),
            'readiness_score': max(50, min(100, random.gauss(78, 8))),
            'temp_deviation': abs(random.gauss(0.05, 0.08))
        })
    return records


if __name__ == '__main__':
    mode = '--demo'
    if len(sys.argv) > 1:
        mode = sys.argv[1]

    if mode == '--real':
        import os
        filepath = os.path.join(os.path.dirname(__file__), 'oura_export.csv')
        if not os.path.exists(filepath):
            print(f"Error: {filepath} not found.")
            print("Export from Oura app: Profile → Settings → Data Export → Download CSV")
            print("Place file at: research/oura_export.csv")
            sys.exit(1)
        records = load_real_oura_csv(filepath)
        run_analysis(records, label="[REAL OURA DATA]")
    else:
        records = generate_demo_data(n=90)
        run_analysis(records, label="[SIMULATED DATA — demo only]")
        print("\nNote: Simulated data uses plausible parameters for a high-alignment individual.")
        print("Run with --real flag and research/oura_export.csv for actual results.")
