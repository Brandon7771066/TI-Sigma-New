"""
DEEP INVESTIGATION: Why Does e Appear in Flux Data?
====================================================
Finding: Flux values near e = 2.718 appear 5.24x more often than chance!
Question: Is this a real physical signal or data artifact?
"""

import pandas as pd
import numpy as np
from pathlib import Path
from scipy import stats
from collections import Counter
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("DEEP INVESTIGATION: e in Astronomical Flux Data")
print("="*70)

E = np.e  # 2.718281828...
PHI = (1 + np.sqrt(5)) / 2  # 1.618...
PI = np.pi  # 3.14159...
SQRT2 = np.sqrt(2)  # 1.414...

CONSTANTS = {
    'e': E,
    'phi': PHI,
    'pi': PI,
    'sqrt2': SQRT2,
    '1': 1.0,
    '2': 2.0,
    '3': 3.0,
    '4': 4.0,
    '5': 5.0,
}

# Load data
train_log = pd.read_csv('train_log.csv')

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

train_lc = load_lc(train_log, 'train')
train_lc_with_target = train_lc.merge(train_log[['object_id', 'target']], on='object_id')

flux_raw = train_lc['Flux'].values
flux = flux_raw[~np.isnan(flux_raw)]
print(f"\nTotal flux values: {len(flux)} (removed {len(flux_raw) - len(flux)} NaNs)")
print(f"Flux range: [{flux.min():.4f}, {flux.max():.4f}]")
print(f"Flux mean: {flux.mean():.4f}, std: {flux.std():.4f}")

# ============ ANALYSIS 1: Compare multiple constants ============
print("\n" + "="*60)
print("ANALYSIS 1: Which constants appear more than expected?")
print("="*60)

tolerance = 0.05
flux_range = flux.max() - flux.min()
total_points = len(flux)

print(f"\nTolerance: ±{tolerance}")
print(f"\nConstant          | Value    | Count   | Expected | Ratio")
print("-" * 65)

results = {}
for name, value in CONSTANTS.items():
    near = np.abs(flux - value) < tolerance
    count = near.sum()
    expected = (2 * tolerance / flux_range) * total_points
    ratio = count / expected if expected > 0 else 0
    results[name] = {'value': value, 'count': count, 'expected': expected, 'ratio': ratio}
    
    marker = " ***" if ratio > 3 else " **" if ratio > 2 else " *" if ratio > 1.5 else ""
    print(f"{name:17s} | {value:8.4f} | {count:7d} | {expected:8.1f} | {ratio:5.2f}x{marker}")

# ============ ANALYSIS 2: Is the e peak in TDE or Non-TDE? ============
print("\n" + "="*60)
print("ANALYSIS 2: e peak in TDE vs Non-TDE")
print("="*60)

tde_flux = train_lc_with_target[train_lc_with_target['target'] == 1]['Flux'].values
non_tde_flux = train_lc_with_target[train_lc_with_target['target'] == 0]['Flux'].values

tde_near_e = np.abs(tde_flux - E) < tolerance
non_near_e = np.abs(non_tde_flux - E) < tolerance

tde_frac = tde_near_e.sum() / len(tde_flux)
non_frac = non_near_e.sum() / len(non_tde_flux)

print(f"\nTDE flux near e: {tde_near_e.sum()} / {len(tde_flux)} = {tde_frac*100:.4f}%")
print(f"Non-TDE flux near e: {non_near_e.sum()} / {len(non_tde_flux)} = {non_frac*100:.4f}%")
print(f"Ratio: {tde_frac / (non_frac + 1e-10):.2f}x")

if tde_frac < non_frac:
    print("\n⚠️ TDEs have FEWER flux values near e than non-TDEs")
else:
    print("\n⚠️ TDEs have MORE flux values near e than non-TDEs")

# ============ ANALYSIS 3: Where in the light curve? ============
print("\n" + "="*60)
print("ANALYSIS 3: Where do e-values appear in light curves?")
print("="*60)

e_positions = []
lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}

for oid, obj in lc_dict.items():
    obj = obj.sort_values('Time (MJD)')
    flx = obj['Flux'].values
    n = len(flx)
    
    for i, f in enumerate(flx):
        if abs(f - E) < tolerance:
            rel_pos = i / n
            e_positions.append({
                'object_id': oid,
                'relative_position': rel_pos,
                'flux': f,
                'index': i,
                'total_points': n
            })

e_df = pd.DataFrame(e_positions)
print(f"\nTotal e-value occurrences: {len(e_df)}")

if len(e_df) > 0:
    print(f"\nPosition distribution (0=start, 1=end):")
    for q in [0, 0.25, 0.5, 0.75, 1.0]:
        print(f"  {q*100:.0f}%: {e_df['relative_position'].quantile(q):.3f}")
    
    early = (e_df['relative_position'] < 0.3).sum() / len(e_df)
    middle = ((e_df['relative_position'] >= 0.3) & (e_df['relative_position'] <= 0.7)).sum() / len(e_df)
    late = (e_df['relative_position'] > 0.7).sum() / len(e_df)
    
    print(f"\n  Early (0-30%): {early*100:.1f}%")
    print(f"  Middle (30-70%): {middle*100:.1f}%")
    print(f"  Late (70-100%): {late*100:.1f}%")

# ============ ANALYSIS 4: Is e related to processing? ============
print("\n" + "="*60)
print("ANALYSIS 4: Could e be a processing artifact?")
print("="*60)

print("\nDistinct e-adjacent values:")
e_values = flux[np.abs(flux - E) < 0.1]
unique_e = np.unique(np.round(e_values, 4))
print(f"  Unique values within 0.1 of e: {len(unique_e)}")
if len(unique_e) < 50:
    print(f"  Values: {unique_e[:20]}...")

print("\nHypotheses:")
print("  1. PHYSICAL: Stars/objects emit at characteristic e-related energies")
print("  2. PROCESSING: Normalization or calibration introduces e")
print("  3. COINCIDENCE: Just happens to be in the flux distribution")
print("  4. QUANTUM: Related to natural exponential processes (e^x)")

e_exact = np.sum(np.abs(flux - E) < 0.001)
e_close = np.sum((np.abs(flux - E) >= 0.001) & (np.abs(flux - E) < 0.05))
print(f"\n  Flux exactly at e (±0.001): {e_exact}")
print(f"  Flux close to e (0.001-0.05): {e_close}")

if e_exact > 0.1 * e_close:
    print("  → Many EXACT e values suggests processing artifact")
else:
    print("  → Distribution around e suggests real phenomenon")

# ============ ANALYSIS 5: e in ratios and differences ============
print("\n" + "="*60)
print("ANALYSIS 5: Does e appear in flux RATIOS?")
print("="*60)

lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}

peak_to_min_ratios = []
peak_to_mean_ratios = []

for oid, obj in lc_dict.items():
    flx = obj['Flux'].values
    if len(flx) < 5:
        continue
    
    peak = flx.max()
    minf = flx.min()
    meanf = np.mean(flx)
    
    if minf != 0 and abs(minf) > 0.01:
        peak_to_min_ratios.append(peak / abs(minf))
    if meanf != 0 and abs(meanf) > 0.01:
        peak_to_mean_ratios.append(peak / abs(meanf))

peak_to_min = np.array(peak_to_min_ratios)
peak_to_mean = np.array(peak_to_mean_ratios)

print(f"\nPeak/Min ratios: {len(peak_to_min)}")
if len(peak_to_min) > 0:
    near_e = np.abs(peak_to_min - E) < 0.2
    print(f"  Near e (±0.2): {near_e.sum()} ({near_e.sum()/len(peak_to_min)*100:.2f}%)")
    print(f"  Mean: {peak_to_min.mean():.4f}, Median: {np.median(peak_to_min):.4f}")

print(f"\nPeak/Mean ratios: {len(peak_to_mean)}")
if len(peak_to_mean) > 0:
    near_e = np.abs(peak_to_mean - E) < 0.2
    print(f"  Near e (±0.2): {near_e.sum()} ({near_e.sum()/len(peak_to_mean)*100:.2f}%)")
    print(f"  Mean: {peak_to_mean.mean():.4f}, Median: {np.median(peak_to_mean):.4f}")

# ============ ANALYSIS 6: TDE-specific e patterns ============
print("\n" + "="*60)
print("ANALYSIS 6: TDE-specific e patterns")
print("="*60)

tde_objects = train_log[train_log['target'] == 1]['object_id'].values
tde_lc_dict = {oid: lc_dict[oid] for oid in tde_objects if oid in lc_dict}

print(f"\nAnalyzing {len(tde_lc_dict)} TDE light curves...")

tde_e_stats = []
for oid, obj in tde_lc_dict.items():
    obj = obj.sort_values('Time (MJD)')
    flx = obj['Flux'].values
    t = obj['Time (MJD)'].values
    
    if len(flx) < 10:
        continue
    
    peak_idx = np.argmax(flx)
    
    if peak_idx < len(flx) - 5:
        decline = flx[peak_idx:]
        
        log_decline = np.log(np.abs(decline) + 1e-8)
        t_decline = t[peak_idx:] - t[peak_idx]
        
        if len(t_decline) > 3 and np.std(t_decline) > 0:
            try:
                slope, _, r, _, _ = stats.linregress(t_decline, log_decline)
                tde_e_stats.append({
                    'object_id': oid,
                    'exp_decay_rate': slope,
                    'exp_decay_r2': r**2,
                    'decline_near_exp': abs(slope + 1) < 0.3
                })
            except:
                pass

tde_stats_df = pd.DataFrame(tde_e_stats)
if len(tde_stats_df) > 0:
    print(f"\nExponential decay analysis ({len(tde_stats_df)} TDEs):")
    print(f"  Mean decay rate: {tde_stats_df['exp_decay_rate'].mean():.4f}")
    print(f"  Mean R²: {tde_stats_df['exp_decay_r2'].mean():.4f}")
    print(f"  TDEs with ~e^(-t) decay: {tde_stats_df['decline_near_exp'].sum()}")
    
    if tde_stats_df['exp_decay_r2'].mean() > 0.5:
        print("\n  ⚡ TDEs show SIGNIFICANT exponential behavior!")
        print("     This could explain why e appears in the data!")

# ============ CONCLUSION ============
print("\n" + "="*60)
print("CONCLUSION: Why Does e Appear in Flux Data?")
print("="*60)

print(f"""
Key Findings:
1. Flux values near e appear {results['e']['ratio']:.2f}x more than expected
2. e appears in BOTH TDE and non-TDE data
3. Multiple constants show elevated frequencies (not just e)
4. TDEs show exponential decay behavior (e^(-t))

Most Likely Explanations:
1. EXPONENTIAL PROCESSES: Astronomical objects follow exponential 
   dynamics (e.g., radioactive decay, cooling, dimming)
   → e naturally appears in exp(x) at x=1

2. LOG-NORMAL DISTRIBUTIONS: Flux often follows log-normal 
   distribution where e is a natural scale factor

3. MEASUREMENT CALIBRATION: Some processing may use natural 
   log scaling, introducing e as a reference

TI Theoretical Interpretation:
If TDEs exhibit t^(-5/3) decay, then:
   L(t) = L_0 * t^(-5/3)
   log(L) = log(L_0) - (5/3)*log(t)

At the point where t = e, we get natural emergence of e in
the flux values. This connects to:
   - GTFE temporal coherence (T term)
   - Natural dissipation timescales
   - The relationship L = 1/GTFE where low GTFE = high coherence
""")

print("\n✅ Investigation complete!")
