"""
INVESTIGATION: Is 2.71 ≈ e a REAL SIGNAL?
Testing if the quantum_tde_fingerprint ratio equals Euler's number
"""

import pandas as pd
import numpy as np
from pathlib import Path
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("INVESTIGATION: 2.71 ≈ e (Euler's Number)?")
print("="*70)

E_CONSTANT = np.e  # 2.718281828...
print(f"\nEuler's number e = {E_CONSTANT:.10f}")

# Load data
train_log = pd.read_csv('train_log.csv')
print(f"\nTotal objects: {len(train_log)}")
print(f"TDEs: {train_log['target'].sum()}")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

train_lc = load_lc(train_log, 'train')
print(f"Light curve points: {len(train_lc)}")

# ============ ANALYSIS 1: Raw flux values near e ============
print("\n" + "="*60)
print("ANALYSIS 1: How often does flux ≈ e appear?")
print("="*60)

# Count flux values near e
tolerance = 0.05
near_e = np.abs(train_lc['Flux'].values - E_CONSTANT) < tolerance
count_near_e = near_e.sum()
total_points = len(train_lc)

print(f"\nFlux values within {tolerance} of e: {count_near_e} / {total_points} = {count_near_e/total_points*100:.4f}%")

# Expected by random chance (assuming uniform distribution)
flux_range = train_lc['Flux'].max() - train_lc['Flux'].min()
expected_by_chance = (2 * tolerance / flux_range) * total_points
print(f"Expected by chance: ~{expected_by_chance:.0f}")
print(f"Ratio (observed/expected): {count_near_e / expected_by_chance:.2f}x")

# ============ ANALYSIS 2: TDE vs Non-TDE flux near e ============
print("\n" + "="*60)
print("ANALYSIS 2: TDE vs Non-TDE flux near e")
print("="*60)

# Merge with target
train_lc_with_target = train_lc.merge(train_log[['object_id', 'target']], on='object_id')

tde_lc = train_lc_with_target[train_lc_with_target['target'] == 1]
non_tde_lc = train_lc_with_target[train_lc_with_target['target'] == 0]

tde_near_e = (np.abs(tde_lc['Flux'].values - E_CONSTANT) < tolerance).sum()
non_tde_near_e = (np.abs(non_tde_lc['Flux'].values - E_CONSTANT) < tolerance).sum()

tde_frac = tde_near_e / len(tde_lc)
non_tde_frac = non_tde_near_e / len(non_tde_lc)

print(f"\nTDE flux near e: {tde_near_e} / {len(tde_lc)} = {tde_frac*100:.4f}%")
print(f"Non-TDE flux near e: {non_tde_near_e} / {len(non_tde_lc)} = {non_tde_frac*100:.4f}%")
print(f"Ratio (TDE/Non-TDE): {tde_frac / (non_tde_frac + 1e-10):.2f}x")

# ============ ANALYSIS 3: Quantum TDE Fingerprint ============
print("\n" + "="*60)
print("ANALYSIS 3: Quantum TDE Fingerprint = 2.71?")
print("="*60)

def compute_quantum_fingerprint(flux, times):
    """Compute the quantum TDE fingerprint"""
    if len(flux) < 5:
        return 0
    
    peak_idx = np.argmax(flux)
    
    # Rise-decline asymmetry
    if peak_idx > 2 and peak_idx < len(flux) - 3:
        rise = flux[:peak_idx]
        decline = flux[peak_idx:]
        
        # LCC resonance between rise and reversed decline
        if len(rise) > 2 and len(decline) > 2:
            min_len = min(len(rise), len(decline))
            rise_norm = rise[-min_len:]
            decline_norm = decline[:min_len][::-1]
            
            if np.std(rise_norm) > 0 and np.std(decline_norm) > 0:
                lcc = np.corrcoef(rise_norm, decline_norm)[0, 1]
                if np.isnan(lcc):
                    lcc = 0
            else:
                lcc = 0
        else:
            lcc = 0
        
        # Power-law slope match
        if len(decline) > 4:
            rel_t = times[peak_idx:] - times[peak_idx] + 1
            log_t = np.log(rel_t[:len(decline)])
            log_f = np.log(np.abs(decline) + 1e-8)
            
            try:
                slope, _, r, _, _ = stats.linregress(log_t, log_f)
                tde_match = 1 / (1 + np.abs(slope - (-5/3)))
            except:
                tde_match = 0
        else:
            tde_match = 0
        
        # Rate asymmetry
        rise_rate = (flux[peak_idx] - flux[0]) / (times[peak_idx] - times[0] + 1e-8)
        decline_rate = (flux[-1] - flux[peak_idx]) / (times[-1] - times[peak_idx] + 1e-8)
        rate_asym = np.abs(rise_rate) / (np.abs(decline_rate) + 1e-8)
        
        fingerprint = lcc * tde_match * np.log1p(rate_asym)
        return fingerprint
    
    return 0

# Compute for all objects
lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}

fingerprints = []
for _, row in train_log.iterrows():
    oid = row['object_id']
    target = row['target']
    
    if oid in lc_dict:
        obj = lc_dict[oid].sort_values('Time (MJD)')
        fp = compute_quantum_fingerprint(obj['Flux'].values, obj['Time (MJD)'].values)
        fingerprints.append({'object_id': oid, 'target': target, 'fingerprint': fp})

fp_df = pd.DataFrame(fingerprints)

tde_fp = fp_df[fp_df['target'] == 1]['fingerprint']
non_tde_fp = fp_df[fp_df['target'] == 0]['fingerprint']

tde_mean = tde_fp.mean()
non_tde_mean = non_tde_fp.mean()
ratio = tde_mean / (non_tde_mean + 1e-10)

print(f"\nQuantum TDE Fingerprint:")
print(f"  TDE mean: {tde_mean:.4f}")
print(f"  Non-TDE mean: {non_tde_mean:.4f}")
print(f"  Ratio: {ratio:.4f}")
print(f"  Euler's e: {E_CONSTANT:.4f}")
print(f"  Difference from e: {abs(ratio - E_CONSTANT):.4f} ({abs(ratio - E_CONSTANT)/E_CONSTANT*100:.2f}%)")

# Statistical test
if abs(ratio - E_CONSTANT) / E_CONSTANT < 0.05:
    print(f"\n  ⚠️ RATIO IS WITHIN 5% OF EULER'S NUMBER e!")

# ============ ANALYSIS 4: Other e-related patterns ============
print("\n" + "="*60)
print("ANALYSIS 4: Searching for e in other TI features")
print("="*60)

# Compute various TDE statistics
tde_stats = []
for oid in train_log[train_log['target'] == 1]['object_id']:
    if oid in lc_dict:
        obj = lc_dict[oid].sort_values('Time (MJD)')
        flux = obj['Flux'].values
        
        if len(flux) > 5:
            peak_idx = np.argmax(flux)
            
            # Various ratios
            rise_time = peak_idx
            decline_time = len(flux) - peak_idx
            
            if decline_time > 0:
                time_ratio = rise_time / decline_time
                tde_stats.append({
                    'time_ratio': time_ratio,
                    'peak_to_mean': flux[peak_idx] / (np.mean(flux) + 1e-8),
                    'std_to_mean': np.std(flux) / (np.mean(np.abs(flux)) + 1e-8),
                })

stats_df = pd.DataFrame(tde_stats)

print("\nTDE Statistics (searching for e):")
for col in stats_df.columns:
    mean = stats_df[col].mean()
    median = stats_df[col].median()
    print(f"  {col}: mean={mean:.4f}, median={median:.4f}")
    
    if abs(mean - E_CONSTANT) < 0.3:
        print(f"    ⚠️ Close to e! Diff = {abs(mean - E_CONSTANT):.4f}")
    if abs(median - E_CONSTANT) < 0.3:
        print(f"    ⚠️ Median close to e! Diff = {abs(median - E_CONSTANT):.4f}")

# ============ CONCLUSION ============
print("\n" + "="*60)
print("CONCLUSION")
print("="*60)

print(f"""
Key Findings:
1. Quantum TDE Fingerprint ratio: {ratio:.4f}
2. Euler's e: {E_CONSTANT:.4f}
3. Difference: {abs(ratio - E_CONSTANT):.4f} ({abs(ratio - E_CONSTANT)/E_CONSTANT*100:.2f}%)

Interpretation:
- If ratio ≈ e with <5% error: Strong evidence for fundamental connection
- If ratio ≈ e with 5-15% error: Suggestive but not conclusive
- If ratio differs by >15%: Likely coincidence

Theoretical Significance:
If the TDE/Non-TDE fingerprint ratio equals e, this could mean:
1. TDEs exhibit natural exponential dynamics (e appears in exp decay)
2. The GTFE framework has deeper mathematical structure
3. L = 1/GTFE maps to e through the relationship L × E = e^(-1)?
""")
