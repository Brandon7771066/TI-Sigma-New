"""
TI MALLORN v4 - Maximum Performance TDE Detection
Focus on TDE-specific features + aggressive threshold tuning
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier, ExtraTreesClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.ndimage import uniform_filter1d
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN SOLVER v4 - Maximum Performance")
print("="*70)

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Training: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

# Load light curves
def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

print("Loading light curves...")
train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')

# Build lookup dictionaries for faster access
print("Building lookup tables...")
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_tde_features(object_id, lc_dict):
    """Extract TDE-optimized features"""
    if object_id not in lc_dict:
        return {}
    
    obj = lc_dict[object_id].sort_values('Time (MJD)').copy()
    
    if len(obj) < 3:
        return {}
    
    f = {}
    t = obj['Time (MJD)'].values
    flux = obj['Flux'].values
    err = obj['Flux_err'].values
    
    # === Core statistics ===
    f['n_obs'] = len(flux)
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_min'] = np.min(flux)
    f['flux_max'] = np.max(flux)
    f['flux_range'] = f['flux_max'] - f['flux_min']
    f['flux_iqr'] = np.percentile(flux, 75) - np.percentile(flux, 25)
    f['flux_mad'] = np.median(np.abs(flux - np.median(flux)))
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurt'] = stats.kurtosis(flux)
    
    # === Signal quality ===
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_90pct'] = np.percentile(snr, 90)
    
    # === Temporal ===
    f['duration'] = t.max() - t.min()
    dt = np.diff(t)
    if len(dt) > 0:
        f['cadence_mean'] = np.mean(dt)
        f['cadence_std'] = np.std(dt)
    
    # === TDE Light Curve Shape ===
    # TDEs: rapid rise (days-weeks), slow power-law decline (months)
    
    peak_idx = np.argmax(flux)
    f['peak_position'] = peak_idx / len(flux)
    f['peak_flux'] = flux[peak_idx]
    f['peak_snr'] = snr[peak_idx]
    
    # Time metrics relative to peak
    f['time_to_peak'] = t[peak_idx] - t[0]
    f['time_from_peak'] = t[-1] - t[peak_idx]
    f['peak_time_ratio'] = f['time_to_peak'] / (f['duration'] + 1e-8)
    
    # Rise phase analysis
    if peak_idx > 2:
        rise = flux[:peak_idx+1]
        rise_t = t[:peak_idx+1]
        f['rise_rate'] = (rise[-1] - rise[0]) / (rise_t[-1] - rise_t[0] + 1e-8)
        f['rise_max_rate'] = np.max(np.diff(rise) / (np.diff(rise_t) + 1e-8))
        
        # Smoothness of rise
        if len(rise) > 3:
            smooth = uniform_filter1d(rise, 3)
            f['rise_smoothness'] = 1 - np.std(rise - smooth) / (np.std(rise) + 1e-8)
    else:
        f['rise_rate'] = 0
        f['rise_max_rate'] = 0
        f['rise_smoothness'] = 0
    
    # Decline phase analysis
    if peak_idx < len(flux) - 3:
        decline = flux[peak_idx:]
        decline_t = t[peak_idx:]
        f['decline_rate'] = (decline[-1] - decline[0]) / (decline_t[-1] - decline_t[0] + 1e-8)
        
        # Power-law fit for TDE decline (f ~ t^-5/3)
        if len(decline) > 3:
            log_t = np.log(decline_t - decline_t[0] + 1)
            log_f = np.log(np.abs(decline) + 1)
            try:
                slope, _, r, _, _ = stats.linregress(log_t, log_f)
                f['decline_power_law_slope'] = slope
                f['decline_power_law_r2'] = r**2
            except:
                f['decline_power_law_slope'] = 0
                f['decline_power_law_r2'] = 0
    else:
        f['decline_rate'] = 0
        f['decline_power_law_slope'] = 0
        f['decline_power_law_r2'] = 0
    
    # Asymmetry (TDEs are highly asymmetric)
    f['rate_asymmetry'] = abs(f.get('rise_rate', 0)) / (abs(f.get('decline_rate', 1e-8)) + 1e-8)
    f['duration_asymmetry'] = f['time_to_peak'] / (f['time_from_peak'] + 1e-8)
    
    # === Variability ===
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    f['lcc_042'] = np.sum(np.abs(norm) > 0.42)
    f['lcc_085'] = np.sum(np.abs(norm) > 0.85)
    f['lcc_ratio'] = f['lcc_042'] / len(flux)
    
    # Excess variance
    f['excess_var'] = (np.var(flux) - np.mean(err**2)) / (f['flux_mean']**2 + 1e-8)
    
    # Amplitude ratio
    f['amp_ratio'] = f['flux_range'] / (f['flux_mean'] + 1e-8)
    
    # === Per-filter ===
    for filt in ['u', 'g', 'r', 'i', 'z', 'y']:
        fd = obj[obj['Filter'] == filt] if 'Filter' in obj.columns else pd.DataFrame()
        if len(fd) > 0:
            ff = fd['Flux'].values
            f[f'{filt}_n'] = len(fd)
            f[f'{filt}_mean'] = np.mean(ff)
            f[f'{filt}_std'] = np.std(ff)
            f[f'{filt}_max'] = np.max(ff)
            f[f'{filt}_range'] = np.ptp(ff)
            f[f'{filt}_frac'] = len(fd) / len(obj)
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_range'] = 0
            f[f'{filt}_frac'] = 0
    
    # Colors (TDEs are blue)
    if f.get('g_mean', 0) > 0 and f.get('r_mean', 0) > 0:
        f['g_r'] = f['g_mean'] - f['r_mean']
    else:
        f['g_r'] = 0
    
    if f.get('r_mean', 0) > 0 and f.get('i_mean', 0) > 0:
        f['r_i'] = f['r_mean'] - f['i_mean']
    else:
        f['r_i'] = 0
    
    return f

# Extract features
print("\nExtracting features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_tde_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    train_feats.append(feat)
    if (i+1) % 500 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_tde_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    test_feats.append(feat)
    if (i+1) % 1000 == 0: print(f"  Test: {i+1}/{len(test_log)}")

train_df = pd.DataFrame(train_feats)
test_df = pd.DataFrame(test_feats)

cols = [c for c in train_df.columns if c != 'object_id']
X = train_df[cols].fillna(0)
X_test = test_df[cols].fillna(0)
y = train_log['target'].values

print(f"\nFeatures: {len(cols)}")

scaler = StandardScaler()
X_s = scaler.fit_transform(X)
X_test_s = scaler.transform(X_test)

# Training
print("\n" + "="*50)
print("TRAINING (Multi-model Ensemble)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof1 = np.zeros(len(X))
oof2 = np.zeros(len(X))
oof3 = np.zeros(len(X))
test1 = np.zeros(len(X_test))
test2 = np.zeros(len(X_test))
test3 = np.zeros(len(X_test))

scores = []

for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
    Xt, Xv = X_s[ti], X_s[vi]
    yt, yv = y[ti], y[vi]
    
    # HGB 1
    m1 = HistGradientBoostingClassifier(
        max_iter=600, max_depth=9, learning_rate=0.025,
        l2_regularization=0.02, max_bins=255, min_samples_leaf=8,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.12, n_iter_no_change=50, random_state=42
    )
    m1.fit(Xt, yt)
    oof1[vi] = m1.predict_proba(Xv)[:, 1]
    test1 += m1.predict_proba(X_test_s)[:, 1] / 5
    
    # HGB 2 (different params)
    m2 = HistGradientBoostingClassifier(
        max_iter=400, max_depth=6, learning_rate=0.04,
        l2_regularization=0.05, max_bins=255, min_samples_leaf=15,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.12, n_iter_no_change=40, random_state=43
    )
    m2.fit(Xt, yt)
    oof2[vi] = m2.predict_proba(Xv)[:, 1]
    test2 += m2.predict_proba(X_test_s)[:, 1] / 5
    
    # ExtraTrees
    m3 = ExtraTreesClassifier(
        n_estimators=300, max_depth=12, min_samples_leaf=4,
        class_weight='balanced', random_state=44, n_jobs=-1
    )
    m3.fit(Xt, yt)
    oof3[vi] = m3.predict_proba(Xv)[:, 1]
    test3 += m3.predict_proba(X_test_s)[:, 1] / 5
    
    # Blend
    blend = 0.4 * oof1[vi] + 0.35 * oof2[vi] + 0.25 * oof3[vi]
    
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.05, 0.8, 0.02):
        f1 = f1_score(yv, (blend >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    scores.append(best_f1)
    print(f"Fold {fold+1}: F1={best_f1:.4f} @ thresh={best_th:.2f}")

print(f"\nCV F1: {np.mean(scores):.4f} ± {np.std(scores):.4f}")

# Final
oof_blend = 0.4 * oof1 + 0.35 * oof2 + 0.25 * oof3
test_blend = 0.4 * test1 + 0.35 * test2 + 0.25 * test3

best_f1, best_th = 0, 0.5
for th in np.arange(0.05, 0.8, 0.01):
    f1 = f1_score(y, (oof_blend >= th).astype(int), zero_division=0)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print(f"\nOptimal threshold: {best_th:.2f}")
print(f"OOF F1: {best_f1:.4f}")

pred = (test_blend >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v4.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v4.csv")
