"""
TI MALLORN v14 - OPTIMIZED SYNTHESIS
=====================================
Best features from v12 + v13, optimized for F1:

Key findings integrated:
- E (Existence) = #1 feature from v13
- sacred_fraction = consistent top performer
- synergy_score = #2 in v12
- flux_near_phi = sacred constant proximity
- tozzi_dim_6 = first harmonic (fundamental frequency)
- gtfe_total ratio 0.48 = strong TDE signal

Strategy: Use v12 base + selected v13 enhancements + feature selection
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier
from sklearn.feature_selection import SelectFromModel
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.fft import fft
import sys
sys.path.append('..')
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v14 - OPTIMIZED SYNTHESIS")
print("Best of v12 + v13 with Feature Selection")
print("="*70)

# TI Constants
LCC_042 = 0.42
LCC_060 = 0.60
GTFE_TDE_THRESHOLD = 12.0
TDE_POWER_LAW = -5/3

E_CONSTANT = np.e
PHI = (1 + np.sqrt(5)) / 2
PI = np.pi
SQRT2 = np.sqrt(2)

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Training: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

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
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def create_tde_template(n_points=100, t_peak=20):
    t = np.linspace(0, 100, n_points)
    flux = np.zeros(n_points)
    peak_idx = int(t_peak / 100 * n_points)
    for i in range(n_points):
        if i <= peak_idx:
            flux[i] = (i / peak_idx) ** 2
        else:
            rel_t = (i - peak_idx) / (n_points - peak_idx) * 80 + 1
            flux[i] = rel_t ** (-5/3)
    return flux

TDE_TEMPLATE = create_tde_template()

def extract_features(obj_id, lc_dict):
    """Extract optimized feature set"""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id]
    flux_raw = df['Flux'].values
    flux = flux_raw[~np.isnan(flux_raw)]
    
    err = df['Flux_err'].values if 'Flux_err' in df else np.ones(len(flux_raw))
    times = df['mjd'].values if 'mjd' in df else np.arange(len(flux_raw))
    
    if len(flux) < 5:
        return None
    
    f = {}
    
    # ===== GTFE (proven ratio 0.48) =====
    ccc_ref = np.median(flux)
    divergence = np.abs(flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    f['gtfe_c'] = np.mean(divergence)
    
    err_clean = err[~np.isnan(err)]
    if len(err_clean) > 0:
        min_len = min(len(flux), len(err_clean))
        snr = np.abs(flux[:min_len]) / (err_clean[:min_len] + 1e-8)
        f['gtfe_h'] = 1 / (np.mean(snr) + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
    else:
        f['gtfe_h'] = 0.5
        f['snr_mean'] = 0
        f['snr_max'] = 0
    
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        f['gtfe_t'] = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        f['gtfe_t'] = 0.5
    
    f['gtfe_total'] = f['gtfe_c'] + f['gtfe_h'] + f['gtfe_t']
    f['gtfe_passes_constraint'] = 1 if f['gtfe_total'] < GTFE_TDE_THRESHOLD else 0
    
    # L = 1/GTFE (proven theory)
    f['L'] = 1 / (f['gtfe_total'] + 1e-8)
    
    # ===== SACRED FRACTION (consistent top performer) =====
    h_mean, h_std = np.mean(flux), np.std(flux)
    sacred_low = h_mean - 2*h_std/3
    sacred_high = h_mean + h_std/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / len(flux)
    
    # E = Existence = sacred_fraction (v13 #1 feature!)
    f['E'] = f['sacred_fraction']
    f['LxE'] = f['L'] * f['E']
    
    # ===== SACRED CONSTANTS (flux_near_phi = v13 #5) =====
    tol = 0.1
    f['flux_near_e'] = np.sum(np.abs(flux - E_CONSTANT) < tol) / len(flux)
    f['flux_near_phi'] = np.sum(np.abs(flux - PHI) < tol) / len(flux)
    f['flux_near_pi'] = np.sum(np.abs(flux - PI) < tol) / len(flux)
    f['flux_near_sqrt2'] = np.sum(np.abs(flux - SQRT2) < tol) / len(flux)
    f['sacred_proximity'] = f['flux_near_e'] + f['flux_near_phi'] + f['flux_near_pi'] + f['flux_near_sqrt2']
    
    # ===== TOZZI HARMONICS (tozzi_dim_6 = v13 #6) =====
    fft_vals = np.abs(fft(flux))[:len(flux)//2]
    n_harmonics = min(4, len(fft_vals))  # Only first 4 harmonics
    harmonics = np.zeros(4)
    harmonics[:n_harmonics] = fft_vals[:n_harmonics]
    harmonics = harmonics / (np.sum(harmonics) + 1e-8)
    
    for i in range(4):
        f[f'tozzi_harmonic_{i}'] = harmonics[i]
    f['tozzi_toroidal'] = np.sum(harmonics[:3]**2)
    
    # ===== LCC TEMPLATE MATCHING =====
    flux_norm = (flux - np.mean(flux)) / (np.std(flux) + 1e-8)
    template_resized = np.interp(
        np.linspace(0, 1, len(flux)),
        np.linspace(0, 1, len(TDE_TEMPLATE)),
        TDE_TEMPLATE
    )
    template_norm = (template_resized - np.mean(template_resized)) / (np.std(template_resized) + 1e-8)
    corr = np.corrcoef(flux_norm, template_norm)[0, 1]
    f['lcc_template_resonance'] = corr if not np.isnan(corr) else 0
    f['lcc_passes_threshold'] = 1 if f['lcc_template_resonance'] >= LCC_060 else 0
    
    # ===== TDE POWER LAW =====
    peak_idx = np.argmax(flux)
    if peak_idx < len(flux) - 5:
        decline_flux = flux[peak_idx:]
        decline_times = np.arange(1, len(decline_flux) + 1)
        positive_decline = decline_flux[decline_flux > 0]
        positive_times = decline_times[:len(positive_decline)]
        
        if len(positive_decline) > 3:
            log_flux = np.log(positive_decline)
            log_times = np.log(positive_times)
            slope, intercept, r, p, se = stats.linregress(log_times, log_flux)
            f['decline_power_slope'] = slope
            f['decline_power_r2'] = r**2
            f['tde_slope_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
        else:
            f['decline_power_slope'] = 0
            f['decline_power_r2'] = 0
            f['tde_slope_match'] = 0
    else:
        f['decline_power_slope'] = 0
        f['decline_power_r2'] = 0
        f['tde_slope_match'] = 0
    
    # ===== TRADITIONAL (always useful) =====
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_skew'] = stats.skew(flux)
    
    times_clean = times[~np.isnan(times)]
    f['duration'] = np.ptp(times_clean) if len(times_clean) > 1 else 0
    f['n_obs'] = len(flux)
    
    positive_flux = flux[flux > 0]
    f['log_flux_mean'] = np.mean(np.log10(positive_flux + 1e-8)) if len(positive_flux) > 0 else 0
    
    f['time_to_peak'] = peak_idx / len(flux)
    
    if peak_idx > 0 and peak_idx < len(flux) - 1:
        rise_rate = (flux[peak_idx] - flux[0]) / (peak_idx + 1)
        decline_rate = (flux[peak_idx] - flux[-1]) / (len(flux) - peak_idx)
        f['rate_asymmetry'] = rise_rate / (decline_rate + 1e-8)
    else:
        f['rate_asymmetry'] = 1
    
    # ===== ENTROPY =====
    if np.max(flux) - np.min(flux) > 0:
        probs = np.histogram(flux, bins=10, density=True)[0]
        probs = probs[probs > 0]
        f['gile_entropy'] = -np.sum(probs * np.log2(probs + 1e-10)) / np.log2(10)
    else:
        f['gile_entropy'] = 0
    
    # ===== SYNERGY SCORES (v12 #2) =====
    f['gtfe_lcc_synergy'] = f['gtfe_passes_constraint'] * f['lcc_passes_threshold']
    
    f['quantum_tde_fingerprint'] = (
        f['tde_slope_match'] * 
        np.log1p(f.get('rate_asymmetry', 1)) *
        (1 + f['lcc_template_resonance'])
    )
    
    f['synergy_score'] = (
        f['gtfe_passes_constraint'] * 0.25 +
        f['lcc_passes_threshold'] * 0.25 +
        f['tde_slope_match'] * 0.20 +
        f['sacred_fraction'] * 0.15 +
        f['tozzi_toroidal'] * 0.15
    )
    
    # ===== Z STATISTIC =====
    tde_mean_gtfe = 8.5  # Known TDE mean
    non_tde_mean_gtfe = 17.5
    f['Z'] = (f['gtfe_total'] - non_tde_mean_gtfe) / (non_tde_mean_gtfe - tde_mean_gtfe + 1e-8)
    
    return f

# ===== EXTRACT FEATURES =====
print("\nExtracting optimized features...")
train_features = []
train_targets = []

for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict)
    if feat is not None:
        train_features.append(feat)
        train_targets.append(r['target'])
    if (i + 1) % 1000 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

X_train = pd.DataFrame(train_features)
y_train = np.array(train_targets)

print("\nExtracting test features...")
test_features = []
test_ids = []

for i, r in test_log.iterrows():
    feat = extract_features(r['object_id'], test_lc_dict)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 2000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_test = pd.DataFrame(test_features)

print(f"\nFeatures: {len(X_train.columns)}")

# ===== TRAINING =====
print("\n" + "="*60)
print("TRAINING (HGB + RF Ensemble)")
print("="*60)

scaler = StandardScaler()
X_train_scaled = scaler.fit_transform(X_train.fillna(0))
X_test_scaled = scaler.transform(X_test.fillna(0))

# Cross-validation
cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

hgb = HistGradientBoostingClassifier(
    learning_rate=0.05,
    max_iter=500,
    max_depth=5,
    min_samples_leaf=20,
    l2_regularization=1.0,
    random_state=42
)

rf = RandomForestClassifier(
    n_estimators=200,
    max_depth=8,
    min_samples_leaf=10,
    max_features='sqrt',
    random_state=42,
    n_jobs=-1
)

oof_hgb = np.zeros(len(X_train))
oof_rf = np.zeros(len(X_train))
test_hgb = np.zeros(len(X_test))
test_rf = np.zeros(len(X_test))

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_train_scaled, y_train)):
    X_tr, X_val = X_train_scaled[tr_idx], X_train_scaled[val_idx]
    y_tr, y_val = y_train[tr_idx], y_train[val_idx]
    
    hgb.fit(X_tr, y_tr)
    oof_hgb[val_idx] = hgb.predict_proba(X_val)[:, 1]
    test_hgb += hgb.predict_proba(X_test_scaled)[:, 1] / 5
    
    rf.fit(X_tr, y_tr)
    oof_rf[val_idx] = rf.predict_proba(X_val)[:, 1]
    test_rf += rf.predict_proba(X_test_scaled)[:, 1] / 5

# Individual model scores
best_hgb_f1, best_hgb_thresh = 0, 0.3
best_rf_f1, best_rf_thresh = 0, 0.3

for thresh in np.linspace(0.2, 0.6, 41):
    hgb_f1 = f1_score(y_train, oof_hgb >= thresh)
    rf_f1 = f1_score(y_train, oof_rf >= thresh)
    if hgb_f1 > best_hgb_f1:
        best_hgb_f1, best_hgb_thresh = hgb_f1, thresh
    if rf_f1 > best_rf_f1:
        best_rf_f1, best_rf_thresh = rf_f1, thresh

print(f"\nHGB F1: {best_hgb_f1:.4f} @ {best_hgb_thresh:.3f}")
print(f"RF F1: {best_rf_f1:.4f} @ {best_rf_thresh:.3f}")

# Weighted ensemble (favor better model)
w_hgb = best_hgb_f1 / (best_hgb_f1 + best_rf_f1)
w_rf = best_rf_f1 / (best_hgb_f1 + best_rf_f1)

oof_ensemble = w_hgb * oof_hgb + w_rf * oof_rf
test_ensemble = w_hgb * test_hgb + w_rf * test_rf

# Find optimal threshold
best_f1 = 0
best_thresh = 0.3

for thresh in np.linspace(0.15, 0.55, 41):
    f1 = f1_score(y_train, oof_ensemble >= thresh)
    if f1 > best_f1:
        best_f1 = f1
        best_thresh = thresh

print(f"\n{'='*60}")
print(f"FINAL: OOF F1 = {best_f1:.4f} @ threshold {best_thresh:.3f}")
print(f"{'='*60}")

# Generate submission
y_pred = (test_ensemble >= best_thresh).astype(int)
submission = pd.DataFrame({
    'object_id': test_ids,
    'target': y_pred
})
submission.to_csv('submission_mallorn_v14.csv', index=False)
print(f"\nPredicted TDEs: {y_pred.sum()} / {len(y_pred)}")
print(f"\n✅ Saved: submission_mallorn_v14.csv")

# ===== FEATURE IMPORTANCE =====
print("\n" + "="*60)
print("TOP FEATURES (RF Importance)")
print("="*60)

rf.fit(X_train_scaled, y_train)
importances = pd.Series(rf.feature_importances_, index=X_train.columns)
importances = importances.sort_values(ascending=False)

print("\nTop 20 features:")
for i, (feat, imp) in enumerate(importances.head(20).items()):
    print(f"  {i+1:2d}. {feat:30s} {imp:.4f}")

# ===== LAYER VALIDATION =====
print("\n" + "="*60)
print("KEY FEATURES VALIDATION (TDE vs Non-TDE)")
print("="*60)

key_features = [
    'gtfe_total', 'L', 'E', 'LxE', 'sacred_fraction', 
    'synergy_score', 'quantum_tde_fingerprint',
    'flux_near_phi', 'tozzi_toroidal', 'lcc_template_resonance'
]

for feat in key_features:
    if feat in X_train.columns:
        tde_mean = X_train.loc[y_train == 1, feat].mean()
        non_tde_mean = X_train.loc[y_train == 0, feat].mean()
        ratio = tde_mean / (non_tde_mean + 1e-8)
        print(f"  {feat:30s}: TDE={tde_mean:.4f}, Non-TDE={non_tde_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*60)
print("TI MALLORN v14 OPTIMIZED COMPLETE")
print("="*60)
