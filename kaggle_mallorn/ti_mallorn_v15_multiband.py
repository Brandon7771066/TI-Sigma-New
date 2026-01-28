"""
TI MALLORN v15 - MULTI-BAND + METADATA
======================================
Key improvements:
1. 6-band (ugrizy) separate features
2. Color features (g-r, r-i, etc.)
3. Redshift (Z) and extinction (EBV) 
4. Band-specific TDE signatures
5. TI Sigma features from v12
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier, GradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v15 - MULTI-BAND + METADATA")
print("6-filter photometry + redshift + TI features")
print("="*70)

# Constants
BANDS = ['u', 'g', 'r', 'i', 'z', 'y']
TDE_POWER_LAW = -5/3
PHI = (1 + np.sqrt(5)) / 2

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

# Rename columns for consistency
if 'Time (MJD)' in train_lc.columns:
    train_lc = train_lc.rename(columns={'Time (MJD)': 'mjd'})
    test_lc = test_lc.rename(columns={'Time (MJD)': 'mjd'})

train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_band_features(band_df, band_name):
    """Extract features for a single band"""
    f = {}
    prefix = f"b_{band_name}_"
    
    flux = band_df['Flux'].values
    flux = flux[~np.isnan(flux)]
    
    if len(flux) < 3:
        return {f'{prefix}n_obs': len(flux)}
    
    f[f'{prefix}n_obs'] = len(flux)
    f[f'{prefix}flux_mean'] = np.mean(flux)
    f[f'{prefix}flux_std'] = np.std(flux)
    f[f'{prefix}flux_max'] = np.max(flux)
    f[f'{prefix}flux_min'] = np.min(flux)
    f[f'{prefix}flux_range'] = np.ptp(flux)
    f[f'{prefix}flux_skew'] = stats.skew(flux)
    
    # Peak analysis
    peak_idx = np.argmax(flux)
    f[f'{prefix}time_to_peak'] = peak_idx / len(flux) if len(flux) > 0 else 0.5
    
    # Decline rate
    if peak_idx < len(flux) - 3:
        decline = flux[peak_idx:]
        if len(decline) > 2 and decline[0] != 0:
            decline_rate = (decline[-1] - decline[0]) / (len(decline) * decline[0] + 1e-8)
            f[f'{prefix}decline_rate'] = decline_rate
        else:
            f[f'{prefix}decline_rate'] = 0
    else:
        f[f'{prefix}decline_rate'] = 0
    
    return f

def extract_features(obj_id, lc_dict, meta_row):
    """Extract all features for an object"""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id]
    f = {}
    
    # ===== METADATA FEATURES =====
    f['Z'] = meta_row['Z']
    f['Z_err'] = meta_row['Z_err']
    f['EBV'] = meta_row['EBV']
    
    # Z-derived features
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['Z_squared'] = meta_row['Z'] ** 2
    
    # ===== GLOBAL FLUX FEATURES =====
    all_flux = df['Flux'].dropna().values
    if len(all_flux) < 5:
        return None
    
    f['flux_mean'] = np.mean(all_flux)
    f['flux_std'] = np.std(all_flux)
    f['flux_median'] = np.median(all_flux)
    f['flux_skew'] = stats.skew(all_flux)
    f['flux_kurtosis'] = stats.kurtosis(all_flux)
    f['n_obs_total'] = len(all_flux)
    
    # Positive flux stats
    pos_flux = all_flux[all_flux > 0]
    if len(pos_flux) > 0:
        f['log_flux_mean'] = np.mean(np.log10(pos_flux + 1e-8))
        f['flux_positive_frac'] = len(pos_flux) / len(all_flux)
    else:
        f['log_flux_mean'] = 0
        f['flux_positive_frac'] = 0
    
    # ===== PER-BAND FEATURES =====
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) > 0:
            band_feats = extract_band_features(band_df, band)
            f.update(band_feats)
        else:
            f[f'b_{band}_n_obs'] = 0
    
    # ===== COLOR FEATURES (ratios between bands) =====
    band_means = {}
    for band in BANDS:
        key = f'b_{band}_flux_mean'
        if key in f and f.get(f'b_{band}_n_obs', 0) > 2:
            band_means[band] = f[key]
    
    # Color indices
    if 'g' in band_means and 'r' in band_means:
        f['color_g_r'] = band_means['g'] - band_means['r']
    if 'r' in band_means and 'i' in band_means:
        f['color_r_i'] = band_means['r'] - band_means['i']
    if 'i' in band_means and 'z' in band_means:
        f['color_i_z'] = band_means['i'] - band_means['z']
    if 'u' in band_means and 'g' in band_means:
        f['color_u_g'] = band_means['u'] - band_means['g']
    
    # Blue vs red ratio (TDEs are bluer)
    blue_flux = sum(band_means.get(b, 0) for b in ['u', 'g'])
    red_flux = sum(band_means.get(b, 0) for b in ['i', 'z', 'y'])
    if red_flux != 0:
        f['blue_red_ratio'] = blue_flux / (red_flux + 1e-8)
    else:
        f['blue_red_ratio'] = 1.0
    
    # ===== TI SIGMA FEATURES =====
    # GTFE
    ccc_ref = np.median(all_flux)
    divergence = np.abs(all_flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    f['gtfe_c'] = np.mean(divergence)
    
    err = df['Flux_err'].values if 'Flux_err' in df else np.ones(len(all_flux))
    err_clean = err[~np.isnan(err)]
    if len(err_clean) > 0:
        min_len = min(len(all_flux), len(err_clean))
        snr = np.abs(all_flux[:min_len]) / (err_clean[:min_len] + 1e-8)
        f['gtfe_h'] = 1 / (np.mean(snr) + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
    else:
        f['gtfe_h'] = 0.5
        f['snr_mean'] = 0
        f['snr_max'] = 0
    
    if len(all_flux) > 3:
        autocorr = np.corrcoef(all_flux[:-1], all_flux[1:])[0, 1]
        f['gtfe_t'] = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        f['gtfe_t'] = 0.5
    
    f['gtfe_total'] = f['gtfe_c'] + f['gtfe_h'] + f['gtfe_t']
    f['L'] = 1 / (f['gtfe_total'] + 1e-8)
    
    # Sacred fraction (E)
    h_mean, h_std = np.mean(all_flux), np.std(all_flux)
    sacred_low = h_mean - 2*h_std/3
    sacred_high = h_mean + h_std/3
    f['sacred_fraction'] = np.sum((all_flux >= sacred_low) & (all_flux <= sacred_high)) / len(all_flux)
    f['E'] = f['sacred_fraction']
    f['LxE'] = f['L'] * f['E']
    
    # TDE power law match
    peak_idx = np.argmax(all_flux)
    if peak_idx < len(all_flux) - 5:
        decline_flux = all_flux[peak_idx:]
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
    
    # Synergy score
    gtfe_constraint = 1 if f['gtfe_total'] < 12.0 else 0
    f['synergy_score'] = (
        gtfe_constraint * 0.3 +
        f['tde_slope_match'] * 0.3 +
        f['sacred_fraction'] * 0.2 +
        (1 if f.get('blue_red_ratio', 1) > 1.5 else 0) * 0.2
    )
    
    # Metallic mean zone
    in_zone = np.sum((all_flux >= 1.2) & (all_flux <= 1.8)) / len(all_flux)
    f['metallic_mean_zone'] = in_zone
    
    # Near phi
    f['flux_near_phi'] = np.sum(np.abs(all_flux - PHI) < 0.1) / len(all_flux)
    
    return f

# ===== EXTRACT FEATURES =====
print("\nExtracting multi-band + metadata features...")
train_features = []
train_targets = []

for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict, r)
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
    feat = extract_features(r['object_id'], test_lc_dict, r)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 2000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_test = pd.DataFrame(test_features)

# Align columns between train and test
common_cols = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common_cols].fillna(0)
X_test = X_test[common_cols].fillna(0)

print(f"\nFeatures: {len(X_train.columns)}")

# ===== TRAINING =====
print("\n" + "="*60)
print("TRAINING (3-Model Ensemble)")
print("="*60)

scaler = StandardScaler()
X_train_scaled = scaler.fit_transform(X_train)
X_test_scaled = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

# Three models
hgb = HistGradientBoostingClassifier(
    learning_rate=0.03,
    max_iter=800,
    max_depth=6,
    min_samples_leaf=15,
    l2_regularization=0.5,
    random_state=42
)

rf = RandomForestClassifier(
    n_estimators=300,
    max_depth=10,
    min_samples_leaf=5,
    max_features='sqrt',
    class_weight='balanced',
    random_state=42,
    n_jobs=-1
)

gb = GradientBoostingClassifier(
    n_estimators=300,
    learning_rate=0.03,
    max_depth=5,
    min_samples_leaf=10,
    random_state=42
)

models = [('HGB', hgb), ('RF', rf), ('GB', gb)]
oof_preds = {name: np.zeros(len(X_train)) for name, _ in models}
test_preds = {name: np.zeros(len(X_test)) for name, _ in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_train_scaled, y_train)):
    X_tr, X_val = X_train_scaled[tr_idx], X_train_scaled[val_idx]
    y_tr, y_val = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models:
        model.fit(X_tr, y_tr)
        oof_preds[name][val_idx] = model.predict_proba(X_val)[:, 1]
        test_preds[name] += model.predict_proba(X_test_scaled)[:, 1] / 5

# Find best per-model thresholds
print("\nIndividual Model Performance:")
model_scores = {}
for name in oof_preds:
    best_f1, best_thresh = 0, 0.3
    for thresh in np.linspace(0.1, 0.6, 51):
        f1 = f1_score(y_train, oof_preds[name] >= thresh)
        if f1 > best_f1:
            best_f1, best_thresh = f1, thresh
    model_scores[name] = (best_f1, best_thresh)
    preds = oof_preds[name] >= best_thresh
    prec = precision_score(y_train, preds)
    rec = recall_score(y_train, preds)
    print(f"  {name}: F1={best_f1:.4f} @ {best_thresh:.3f} (P={prec:.3f}, R={rec:.3f})")

# Weighted ensemble
total_f1 = sum(s[0] for s in model_scores.values())
weights = {name: model_scores[name][0] / total_f1 for name in model_scores}

oof_ensemble = sum(weights[name] * oof_preds[name] for name in weights)
test_ensemble = sum(weights[name] * test_preds[name] for name in weights)

# Find optimal threshold
best_f1 = 0
best_thresh = 0.3

for thresh in np.linspace(0.1, 0.5, 41):
    preds = oof_ensemble >= thresh
    f1 = f1_score(y_train, preds)
    if f1 > best_f1:
        best_f1 = f1
        best_thresh = thresh
        prec = precision_score(y_train, preds)
        rec = recall_score(y_train, preds)

print(f"\n{'='*60}")
print(f"FINAL: OOF F1 = {best_f1:.4f} @ threshold {best_thresh:.3f}")
print(f"       Precision = {prec:.4f}, Recall = {rec:.4f}")
print(f"{'='*60}")

# Generate submission
y_pred = (test_ensemble >= best_thresh).astype(int)
submission = pd.DataFrame({
    'object_id': test_ids,
    'target': y_pred
})
submission.to_csv('submission_mallorn_v15.csv', index=False)
print(f"\nPredicted TDEs: {y_pred.sum()} / {len(y_pred)}")
print(f"\n✅ Saved: submission_mallorn_v15.csv")

# ===== FEATURE IMPORTANCE =====
print("\n" + "="*60)
print("TOP FEATURES (RF Importance)")
print("="*60)

rf.fit(X_train_scaled, y_train)
importances = pd.Series(rf.feature_importances_, index=X_train.columns)
importances = importances.sort_values(ascending=False)

print("\nTop 25 features:")
for i, (feat, imp) in enumerate(importances.head(25).items()):
    print(f"  {i+1:2d}. {feat:30s} {imp:.4f}")

# ===== KEY FEATURE ANALYSIS =====
print("\n" + "="*60)
print("TDE vs NON-TDE KEY FEATURES")
print("="*60)

key_feats = ['Z', 'blue_red_ratio', 'gtfe_total', 'synergy_score', 'sacred_fraction', 
             'color_g_r', 'log_flux_mean', 'metallic_mean_zone']

for feat in key_feats:
    if feat in X_train.columns:
        tde_mean = X_train.loc[y_train == 1, feat].mean()
        non_tde_mean = X_train.loc[y_train == 0, feat].mean()
        ratio = tde_mean / (non_tde_mean + 1e-8)
        print(f"  {feat:25s}: TDE={tde_mean:.4f}, Non-TDE={non_tde_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*60)
print("TI MALLORN v15 MULTI-BAND COMPLETE")
print("="*60)
