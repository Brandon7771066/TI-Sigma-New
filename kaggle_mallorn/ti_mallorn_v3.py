"""
TI MALLORN v3 - Enhanced TDE Detection
Advanced feature engineering + ensemble
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN SOLVER v3 - Enhanced TDE Detection")
print("="*70)

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"Training: {len(train_log)} | TDE rate: {train_log['target'].mean()*100:.2f}%")

# Load all light curves
def load_all_lightcurves(log_df, lc_type='train'):
    all_lc = []
    for split in log_df['split'].unique():
        lc_file = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(lc_file).exists():
            lc = pd.read_csv(lc_file)
            all_lc.append(lc)
    return pd.concat(all_lc, ignore_index=True) if all_lc else pd.DataFrame()

print("Loading light curves...")
train_lc = load_all_lightcurves(train_log, 'train')
test_lc = load_all_lightcurves(test_log, 'test')
print(f"Train LC: {len(train_lc):,} | Test LC: {len(test_lc):,}")

# Advanced feature extraction
def extract_features_v3(object_id, lc_df):
    """Extract comprehensive features for TDE detection"""
    obj_lc = lc_df[lc_df['object_id'] == object_id].copy()
    
    if len(obj_lc) == 0:
        return {}
    
    features = {}
    
    # Sort by time
    obj_lc = obj_lc.sort_values('Time (MJD)')
    time = obj_lc['Time (MJD)'].values
    flux = obj_lc['Flux'].values
    flux_err = obj_lc['Flux_err'].values if 'Flux_err' in obj_lc.columns else np.ones(len(flux))
    
    # === Basic statistics ===
    features['n_obs'] = len(flux)
    features['flux_mean'] = np.mean(flux)
    features['flux_std'] = np.std(flux)
    features['flux_median'] = np.median(flux)
    features['flux_min'] = np.min(flux)
    features['flux_max'] = np.max(flux)
    features['flux_range'] = features['flux_max'] - features['flux_min']
    features['flux_iqr'] = np.percentile(flux, 75) - np.percentile(flux, 25)
    
    # Moments
    features['flux_skew'] = stats.skew(flux)
    features['flux_kurt'] = stats.kurtosis(flux)
    
    # === Signal quality ===
    snr = flux / (flux_err + 1e-8)
    features['snr_mean'] = np.mean(snr)
    features['snr_max'] = np.max(snr)
    features['snr_std'] = np.std(snr)
    
    # Weighted mean
    weights = 1 / (flux_err**2 + 1e-8)
    features['flux_wmean'] = np.average(flux, weights=weights)
    
    # === Temporal features ===
    features['duration'] = time.max() - time.min()
    
    if len(time) > 1:
        dt = np.diff(time)
        features['cadence_mean'] = np.mean(dt)
        features['cadence_std'] = np.std(dt)
        features['cadence_min'] = np.min(dt)
        features['cadence_max'] = np.max(dt)
    
    # === TDE signature: Light curve shape ===
    # TDEs show rapid rise, slow power-law decline
    
    peak_idx = np.argmax(flux)
    features['peak_position'] = peak_idx / len(flux)  # Early peak = TDE-like
    features['peak_flux'] = flux[peak_idx]
    features['time_to_peak'] = time[peak_idx] - time[0]
    features['time_from_peak'] = time[-1] - time[peak_idx]
    
    # Rise rate
    if peak_idx > 0:
        rise_flux = flux[:peak_idx+1]
        rise_time = time[:peak_idx+1]
        rise_dt = rise_time[-1] - rise_time[0]
        features['rise_rate'] = (rise_flux[-1] - rise_flux[0]) / (rise_dt + 1e-8)
        features['rise_duration'] = rise_dt
    else:
        features['rise_rate'] = 0
        features['rise_duration'] = 0
    
    # Decline rate
    if peak_idx < len(flux) - 1:
        decline_flux = flux[peak_idx:]
        decline_time = time[peak_idx:]
        decline_dt = decline_time[-1] - decline_time[0]
        features['decline_rate'] = (decline_flux[-1] - decline_flux[0]) / (decline_dt + 1e-8)
        features['decline_duration'] = decline_dt
    else:
        features['decline_rate'] = 0
        features['decline_duration'] = 0
    
    # Asymmetry: TDEs have rise faster than decline
    features['rise_decline_ratio'] = features['rise_duration'] / (features['decline_duration'] + 1e-8)
    features['rate_asymmetry'] = abs(features['rise_rate']) / (abs(features['decline_rate']) + 1e-8)
    
    # === Variability features ===
    # Stetson J statistic (for irregular sampling)
    if len(flux) > 2:
        residual = (flux - features['flux_mean']) / (flux_err + 1e-8)
        features['stetson_j'] = np.sum(np.sign(residual[:-1] * residual[1:]) * np.sqrt(np.abs(residual[:-1] * residual[1:])))
        
        # Excess variance
        features['excess_var'] = (np.var(flux) - np.mean(flux_err**2)) / (features['flux_mean']**2 + 1e-8)
    
    # === LCC-inspired features (TI Framework) ===
    # Threshold at 0.42 for "significant" variations
    norm_flux = (flux - np.mean(flux)) / (np.std(flux) + 1e-8)
    features['lcc_events'] = np.sum(np.abs(norm_flux) > 0.42)
    features['lcc_ratio'] = features['lcc_events'] / len(flux)
    
    # Events above 0.85 (high significance)
    features['high_sig_events'] = np.sum(np.abs(norm_flux) > 0.85)
    
    # === Per-filter features ===
    filters = ['u', 'g', 'r', 'i', 'z', 'y']
    for filt in filters:
        filt_data = obj_lc[obj_lc['Filter'] == filt] if 'Filter' in obj_lc.columns else pd.DataFrame()
        
        if len(filt_data) > 0:
            filt_flux = filt_data['Flux'].values
            features[f'{filt}_n'] = len(filt_data)
            features[f'{filt}_mean'] = np.mean(filt_flux)
            features[f'{filt}_std'] = np.std(filt_flux)
            features[f'{filt}_max'] = np.max(filt_flux)
            features[f'{filt}_range'] = np.ptp(filt_flux)
            
            # Per-filter variability
            if len(filt_flux) > 1:
                features[f'{filt}_var_ratio'] = np.std(filt_flux) / (np.mean(np.abs(filt_flux)) + 1e-8)
        else:
            features[f'{filt}_n'] = 0
            features[f'{filt}_mean'] = 0
            features[f'{filt}_std'] = 0
            features[f'{filt}_max'] = 0
            features[f'{filt}_range'] = 0
            features[f'{filt}_var_ratio'] = 0
    
    # === Color features ===
    # TDEs have characteristic blue colors
    if features.get('g_mean', 0) > 0 and features.get('r_mean', 0) > 0:
        features['g_r_color'] = features['g_mean'] - features['r_mean']
    else:
        features['g_r_color'] = 0
    
    if features.get('r_mean', 0) > 0 and features.get('i_mean', 0) > 0:
        features['r_i_color'] = features['r_mean'] - features['i_mean']
    else:
        features['r_i_color'] = 0
    
    if features.get('i_mean', 0) > 0 and features.get('z_mean', 0) > 0:
        features['i_z_color'] = features['i_mean'] - features['z_mean']
    else:
        features['i_z_color'] = 0
    
    return features

# Process all objects
print("\nExtracting features...")

train_features = []
for i, row in train_log.iterrows():
    feats = extract_features_v3(row['object_id'], train_lc)
    feats['object_id'] = row['object_id']
    feats['Z'] = row['Z'] if pd.notna(row['Z']) else 0
    feats['EBV'] = row['EBV'] if pd.notna(row['EBV']) else 0
    train_features.append(feats)
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

test_features = []
for i, row in test_log.iterrows():
    feats = extract_features_v3(row['object_id'], test_lc)
    feats['object_id'] = row['object_id']
    feats['Z'] = row['Z'] if pd.notna(row['Z']) else 0
    feats['EBV'] = row['EBV'] if pd.notna(row['EBV']) else 0
    test_features.append(feats)
    if (i + 1) % 1000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

train_df = pd.DataFrame(train_features)
test_df = pd.DataFrame(test_features)

# Prepare for training
feature_cols = [c for c in train_df.columns if c != 'object_id']
X = train_df[feature_cols].fillna(0)
X_test = test_df[feature_cols].fillna(0)
y = train_log['target'].values

print(f"\nFeatures: {len(feature_cols)}")

# Scale
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
X_test_scaled = scaler.transform(X_test)

# Training with ensemble
print("\n" + "="*50)
print("TRAINING (Ensemble)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof_hgb = np.zeros(len(X))
oof_rf = np.zeros(len(X))
test_hgb = np.zeros(len(X_test))
test_rf = np.zeros(len(X_test))

f1_scores = []

for fold, (train_idx, val_idx) in enumerate(skf.split(X_scaled, y)):
    X_tr, X_val = X_scaled[train_idx], X_scaled[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # HistGradientBoosting
    hgb = HistGradientBoostingClassifier(
        max_iter=500,
        max_depth=8,
        learning_rate=0.03,
        l2_regularization=0.03,
        max_bins=255,
        min_samples_leaf=10,
        class_weight='balanced',
        early_stopping=True,
        validation_fraction=0.15,
        n_iter_no_change=40,
        random_state=42
    )
    hgb.fit(X_tr, y_tr)
    oof_hgb[val_idx] = hgb.predict_proba(X_val)[:, 1]
    test_hgb += hgb.predict_proba(X_test_scaled)[:, 1] / 5
    
    # Random Forest
    rf = RandomForestClassifier(
        n_estimators=300,
        max_depth=10,
        min_samples_leaf=5,
        class_weight='balanced',
        random_state=42,
        n_jobs=-1
    )
    rf.fit(X_tr, y_tr)
    oof_rf[val_idx] = rf.predict_proba(X_val)[:, 1]
    test_rf += rf.predict_proba(X_test_scaled)[:, 1] / 5
    
    # Blend
    val_blend = 0.6 * oof_hgb[val_idx] + 0.4 * oof_rf[val_idx]
    
    # Find optimal threshold
    best_f1, best_thresh = 0, 0.5
    for thresh in np.arange(0.05, 0.95, 0.02):
        f1 = f1_score(y_val, (val_blend >= thresh).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_thresh = f1, thresh
    
    f1_scores.append(best_f1)
    print(f"Fold {fold+1}: F1={best_f1:.4f} @ thresh={best_thresh:.2f}")

print(f"\nCV F1: {np.mean(f1_scores):.4f} ± {np.std(f1_scores):.4f}")

# Final blend
oof_blend = 0.6 * oof_hgb + 0.4 * oof_rf
test_blend = 0.6 * test_hgb + 0.4 * test_rf

# Find global optimal threshold
best_f1_global, best_thresh_global = 0, 0.5
for thresh in np.arange(0.05, 0.95, 0.01):
    f1 = f1_score(y, (oof_blend >= thresh).astype(int), zero_division=0)
    if f1 > best_f1_global:
        best_f1_global, best_thresh_global = f1, thresh

print(f"\nOptimal threshold: {best_thresh_global:.2f}")
print(f"OOF F1 at optimal: {best_f1_global:.4f}")

# Generate submission
test_pred = (test_blend >= best_thresh_global).astype(int)
print(f"\nPredicted TDEs: {test_pred.sum()} / {len(test_pred)}")

submission = pd.DataFrame({
    'object_id': test_log['object_id'],
    'prediction': test_pred
})
submission.to_csv('submission_mallorn_v3.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v3.csv")
