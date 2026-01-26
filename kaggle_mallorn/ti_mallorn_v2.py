"""
TI MALLORN ASTRONOMICAL CLASSIFICATION SOLVER v2
Tidal Disruption Event (TDE) Detection
Metric: F1 Score | Deadline: Jan 30, 2026 | Prize: €1,000
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN SOLVER v2 - Tidal Disruption Event Detection")
print("="*70)

# Load metadata
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"Training objects: {len(train_log)}")
print(f"Test objects: {len(test_log)}")

print(f"\nClass distribution (target):")
print(train_log['target'].value_counts())
print(f"TDE rate: {train_log['target'].mean()*100:.2f}%")

print(f"\nSpectral types:")
print(train_log['SpecType'].value_counts())

# Load all light curves from splits
def load_all_lightcurves(log_df, lc_type='train'):
    all_lc = []
    splits = log_df['split'].unique()
    
    for split in splits:
        lc_file = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(lc_file).exists():
            lc = pd.read_csv(lc_file)
            all_lc.append(lc)
    
    if all_lc:
        return pd.concat(all_lc, ignore_index=True)
    return pd.DataFrame()

print("\nLoading light curves...")
train_lc = load_all_lightcurves(train_log, 'train')
test_lc = load_all_lightcurves(test_log, 'test')

print(f"Train LC observations: {len(train_lc):,}")
print(f"Test LC observations: {len(test_lc):,}")

# Feature extraction from light curves
def extract_features(object_id, lc_df):
    """Extract features from light curve data for one object"""
    obj_lc = lc_df[lc_df['object_id'] == object_id]
    
    if len(obj_lc) == 0:
        return {}
    
    features = {}
    
    # Overall statistics
    features['n_obs'] = len(obj_lc)
    features['flux_mean'] = obj_lc['Flux'].mean()
    features['flux_std'] = obj_lc['Flux'].std()
    features['flux_min'] = obj_lc['Flux'].min()
    features['flux_max'] = obj_lc['Flux'].max()
    features['flux_range'] = features['flux_max'] - features['flux_min']
    features['flux_skew'] = obj_lc['Flux'].skew()
    features['flux_kurt'] = obj_lc['Flux'].kurt()
    
    # Error-weighted features
    if 'Flux_err' in obj_lc.columns:
        weights = 1 / (obj_lc['Flux_err'] + 1e-8)
        features['flux_wmean'] = np.average(obj_lc['Flux'], weights=weights)
        features['snr_mean'] = (obj_lc['Flux'] / (obj_lc['Flux_err'] + 1e-8)).mean()
        features['snr_max'] = (obj_lc['Flux'] / (obj_lc['Flux_err'] + 1e-8)).max()
    
    # Time features
    if 'Time (MJD)' in obj_lc.columns:
        time = obj_lc['Time (MJD)'].values
        features['duration'] = time.max() - time.min()
        features['cadence_mean'] = np.mean(np.diff(np.sort(time))) if len(time) > 1 else 0
        features['cadence_std'] = np.std(np.diff(np.sort(time))) if len(time) > 1 else 0
        
        # TDE signature: Find peak and measure rise/decline
        sorted_idx = np.argsort(time)
        sorted_flux = obj_lc['Flux'].iloc[sorted_idx].values
        sorted_time = time[sorted_idx]
        
        if len(sorted_flux) >= 5:
            peak_idx = np.argmax(sorted_flux)
            
            # Rise phase
            if peak_idx > 0:
                rise_flux = sorted_flux[:peak_idx+1]
                rise_time = sorted_time[:peak_idx+1]
                features['rise_rate'] = (rise_flux[-1] - rise_flux[0]) / (rise_time[-1] - rise_time[0] + 1e-8)
            else:
                features['rise_rate'] = 0
            
            # Decline phase
            if peak_idx < len(sorted_flux) - 1:
                decline_flux = sorted_flux[peak_idx:]
                decline_time = sorted_time[peak_idx:]
                features['decline_rate'] = (decline_flux[-1] - decline_flux[0]) / (decline_time[-1] - decline_time[0] + 1e-8)
            else:
                features['decline_rate'] = 0
            
            # TDE asymmetry: rapid rise, slow decline
            features['asymmetry'] = abs(features['rise_rate']) / (abs(features['decline_rate']) + 1e-8)
            features['peak_position'] = peak_idx / len(sorted_flux)
    
    # Per-filter statistics
    filters = obj_lc['Filter'].unique() if 'Filter' in obj_lc.columns else []
    for filt in ['u', 'g', 'r', 'i', 'z', 'y']:
        filt_data = obj_lc[obj_lc['Filter'] == filt] if 'Filter' in obj_lc.columns else pd.DataFrame()
        
        if len(filt_data) > 0:
            features[f'{filt}_n'] = len(filt_data)
            features[f'{filt}_mean'] = filt_data['Flux'].mean()
            features[f'{filt}_std'] = filt_data['Flux'].std()
            features[f'{filt}_range'] = filt_data['Flux'].max() - filt_data['Flux'].min()
            
            # TI-inspired: LCC threshold (0.42) for significant variations
            norm_flux = (filt_data['Flux'] - filt_data['Flux'].mean()) / (filt_data['Flux'].std() + 1e-8)
            features[f'{filt}_lcc_events'] = (norm_flux.abs() > 0.42).sum()
        else:
            features[f'{filt}_n'] = 0
            features[f'{filt}_mean'] = 0
            features[f'{filt}_std'] = 0
            features[f'{filt}_range'] = 0
            features[f'{filt}_lcc_events'] = 0
    
    # Color features (flux ratios between bands)
    if features.get('g_mean', 0) > 0 and features.get('r_mean', 0) > 0:
        features['g_r_color'] = features['g_mean'] / (features['r_mean'] + 1e-8)
    else:
        features['g_r_color'] = 0
    
    if features.get('r_mean', 0) > 0 and features.get('i_mean', 0) > 0:
        features['r_i_color'] = features['r_mean'] / (features['i_mean'] + 1e-8)
    else:
        features['r_i_color'] = 0
    
    return features

# Process all objects
print("\nExtracting features...")

train_features = []
for i, row in train_log.iterrows():
    feats = extract_features(row['object_id'], train_lc)
    feats['object_id'] = row['object_id']
    feats['Z'] = row['Z'] if pd.notna(row['Z']) else 0
    feats['EBV'] = row['EBV'] if pd.notna(row['EBV']) else 0
    train_features.append(feats)
    
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

test_features = []
for i, row in test_log.iterrows():
    feats = extract_features(row['object_id'], test_lc)
    feats['object_id'] = row['object_id']
    feats['Z'] = row['Z'] if pd.notna(row['Z']) else 0
    feats['EBV'] = row['EBV'] if pd.notna(row['EBV']) else 0
    test_features.append(feats)
    
    if (i + 1) % 500 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

train_df = pd.DataFrame(train_features)
test_df = pd.DataFrame(test_features)

# Prepare features
feature_cols = [c for c in train_df.columns if c != 'object_id']
X = train_df[feature_cols].fillna(0)
X_test = test_df[feature_cols].fillna(0)
y = train_log['target'].values

print(f"\nFeatures: {len(feature_cols)}")
print(f"Training: {len(X)}, Test: {len(X_test)}")
print(f"TDE positive rate: {y.mean():.4f}")

# Scale
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
X_test_scaled = scaler.transform(X_test)

# Training with cross-validation
print("\n" + "="*50)
print("TRAINING (5-fold Stratified CV)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = np.zeros(len(X))
test_preds = np.zeros(len(X_test))

f1_scores = []
precision_list = []
recall_list = []

for fold, (train_idx, val_idx) in enumerate(skf.split(X_scaled, y)):
    X_tr, X_val = X_scaled[train_idx], X_scaled[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # HistGradientBoosting
    model = HistGradientBoostingClassifier(
        max_iter=400,
        max_depth=7,
        learning_rate=0.04,
        l2_regularization=0.05,
        max_bins=255,
        min_samples_leaf=15,
        class_weight='balanced',
        early_stopping=True,
        validation_fraction=0.15,
        n_iter_no_change=30,
        random_state=42
    )
    model.fit(X_tr, y_tr)
    
    # Predict probabilities
    val_proba = model.predict_proba(X_val)[:, 1]
    oof_preds[val_idx] = val_proba
    test_preds += model.predict_proba(X_test_scaled)[:, 1] / 5
    
    # Find optimal threshold for F1
    best_f1 = 0
    best_thresh = 0.5
    for thresh in np.arange(0.05, 0.95, 0.02):
        val_pred = (val_proba >= thresh).astype(int)
        f1 = f1_score(y_val, val_pred, zero_division=0)
        if f1 > best_f1:
            best_f1 = f1
            best_thresh = thresh
    
    val_pred = (val_proba >= best_thresh).astype(int)
    f1 = f1_score(y_val, val_pred, zero_division=0)
    prec = precision_score(y_val, val_pred, zero_division=0)
    rec = recall_score(y_val, val_pred, zero_division=0)
    
    f1_scores.append(f1)
    precision_list.append(prec)
    recall_list.append(rec)
    
    print(f"Fold {fold+1}: F1={f1:.4f} | P={prec:.4f} | R={rec:.4f} | Thresh={best_thresh:.2f}")

print(f"\n{'='*50}")
print(f"CV F1: {np.mean(f1_scores):.4f} ± {np.std(f1_scores):.4f}")
print(f"CV Precision: {np.mean(precision_list):.4f}")
print(f"CV Recall: {np.mean(recall_list):.4f}")
print(f"{'='*50}")

# Find global optimal threshold
best_f1_global = 0
best_thresh_global = 0.5
for thresh in np.arange(0.05, 0.95, 0.01):
    oof_pred = (oof_preds >= thresh).astype(int)
    f1 = f1_score(y, oof_pred, zero_division=0)
    if f1 > best_f1_global:
        best_f1_global = f1
        best_thresh_global = thresh

print(f"\nOptimal threshold: {best_thresh_global:.2f}")
print(f"OOF F1 at optimal: {best_f1_global:.4f}")

# Generate submission
test_pred_binary = (test_preds >= best_thresh_global).astype(int)
print(f"\nPredicted TDEs: {test_pred_binary.sum()} / {len(test_pred_binary)}")

submission = pd.DataFrame({
    'object_id': test_log['object_id'],
    'prediction': test_pred_binary
})
submission.to_csv('submission_mallorn_v2.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v2.csv")
print(f"Sample:\n{submission.head()}")
