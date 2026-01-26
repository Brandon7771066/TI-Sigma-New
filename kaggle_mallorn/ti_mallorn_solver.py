"""
TI MALLORN ASTRONOMICAL CLASSIFICATION SOLVER
Tidal Disruption Event (TDE) Classification
Metric: F1 Score | Deadline: Jan 30, 2026 | Prize: €1,000

DATA NEEDED (download from Kaggle):
- training_log.csv
- training_lc/ (folder with light curve CSVs)
- test_log.csv
- test_lc/ (folder with test light curves)
- sample_submission.csv
"""

import pandas as pd
import numpy as np
from pathlib import Path
import os
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN ASTRONOMICAL CLASSIFICATION SOLVER")
print("Tidal Disruption Event Detection | F1 Metric")
print("="*70)

# Check for data
DATA_DIR = Path(".")
required_files = ['training_log.csv', 'test_log.csv']
missing = [f for f in required_files if not (DATA_DIR / f).exists()]

if missing:
    print(f"\n⚠️  MISSING DATA FILES: {missing}")
    print("\nDownload from: https://www.kaggle.com/competitions/mallorn-astronomical-classification-challenge/data")
    print("Place files in: kaggle_mallorn/")
    exit(1)

# Load metadata
print("\nLoading data...")
train_log = pd.read_csv('training_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"Training samples: {len(train_log)}")
print(f"Test samples: {len(test_log)}")

# Class distribution
print(f"\nClass distribution:")
print(train_log['spectral_type'].value_counts())

# Binary target: TDE = 1, others = 0
train_log['is_tde'] = (train_log['spectral_type'] == 'TDE').astype(int)
print(f"\nTDE count: {train_log['is_tde'].sum()} ({100*train_log['is_tde'].mean():.2f}%)")

# Feature extraction from light curves
def extract_lc_features(object_id, lc_dir):
    """Extract features from a single light curve file"""
    lc_path = Path(lc_dir) / f"{object_id}.csv"
    
    if not lc_path.exists():
        return None
    
    try:
        lc = pd.read_csv(lc_path)
    except:
        return None
    
    features = {}
    
    # Per-band statistics
    bands = ['u', 'g', 'r', 'i', 'z', 'y']
    
    for band in bands:
        band_data = lc[lc['band'] == band] if 'band' in lc.columns else lc
        
        if len(band_data) == 0:
            features[f'{band}_n'] = 0
            features[f'{band}_mean'] = np.nan
            features[f'{band}_std'] = np.nan
            features[f'{band}_min'] = np.nan
            features[f'{band}_max'] = np.nan
            features[f'{band}_range'] = np.nan
            features[f'{band}_skew'] = np.nan
            continue
        
        flux_col = 'flux' if 'flux' in band_data.columns else 'mag' if 'mag' in band_data.columns else None
        
        if flux_col is None:
            continue
            
        flux = band_data[flux_col].dropna()
        
        if len(flux) == 0:
            continue
        
        features[f'{band}_n'] = len(flux)
        features[f'{band}_mean'] = flux.mean()
        features[f'{band}_std'] = flux.std()
        features[f'{band}_min'] = flux.min()
        features[f'{band}_max'] = flux.max()
        features[f'{band}_range'] = flux.max() - flux.min()
        features[f'{band}_skew'] = flux.skew() if len(flux) > 2 else 0
        
        # TI-inspired: Check if flux exceeds LCC threshold (0.42)
        norm_flux = (flux - flux.mean()) / (flux.std() + 1e-8)
        features[f'{band}_lcc_events'] = (norm_flux.abs() > 0.42).sum()
        
        # Time features
        if 'mjd' in band_data.columns or 'time' in band_data.columns:
            time_col = 'mjd' if 'mjd' in band_data.columns else 'time'
            time_data = band_data[time_col].values
            if len(time_data) > 1:
                features[f'{band}_duration'] = time_data.max() - time_data.min()
                features[f'{band}_cadence'] = np.median(np.diff(np.sort(time_data)))
    
    # Global features
    if 'flux' in lc.columns or 'mag' in lc.columns:
        flux_col = 'flux' if 'flux' in lc.columns else 'mag'
        all_flux = lc[flux_col].dropna()
        
        if len(all_flux) > 0:
            features['total_n'] = len(all_flux)
            features['global_mean'] = all_flux.mean()
            features['global_std'] = all_flux.std()
            features['global_range'] = all_flux.max() - all_flux.min()
            
            # TDE signature: rapid rise, slow decline
            if 'mjd' in lc.columns or 'time' in lc.columns:
                time_col = 'mjd' if 'mjd' in lc.columns else 'time'
                sorted_idx = lc[time_col].argsort()
                sorted_flux = lc[flux_col].iloc[sorted_idx].values
                
                if len(sorted_flux) > 10:
                    peak_idx = np.argmax(sorted_flux)
                    rise = sorted_flux[:peak_idx+1] if peak_idx > 0 else sorted_flux[:1]
                    decline = sorted_flux[peak_idx:] if peak_idx < len(sorted_flux)-1 else sorted_flux[-1:]
                    
                    features['rise_rate'] = (rise[-1] - rise[0]) / (len(rise) + 1)
                    features['decline_rate'] = (decline[-1] - decline[0]) / (len(decline) + 1)
                    features['asymmetry'] = features['rise_rate'] / (abs(features['decline_rate']) + 1e-8)
    
    return features

# Extract features for all objects
print("\nExtracting light curve features...")

def process_objects(log_df, lc_dir):
    features_list = []
    
    for i, row in log_df.iterrows():
        obj_id = row['object_id']
        feats = extract_lc_features(obj_id, lc_dir)
        
        if feats is None:
            feats = {}
        
        feats['object_id'] = obj_id
        
        # Add metadata features
        if 'true_redshift' in row:
            feats['redshift'] = row['true_redshift']
        
        features_list.append(feats)
        
        if (i + 1) % 500 == 0:
            print(f"  Processed {i+1}/{len(log_df)}")
    
    return pd.DataFrame(features_list)

# Check if light curve directories exist
train_lc_dir = 'training_lc'
test_lc_dir = 'test_lc'

if not Path(train_lc_dir).exists():
    print(f"\n⚠️  Light curve directory not found: {train_lc_dir}")
    print("Please download and extract the light curve data.")
    print("\nDownload from: https://www.kaggle.com/competitions/mallorn-astronomical-classification-challenge/data")
    print("Extract training_lc.zip and test_lc.zip to this folder")
    print("\n❌ Cannot generate valid submission without light curve data.")
    print("   The metadata alone is insufficient for TDE classification.")
    exit(1)
    
else:
    train_features = process_objects(train_log, train_lc_dir)
    test_features = process_objects(test_log, test_lc_dir)
    
    # Merge with target
    train_features = train_features.merge(
        train_log[['object_id', 'is_tde']], on='object_id'
    )
    
    y = train_features['is_tde'].values
    
    # Feature columns
    feature_cols = [c for c in train_features.columns 
                   if c not in ['object_id', 'is_tde']]
    
    X_train = train_features[feature_cols].fillna(0)
    X_test = test_features[[c for c in feature_cols if c in test_features.columns]].fillna(0)
    
    # Align columns
    for c in feature_cols:
        if c not in X_test.columns:
            X_test[c] = 0
    X_test = X_test[feature_cols]

print(f"\nFeatures: {X_train.shape[1]}")
print(f"Training: {len(X_train)}, Test: {len(X_test)}")
print(f"TDE positive rate: {y.mean():.4f}")

# Training with class weighting (imbalanced dataset)
print("\n" + "="*50)
print("TRAINING (5-fold CV)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = np.zeros(len(X_train))
test_preds = np.zeros(len(X_test))

f1_scores = []
precision_scores_list = []
recall_scores_list = []

# Scale features
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X_train)
X_test_scaled = scaler.transform(X_test)

for fold, (train_idx, val_idx) in enumerate(skf.split(X_scaled, y)):
    X_tr, X_val = X_scaled[train_idx], X_scaled[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # Calculate class weight
    pos_weight = len(y_tr) / (2 * y_tr.sum()) if y_tr.sum() > 0 else 1
    sample_weight = np.where(y_tr == 1, pos_weight, 1.0)
    
    # HistGradientBoosting (handles imbalance via class_weight proxy)
    model = HistGradientBoostingClassifier(
        max_iter=300,
        max_depth=6,
        learning_rate=0.05,
        l2_regularization=0.1,
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
    for thresh in np.arange(0.1, 0.9, 0.05):
        val_pred = (val_proba >= thresh).astype(int)
        f1 = f1_score(y_val, val_pred)
        if f1 > best_f1:
            best_f1 = f1
            best_thresh = thresh
    
    val_pred = (val_proba >= best_thresh).astype(int)
    f1 = f1_score(y_val, val_pred)
    prec = precision_score(y_val, val_pred)
    rec = recall_score(y_val, val_pred)
    
    f1_scores.append(f1)
    precision_scores_list.append(prec)
    recall_scores_list.append(rec)
    
    print(f"Fold {fold+1}: F1={f1:.4f} | Precision={prec:.4f} | Recall={rec:.4f} | Thresh={best_thresh:.2f}")

print(f"\n{'='*50}")
print(f"CV F1 Score: {np.mean(f1_scores):.4f} ± {np.std(f1_scores):.4f}")
print(f"CV Precision: {np.mean(precision_scores_list):.4f}")
print(f"CV Recall: {np.mean(recall_scores_list):.4f}")
print(f"{'='*50}")

# Find global optimal threshold
best_f1_global = 0
best_thresh_global = 0.5
for thresh in np.arange(0.1, 0.9, 0.02):
    oof_pred = (oof_preds >= thresh).astype(int)
    f1 = f1_score(y, oof_pred)
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
submission.to_csv('submission_mallorn.csv', index=False)
print(f"\n✅ Saved: submission_mallorn.csv")
print(f"Format check: {submission.head(3).to_string()}")
