"""
TI Heart Disease v2 — FULL 630k DATA
======================================

Upgrade from v1: uses complete 630,000 training samples (not 200k sample).
Faster HGB settings to stay within compute limits.

v1 result: OOF Accuracy = 0.8856 (200k stratified sample, 3-fold)
v2 target:  OOF Accuracy > 0.90 (full 630k, 2-fold, faster HGB)

Note: XGBoost/LightGBM unavailable due to pyproject.toml conflict.
sklearn ceiling for this dataset: ~90-93%. 96% requires XGBoost or DNN.

Brandon Emerick — TI Sigma Research
February 27, 2026
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import pandas as pd
import time
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import (HistGradientBoostingClassifier,
                               ExtraTreesClassifier)
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import accuracy_score
import warnings
warnings.filterwarnings('ignore')

from ti_sigma import PHI, LCC_TRALSE, LCC_HIGH
from ti_sigma.constants import verify_matching_rules
from ti_sigma.kaggle_adapter import HeartDiseaseAdapter

print("=" * 70)
print("TI HEART DISEASE v2 — FULL 630k DATA")
print("=" * 70)

rules = verify_matching_rules()
adapter = HeartDiseaseAdapter(n_quantum_modes=8)

DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'data', 'kaggle_s6e2')

print("[1/4] Loading full 630k dataset...")
train = pd.read_csv(os.path.join(DATA_DIR, 'train.csv'))
test  = pd.read_csv(os.path.join(DATA_DIR, 'test.csv'))
print(f"  Train: {len(train):,}  |  Test: {len(test):,}")

y_train  = (train['Heart Disease'] == 'Presence').astype(int).values
test_ids = test['id'].values
X_raw    = train.drop(columns=['id', 'Heart Disease'])
X_te_raw = test.drop(columns=['id'])

print("\n[2/4] Building Hypercomputer features (all 630k vectorized)...")
t0 = time.time()
X_feat    = adapter.build_features(X_raw)
X_te_feat = adapter.build_features(X_te_raw)
print(f"  Build time: {time.time()-t0:.1f}s")
print(f"  Feature shape: train={X_feat.shape}  test={X_te_feat.shape}")

# Additional hand-crafted cardiac interaction features
# (domain knowledge not captured by TI Hypercomputer alone)
def add_cardiac_interactions(X_raw_df, X_feat_arr):
    """Add polynomial interactions between top cardiac predictors."""
    cp   = X_raw_df['Chest pain type'].fillna(0).values.astype(float)
    age  = X_raw_df['Age'].fillna(50).values.astype(float)
    st   = X_raw_df['ST depression'].fillna(0).values.astype(float)
    mhr  = X_raw_df['Max HR'].fillna(150).values.astype(float)
    thal = X_raw_df['Thallium'].fillna(3).values.astype(float)
    nv   = X_raw_df['Number of vessels fluro'].fillna(0).values.astype(float)
    ea   = X_raw_df['Exercise angina'].fillna(0).values.astype(float)
    bp   = X_raw_df['BP'].fillna(130).values.astype(float)

    extras = np.column_stack([
        cp * st,                                   # chest pain × ST depression
        cp * ea,                                   # chest pain × exercise angina
        (thal == 7).astype(float) * age / 60.0,   # reversible defect × age
        nv * st,                                   # vessels × ST depression
        (nv >= 2).astype(float),                   # multi-vessel disease flag
        (cp == 4).astype(float),                   # typical angina flag
        (thal == 7).astype(float),                 # reversible defect flag
        np.log1p(st * age),                        # log ST-age interaction
        mhr * (1 - ea),                            # HR without angina constraint
        bp / (mhr + 1),                            # pressure-to-rate ratio
        age * (nv + 0.5) * st,                     # cumulative burden score
    ])
    return np.hstack([X_feat_arr, extras])

print("  Adding cardiac interaction features...")
X_feat    = add_cardiac_interactions(X_raw, X_feat)
X_te_feat = add_cardiac_interactions(X_te_raw, X_te_feat)
print(f"  Final feature shape: train={X_feat.shape}  test={X_te_feat.shape}")

print("\n[3/4] Training (2-fold StratifiedKFold, HGB full data)...")

scaler = StandardScaler()
X_s    = scaler.fit_transform(X_feat)
Xte_s  = scaler.transform(X_te_feat)

cv = StratifiedKFold(n_splits=2, shuffle=True, random_state=42)

# HGB: fast enough for 630k with these settings
hgb = HistGradientBoostingClassifier(
    learning_rate=0.05,
    max_iter=150,
    max_depth=7,
    min_samples_leaf=30,
    l2_regularization=0.5,
    max_features=0.8,
    random_state=42,
)

oof_hgb  = np.zeros(len(X_s))
test_hgb = np.zeros(len(Xte_s))

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_s, y_train)):
    t_fold = time.time()
    print(f"  Fold {fold+1}/2 ...", end="  ", flush=True)
    hgb.fit(X_s[tr_idx], y_train[tr_idx])
    oof_hgb[val_idx]  = hgb.predict_proba(X_s[val_idx])[:, 1]
    test_hgb         += hgb.predict_proba(Xte_s)[:, 1] / 2
    print(f"HGB✓  ({time.time()-t_fold:.1f}s)")

# Find best threshold
best_acc, best_thresh = 0, 0.5
for thresh in np.linspace(0.30, 0.70, 81):
    acc = accuracy_score(y_train, oof_hgb >= thresh)
    if acc > best_acc:
        best_acc, best_thresh = acc, thresh

print(f"\n{'='*60}")
print(f"OOF ACCURACY = {best_acc:.4f} @ thresh={best_thresh:.3f}")
print(f"  v1 (200k sample): 0.8856")
improvement = (best_acc - 0.8856) * 100
print(f"  v2 improvement:  {improvement:+.2f} pp")
print(f"  sklearn ceiling: ~90–93% (XGBoost needed for 96%)")
print(f"{'='*60}")

# Feature importance
if hasattr(hgb, 'feature_importances_'):
    imp      = hgb.feature_importances_
    top_idx  = np.argsort(imp)[-20:][::-1]
    print(f"\nTop 20 features:")
    for rank, idx in enumerate(top_idx):
        name = f'feat_{idx}'
        if idx >= X_feat.shape[1] - 11:
            extras = ['cp×st','cp×ea','thal×age','nv×st','multi_vessel',
                      'typical_angina','rev_defect','log_st_age',
                      'hr_no_angina','bp_hr_ratio','burden']
            name = 'cardiac_' + extras[idx - (X_feat.shape[1] - 11)]
        elif idx >= X_feat.shape[1] - 11 - 8:
            dom = ['cardiac_risk','hr_reserve','bp_hr_prod','phi_age',
                   'chol_lcc','tralse_r','sacred_f','lcc_coh']
            name = 'domain_' + dom[idx - (X_feat.shape[1] - 11 - 8)]
        print(f"  {rank+1:2d}. {name}: {imp[idx]:.4f}")

print("\n[4/4] Generating submission...")
y_pred      = (test_hgb >= best_thresh).astype(int)
pred_labels = np.where(y_pred == 1, 'Presence', 'Absence')
sub = pd.DataFrame({'id': test_ids, 'Heart Disease': pred_labels})
out = os.path.join(os.path.dirname(__file__), 'submission_heart_v2_full_data.csv')
sub.to_csv(out, index=False)
print(f"  Saved: {out}")
print(f"  Predicted Presence: {y_pred.sum():,} / {len(y_pred):,} ({y_pred.mean()*100:.1f}%)")
print("\n" + "="*70)
print("TI HEART DISEASE v2 COMPLETE")
print("="*70)
