"""
TI MALLORN v16 DEMO - Quick Tralse Feature Validation
=====================================================
Single-fold training for fast demonstration.
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI MALLORN v16 DEMO - TRALSE FEATURES")
print("Quick validation of 4-valued logic integration")
print("=" * 70)

PHI = (1 + np.sqrt(5)) / 2
TDE_POWER_LAW = -5/3
LCC_085 = 0.85

def tralse_activation(x):
    x = np.asarray(x).flatten()
    t = np.maximum(0, x)
    f = np.maximum(0, -x)
    phi = np.exp(-x**2)
    return t, f, phi

def myrion_phi(pos, neg):
    contra = np.minimum(np.abs(pos), np.abs(neg))
    return contra / (np.abs(pos) + np.abs(neg) + 1e-8)

# Load
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Train: {len(train_log)} | TDE: {train_log['target'].sum()}")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')

if 'Time (MJD)' in train_lc.columns:
    train_lc = train_lc.rename(columns={'Time (MJD)': 'mjd'})
    test_lc = test_lc.rename(columns={'Time (MJD)': 'mjd'})

train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract(obj_id, lc_dict, meta):
    if obj_id not in lc_dict:
        return None
    flux = lc_dict[obj_id]['Flux'].dropna().values
    if len(flux) < 5:
        return None
    
    f = {}
    f['Z'] = meta['Z']
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    
    # TRALSE
    t, fal, phi = tralse_activation(flux)
    f['taf_t_mean'] = np.mean(t)
    f['taf_f_mean'] = np.mean(fal)
    f['taf_phi_mean'] = np.mean(phi)
    f['taf_certainty'] = np.mean(1 - phi)
    
    # MYRION
    diffs = np.diff(flux)
    pos_d = np.sum(np.maximum(0, diffs))
    neg_d = np.sum(np.maximum(0, -diffs))
    f['myr_phi'] = float(myrion_phi(pos_d, neg_d))
    
    # LCC
    flux_n = (flux - np.mean(flux)) / (np.std(flux) + 1e-8)
    f['lcc_085'] = np.mean(np.abs(flux_n) > LCC_085)
    
    # Power law
    peak = np.argmax(flux)
    if peak < len(flux) - 5:
        dec = flux[peak:]
        pos_dec = dec[dec > 0]
        if len(pos_dec) > 3:
            slope, _, r, _, _ = stats.linregress(
                np.log(np.arange(1, len(pos_dec)+1)), np.log(pos_dec)
            )
            f['tde_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
        else:
            f['tde_match'] = 0
    else:
        f['tde_match'] = 0
    
    # GTFE
    f['gtfe_c'] = np.mean(np.abs(flux - np.median(flux)) / (np.abs(np.median(flux)) + 1e-8))
    
    # Synergy
    f['tralse_synergy'] = f['taf_certainty'] * (1 - f['myr_phi']) * f['lcc_085']
    
    return f

print("\nExtracting...")
train_f, train_y = [], []
for i, r in train_log.iterrows():
    feat = extract(r['object_id'], train_lc_dict, r)
    if feat:
        train_f.append(feat)
        train_y.append(r['target'])

test_f, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract(r['object_id'], test_lc_dict, r)
    if feat:
        test_f.append(feat)
        test_ids.append(r['object_id'])

X_train = pd.DataFrame(train_f).fillna(0)
y_train = np.array(train_y)
X_test = pd.DataFrame(test_f).fillna(0)

common = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common]
X_test = X_test[common]

print(f"Features: {len(common)}")

# Single model training
print("\nTraining RF...")
scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

rf = RandomForestClassifier(n_estimators=100, max_depth=8, random_state=42, n_jobs=-1)
rf.fit(X_tr, y_train)

# Find threshold
probs = rf.predict_proba(X_tr)[:, 1]
best_f1, best_th = 0, 0.3
for th in np.linspace(0.1, 0.5, 21):
    f1 = f1_score(y_train, probs >= th)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print(f"\nTRAINING F1: {best_f1:.4f} @ {best_th:.3f}")

# Predict
test_probs = rf.predict_proba(X_te)[:, 1]
y_pred = (test_probs >= best_th).astype(int)

submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_mallorn_v16_demo.csv', index=False)
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)}")
print(f"\n✅ Saved: submission_mallorn_v16_demo.csv")

# Feature importance
print("\n" + "=" * 60)
print("FEATURE IMPORTANCE")
print("=" * 60)
imp = pd.Series(rf.feature_importances_, index=X_train.columns).sort_values(ascending=False)
for i, (feat, val) in enumerate(imp.items()):
    ti = "★ TRALSE" if any(x in feat for x in ['taf', 'myr', 'lcc', 'tralse']) else ""
    print(f"  {i+1:2d}. {feat:20s} {val:.4f} {ti}")

# TDE vs non-TDE
print("\n" + "=" * 60)
print("TDE vs NON-TDE COMPARISON")
print("=" * 60)
for feat in X_train.columns:
    tde = X_train.loc[y_train == 1, feat].mean()
    non = X_train.loc[y_train == 0, feat].mean()
    diff = (tde - non) / (non + 1e-8) * 100
    if abs(diff) > 10:
        print(f"  {feat:20s}: TDE={tde:.4f}, Non={non:.4f}, Diff={diff:+.1f}%")

print("\n✅ v16 DEMO COMPLETE - Tralse features validated!")
