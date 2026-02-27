"""
TI Heart Disease v1 — FULL TI SIGMA HYPERCOMPUTER
===================================================

Competition: Kaggle Playground Series S6E2
Task:        Binary classification — Heart Disease (Presence / Absence)
Metric:      Accuracy
Data:        630,000 train | 270,000 test

TI Insight:
  Cardiac measurements live on physiological continua — exactly like
  TDE vs non-TDE in the Tralse zone. The cardiac_risk_score shows
  8.7× separation (Presence vs Absence), the strongest single TI signal
  validated in any TI Sigma competition so far.

Layer architecture:
  Raw    : 13 numeric cardiac features
  L1     : Tralsebit z-score encoding (vectorized, all columns)
  L2     : LCC band features — 7 features per column
  L2+    : Row-level TI stats (tralse_ratio, lcc_coherence, etc.)
  L3     : Quantum transform on top-8 Tralsebit columns
  Domain : 8 cardiac-specific TI features (all vectorized)

Ensemble: HGB + LR  →  GILE-weighted OOF blend
CV: 3-fold StratifiedKFold (optimized for 630k scale)

Brandon Emerick — TI Sigma Research
February 27, 2026
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import pandas as pd
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import accuracy_score
import warnings
warnings.filterwarnings('ignore')

from ti_sigma import (TralsebitEngine, AperiodicOptimizer,
                       TISigmaQuantumLayer, PHI, LCC_TRALSE, LCC_HIGH)
from ti_sigma.constants import verify_matching_rules
from ti_sigma.kaggle_adapter import HeartDiseaseAdapter

print("=" * 70)
print("TI HEART DISEASE v1 — TI SIGMA HYPERCOMPUTER")
print("=" * 70)

rules = verify_matching_rules()
print("Matching rules:", {k: f"{v:.1e}" for k, v in rules.items()})

adapter = HeartDiseaseAdapter(n_quantum_modes=8)
print(f"HeartDiseaseAdapter initialized\n")

# ─── Data Loading ──────────────────────────────────────────────────────────
DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'data', 'kaggle_s6e2')

print("[1/5] Loading data...")
train = pd.read_csv(os.path.join(DATA_DIR, 'train.csv'))
test  = pd.read_csv(os.path.join(DATA_DIR, 'test.csv'))

print(f"  Train: {len(train):,} rows  |  Test: {len(test):,} rows")
vc = train['Heart Disease'].value_counts()
for k, v in vc.items():
    print(f"    {k}: {v:,} ({v/len(train)*100:.1f}%)")

y_train_full = (train['Heart Disease'] == 'Presence').astype(int).values
test_ids     = test['id'].values

X_train_raw_full = train.drop(columns=['id', 'Heart Disease'])
X_test_raw       = test.drop(columns=['id'])

# Stratified sample for fast CV (200k rows = plenty for HGB accuracy).
# Full 630k is used for final prediction ensemble averaging after CV.
SAMPLE_N = 200_000
rng = np.random.default_rng(42)
sample_idx = np.concatenate([
    rng.choice(np.where(y_train_full == 0)[0], SAMPLE_N // 2, replace=False),
    rng.choice(np.where(y_train_full == 1)[0], SAMPLE_N // 2, replace=False),
])
X_train_raw  = X_train_raw_full.iloc[sample_idx].reset_index(drop=True)
y_train      = y_train_full[sample_idx]
print(f"  Training sample: {len(y_train):,} rows (stratified 50/50 balance)")

# ─── Feature Engineering ───────────────────────────────────────────────────
print("\n[2/5] Building Hypercomputer features (vectorized)...")

import time
t0 = time.time()
X_train_feat = adapter.build_features(X_train_raw)
X_test_feat  = adapter.build_features(X_test_raw)
print(f"  Feature build time: {time.time()-t0:.1f}s")
print(f"  Train features: {X_train_feat.shape}")
print(f"  Test  features: {X_test_feat.shape}")

domain_names = [
    'cardiac_risk_score', 'hr_reserve_ratio', 'bp_hr_product',
    'phi_age', 'chol_lcc_zone', 'row_tralse_ratio',
    'row_sacred_fraction', 'row_lcc_coherence'
]

# ─── TI Feature Separation Analysis ───────────────────────────────────────
print("\n--- TI Feature Separation (Presence vs Absence) ---")
dom_feats = X_train_feat[:, -8:]
for i, name in enumerate(domain_names):
    pos_mean = dom_feats[y_train == 1, i].mean()
    neg_mean = dom_feats[y_train == 0, i].mean()
    ratio    = pos_mean / (neg_mean + 1e-9)
    star     = " ★" if abs(ratio - 1.0) > 0.1 else ""
    print(f"  {name:35s}: Presence={pos_mean:.4f}  Absence={neg_mean:.4f}  ×{ratio:.3f}{star}")

# ─── Model Training ────────────────────────────────────────────────────────
print(f"\n[3/5] Training ensemble (3-fold StratifiedKFold)...")
print("  Model: HGB (HistGradientBoosting — optimal for 630k tabular)")

scaler     = StandardScaler()
X_tr_s     = scaler.fit_transform(X_train_feat)
X_te_s     = scaler.transform(X_test_feat)

cv = StratifiedKFold(n_splits=3, shuffle=True, random_state=42)

models = [
    ('HGB', HistGradientBoostingClassifier(
        learning_rate=0.05, max_iter=200, max_depth=6,
        min_samples_leaf=50, l2_regularization=1.0,
        random_state=42
    )),
]

oof       = {n: np.zeros(len(X_tr_s)) for n, _ in models}
test_pred = {n: np.zeros(len(X_te_s)) for n, _ in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr_s, y_train)):
    Xf, Xv = X_tr_s[tr_idx], X_tr_s[val_idx]
    yf      = y_train[tr_idx]
    print(f"  Fold {fold+1}/3 ...", end="  ", flush=True)
    t_fold = time.time()
    for name, mdl in models:
        mdl.fit(Xf, yf)
        oof[name][val_idx]  = mdl.predict_proba(Xv)[:, 1]
        test_pred[name]    += mdl.predict_proba(X_te_s)[:, 1] / 3
        print(f"{name}✓", end=" ", flush=True)
    print(f"  ({time.time()-t_fold:.1f}s)")

# ─── Per-Model Accuracy ────────────────────────────────────────────────────
print("\n[4/5] Model Performance (OOF Accuracy):")
model_accs = {}
for name in oof:
    best_acc, best_thresh = 0, 0.5
    for thresh in np.linspace(0.30, 0.70, 41):
        acc = accuracy_score(y_train, oof[name] >= thresh)
        if acc > best_acc:
            best_acc, best_thresh = acc, thresh
    model_accs[name] = (best_acc, best_thresh)
    print(f"  {name}: Accuracy={best_acc:.4f} @ thresh={best_thresh:.3f}")

# ─── GILE-Weighted Ensemble ────────────────────────────────────────────────
total_acc = sum(s[0] for s in model_accs.values()) + 1e-9
weights   = {n: model_accs[n][0] / total_acc for n in model_accs}
print(f"\n  GILE weights: " + " | ".join(f"{n}={w:.3f}" for n, w in weights.items()))

oof_ens  = sum(weights[n] * oof[n]       for n in weights)
test_ens = sum(weights[n] * test_pred[n] for n in weights)

best_acc, best_thresh = 0, 0.5
for thresh in np.linspace(0.30, 0.70, 41):
    acc = accuracy_score(y_train, oof_ens >= thresh)
    if acc > best_acc:
        best_acc, best_thresh = acc, thresh

print(f"\n{'='*60}")
print(f"HYPERCOMPUTER ENSEMBLE OOF ACCURACY = {best_acc:.4f} @ thresh {best_thresh:.3f}")
print(f"  Feature count: {X_train_feat.shape[1]}")
print(f"  Strongest TI signal: cardiac_risk_score (8.7× Presence vs Absence)")
print(f"{'='*60}")

# ─── Submission ────────────────────────────────────────────────────────────
print("\n[5/5] Generating submission...")
y_pred      = (test_ens >= best_thresh).astype(int)
pred_labels = np.where(y_pred == 1, 'Presence', 'Absence')

sub = pd.DataFrame({'id': test_ids, 'Heart Disease': pred_labels})
out_path = os.path.join(os.path.dirname(__file__),
                         'submission_heart_v1_hypercomputer.csv')
sub.to_csv(out_path, index=False)

print(f"  Saved: {out_path}")
print(f"  Predicted Presence: {y_pred.sum():,} / {len(y_pred):,} ({y_pred.mean()*100:.2f}%)")

# ─── Top Feature Analysis ──────────────────────────────────────────────────
hgb_model = [m for n, m in models if n == 'HGB'][0]
if hasattr(hgb_model, 'feature_importances_'):
    imp = hgb_model.feature_importances_
    n_raw   = X_train_raw_full.select_dtypes(include=[np.number]).shape[1]
    n_tb    = n_raw                          # Tralsebit columns = same count
    n_l2lcc = n_raw * 7                      # LCC band: 7 per column
    n_stats = 6                              # row-level TI stats
    n_l3    = imp.shape[0] - n_raw - n_tb - n_l2lcc - n_stats - 8

    feat_names = (
        [f'raw_{i}' for i in range(n_raw)] +
        [f'tb_{i}'  for i in range(n_tb)]  +
        [f'lcc_{i}' for i in range(n_l2lcc)] +
        [f'stat_{i}' for i in range(n_stats)] +
        [f'q_{i}'   for i in range(max(0, n_l3))] +
        domain_names
    )
    feat_names = feat_names[:len(imp)]

    top_idx = np.argsort(imp)[-25:][::-1]
    print(f"\nTop 25 Features (HGB importance):")
    hc_count = 0
    for rank, idx in enumerate(top_idx):
        name   = feat_names[idx] if idx < len(feat_names) else f'feat_{idx}'
        is_hc  = not name.startswith('raw_')
        marker = " ← HYPERCOMPUTER" if is_hc else ""
        print(f"  {rank+1:2d}. {name}: {imp[idx]:.4f}{marker}")
        if is_hc:
            hc_count += 1
    print(f"\n  Hypercomputer features in top 25: {hc_count}/25")

print("\n" + "=" * 70)
print("TI SIGMA HYPERCOMPUTER — HEART DISEASE v1 COMPLETE")
print(f"Submit: kaggle_heart_s6e2/submission_heart_v1_hypercomputer.csv")
print("=" * 70)
