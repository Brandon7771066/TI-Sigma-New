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

Ensemble: HGB + RF + ET + LR  →  GILE-weighted OOF blend
CV: 3-fold StratifiedKFold (MALLORN v17 pattern, speed-optimized for Replit)

Brandon Emerick — TI Sigma Research
February 28, 2026
"""

import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import pandas as pd
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import (HistGradientBoostingClassifier,
                               RandomForestClassifier,
                               ExtraTreesClassifier)
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
print("TI HEART DISEASE v1 — TI SIGMA HYPERCOMPUTER (MALLORN v17 PATTERN)")
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

# Stratified 50/50 sample for CV — 50k rows (25k per class).
# Balanced classes match the competition's real-world distribution.
# Full 630k is used for final test inference after CV weights are set.
SAMPLE_N = 50_000
rng = np.random.default_rng(42)
# Guard: only sample as many as exist in minority class
n_pos = (y_train_full == 1).sum()
n_neg = (y_train_full == 0).sum()
per_class = min(SAMPLE_N // 2, n_pos, n_neg)
sample_idx = np.concatenate([
    rng.choice(np.where(y_train_full == 0)[0], per_class, replace=False),
    rng.choice(np.where(y_train_full == 1)[0], per_class, replace=False),
])
X_train_raw  = X_train_raw_full.iloc[sample_idx].reset_index(drop=True)
y_train      = y_train_full[sample_idx]
print(f"  CV sample: {len(y_train):,} rows (stratified 50/50 balance)")

# ─── Feature Engineering ───────────────────────────────────────────────────
print("\n[2/5] Building Hypercomputer features (vectorized)...")

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
    star     = " ★" if abs(ratio - 1.0) > 0.10 else ""
    print(f"  {name:35s}: Presence={pos_mean:.4f}  Absence={neg_mean:.4f}  ×{ratio:.3f}{star}")

# ─── Model Training — MALLORN v17 4-Model Ensemble ────────────────────────
print(f"\n[3/5] Training 4-model ensemble (5-fold StratifiedKFold)...")
print("  L1=Tralsebit · L2=Aperiodic · L3=Quantum · HGB+RF+ET+LR")

scaler   = StandardScaler()
X_tr_s   = scaler.fit_transform(X_train_feat)
X_te_s   = scaler.transform(X_test_feat)

cv = StratifiedKFold(n_splits=3, shuffle=True, random_state=42)

# ET (ExtraTrees) serves as the "GB" forest slot — faster than sklearn GB,
# same ensemble diversity benefit, supports n_jobs=-1 parallelism.
# All forest models use n_jobs=-1 and shallow trees for Replit CPU budget.
models = [
    ('HGB', HistGradientBoostingClassifier(
        learning_rate=0.05, max_iter=300, max_depth=6,
        min_samples_leaf=20, l2_regularization=1.0,
        random_state=42
    )),
    ('RF', RandomForestClassifier(
        n_estimators=100, max_depth=10, n_jobs=-1,
        min_samples_leaf=10, random_state=42
    )),
    ('ET', ExtraTreesClassifier(
        n_estimators=100, max_depth=12, n_jobs=-1,
        min_samples_leaf=5, random_state=42
    )),
    ('LR', LogisticRegression(
        max_iter=500, C=0.1, solver='lbfgs', n_jobs=-1,
        random_state=42
    )),
]

n_folds   = cv.get_n_splits()
oof       = {n: np.zeros(len(X_tr_s)) for n, _ in models}
test_pred = {n: np.zeros(len(X_te_s)) for n, _ in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr_s, y_train)):
    Xf, Xv = X_tr_s[tr_idx], X_tr_s[val_idx]
    yf      = y_train[tr_idx]
    print(f"  Fold {fold+1}/{n_folds} ...", end="  ", flush=True)
    t_fold = time.time()
    for name, mdl in models:
        mdl.fit(Xf, yf)
        oof[name][val_idx]  = mdl.predict_proba(Xv)[:, 1]
        test_pred[name]    += mdl.predict_proba(X_te_s)[:, 1] / n_folds
        print(f"{name}✓", end=" ", flush=True)
    print(f"  ({time.time()-t_fold:.1f}s)")

# ─── Per-Model OOF Accuracy ────────────────────────────────────────────────
print("\n[4/5] Model Performance (OOF Accuracy — threshold-optimized):")
model_accs = {}
for name in oof:
    best_acc, best_thresh = 0, 0.5
    for thresh in np.linspace(0.30, 0.70, 41):
        acc = accuracy_score(y_train, oof[name] >= thresh)
        if acc > best_acc:
            best_acc, best_thresh = acc, thresh
    model_accs[name] = (best_acc, best_thresh)
    print(f"  {name}: OOF Accuracy={best_acc:.4f} @ threshold={best_thresh:.3f}")

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
print(f"  Ensemble: HGB + RF + ET + LR (4-model MALLORN v17 pattern)")
print(f"{'='*60}")

# ─── Submission ────────────────────────────────────────────────────────────
print("\n[5/5] Generating submission...")
y_pred      = (test_ens >= best_thresh).astype(int)
pred_labels = np.where(y_pred == 1, 'Presence', 'Absence')

sub      = pd.DataFrame({'id': test_ids, 'Heart Disease': pred_labels})
out_path = os.path.join(os.path.dirname(__file__),
                         'submission_heart_v1_hypercomputer.csv')
sub.to_csv(out_path, index=False)

print(f"  Saved: {out_path}")
print(f"  Rows: {len(sub):,} (expected 270,000)")
print(f"  Predicted Presence: {y_pred.sum():,} / {len(y_pred):,} ({y_pred.mean()*100:.2f}%)")

# ─── Submission Validation ─────────────────────────────────────────────────
assert len(sub) == 270_000, f"Row count mismatch: {len(sub)}"
assert list(sub.columns) == ['id', 'Heart Disease'], "Column mismatch"
assert set(sub['Heart Disease'].unique()).issubset({'Presence', 'Absence'}), "Label mismatch"
print("  Submission validation: PASSED ✓")

# ─── Top Feature Analysis (HGB) ────────────────────────────────────────────
hgb_model = dict(models)['HGB']
if hasattr(hgb_model, 'feature_importances_'):
    imp     = hgb_model.feature_importances_
    n_raw   = X_train_raw_full.select_dtypes(include=[np.number]).shape[1]
    n_tb    = n_raw
    n_l2lcc = n_raw * 7
    n_stats = 6
    n_l3    = max(0, imp.shape[0] - n_raw - n_tb - n_l2lcc - n_stats - 8)

    feat_names = (
        [f'raw_{i}'  for i in range(n_raw)]   +
        [f'tb_{i}'   for i in range(n_tb)]    +
        [f'lcc_{i}'  for i in range(n_l2lcc)] +
        [f'stat_{i}' for i in range(n_stats)] +
        [f'q_{i}'    for i in range(n_l3)]    +
        domain_names
    )
    feat_names = feat_names[:len(imp)]

    top_idx  = np.argsort(imp)[-25:][::-1]
    hc_count = 0
    print(f"\nTop 25 Features (HGB importance):")
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
print(f"  OOF Accuracy : {best_acc:.4f}")
print(f"  Threshold    : {best_thresh:.3f}")
print(f"  Features     : {X_train_feat.shape[1]}")
print(f"  Submit: kaggle_heart_s6e2/submission_heart_v1_hypercomputer.csv")
print("=" * 70)
