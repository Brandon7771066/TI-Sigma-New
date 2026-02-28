"""
TI Heart Disease v3 — DEADLINE SPRINT
======================================

Key insight from v1/v2 post-mortem:
150 noisy Hypercomputer features ≈ 88.69% — adding quantum/aperiodic noise
hurt more than it helped. The 13 clinical features + targeted interactions
+ proper categorical encoding + diverse sklearn ensemble should push 90%+.

Clinical domain knowledge:
- Number of vessels fluro (ca): strongest predictor (#1)
- Thallium (thal): 7=reversible defect → strongest qualitative signal (#2)
- Chest pain type: 4=asymptomatic → paradoxically worst prognosis (#3)
- ST depression: continuous measure of ischemia (#4)
- Exercise angina + Age + ST interaction: cardiac_risk_score (#5)

Philosophy: clean < 40 features, 3-model diverse sklearn ensemble.

Brandon Emerick — TI Sigma Research
February 28, 2026 (COMPETITION DEADLINE)
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
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import accuracy_score
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI HEART DISEASE v3 — DEADLINE SPRINT (Clinical + ExtraTrees)")
print("=" * 70)

DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'data', 'kaggle_s6e2')

print("[1/4] Loading full 630k dataset...")
train = pd.read_csv(os.path.join(DATA_DIR, 'train.csv'))
test  = pd.read_csv(os.path.join(DATA_DIR, 'test.csv'))
print(f"  Train: {len(train):,}  |  Test: {len(test):,}")

y_train  = (train['Heart Disease'] == 'Presence').astype(int).values
test_ids = test['id'].values
X_raw    = train.drop(columns=['id', 'Heart Disease'])
X_te_raw = test.drop(columns=['id'])


def engineer_features(df):
    """
    Clean, clinically-grounded feature engineering.
    Hypothesis: 35 focused features >> 150 noisy hypercomputer features.
    """
    X = df.copy()

    age  = X['Age'].values.astype(float)
    sex  = X['Sex'].values.astype(float)
    cp   = X['Chest pain type'].values.astype(float)
    bp   = X['BP'].values.astype(float)
    chol = X['Cholesterol'].values.astype(float)
    fbs  = X['FBS over 120'].values.astype(float)
    ekg  = X['EKG results'].values.astype(float)
    mhr  = X['Max HR'].values.astype(float)
    ea   = X['Exercise angina'].values.astype(float)
    st   = X['ST depression'].values.astype(float)
    slp  = X['Slope of ST'].values.astype(float)
    nv   = X['Number of vessels fluro'].values.astype(float)
    thal = X['Thallium'].values.astype(float)

    # Raw features (passthrough)
    raw = np.column_stack([age, sex, cp, bp, chol, fbs, ekg, mhr, ea, st, slp, nv, thal])

    # One-hot encoding of categoricals
    cp_ohe   = np.column_stack([(cp == v).astype(float) for v in [1, 2, 3, 4]])
    ekg_ohe  = np.column_stack([(ekg == v).astype(float) for v in [0, 1, 2]])
    slp_ohe  = np.column_stack([(slp == v).astype(float) for v in [1, 2, 3]])
    thal_ohe = np.column_stack([(thal == v).astype(float) for v in [3, 6, 7]])
    nv_ohe   = np.column_stack([(nv == v).astype(float) for v in [0, 1, 2, 3]])

    # Clinical interaction features (TI L×E product structure)
    cardiac_risk   = age * st * ea                          # L×E triple product
    hr_reserve     = mhr / np.clip(220 - age, 80, 220)     # cardiac reserve
    bp_hr_product  = bp * mhr / 10000.0                    # double product (MI risk)
    chol_age       = chol * age / 1000.0                   # cumulative cholesterol burden
    st_slope_int   = st * (slp == 1).astype(float)         # downsloping + ST depression
    vessel_thal    = nv * (thal == 7).astype(float)        # multi-vessel reversible defect
    age_sex        = age * sex                              # male cardiac risk amplifier
    max_hr_pct     = mhr / 220.0                           # % max HR
    thal7_age      = (thal == 7).astype(float) * age / 60  # reversible defect scaled by age
    cp4_st         = (cp == 4).astype(float) * st          # asymptomatic × ST depression
    nv_st          = nv * st                               # vessel count × ischemia
    multi_vessel   = (nv >= 2).astype(float)               # binary multi-vessel disease
    asymp_angina   = (cp == 4).astype(float) * ea          # asymptomatic + exercise angina
    log_st_age     = np.log1p(np.abs(st) * age)            # log-scale burden
    bp_age         = bp * age / 5000.0                     # cumulative pressure-age
    phi            = 1.61803398875
    phi_age        = (age - 42) / (phi * 42)               # φ-normalized cardiac age onset
    thal7_flag     = (thal == 7).astype(float)             # reversible defect flag
    cp4_flag       = (cp == 4).astype(float)               # typical angina (paradox) flag
    normal_thal    = (thal == 3).astype(float)             # normal perfusion = protective
    high_nv        = (nv >= 3).astype(float)               # 3-vessel disease = severe
    zero_nv        = (nv == 0).astype(float)               # no obstruction = protective

    interactions = np.column_stack([
        cardiac_risk, hr_reserve, bp_hr_product, chol_age,
        st_slope_int, vessel_thal, age_sex, max_hr_pct,
        thal7_age, cp4_st, nv_st, multi_vessel, asymp_angina,
        log_st_age, bp_age, phi_age, thal7_flag, cp4_flag,
        normal_thal, high_nv, zero_nv,
    ])

    feat = np.hstack([raw, cp_ohe, ekg_ohe, slp_ohe, thal_ohe, nv_ohe, interactions])
    return feat


print("\n[2/4] Engineering clinical features...")
t0 = time.time()
X_feat    = engineer_features(X_raw)
X_te_feat = engineer_features(X_te_raw)
print(f"  Build time: {time.time()-t0:.1f}s")
print(f"  Feature shape: train={X_feat.shape}  test={X_te_feat.shape}")

# Feature analysis
print("\n--- Top Clinical Features (Presence vs Absence) ---")
feat_names = (
    ['age','sex','cp','bp','chol','fbs','ekg','mhr','ea','st','slp','nv','thal'] +
    [f'cp{i}' for i in [1,2,3,4]] +
    [f'ekg{i}' for i in [0,1,2]] +
    [f'slp{i}' for i in [1,2,3]] +
    [f'thal{i}' for i in [3,6,7]] +
    [f'nv{i}' for i in [0,1,2,3]] +
    ['cardiac_risk','hr_reserve','bp_hr_prod','chol_age','st_slope',
     'vessel_thal','age_sex','max_hr_pct','thal7_age','cp4_st','nv_st',
     'multi_vessel','asymp_angina','log_st_age','bp_age','phi_age',
     'thal7_flag','cp4_flag','normal_thal','high_nv','zero_nv']
)
pos = X_feat[y_train == 1]
neg = X_feat[y_train == 0]
for i, name in enumerate(feat_names[:34]):
    pm = pos[:, i].mean(); nm = neg[:, i].mean()
    r  = pm / (nm + 1e-9)
    if abs(r - 1.0) > 0.2:
        print(f"  {name:20s}: Presence={pm:.4f}  Absence={nm:.4f}  ×{r:.3f} ★")


print("\n[3/4] Training diverse ensemble (3-fold)...")
scaler = StandardScaler()
X_s    = scaler.fit_transform(X_feat)
Xte_s  = scaler.transform(X_te_feat)

cv = StratifiedKFold(n_splits=3, shuffle=True, random_state=42)

# Three diverse models — different inductive biases
models = {
    'HGB': HistGradientBoostingClassifier(
        learning_rate=0.05, max_iter=200, max_depth=7,
        min_samples_leaf=30, l2_regularization=0.3,
        max_features=0.85, random_state=42
    ),
    'EXT': ExtraTreesClassifier(
        n_estimators=500, max_depth=None, min_samples_leaf=3,
        max_features='sqrt', n_jobs=-1, random_state=42
    ),
    'LR': LogisticRegression(
        C=0.5, max_iter=500, solver='lbfgs', n_jobs=-1, random_state=42
    ),
}

oof   = {k: np.zeros(len(X_s)) for k in models}
preds = {k: np.zeros(len(Xte_s)) for k in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_s, y_train)):
    print(f"\n  Fold {fold+1}/3:")
    for name, mdl in models.items():
        t_s = time.time()
        mdl.fit(X_s[tr_idx], y_train[tr_idx])
        oof[name][val_idx]  = mdl.predict_proba(X_s[val_idx])[:, 1]
        preds[name]        += mdl.predict_proba(Xte_s)[:, 1] / 3
        acc = accuracy_score(y_train[val_idx], oof[name][val_idx] >= 0.5)
        print(f"    {name}: {acc:.4f}  ({time.time()-t_s:.1f}s)")

print("\n--- Per-Model OOF Accuracy ---")
weights = {}
for name in models:
    best_a, best_t = 0, 0.5
    for t in np.linspace(0.3, 0.7, 81):
        a = accuracy_score(y_train, oof[name] >= t)
        if a > best_a: best_a, best_t = a, t
    weights[name] = best_a
    print(f"  {name}: {best_a:.4f} @ thresh={best_t:.3f}")

# GILE-weighted ensemble (weight = OOF accuracy)
w_total = sum(weights.values())
ensemble_prob = sum(preds[k] * weights[k] / w_total for k in models)
oof_ensemble  = sum(oof[k] * weights[k] / w_total for k in models)

best_acc, best_thresh = 0, 0.5
for thresh in np.linspace(0.30, 0.70, 81):
    acc = accuracy_score(y_train, oof_ensemble >= thresh)
    if acc > best_acc: best_acc, best_thresh = acc, thresh

print(f"\n{'='*60}")
print(f"ENSEMBLE OOF ACCURACY = {best_acc:.4f} @ thresh={best_thresh:.3f}")
print(f"  v1 (HGB 200k):  0.8856")
print(f"  v2 (HGB 630k):  0.8869")
print(f"  v3 (Clinical+Ensemble): {best_acc:.4f}")
improvement = (best_acc - 0.8869) * 100
print(f"  v3 vs v2 improvement: {improvement:+.2f} pp")
print(f"{'='*60}")

# Feature importance from ExtraTrees
ext_model = models['EXT']
if hasattr(ext_model, 'feature_importances_'):
    imp = ext_model.feature_importances_
    top  = np.argsort(imp)[-15:][::-1]
    print(f"\nTop 15 features (ExtraTrees):")
    for rank, idx in enumerate(top):
        n = feat_names[idx] if idx < len(feat_names) else f'feat_{idx}'
        print(f"  {rank+1:2d}. {n}: {imp[idx]:.4f}")

print("\n[4/4] Generating deadline submission...")
y_pred      = (ensemble_prob >= best_thresh).astype(int)
pred_labels = np.where(y_pred == 1, 'Presence', 'Absence')
sub         = pd.DataFrame({'id': test_ids, 'Heart Disease': pred_labels})
out         = os.path.join(os.path.dirname(__file__), 'submission_heart_v3_deadline.csv')
sub.to_csv(out, index=False)
print(f"  Saved: {out}")
print(f"  Predicted Presence: {y_pred.sum():,} / {len(y_pred):,} ({y_pred.mean()*100:.1f}%)")
print(f"\n>>> UPLOAD THIS FILE TO KAGGLE TODAY: {out}")
print("\n" + "="*70)
print("TI HEART DISEASE v3 COMPLETE — DEADLINE SUBMISSION READY")
print("="*70)
