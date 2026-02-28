"""
TI Heart Disease v4 — FAST CLINICAL ENSEMBLE (FINAL DEADLINE)
==============================================================
Lessons from v3: clean 51 clinical features better than 150 noisy HC.
ExtraTrees too slow and underperforms HGB. LR surprisingly competitive.

This version: HGB + LR ensemble, 2-fold, runs in ~90 seconds.
Goal: push past 88.69% with cleaner feature set.

Feb 28, 2026 — COMPETITION DEADLINE
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import pandas as pd
import time
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import accuracy_score
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI HEART DISEASE v4 — FAST CLINICAL ENSEMBLE (FINAL DEADLINE)")
print("=" * 70)

DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'data', 'kaggle_s6e2')

print("[1/3] Loading full 630k dataset...")
train = pd.read_csv(os.path.join(DATA_DIR, 'train.csv'))
test  = pd.read_csv(os.path.join(DATA_DIR, 'test.csv'))

y_train  = (train['Heart Disease'] == 'Presence').astype(int).values
test_ids = test['id'].values
X_raw    = train.drop(columns=['id', 'Heart Disease'])
X_te_raw = test.drop(columns=['id'])

PHI = 1.61803398875

def engineer_features(df):
    age  = df['Age'].values.astype(float)
    sex  = df['Sex'].values.astype(float)
    cp   = df['Chest pain type'].values.astype(float)
    bp   = df['BP'].values.astype(float)
    chol = df['Cholesterol'].values.astype(float)
    fbs  = df['FBS over 120'].values.astype(float)
    ekg  = df['EKG results'].values.astype(float)
    mhr  = df['Max HR'].values.astype(float)
    ea   = df['Exercise angina'].values.astype(float)
    st   = df['ST depression'].values.astype(float)
    slp  = df['Slope of ST'].values.astype(float)
    nv   = df['Number of vessels fluro'].values.astype(float)
    thal = df['Thallium'].values.astype(float)

    # Categoricals as raw + one-hot
    raw = np.column_stack([age, sex, cp, bp, chol, fbs, ekg, mhr, ea, st, slp, nv, thal])
    ohe = np.column_stack([
        (cp == 1).astype(float), (cp == 2).astype(float),
        (cp == 3).astype(float), (cp == 4).astype(float),
        (ekg == 0).astype(float), (ekg == 2).astype(float),
        (slp == 1).astype(float), (slp == 2).astype(float), (slp == 3).astype(float),
        (thal == 3).astype(float), (thal == 6).astype(float), (thal == 7).astype(float),
        (nv == 0).astype(float), (nv == 1).astype(float),
        (nv == 2).astype(float), (nv == 3).astype(float),
    ])

    # Clinical interactions (strongest by domain knowledge)
    cardiac_risk  = age * st * ea                                # L×E triple (×15 separation)
    nv_thal7      = nv * (thal == 7).astype(float)              # multi-vessel reversible
    cp4_st        = (cp == 4).astype(float) * st                # asymptomatic + ischemia
    hr_reserve    = mhr / np.clip(220 - age, 80, 220)
    bp_hr_prod    = bp * mhr / 10000.0
    thal7_age     = (thal == 7).astype(float) * age / 60.0
    chol_age      = chol * age / 10000.0
    log_st_age    = np.log1p(np.abs(st) * age)
    phi_age       = (age - 42) / (PHI * 42)
    multi_vessel  = (nv >= 2).astype(float)
    high_risk     = (nv >= 2).astype(float) * (thal == 7).astype(float)
    age_sex       = age * sex
    nv_st         = nv * st
    slp2_st       = (slp == 2).astype(float) * st               # flat slope + ischemia
    asymp_ea      = (cp == 4).astype(float) * ea
    chol_lt200    = (chol < 200).astype(float)                  # low cholesterol protective
    mhr_deficit   = np.clip(220 - age - mhr, 0, 100)            # max HR deficit

    ixn = np.column_stack([
        cardiac_risk, nv_thal7, cp4_st, hr_reserve, bp_hr_prod,
        thal7_age, chol_age, log_st_age, phi_age, multi_vessel,
        high_risk, age_sex, nv_st, slp2_st, asymp_ea,
        chol_lt200, mhr_deficit,
    ])

    # Polynomial on top-5 raw features (nv, thal, cp, st, ea)
    top5 = np.column_stack([nv, thal, cp, st, ea])
    poly = []
    for i in range(top5.shape[1]):
        for j in range(i, top5.shape[1]):
            poly.append(top5[:, i] * top5[:, j])
    poly = np.column_stack(poly)

    return np.hstack([raw, ohe, ixn, poly])

print("[2/3] Engineering features...")
t0 = time.time()
X_feat    = engineer_features(X_raw)
X_te_feat = engineer_features(X_te_raw)
print(f"  {X_feat.shape[1]} features built in {time.time()-t0:.1f}s")

scaler = StandardScaler()
X_s    = scaler.fit_transform(X_feat)
Xte_s  = scaler.transform(X_te_feat)

print("[3/3] Training HGB + LR ensemble (2-fold)...")
cv = StratifiedKFold(n_splits=2, shuffle=True, random_state=42)

hgb = HistGradientBoostingClassifier(
    learning_rate=0.04, max_iter=300, max_depth=8,
    min_samples_leaf=20, l2_regularization=0.2,
    max_features=0.9, random_state=42
)
lr = LogisticRegression(C=0.3, max_iter=1000, solver='lbfgs', n_jobs=-1)

oof_hgb = np.zeros(len(X_s)); pred_hgb = np.zeros(len(Xte_s))
oof_lr  = np.zeros(len(X_s)); pred_lr  = np.zeros(len(Xte_s))

for fold, (tr, val) in enumerate(cv.split(X_s, y_train)):
    t_f = time.time()
    hgb.fit(X_s[tr], y_train[tr])
    oof_hgb[val] = hgb.predict_proba(X_s[val])[:, 1]
    pred_hgb    += hgb.predict_proba(Xte_s)[:, 1] / 2
    h_acc = accuracy_score(y_train[val], oof_hgb[val] >= 0.5)

    lr.fit(X_s[tr], y_train[tr])
    oof_lr[val] = lr.predict_proba(X_s[val])[:, 1]
    pred_lr    += lr.predict_proba(Xte_s)[:, 1] / 2
    l_acc = accuracy_score(y_train[val], oof_lr[val] >= 0.5)

    print(f"  Fold {fold+1}: HGB={h_acc:.4f}  LR={l_acc:.4f}  ({time.time()-t_f:.1f}s)")

# Tune weights
best_acc, best_thresh, best_w = 0, 0.5, 0.7
for w in np.linspace(0.4, 1.0, 13):        # w = HGB weight
    blended_oof = w * oof_hgb + (1-w) * oof_lr
    for t in np.linspace(0.3, 0.7, 81):
        a = accuracy_score(y_train, blended_oof >= t)
        if a > best_acc: best_acc, best_thresh, best_w = a, t, w

ensemble_prob = best_w * pred_hgb + (1-best_w) * pred_lr
y_pred = (ensemble_prob >= best_thresh).astype(int)

print(f"\n{'='*60}")
print(f"FINAL ENSEMBLE OOF ACCURACY = {best_acc:.4f}")
print(f"  HGB weight={best_w:.2f}  LR weight={1-best_w:.2f}  thresh={best_thresh:.3f}")
print(f"  v2 (HGB 630k):           0.8869")
print(f"  v4 (Clinical Ensemble):  {best_acc:.4f}  ({(best_acc-0.8869)*100:+.2f} pp)")
print(f"{'='*60}")

pred_labels = np.where(y_pred == 1, 'Presence', 'Absence')
sub = pd.DataFrame({'id': test_ids, 'Heart Disease': pred_labels})
out = os.path.join(os.path.dirname(__file__), 'submission_heart_v4_final.csv')
sub.to_csv(out, index=False)
print(f"\n>>> DEADLINE SUBMISSION: {out}")
print(f"    Predicted Presence: {y_pred.sum():,} / {len(y_pred):,} ({y_pred.mean()*100:.1f}%)")
