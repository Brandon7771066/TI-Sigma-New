"""
TI STACKING SOLVER
Multi-layer stacking ensemble
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import (
    HistGradientBoostingRegressor, 
    RandomForestRegressor,
    ExtraTreesRegressor,
    StackingRegressor
)
from sklearn.linear_model import Ridge, ElasticNet, HuberRegressor
from sklearn.svm import SVR
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI STACKING SOLVER (Multi-layer Ensemble)")
print("="*70)

train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')
test_ids = test['id']
y = train['exam_score'].values

# Target encoding
cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']
global_mean = y.mean()
for col in cat_cols:
    means = train.groupby(col)['exam_score'].mean()
    train[f'{col}_te'] = train[col].map(means).fillna(global_mean)
    test[f'{col}_te'] = test[col].map(means).fillna(global_mean)

# Features
def engineer(df):
    df = df.copy()
    df['study_sq'] = df['study_hours'] ** 2
    df['study_cube'] = df['study_hours'] ** 3
    df['study_sqrt'] = np.sqrt(df['study_hours'])
    df['study_log'] = np.log1p(df['study_hours'])
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_att_sq'] = df['study_att'] ** 2
    
    sleep_map = {'poor': 0, 'average': 1, 'good': 2}
    fac_map = {'low': 0, 'medium': 1, 'high': 2}
    diff_map = {'easy': 2, 'moderate': 1, 'hard': 0}
    inet_map = {'no': 0, 'yes': 1}
    
    df['sleep_q'] = df['sleep_quality'].str.lower().map(sleep_map).fillna(1)
    df['facility'] = df['facility_rating'].str.lower().map(fac_map).fillna(1)
    df['diff'] = df['exam_difficulty'].str.lower().map(diff_map).fillna(1)
    df['inet'] = df['internet_access'].str.lower().map(inet_map).fillna(0.5)
    
    df['study_diff'] = df['study_hours'] * (df['diff'] + 1)
    
    for col in ['gender', 'course', 'study_method']:
        df[f'{col}_enc'] = pd.factorize(df[col].astype(str))[0]
    
    return df

train = engineer(train)
test = engineer(test)

feature_cols = [
    'age', 'study_hours', 'class_attendance', 'sleep_hours',
    'study_sq', 'study_cube', 'study_sqrt', 'study_log',
    'study_att', 'study_att_sq',
    'sleep_q', 'facility', 'diff', 'inet', 'study_diff',
    'gender_enc', 'course_enc', 'study_method_enc'
] + [f'{c}_te' for c in cat_cols]

X = train[feature_cols].fillna(0)
X_test = test[feature_cols].fillna(0)

print(f"Features: {len(feature_cols)}")

# Scale
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
X_test_scaled = scaler.transform(X_test)

# Manual stacking (faster than StackingRegressor)
kf = KFold(n_splits=5, shuffle=True, random_state=42)

# Level 1: Generate OOF predictions from diverse models
print("\n=== Level 1: Base Models ===")

oof_hgb1 = np.zeros(len(X))
oof_hgb2 = np.zeros(len(X))
oof_hgb3 = np.zeros(len(X))
oof_ridge = np.zeros(len(X))

test_hgb1 = np.zeros(len(X_test))
test_hgb2 = np.zeros(len(X_test))
test_hgb3 = np.zeros(len(X_test))
test_ridge = np.zeros(len(X_test))

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    X_tr_s, X_val_s = X_scaled[train_idx], X_scaled[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # HGB 1: Deep trees
    m1 = HistGradientBoostingRegressor(
        max_iter=600, max_depth=10, learning_rate=0.03,
        l2_regularization=0.01, max_bins=255, min_samples_leaf=15,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=40, random_state=42
    )
    m1.fit(X_tr, y_tr)
    oof_hgb1[val_idx] = m1.predict(X_val)
    test_hgb1 += m1.predict(X_test) / 5
    
    # HGB 2: Shallow trees
    m2 = HistGradientBoostingRegressor(
        max_iter=800, max_depth=5, learning_rate=0.025,
        l2_regularization=0.05, max_bins=255, min_samples_leaf=30,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=40, random_state=43
    )
    m2.fit(X_tr, y_tr)
    oof_hgb2[val_idx] = m2.predict(X_val)
    test_hgb2 += m2.predict(X_test) / 5
    
    # HGB 3: Mid-depth, higher LR
    m3 = HistGradientBoostingRegressor(
        max_iter=400, max_depth=7, learning_rate=0.05,
        l2_regularization=0.02, max_bins=255, min_samples_leaf=20,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=40, random_state=44
    )
    m3.fit(X_tr, y_tr)
    oof_hgb3[val_idx] = m3.predict(X_val)
    test_hgb3 += m3.predict(X_test) / 5
    
    # Ridge
    m4 = Ridge(alpha=1.0)
    m4.fit(X_tr_s, y_tr)
    oof_ridge[val_idx] = m4.predict(X_val_s)
    test_ridge += m4.predict(X_test_scaled) / 5
    
    print(f"Fold {fold+1}: HGB1={np.sqrt(mean_squared_error(y_val, oof_hgb1[val_idx])):.4f}, "
          f"HGB2={np.sqrt(mean_squared_error(y_val, oof_hgb2[val_idx])):.4f}")

print(f"\nHGB1 OOF RMSE: {np.sqrt(mean_squared_error(y, oof_hgb1)):.4f}")
print(f"HGB2 OOF RMSE: {np.sqrt(mean_squared_error(y, oof_hgb2)):.4f}")
print(f"HGB3 OOF RMSE: {np.sqrt(mean_squared_error(y, oof_hgb3)):.4f}")
print(f"Ridge OOF RMSE: {np.sqrt(mean_squared_error(y, oof_ridge)):.4f}")

# Level 2: Meta-model
print("\n=== Level 2: Meta Model ===")

X_meta = np.column_stack([oof_hgb1, oof_hgb2, oof_hgb3, oof_ridge])
X_meta_test = np.column_stack([test_hgb1, test_hgb2, test_hgb3, test_ridge])

meta_oof = np.zeros(len(X))
meta_test = np.zeros(len(X_test))

for fold, (train_idx, val_idx) in enumerate(kf.split(X_meta)):
    X_tr, X_val = X_meta[train_idx], X_meta[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    meta = Ridge(alpha=0.1)
    meta.fit(X_tr, y_tr)
    
    meta_oof[val_idx] = meta.predict(X_val)
    meta_test += meta.predict(X_meta_test) / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, meta_oof[val_idx]))
    print(f"Fold {fold+1}: Meta RMSE = {rmse:.4f}")

final_cv = np.sqrt(mean_squared_error(y, meta_oof))
print(f"\n{'='*50}")
print(f"STACKING CV RMSE: {final_cv:.4f}")
print(f"Target: 8.50 | Leader: 8.53 | Gap: {final_cv - 8.53:+.4f}")
print(f"{'='*50}")

# Simple average as backup
simple_blend = 0.35 * test_hgb1 + 0.35 * test_hgb2 + 0.20 * test_hgb3 + 0.10 * test_ridge
simple_oof = 0.35 * oof_hgb1 + 0.35 * oof_hgb2 + 0.20 * oof_hgb3 + 0.10 * oof_ridge
simple_cv = np.sqrt(mean_squared_error(y, simple_oof))
print(f"Simple Blend CV RMSE: {simple_cv:.4f}")

# Use best
if simple_cv < final_cv:
    print("Using simple blend")
    test_preds = simple_blend
    best_cv = simple_cv
else:
    print("Using stacked meta")
    test_preds = meta_test
    best_cv = final_cv

sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_stacked.csv', index=False)
print(f"\nSaved: submission_stacked.csv (CV: {best_cv:.4f})")
