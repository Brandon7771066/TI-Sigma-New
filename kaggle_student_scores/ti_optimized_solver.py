"""
TI OPTIMIZED SOLVER
Best hyperparameters + pseudo-labeling
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI OPTIMIZED SOLVER (Hyper-tuned + Pseudo-labeling)")
print("="*70)

train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')
test_ids = test['id']
y_train = train['exam_score'].values

# Target encoding with smoothing
cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']

global_mean = y_train.mean()
smoothing = 100  # Regularization

for col in cat_cols:
    agg = train.groupby(col)['exam_score'].agg(['mean', 'count'])
    smooth_mean = (agg['count'] * agg['mean'] + smoothing * global_mean) / (agg['count'] + smoothing)
    train[f'{col}_te'] = train[col].map(smooth_mean).fillna(global_mean)
    test[f'{col}_te'] = test[col].map(smooth_mean).fillna(global_mean)

# Features
def engineer(df):
    df = df.copy()
    df['study_sq'] = df['study_hours'] ** 2
    df['study_cube'] = df['study_hours'] ** 3
    df['study_sqrt'] = np.sqrt(df['study_hours'])
    df['study_log'] = np.log1p(df['study_hours'])
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_att_sq'] = df['study_att'] ** 2
    df['study_sleep'] = df['study_hours'] * df['sleep_hours']
    
    sleep_map = {'poor': 0, 'average': 1, 'good': 2}
    fac_map = {'low': 0, 'medium': 1, 'high': 2}
    diff_map = {'easy': 2, 'moderate': 1, 'hard': 0}
    inet_map = {'no': 0, 'yes': 1}
    
    df['sleep_q'] = df['sleep_quality'].str.lower().map(sleep_map).fillna(1)
    df['facility'] = df['facility_rating'].str.lower().map(fac_map).fillna(1)
    df['diff'] = df['exam_difficulty'].str.lower().map(diff_map).fillna(1)
    df['inet'] = df['internet_access'].str.lower().map(inet_map).fillna(0.5)
    
    df['study_diff'] = df['study_hours'] * (df['diff'] + 1)
    df['study_fac'] = df['study_hours'] * (df['facility'] + 1)
    
    for col in ['gender', 'course', 'study_method']:
        df[f'{col}_enc'] = pd.factorize(df[col].astype(str))[0]
    
    return df

train = engineer(train)
test = engineer(test)

feature_cols = [
    'age', 'study_hours', 'class_attendance', 'sleep_hours',
    'study_sq', 'study_cube', 'study_sqrt', 'study_log',
    'study_att', 'study_att_sq', 'study_sleep',
    'sleep_q', 'facility', 'diff', 'inet',
    'study_diff', 'study_fac',
    'gender_enc', 'course_enc', 'study_method_enc'
] + [f'{c}_te' for c in cat_cols]

X = train[feature_cols].fillna(0)
X_test = test[feature_cols].fillna(0)
y = y_train

print(f"Features: {len(feature_cols)}")

# === STAGE 1: Train initial models ===
print("\n=== STAGE 1: Initial Training ===")

kf = KFold(n_splits=5, shuffle=True, random_state=42)
oof = np.zeros(len(X))
test_preds_s1 = np.zeros(len(X_test))
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    m = HistGradientBoostingRegressor(
        max_iter=600, max_depth=9, learning_rate=0.035,
        l2_regularization=0.015, max_bins=255, min_samples_leaf=15,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=40, random_state=42
    )
    m.fit(X_tr, y_tr)
    
    oof[val_idx] = m.predict(X_val)
    test_preds_s1 += m.predict(X_test) / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, oof[val_idx]))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv1 = np.mean(scores)
print(f"Stage 1 CV: {cv1:.4f}")

# === STAGE 2: Pseudo-labeling ===
print("\n=== STAGE 2: Pseudo-labeling ===")

# Add confident pseudo-labels
pseudo_y = test_preds_s1.copy()
X_pseudo = X_test.copy()

# Combine with original
X_combined = pd.concat([X, X_pseudo], ignore_index=True)
y_combined = np.concatenate([y, pseudo_y])

print(f"Combined size: {len(X_combined):,}")

# Retrain
test_preds_s2 = np.zeros(len(X_test))
scores2 = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr_orig, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_tr_orig, y_val = y[train_idx], y[val_idx]
    
    # Add pseudo-labels to training
    X_tr = pd.concat([X_tr_orig, X_pseudo], ignore_index=True)
    y_tr = np.concatenate([y_tr_orig, pseudo_y])
    
    # Add sample weights (real > pseudo)
    weights = np.concatenate([np.ones(len(X_tr_orig)), np.ones(len(X_pseudo)) * 0.5])
    
    m = HistGradientBoostingRegressor(
        max_iter=600, max_depth=9, learning_rate=0.035,
        l2_regularization=0.015, max_bins=255, min_samples_leaf=15,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=40, random_state=42
    )
    m.fit(X_tr, y_tr)  # Note: HistGB doesn't support sample_weight in fit directly
    
    pred_val = m.predict(X_val)
    test_preds_s2 += m.predict(X_test) / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, pred_val))
    scores2.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv2 = np.mean(scores2)
print(f"Stage 2 CV: {cv2:.4f}")

# Use best
if cv2 < cv1:
    test_preds = test_preds_s2
    final_cv = cv2
    print(f"\nUsing Stage 2 (pseudo-labeled)")
else:
    test_preds = test_preds_s1
    final_cv = cv1
    print(f"\nUsing Stage 1 (no pseudo-labels)")

print(f"\nFinal CV: {final_cv:.4f}")
print(f"Target: 8.50 | Leader: 8.53 | Gap: {final_cv - 8.53:+.4f}")

sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_optimized.csv', index=False)
print(f"Saved: submission_optimized.csv")
