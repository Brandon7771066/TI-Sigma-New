"""
TI FAST AGGRESSIVE SOLVER
Faster version with aggressive features
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI FAST AGGRESSIVE SOLVER")
print("="*70)

train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')
test_ids = test['id']
y = train['exam_score'].values

# Target encoding (fast version)
cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']

global_mean = y.mean()
for col in cat_cols:
    means = train.groupby(col)['exam_score'].mean()
    train[f'{col}_te'] = train[col].map(means).fillna(global_mean)
    test[f'{col}_te'] = test[col].map(means).fillna(global_mean)

# Feature engineering
def engineer(df):
    df = df.copy()
    df['study_sq'] = df['study_hours'] ** 2
    df['study_cube'] = df['study_hours'] ** 3
    df['study_sqrt'] = np.sqrt(df['study_hours'])
    df['study_log'] = np.log1p(df['study_hours'])
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_att_sq'] = df['study_att'] ** 2
    df['study_sleep'] = df['study_hours'] * df['sleep_hours']
    df['sleep_dev'] = abs(df['sleep_hours'] - 7.5)
    
    for col in ['gender', 'course', 'study_method']:
        df[f'{col}_enc'] = pd.factorize(df[col].astype(str))[0]
    
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
    
    return df

train = engineer(train)
test = engineer(test)

feature_cols = [
    'age', 'study_hours', 'class_attendance', 'sleep_hours',
    'study_sq', 'study_cube', 'study_sqrt', 'study_log',
    'study_att', 'study_att_sq', 'study_sleep', 'sleep_dev',
    'gender_enc', 'course_enc', 'study_method_enc',
    'sleep_q', 'facility', 'diff', 'inet',
    'study_diff', 'study_fac'
] + [f'{c}_te' for c in cat_cols]

X = train[feature_cols].fillna(0)
X_test = test[feature_cols].fillna(0)

print(f"Features: {len(feature_cols)}")

# Training
kf = KFold(n_splits=5, shuffle=True, random_state=42)
test_preds = np.zeros(len(X_test))
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    m1 = HistGradientBoostingRegressor(
        max_iter=400, max_depth=8, learning_rate=0.04,
        l2_regularization=0.02, max_bins=255,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=42
    )
    m1.fit(X_tr, y_tr)
    p1 = m1.predict(X_val)
    t1 = m1.predict(X_test)
    
    m2 = HistGradientBoostingRegressor(
        max_iter=500, max_depth=5, learning_rate=0.03,
        l2_regularization=0.05, max_bins=255,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=43
    )
    m2.fit(X_tr, y_tr)
    p2 = m2.predict(X_val)
    t2 = m2.predict(X_test)
    
    val_pred = 0.6 * p1 + 0.4 * p2
    test_pred = 0.6 * t1 + 0.4 * t2
    
    test_preds += test_pred / 5
    rmse = np.sqrt(mean_squared_error(y_val, val_pred))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv_score = np.mean(scores)
print(f"\nCV RMSE: {cv_score:.4f} | Target: 8.50 | Leader: 8.53")
print(f"Gap to leader: {cv_score - 8.53:+.4f}")

sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_fast_agg.csv', index=False)
print(f"Saved: submission_fast_agg.csv")
