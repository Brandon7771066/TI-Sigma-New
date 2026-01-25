"""
TI SIGMA FINAL SOLVER
Maximum performance version

KEY INSIGHT FROM LCC:
study_hours alone explains 76% of variance!
Focus ALL optimization on study_hours relationships.
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import LabelEncoder, StandardScaler, PolynomialFeatures
from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI SIGMA FINAL SOLVER - Maximum Performance")
print("="*70)

train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')
test_ids = test['id']

print(f"Train: {len(train):,} | Test: {len(test):,}")

# === FEATURE ENGINEERING: Focus on study_hours ===

def engineer_features(df):
    df = df.copy()
    
    # study_hours is king (r=0.76)
    df['study_sq'] = df['study_hours'] ** 2
    df['study_cube'] = df['study_hours'] ** 3
    df['study_sqrt'] = np.sqrt(df['study_hours'])
    df['study_log'] = np.log1p(df['study_hours'])
    
    # attendance interaction
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_att_sq'] = df['study_att'] ** 2
    
    # sleep interaction
    df['study_sleep'] = df['study_hours'] * df['sleep_hours']
    
    # categorical numerics
    sleep_map = {'poor': 0, 'average': 1, 'good': 2}
    fac_map = {'low': 0, 'medium': 1, 'high': 2}
    diff_map = {'easy': 2, 'moderate': 1, 'hard': 0}  # inverted: easy = bonus
    inet_map = {'no': 0, 'yes': 1}
    
    df['sleep_q'] = df['sleep_quality'].str.lower().map(sleep_map).fillna(1)
    df['facility'] = df['facility_rating'].str.lower().map(fac_map).fillna(1)
    df['diff'] = df['exam_difficulty'].str.lower().map(diff_map).fillna(1)
    df['inet'] = df['internet_access'].str.lower().map(inet_map).fillna(0.5)
    
    # combined
    df['resources'] = df['inet'] + df['facility']/2
    df['study_diff'] = df['study_hours'] * (df['diff'] + 1)
    
    # label encode categoricals
    cat_cols = ['gender', 'course', 'study_method']
    for col in cat_cols:
        if col not in df.columns:
            continue
        df[col + '_enc'] = pd.factorize(df[col].astype(str))[0]
    
    return df

train = engineer_features(train)
test = engineer_features(test)

# Features
feature_cols = [
    'age', 'study_hours', 'class_attendance', 'sleep_hours',
    'study_sq', 'study_cube', 'study_sqrt', 'study_log',
    'study_att', 'study_att_sq', 'study_sleep',
    'sleep_q', 'facility', 'diff', 'inet', 'resources', 'study_diff',
    'gender_enc', 'course_enc', 'study_method_enc'
]

X = train[feature_cols].fillna(0)
y = train['exam_score'].values
X_test = test[feature_cols].fillna(0)

print(f"Features: {len(feature_cols)}")

# === TRIPLE ENSEMBLE ===
print("\n" + "="*70)
print("TRAINING TRIPLE ENSEMBLE")
print("="*70)

kf = KFold(n_splits=5, shuffle=True, random_state=42)
test_preds = np.zeros(len(X_test))
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # Model 1: Deep trees
    m1 = HistGradientBoostingRegressor(
        max_iter=600, max_depth=9, learning_rate=0.04,
        l2_regularization=0.02, max_bins=255,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=42
    )
    m1.fit(X_tr, y_tr)
    p1_val = m1.predict(X_val)
    p1_test = m1.predict(X_test)
    
    # Model 2: Shallow trees (different view)
    m2 = HistGradientBoostingRegressor(
        max_iter=800, max_depth=5, learning_rate=0.03,
        l2_regularization=0.1, max_bins=255,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=43
    )
    m2.fit(X_tr, y_tr)
    p2_val = m2.predict(X_val)
    p2_test = m2.predict(X_test)
    
    # Model 3: Ridge
    scaler = StandardScaler()
    X_tr_s = scaler.fit_transform(X_tr)
    X_val_s = scaler.transform(X_val)
    X_test_s = scaler.transform(X_test)
    
    m3 = Ridge(alpha=5.0)
    m3.fit(X_tr_s, y_tr)
    p3_val = m3.predict(X_val_s)
    p3_test = m3.predict(X_test_s)
    
    # Weighted blend
    val_pred = 0.5 * p1_val + 0.35 * p2_val + 0.15 * p3_val
    test_pred = 0.5 * p1_test + 0.35 * p2_test + 0.15 * p3_test
    
    test_preds += test_pred / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, val_pred))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv_score = np.mean(scores)
print(f"\n{'='*50}")
print(f"FINAL CV RMSE: {cv_score:.4f} (+/- {np.std(scores):.4f})")
print(f"Target: 8.76 | Gap: {cv_score - 8.76:+.4f}")
print(f"{'='*50}")

# Save
sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_final.csv', index=False)
print(f"\nSaved: submission_final.csv")
print(f"Mean: {test_preds.mean():.2f}, Std: {test_preds.std():.2f}")
