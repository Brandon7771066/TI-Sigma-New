"""
TI SIGMA AGGRESSIVE SOLVER
Target: Below 8.50 RMSE

Current gap: 8.80 → 8.53 = 0.27 to close

AGGRESSIVE STRATEGIES:
1. Target Encoding (mean encoding) - captures category-target relationships
2. K-Fold Target Encoding (prevents leakage)
3. More polynomial features on study_hours
4. Interaction features
5. Optimized hyperparameters
6. Multiple diverse models
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import LabelEncoder, StandardScaler
from sklearn.ensemble import HistGradientBoostingRegressor, ExtraTreesRegressor
from sklearn.linear_model import Ridge, HuberRegressor, ElasticNet
from sklearn.metrics import mean_squared_error
from collections import defaultdict
import warnings
warnings.filterwarnings('ignore')

np.random.seed(42)

print("="*70)
print("TI SIGMA AGGRESSIVE SOLVER")
print("Target: < 8.50 RMSE (Current leader: 8.53)")
print("="*70)

# Load data
train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')
test_ids = test['id']

print(f"Train: {len(train):,} | Test: {len(test):,}")

target = 'exam_score'
y = train[target].values

# === TARGET ENCODING (KEY TECHNIQUE) ===
print("\n" + "="*70)
print("TARGET ENCODING (K-Fold to prevent leakage)")
print("="*70)

cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']

def target_encode_kfold(train_df, test_df, cat_col, target_col, n_splits=5):
    """K-Fold target encoding to prevent leakage."""
    train_enc = np.zeros(len(train_df))
    test_enc = np.zeros(len(test_df))
    
    global_mean = train_df[target_col].mean()
    kf = KFold(n_splits=n_splits, shuffle=True, random_state=42)
    
    for train_idx, val_idx in kf.split(train_df):
        # Calculate means on train fold
        means = train_df.iloc[train_idx].groupby(cat_col)[target_col].mean()
        # Apply to validation fold
        train_enc[val_idx] = train_df.iloc[val_idx][cat_col].map(means).fillna(global_mean)
    
    # For test, use full train means
    full_means = train_df.groupby(cat_col)[target_col].mean()
    test_enc = test_df[cat_col].map(full_means).fillna(global_mean).values
    
    return train_enc, test_enc

# Apply target encoding
for col in cat_cols:
    train_enc, test_enc = target_encode_kfold(train, test, col, target)
    train[f'{col}_te'] = train_enc
    test[f'{col}_te'] = test_enc
    print(f"  {col}: encoded")

# === AGGRESSIVE FEATURE ENGINEERING ===
print("\n" + "="*70)
print("AGGRESSIVE FEATURE ENGINEERING")
print("="*70)

def engineer_aggressive(df):
    df = df.copy()
    
    # study_hours is king (r=0.76)
    df['study_sq'] = df['study_hours'] ** 2
    df['study_cube'] = df['study_hours'] ** 3
    df['study_4th'] = df['study_hours'] ** 4
    df['study_sqrt'] = np.sqrt(df['study_hours'])
    df['study_log'] = np.log1p(df['study_hours'])
    df['study_exp'] = 1 - np.exp(-df['study_hours'] / 5)  # Saturation curve
    
    # Attendance
    df['att_sq'] = df['class_attendance'] ** 2
    df['att_log'] = np.log1p(df['class_attendance'])
    
    # Interactions
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_att_sq'] = df['study_att'] ** 2
    df['study_att_log'] = np.log1p(df['study_att'])
    df['study_sleep'] = df['study_hours'] * df['sleep_hours']
    
    # Sleep optimization
    df['sleep_dev'] = abs(df['sleep_hours'] - 7.5)
    df['sleep_optimal'] = ((df['sleep_hours'] >= 6) & (df['sleep_hours'] <= 9)).astype(float)
    
    # Categorical numerics
    sleep_map = {'poor': 0, 'average': 1, 'good': 2}
    fac_map = {'low': 0, 'medium': 1, 'high': 2}
    diff_map = {'easy': 2, 'moderate': 1, 'hard': 0}
    inet_map = {'no': 0, 'yes': 1}
    
    df['sleep_q'] = df['sleep_quality'].str.lower().map(sleep_map).fillna(1)
    df['facility'] = df['facility_rating'].str.lower().map(fac_map).fillna(1)
    df['diff'] = df['exam_difficulty'].str.lower().map(diff_map).fillna(1)
    df['inet'] = df['internet_access'].str.lower().map(inet_map).fillna(0.5)
    
    # More interactions
    df['study_diff'] = df['study_hours'] * (df['diff'] + 1)
    df['study_fac'] = df['study_hours'] * (df['facility'] + 1)
    df['study_sleep_q'] = df['study_hours'] * (df['sleep_q'] + 1)
    df['att_diff'] = df['class_attendance'] * (df['diff'] + 1) / 100
    
    # Ratios
    df['study_per_sleep'] = df['study_hours'] / (df['sleep_hours'] + 0.1)
    df['efficiency'] = df['study_hours'] * df['class_attendance'] / (df['age'] + 1)
    
    # Label encode remaining cats
    for col in ['gender', 'course', 'study_method']:
        df[f'{col}_enc'] = pd.factorize(df[col].astype(str))[0]
    
    return df

train = engineer_aggressive(train)
test = engineer_aggressive(test)

# === FEATURE LIST ===
num_cols = ['age', 'study_hours', 'class_attendance', 'sleep_hours']
te_cols = [f'{c}_te' for c in cat_cols]
eng_cols = [
    'study_sq', 'study_cube', 'study_4th', 'study_sqrt', 'study_log', 'study_exp',
    'att_sq', 'att_log',
    'study_att', 'study_att_sq', 'study_att_log', 'study_sleep',
    'sleep_dev', 'sleep_optimal',
    'sleep_q', 'facility', 'diff', 'inet',
    'study_diff', 'study_fac', 'study_sleep_q', 'att_diff',
    'study_per_sleep', 'efficiency',
    'gender_enc', 'course_enc', 'study_method_enc'
]

feature_cols = num_cols + te_cols + eng_cols
print(f"Total features: {len(feature_cols)}")

X = train[feature_cols].fillna(0).replace([np.inf, -np.inf], 0)
X_test = test[feature_cols].fillna(0).replace([np.inf, -np.inf], 0)

# === TRAIN MULTIPLE MODELS ===
print("\n" + "="*70)
print("TRAINING DIVERSE ENSEMBLE")
print("="*70)

kf = KFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = np.zeros(len(X))
test_preds_list = []
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    fold_test_preds = []
    
    # Model 1: Deep HistGB
    m1 = HistGradientBoostingRegressor(
        max_iter=800, max_depth=10, learning_rate=0.03,
        l2_regularization=0.01, max_bins=255, min_samples_leaf=20,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=50, random_state=42
    )
    m1.fit(X_tr, y_tr)
    p1 = m1.predict(X_val)
    fold_test_preds.append(m1.predict(X_test))
    
    # Model 2: Shallow HistGB
    m2 = HistGradientBoostingRegressor(
        max_iter=1000, max_depth=5, learning_rate=0.02,
        l2_regularization=0.05, max_bins=255, min_samples_leaf=50,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=50, random_state=43
    )
    m2.fit(X_tr, y_tr)
    p2 = m2.predict(X_val)
    fold_test_preds.append(m2.predict(X_test))
    
    # Model 3: Very deep HistGB
    m3 = HistGradientBoostingRegressor(
        max_iter=500, max_depth=15, learning_rate=0.05,
        l2_regularization=0.001, max_bins=255, min_samples_leaf=10,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=44
    )
    m3.fit(X_tr, y_tr)
    p3 = m3.predict(X_val)
    fold_test_preds.append(m3.predict(X_test))
    
    # Model 4: Ridge
    scaler = StandardScaler()
    X_tr_s = scaler.fit_transform(X_tr)
    X_val_s = scaler.transform(X_val)
    X_test_s = scaler.transform(X_test)
    
    m4 = Ridge(alpha=1.0)
    m4.fit(X_tr_s, y_tr)
    p4 = m4.predict(X_val_s)
    fold_test_preds.append(m4.predict(X_test_s))
    
    # Blend (optimize weights)
    val_pred = 0.35 * p1 + 0.30 * p2 + 0.25 * p3 + 0.10 * p4
    test_pred = 0.35 * fold_test_preds[0] + 0.30 * fold_test_preds[1] + 0.25 * fold_test_preds[2] + 0.10 * fold_test_preds[3]
    
    oof_preds[val_idx] = val_pred
    test_preds_list.append(test_pred)
    
    rmse = np.sqrt(mean_squared_error(y_val, val_pred))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

test_preds = np.mean(test_preds_list, axis=0)
cv_score = np.mean(scores)

print(f"\n{'='*50}")
print(f"CV RMSE: {cv_score:.4f} (+/- {np.std(scores):.4f})")
print(f"Target: 8.50 | Gap: {cv_score - 8.50:+.4f}")
print(f"Leader: 8.53 | Gap: {cv_score - 8.53:+.4f}")
print(f"{'='*50}")

# Save
sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_aggressive.csv', index=False)
print(f"\nSaved: submission_aggressive.csv")
