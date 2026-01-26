"""
TI NEURAL SOLVER - Using MLP Neural Network
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import StandardScaler, PolynomialFeatures
from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.neural_network import MLPRegressor
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI NEURAL SOLVER (HistGB + MLP Ensemble)")
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

# Minimal but effective features
def engineer(df):
    df = df.copy()
    df['study_sq'] = df['study_hours'] ** 2
    df['study_att'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_log'] = np.log1p(df['study_hours'])
    
    sleep_map = {'poor': 0, 'average': 1, 'good': 2}
    fac_map = {'low': 0, 'medium': 1, 'high': 2}
    diff_map = {'easy': 2, 'moderate': 1, 'hard': 0}
    
    df['sleep_q'] = df['sleep_quality'].str.lower().map(sleep_map).fillna(1)
    df['facility'] = df['facility_rating'].str.lower().map(fac_map).fillna(1)
    df['diff'] = df['exam_difficulty'].str.lower().map(diff_map).fillna(1)
    
    return df

train = engineer(train)
test = engineer(test)

feature_cols = [
    'age', 'study_hours', 'class_attendance', 'sleep_hours',
    'study_sq', 'study_att', 'study_log',
    'sleep_q', 'facility', 'diff'
] + [f'{c}_te' for c in cat_cols]

X = train[feature_cols].fillna(0)
X_test = test[feature_cols].fillna(0)

print(f"Base features: {len(feature_cols)}")

# Scale for MLP
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
X_test_scaled = scaler.transform(X_test)

# Training
kf = KFold(n_splits=5, shuffle=True, random_state=42)
test_preds_hgb = np.zeros(len(X_test))
test_preds_mlp = np.zeros(len(X_test))
scores_hgb = []
scores_mlp = []
scores_blend = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_tr, X_val = X.iloc[train_idx], X.iloc[val_idx]
    X_tr_s, X_val_s = X_scaled[train_idx], X_scaled[val_idx]
    y_tr, y_val = y[train_idx], y[val_idx]
    
    # HistGB
    m1 = HistGradientBoostingRegressor(
        max_iter=500, max_depth=8, learning_rate=0.04,
        l2_regularization=0.02, max_bins=255,
        early_stopping=True, validation_fraction=0.1,
        n_iter_no_change=30, random_state=42
    )
    m1.fit(X_tr, y_tr)
    p1 = m1.predict(X_val)
    test_preds_hgb += m1.predict(X_test) / 5
    
    # MLP (smaller sample for speed)
    sample_size = min(100000, len(X_tr_s))
    idx = np.random.choice(len(X_tr_s), sample_size, replace=False)
    
    m2 = MLPRegressor(
        hidden_layer_sizes=(128, 64, 32),
        activation='relu',
        solver='adam',
        alpha=0.001,
        batch_size=256,
        learning_rate='adaptive',
        learning_rate_init=0.001,
        max_iter=100,
        early_stopping=True,
        validation_fraction=0.1,
        n_iter_no_change=10,
        random_state=42
    )
    m2.fit(X_tr_s[idx], y_tr[idx])
    p2 = m2.predict(X_val_s)
    test_preds_mlp += m2.predict(X_test_scaled) / 5
    
    rmse_hgb = np.sqrt(mean_squared_error(y_val, p1))
    rmse_mlp = np.sqrt(mean_squared_error(y_val, p2))
    
    # Blend
    blend = 0.7 * p1 + 0.3 * p2
    rmse_blend = np.sqrt(mean_squared_error(y_val, blend))
    
    scores_hgb.append(rmse_hgb)
    scores_mlp.append(rmse_mlp)
    scores_blend.append(rmse_blend)
    
    print(f"Fold {fold+1}: HGB={rmse_hgb:.4f} | MLP={rmse_mlp:.4f} | Blend={rmse_blend:.4f}")

print(f"\nCV HGB: {np.mean(scores_hgb):.4f}")
print(f"CV MLP: {np.mean(scores_mlp):.4f}")
print(f"CV Blend: {np.mean(scores_blend):.4f}")

# Final predictions
test_preds = 0.7 * test_preds_hgb + 0.3 * test_preds_mlp

sub = pd.DataFrame({'id': test_ids, 'exam_score': test_preds})
sub.to_csv('submission_neural.csv', index=False)
print(f"\nSaved: submission_neural.csv")
print(f"Target: 8.50 | Leader: 8.53")
