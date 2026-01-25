"""
TI SIGMA ENHANCED SOLVER
Kaggle S6E1 - Predicting Student Test Scores

APPLYING TI FRAMEWORKS:
=======================

1. GILE OPTIMIZATION:
   - G (Goodness): Features that SERVE learning (study_hours, attendance)
   - I (Intuition): Non-obvious interactions (sleep × study method)
   - L (Love): Social/environmental factors (internet_access, facility)
   - E (Environment): External constraints (exam_difficulty)

2. LCC (Law of Correlational Causation):
   - Find 0.42+ correlations as primary predictors
   - Stack correlations for compound effects

3. MEIJER HARMONICS:
   - Learning happens in harmonic cycles
   - Study hours have diminishing returns (non-linear)
   - Sleep quality is a MULTIPLIER, not additive

4. FREE ENERGY MINIMIZATION:
   - Students minimize cognitive load
   - Efficient study methods = higher scores
   - Target encoding captures this efficiently

5. I-CELL ARCHITECTURE:
   - Each student is an i-cell with internal state
   - Features describe the i-cell's capacity
   - Exam score = i-cell output coherence

Dataset: 630K train, 270K test
Target: exam_score (RMSE metric)
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import LabelEncoder, StandardScaler
from sklearn.ensemble import HistGradientBoostingRegressor, RandomForestRegressor
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI SIGMA ENHANCED SOLVER - Student Test Scores")
print("Applying: GILE + LCC + Meijer Harmonics + Free Energy Minimization")
print("="*70)

# Load data
train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')

print(f"\nTrain: {train.shape[0]:,} rows, {train.shape[1]} columns")
print(f"Test: {test.shape[0]:,} rows")
print(f"\nTarget (exam_score): mean={train['exam_score'].mean():.2f}, std={train['exam_score'].std():.2f}")

# Identify columns
target = 'exam_score'
id_col = 'id'
test_ids = test[id_col]

cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']
num_cols = ['age', 'study_hours', 'class_attendance', 'sleep_hours']

print(f"\nCategorical: {cat_cols}")
print(f"Numerical: {num_cols}")

# === TI FEATURE ENGINEERING ===
print("\n" + "="*70)
print("TI FEATURE ENGINEERING")
print("="*70)

def create_ti_features(df):
    """Apply TI framework insights to create features."""
    df = df.copy()
    
    # === GILE G-DIMENSION: GOODNESS (Features that SERVE learning) ===
    # Study efficiency = study hours × class attendance
    df['study_efficiency'] = df['study_hours'] * df['class_attendance'] / 100
    
    # === GILE I-DIMENSION: INTUITION (Non-obvious interactions) ===
    # Sleep-study synergy (quality sleep amplifies study)
    sleep_quality_map = {'Poor': 0.5, 'Average': 1.0, 'Good': 1.5}
    df['sleep_quality_num'] = df['sleep_quality'].map(sleep_quality_map).fillna(1.0)
    df['sleep_study_synergy'] = df['sleep_hours'] * df['sleep_quality_num'] * df['study_hours'] / 50
    
    # === GILE L-DIMENSION: LOVE (Environmental/social support) ===
    # Resource access score
    internet_map = {'No': 0, 'Yes': 1}
    facility_map = {'Poor': 0, 'Average': 1, 'Good': 2}
    df['internet_num'] = df['internet_access'].map(internet_map).fillna(0.5)
    df['facility_num'] = df['facility_rating'].map(facility_map).fillna(1)
    df['resource_score'] = df['internet_num'] + df['facility_num'] / 2
    
    # === GILE E-DIMENSION: ENVIRONMENT (External constraints) ===
    # Difficulty adjustment - harder exams need more prep
    difficulty_map = {'Easy': 0.8, 'Medium': 1.0, 'Hard': 1.2}
    df['difficulty_num'] = df['exam_difficulty'].map(difficulty_map).fillna(1.0)
    df['prep_vs_difficulty'] = df['study_efficiency'] / df['difficulty_num']
    
    # === LCC THRESHOLD (0.42) ===
    # High-impact binary: is study_hours above median?
    df['high_study'] = (df['study_hours'] > df['study_hours'].median()).astype(int)
    df['high_attendance'] = (df['class_attendance'] > 70).astype(int)
    df['lcc_compound'] = df['high_study'] + df['high_attendance']
    
    # === MEIJER HARMONICS: Non-linear transformations ===
    # Diminishing returns on study hours (log-like)
    df['study_hours_harmonic'] = np.log1p(df['study_hours'])
    df['sleep_hours_squared'] = df['sleep_hours'] ** 2  # Optimal sleep matters
    
    # === FREE ENERGY MINIMIZATION ===
    # Cognitive load proxy
    df['cognitive_balance'] = df['sleep_hours'] / (df['study_hours'] + 1)
    
    return df

train = create_ti_features(train)
test = create_ti_features(test)

print("Created TI features:")
print("  - study_efficiency (G-dimension)")
print("  - sleep_study_synergy (I-dimension)")  
print("  - resource_score (L-dimension)")
print("  - prep_vs_difficulty (E-dimension)")
print("  - lcc_compound (LCC threshold)")
print("  - study_hours_harmonic (Meijer harmonics)")
print("  - cognitive_balance (Free energy)")

# === ENCODING ===
print("\n" + "="*70)
print("ENCODING CATEGORICAL FEATURES")
print("="*70)

# Simple label encoding (fast for large dataset)
encoders = {}
for col in cat_cols:
    le = LabelEncoder()
    combined = pd.concat([train[col].astype(str), test[col].astype(str)])
    le.fit(combined)
    train[col + '_enc'] = le.transform(train[col].astype(str))
    test[col + '_enc'] = le.transform(test[col].astype(str))
    encoders[col] = le

# Feature list
feature_cols = (
    num_cols + 
    [c + '_enc' for c in cat_cols] +
    ['study_efficiency', 'sleep_study_synergy', 'resource_score', 
     'prep_vs_difficulty', 'lcc_compound', 'study_hours_harmonic',
     'sleep_hours_squared', 'cognitive_balance', 'sleep_quality_num',
     'internet_num', 'facility_num', 'difficulty_num', 'high_study', 'high_attendance']
)

X = train[feature_cols].fillna(0)
y = train[target].values
X_test = test[feature_cols].fillna(0)

print(f"\nTotal features: {len(feature_cols)}")
print(f"Training samples: {len(X):,}")

# === TRAINING ===
print("\n" + "="*70)
print("TRAINING MODELS (HistGradientBoosting - fast for large data)")
print("="*70)

# HistGradientBoosting is MUCH faster for large datasets
kf = KFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = np.zeros(len(X))
test_preds = np.zeros(len(X_test))
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_train, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_train, y_val = y[train_idx], y[val_idx]
    
    # HistGradientBoosting - sklearn's fast gradient boosting
    model = HistGradientBoostingRegressor(
        max_iter=300,
        max_depth=8,
        learning_rate=0.05,
        l2_regularization=0.1,
        max_bins=255,
        random_state=42
    )
    
    model.fit(X_train, y_train)
    
    val_pred = model.predict(X_val)
    oof_preds[val_idx] = val_pred
    test_preds += model.predict(X_test) / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, val_pred))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv_score = np.mean(scores)
print(f"\n{'='*40}")
print(f"CV RMSE: {cv_score:.4f} (+/- {np.std(scores):.4f})")
print(f"{'='*40}")

# === FEATURE IMPORTANCE ===
print("\nTop 10 Feature Importances (from last fold):")
if hasattr(model, 'feature_importances_'):
    importance = pd.DataFrame({
        'feature': feature_cols,
        'importance': model.feature_importances_
    }).sort_values('importance', ascending=False)
    for i, row in importance.head(10).iterrows():
        print(f"  {row['feature']}: {row['importance']:.4f}")

# === SUBMISSION ===
print("\n" + "="*70)
print("GENERATING SUBMISSION")
print("="*70)

submission = pd.DataFrame({
    'id': test_ids,
    'exam_score': test_preds
})
submission.to_csv('submission_ti.csv', index=False)

print(f"Saved: submission_ti.csv")
print(f"Predictions: mean={test_preds.mean():.2f}, std={test_preds.std():.2f}")
print(f"Range: [{test_preds.min():.2f}, {test_preds.max():.2f}]")

# Sanity check
print(f"\nSanity check:")
print(f"  Train target: mean={y.mean():.2f}, std={y.std():.2f}")
print(f"  Predictions:  mean={test_preds.mean():.2f}, std={test_preds.std():.2f}")

print("\n" + "="*70)
print(f"DONE! CV RMSE: {cv_score:.4f}")
print("Upload submission_ti.csv to Kaggle!")
print("="*70)
