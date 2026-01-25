"""
TI SIGMA ADVANCED SOLVER v2
Kaggle S6E1 - Predicting Student Test Scores

INSIGHTS FROM TOP NOTEBOOKS:
- study_hours has 0.76 correlation with exam_score (DOMINANT feature)
- class_attendance has 0.36 correlation
- sleep_hours has 0.17 correlation
- Original dataset available for augmentation (20K samples)

TI FRAMEWORK ENHANCEMENTS:
1. LCC Threshold 0.42: study_hours (0.76) exceeds threshold = PRIMARY predictor
2. Meijer Harmonics: Polynomial features for study_hours
3. GILE Matrix: Feature interactions across all 4 dimensions
4. Target Encoding: For categorical features (more signal)
5. Stacking: Multiple model layers like consciousness layers

Current best: 8.76 (public notebook)
Our target: Beat that!
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold
from sklearn.preprocessing import LabelEncoder, StandardScaler
from sklearn.ensemble import HistGradientBoostingRegressor, StackingRegressor
from sklearn.linear_model import Ridge, HuberRegressor
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI SIGMA ADVANCED SOLVER v2")
print("Target: Beat 8.76 RMSE")
print("="*70)

# Load data
train = pd.read_csv('train.csv')
test = pd.read_csv('test.csv')

# Try to load original dataset for augmentation
try:
    og = pd.read_csv('exam-score-prediction-dataset/Exam_Score_Prediction.csv')
    if 'student_id' in og.columns:
        og = og.drop('student_id', axis=1)
    if 'id' not in og.columns:
        og['id'] = range(len(train) + 1000000, len(train) + 1000000 + len(og))
    train = pd.concat([train, og], ignore_index=True)
    print(f"Augmented with original data: {len(og)} samples")
except:
    print("Original dataset not available, using synthetic only")

print(f"\nTrain: {train.shape[0]:,} samples")
print(f"Test: {test.shape[0]:,} samples")

target = 'exam_score'
test_ids = test['id']

# === LCC INSIGHT: study_hours is DOMINANT (r=0.76 > 0.42 threshold) ===
print("\n" + "="*70)
print("LCC ANALYSIS: Correlation with exam_score")
print("="*70)
num_cols = ['age', 'study_hours', 'class_attendance', 'sleep_hours']
for col in num_cols:
    corr = train[[col, target]].corr().iloc[0,1]
    lcc_status = "ABOVE 0.42 ✓" if abs(corr) > 0.42 else "below 0.42"
    print(f"  {col}: r = {corr:.3f} [{lcc_status}]")

# === TI FEATURE ENGINEERING v2 ===
print("\n" + "="*70)
print("TI FEATURE ENGINEERING v2")
print("="*70)

def create_ti_features_v2(df, is_train=True, target_means=None):
    """Enhanced TI features with deeper domain knowledge."""
    df = df.copy()
    
    # === PRIMARY: study_hours transformations (r=0.76!) ===
    df['study_hours_sq'] = df['study_hours'] ** 2
    df['study_hours_sqrt'] = np.sqrt(df['study_hours'])
    df['study_hours_log'] = np.log1p(df['study_hours'])
    
    # === INTERACTION: study × attendance ===
    df['study_attendance'] = df['study_hours'] * df['class_attendance'] / 100
    df['study_attendance_sq'] = df['study_attendance'] ** 2
    
    # === SLEEP OPTIMIZATION ===
    # Optimal sleep is around 7-8 hours
    df['sleep_deviation'] = abs(df['sleep_hours'] - 7.5)
    df['sleep_optimal'] = (df['sleep_hours'] >= 6) & (df['sleep_hours'] <= 9)
    df['sleep_optimal'] = df['sleep_optimal'].astype(int)
    
    # === CATEGORICAL ENCODING ===
    # Map categorical to numerical
    sleep_quality_map = {'poor': 0, 'average': 1, 'good': 2}
    facility_map = {'low': 0, 'medium': 1, 'high': 2}
    difficulty_map = {'easy': 0, 'moderate': 1, 'hard': 2}
    internet_map = {'no': 0, 'yes': 1}
    
    df['sleep_quality_num'] = df['sleep_quality'].str.lower().map(sleep_quality_map).fillna(1)
    df['facility_num'] = df['facility_rating'].str.lower().map(facility_map).fillna(1)
    df['difficulty_num'] = df['exam_difficulty'].str.lower().map(difficulty_map).fillna(1)
    df['internet_num'] = df['internet_access'].str.lower().map(internet_map).fillna(0.5)
    
    # === GILE INTERACTIONS ===
    # G: Goodness (effectiveness)
    df['study_quality'] = df['study_hours'] * (df['sleep_quality_num'] + 1)
    
    # I: Intuition (synergies)
    df['total_engagement'] = df['study_hours'] + df['class_attendance']/10 + df['sleep_hours']
    
    # L: Love (support systems)
    df['support_score'] = df['internet_num'] + df['facility_num'] / 2
    
    # E: Environment (challenges)
    df['adjusted_prep'] = df['study_hours'] * (3 - df['difficulty_num']) / 2
    
    # === POLYNOMIAL FEATURE (from top notebook insight) ===
    df['study_poly'] = df['study_hours']**2 + df['class_attendance'] * df['study_hours'] / 100
    
    return df

train = create_ti_features_v2(train, is_train=True)
test = create_ti_features_v2(test, is_train=False)

print("Created enhanced features:")
print("  - study_hours transformations (sq, sqrt, log)")
print("  - study_attendance interactions")
print("  - sleep optimization features")
print("  - GILE dimension features")
print("  - polynomial combinations")

# === LABEL ENCODING ===
cat_cols = ['gender', 'course', 'internet_access', 'sleep_quality', 
            'study_method', 'facility_rating', 'exam_difficulty']

for col in cat_cols:
    le = LabelEncoder()
    combined = pd.concat([train[col].astype(str), test[col].astype(str)])
    le.fit(combined)
    train[col + '_enc'] = le.transform(train[col].astype(str))
    test[col + '_enc'] = le.transform(test[col].astype(str))

# === FEATURE LIST ===
feature_cols = (
    num_cols +
    [c + '_enc' for c in cat_cols] +
    ['study_hours_sq', 'study_hours_sqrt', 'study_hours_log',
     'study_attendance', 'study_attendance_sq',
     'sleep_deviation', 'sleep_optimal',
     'sleep_quality_num', 'facility_num', 'difficulty_num', 'internet_num',
     'study_quality', 'total_engagement', 'support_score', 'adjusted_prep',
     'study_poly']
)

X = train[feature_cols].fillna(0)
y = train[target].values
X_test = test[feature_cols].fillna(0)

print(f"\nTotal features: {len(feature_cols)}")

# === TRAINING WITH STACKING ===
print("\n" + "="*70)
print("TRAINING STACKED ENSEMBLE (TI Consciousness Layers)")
print("="*70)

kf = KFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = np.zeros(len(X))
test_preds = np.zeros(len(X_test))
scores = []

for fold, (train_idx, val_idx) in enumerate(kf.split(X)):
    X_train, X_val = X.iloc[train_idx], X.iloc[val_idx]
    y_train, y_val = y[train_idx], y[val_idx]
    
    # Model 1: HistGradientBoosting (fast, accurate)
    model1 = HistGradientBoostingRegressor(
        max_iter=500,
        max_depth=7,
        learning_rate=0.05,
        l2_regularization=0.05,
        max_bins=255,
        early_stopping=True,
        validation_fraction=0.1,
        n_iter_no_change=20,
        random_state=42
    )
    
    model1.fit(X_train, y_train)
    pred1_val = model1.predict(X_val)
    pred1_test = model1.predict(X_test)
    
    # Model 2: Ridge (captures linear relationships)
    scaler = StandardScaler()
    X_train_scaled = scaler.fit_transform(X_train)
    X_val_scaled = scaler.transform(X_val)
    X_test_scaled = scaler.transform(X_test)
    
    model2 = Ridge(alpha=10.0)
    model2.fit(X_train_scaled, y_train)
    pred2_val = model2.predict(X_val_scaled)
    pred2_test = model2.predict(X_test_scaled)
    
    # Blend (0.8 GB + 0.2 Ridge based on typical performance)
    val_pred = 0.85 * pred1_val + 0.15 * pred2_val
    test_pred = 0.85 * pred1_test + 0.15 * pred2_test
    
    oof_preds[val_idx] = val_pred
    test_preds += test_pred / 5
    
    rmse = np.sqrt(mean_squared_error(y_val, val_pred))
    scores.append(rmse)
    print(f"Fold {fold+1}: RMSE = {rmse:.4f}")

cv_score = np.mean(scores)
print(f"\n{'='*40}")
print(f"CV RMSE: {cv_score:.4f} (+/- {np.std(scores):.4f})")
print(f"Target: 8.76 | Gap: {cv_score - 8.76:.4f}")
print(f"{'='*40}")

# === SUBMISSION ===
print("\n" + "="*70)
print("GENERATING SUBMISSION")
print("="*70)

submission = pd.DataFrame({
    'id': test_ids,
    'exam_score': test_preds
})
submission.to_csv('submission_ti_v2.csv', index=False)

print(f"Saved: submission_ti_v2.csv")
print(f"Predictions: mean={test_preds.mean():.2f}, std={test_preds.std():.2f}")

# Also save the base model prediction
submission_hgb = pd.DataFrame({
    'id': test_ids,
    'exam_score': test_preds  # Already averaged
})
submission_hgb.to_csv('submission_ti_v2.csv', index=False)

print("\n" + "="*70)
print(f"DONE! CV RMSE: {cv_score:.4f}")
print("Upload submission_ti_v2.csv to Kaggle!")
print("="*70)
