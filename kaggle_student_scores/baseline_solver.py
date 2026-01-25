"""
Kaggle Playground Series S6E1 - Predicting Student Test Scores
Baseline Solution

Competition: https://www.kaggle.com/competitions/playground-series-s6e1
Metric: RMSE (Root Mean Squared Error)
Deadline: January 31, 2026

Features typically include:
- Demographics (gender, race/ethnicity)
- Parental education level  
- Lunch type (standard vs free/reduced)
- Test preparation course
- Previous scores (math, reading, writing)

This baseline uses:
1. XGBoost Regressor
2. LightGBM Regressor  
3. Simple ensemble averaging
"""

import pandas as pd
import numpy as np
from sklearn.model_selection import KFold, cross_val_score
from sklearn.preprocessing import LabelEncoder, StandardScaler
from sklearn.ensemble import RandomForestRegressor, GradientBoostingRegressor
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_squared_error
import warnings
warnings.filterwarnings('ignore')

try:
    import xgboost as xgb
    HAS_XGB = True
except ImportError:
    HAS_XGB = False
    print("XGBoost not available, using sklearn alternatives")

try:
    import lightgbm as lgb
    HAS_LGB = True
except ImportError:
    HAS_LGB = False
    print("LightGBM not available, using sklearn alternatives")


def load_data():
    """Load train and test data."""
    train = pd.read_csv('train.csv')
    test = pd.read_csv('test.csv')
    
    print(f"Train shape: {train.shape}")
    print(f"Test shape: {test.shape}")
    print(f"\nColumns: {list(train.columns)}")
    print(f"\nTarget stats:")
    if 'exam_score' in train.columns:
        print(train['exam_score'].describe())
    
    return train, test


def preprocess(train, test):
    """Preprocess data for modeling."""
    target_col = 'exam_score'
    id_col = 'id'
    
    if target_col not in train.columns:
        print(f"Warning: {target_col} not in columns. Available: {train.columns.tolist()}")
        target_col = train.columns[-1]
        print(f"Using {target_col} as target")
    
    y = train[target_col].values
    
    drop_cols = [c for c in [id_col, target_col] if c in train.columns]
    X_train = train.drop(columns=drop_cols)
    
    test_ids = test[id_col] if id_col in test.columns else test.index
    drop_cols_test = [c for c in [id_col, target_col] if c in test.columns]
    X_test = test.drop(columns=drop_cols_test)
    
    cat_cols = X_train.select_dtypes(include=['object', 'category']).columns.tolist()
    num_cols = X_train.select_dtypes(include=['int64', 'float64']).columns.tolist()
    
    print(f"\nCategorical columns ({len(cat_cols)}): {cat_cols}")
    print(f"Numerical columns ({len(num_cols)}): {num_cols}")
    
    encoders = {}
    for col in cat_cols:
        le = LabelEncoder()
        combined = pd.concat([X_train[col].astype(str), X_test[col].astype(str)])
        le.fit(combined)
        X_train[col] = le.transform(X_train[col].astype(str))
        X_test[col] = le.transform(X_test[col].astype(str))
        encoders[col] = le
    
    X_train = X_train.fillna(X_train.median())
    X_test = X_test.fillna(X_test.median())
    
    return X_train, X_test, y, test_ids


def train_models(X, y, n_folds=5):
    """Train ensemble of models with cross-validation."""
    kf = KFold(n_splits=n_folds, shuffle=True, random_state=42)
    
    models = {}
    scores = {}
    
    print("\n" + "="*60)
    print("TRAINING MODELS")
    print("="*60)
    
    rf = RandomForestRegressor(
        n_estimators=200,
        max_depth=12,
        min_samples_leaf=4,
        n_jobs=-1,
        random_state=42
    )
    rf_scores = -cross_val_score(rf, X, y, cv=kf, scoring='neg_root_mean_squared_error')
    rf.fit(X, y)
    models['rf'] = rf
    scores['rf'] = rf_scores.mean()
    print(f"RandomForest RMSE: {rf_scores.mean():.4f} (+/- {rf_scores.std():.4f})")
    
    ridge = Ridge(alpha=1.0)
    ridge_scores = -cross_val_score(ridge, X, y, cv=kf, scoring='neg_root_mean_squared_error')
    ridge.fit(X, y)
    models['ridge'] = ridge
    scores['ridge'] = ridge_scores.mean()
    print(f"Ridge RMSE: {ridge_scores.mean():.4f} (+/- {ridge_scores.std():.4f})")
    
    if HAS_XGB:
        xgb_model = xgb.XGBRegressor(
            n_estimators=300,
            max_depth=6,
            learning_rate=0.05,
            subsample=0.8,
            colsample_bytree=0.8,
            random_state=42,
            n_jobs=-1
        )
        xgb_scores = -cross_val_score(xgb_model, X, y, cv=kf, scoring='neg_root_mean_squared_error')
        xgb_model.fit(X, y)
        models['xgb'] = xgb_model
        scores['xgb'] = xgb_scores.mean()
        print(f"XGBoost RMSE: {xgb_scores.mean():.4f} (+/- {xgb_scores.std():.4f})")
    
    if HAS_LGB:
        lgb_model = lgb.LGBMRegressor(
            n_estimators=300,
            max_depth=6,
            learning_rate=0.05,
            subsample=0.8,
            colsample_bytree=0.8,
            random_state=42,
            n_jobs=-1,
            verbose=-1
        )
        lgb_scores = -cross_val_score(lgb_model, X, y, cv=kf, scoring='neg_root_mean_squared_error')
        lgb_model.fit(X, y)
        models['lgb'] = lgb_model
        scores['lgb'] = lgb_scores.mean()
        print(f"LightGBM RMSE: {lgb_scores.mean():.4f} (+/- {lgb_scores.std():.4f})")
    
    gb = GradientBoostingRegressor(
        n_estimators=200,
        max_depth=5,
        learning_rate=0.05,
        random_state=42
    )
    gb_scores = -cross_val_score(gb, X, y, cv=kf, scoring='neg_root_mean_squared_error')
    gb.fit(X, y)
    models['gb'] = gb
    scores['gb'] = gb_scores.mean()
    print(f"GradientBoosting RMSE: {gb_scores.mean():.4f} (+/- {gb_scores.std():.4f})")
    
    return models, scores


def predict_ensemble(models, X_test, weights=None):
    """Generate ensemble predictions."""
    preds = {}
    for name, model in models.items():
        preds[name] = model.predict(X_test)
    
    if weights is None:
        weights = {name: 1/len(models) for name in models}
    
    ensemble_pred = np.zeros(len(X_test))
    for name, pred in preds.items():
        ensemble_pred += weights.get(name, 0) * pred
    
    return ensemble_pred, preds


def create_submission(test_ids, predictions, filename='submission.csv'):
    """Create submission file."""
    sub = pd.DataFrame({
        'id': test_ids,
        'exam_score': predictions
    })
    sub.to_csv(filename, index=False)
    print(f"\nSubmission saved: {filename}")
    print(f"Predictions range: [{predictions.min():.2f}, {predictions.max():.2f}]")
    print(f"Predictions mean: {predictions.mean():.2f}")
    return sub


def main():
    print("="*60)
    print("KAGGLE S6E1 - PREDICTING STUDENT TEST SCORES")
    print("="*60)
    
    train, test = load_data()
    
    X_train, X_test, y, test_ids = preprocess(train, test)
    
    models, scores = train_models(X_train, y)
    
    best_model = min(scores, key=scores.get)
    print(f"\nBest single model: {best_model} (RMSE: {scores[best_model]:.4f})")
    
    total_weight = sum(1/s for s in scores.values())
    weights = {name: (1/score)/total_weight for name, score in scores.items()}
    print(f"\nEnsemble weights: {weights}")
    
    ensemble_pred, individual_preds = predict_ensemble(models, X_test, weights)
    
    create_submission(test_ids, ensemble_pred, 'submission_ensemble.csv')
    
    best_pred = individual_preds[best_model]
    create_submission(test_ids, best_pred, f'submission_{best_model}.csv')
    
    print("\n" + "="*60)
    print("DONE! Upload submission_ensemble.csv to Kaggle")
    print("="*60)


if __name__ == "__main__":
    main()
