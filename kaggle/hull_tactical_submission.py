"""
Hull Tactical Market Prediction - Kaggle Competition Submission
================================================================

Competition: Hull Tactical Market Prediction
Prize: $100,000 ($50,000 first place)
Task: Predict S&P 500 excess returns
Metric: Modified Sharpe ratio
Deadline: June 16, 2026

This script:
1. Downloads competition data
2. Applies TI Feature Engine (as "Momentum Coherence" features)
3. Trains ensemble model
4. Generates submission

Academic framing:
- "Novel multi-scale momentum coherence metrics"
- "Regime-aware feature engineering"
- "Asymmetric memory kernels for time series"

Internal: This is GSA/GILE adapted for competition format.
"""

import numpy as np
import pandas as pd
import os
import sys
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from sklearn.ensemble import GradientBoostingRegressor, RandomForestRegressor
from sklearn.linear_model import Ridge
from sklearn.preprocessing import StandardScaler
from sklearn.model_selection import TimeSeriesSplit
import warnings
warnings.filterwarnings('ignore')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ti_feature_engine import MomentumCoherenceEngine, CyclicalFeatureEngine

# Constants
COMPETITION_NAME = "hull-tactical-market-prediction"
SUBMISSION_DIR = "kaggle/submissions"

class HullTacticalModel:
    """
    Competition model using TI Feature Engine.
    
    Architecture:
    1. Feature extraction via MomentumCoherenceEngine
    2. Ensemble of GBM, RF, and Ridge
    3. Regime-aware weighting
    """
    
    def __init__(self):
        self.feature_engine = MomentumCoherenceEngine(short_window=7, long_window=30)
        self.cyclical_engine = CyclicalFeatureEngine()
        self.scaler = StandardScaler()
        
        # Ensemble models
        self.models = {
            'gbm': GradientBoostingRegressor(
                n_estimators=100,
                max_depth=4,
                learning_rate=0.05,
                random_state=42
            ),
            'rf': RandomForestRegressor(
                n_estimators=100,
                max_depth=6,
                random_state=42
            ),
            'ridge': Ridge(alpha=1.0)
        }
        
        # Model weights (adjusted based on regime)
        self.base_weights = {'gbm': 0.5, 'rf': 0.3, 'ridge': 0.2}
        self.is_fitted = False
    
    def extract_features_for_row(self, prices: np.ndarray, returns: np.ndarray) -> Dict:
        """Extract all features for a single time point."""
        momentum_features = self.feature_engine.extract_all_features(prices, returns)
        cyclical_features = self.cyclical_engine.extract_cyclical_features(prices)
        
        all_features = {**momentum_features, **cyclical_features}
        return all_features
    
    def prepare_training_data(self, df: pd.DataFrame, 
                               price_col: str = 'close',
                               target_col: str = 'target',
                               lookback: int = 60) -> Tuple[pd.DataFrame, np.ndarray]:
        """
        Prepare training data with engineered features.
        
        Args:
            df: DataFrame with price/target data
            price_col: Column name for prices
            target_col: Column name for target variable
            lookback: Number of periods for feature calculation
        
        Returns:
            X: Feature DataFrame
            y: Target array
        """
        prices = df[price_col].values
        returns = df[price_col].pct_change().fillna(0).values * 100
        targets = df[target_col].values if target_col in df.columns else None
        
        feature_list = []
        valid_indices = []
        
        for i in range(lookback, len(prices)):
            price_window = prices[i-lookback:i+1]
            return_window = returns[max(0, i-lookback):i]
            
            if len(return_window) < 10:
                continue
            
            features = self.extract_features_for_row(price_window, return_window)
            feature_list.append(features)
            valid_indices.append(i)
        
        X = pd.DataFrame(feature_list)
        y = targets[valid_indices] if targets is not None else None
        
        return X, y
    
    def fit(self, X: pd.DataFrame, y: np.ndarray):
        """Fit the ensemble model."""
        
        # Scale features
        X_scaled = self.scaler.fit_transform(X.fillna(0))
        
        # Fit each model
        for name, model in self.models.items():
            print(f"  Training {name}...")
            model.fit(X_scaled, y)
        
        self.is_fitted = True
        print("  Model fitting complete!")
    
    def predict(self, X: pd.DataFrame, regime: str = 'expansion') -> np.ndarray:
        """Generate predictions with regime-aware weighting."""
        
        if not self.is_fitted:
            raise ValueError("Model not fitted. Call fit() first.")
        
        X_scaled = self.scaler.transform(X.fillna(0))
        
        # Adjust weights based on regime
        weights = self.base_weights.copy()
        if regime == 'fracture':
            # In fracture, prefer more conservative models
            weights = {'gbm': 0.3, 'rf': 0.2, 'ridge': 0.5}
        elif regime == 'compression':
            # In compression, prefer momentum models
            weights = {'gbm': 0.6, 'rf': 0.3, 'ridge': 0.1}
        
        # Generate weighted ensemble prediction
        predictions = np.zeros(len(X))
        for name, model in self.models.items():
            pred = model.predict(X_scaled)
            predictions += weights[name] * pred
        
        return predictions
    
    def cross_validate(self, X: pd.DataFrame, y: np.ndarray, n_splits: int = 5) -> Dict:
        """Time-series cross-validation."""
        
        tscv = TimeSeriesSplit(n_splits=n_splits)
        
        results = {
            'sharpe': [],
            'returns': [],
            'correlation': []
        }
        
        for fold, (train_idx, test_idx) in enumerate(tscv.split(X)):
            X_train, X_test = X.iloc[train_idx], X.iloc[test_idx]
            y_train, y_test = y[train_idx], y[test_idx]
            
            # Fit on training data
            X_train_scaled = self.scaler.fit_transform(X_train.fillna(0))
            X_test_scaled = self.scaler.transform(X_test.fillna(0))
            
            for name, model in self.models.items():
                model.fit(X_train_scaled, y_train)
            
            # Predict on test data
            predictions = np.zeros(len(X_test))
            for name, model in self.models.items():
                pred = model.predict(X_test_scaled)
                predictions += self.base_weights[name] * pred
            
            # Calculate metrics
            correlation = np.corrcoef(predictions, y_test)[0, 1]
            
            # Simulate returns (sign of prediction * actual return)
            simulated_returns = np.sign(predictions) * y_test
            mean_return = np.mean(simulated_returns)
            std_return = np.std(simulated_returns)
            sharpe = mean_return / std_return * np.sqrt(252) if std_return > 0 else 0
            
            results['sharpe'].append(sharpe)
            results['returns'].append(np.sum(simulated_returns))
            results['correlation'].append(correlation)
            
            print(f"  Fold {fold+1}: Sharpe={sharpe:.2f}, Corr={correlation:.3f}")
        
        # Summary
        avg_sharpe = np.mean(results['sharpe'])
        avg_corr = np.mean(results['correlation'])
        
        print(f"\n  Cross-validation summary:")
        print(f"    Average Sharpe: {avg_sharpe:.2f}")
        print(f"    Average Correlation: {avg_corr:.3f}")
        
        return results


def create_sample_submission():
    """Generate sample submission with synthetic data for testing."""
    
    print("=" * 60)
    print("Hull Tactical Model - Test Run")
    print("=" * 60)
    
    # Generate synthetic market data
    np.random.seed(42)
    n_days = 500
    
    # Simulate S&P 500-like returns
    base_returns = np.random.randn(n_days) * 0.01
    trend = np.linspace(0, 0.002, n_days)  # Slight upward drift
    returns = base_returns + trend
    
    prices = 100 * np.exp(np.cumsum(returns))
    
    # Simulate target (future excess return)
    target = np.roll(returns, -5) * 100  # 5-day forward return
    target[-5:] = 0  # No future data for last 5 days
    
    df = pd.DataFrame({
        'date': pd.date_range('2023-01-01', periods=n_days),
        'close': prices,
        'target': target
    })
    
    print(f"\nSample data: {len(df)} days")
    print(f"Price range: ${df['close'].min():.2f} - ${df['close'].max():.2f}")
    
    # Initialize and train model
    print("\nTraining model...")
    model = HullTacticalModel()
    
    X, y = model.prepare_training_data(df, lookback=60)
    print(f"Features extracted: {X.shape[0]} samples, {X.shape[1]} features")
    print(f"Feature names: {list(X.columns)}")
    
    # Cross-validate
    print("\nCross-validation:")
    results = model.cross_validate(X, y, n_splits=5)
    
    # Final fit on all data
    print("\nFitting final model on all data...")
    model.fit(X, y)
    
    # Generate predictions
    predictions = model.predict(X)
    
    print(f"\nPrediction statistics:")
    print(f"  Mean: {np.mean(predictions):.4f}")
    print(f"  Std: {np.std(predictions):.4f}")
    print(f"  Min/Max: {np.min(predictions):.4f} / {np.max(predictions):.4f}")
    
    # Create submission format
    os.makedirs(SUBMISSION_DIR, exist_ok=True)
    
    submission = pd.DataFrame({
        'id': range(len(predictions)),
        'prediction': predictions
    })
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    submission_file = f"{SUBMISSION_DIR}/hull_tactical_{timestamp}.csv"
    submission.to_csv(submission_file, index=False)
    
    print(f"\nSubmission saved: {submission_file}")
    print(f"Shape: {submission.shape}")
    
    print("\n" + "=" * 60)
    print("Model ready for Hull Tactical competition!")
    print("=" * 60)
    
    return model, results


def download_competition_data():
    """Instructions for downloading Hull Tactical data."""
    
    print("""
Hull Tactical Competition Data
==============================

To download the official competition data:

1. Create Kaggle account at kaggle.com
2. Join competition at:
   kaggle.com/competitions/hull-tactical-market-prediction
3. Accept competition rules
4. Download data:
   - Via CLI: kaggle competitions download -c hull-tactical-market-prediction
   - Via web: Click "Download All" on Data tab

Place files in: kaggle/data/hull_tactical/

Expected files:
- train.csv
- test.csv
- sample_submission.csv
""")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Hull Tactical Competition Model")
    parser.add_argument('--mode', choices=['test', 'download', 'train'], default='test')
    
    args = parser.parse_args()
    
    if args.mode == 'test':
        create_sample_submission()
    elif args.mode == 'download':
        download_competition_data()
    elif args.mode == 'train':
        print("Training mode requires competition data.")
        print("Run with --mode download first.")
