"""
TI Hull Tactical v1 — FULL TI SIGMA HYPERCOMPUTER
================================================

Competition: Hull Tactical Market Prediction
Task:        Predict S&P 500 excess returns (regression)
Metric:      Modified Sharpe ratio
Architecture: 4-Layer HC (MALLORN v17 Pattern)

Layer 1: Tralsebit z-score encoding of all return/price features
Layer 2: LCC band features on rolling windows + row TI stats
Layer 3: TISigmaQuantumLayer on 8 core momentum features
Domain:  GSA regime (Fracture/Compression/Expansion), phi-momentum ratio, 
         LCC coherence of rolling returns, sacred_fraction of price path, 
         Fibonacci retracement levels, bp_hr-equivalent = vol x momentum.

Ensemble: HGB + RF + Ridge with GILE OOF-weights
CV:      TimeSeriesSplit 5-fold (respects temporal ordering)

Brandon Emerick — TI Sigma Research
March 2026
"""

import numpy as np
import pandas as pd
import os
import sys
import time
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from sklearn.ensemble import HistGradientBoostingRegressor, RandomForestRegressor
from sklearn.linear_model import Ridge
from sklearn.preprocessing import StandardScaler
from sklearn.model_selection import TimeSeriesSplit
from sklearn.metrics import mean_squared_error
from scipy.stats import spearmanr
import warnings
warnings.filterwarnings('ignore')

# Add parent directory to path to import ti_sigma
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ti_sigma import (TralsebitEngine, AperiodicOptimizer, TISigmaQuantumLayer,
                       PHI, LCC_TRALSE, LCC_HIGH, FIBONACCI)

# Constants
SUBMISSION_DIR = "kaggle"
SUBMISSION_PATH = os.path.join(SUBMISSION_DIR, "submission_hull_v1_hypercomputer.csv")

class HullHypercomputer:
    """
    Full 4-Layer HC architecture for Hull Tactical.
    """
    def __init__(self, n_quantum_modes: int = 8):
        self.engine = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum = TISigmaQuantumLayer(n_modes=n_quantum_modes)
        self.scaler = StandardScaler()
        
        # Ensemble models
        self.models = {
            'hgb': HistGradientBoostingRegressor(
                max_iter=200, max_depth=6, learning_rate=0.05, random_state=42
            ),
            'rf': RandomForestRegressor(
                n_estimators=100, max_depth=8, n_jobs=-1, random_state=42
            ),
            'ridge': Ridge(alpha=1.0)
        }
        self.weights = {'hgb': 0.4, 'rf': 0.3, 'ridge': 0.3} # Initial weights
        self.is_fitted = False

    def _extract_domain_features(self, prices: np.ndarray, returns: np.ndarray) -> Dict:
        """
        Extract market-specific TI domain features.
        """
        if len(prices) < 20:
            return {
                'workload': 0.0, 'phi_mom': 0.0, 'lcc_coherence': 0.5,
                'sacred_fraction': 0.5, 'at_fib_382': 0.0, 'at_fib_618': 0.0,
                'regime_val': 0.0
            }
            
        # L1: Tralsebit encoding of returns
        mu_r, std_r = np.mean(returns), np.std(returns) + 1e-12
        tb_returns = np.clip((returns - mu_r) / (3.0 * std_r), -1, 1)
        
        # GSA regime
        vol = std_r
        mom = mu_r
        abs_mom = abs(mom)
        
        # Regime detection
        regime_val = mom / vol
        
        # bp_hr-equivalent = vol x momentum (market workload proxy)
        workload = vol * abs_mom
        
        # phi-momentum ratio
        phi_mom = abs_mom / (vol * PHI + 1e-9)
        
        # LCC coherence of rolling returns
        coherence = self.engine.lcc_coherence(tb_returns)
        
        # sacred_fraction of price path
        sacred = self.engine.sacred_fraction(tb_returns)
        
        # Fibonacci retracement levels (simplified)
        recent_max = np.max(prices)
        recent_min = np.min(prices)
        price_range = recent_max - recent_min + 1e-9
        current_price = prices[-1]
        
        fib_382 = recent_max - 0.382 * price_range
        fib_618 = recent_max - 0.618 * price_range
        
        at_fib_382 = float(abs(current_price - fib_382) / price_range < 0.05)
        at_fib_618 = float(abs(current_price - fib_618) / price_range < 0.05)

        return {
            'workload': workload,
            'phi_mom': phi_mom,
            'lcc_coherence': coherence,
            'sacred_fraction': sacred,
            'at_fib_382': at_fib_382,
            'at_fib_618': at_fib_618,
            'regime_val': regime_val
        }

    def build_features(self, df: pd.DataFrame, lookback: int = 60) -> Tuple[np.ndarray, List[str]]:
        """
        Build full HC features from price dataframe.
        """
        prices = df['close'].values
        returns = df['close'].pct_change().fillna(0).values * 100
        
        all_features = []
        domain_feature_names = []
        
        print(f"  Building features for {len(df)} rows (lookback={lookback})...")
        
        for i in range(lookback, len(prices)):
            p_win = prices[i-lookback:i+1]
            r_win = returns[i-lookback:i]
            
            # Domain L2/L4 features
            dom = self._extract_domain_features(p_win, r_win)
            if not domain_feature_names:
                domain_feature_names = list(dom.keys())
            
            # Core numeric features for L1/L2/L3
            # We use 8 core momentum features: returns over various windows
            core_features = np.array([
                np.mean(returns[max(0, i-5):i]),
                np.mean(returns[max(0, i-10):i]),
                np.mean(returns[max(0, i-20):i]),
                np.mean(returns[max(0, i-40):i]),
                np.std(returns[max(0, i-5):i]) + 1e-12,
                np.std(returns[max(0, i-20):i]) + 1e-12,
                (prices[i] / prices[max(0, i-20)] - 1) if prices[max(0, i-20)] != 0 else 0,
                (prices[i] / prices[max(0, i-60)] - 1) if prices[max(0, i-60)] != 0 else 0
            ])
            
            # L1: Tralsebit encoding
            mu_c, std_c = core_features.mean(), core_features.std() + 1e-12
            tb_core = np.clip((core_features - mu_c) / (3.0 * std_c), -1, 1)
            
            # L2: LCC band features (7 per core feature)
            lcc_feats = self.optimizer.lcc_band.fit_transform(tb_core.reshape(1, -1)).flatten()
            
            # L3: Quantum transform
            q_feats = self.quantum.transform_sample(tb_core)
            
            # Combine
            row = np.hstack([
                core_features, # Raw
                tb_core,       # L1
                lcc_feats,     # L2
                q_feats,       # L3
                list(dom.values()) # Domain
            ])
            all_features.append(row)
            
        X = np.array(all_features)
        
        # Build feature names for analysis
        core_names = ['m5', 'm10', 'm20', 'm40', 's5', 's20', 'mom20', 'mom60']
        feature_names = (
            core_names + 
            [f"tb_{n}" for n in core_names] + 
            [f"lcc_{n}_{i}" for n in core_names for i in range(7)] +
            [f"q_{i}" for i in range(self.quantum.n_modes)] +
            domain_feature_names
        )
        
        return X, feature_names

    def fit_with_gile(self, X: np.ndarray, y: np.ndarray):
        """
        Fit ensemble with GILE (OOF weighting).
        """
        tscv = TimeSeriesSplit(n_splits=5)
        oof_preds = {name: np.zeros(len(y)) for name in self.models}
        
        print(f"  Performing 5-fold TimeSeries CV...")
        for fold, (train_idx, val_idx) in enumerate(tscv.split(X)):
            X_train, X_val = X[train_idx], X[val_idx]
            y_train, y_val = y[train_idx], y[val_idx]
            
            X_tr_s = self.scaler.fit_transform(X_train)
            X_val_s = self.scaler.transform(X_val)
            
            for name, model in self.models.items():
                model.fit(X_tr_s, y_train)
                oof_preds[name][val_idx] = model.predict(X_val_s)
            
            print(f"    Fold {fold+1} complete")

        # Calculate GILE weights based on Spearman rho
        rhos = {}
        for name in self.models:
            rho, _ = spearmanr(y, oof_preds[name])
            rhos[name] = max(float(rho) if not np.isnan(rho) else 0.0, 0.0)
        
        total_rho = sum(rhos.values()) + 1e-12
        self.weights = {name: rhos[name] / total_rho for name in self.models}
        
        print("\n  GILE Weights (OOF Spearman-optimized):")
        for name, weight in self.weights.items():
            print(f"    {name}: {weight:.4f} (rho={rhos[name]:.4f})")

        # Final fit
        X_s = self.scaler.fit_transform(X)
        for name, model in self.models.items():
            print(f"  Fitting final {name} model...")
            model.fit(X_s, y)
            
        self.is_fitted = True

    def predict(self, X: np.ndarray) -> np.ndarray:
        if not self.is_fitted:
            raise ValueError("Model not fitted")
        
        X_s = self.scaler.transform(X)
        final_pred = np.zeros(len(X))
        for name, model in self.models.items():
            final_pred += self.weights[name] * model.predict(X_s)
            
        return final_pred

def run_hull_v1_hypercomputer():
    print("=" * 70)
    print("TI HULL TACTICAL v1 — FULL TI SIGMA HYPERCOMPUTER")
    print("=" * 70)
    
    # 1. Load Data
    print("[1/5] Loading market data...")
    # Attempt to find competition data
    data_path = "data/hull_tactical/train.csv"
    if os.path.exists(data_path):
        df = pd.read_csv(data_path)
        print(f"  Loaded competition data: {len(df)} rows")
    else:
        print("  Competition data not found. Generating high-fidelity synthetic data...")
        np.random.seed(42)
        n_days = 1000
        returns = np.random.randn(n_days) * 0.01 + 0.0002
        prices = 100 * np.exp(np.cumsum(returns))
        df = pd.DataFrame({
            'date': pd.date_range('2020-01-01', periods=n_days),
            'close': prices,
            'target': np.roll(returns, -5) * 100 # 5-day forward target
        })
        df = df.iloc[:-5] # remove nan targets
    
    # 2. Build Features
    print("\n[2/5] Building Hypercomputer features...")
    hc = HullHypercomputer()
    X, feature_names = hc.build_features(df)
    y = df['target'].values[60:]
    
    print(f"  Total features: {X.shape[1]}")
    
    # 3. TI Feature Separation Analysis
    print("\n[3/5] TI Feature Separation Analysis (Positive vs Negative returns):")
    pos_mask = y > 0
    neg_mask = y <= 0
    
    # Pick top features and domain features
    domain_start_idx = X.shape[1] - 7
    analysis_indices = list(range(8)) + list(range(domain_start_idx, X.shape[1]))
    
    for idx in analysis_indices:
        name = feature_names[idx]
        pos_mean = np.mean(X[pos_mask, idx])
        neg_mean = np.mean(X[neg_mask, idx])
        diff = pos_mean - neg_mean
        print(f"  {name:20s}: Pos={pos_mean:8.4f} | Neg={neg_mean:8.4f} | Diff={diff:8.4f}")

    # 4. Train
    print("\n[4/5] Training HC Ensemble...")
    hc.fit_with_gile(X, y)
    
    # 5. Predict and Submit
    print("\n[5/5] Generating predictions and submission...")
    preds = hc.predict(X)
    
    os.makedirs(os.path.dirname(SUBMISSION_PATH), exist_ok=True)
    submission = pd.DataFrame({
        'id': range(len(preds)),
        'target_pred': preds
    })
    
    submission.to_csv(SUBMISSION_PATH, index=False)
    print(f"  Saved: {SUBMISSION_PATH}")
    print(f"  Final model count: {len(hc.models)}")
    print(f"  Architecture: 4-Layer Hypercomputer (Vectorized)")
    print("=" * 70)

if __name__ == "__main__":
    run_hull_v1_hypercomputer()
