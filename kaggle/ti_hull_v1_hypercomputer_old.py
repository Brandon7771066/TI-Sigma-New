"""
Hull Tactical Market Prediction — TI Sigma Hypercomputer v1
============================================================

Competition: Hull Tactical Market Prediction
Prize:       $100,000 ($50,000 first place)
Task:        Predict S&P 500 excess returns (regression)
Metric:      Modified Sharpe ratio
Deadline:    June 16, 2026

TI Sigma Architecture (MALLORN v17 pattern — adapted for time series regression):
  L1  : TralsebitEngine z-score encoding of all return/momentum features
  L2  : LCC band features on rolling windows + per-row TI stats
  L3  : TISigmaQuantumLayer quantum transform on 8 core momentum features
  Dom : GSA regime classification, φ-momentum ratio, LCC coherence of returns,
        sacred_fraction of price path, Fibonacci retracement levels,
        vol×momentum market workload proxy

Ensemble: HGB + RF + Ridge with GILE OOF-weighting (no hardcoded weights)
CV:       TimeSeriesSplit 5-fold (respects temporal ordering — no lookahead)

Academic framing (for paper/submission description):
  "Multi-scale momentum coherence metrics with regime-aware feature engineering.
   Asymmetric memory kernels on temporally-ordered rolling windows."

Brandon Emerick — TI Sigma Research
March 1, 2026
"""

import os
import sys
import warnings
import numpy as np
import pandas as pd
from datetime import datetime
from typing import Dict, List, Tuple, Optional

warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sklearn.ensemble import (
    HistGradientBoostingRegressor,
    RandomForestRegressor,
)
from sklearn.linear_model import Ridge
from sklearn.model_selection import TimeSeriesSplit
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import r2_score
from scipy.stats import spearmanr

from ti_sigma.tralsebit_engine import TralsebitEngine
from ti_sigma.aperiodic_optimizer import AperiodicOptimizer
from ti_sigma.quantum_layer import TISigmaQuantumLayer
from ti_sigma.constants import PHI, LCC_TRALSE, LCC_HIGH, LCC_EMERICK

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
PHI2 = PHI ** 2
FIB_LEVELS = np.array([0.0, 0.236, 0.382, 0.500, 0.618, 0.786, 1.000])

DATA_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'kaggle_hull')
SUBMISSION_DIR = os.path.dirname(os.path.abspath(__file__))
SUBMISSION_PATH = os.path.join(SUBMISSION_DIR, 'submission_hull_v1_hypercomputer.csv')


# ─────────────────────────────────────────────────────────────────────────────
# DOMAIN FEATURE BUILDER
# ─────────────────────────────────────────────────────────────────────────────

class HullMarketAdapter:
    """
    Domain-specific TI features for S&P 500 excess return prediction.

    TI Insights:
      - Market returns live in the Tralse zone: ambiguous (≈LCC_TRALSE) on most days,
        resolving to High/Radiant during regime transitions
      - GSA regime (Fracture / Compression / Expansion) maps to LCC zones:
          Fracture    → LCC < LCC_TRALSE  (sub-threshold, chaotic)
          Compression → LCC_TRALSE–LCC_HIGH (ambiguous accumulation)
          Expansion   → LCC > LCC_HIGH    (resolved uptrend)
      - Momentum coherence = fraction of rolling windows with aligned trend sign
        → analogous to lcc_coherence in cardiac / TDE domains
      - φ-momentum ratio: ratio of short-window to long-window momentum × φ
        → when ratio ≈ 1/φ, system is at the Tralse transition
      - Fibonacci retracement levels: price position relative to FIB_LEVELS
        → sacred geometry in financial time series (well-documented in literature)
    """

    SHORT  = 5
    MID    = 21
    LONG   = 63
    VLONG  = 126

    def __init__(self):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum   = TISigmaQuantumLayer(n_modes=8)
        self.scaler    = StandardScaler()

    def _momentum_features(self, returns: np.ndarray, prices: np.ndarray) -> dict:
        """Rolling momentum and volatility features."""
        n = len(returns)
        r = returns

        def safe_mean(arr, w):
            return float(np.nanmean(arr[-w:])) if len(arr) >= w else float(np.nanmean(arr))

        def safe_std(arr, w):
            return float(np.nanstd(arr[-w:]) + 1e-12) if len(arr) >= w else float(np.nanstd(arr) + 1e-12)

        mom_short  = safe_mean(r, self.SHORT)
        mom_mid    = safe_mean(r, self.MID)
        mom_long   = safe_mean(r, self.LONG)
        mom_vlong  = safe_mean(r, self.VLONG)

        vol_short  = safe_std(r, self.SHORT)
        vol_mid    = safe_std(r, self.MID)
        vol_long   = safe_std(r, self.LONG)

        phi_mom_ratio  = (mom_short / (abs(mom_long) + 1e-9)) * PHI
        sharpe_short   = mom_short  / vol_short
        sharpe_mid     = mom_mid    / vol_mid
        sharpe_long    = mom_long   / vol_long

        # vol×momentum = market workload proxy (analogous to bp_hr_product)
        market_workload = abs(mom_mid) * vol_mid

        # Momentum coherence = fraction of sub-windows with same sign as overall
        signs_short = np.sign(r[-self.SHORT:] if n >= self.SHORT else r)
        mom_sign    = np.sign(mom_short) if mom_short != 0 else 1.0
        coherence   = float(np.mean(signs_short == mom_sign))

        # Trend consistency across timescales
        trend_align = float(np.sign(mom_short) == np.sign(mom_mid) == np.sign(mom_long))

        return {
            'mom_short':       mom_short,
            'mom_mid':         mom_mid,
            'mom_long':        mom_long,
            'mom_vlong':       mom_vlong,
            'vol_short':       vol_short,
            'vol_mid':         vol_mid,
            'vol_long':        vol_long,
            'phi_mom_ratio':   phi_mom_ratio,
            'sharpe_short':    sharpe_short,
            'sharpe_mid':      sharpe_mid,
            'sharpe_long':     sharpe_long,
            'market_workload': market_workload,
            'mom_coherence':   coherence,
            'trend_align':     trend_align,
        }

    def _gsa_regime(self, returns: np.ndarray, prices: np.ndarray) -> dict:
        """
        GSA (Grand Stock Algorithm) regime classification.
        Maps market states to TI LCC zones.

        Fracture    (LCC < 0.42):  high vol, negative momentum → regime 0
        Compression (0.42–0.85):   low vol, flat momentum      → regime 1
        Expansion   (LCC > 0.85):  low vol, positive momentum  → regime 2
        """
        if len(returns) < self.MID:
            return {'gsa_regime': 1, 'regime_frac': 0.5, 'regime_lcc': 0.5}

        r_mid  = returns[-self.MID:]
        vol    = float(np.std(r_mid) + 1e-12)
        mom    = float(np.mean(r_mid))

        lcc_approx = float(1.0 / (1.0 + vol * 10.0))

        if lcc_approx < LCC_TRALSE:
            regime = 0   # Fracture
        elif lcc_approx < LCC_HIGH:
            regime = 1   # Compression
        else:
            regime = 2   # Expansion

        return {
            'gsa_regime':  float(regime),
            'regime_frac': float(regime) / 2.0,
            'regime_lcc':  lcc_approx,
        }

    def _fibonacci_features(self, prices: np.ndarray) -> dict:
        """Price position relative to Fibonacci retracement levels."""
        if len(prices) < 2:
            return {f'fib_{int(lvl*1000):04d}': 0.0 for lvl in FIB_LEVELS[1:-1]}

        high = float(np.max(prices))
        low  = float(np.min(prices))
        rng  = high - low + 1e-9
        cur  = float(prices[-1])
        pos  = (cur - low) / rng   # 0=at_low, 1=at_high

        feats = {}
        for lvl in FIB_LEVELS[1:-1]:
            feats[f'fib_{int(lvl*1000):04d}'] = float(abs(pos - lvl) < 0.02)  # within 2% of level

        feats['fib_position']   = pos
        feats['phi_retracement'] = float(abs(pos - (1.0 / PHI)) < 0.05)  # at golden ratio level
        return feats

    def _ti_signal_features(self, returns: np.ndarray) -> dict:
        """
        TI Sigma specific features derived from Tralsebit encoding of returns.
        These are the key features validated in MALLORN and Heart Disease domains.
        """
        if len(returns) < 5:
            return {
                'tralse_ratio': 0.5, 'sacred_fraction': 0.5,
                'lcc_coherence': 0.5, 'phi_score': 0.0,
                'peak_tralse': 0.0, 'mr_fraction': 0.5,
            }

        r = returns[-self.LONG:] if len(returns) >= self.LONG else returns
        mu, sig = np.mean(r), np.std(r) + 1e-12
        tb = np.clip((r - mu) / (3.0 * sig), -1.0, 1.0)
        abs_tb = np.abs(tb)

        tralse_ratio  = float(np.mean((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH)))
        lcc_coherence = float(np.mean(abs_tb > LCC_TRALSE))
        mr_fraction   = float(np.mean(abs_tb > LCC_HIGH))
        phi_score     = float(np.mean(np.abs(abs_tb - 1.0/PHI) < 0.05))
        peak_tralse   = float(np.max(abs_tb))

        tb_mu     = float(np.mean(tb))
        tolerance = abs(tb_mu) / PHI + 1e-9
        sacred    = float(np.mean(np.abs(tb - tb_mu) <= tolerance))

        return {
            'tralse_ratio':  tralse_ratio,
            'sacred_fraction': sacred,
            'lcc_coherence': lcc_coherence,
            'phi_score':     phi_score,
            'peak_tralse':   peak_tralse,
            'mr_fraction':   mr_fraction,
        }

    def extract_all_features(
        self,
        prices:  np.ndarray,
        returns: np.ndarray,
    ) -> dict:
        """Extract all TI Sigma market features for a single time point."""
        feats = {}
        feats.update(self._momentum_features(returns, prices))
        feats.update(self._gsa_regime(returns, prices))
        feats.update(self._fibonacci_features(prices))
        feats.update(self._ti_signal_features(returns))
        return feats

    def build_feature_matrix(
        self,
        df:         pd.DataFrame,
        price_col:  str = 'close',
        return_col: str = 'return',
        lookback:   int = 63,
    ) -> Tuple[np.ndarray, List[int]]:
        """
        Build full Hypercomputer feature matrix from price/return DataFrame.

        Returns feature matrix X and list of valid row indices.
        """
        if return_col in df.columns:
            returns = df[return_col].fillna(0).values
        else:
            prices_raw = df[price_col].values
            returns    = np.diff(prices_raw) / (prices_raw[:-1] + 1e-9) * 100
            returns    = np.concatenate([[0.0], returns])

        prices  = df[price_col].values if price_col in df.columns else np.arange(len(df), dtype=float)
        n       = len(returns)

        feature_list  = []
        valid_indices = []

        for i in range(lookback, n):
            price_w  = prices[max(0, i-lookback):i+1]
            return_w = returns[max(0, i-lookback):i]
            feats    = self.extract_all_features(price_w, return_w)
            feature_list.append(feats)
            valid_indices.append(i)

        if not feature_list:
            return np.zeros((0, 1)), []

        X_raw = pd.DataFrame(feature_list).fillna(0).values

        # L1: Tralsebit encoding of the raw feature matrix
        mu_c  = X_raw.mean(axis=0, keepdims=True)
        sig_c = X_raw.std(axis=0, keepdims=True) + 1e-12
        tb_X  = np.clip((X_raw - mu_c) / (3.0 * sig_c), -1.0, 1.0)

        # L2: Row-level TI stats on Tralsebit matrix
        abs_tb     = np.abs(tb_X)
        row_tralse = ((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH)).mean(axis=1, keepdims=True)
        row_high   = (abs_tb >= LCC_HIGH).mean(axis=1, keepdims=True)
        row_mu_tb  = tb_X.mean(axis=1, keepdims=True)
        row_std_tb = tb_X.std(axis=1, keepdims=True)
        pos_bias   = (tb_X > 0).mean(axis=1, keepdims=True)
        resolved   = (abs_tb > LCC_TRALSE).mean(axis=1, keepdims=True)

        L2_stats = np.hstack([row_tralse, row_high, row_mu_tb, row_std_tb, pos_bias, resolved])

        # L3: Quantum transform on top-8 Tralsebit features
        top8 = tb_X[:, :8] if tb_X.shape[1] >= 8 else tb_X
        L3   = self.quantum.quantum_feature_transform(top8)

        X_full = np.hstack([X_raw, tb_X, L2_stats, L3])
        return X_full, valid_indices


# ─────────────────────────────────────────────────────────────────────────────
# MAIN SOLVER
# ─────────────────────────────────────────────────────────────────────────────

def print_ti_feature_separation(X: np.ndarray, y: np.ndarray, n_features: int = 20) -> None:
    """Print TI feature separation for positive-return vs negative-return days."""
    pos_mask = y > 0
    neg_mask = y <= 0
    print(f"\n{'─'*65}")
    print(f"{'TI FEATURE SEPARATION: Positive vs Negative Return Days':^65}")
    print(f"{'─'*65}")
    print(f"{'Feature':>8} {'Pos Mean':>10} {'Neg Mean':>10} {'Ratio':>8} {'TI Tag':>12}")
    print(f"{'─'*65}")

    seps = []
    for i in range(min(n_features, X.shape[1])):
        pos_m = float(np.mean(X[pos_mask, i])) if pos_mask.sum() > 0 else 0.0
        neg_m = float(np.mean(X[neg_mask, i])) if neg_mask.sum() > 0 else 0.0
        ratio = pos_m / (abs(neg_m) + 1e-9)
        seps.append((i, pos_m, neg_m, ratio))

    seps.sort(key=lambda x: abs(x[3] - 1.0), reverse=True)
    for i, pos_m, neg_m, ratio in seps[:15]:
        tag = ('★ φ-SCALED' if abs(ratio - PHI) < 0.05
               else '✓ TRALSE' if abs(ratio - 1.0) > 0.05
               else '  FLAT')
        print(f"  F{i:04d}  {pos_m:>10.4f} {neg_m:>10.4f} {ratio:>8.3f} {tag:>12}")
    print(f"{'─'*65}")


def train_and_predict(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test:  np.ndarray,
    n_splits: int = 5,
) -> Tuple[np.ndarray, np.ndarray, Dict]:
    """
    Train GILE-weighted ensemble (HGB + RF + Ridge) with TimeSeriesSplit.
    Returns (oof_predictions, test_predictions, metrics_dict).
    """
    tscv = TimeSeriesSplit(n_splits=n_splits)
    n_train = len(y_train)
    n_test  = len(X_test)

    models = {
        'HGB': HistGradientBoostingRegressor(
            max_iter=200, learning_rate=0.05, max_depth=5,
            min_samples_leaf=20, random_state=42,
        ),
        'RF': RandomForestRegressor(
            n_estimators=100, max_depth=8, min_samples_leaf=20,
            n_jobs=-1, random_state=42,
        ),
        'Ridge': Ridge(alpha=1.0),
    }

    oof_preds = {name: np.zeros(n_train) for name in models}
    test_preds = {name: np.zeros(n_test) for name in models}
    fold_metrics = {name: [] for name in models}

    scaler = StandardScaler()

    for fold, (tr_idx, val_idx) in enumerate(tscv.split(X_train)):
        X_tr, X_val = X_train[tr_idx], X_train[val_idx]
        y_tr, y_val = y_train[tr_idx], y_train[val_idx]

        X_tr_s  = scaler.fit_transform(X_tr)
        X_val_s = scaler.transform(X_val)

        for name, model in models.items():
            model.fit(X_tr_s, y_tr)
            val_pred = model.predict(X_val_s)
            oof_preds[name][val_idx] = val_pred
            corr, _ = spearmanr(y_val, val_pred)
            fold_metrics[name].append(float(corr) if not np.isnan(corr) else 0.0)
            print(f"  Fold {fold+1} | {name:5s} | Spearman ρ = {fold_metrics[name][-1]:+.4f}")

    # Refit on full train for test predictions
    X_train_s = scaler.fit_transform(X_train)
    X_test_s  = scaler.transform(X_test) if n_test > 0 else np.zeros((0, X_test.shape[1]))
    for name, model in models.items():
        model.fit(X_train_s, y_train)
        if n_test > 0:
            test_preds[name] = model.predict(X_test_s)

    # GILE weighting = OOF Spearman correlation (higher = more weight)
    gile_scores = {}
    for name in models:
        rho, _ = spearmanr(y_train, oof_preds[name])
        gile_scores[name] = max(float(rho) if not np.isnan(rho) else 0.0, 0.0)

    total = sum(gile_scores.values()) + 1e-12
    weights = {name: score / total for name, score in gile_scores.items()}

    print(f"\n{'─'*55}")
    print("GILE ENSEMBLE WEIGHTS (OOF Spearman-based):")
    for name, w in weights.items():
        rho = gile_scores[name]
        print(f"  {name:6s} | ρ = {rho:+.4f} | weight = {w:.4f}")
    print(f"{'─'*55}")

    oof_ensemble  = sum(weights[n] * oof_preds[n]  for n in models)
    test_ensemble = sum(weights[n] * test_preds[n] for n in models)

    ens_rho, _ = spearmanr(y_train, oof_ensemble)
    print(f"  ENSEMBLE OOF Spearman ρ = {ens_rho:+.4f}")

    return oof_ensemble, test_ensemble, {
        'oof_spearman': float(ens_rho),
        'model_weights': weights,
        'model_oof_rho': gile_scores,
    }


def generate_mock_data(n_train: int = 2000, n_test: int = 500) -> Tuple[pd.DataFrame, pd.DataFrame]:
    """
    Generate mock S&P 500-like data for development/testing.
    Replace with real competition data when downloaded from Kaggle.
    """
    np.random.seed(42)
    print("  [MOCK DATA] Generating synthetic S&P 500-like data...")
    print("  [MOCK DATA] Replace data/ path with real competition files when available.")

    dates_train = pd.date_range('2000-01-03', periods=n_train, freq='B')
    dates_test  = pd.date_range(dates_train[-1] + pd.Timedelta('1D'), periods=n_test, freq='B')

    def sim_returns(n):
        regime = np.random.choice([0, 1, 2], n, p=[0.15, 0.55, 0.30])
        r = np.where(regime == 0, np.random.normal(-0.3, 1.5, n),
            np.where(regime == 1, np.random.normal( 0.0, 0.6, n),
                                  np.random.normal( 0.1, 0.8, n)))
        return r

    r_train = sim_returns(n_train)
    r_test  = sim_returns(n_test)

    prices_train = 1000.0 * np.exp(np.cumsum(r_train / 100))
    prices_test  = prices_train[-1] * np.exp(np.cumsum(r_test / 100))

    target_train = np.roll(r_train, -1)
    target_train[-1] = 0.0

    df_train = pd.DataFrame({
        'date':   dates_train,
        'close':  prices_train,
        'return': r_train,
        'target': target_train,
        'id':     range(n_train),
    })
    df_test = pd.DataFrame({
        'date':   dates_test,
        'close':  prices_test,
        'return': r_test,
        'id':     range(n_train, n_train + n_test),
    })
    return df_train, df_test


def load_data() -> Tuple[Optional[pd.DataFrame], Optional[pd.DataFrame]]:
    """Load competition data or fall back to mock data."""
    train_paths = [
        os.path.join(DATA_PATH, 'train.csv'),
        'data/kaggle_hull/train.csv',
    ]
    test_paths = [
        os.path.join(DATA_PATH, 'test.csv'),
        'data/kaggle_hull/test.csv',
    ]

    df_train, df_test = None, None
    for p in train_paths:
        if os.path.exists(p):
            print(f"  Loading training data from {p}")
            df_train = pd.read_csv(p)
            break
    for p in test_paths:
        if os.path.exists(p):
            print(f"  Loading test data from {p}")
            df_test = pd.read_csv(p)
            break

    if df_train is None or df_test is None:
        print("  Competition data not found — using mock data for development.")
        df_train, df_test = generate_mock_data()

    return df_train, df_test


def main():
    print("=" * 65)
    print("  TI SIGMA HYPERCOMPUTER v1 — Hull Tactical Market Prediction")
    print("  Brandon Emerick | March 1, 2026 | Prize: $100,000")
    print("=" * 65)

    adapter = HullMarketAdapter()

    print("\n[1/5] Loading data...")
    df_train, df_test = load_data()
    print(f"  Train: {len(df_train):,} rows | Test: {len(df_test):,} rows")

    price_col  = 'close'  if 'close'  in df_train.columns else df_train.columns[1]
    target_col = 'target' if 'target' in df_train.columns else df_train.columns[-1]
    id_col     = 'id'     if 'id'     in df_test.columns  else None

    print("\n[2/5] Building TI Hypercomputer features...")
    X_train_full, train_idx = adapter.build_feature_matrix(df_train, price_col, lookback=63)
    X_test_full,  test_idx  = adapter.build_feature_matrix(df_test,  price_col, lookback=63)

    y_train_raw = df_train[target_col].values[train_idx] if target_col in df_train.columns else np.zeros(len(train_idx))
    y_train = y_train_raw.astype(float)

    n_feat = X_train_full.shape[1]
    print(f"  Feature matrix: {X_train_full.shape[0]:,} × {n_feat} (train) | {X_test_full.shape[0]:,} × {n_feat} (test)")
    print(f"  L1+L2+L3+Domain layers | {n_feat} total Hypercomputer features")

    # Fill NaN
    X_train_full = np.nan_to_num(X_train_full, 0.0)
    X_test_full  = np.nan_to_num(X_test_full,  0.0)

    print_ti_feature_separation(X_train_full, y_train)

    print("\n[3/5] Training GILE-weighted ensemble (TimeSeriesSplit 5-fold)...")
    oof_preds, test_preds, metrics = train_and_predict(
        X_train_full, y_train, X_test_full, n_splits=5
    )

    print(f"\n[4/5] Results:")
    print(f"  OOF Spearman ρ = {metrics['oof_spearman']:+.4f}")
    print(f"  Model weights  : {', '.join(f'{k}={v:.3f}' for k,v in metrics['model_weights'].items())}")
    lcc_equiv = float(np.clip(abs(metrics['oof_spearman']), 0, 1))
    zone = ('LCC_RADIANT' if lcc_equiv >= 0.93 else
            'LCC_HIGH'    if lcc_equiv >= 0.85 else
            'LCC_TRUE'    if lcc_equiv >= 0.62 else
            'LCC_TRALSE'  if lcc_equiv >= 0.41 else 'SUB-THRESHOLD')
    print(f"  LCC Equivalent : {lcc_equiv:.4f} → {zone} zone")

    print(f"\n[5/5] Generating submission...")
    if id_col and len(test_idx) > 0:
        test_ids = df_test[id_col].values[test_idx]
    else:
        test_ids = np.arange(len(test_idx))

    submission = pd.DataFrame({
        'id':     test_ids,
        'target': test_preds,
    })
    submission.to_csv(SUBMISSION_PATH, index=False)
    print(f"  Submission saved → {SUBMISSION_PATH}")
    print(f"  Rows: {len(submission):,} | Columns: {list(submission.columns)}")

    print("\n" + "=" * 65)
    print("  TI Sigma Hypercomputer v1 — Hull Tactical COMPLETE")
    print(f"  OOF ρ = {metrics['oof_spearman']:+.4f} | {n_feat} HC features")
    print(f"  Deadline: June 16, 2026 | Prize: $100,000")
    print("=" * 65)


if __name__ == '__main__':
    main()
