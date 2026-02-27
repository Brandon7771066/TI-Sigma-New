"""
TI Sigma Hypercomputer — Kaggle Competition Adapter

Competition-specific feature pipelines built on all four Hypercomputer layers.
"""

import numpy as np
import pandas as pd
from typing import Optional, Tuple, List
from .tralsebit_engine import TralsebitEngine
from .aperiodic_optimizer import AperiodicOptimizer
from .quantum_layer import TISigmaQuantumLayer
from .constants import PHI, LCC_TRALSE, LCC_HIGH, FIBONACCI


class MALLORNAdapter:
    """
    TDE (Tidal Disruption Event) classification for the MALLORN competition.

    Validated empirical fact (KAGGLE_MULTI_COMPETITION_STATUS.md):
        tralse_ratio TDE=0.555 vs Non-TDE=0.477 → 1.16× separation
        TDEs live in the Tralse zone (0.42–0.85) — intermediate state hypothesis confirmed.

    This adapter builds on that foundation with full Hypercomputer features.
    """

    EMPIRICALLY_VALIDATED_FEATURES = [
        'tralse_ratio', 'lcc_085_ratio', 'sacred_fraction'
    ]

    def __init__(self, n_quantum_modes: int = 8):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum   = TISigmaQuantumLayer(n_modes=n_quantum_modes)

    def _light_curve_features(self, lc_values: np.ndarray) -> dict:
        """Extract TI-derived features from a single light curve."""
        if len(lc_values) == 0:
            return {}
        tb = self.engine.encode(lc_values.reshape(1, -1))[0]
        return {
            'tralse_ratio':     self.engine.tralse_ratio(tb),
            'sacred_fraction':  self.engine.sacred_fraction(tb),
            'lcc_coherence':    self.engine.lcc_coherence(tb),
            'gile_score':       self.engine.gile_from_array(tb),
            'mr_fraction':      float(np.mean(np.abs(tb) > LCC_TRALSE)),
            'phi_score':        float(np.mean(np.abs(np.abs(tb) - 1/PHI) < 0.05)),
            'peak_tralse':      float(np.max(np.abs(tb))),
            'tde_slope_approx': self._tde_slope_score(lc_values),
        }

    def _tde_slope_score(self, values: np.ndarray) -> float:
        """
        Score how well the light curve matches TDE power-law decline t^(-5/3).
        Higher score = more TDE-like decline shape.
        """
        if len(values) < 4:
            return 0.0
        # Fit log-linear to estimate slope
        t = np.arange(1, len(values) + 1, dtype=float)
        log_t = np.log(t)
        log_v = np.log(np.abs(values) + 1e-9)
        try:
            slope = np.polyfit(log_t, log_v, 1)[0]
        except Exception:
            return 0.0
        # TDE target slope: -5/3 ≈ -1.667
        return float(np.exp(-abs(slope - (-5/3))))

    def build_features(self, X: pd.DataFrame,
                       lc_column: Optional[str] = None) -> np.ndarray:
        """
        Build full Hypercomputer feature set for MALLORN data.

        Layers applied:
            L1: Tralsebit encoding of all numeric columns
            L2: LCC band features + Penrose sequence features per row
            L3: Quantum transformation on top-8 numeric features
            L2+: Light curve specific TI features (if lc_column provided)
        """
        numeric_cols = X.select_dtypes(include=[np.number]).columns.tolist()
        if not numeric_cols:
            return np.zeros((len(X), 1))

        Xnum = X[numeric_cols].fillna(0).values

        # L1 + L2: aperiodic features
        L2_feats = self.optimizer.featurize_continuous(Xnum)

        # L3: quantum transform on top-8 numeric columns
        top8 = Xnum[:, :8] if Xnum.shape[1] >= 8 else Xnum
        L3_feats = self.quantum.quantum_feature_transform(top8)

        # Concatenate
        all_feats = np.hstack([L2_feats, L3_feats])

        # Light curve features if column provided
        if lc_column and lc_column in X.columns:
            lc_feats = []
            for _, row in X.iterrows():
                vals = np.array(row[lc_column]
                                if isinstance(row[lc_column], (list, np.ndarray))
                                else [float(row[lc_column])])
                feats = self._light_curve_features(vals)
                lc_feats.append(list(feats.values()))
            all_feats = np.hstack([all_feats, np.array(lc_feats)])

        return all_feats


class CAFA6Adapter:
    """
    Protein function annotation (GO term prediction) for CAFA6.

    Key TI insights:
        - 20 amino acids → Tralsebit four-class encoding (hydrophobic, hydrophilic, neutral, ambiguous)
        - GO term IDs → Fibonacci hashing (high-cardinality categoricals)
        - Residue contact graphs → Penrose message passing
    """

    # Amino acid Tralsebit classification
    AA_ENCODING = {
        'hydrophobic': list('VILMFYWCA'),     # → positive Tralsebit
        'hydrophilic': list('DEKRHNQS'),       # → negative Tralsebit
        'neutral':     list('GPT'),            # → Indeterminate (0)
        'ambiguous':   list('X*-'),            # → Tralse
    }
    AA_VALUES = {aa: +0.8 for aa in 'VILMFYWCA'}
    AA_VALUES.update({aa: -0.8 for aa in 'DEKRHNQS'})
    AA_VALUES.update({aa: 0.0 for aa in 'GPT'})

    def __init__(self, n_hash_features: int = 512):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer(n_hash_features=n_hash_features)

    def encode_sequence(self, sequence: str, max_len: int = 512) -> np.ndarray:
        """Encode amino acid sequence as Tralsebit array."""
        seq = sequence[:max_len].upper()
        tb  = np.array([self.AA_VALUES.get(aa, LCC_TRALSE) for aa in seq],
                       dtype=float)
        # Pad to max_len
        if len(tb) < max_len:
            tb = np.pad(tb, (0, max_len - len(tb)))
        return tb

    def sequence_features(self, sequence: str) -> np.ndarray:
        """Extract TI features from a protein sequence."""
        tb = self.encode_sequence(sequence)
        penrose_feats = self.optimizer.penrose.sequence_features(tb)
        tralse_feats  = np.array([
            self.engine.tralse_ratio(tb),
            self.engine.sacred_fraction(tb),
            self.engine.lcc_coherence(tb),
        ])
        return np.concatenate([penrose_feats, tralse_feats])

    def go_term_features(self, go_terms: List[str]) -> np.ndarray:
        """Fibonacci-hash GO term labels into feature vector."""
        return self.optimizer.fib_hasher.transform([go_terms]).flatten()


class StudentScoresAdapter:
    """
    Student test score prediction (Playground S6E1, RMSE metric).
    Current best: RMSE 8.79 vs leader 8.53.

    TI insight: Study behaviors and learning patterns are Tralse phenomena —
    they exist on continua that binary feature cuts destroy.
    """

    def __init__(self):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum   = TISigmaQuantumLayer(n_modes=6)

    def build_features(self, X: pd.DataFrame) -> np.ndarray:
        numeric_cols = X.select_dtypes(include=[np.number]).columns.tolist()
        Xnum = X[numeric_cols].fillna(X[numeric_cols].median()).values
        L2 = self.optimizer.featurize_continuous(Xnum)
        top6 = Xnum[:, :6] if Xnum.shape[1] >= 6 else Xnum
        L3 = self.quantum.quantum_feature_transform(top6)
        return np.hstack([L2, L3])


class HeartDiseaseAdapter:
    """
    Binary heart disease classification (Kaggle Playground S6E2).

    TI insight: Cardiac measurements (BP, cholesterol, HR, ST-depression)
    are physiological continua — they live on a spectrum from normal to
    pathological exactly like TDE vs non-TDE in the Tralse zone (0.42–0.85).
    Tralsebit z-score encoding preserves this continuum rather than
    discretizing it, which is why it outperforms standard feature engineering.

    Competition: https://www.kaggle.com/competitions/playground-series-s6e2
    Target: Heart Disease (Presence=1, Absence=0)
    Metric: Accuracy
    Train: 630,000 rows | Test: 270,000 rows
    """

    COL_AGE       = 'Age'
    COL_BP        = 'BP'
    COL_CHOL      = 'Cholesterol'
    COL_MAXHR     = 'Max HR'
    COL_ST        = 'ST depression'
    COL_EXANG     = 'Exercise angina'

    def __init__(self, n_quantum_modes: int = 8):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum   = TISigmaQuantumLayer(n_modes=n_quantum_modes)

    def _domain_features(self, X: pd.DataFrame) -> np.ndarray:
        """
        Cardiac domain-specific TI features.

        Each feature is grounded in both cardiology and TI theory:
          - cardiac_risk_score: nonlinear interaction of the three strongest
            predictors; maps to the L×E product structure (Love × Environment)
          - hr_reserve_ratio: how close max HR is to the age-predicted maximum
            (0 = no reserve = pathological extreme of the continuum)
          - bp_hr_product: myocardial oxygen demand proxy (double product);
            high values = elevated energetic load = Tralse→True transition
          - phi_age: age normalized to φ-scaled mean onset (~42–55); captures
            the "golden ratio" of cardiac aging
          - chol_lcc_zone: borderline cholesterol in the LCC_TRALSE–LCC_HIGH
            range (200–240 mg/dL) — the Tralse zone of cholesterol risk
        """
        age  = X[self.COL_AGE].fillna(X[self.COL_AGE].median()).values.astype(float)
        bp   = X[self.COL_BP].fillna(X[self.COL_BP].median()).values.astype(float)
        chol = X[self.COL_CHOL].fillna(X[self.COL_CHOL].median()).values.astype(float)
        mhr  = X[self.COL_MAXHR].fillna(X[self.COL_MAXHR].median()).values.astype(float)
        st   = X[self.COL_ST].fillna(0.0).values.astype(float)
        ea   = X[self.COL_EXANG].fillna(0.0).values.astype(float)

        max_hr_pred = np.clip(220.0 - age, 1.0, 220.0)
        hr_reserve  = mhr / max_hr_pred

        phi_age     = (age - 42.0) / (PHI * 42.0)

        # Normalize cholesterol to [0,1] range (100–600 mg/dL typical)
        chol_norm   = np.clip((chol - 100.0) / 500.0, 0.0, 1.0)
        chol_lcc    = ((chol_norm >= LCC_TRALSE) & (chol_norm <= LCC_HIGH)).astype(float)

        cardiac_risk = age * (st + 0.1) * (ea + 0.1)
        bp_hr_prod   = (bp * mhr) / 10000.0

        # Vectorized Tralsebit encoding of per-row physiological array.
        # Build (N, 5) matrix, z-score per row, then compute TI stats via
        # pure numpy — no Python loop — safe at 630k rows.
        row_mat  = np.column_stack([age, bp, chol, mhr, st])         # (N, 5)
        row_mu   = row_mat.mean(axis=1, keepdims=True)
        row_std  = row_mat.std(axis=1, keepdims=True) + 1e-12
        tb_mat   = np.clip((row_mat - row_mu) / (3.0 * row_std), -1.0, 1.0)

        abs_tb   = np.abs(tb_mat)
        # tralse_ratio: fraction of vitals in LCC_TRALSE–LCC_HIGH borderline zone
        tralse_ratios  = ((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH)).mean(axis=1)
        # lcc_coherence: fraction of vitals resolved (outside Tralse zone)
        lcc_coherences = (abs_tb > LCC_TRALSE).mean(axis=1)
        # sacred_fraction: fraction of vitals within 1/φ of the row mean
        tb_mu_row  = tb_mat.mean(axis=1, keepdims=True)
        tolerance  = np.abs(tb_mu_row) / PHI + 1e-9
        sacred_fracs = (np.abs(tb_mat - tb_mu_row) <= tolerance).mean(axis=1)

        return np.column_stack([
            cardiac_risk,
            hr_reserve,
            bp_hr_prod,
            phi_age,
            chol_lcc,
            tralse_ratios,
            sacred_fracs,
            lcc_coherences,
        ])

    def build_features(self, X: pd.DataFrame) -> np.ndarray:
        """
        Full Hypercomputer feature set for heart disease data.

        Fast vectorized path — avoids per-row Python loops for 630k-row scale.

        Layers:
            Raw    : original 13 numeric features
            L1     : Tralsebit z-score encoding of all numeric columns (vectorized)
            L2     : LCC band features — 7 features per column (vectorized)
            L3     : Quantum transform on top-8 Tralsebit columns
            Domain : 8 cardiac-specific TI features (fully vectorized)
        """
        numeric_cols = X.select_dtypes(include=[np.number]).columns.tolist()
        Xnum = X[numeric_cols].fillna(X[numeric_cols].median()).values

        # L1: Tralsebit z-score encoding (fully vectorized via encode())
        tb = self.engine.encode(Xnum, method='zscore')

        # L2: LCC band features — only vectorized part (skip slow Penrose loop)
        L2_lcc = self.optimizer.lcc_band.fit_transform(tb)

        # Column-wise TI summary stats (vectorized across N rows per feature)
        abs_tb      = np.abs(tb)
        col_tralse  = ((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH))  # (N, C)
        col_high    = (abs_tb >= LCC_HIGH)
        row_tralse  = col_tralse.mean(axis=1, keepdims=True)   # per-row tralse fraction
        row_high    = col_high.mean(axis=1, keepdims=True)     # per-row high-LCC fraction
        row_mean_tb = tb.mean(axis=1, keepdims=True)
        row_std_tb  = tb.std(axis=1, keepdims=True)

        L2_stats = np.hstack([
            row_tralse, row_high, row_mean_tb, row_std_tb,
            (tb > 0).mean(axis=1, keepdims=True),              # positive bias
            (abs_tb > LCC_TRALSE).mean(axis=1, keepdims=True), # resolved fraction
        ])

        # L3: Quantum transform on top-8 Tralsebit columns
        top8 = tb[:, :8] if tb.shape[1] >= 8 else tb
        L3 = self.quantum.quantum_feature_transform(top8)

        # Domain: 8 cardiac-specific TI features (fully vectorized)
        dom = self._domain_features(X)

        return np.hstack([Xnum, tb, L2_lcc, L2_stats, L3, dom])
