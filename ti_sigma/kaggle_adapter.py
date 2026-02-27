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
