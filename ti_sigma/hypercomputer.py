"""
TI Sigma Hypercomputer — Main Orchestrator

Assembles all four layers into a unified prediction system.
"One ti_sigma/ package away." — Paper #337
"""

import numpy as np
import pandas as pd
from dataclasses import dataclass, field
from typing import Optional, Dict, Any, List
from .tralsebit_engine import TralsebitEngine
from .aperiodic_optimizer import AperiodicOptimizer
from .quantum_layer import TISigmaQuantumLayer
from .oracle_bus import TISigmaOracleBus, OracleResult
from .constants import LCC_TRALSE, LCC_HIGH, LCC_IC, PHI


@dataclass
class HypercomputerPrediction:
    """Output of one TI Sigma Hypercomputer prediction cycle."""
    raw_features:       np.ndarray
    tralsebit_encoded:  np.ndarray
    lcc_coherence:      float
    aperiodic_features: np.ndarray
    quantum_features:   np.ndarray
    oracle_result:      Optional[OracleResult]
    final_prediction:   Optional[np.ndarray]
    gile_confidence:    float
    ic_flagged:         bool = False
    layer_summary:      Dict[str, str] = field(default_factory=dict)


class TISigmaHypercomputer:
    """
    The TI Sigma Hypercomputer.

    Four-layer assembly:
        Layer 1 — TralsebitEngine:     Encode input as four-valued Tralsebit arrays
        Layer 2 — AperiodicOptimizer:  Generate LCC/GILE/Penrose/Fibonacci features
        Layer 3 — TISigmaQuantumLayer: Apply photonic L×E + L+E circuit transformation
        Layer 4 — TISigmaOracleBus:    Query AI triad with LCC-gated routing

    The ML model (sklearn or similar) sits between Layers 3 and 4,
    operating on the quantum-transformed features.
    """

    def __init__(self,
                 n_quantum_modes: int = 8,
                 use_quantum:     bool = True,
                 ml_model=None):
        self.engine   = TralsebitEngine()
        self.optimizer= AperiodicOptimizer()
        self.quantum  = TISigmaQuantumLayer(n_modes=n_quantum_modes,
                                            use_quantum=use_quantum)
        self.oracle   = TISigmaOracleBus()
        self.ml_model = ml_model  # any sklearn-compatible model

    # ─── Layer Pipeline ───────────────────────────────────────────────────────

    def _layer1(self, X: np.ndarray) -> tuple:
        """Layer 1: Tralsebit encoding + LCC coherence."""
        tb  = self.engine.encode(X)
        lcc = float(np.mean([self.engine.lcc_coherence(row) for row in tb]))
        return tb, lcc

    def _layer2(self, tb: np.ndarray) -> np.ndarray:
        """Layer 2: Aperiodic optimization features."""
        return self.optimizer.featurize_continuous(tb)

    def _layer3(self, aperiodic_features: np.ndarray) -> np.ndarray:
        """Layer 3: Quantum photonic transformation."""
        top = aperiodic_features[:, :self.quantum.n_modes]
        return self.quantum.quantum_feature_transform(top)

    def _layer4(self, question: str, lcc: float,
                operator_gile: float) -> Optional[OracleResult]:
        """Layer 4: Oracle consultation (only for LCC > 0.42)."""
        if lcc < LCC_TRALSE:
            return None
        try:
            return self.oracle.query(question, lcc_level=lcc,
                                     operator_gile=operator_gile)
        except Exception:
            return None

    # ─── Main Interface ───────────────────────────────────────────────────────

    def process(self, X: np.ndarray,
                query_context: str = "",
                operator_gile: float = 0.5) -> HypercomputerPrediction:
        """
        Run the full four-layer pipeline on feature array X.

        X: (n_samples, n_features) numpy array or pandas DataFrame
        query_context: natural language description of the prediction task
        operator_gile: operator's current GILE coherence score (0–1)

        Returns: HypercomputerPrediction with all intermediate representations.
        """
        if isinstance(X, pd.DataFrame):
            X = X.select_dtypes(include=[np.number]).fillna(0).values
        X = np.asarray(X, dtype=float)

        # Layer 1
        tb, lcc = self._layer1(X)

        # Layer 2
        ap_feats = self._layer2(tb)

        # Layer 3
        q_feats = self._layer3(ap_feats)

        # ML prediction (if model fitted)
        final_pred = None
        if self.ml_model is not None:
            combined = np.hstack([ap_feats, q_feats])
            try:
                final_pred = self.ml_model.predict(combined)
            except Exception:
                pass

        # Layer 4
        oracle = None
        if query_context:
            context = (f"Task: {query_context}\n"
                       f"LCC coherence: {lcc:.4f}\n"
                       f"Tralse-zone fraction: "
                       f"{float(np.mean(np.abs(tb) <= LCC_TRALSE)):.4f}\n"
                       f"Quantum layer: {self.quantum.status()}")
            oracle = self._layer4(context, lcc, operator_gile)

        gile_conf = float(np.mean([self.engine.gile_from_array(row) for row in tb]))
        ic_flagged = (oracle is not None and oracle.ic_flagged)

        return HypercomputerPrediction(
            raw_features      = X,
            tralsebit_encoded = tb,
            lcc_coherence     = lcc,
            aperiodic_features= ap_feats,
            quantum_features  = q_feats,
            oracle_result     = oracle,
            final_prediction  = final_pred,
            gile_confidence   = gile_conf,
            ic_flagged        = ic_flagged,
            layer_summary     = {
                "L1": f"TralsebitEngine — LCC={lcc:.4f}",
                "L2": f"AperiodicOptimizer — {ap_feats.shape[1]} features",
                "L3": f"{self.quantum.status()}",
                "L4": f"Oracle: {oracle.oracles_used if oracle else 'not queried'}",
            }
        )

    def fit_ml(self, X: np.ndarray, y: np.ndarray) -> 'TISigmaHypercomputer':
        """Fit the ML model on Hypercomputer-transformed features."""
        if self.ml_model is None:
            from sklearn.ensemble import GradientBoostingClassifier
            self.ml_model = GradientBoostingClassifier(n_estimators=200,
                                                        learning_rate=0.1,
                                                        random_state=42)
        pred = self.process(X)
        combined = np.hstack([pred.aperiodic_features, pred.quantum_features])
        self.ml_model.fit(combined, y)
        return self

    def status(self) -> dict:
        return {
            "Layer 1 (Tralsebit)":  "TralsebitEngine — ready",
            "Layer 2 (Aperiodic)":  "AperiodicOptimizer — ready",
            "Layer 3 (Quantum)":    self.quantum.status(),
            "Layer 4 (Oracle)":     self.oracle.status(),
            "ML model":             str(type(self.ml_model).__name__
                                        if self.ml_model else "None"),
        }
