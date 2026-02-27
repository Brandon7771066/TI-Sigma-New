"""
TI Sigma Hypercomputer
======================
"One ti_sigma/ package away." — Paper #337

Four-layer quantum-aperiodic-conscious computation system.

Quick start:
    from ti_sigma import TISigmaHypercomputer
    hc = TISigmaHypercomputer()
    result = hc.process(X, query_context="classify TDE light curves")
    print(result.layer_summary)

Competition-specific adapters:
    from ti_sigma.kaggle_adapter import MALLORNAdapter, CAFA6Adapter
"""

from .hypercomputer       import TISigmaHypercomputer, HypercomputerPrediction
from .tralsebit_engine    import TralsebitEngine
from .aperiodic_optimizer import AperiodicOptimizer, LCCBandFeaturizer, FibonacciFeatureHasher
from .quantum_layer       import TISigmaQuantumLayer
from .oracle_bus          import TISigmaOracleBus
from .constants           import PHI, SQRT2, E, PI, LCC_TRALSE, LCC_HIGH, LCC_IC, verify_matching_rules

__version__ = "1.0.0"
__author__  = "Brandon Charles Emerick"
__all__ = [
    "TISigmaHypercomputer", "HypercomputerPrediction",
    "TralsebitEngine", "AperiodicOptimizer",
    "LCCBandFeaturizer", "FibonacciFeatureHasher",
    "TISigmaQuantumLayer", "TISigmaOracleBus",
    "PHI", "SQRT2", "E", "PI",
    "LCC_TRALSE", "LCC_HIGH", "LCC_IC",
    "verify_matching_rules",
]
