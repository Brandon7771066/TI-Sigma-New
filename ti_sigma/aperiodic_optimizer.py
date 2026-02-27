"""
TI Sigma Hypercomputer — Layer 2: Aperiodic Optimizer

Fibonacci feature hashing, LCC band featurization, Penrose graph features.
Integrates: simulations/aperiodic_validation.py, lcc_hypercomputer_test_harness.py
"""

import numpy as np
import math
from typing import Optional, List
from collections import defaultdict
from .constants import PHI, SQRT2, LCC_TRALSE, LCC_HIGH, LCC_IC, FIBONACCI
from .tralsebit_engine import TralsebitEngine


class LCCBandFeaturizer:
    """
    Generate 7 LCC-band features from each continuous input column.

    The five bands:
        Zone 0: highly false    [-1.0, -0.85]
        Zone 1: tralse-false   (-0.85, -0.42]
        Zone 2: tralse core    (-0.42, +0.42)   ← most informative
        Zone 3: tralse-true    [+0.42, +0.85)
        Zone 4: highly true    [+0.85, +1.0]

    Output per column: 5 zone indicators + raw value + MR-resolved value = 7 features.
    7 × n_cols total output features.
    """

    THRESHOLDS = [LCC_TRALSE, LCC_HIGH]  # 0.4142, 0.85

    def featurize_column(self, col: np.ndarray) -> np.ndarray:
        """Transform one column into 7 LCC-band features."""
        t_low, t_high = self.THRESHOLDS
        engine = TralsebitEngine()

        z0 = (col <= -t_high).astype(float)
        z1 = ((col > -t_high) & (col <= -t_low)).astype(float)
        z2 = ((col > -t_low) & (col < t_low)).astype(float)
        z3 = ((col >= t_low) & (col < t_high)).astype(float)
        z4 = (col >= t_high).astype(float)
        raw = col.copy()
        mr  = engine.myrion_resolution(col)

        return np.column_stack([z0, z1, z2, z3, z4, raw, mr])

    def fit_transform(self, X: np.ndarray) -> np.ndarray:
        """Apply LCC band featurization to all columns of X."""
        X = np.asarray(X, dtype=float)
        parts = [self.featurize_column(X[:, c]) for c in range(X.shape[1])]
        return np.hstack(parts)


class FibonacciFeatureHasher:
    """
    φ-multiplicative hash for high-cardinality categorical features.

    Outperforms binary (mod) hashing for hash-table collision avoidance
    because φ-multiplication distributes values near-uniformly across
    any hash table size, without clustering at powers of 2.

    This is Knuth's multiplicative hashing with base φ.
    """

    def __init__(self, n_features: int = 512):
        self.n_features = n_features

    def hash_string(self, s: str) -> int:
        raw = hash(s) & 0xFFFFFFFF
        return int((raw * PHI % 1) * self.n_features)

    def hash_integer(self, n: int) -> int:
        return int((n * PHI % 1) * self.n_features)

    def transform(self, categories: List[str]) -> np.ndarray:
        """Hash a list of categorical values into a sparse indicator array."""
        out = np.zeros((len(categories), self.n_features))
        for i, c in enumerate(categories):
            idx = self.hash_string(str(c))
            out[i, idx] = 1.0
        return out

    def transform_multi(self, category_lists: List[List[str]]) -> np.ndarray:
        """Hash multiple categories per row (multi-hot encoding)."""
        out = np.zeros((len(category_lists), self.n_features))
        for i, cats in enumerate(category_lists):
            for c in cats:
                idx = self.hash_string(str(c))
                out[i, idx] += 1.0
        return out


class PenroseGraphFeaturizer:
    """
    Penrose/Fibonacci graph message passing for relational feature sets.

    For any dataset representable as a graph (sequences, molecular structures,
    time series, citation networks), this applies one round of message passing
    using the Penrose lattice topology — Fibonacci-spaced neighbors + non-local
    golden-ratio connections.

    The non-local connections implement the L+E global structure:
    information propagates across the graph along paths that canonical
    GCNs or CNNs cannot access.
    """

    def __init__(self):
        self.engine = TralsebitEngine()

    def build_penrose_graph(self, n: int):
        """Build Penrose adjacency list for n nodes."""
        fib_offsets = [f for f in FIBONACCI[1:] if 0 < f < n]
        adj = defaultdict(set)
        for i in range(n):
            for f in fib_offsets:
                j = (i + f) % n
                adj[i].add(j); adj[j].add(i)
            nl = int(i * PHI) % n
            if nl != i:
                adj[i].add(nl); adj[nl].add(i)
        return adj

    def message_pass(self, features: np.ndarray,
                     n_rounds: int = 2) -> np.ndarray:
        """
        Apply n_rounds of Penrose message passing to a feature sequence.
        features: (n_nodes, n_features) array
        Returns: (n_nodes, n_features) array with aggregated neighbor info.
        """
        n = features.shape[0]
        adj = self.build_penrose_graph(n)
        result = features.copy()
        for _ in range(n_rounds):
            new_result = np.zeros_like(result)
            for i in range(n):
                neighbors = list(adj[i]) + [i]
                new_result[i] = np.mean(result[neighbors], axis=0)
            result = new_result
        return result

    def sequence_features(self, sequence: np.ndarray) -> np.ndarray:
        """
        Extract Penrose-aggregated features from a 1D sequence.
        Treats the sequence as a Penrose lattice of n nodes, 1 feature each.
        Returns the message-passed sequence plus derived statistics.
        """
        seq2d = sequence.reshape(-1, 1)
        passed = self.message_pass(seq2d, n_rounds=2).flatten()
        return np.array([
            np.mean(passed), np.std(passed),
            np.min(passed), np.max(passed),
            self.engine.tralse_ratio(passed),
            self.engine.sacred_fraction(passed),
            self.engine.lcc_coherence(passed),
        ])


class AperiodicOptimizer:
    """
    Layer 2 of the TI Sigma Hypercomputer.
    Orchestrates all three aperiodic optimization modules.
    """

    def __init__(self, n_hash_features: int = 256):
        self.lcc_band     = LCCBandFeaturizer()
        self.fib_hasher   = FibonacciFeatureHasher(n_features=n_hash_features)
        self.penrose      = PenroseGraphFeaturizer()
        self.engine       = TralsebitEngine()

    def featurize_continuous(self, X: np.ndarray) -> np.ndarray:
        """
        Full Layer 2 transformation for continuous feature arrays.
        Returns: original X + LCC-band features + Penrose sequence features.
        """
        X = np.asarray(X, dtype=float)

        # 1. Tralsebit encoding
        tb = self.engine.encode(X)

        # 2. LCC band features (7× column expansion)
        lcc_feats = self.lcc_band.fit_transform(tb)

        # 3. Penrose row-wise features (per sample)
        penrose_feats = np.array([
            self.penrose.sequence_features(row) for row in tb
        ])

        # 4. Holistic Tralse scores per sample
        tralse_scores = np.array([
            [self.engine.tralse_ratio(row),
             self.engine.sacred_fraction(row),
             self.engine.lcc_coherence(row),
             self.engine.gile_from_array(row)]
            for row in tb
        ])

        return np.hstack([X, tb, lcc_feats, penrose_feats, tralse_scores])

    def featurize_categorical(self, categories: List[List[str]]) -> np.ndarray:
        """Apply Fibonacci hashing to multi-hot categorical features."""
        return self.fib_hasher.transform_multi(categories)

    def compute_sample_lcc(self, X: np.ndarray) -> np.ndarray:
        """Return LCC coherence per sample (1D array)."""
        tb = self.engine.encode(X)
        return np.array([self.engine.lcc_coherence(row) for row in tb])
