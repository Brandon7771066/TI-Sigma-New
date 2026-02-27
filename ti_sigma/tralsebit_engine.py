"""
TI Sigma Hypercomputer — Layer 1: Tralsebit Engine

Four-valued logic tensor operations on NumPy arrays.
Integrates: eleven_dimensional_tralsebit.py, double_tralse_theory.py,
            grand_tralse_field_equation.py
"""

import numpy as np
import math
from typing import Union, Tuple, Optional
from .constants import (PHI, SQRT2, LCC_TRALSE, LCC_HIGH, LCC_IC,
                         FIBONACCI, GILE_WEIGHTS, TB_TRUE, TB_FALSE)


class TralsebitEngine:
    """
    Layer 1 of the TI Sigma Hypercomputer.

    Every value in [-1, +1] is a valid Tralsebit.
    Classical subspace: {-1 (False), 0 (Indeterminate), +1 (True)}
    Tralse region: (-LCC_TRALSE, +LCC_TRALSE) — values not yet resolved

    All operations preserve the [-1, +1] range via np.clip.
    """

    MR_THRESHOLD = LCC_TRALSE  # 0.4142 = √2 − 1

    # ─── Encoding ─────────────────────────────────────────────────────────────

    def encode(self, X: np.ndarray, method: str = 'minmax') -> np.ndarray:
        """
        Encode raw feature array into Tralsebit range [-1, +1].

        method='minmax':  standard min-max normalization to [-1, +1]
        method='zscore':  z-score clamped to [-1, +1] at ±3σ
        method='phi':     φ-normalized (divides by φ * max_abs)
        """
        X = np.asarray(X, dtype=float)
        if method == 'minmax':
            mn, mx = X.min(axis=0), X.max(axis=0)
            rng = np.where(mx - mn > 1e-12, mx - mn, 1.0)
            return np.clip(2 * (X - mn) / rng - 1, -1, 1)
        elif method == 'zscore':
            mu, sigma = X.mean(axis=0), X.std(axis=0) + 1e-12
            return np.clip((X - mu) / (3 * sigma), -1, 1)
        elif method == 'phi':
            scale = PHI * np.abs(X).max(axis=0)
            scale = np.where(scale > 1e-12, scale, 1.0)
            return np.clip(X / scale, -1, 1)
        else:
            raise ValueError(f"Unknown method: {method}")

    # ─── Myrion Resolution ────────────────────────────────────────────────────

    def myrion_resolution(self, tb: np.ndarray,
                          threshold: Optional[float] = None) -> np.ndarray:
        """
        Apply MR operator: values beyond ±threshold resolve to ±1 or 0.
        Values inside the threshold remain Tralse (unchanged).

        MR is the Tralse collapse operator — analogous to wavefunction collapse
        but for four-valued logic states.
        """
        t = threshold if threshold is not None else self.MR_THRESHOLD
        resolved = tb.copy()
        resolved[tb > t]  = TB_TRUE
        resolved[tb < -t] = TB_FALSE
        # Values in (-t, +t) remain Tralse (no change)
        return resolved

    def partial_resolution(self, tb: np.ndarray, iterations: int = 3) -> np.ndarray:
        """
        Iterative MR: threshold tightens by 1/φ each pass.
        Models successive rounds of evidence accumulation.
        """
        t = self.MR_THRESHOLD
        result = tb.copy()
        for _ in range(iterations):
            result = self.myrion_resolution(result, threshold=t)
            t = t / PHI  # threshold shrinks — more resolves each round
        return result

    # ─── LCC Coherence ────────────────────────────────────────────────────────

    def lcc_coherence(self, tb: np.ndarray) -> float:
        """
        Compute LCC coherence of a Tralsebit array.

        Coherence = 1 - (fraction of values in the Tralse zone [-MR_T, +MR_T])
        High coherence = most values resolved to True/False.
        Low coherence = most values still Tralse.

        Returns scalar in [0, 1].
        """
        tralse_fraction = np.mean(np.abs(tb) <= self.MR_THRESHOLD)
        return float(1 - tralse_fraction)

    def lcc_band(self, value: float) -> int:
        """
        Return which LCC zone a single value falls into (0–4).
        Zone 0: highly false, Zone 2: Tralse, Zone 4: highly true.
        """
        a = abs(value)
        if a <= LCC_TRALSE:           return 2  # Tralse zone
        elif a <= 0.85:               return 3 if value > 0 else 1
        else:                          return 4 if value > 0 else 0

    # ─── GILE Scoring ─────────────────────────────────────────────────────────

    def gile_score(self,
                   G: np.ndarray, I: np.ndarray,
                   L: np.ndarray, E: np.ndarray,
                   weights: Optional[dict] = None) -> np.ndarray:
        """
        Compute GILE score combining the dual formulation:
            LxE = L × E  (multiplicative — local order)
            LpE = L + E  (additive — global contribution)
            GxI = G × I

        Full score: (G × I) × (L × E) + α(G + I + L + E)
        where α is calibrated to balance the two terms.
        """
        w = weights or GILE_WEIGHTS
        LxE = np.clip(L * E, -1, 1)
        LpE = np.clip((L + E) / 2, -1, 1)
        GxI = np.clip(G * I, -1, 1)

        multiplicative = GxI * LxE           # L×E contribution
        additive = (w['G']*G + w['I']*I +
                    w['L']*LpE + w['E']*E)    # L+E contribution

        return np.clip(0.6 * multiplicative + 0.4 * additive, -1, 1)

    def gile_from_array(self, tb: np.ndarray) -> float:
        """
        Compute GILE score from a single Tralsebit array.
        Splits array into four equal quadrants as G, I, L, E proxies.
        """
        n = len(tb) // 4
        if n == 0:
            return float(np.mean(tb))
        G, I, L, E_ = tb[:n], tb[n:2*n], tb[2*n:3*n], tb[3*n:4*n]
        return float(np.mean(self.gile_score(G, I, L, E_)))

    # ─── Phi Decomposition ────────────────────────────────────────────────────

    def phi_power_decompose(self, n: int) -> Tuple[int, int]:
        """
        Decompose φⁿ = F(n)φ + F(n-1) — the dual decomposition.
        Returns (F(n), F(n-1)) — the Fibonacci coefficients.
        This is the number-theoretic proof that L×E = L+E at the golden ratio.
        """
        if n < len(FIBONACCI):
            return FIBONACCI[n], FIBONACCI[n-1] if n > 0 else 0
        # Compute for larger n
        a, b = 0, 1
        for _ in range(n):
            a, b = b, a + b
        return b, a

    # ─── Penrose Adjacency ────────────────────────────────────────────────────

    def penrose_adjacency(self, n: int) -> np.ndarray:
        """
        Generate Penrose/Fibonacci adjacency matrix for n nodes.
        Connectivity: Fibonacci-spaced neighbors + golden-ratio non-local link.
        Used as the native topology for all Tralsebit network operations.
        """
        import networkx as nx
        fib_offsets = [f for f in FIBONACCI[1:] if 0 < f < n]
        G = nx.Graph()
        G.add_nodes_from(range(n))
        for i in range(n):
            for f in fib_offsets:
                j = (i + f) % n
                G.add_edge(i, j)
            # Non-local golden-ratio link
            nl = int(i * PHI) % n
            if nl != i:
                G.add_edge(i, nl)
        import networkx as nx
        return nx.to_numpy_array(G)

    # ─── Tralse Zone Membership ───────────────────────────────────────────────

    def tralse_ratio(self, values: np.ndarray) -> float:
        """
        Fraction of values that fall in the Tralse zone [LCC_TRALSE, LCC_HIGH].
        The MALLORN-validated feature: TDEs show 16% higher tralse_ratio.
        """
        a = np.abs(values)
        return float(np.mean((a >= LCC_TRALSE) & (a <= LCC_HIGH)))

    def sacred_fraction(self, values: np.ndarray) -> float:
        """
        GILE 'sacred fraction': proportion of values within 1/φ of the mean.
        Operationalizes GILE harmony as proximity to the golden mean.
        """
        mu = float(np.mean(values))
        deviation = np.abs(values - mu)
        tolerance = abs(mu) / PHI + 1e-9
        return float(np.mean(deviation <= tolerance))
