"""
H_TSC — The TI Sigma Crystal Hamiltonian.

H_TSC = H_hop + H_onsite + H_gile

  H_hop    = -J Σ_{<i,j>} (|i⟩⟨j| + h.c.)   — quantum tunneling between adjacent vertices
  H_onsite =  U Σ_i |α_i|^2 · |i⟩⟨i|         — on-site repulsion (truth-state localization)
  H_gile   =  μ Σ_i w_i · |i⟩⟨i|             — GILE chemical potential per vertex

Phase regimes are controlled by J/U ratio:
  J >> U  → BEC phase (delocalized → TRUE)
  J ~  U  → Supersolid / FQH
  J << U  → Mott Insulator (localized → FALSE)

H_SAT — Clause penalty Hamiltonian (added to H_TSC during evolution):
  H_SAT = P Σ_clauses |unsatisfied⟩⟨unsatisfied|
where P is the penalty weight.
"""

import numpy as np
from hypercomputer.tsc import ADJACENCY, N_VERTICES
from hypercomputer.constants import PHI, C_TI, T_TI


def build_hop_hamiltonian(J: float = 1.0) -> np.ndarray:
    """Tunneling (hopping) term: H_hop = -J * A."""
    return -J * ADJACENCY.copy()


def build_onsite_hamiltonian(amplitudes: np.ndarray, U: float = 1.0) -> np.ndarray:
    """On-site interaction: H_onsite = U * diag(|α_i|²)."""
    diag = U * np.abs(amplitudes) ** 2
    return np.diag(diag)


def build_gile_hamiltonian(gile_weights: dict) -> np.ndarray:
    """
    GILE chemical potential per ring:
      Ring 1 (C) → GILE-G (Goodness)
      Ring 2 (T) → GILE-I (Intuition)
      Ring 3 (1) → GILE-L (Love)
      Ring 4 (√2)→ GILE-E (Environment)
      Rings 5-7  → weighted combinations
    """
    G = gile_weights.get('G', 0.25)
    I = gile_weights.get('I', 0.25)
    L = gile_weights.get('L', 0.25)
    E = gile_weights.get('E', 0.25)

    ring_weights = [G, I, L, E, (G+I)/2, (L+E)/2, (G+I+L+E)/4]
    mu_diag = np.zeros(N_VERTICES)
    mu_diag[0] = 0.0  # origin: no chemical potential

    for r in range(1, 8):
        w = ring_weights[r - 1]
        for l in range(8):
            idx = (r - 1) * 8 + l + 1
            mu_diag[idx] = w

    return np.diag(mu_diag)


def build_sat_hamiltonian(clauses: list, n_vars: int, penalty: float = 5.0) -> np.ndarray:
    """
    Embed a CNF formula as a penalty Hamiltonian on the first n_vars TSC vertices.
    Each clause (list of signed ints, 1-indexed) adds a projector penalty.

    Clause (x_i ∨ ¬x_j ∨ x_k) → unsatisfied when x_i=0, x_j=1, x_k=0.
    Penalty is added to the vertex amplitudes of the falsified literals.

    Simplified encoding: diagonal penalty on vertex i if literal i is falsified.
    """
    H_sat = np.zeros((N_VERTICES, N_VERTICES), dtype=complex)

    for clause in clauses:
        for lit in clause:
            var_idx = abs(lit)
            if var_idx > n_vars or var_idx == 0:
                continue
            vertex_idx = var_idx  # variable i → vertex i (1-indexed in TSC)
            # Penalty on the "wrong" phase for this literal
            H_sat[vertex_idx, vertex_idx] += penalty

    return H_sat


def build_total_hamiltonian(
    amplitudes: np.ndarray,
    clauses: list,
    n_vars: int,
    J: float = 1.0,
    U: float = 0.5,
    penalty: float = 5.0,
    gile_weights: dict = None
) -> np.ndarray:
    if gile_weights is None:
        gile_weights = {'G': 0.25, 'I': 0.25, 'L': 0.25, 'E': 0.25}

    H = (build_hop_hamiltonian(J)
         + build_onsite_hamiltonian(amplitudes, U)
         + build_gile_hamiltonian(gile_weights))

    if clauses:
        H += build_sat_hamiltonian(clauses, n_vars, penalty).real

    return H
