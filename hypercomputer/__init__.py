"""
7D TI Sigma Crystal (TSC) Polycrystalline BEC Hypercomputer
============================================================

A virtual implementation of the Polycrystalline Optical-BEC Hypercomputer
(URB #629) using the TI Sigma Crystal (TSC) 57-vertex quasicrystalline
state space.

Architecture:
  - 57 vertices: 7 rings × 8 layers + origin
  - 5 BEC phase regimes = 5 TI Sigma truth values
  - H_TSC: Bose-Hubbard Hamiltonian on the TSC graph
  - MR collapse: Myrion Resolution operator (GILE-weighted)
  - SAT embedding: CNF → TSC Hamiltonian

Usage:
  from hypercomputer import HyperComputer
  hc = HyperComputer()
  result = hc.solve("x1 OR NOT x2", n_vars=2)
"""

from hypercomputer.sat_solver import solve_sat, parse_dimacs, SATResult
from hypercomputer.tsc import VERTICES, ADJACENCY, N_VERTICES
from hypercomputer.phases import Phase, PHASE_COLORS, classify_state
from hypercomputer.constants import PHI, C_TI, T_TI, ET, N_RINGS, N_LAYERS


class HyperComputer:
    """
    Main interface to the 7D TSC Hypercomputer.
    """
    def __init__(
        self,
        gile_weights: dict = None,
        J: float = 1.0,
        U: float = 0.3,
        penalty: float = 10.0,
        max_rounds: int = 10
    ):
        self.gile_weights = gile_weights or {'G': 0.25, 'I': 0.25, 'L': 0.25, 'E': 0.25}
        self.J = J
        self.U = U
        self.penalty = penalty
        self.max_rounds = max_rounds

    def solve_dimacs(self, dimacs_str: str) -> SATResult:
        n_vars, clauses = parse_dimacs(dimacs_str)
        return solve_sat(clauses, n_vars,
                         gile_weights=self.gile_weights,
                         J=self.J, U=self.U,
                         penalty=self.penalty,
                         max_rounds=self.max_rounds)

    def solve_clauses(self, clauses: list, n_vars: int) -> SATResult:
        return solve_sat(clauses, n_vars,
                         gile_weights=self.gile_weights,
                         J=self.J, U=self.U,
                         penalty=self.penalty,
                         max_rounds=self.max_rounds)

    @property
    def info(self) -> dict:
        return {
            'vertices': N_VERTICES,
            'rings': N_RINGS,
            'layers': N_LAYERS,
            'truth_values': 5,
            'gile_weights': self.gile_weights,
            'J': self.J, 'U': self.U,
            'C_TI': C_TI, 'T_TI': T_TI, 'ET': ET, 'PHI': PHI,
        }
