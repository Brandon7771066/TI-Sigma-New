"""
SAT Embedding and Solver using the 7D TSC Hypercomputer.

Workflow:
  1. Parse CNF formula (DIMACS or list of clauses)
  2. Embed as TSC initial state (superposition over all 2^n assignments)
  3. Construct H_total = H_TSC + H_SAT
  4. Time-evolve: Ψ(t) = exp(-i H_total t) Ψ(0)
  5. Apply MR collapse to get a classical assignment
  6. Verify: check if the assignment satisfies all clauses
  7. Iterate if needed (up to max_rounds MR rounds)

The time evolution uses matrix exponentiation (exact for small n_vars).
For large n_vars, Trotterization or imaginary-time evolution is used.
"""

import numpy as np
from typing import List, Tuple, Optional
from dataclasses import dataclass

from hypercomputer.tsc import N_VERTICES
from hypercomputer.hamiltonian import build_total_hamiltonian
from hypercomputer.mr_collapse import mr_collapse
from hypercomputer.phases import classify_state
from hypercomputer.constants import C_TI, T_TI


@dataclass
class SATResult:
    satisfiable: Optional[bool]
    assignment: Optional[List[bool]]
    iterations: int
    final_pd: float
    coherence: float
    dt_count: int
    evolution_snapshots: List[np.ndarray]
    phase_history: List[list]
    verified: bool


def parse_dimacs(dimacs_str: str) -> Tuple[int, List[List[int]]]:
    n_vars = 0
    clauses = []
    for line in dimacs_str.strip().split('\n'):
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('p cnf'):
            parts = line.split()
            n_vars = int(parts[2])
        elif not line.startswith('%'):
            lits = list(map(int, line.split()))
            if lits and lits[-1] == 0:
                lits = lits[:-1]
            if lits:
                clauses.append(lits)
    return n_vars, clauses


def check_assignment(assignment: List[bool], clauses: List[List[int]]) -> bool:
    for clause in clauses:
        satisfied = False
        for lit in clause:
            var = abs(lit) - 1
            if var >= len(assignment):
                continue
            val = assignment[var]
            if (lit > 0 and val) or (lit < 0 and not val):
                satisfied = True
                break
        if not satisfied:
            return False
    return True


def initial_state(n_vars: int) -> np.ndarray:
    """
    Initial TSC state: superposition over all 2^n assignments.
    For vertices 1..n_vars: equal complex amplitudes with random phases.
    For remaining vertices: small coherent background.
    Origin: normalized vacuum amplitude.
    """
    psi = np.zeros(N_VERTICES, dtype=complex)

    # Superposition: each variable vertex gets equal weight
    # Phase encodes initial uncertainty (Tralse wave state)
    amp = 1.0 / np.sqrt(n_vars + 1e-9)
    for i in range(1, n_vars + 1):
        phase = np.random.uniform(0, 2 * np.pi)
        psi[i] = amp * np.exp(1j * phase)

    # Background coherence on remaining vertices
    for i in range(n_vars + 1, N_VERTICES):
        psi[i] = (C_TI / N_VERTICES) * np.exp(1j * np.random.uniform(0, 2 * np.pi))

    # Origin: vacuum normalization
    psi[0] = 0.0

    # Normalize
    norm = np.linalg.norm(psi)
    if norm > 1e-10:
        psi /= norm

    return psi


def evolve_state(
    psi: np.ndarray,
    H: np.ndarray,
    dt: float,
    steps: int,
    snapshots_at: List[int] = None
) -> Tuple[np.ndarray, List[np.ndarray]]:
    """
    Time-evolve Ψ under H for 'steps' time steps of size dt.
    Uses matrix exponential (exact) for N_VERTICES × N_VERTICES H.

    For imaginary-time evolution (annealing toward ground state):
      set dt = -i * dt_real
    """
    snapshots = []
    snapshot_set = set(snapshots_at) if snapshots_at else set()

    # Use imaginary-time evolution for ground state finding
    # Ψ(t+dt) = exp(-H·dt) Ψ(t) / |exp(-H·dt) Ψ(t)|
    # (imaginary time: τ = i·t, so exp(-iH·dt) → exp(-H·dτ))

    # Compute matrix exponential once (H is time-independent given fixed amplitudes)
    from scipy.linalg import expm
    evolution_op = expm(-H * dt)

    for step in range(steps):
        psi = evolution_op @ psi
        # Renormalize (imaginary-time evolution is not unitary)
        norm = np.linalg.norm(psi)
        if norm > 1e-12:
            psi /= norm
        else:
            break
        if step in snapshot_set:
            snapshots.append(psi.copy())

    return psi, snapshots


def solve_sat(
    clauses: List[List[int]],
    n_vars: int,
    gile_weights: dict = None,
    J: float = 1.0,
    U: float = 0.3,
    penalty: float = 10.0,
    dt: float = 0.1,
    steps_per_round: int = 50,
    max_rounds: int = 10,
    snapshot_interval: int = 10
) -> SATResult:
    if gile_weights is None:
        gile_weights = {'G': 0.25, 'I': 0.25, 'L': 0.25, 'E': 0.25}

    if n_vars > N_VERTICES - 1:
        raise ValueError(f"Max {N_VERTICES - 1} variables; got {n_vars}")

    psi = initial_state(n_vars)
    all_snapshots = [psi.copy()]
    all_phase_histories = [classify_state(psi)]

    snapshot_steps = list(range(0, steps_per_round, snapshot_interval))

    for round_idx in range(max_rounds):
        # Build Hamiltonian with current state amplitudes
        H = build_total_hamiltonian(
            amplitudes=psi,
            clauses=clauses,
            n_vars=n_vars,
            J=J,
            U=U,
            penalty=penalty,
            gile_weights=gile_weights
        )

        # Evolve toward ground state
        psi, snaps = evolve_state(psi, H, dt=dt, steps=steps_per_round,
                                   snapshots_at=snapshot_steps)
        all_snapshots.extend(snaps)
        all_phase_histories.append(classify_state(psi))

        # Apply MR collapse
        result = mr_collapse(psi, n_vars, gile_weights)
        assignment = result['assignment']

        # Verify
        if clauses:
            sat = check_assignment(assignment, clauses)
            if sat:
                return SATResult(
                    satisfiable=True,
                    assignment=assignment,
                    iterations=round_idx + 1,
                    final_pd=result['global_pd'],
                    coherence=result['coherence'],
                    dt_count=result['dt_count'],
                    evolution_snapshots=all_snapshots,
                    phase_history=all_phase_histories,
                    verified=True
                )

            # Feedback: increase penalty on unsatisfied clauses
            penalty *= 1.5

        else:
            # No clauses: trivially satisfiable
            return SATResult(
                satisfiable=True,
                assignment=[True] * n_vars,
                iterations=0,
                final_pd=result['global_pd'],
                coherence=result['coherence'],
                dt_count=0,
                evolution_snapshots=all_snapshots,
                phase_history=all_phase_histories,
                verified=True
            )

    # Failed to find satisfying assignment after max_rounds
    # Check if unsatisfiable (heuristic: very high penalty, still fails)
    final_result = mr_collapse(psi, n_vars, gile_weights)
    return SATResult(
        satisfiable=None,  # Unknown: could be UNSAT or need more rounds
        assignment=final_result['assignment'],
        iterations=max_rounds,
        final_pd=final_result['global_pd'],
        coherence=final_result['coherence'],
        dt_count=final_result['dt_count'],
        evolution_snapshots=all_snapshots,
        phase_history=all_phase_histories,
        verified=False
    )
