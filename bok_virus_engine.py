"""
BOK Crystal Virus vs BOK Graph Virus
=====================================
URB #647 — Brandon Emerick | TI Sigma Research | April 2026

Simulates a meme/idea/pathogen spreading through the BOK (Book of Knowledge)
represented as two different structures:

  CRYSTAL BOK: The 57-vertex TSC (TI Sigma Crystal) lattice.
    Transmission is phase-dependent: BEC vertices (inner rings) are super-spreaders;
    Mott/Fragmented vertices (outer rings) act as insulators.
    BEC long-range coupling: Ring-2 (T threshold) vertices can infect non-adjacent
    vertices with small probability — representing quantum non-local coherence.

  GRAPH BOK: An Erdős-Rényi random graph on the same 57 nodes.
    Uniform transmission (classical information-theoretic network).
    No phase effects, no long-range coupling.

Both run SIR (Susceptible → Infected → Recovered) dynamics.

KEY TI SIGMA PREDICTION:
  Crystal BOK produces a BIMODAL epidemic curve — fast inner-ring BEC spread
  followed by a Mott-insulated outer-ring plateau.
  Graph BOK produces a standard logistic S-curve.
  The crystal's BEC long-range coupling causes earlier peak infections
  but the Mott insulation limits final R (herd immunity).

GILE-LCC COMPOSITE MATRIX:
  Each vertex carries a GILE-LCC composite score derived from ring index:
    Ring 0 (Origin):   G=1.0, I=1.0, L=1.0, E=1.0  — full coherence
    Ring 1 (C=0.437):  G=0.90, I=0.80, L=0.85, E=0.80
    Ring 2 (T=0.934):  G=0.85, I=0.75, L=0.80, E=0.75
    Ring 3 (1.000):    G=0.70, I=0.65, L=0.70, E=0.65
    Ring 4 (√2=1.414): G=0.55, I=0.55, L=0.60, E=0.55
    Ring 5 (φ=1.618):  G=0.45, I=0.48, L=0.50, E=0.45
    Ring 6 (e=2.718):  G=0.30, I=0.35, L=0.35, E=0.30
    Ring 7 (π=3.142):  G=0.15, I=0.20, L=0.18, E=0.15
"""

from __future__ import annotations

import numpy as np
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from enum import Enum

# ── TI Sigma constants ───────────────────────────────────────────────────────
ET   = np.sqrt(2.0) - 1.0
C_TI = 1.0 / ((1.0 + np.sqrt(5.0)) / 2.0 * np.sqrt(2.0))
T_TI = 1.0 - np.exp(-np.e)
PHI  = (1.0 + np.sqrt(5.0)) / 2.0

# GILE-LCC composite per ring (inner BOK loops = GILE structure)
RING_GILE = {
    0: {'G': 1.00, 'I': 1.00, 'L': 1.00, 'E': 1.00},   # Origin — BEC seed
    1: {'G': 0.90, 'I': 0.80, 'L': 0.85, 'E': 0.80},   # Ring C  — coherence
    2: {'G': 0.85, 'I': 0.75, 'L': 0.80, 'E': 0.75},   # Ring T  — BEC threshold
    3: {'G': 0.70, 'I': 0.65, 'L': 0.70, 'E': 0.65},   # Ring 1  — unity
    4: {'G': 0.55, 'I': 0.55, 'L': 0.60, 'E': 0.55},   # Ring √2 — Supersolid
    5: {'G': 0.45, 'I': 0.48, 'L': 0.50, 'E': 0.45},   # Ring φ  — FQH
    6: {'G': 0.30, 'I': 0.35, 'L': 0.35, 'E': 0.30},   # Ring e  — Mott
    7: {'G': 0.15, 'I': 0.20, 'L': 0.18, 'E': 0.15},   # Ring π  — Fragmented
}

# GILE canonical weights (URB #576)
GILE_W = {'G': ET, 'I': 0.25, 'L': 0.18, 'E': 0.15}

RING_NAMES = ["Origin", "C (coherence)", "T (BEC)", "1 (unity)",
              "√2 (Supersolid)", "φ (FQH)", "e (Mott)", "π (Fragmented)"]


def gile_composite(ring: int) -> float:
    g = RING_GILE.get(ring, RING_GILE[7])
    return (GILE_W['G'] * g['G'] + GILE_W['I'] * g['I']
          + GILE_W['L'] * g['L'] + GILE_W['E'] * g['E'])


# Crystal transmission rates by ring (phase-dependent β)
RING_BETA = {
    0: 1.00,   # Origin — full coherence seed
    1: 0.88,   # C ring  — near-BEC, high transmission
    2: 0.82,   # T ring  — BEC threshold, strong spread
    3: 0.68,   # Unity   — Supersolid, moderate
    4: 0.50,   # √2      — FQH boundary
    5: 0.35,   # φ       — weakening, partially insulating
    6: 0.18,   # e       — Mott insulating
    7: 0.08,   # π       — Fragmented, near-blocked
}

# Recovery rate = GILE-G weight (canonical from URB #576)
GAMMA = ET   # ≈ 0.4142


class SIRState(Enum):
    S = "Susceptible"
    I = "Infected"
    R = "Recovered"


STATE_COLORS = {
    SIRState.S: "#3399ff",   # blue
    SIRState.I: "#ff3333",   # red
    SIRState.R: "#44cc44",   # green
}

STATE_COLOR_IDX = {
    SIRState.S: 0,
    SIRState.I: 1,
    SIRState.R: 2,
}


# ── Snapshot ─────────────────────────────────────────────────────────────────

@dataclass
class StepSnapshot:
    step:        int
    states:      List[SIRState]    # per-vertex state
    S:           int
    I:           int
    R:           int
    new_infected: List[int]        # vertices that just became infected
    new_recovered: List[int]


# ── Crystal BOK Virus ─────────────────────────────────────────────────────────

class CrystalBOKVirus:
    """
    SIR epidemic on the TSC 57-vertex crystal lattice.

    Spread rules:
      1. Local: an infected vertex infects each susceptible neighbor with
         probability β = RING_BETA[source_ring] × RING_BETA[target_ring]^0.5
         (geometric mean: need both source energy AND target receptivity).
      2. BEC long-range (Rings 0–2 only): infected BEC vertices have a
         p_bec chance of infecting ANY non-adjacent susceptible vertex
         in Rings 0–3 (the coherent core). Represents quantum non-local coupling.
      3. Recovery: each infected vertex recovers with probability γ per step.
    """

    def __init__(
        self,
        adjacency: np.ndarray,      # 57×57 adjacency matrix
        rings:     List[int],        # ring index per vertex [0..7]
        positions: List[complex],    # complex positions for layout
        labels:    List[str],
        seed_vertex: int = 0,        # initial infection (Origin by default)
        beta_scale: float = 1.0,
        gamma: float = GAMMA,
        bec_long_range_p: float = 0.05,
        rng_seed: int = 42,
    ):
        self.adj     = np.array(adjacency, dtype=bool)
        self.rings   = rings
        self.pos     = positions
        self.labels  = labels
        self.n       = len(rings)
        self.beta_scale = beta_scale
        self.gamma   = gamma
        self.p_bec   = bec_long_range_p
        self.rng     = np.random.default_rng(rng_seed)

        # BEC-core vertices (Rings 0–2)
        self.bec_core = [i for i, r in enumerate(rings) if r <= 2]

        # Initialize SIR
        self.states = [SIRState.S] * self.n
        self.states[seed_vertex] = SIRState.I

        self.history: List[StepSnapshot] = []
        self._record(step=0, new_i=[seed_vertex], new_r=[])

    def _transmission_prob(self, src: int, tgt: int) -> float:
        """β for src→tgt edge: geometric mean of source & target ring β."""
        b_src = RING_BETA.get(self.rings[src], 0.05) * self.beta_scale
        b_tgt = RING_BETA.get(self.rings[tgt], 0.05)
        return float(np.sqrt(b_src * b_tgt))

    def step(self) -> StepSnapshot:
        new_infected  = []
        new_recovered = []
        next_states   = list(self.states)

        infected_vertices = [i for i, s in enumerate(self.states) if s == SIRState.I]

        for src in infected_vertices:
            # 1. Local spread along crystal edges
            neighbors = np.where(self.adj[src])[0]
            for tgt in neighbors:
                if self.states[tgt] == SIRState.S:
                    p = self._transmission_prob(src, tgt)
                    if self.rng.random() < p:
                        next_states[tgt] = SIRState.I
                        new_infected.append(tgt)

            # 2. BEC long-range coupling (only from BEC core vertices)
            if self.rings[src] <= 2 and self.p_bec > 0:
                # Can reach any susceptible vertex in Rings 0–3
                candidates = [
                    j for j in self.bec_core
                    if self.states[j] == SIRState.S and not self.adj[src, j]
                ]
                for tgt in candidates:
                    if self.rng.random() < self.p_bec * self.beta_scale:
                        next_states[tgt] = SIRState.I
                        new_infected.append(tgt)

            # 3. Recovery
            if self.rng.random() < self.gamma:
                next_states[src] = SIRState.R
                new_recovered.append(src)

        # Deduplicate (vertex may have been targeted by multiple sources)
        new_infected = list(set(new_infected))

        self.states = next_states
        step_n = len(self.history)
        self._record(step_n, new_infected, new_recovered)
        return self.history[-1]

    def _record(self, step: int, new_i: List[int], new_r: List[int]):
        counts = {s: self.states.count(s) for s in SIRState}
        self.history.append(StepSnapshot(
            step=step,
            states=list(self.states),
            S=counts[SIRState.S],
            I=counts[SIRState.I],
            R=counts[SIRState.R],
            new_infected=new_i,
            new_recovered=new_r,
        ))

    def run(self, max_steps: int = 40) -> List[StepSnapshot]:
        for _ in range(max_steps):
            snap = self.step()
            if snap.I == 0:
                break
        return self.history

    def is_finished(self) -> bool:
        return all(s != SIRState.I for s in self.states)


# ── Graph BOK Virus ───────────────────────────────────────────────────────────

class GraphBOKVirus:
    """
    SIR epidemic on an Erdős-Rényi random graph (57 nodes).

    Classical information-theoretic spreading:
      - Uniform β (no phase effects)
      - No long-range coupling
      - Standard SIR dynamics
    """

    def __init__(
        self,
        n: int = 57,
        edge_prob: float = 0.12,    # ER connection probability (≈ same density as crystal)
        rings: Optional[List[int]] = None,
        labels: Optional[List[str]] = None,
        seed_vertex: int = 0,
        beta: float = 0.45,
        gamma: float = GAMMA,
        rng_seed: int = 42,
    ):
        self.n      = n
        self.beta   = beta
        self.gamma  = gamma
        self.rings  = rings or [min(7, i // 8) for i in range(n)]
        self.labels = labels or [f"G{i}" for i in range(n)]
        self.rng    = np.random.default_rng(rng_seed)

        # Generate Erdős-Rényi graph
        self.adj = self._make_er_graph(n, edge_prob, rng_seed)

        # Layout: circular with some jitter
        angles = np.linspace(0, 2 * np.pi, n, endpoint=False)
        self.pos = [complex(np.cos(a), np.sin(a)) * (1.0 + self.rng.uniform(-0.2, 0.2))
                    for a in angles]

        # Initialize SIR
        self.states = [SIRState.S] * self.n
        self.states[seed_vertex] = SIRState.I
        self.history: List[StepSnapshot] = []
        self._record(step=0, new_i=[seed_vertex], new_r=[])

    @staticmethod
    def _make_er_graph(n: int, p: float, seed: int) -> np.ndarray:
        rng = np.random.default_rng(seed)
        adj = np.zeros((n, n), dtype=bool)
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    adj[i, j] = adj[j, i] = True
        # Ensure connectivity: connect any isolated vertex to a random neighbor
        for i in range(n):
            if not np.any(adj[i]):
                j = rng.integers(0, n - 1)
                j = j if j != i else (j + 1) % n
                adj[i, j] = adj[j, i] = True
        return adj

    def step(self) -> StepSnapshot:
        new_infected  = []
        new_recovered = []
        next_states   = list(self.states)

        infected_vertices = [i for i, s in enumerate(self.states) if s == SIRState.I]

        for src in infected_vertices:
            neighbors = np.where(self.adj[src])[0]
            for tgt in neighbors:
                if self.states[tgt] == SIRState.S:
                    if self.rng.random() < self.beta:
                        next_states[tgt] = SIRState.I
                        new_infected.append(tgt)
            if self.rng.random() < self.gamma:
                next_states[src] = SIRState.R
                new_recovered.append(src)

        new_infected = list(set(new_infected))
        self.states = next_states
        step_n = len(self.history)
        self._record(step_n, new_infected, new_recovered)
        return self.history[-1]

    def _record(self, step: int, new_i: List[int], new_r: List[int]):
        counts = {s: self.states.count(s) for s in SIRState}
        self.history.append(StepSnapshot(
            step=step,
            states=list(self.states),
            S=counts[SIRState.S],
            I=counts[SIRState.I],
            R=counts[SIRState.R],
            new_infected=new_i,
            new_recovered=new_r,
        ))

    def run(self, max_steps: int = 40) -> List[StepSnapshot]:
        for _ in range(max_steps):
            snap = self.step()
            if snap.I == 0:
                break
        return self.history

    def is_finished(self) -> bool:
        return all(s != SIRState.I for s in self.states)


# ── Comparative Metrics ───────────────────────────────────────────────────────

def epidemic_metrics(history: List[StepSnapshot], n: int) -> dict:
    """Compute key epidemic curve statistics from simulation history."""
    if not history:
        return {}

    I_curve = [s.I for s in history]
    R_curve = [s.R for s in history]

    peak_I      = max(I_curve)
    peak_step   = I_curve.index(peak_I)
    final_R     = R_curve[-1]
    attack_rate = final_R / n    # fraction of population that was ever infected
    duration    = len(history) - 1

    # R0 estimate: total infections / initial infected × 1/γ
    total_infected = sum(len(s.new_infected) for s in history)
    r0_est = total_infected / (1 + 1e-9) * (1.0 / GAMMA)

    # Bimodality: check if I(t) has two local maxima (crystal signature)
    import numpy as np
    i_arr = np.array(I_curve, dtype=float)
    if len(i_arr) >= 5:
        peaks = []
        for k in range(1, len(i_arr) - 1):
            if i_arr[k] > i_arr[k-1] and i_arr[k] > i_arr[k+1]:
                peaks.append(k)
        bimodal = len(peaks) >= 2
    else:
        bimodal = False

    return {
        'peak_I':      peak_I,
        'peak_step':   peak_step,
        'final_R':     final_R,
        'attack_rate': round(attack_rate, 3),
        'duration':    duration,
        'bimodal':     bimodal,
        'n_peaks':     len(peaks) if len(i_arr) >= 5 else 0,
    }


def build_simulators(
    adjacency: np.ndarray,
    rings:     List[int],
    positions: List[complex],
    labels:    List[str],
    seed_vertex: int = 0,
    beta_scale:  float = 1.0,
    gamma:       float = GAMMA,
    bec_p:       float = 0.05,
    rng_seed:    int   = 42,
) -> Tuple[CrystalBOKVirus, GraphBOKVirus]:
    """Construct both simulators with matching parameters."""
    crystal = CrystalBOKVirus(
        adjacency=adjacency, rings=rings, positions=positions, labels=labels,
        seed_vertex=seed_vertex, beta_scale=beta_scale, gamma=gamma,
        bec_long_range_p=bec_p, rng_seed=rng_seed,
    )
    # Graph BOK: uniform β = weighted average of crystal β values
    mean_beta = float(np.mean([RING_BETA[r] * beta_scale for r in rings]))
    graph = GraphBOKVirus(
        n=len(rings), rings=rings, labels=labels,
        seed_vertex=seed_vertex, beta=mean_beta, gamma=gamma, rng_seed=rng_seed,
    )
    return crystal, graph
