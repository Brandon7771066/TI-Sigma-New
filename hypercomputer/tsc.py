"""
TI Sigma Crystal (TSC) — 57-vertex quasicrystalline state space.

Structure:
  Origin (vertex 0): the zero / vacuum state
  Ring r ∈ {1..7}: radius = PRIMARY_CONSTANTS[r-1]
  Layer l ∈ {0..7}: angle = l · π/4 (golden-angle offset per ring)

Each vertex (r, l) represents the TSC element:
  value = radius_r · exp(i · θ_l)
where θ_l = l·π/4 + (r-1)·π/PHI (golden-angle offset breaks degeneracy).
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Tuple
from hypercomputer.constants import (
    PHI, C_TI, T_TI, ET, RING_RADII, RING_NAMES, N_RINGS, N_LAYERS, N_VERTICES
)


@dataclass
class TSCVertex:
    index: int
    ring: int        # 0 = origin, 1–7 = rings
    layer: int       # 0–7
    radius: float    # |value| = primary constant for ring
    angle: float     # arg(value) in [0, 2π)
    label: str       # human-readable, e.g. "φ·i³"

    @property
    def position(self) -> complex:
        return self.radius * np.exp(1j * self.angle)

    @property
    def name_short(self) -> str:
        if self.ring == 0:
            return "O"
        return f"{RING_NAMES[self.ring-1]}·i^{self.layer}"


def build_tsc_vertices() -> List[TSCVertex]:
    verts: List[TSCVertex] = []

    # Origin
    verts.append(TSCVertex(
        index=0, ring=0, layer=0,
        radius=0.0, angle=0.0, label="0"
    ))

    # 7 rings × 8 layers
    for r in range(1, N_RINGS + 1):
        radius = RING_RADII[r - 1]
        for l in range(N_LAYERS):
            # Golden-angle offset prevents alignment across rings
            angle = (l * np.pi / 4) + (r - 1) * np.pi / PHI
            angle = angle % (2 * np.pi)
            idx = (r - 1) * N_LAYERS + l + 1
            layer_power = ['1','i','i²','i³','i⁴','i⁵','i⁶','i⁷'][l]
            label = f"{RING_NAMES[r-1]}·{layer_power}"
            verts.append(TSCVertex(
                index=idx, ring=r, layer=l,
                radius=radius, angle=angle, label=label
            ))

    return verts


def adjacency_matrix(vertices: List[TSCVertex]) -> np.ndarray:
    """
    Build adjacency matrix for the TSC graph.
    Two vertices are adjacent if:
      (a) same ring, adjacent layers (mod 8), OR
      (b) adjacent rings, same layer.
    Origin is connected to all ring-1 vertices.
    """
    n = len(vertices)
    A = np.zeros((n, n), dtype=float)

    for i, vi in enumerate(vertices):
        for j, vj in enumerate(vertices):
            if i >= j:
                continue
            # Origin ↔ ring-1 vertices
            if (vi.ring == 0 and vj.ring == 1) or (vi.ring == 1 and vj.ring == 0):
                A[i, j] = A[j, i] = 1.0
            # Same ring, adjacent layers
            elif vi.ring == vj.ring and vi.ring > 0:
                dl = abs(vi.layer - vj.layer)
                if dl == 1 or dl == N_LAYERS - 1:
                    A[i, j] = A[j, i] = 1.0
            # Adjacent rings, same layer
            elif vi.layer == vj.layer and abs(vi.ring - vj.ring) == 1:
                A[i, j] = A[j, i] = 1.0

    return A


VERTICES: List[TSCVertex] = build_tsc_vertices()
ADJACENCY: np.ndarray = adjacency_matrix(VERTICES)
