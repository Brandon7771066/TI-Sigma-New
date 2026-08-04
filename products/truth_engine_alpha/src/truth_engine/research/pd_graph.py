from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Literal

PropagationMode = Literal[
    "additive",
    "log_odds_additive",
    "bounded_logistic",
    "max_min",
    "message_passing",
    "energy_potential",
]


@dataclass(frozen=True, slots=True)
class PDEdge:
    from_node: str
    to_node: str
    edge_type: str
    weight: float


@dataclass(frozen=True, slots=True)
class PDGraphSnapshot:
    node_pd: dict[str, float]
    edge_pd: dict[str, float]
    path_pd: dict[str, float]
    support_gradient: float
    conflict_gradient: float
    threshold_crossings: int
    boundary_instability: float
    mode: PropagationMode


def _bounded(value: float, lo: float = -3.0, hi: float = 2.0) -> float:
    return max(lo, min(hi, value))


def propagate_graph_pd(
    initial_node_pd: dict[str, float],
    edges: list[PDEdge],
    mode: PropagationMode = "additive",
    steps: int = 2,
) -> PDGraphSnapshot:
    node_pd = dict(initial_node_pd)
    edge_pd: dict[str, float] = {}

    for _ in range(max(steps, 1)):
        for idx, edge in enumerate(edges):
            key = f"e{idx+1}:{edge.from_node}->{edge.to_node}:{edge.edge_type}"
            src = node_pd.get(edge.from_node, 0.0)
            dst = node_pd.get(edge.to_node, 0.0)
            direction = 1.0 if edge.edge_type.upper() in {"SUPPORTS", "QUALIFIES", "CITES"} else -1.0
            delta = direction * edge.weight

            if mode == "additive":
                proposed = dst + delta + (0.1 * src)
            elif mode == "log_odds_additive":
                proposed = dst + math.log1p(abs(delta)) * (1 if delta >= 0 else -1)
            elif mode == "bounded_logistic":
                proposed = 2.0 * (1.0 / (1.0 + math.exp(-(dst + delta))) - 0.5)
            elif mode == "max_min":
                proposed = max(dst, src + delta) if delta >= 0 else min(dst, src + delta)
            elif mode == "message_passing":
                proposed = dst + 0.5 * delta + 0.25 * src
            elif mode == "energy_potential":
                proposed = dst + delta - 0.1 * (dst - src)
            else:
                raise ValueError(f"Unsupported mode: {mode}")

            node_pd[edge.to_node] = _bounded(proposed)
            edge_pd[key] = delta

    support_gradient = sum(v for v in edge_pd.values() if v > 0)
    conflict_gradient = abs(sum(v for v in edge_pd.values() if v < 0))
    threshold_crossings = sum(1 for v in node_pd.values() if v >= 1.0 or v <= -1.0)
    boundary_instability = min(1.0, sum(abs(v) for v in node_pd.values()) / max(len(node_pd), 1) / 3.0)

    path_pd = {f"{edge.from_node}->{edge.to_node}": node_pd.get(edge.to_node, 0.0) for edge in edges}
    return PDGraphSnapshot(
        node_pd=node_pd,
        edge_pd=edge_pd,
        path_pd=path_pd,
        support_gradient=support_gradient,
        conflict_gradient=conflict_gradient,
        threshold_crossings=threshold_crossings,
        boundary_instability=boundary_instability,
        mode=mode,
    )
