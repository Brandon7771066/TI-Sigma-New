from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Any, Literal

GraphNodeType = Literal[
    'Claim',
    'Source',
    'Citation',
    'Evidence',
    'Assumption',
    'Definition',
    'Population',
    'Method',
    'Measurement',
    'Mechanism',
    'Action',
]

GraphEdgeType = Literal[
    'SUPPORTS',
    'CONTRADICTS',
    'DEPENDS_ON',
    'QUALIFIES',
    'GENERALIZES',
    'SPECIALIZES',
    'EXPLAINS',
    'CAUSES',
    'CITES',
    'SAME_ONLY_IF',
    'DIFFERS_BY_SCOPE',
    'DIFFERS_BY_POPULATION',
    'DIFFERS_BY_TIME',
    'DIFFERS_BY_METHOD',
    'DIFFERS_BY_MEASUREMENT',
    'DIFFERS_BY_DEFINITION',
    'DIFFERS_BY_PARAMETER',
]

GRAPH_NODE_TYPES = {
    'Claim',
    'Source',
    'Citation',
    'Evidence',
    'Assumption',
    'Definition',
    'Population',
    'Method',
    'Measurement',
    'Mechanism',
    'Action',
}

GRAPH_EDGE_TYPES = {
    'SUPPORTS',
    'CONTRADICTS',
    'DEPENDS_ON',
    'QUALIFIES',
    'GENERALIZES',
    'SPECIALIZES',
    'EXPLAINS',
    'CAUSES',
    'CITES',
    'SAME_ONLY_IF',
    'DIFFERS_BY_SCOPE',
    'DIFFERS_BY_POPULATION',
    'DIFFERS_BY_TIME',
    'DIFFERS_BY_METHOD',
    'DIFFERS_BY_MEASUREMENT',
    'DIFFERS_BY_DEFINITION',
    'DIFFERS_BY_PARAMETER',
}


@dataclass(slots=True)
class GraphNode:
    node_id: str
    node_type: GraphNodeType
    label: str
    attributes: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class GraphEdge:
    edge_id: str
    source: str
    target: str
    edge_type: GraphEdgeType
    evidence: str = ''
    confidence: float = 0.0
    severity: str = 'low'
    attributes: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class ClaimGraph:
    nodes: list[GraphNode]
    edges: list[GraphEdge]
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(slots=True)
class CrystalCell:
    claim_id: str
    values: dict[str, float]
    notes: dict[str, Any] = field(default_factory=dict)