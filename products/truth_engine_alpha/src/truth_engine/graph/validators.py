from __future__ import annotations

from collections import defaultdict
from typing import Any

from .models import ClaimGraph


def _make_detector(detector: str, affected_nodes: list[str], affected_edges: list[str], evidence: str, severity: str, confidence: float, explanation: str, recommended_review: str) -> dict[str, Any]:
    return {
        'detector': detector,
        'affected_nodes': affected_nodes,
        'affected_edges': affected_edges,
        'evidence': evidence,
        'severity': severity,
        'confidence': confidence,
        'explanation': explanation,
        'recommended_review': recommended_review,
    }


def validate_claim_graph(graph: ClaimGraph) -> list[dict[str, Any]]:
    node_ids = {node.node_id for node in graph.nodes}
    errors: list[dict[str, Any]] = []
    for edge in graph.edges:
        if edge.source not in node_ids or edge.target not in node_ids:
            errors.append(_make_detector('missing_dependency', [edge.source, edge.target], [edge.edge_id], 'edge references missing nodes', 'high', 0.95, 'graph edge references a missing node', 'review source-target linkage'))
    return errors


def detect_graph_errors(graph: ClaimGraph) -> list[dict[str, Any]]:
    errors: list[dict[str, Any]] = []
    node_types = {node.node_id: node.node_type for node in graph.nodes}
    outgoing: dict[str, list[str]] = defaultdict(list)
    incoming: dict[str, list[str]] = defaultdict(list)
    edge_lookup = {edge.edge_id: edge for edge in graph.edges}
    support_graph: dict[str, set[str]] = defaultdict(set)

    for edge in graph.edges:
        outgoing[edge.source].append(edge.edge_id)
        incoming[edge.target].append(edge.edge_id)
        if edge.edge_type == 'SUPPORTS':
            support_graph[edge.source].add(edge.target)

    for node in graph.nodes:
        if node.node_type == 'Claim' and not incoming[node.node_id]:
            errors.append(_make_detector('unsupported_claim', [node.node_id], [], 'claim has no support edges', 'medium', 0.82, 'claim lacks explicit support', 'review support chain'))
        if node.node_type == 'Claim' and not outgoing[node.node_id] and not incoming[node.node_id]:
            errors.append(_make_detector('orphan_conclusion', [node.node_id], [], 'claim is isolated', 'high', 0.9, 'claim is disconnected from the graph', 'connect to evidence or source'))
        if node.node_type == 'Claim' and any(edge_lookup[edge_id].edge_type == 'CITES' for edge_id in outgoing[node.node_id]) and not any(edge_lookup[edge_id].edge_type == 'SUPPORTS' for edge_id in incoming[node.node_id]):
            errors.append(_make_detector('citation_claim_disconnect', [node.node_id], outgoing[node.node_id], 'claim cites sources but lacks support linkage', 'medium', 0.78, 'citation exists without support linkage', 'review whether the citation actually supports the claim'))

    for node_id, edges in outgoing.items():
        support_edges = [edge_lookup[edge_id] for edge_id in edges if edge_lookup[edge_id].edge_type == 'SUPPORTS']
        if len(support_edges) > 1:
            errors.append(_make_detector('source_concentration', [node_id], [edge.edge_id for edge in support_edges], 'multiple support links from a single node', 'low', 0.6, 'possible over-concentration of support', 'balance support across sources'))

    contradiction_edges = [edge for edge in graph.edges if edge.edge_type == 'CONTRADICTS']
    if contradiction_edges:
        claim_edges = [(edge.source, edge.target) for edge in contradiction_edges]
        for src, dst in claim_edges:
            if (dst, src) in claim_edges:
                errors.append(_make_detector('contradiction_cycle', [src, dst], [edge.edge_id for edge in contradiction_edges], 'mutual contradiction edges', 'high', 0.9, 'contradictions form a cycle', 'break cycle with scaffolding'))

    for edge in graph.edges:
        if edge.edge_type == 'DIFFERS_BY_SCOPE':
            errors.append(_make_detector('scope_mismatch', [edge.source, edge.target], [edge.edge_id], edge.evidence, 'medium', 0.8, 'scope mismatch annotated', 'review scope statements'))
        if edge.edge_type == 'DIFFERS_BY_POPULATION':
            errors.append(_make_detector('population_mismatch', [edge.source, edge.target], [edge.edge_id], edge.evidence, 'medium', 0.8, 'population mismatch annotated', 'review population framing'))
        if edge.edge_type == 'DIFFERS_BY_TIME':
            errors.append(_make_detector('temporal_mismatch', [edge.source, edge.target], [edge.edge_id], edge.evidence, 'medium', 0.8, 'temporal mismatch annotated', 'review time frame'))
        if edge.edge_type == 'DIFFERS_BY_DEFINITION':
            errors.append(_make_detector('definition_mismatch', [edge.source, edge.target], [edge.edge_id], edge.evidence, 'medium', 0.8, 'definition mismatch annotated', 'review definitions'))

    claim_support_map = defaultdict(int)
    for edge in graph.edges:
        if edge.edge_type == 'SUPPORTS':
            claim_support_map[edge.target] += 1
    for node in graph.nodes:
        if node.node_type == 'Claim' and claim_support_map[node.node_id] == 0:
            errors.append(_make_detector('weak_central_claim', [node.node_id], [], 'no direct support edges', 'medium', 0.7, 'central claim has weak support', 'add supporting evidence'))

    high_quality_support = [edge for edge in graph.edges if edge.edge_type == 'SUPPORTS' and edge.confidence >= 0.75]
    if len(high_quality_support) >= 2:
        errors.append(_make_detector('conflicting_high_quality_sources', [edge.target for edge in high_quality_support], [edge.edge_id for edge in high_quality_support], 'multiple high-confidence support paths', 'low', 0.6, 'high-quality support sources disagree or concentrate', 'compare source quality'))

    for source, targets in support_graph.items():
        stack = [(source, [source])]
        visited: set[str] = set()
        while stack:
            current, path = stack.pop()
            if current in visited:
                continue
            visited.add(current)
            for target in support_graph.get(current, set()):
                if target == source:
                    errors.append(_make_detector('circular_support', [source], [], 'support cycle detected', 'high', 0.91, 'support relations cycle back to the origin', 'break the cycle and inspect source hierarchy'))
                else:
                    stack.append((target, [*path, target]))

    return errors