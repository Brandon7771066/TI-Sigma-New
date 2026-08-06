from __future__ import annotations

from collections import defaultdict
from typing import Any

from ..models import Claim, Contradiction, ScaffoldingCandidate, Source
from .models import ClaimGraph, CrystalCell, GraphEdge, GraphNode


def _node(node_id: str, node_type: str, label: str, **attributes: Any) -> GraphNode:
    return GraphNode(node_id=node_id, node_type=node_type, label=label, attributes=dict(attributes))


def _edge(edge_id: str, source: str, target: str, edge_type: str, evidence: str, confidence: float, severity: str, **attributes: Any) -> GraphEdge:
    return GraphEdge(edge_id=edge_id, source=source, target=target, edge_type=edge_type, evidence=evidence, confidence=confidence, severity=severity, attributes=dict(attributes))


def build_claim_graph(claims: list[Claim], sources: list[Source], contradictions: list[Contradiction], scaffolds: list[ScaffoldingCandidate], citation_audit: list[dict[str, Any]] | None = None) -> ClaimGraph:
    nodes: list[GraphNode] = []
    edges: list[GraphEdge] = []
    citation_audit = citation_audit or []
    audit_lookup = {row.get('claim_id'): row for row in citation_audit}
    seen_nodes: set[str] = set()

    def add_node(node: GraphNode) -> None:
        if node.node_id in seen_nodes:
            return
        seen_nodes.add(node.node_id)
        nodes.append(node)

    for claim in claims:
        add_node(_node(claim.claim_id, 'Claim', claim.normalized_claim, claim_type=claim.claim_type, source_id=claim.source_id))
        if claim.source_id:
            edges.append(_edge(f'edge_cites_{claim.claim_id}', claim.claim_id, claim.source_id, 'CITES', 'claim cites its source', 0.7, 'medium'))
        if claim.population:
            pop_id = f'population_{claim.population}'
            add_node(_node(pop_id, 'Population', claim.population, claim_id=claim.claim_id))
            edges.append(_edge(f'edge_pop_{claim.claim_id}', claim.claim_id, pop_id, 'DIFFERS_BY_POPULATION', 'population annotation', 0.4, 'low'))
        if claim.intervention:
            method_id = f'method_{claim.intervention}'
            add_node(_node(method_id, 'Method', claim.intervention, claim_id=claim.claim_id))
            edges.append(_edge(f'edge_method_{claim.claim_id}', claim.claim_id, method_id, 'DEPENDS_ON', 'method annotation', 0.4, 'low'))
        if claim.outcome:
            evidence_id = f'evidence_{claim.claim_id}'
            add_node(_node(evidence_id, 'Evidence', claim.outcome, claim_id=claim.claim_id))
            edges.append(_edge(f'edge_evidence_{claim.claim_id}', evidence_id, claim.claim_id, 'SUPPORTS', 'evidence annotation', 0.5, 'medium'))
        audit_row = audit_lookup.get(claim.claim_id)
        if audit_row:
            citation_id = f'citation_{claim.claim_id}'
            add_node(_node(citation_id, 'Citation', claim.citations[0] if claim.citations else claim.claim_id, claim_id=claim.claim_id, status=audit_row.get('status')))
            edges.append(_edge(f'edge_audit_{claim.claim_id}', citation_id, claim.claim_id, 'CITES', str(audit_row.get('reason', 'citation audit')), 0.6, 'medium'))
            if audit_row.get('status') in {'SOURCE_SUPPORTS_CLAIM', 'SOURCE_PARTIALLY_SUPPORTS_CLAIM'}:
                edges.append(_edge(f'edge_support_{claim.claim_id}', claim.source_id, claim.claim_id, 'SUPPORTS', str(audit_row.get('reason', 'citation support')), 0.8 if audit_row.get('status') == 'SOURCE_SUPPORTS_CLAIM' else 0.6, 'high' if audit_row.get('status') == 'SOURCE_SUPPORTS_CLAIM' else 'medium'))

    source_lookup = {source.source_id: source for source in sources}
    for source in sources:
        add_node(_node(source.source_id, 'Source', source.title, source_type=source.source_type, evidence_level=source.evidence_level))

    for contradiction in contradictions:
        claim_a = contradiction.claim_ids[0]
        claim_b = contradiction.claim_ids[1] if len(contradiction.claim_ids) > 1 else claim_a
        edges.append(_edge(contradiction.contradiction_id, claim_a, claim_b, 'CONTRADICTS', contradiction.explanation, 0.9, 'high', contradiction_type=contradiction.contradiction_type))
        mismatch_map = {
            'DIRECT_LOGICAL_CONFLICT': 'DIFFERS_BY_DEFINITION',
            'SCOPE_DIFFERENCE': 'DIFFERS_BY_SCOPE',
            'POPULATION_DIFFERENCE': 'DIFFERS_BY_POPULATION',
            'TEMPORAL_DIFFERENCE': 'DIFFERS_BY_TIME',
            'DEFINITION_DIFFERENCE': 'DIFFERS_BY_DEFINITION',
            'MEASUREMENT_DIFFERENCE': 'DIFFERS_BY_MEASUREMENT',
            'METHOD_DIFFERENCE': 'DIFFERS_BY_METHOD',
            'DOSE_OR_PARAMETER_DIFFERENCE': 'DIFFERS_BY_PARAMETER',
        }
        mismatch_type = mismatch_map.get(contradiction.contradiction_type)
        if mismatch_type:
            edges.append(_edge(f'{contradiction.contradiction_id}_{mismatch_type.lower()}', claim_a, claim_b, mismatch_type, f'{contradiction.contradiction_type} mismatch', 0.7, 'medium'))

    for scaffold in scaffolds:
        add_node(_node(scaffold.candidate_id, 'Action', scaffold.rationale, route=scaffold.route, contradiction_id=scaffold.contradiction_id))
        edges.append(_edge(f'edge_scaffold_{scaffold.candidate_id}', scaffold.candidate_id, scaffold.contradiction_id, 'QUALIFIES', scaffold.rationale, 0.6, 'medium'))

    if sources:
        source_ids = [source.source_id for source in sources]
        center = source_ids[0]
        for other_source_id in source_ids[1:]:
            edges.append(_edge(f'edge_source_{center}_{other_source_id}', center, other_source_id, 'SAME_ONLY_IF', 'source concentration check', 0.3, 'low'))

    metadata = {
        'claim_count': len(claims),
        'source_count': len(sources),
        'contradiction_count': len(contradictions),
        'citation_statuses': sorted({str(row.get('status')) for row in citation_audit if row.get('status')}),
    }
    return ClaimGraph(nodes=nodes, edges=edges, metadata=metadata)


def build_crystal_matrix(claims: list[Claim], sources: list[Source], contradictions: list[Contradiction], scaffolds: list[ScaffoldingCandidate], citation_audit: list[dict[str, Any]], truth_engine_score: dict[str, float]) -> list[CrystalCell]:
    source_count = max(len(sources), 1)
    contradiction_count = max(len(contradictions), 1)
    cited_claims = sum(1 for claim in claims if claim.citations)
    evidence_coverage = cited_claims / max(len(claims), 1)
    conflicts_by_claim = defaultdict(int)
    for contradiction in contradictions:
        for claim_id in contradiction.claim_ids:
            conflicts_by_claim[claim_id] += 1

    cells: list[CrystalCell] = []
    for claim in claims:
        claim_id = claim.claim_id
        isolated_claim_score = 1.0 - min(conflicts_by_claim[claim_id] / contradiction_count, 1.0)
        support_score = 1.0 if claim.citations else 0.25
        conflict_density = min(conflicts_by_claim[claim_id] / contradiction_count, 1.0)
        assumption_sensitivity = 0.8 if not claim.population or not claim.intervention else 0.35
        resolution_potential = 0.9 if claim.citations else 0.55
        source_dependency_concentration = 1.0 / source_count
        critical_unknown_centrality = min(1.0, len([row for row in citation_audit if row.get('claim_id') == claim_id and row.get('status') in {'NO_CITATION_PROVIDED', 'SOURCE_NOT_FOUND', 'NOT_VERIFIED_OFFLINE'}]) + 0.25)
        structural_instability = min(1.0, (conflict_density + assumption_sensitivity + critical_unknown_centrality) / 3)
        cells.append(CrystalCell(
            claim_id=claim_id,
            values={
                'claim structure': 1.0,
                'source structure': source_dependency_concentration,
                'evidence quality': support_score,
                'contradictions': conflict_density,
                'scaffolding': 1.0 if any(scaffold.contradiction_id.startswith('contra') for scaffold in scaffolds) else 0.5,
                'uncertainty': 1.0 - evidence_coverage,
                'criticality': critical_unknown_centrality,
                'resolution actions': resolution_potential,
                'isolated_claim_score': isolated_claim_score,
                'evidence_asymmetry': abs(support_score - evidence_coverage),
                'conflict_density': conflict_density,
                'assumption_sensitivity': assumption_sensitivity,
                'resolution_potential': resolution_potential,
                'source_dependency_concentration': source_dependency_concentration,
                'critical_unknown_centrality': critical_unknown_centrality,
                'structural_instability': structural_instability,
            },
            notes={'citation_count': len(claim.citations), 'truth_engine_score': truth_engine_score},
        ))
    return cells