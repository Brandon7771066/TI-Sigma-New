from __future__ import annotations

from typing import Any

from .models import ClaimGraph, CrystalCell


def compute_crystal_diagnostics(cells: list[CrystalCell], graph: ClaimGraph) -> dict[str, Any]:
    cell_count = max(len(cells), 1)
    isolated_claim_score = sum(cell.values.get('isolated_claim_score', 0.0) for cell in cells) / cell_count
    evidence_asymmetry = sum(cell.values.get('evidence_asymmetry', 0.0) for cell in cells) / cell_count
    conflict_density = sum(cell.values.get('conflict_density', 0.0) for cell in cells) / cell_count
    assumption_sensitivity = sum(cell.values.get('assumption_sensitivity', 0.0) for cell in cells) / cell_count
    resolution_potential = sum(cell.values.get('resolution_potential', 0.0) for cell in cells) / cell_count
    source_dependency_concentration = sum(cell.values.get('source_dependency_concentration', 0.0) for cell in cells) / cell_count
    critical_unknown_centrality = sum(cell.values.get('critical_unknown_centrality', 0.0) for cell in cells) / cell_count
    structural_instability = sum(cell.values.get('structural_instability', 0.0) for cell in cells) / cell_count

    return {
        'isolated_claim_score': round(isolated_claim_score, 3),
        'evidence_asymmetry': round(evidence_asymmetry, 3),
        'conflict_density': round(conflict_density, 3),
        'assumption_sensitivity': round(assumption_sensitivity, 3),
        'resolution_potential': round(resolution_potential, 3),
        'source_dependency_concentration': round(source_dependency_concentration, 3),
        'critical_unknown_centrality': round(critical_unknown_centrality, 3),
        'structural_instability': round(structural_instability, 3),
        'claim_count': len(cells),
        'graph_node_count': len(graph.nodes),
        'graph_edge_count': len(graph.edges),
    }