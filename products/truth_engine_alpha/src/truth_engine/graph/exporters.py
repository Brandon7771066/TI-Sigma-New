from __future__ import annotations

import csv
import json
from io import StringIO
from pathlib import Path
from typing import Any

from .models import ClaimGraph, CrystalCell


def _rows_csv(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return ''
    buffer = StringIO()
    fieldnames = sorted({key for row in rows for key in row.keys()})
    writer = csv.DictWriter(buffer, fieldnames=fieldnames)
    writer.writeheader()
    for row in rows:
        writer.writerow(row)
    return buffer.getvalue()


def export_claim_graph(graph: ClaimGraph, output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    payload = graph.to_dict()
    (output_dir / 'claim_graph.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
    (output_dir / 'claim_graph.graphml').write_text(_graphml(graph), encoding='utf-8')


def export_graph_errors_csv(errors: list[dict[str, Any]], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / 'graph_errors.csv').write_text(_rows_csv(errors), encoding='utf-8')


def export_crystal_outputs(cells: list[CrystalCell], diagnostics: dict[str, Any], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    matrix_rows = [{'claim_id': cell.claim_id, **cell.values} for cell in cells]
    (output_dir / 'crystal_matrix.csv').write_text(_rows_csv(matrix_rows), encoding='utf-8')
    (output_dir / 'crystal_diagnostics.json').write_text(json.dumps(diagnostics, indent=2), encoding='utf-8')
    (output_dir / 'crystal_explanation.md').write_text(_crystal_explanation(diagnostics), encoding='utf-8')


def _graphml(graph: ClaimGraph) -> str:
    nodes = '\n'.join(f'<node id="{node.node_id}"><data key="type">{node.node_type}</data><data key="label">{node.label}</data></node>' for node in graph.nodes)
    edges = '\n'.join(f'<edge id="{edge.edge_id}" source="{edge.source}" target="{edge.target}"><data key="type">{edge.edge_type}</data><data key="confidence">{edge.confidence}</data></edge>' for edge in graph.edges)
    return '\n'.join([
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<graphml xmlns="http://graphml.graphdrawing.org/xmlns">',
        '<graph id="TruthEngineClaimGraph" edgedefault="directed">',
        nodes,
        edges,
        '</graph>',
        '</graphml>',
    ])


def _crystal_explanation(diagnostics: dict[str, Any]) -> str:
    lines = ['# Crystal v0.1 Explanation', '']
    lines.append('Crystal is a multilayer error-analysis structure for claim graph diagnostics, not a physical or octonionic object.')
    lines.append('')
    for key, value in diagnostics.items():
        lines.append(f'- {key}: {value}')
    return '\n'.join(lines)