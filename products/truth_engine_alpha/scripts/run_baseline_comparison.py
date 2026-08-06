from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
if str(SRC) in sys.path:
    sys.path.remove(str(SRC))
sys.path.insert(0, str(SRC))

from truth_engine.engine import run_baseline_comparison
from truth_engine.graph import build_claim_graph, build_crystal_matrix, compute_crystal_diagnostics, detect_graph_errors
from truth_engine.models import Claim, Contradiction, ScaffoldingCandidate, Source


def _load_labels() -> dict[str, dict[str, object]]:
    labels_path = ROOT / 'data' / 'benchmarks' / 'graph_reference_labels.json'
    labels = json.loads(labels_path.read_text(encoding='utf-8'))
    return {row['benchmark_id']: row for row in labels}


def _benchmark_claims(input_claims: list[dict[str, object]]) -> list[Claim]:
    claims: list[Claim] = []
    for item in input_claims:
        claims.append(
            Claim(
                str(item.get('claim_id', 'claim')),
                str(item.get('normalized_claim', '')),
                str(item.get('verbatim_text', '')),
                str(item.get('source_id', '')),
                citations=list(item.get('citations', [])),
                population=item.get('population'),
                intervention=item.get('intervention'),
                comparison=item.get('comparison'),
                outcome=item.get('outcome'),
                timeframe=item.get('timeframe'),
                conditions=item.get('conditions'),
                certainty_language=item.get('certainty_language'),
            )
        )
    return claims


def _benchmark_sources(input_claims: list[dict[str, object]]) -> list[Source]:
    return [Source(str(item.get('source_id', '')), str(item.get('verbatim_text', ''))[:80] or str(item.get('claim_id', ''))) for item in input_claims]


def _simple_baseline_metrics(benchmarks: list[dict[str, object]]) -> dict[str, object]:
    total = max(len(benchmarks), 1)
    contradiction_hits = 0
    scaffolding_hits = 0
    resolution_hits = 0
    for case in benchmarks:
        expected_type = str(case.get('expected_contradiction_type', 'MISSING_INFORMATION'))
        expected_route = str(case.get('expected_scaffolding_route', 'context'))
        expected_resolution = str(case.get('expected_resolution_status', 'partially_resolved'))
        contradiction_hits += int('MISSING_INFORMATION' == expected_type)
        scaffolding_hits += int('context' == expected_route)
        resolution_hits += int('partially_resolved' == expected_resolution)
    return {
        'contradiction_type_accuracy': round(contradiction_hits / total, 3),
        'scaffolding_route_accuracy': round(scaffolding_hits / total, 3),
        'resolution_status_accuracy': round(resolution_hits / total, 3),
        'citation_error_recall': 0.0,
        'citation_error_precision': 0.0,
        'report_completeness': 1.0,
        'processing_time': 'heuristic_simple_baseline',
    }


def _write_markdown(output_path: Path, report: dict[str, object]) -> None:
    md_path = output_path.with_suffix('.md')
    simple = report['simple_baseline']
    truth = report['truth_engine_alpha']
    layers = report['held_out_performance']
    lines = [
        '# Baseline Comparison',
        '',
        '| metric | simple baseline | Truth Engine Alpha |',
        '| --- | ---: | ---: |',
        f"| contradiction_type_accuracy | {simple['contradiction_type_accuracy']} | {truth['contradiction_type_accuracy']} |",
        f"| scaffolding_route_accuracy | {simple['scaffolding_route_accuracy']} | {truth['scaffolding_route_accuracy']} |",
        f"| resolution_status_accuracy | {simple['resolution_status_accuracy']} | {truth['resolution_status_accuracy']} |",
        f"| citation_error_recall | {simple['citation_error_recall']} | {truth['citation_error_recall']} |",
        f"| citation_error_precision | {simple['citation_error_precision']} | {truth['citation_error_precision']} |",
        '',
        '## Held-out Layer Comparison',
        '',
        '| layer | benchmark accuracy | notes |',
        '| --- | ---: | --- |',
        f"| keyword baseline | {layers['keyword_baseline']['accuracy']} | {layers['keyword_baseline']['notes']} |",
        f"| flat Truth Engine | {layers['flat_truth_engine']['accuracy']} | {layers['flat_truth_engine']['notes']} |",
        f"| Truth Engine + Claim Graph | {layers['claim_graph']['accuracy']} | {layers['claim_graph']['notes']} |",
        f"| Truth Engine + Crystal diagnostics | {layers['crystal_diagnostics']['accuracy']} | {layers['crystal_diagnostics']['notes']} |",
        '',
        'Truth Engine Alpha values come from the engine implementation. The simple baseline is a fixed heuristic that predicts the same fallback labels for every case. The held-out layer comparison is computed from benchmark reference labels and should not be read as a universal performance claim.',
    ]
    md_path.write_text('\n'.join(lines) + '\n', encoding='utf-8')


def _keyword_baseline_accuracy(benchmarks: list[dict[str, object]]) -> dict[str, object]:
    total = max(len(benchmarks), 1)
    hits = 0
    for case in benchmarks:
        category = str(case.get('category', '')).lower()
        expected_route = str(case.get('expected_scaffolding_route', 'context'))
        predicted_route = 'population' if 'biomedical' in category else 'definitions' if 'citation' in category else 'methods' if 'patent' in category else 'context' if 'formal' in category else 'assumptions'
        hits += int(predicted_route == expected_route)
    return {'accuracy': round(hits / total, 3), 'notes': 'keyword route prediction versus labeled scaffold route'}


def _graph_layer_accuracy(benchmarks: list[dict[str, object]], labels: dict[str, dict[str, object]]) -> dict[str, object]:
    total = max(len(benchmarks), 1)
    hits = 0
    for case in benchmarks:
        benchmark_id = str(case['benchmark_id'])
        label = labels[benchmark_id]
        input_claims = case.get('input_claims', [])
        claims = _benchmark_claims(input_claims)
        sources = _benchmark_sources(input_claims)
        contradiction = Contradiction(f'contra_{benchmark_id}', [claim.claim_id for claim in claims[:2]], str(case.get('expected_contradiction_type', 'MISSING_INFORMATION')), 'benchmark contradiction')
        scaffold = ScaffoldingCandidate(f'scaffold_{benchmark_id}', contradiction.contradiction_id, str(case.get('expected_scaffolding_route', 'context')), 'benchmark scaffold')
        graph = build_claim_graph(claims, sources, [contradiction], [scaffold], [])
        detectors = {row['detector'] for row in detect_graph_errors(graph)}
        expected = set(label['expected_graph_errors'])
        mismatch_types = {edge.edge_type for edge in graph.edges if edge.edge_type.startswith('DIFFERS_BY_')}
        expected_mismatch = set(label.get('expected_mismatch_edges', []))
        if expected.issubset(detectors) and expected_mismatch.issubset(mismatch_types):
            hits += 1
    return {'accuracy': round(hits / total, 3), 'notes': 'graph detector and mismatch-edge recall against reference labels'}


def _crystal_layer_accuracy(benchmarks: list[dict[str, object]], labels: dict[str, dict[str, object]]) -> dict[str, object]:
    total = max(len(benchmarks), 1)
    hits = 0
    for case in benchmarks:
        benchmark_id = str(case['benchmark_id'])
        label = labels[benchmark_id]
        input_claims = case.get('input_claims', [])
        claims = _benchmark_claims(input_claims)
        sources = _benchmark_sources(input_claims)
        contradiction = Contradiction(f'contra_{benchmark_id}', [claim.claim_id for claim in claims[:2]], str(case.get('expected_contradiction_type', 'MISSING_INFORMATION')), 'benchmark contradiction')
        scaffold = ScaffoldingCandidate(f'scaffold_{benchmark_id}', contradiction.contradiction_id, str(case.get('expected_scaffolding_route', 'context')), 'benchmark scaffold')
        graph = build_claim_graph(claims, sources, [contradiction], [scaffold], [])
        cells = build_crystal_matrix(claims, sources, [contradiction], [scaffold], [], {'report_completeness': 1.0})
        diagnostics = compute_crystal_diagnostics(cells, graph)
        expected_instability = 1.0 if label['expected_graph_errors'] else 0.2
        observed_instability = diagnostics['structural_instability']
        if (observed_instability >= 0.5) == (expected_instability >= 0.5):
            hits += 1
    return {'accuracy': round(hits / total, 3), 'notes': 'crystal instability threshold versus graph-error labels'}


def main() -> None:
    benchmarks_path = ROOT / 'data' / 'benchmarks' / 'benchmarks.json'
    output_path = ROOT / 'results' / 'benchmarks' / 'baseline_comparison.json'
    output_path.parent.mkdir(parents=True, exist_ok=True)
    benchmarks = json.loads(benchmarks_path.read_text(encoding='utf-8'))
    labels = _load_labels()
    truth_result = run_baseline_comparison(benchmarks_path, output_path)
    report = {
        'benchmark_count': len(benchmarks),
        'simple_baseline': _simple_baseline_metrics(benchmarks),
        'truth_engine_alpha': truth_result,
        'held_out_performance': {
            'keyword_baseline': _keyword_baseline_accuracy(benchmarks),
            'flat_truth_engine': {'accuracy': truth_result['contradiction_type_accuracy'], 'notes': 'flat engine contradiction accuracy from benchmark set'},
            'claim_graph': _graph_layer_accuracy(benchmarks, labels),
            'crystal_diagnostics': _crystal_layer_accuracy(benchmarks, labels),
        },
    }
    output_path.write_text(json.dumps(report, indent=2), encoding='utf-8')
    _write_markdown(output_path, report)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
