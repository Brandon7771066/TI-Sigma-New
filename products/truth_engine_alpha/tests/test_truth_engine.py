import json
from pathlib import Path

from truth_engine.engine import (
    CITATION_AUDIT_STATUSES,
    CONTRADICTION_TYPES,
    SCAFFOLDING_FINAL_STATUSES,
    SCAFFOLDING_ROUTES,
    analyze_file,
    benchmark_suite,
    render_report,
    validate_input,
)
from truth_engine.algebra import OctonionFeatureBlock, QutritEncoder, QuaternionFeatureBlock, SedenionFeatureBlock
from truth_engine.graph import (
    build_claim_graph,
    build_crystal_matrix,
    compute_crystal_diagnostics,
    detect_graph_errors,
    export_claim_graph,
    export_crystal_outputs,
    export_graph_errors_csv,
)
from truth_engine.graph.models import ClaimGraph, GraphEdge, GraphNode
from truth_engine.graph.validators import validate_claim_graph
from truth_engine.models import Claim, Contradiction, ScaffoldingCandidate, Source


def test_validate_input_reads_jsonl(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text('{"claim_id":"c1","verbatim_text":"a","source_id":"s1"}\n', encoding='utf-8')
    result = validate_input(input_path)
    assert result['valid'] is True
    assert result['item_count'] == 1


def test_analyze_file_writes_outputs(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text('{"claim_id":"c1","verbatim_text":"a","source_id":"s1"}\n{"claim_id":"c2","verbatim_text":"b","source_id":"s2"}\n', encoding='utf-8')
    output_dir = tmp_path / 'out'
    result = analyze_file(input_path, output_dir)
    assert result['analysis_id'] == 'claims'
    assert (output_dir / 'full_result.json').exists()
    assert (output_dir / 'claim_table.csv').exists()
    assert (output_dir / 'contradiction_map.csv').exists()
    assert (output_dir / 'evidence_assessment.csv').exists()
    assert (output_dir / 'executive_summary.md').exists()
    assert (output_dir / 'resolution_report.md').exists()
    assert (output_dir / 'recommended_actions.md').exists()
    assert (output_dir / 'missing_citation_table.csv').exists()
    assert (output_dir / 'corrected_answer_outline.md').exists()
    assert (output_dir / 'citation_audit.csv').exists()
    assert (output_dir / 'scaffolding_analysis.csv').exists()
    assert (output_dir / 'information_gain_actions.csv').exists()
    assert (output_dir / 'contradiction_graph.json').exists()
    assert (output_dir / 'claim_graph.json').exists()
    assert (output_dir / 'claim_graph.graphml').exists()
    assert (output_dir / 'graph_errors.csv').exists()
    assert (output_dir / 'crystal_matrix.csv').exists()
    assert (output_dir / 'crystal_diagnostics.json').exists()
    assert (output_dir / 'crystal_explanation.md').exists()
    assert (output_dir / 'limitations.md').exists()
    assert (output_dir / 'demo_provenance.json').exists()
    assert 'truth_engine_score' in result
    assert 'information_gain' in result
    assert 'contradiction_graph' in result
    assert 'claim_labels' in result
    assert 'citation_audit' in result
    assert 'scaffolding_analysis' in result
    assert result['static_artifacts_disclosed'] is True


def test_benchmark_suite_writes_inventory(tmp_path):
    output_dir = tmp_path / 'bench'
    result = benchmark_suite(None, output_dir)
    assert result['benchmark_count'] == 20
    assert (output_dir / 'benchmark_inventory.json').exists()


def test_analyze_file_supports_csv_input(tmp_path):
    input_path = tmp_path / 'claims.csv'
    input_path.write_text('claim_id,verbatim_text,source_id\nc1,CSV claim,s1\n', encoding='utf-8')
    output_dir = tmp_path / 'csv_out'
    result = analyze_file(input_path, output_dir)
    assert result['analysis_id'] == 'claims'
    assert len(result['claims']) == 1


def test_analyze_file_supports_markdown_input(tmp_path):
    input_path = tmp_path / 'note.md'
    input_path.write_text('A markdown claim body for parsing.', encoding='utf-8')
    output_dir = tmp_path / 'md_out'
    result = analyze_file(input_path, output_dir)
    assert result['analysis_id'] == 'note'
    assert len(result['claims']) == 1


def test_analyze_file_supports_text_input(tmp_path):
    input_path = tmp_path / 'note.txt'
    input_path.write_text('A text claim body for parsing.', encoding='utf-8')
    output_dir = tmp_path / 'txt_out'
    result = analyze_file(input_path, output_dir)
    assert result['analysis_id'] == 'note'
    assert len(result['claims']) == 1


def test_contradiction_taxonomy_and_scaffolding_routes_present():
    expected_types = {
        'DIRECT_LOGICAL_CONFLICT',
        'SCOPE_DIFFERENCE',
        'POPULATION_DIFFERENCE',
        'TEMPORAL_DIFFERENCE',
        'DEFINITION_DIFFERENCE',
        'MEASUREMENT_DIFFERENCE',
        'METHOD_DIFFERENCE',
        'DOSE_OR_PARAMETER_DIFFERENCE',
        'CATEGORY_ERROR',
        'MISSING_INFORMATION',
        'GENUINE_TRADEOFF',
        'SELF_REFERENCE',
        'EVIDENCE_QUALITY_CONFLICT',
        'UNRESOLVED_INCOHERENCE',
    }
    assert expected_types.issubset(CONTRADICTION_TYPES)

    expected_routes = {
        'scope',
        'context',
        'time',
        'population',
        'definitions',
        'methods',
        'mechanisms',
        'assumptions',
        'measurement_quality',
        'domain_differences',
    }
    assert expected_routes.issubset(set(SCAFFOLDING_ROUTES))


def test_missing_and_unsupported_citation_statuses(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"no citation claim","source_id":"s1","citations":[]}\n'
        '{"claim_id":"c2","verbatim_text":"claim with unmatched citation","source_id":"s2","citations":["missing_source"]}\n'
        '{"claim_id":"c3","verbatim_text":"source confirms and supports the claim","source_id":"s3","citations":["s3"]}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    statuses = {row['status'] for row in result['citation_audit']}
    assert 'NO_CITATION_PROVIDED' in statuses
    assert 'SOURCE_NOT_FOUND' in statuses
    assert 'SOURCE_SUPPORTS_CLAIM' in statuses
    assert statuses.issubset(CITATION_AUDIT_STATUSES)


def test_offline_nonverification_status_is_distinct_from_fabrication(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"claim with valid source reference","source_id":"s1","citations":["s1"]}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    status = result['citation_audit'][0]['status']
    assert status == 'NOT_VERIFIED_OFFLINE'


def test_scaffolding_output_has_required_fields(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim A","source_id":"s1","population":"adult"}\n'
        '{"claim_id":"c2","verbatim_text":"Claim B","source_id":"s2","population":"pediatric"}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    rows = result['scaffolding_analysis']
    assert len(rows) >= 1
    required = {
        'claim_a',
        'claim_b',
        'initial_conflict_type',
        'candidate_scope_resolution',
        'candidate_population_resolution',
        'candidate_temporal_resolution',
        'candidate_definition_resolution',
        'candidate_method_resolution',
        'candidate_measurement_resolution',
        'candidate_parameter_resolution',
        'candidate_mechanism_resolution',
        'remaining_conflict',
        'final_resolution_status',
    }
    assert required.issubset(rows[0].keys())
    assert rows[0]['final_resolution_status'] in SCAFFOLDING_FINAL_STATUSES


def test_graph_integrity_and_information_gain_structure(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim A","source_id":"s1"}\n'
        '{"claim_id":"c2","verbatim_text":"Claim B","source_id":"s2"}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    node_ids = {node['claim_id'] for node in result['contradiction_graph']['nodes']}
    for edge in result['contradiction_graph']['edges']:
        assert edge['from'] in node_ids
        assert edge['to'] in node_ids
    gain = result['information_gain']
    assert len(gain) >= 1
    gain_required = {
        'label',
        'action',
        'uncertainties_addressed',
        'contradictions_addressed',
        'estimated_cost_level',
        'estimated_time_level',
        'expected_decision_impact',
        'expected_uncertainty_reduction',
        'assumptions',
        'calculation_method',
        'priority',
    }
    assert gain_required.issubset(gain[0].keys())
    assert gain[0]['label'] == 'HEURISTIC_INFORMATION_GAIN_ESTIMATE'


def test_graph_construction_and_detectors(tmp_path):
    output_dir = tmp_path / 'graph_out'
    claims = [
        Claim('c1', 'Claim A supports the claim', 'Claim A supports the claim', 's1', citations=['s1'], population='adult', intervention='therapy'),
        Claim('c2', 'Claim B contradicts the claim', 'Claim B contradicts the claim', 's2', citations=[], population='pediatric', intervention='therapy'),
    ]
    sources = [Source('s1', 'source one'), Source('s2', 'source two')]
    contradictions = []
    scaffolds = []
    citation_audit = [
        {'claim_id': 'c1', 'status': 'SOURCE_SUPPORTS_CLAIM', 'reason': 'supported'},
    ]
    graph = build_claim_graph(claims, sources, contradictions, scaffolds, citation_audit)
    errors = detect_graph_errors(graph)
    cells = build_crystal_matrix(claims, sources, contradictions, scaffolds, citation_audit, {'report_completeness': 1.0})
    diagnostics = compute_crystal_diagnostics(cells, graph)
    export_claim_graph(graph, output_dir)
    export_graph_errors_csv(errors, output_dir)
    export_crystal_outputs(cells, diagnostics, output_dir)
    assert graph.nodes
    assert graph.edges
    assert errors
    assert 'unsupported_claim' in {error['detector'] for error in errors}
    assert (output_dir / 'claim_graph.json').exists()
    assert (output_dir / 'claim_graph.graphml').exists()
    assert (output_dir / 'graph_errors.csv').exists()
    assert (output_dir / 'crystal_matrix.csv').exists()
    assert (output_dir / 'crystal_diagnostics.json').exists()
    assert (output_dir / 'crystal_explanation.md').exists()
    assert 0.0 <= diagnostics['isolated_claim_score'] <= 1.0
    assert 0.0 <= diagnostics['structural_instability'] <= 1.0


def test_graph_mismatch_detectors():
    graph = ClaimGraph(
        nodes=[
            GraphNode('c1', 'Claim', 'claim one'),
            GraphNode('c2', 'Claim', 'claim two'),
        ],
        edges=[
            GraphEdge('e1', 'c1', 'c2', 'DIFFERS_BY_SCOPE', 'scope mismatch', 0.9, 'high'),
            GraphEdge('e2', 'c1', 'c2', 'DIFFERS_BY_POPULATION', 'population mismatch', 0.9, 'high'),
            GraphEdge('e3', 'c1', 'c2', 'DIFFERS_BY_TIME', 'temporal mismatch', 0.9, 'high'),
            GraphEdge('e4', 'c1', 'c2', 'DIFFERS_BY_DEFINITION', 'definition mismatch', 0.9, 'high'),
        ],
    )
    detectors = {error['detector'] for error in detect_graph_errors(graph)}
    assert 'scope_mismatch' in detectors
    assert 'population_mismatch' in detectors
    assert 'temporal_mismatch' in detectors
    assert 'definition_mismatch' in detectors


def test_graph_cycle_and_missing_dependency_detectors():
    graph = ClaimGraph(
        nodes=[
            GraphNode('c1', 'Claim', 'claim one'),
            GraphNode('c2', 'Claim', 'claim two'),
            GraphNode('s1', 'Source', 'source one'),
        ],
        edges=[
            GraphEdge('e1', 'c1', 'c2', 'SUPPORTS', 'support one', 0.8, 'high'),
            GraphEdge('e2', 'c2', 'c1', 'SUPPORTS', 'support two', 0.8, 'high'),
            GraphEdge('e3', 'c1', 'missing', 'CITES', 'missing target', 0.5, 'medium'),
        ],
    )
    detectors = {error['detector'] for error in detect_graph_errors(graph)}
    validation_detectors = {error['detector'] for error in validate_claim_graph(graph)}
    assert 'circular_support' in detectors
    assert 'missing_dependency' in validation_detectors


def test_crystal_alignment_and_missing_data_behavior():
    claims = [Claim('c1', 'claim one', 'claim one', 's1'), Claim('c2', 'claim two', 'claim two', 's2')]
    sources = [Source('s1', 'source one'), Source('s2', 'source two')]
    graph = build_claim_graph(claims, sources, [], [], [])
    cells = build_crystal_matrix(claims, sources, [], [], [], {'report_completeness': 1.0})
    diagnostics = compute_crystal_diagnostics(cells, graph)
    assert len(cells) == len(claims)
    assert set(cells[0].values.keys()).issuperset({
        'claim structure',
        'source structure',
        'evidence quality',
        'contradictions',
        'scaffolding',
        'uncertainty',
        'criticality',
        'resolution actions',
    })
    assert 0.0 <= diagnostics['conflict_density'] <= 1.0
    assert 0.0 <= diagnostics['source_dependency_concentration'] <= 1.0


def test_future_algebra_interface_shape():
    features = {'a': 1.0, 'b': 2.0, 'c': 3.0}
    quaternion = QuaternionFeatureBlock(features)
    octonion = OctonionFeatureBlock(features)
    sedenion = SedenionFeatureBlock(features)
    qutrit = QutritEncoder(features)
    order = ['a', 'b', 'c']
    assert quaternion.status == 'PROPOSED_THEORETICAL_EXTENSION'
    assert octonion.status == 'PROPOSED_THEORETICAL_EXTENSION'
    assert sedenion.status == 'PROPOSED_THEORETICAL_EXTENSION'
    assert qutrit.status == 'PROPOSED_THEORETICAL_EXTENSION'
    assert quaternion.to_scalar_vector(order) == [1.0, 2.0, 3.0]
    assert octonion.to_scalar_vector(order) == [1.0, 2.0, 3.0]
    assert sedenion.to_scalar_vector(order) == [1.0, 2.0, 3.0]
    assert qutrit.encode(order) == [1.0, 2.0, 3.0]
    assert qutrit.decode(order, [3.0, 2.0, 1.0]) == {'a': 3.0, 'b': 2.0, 'c': 1.0}


def test_operational_score_ranges(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text('{"claim_id":"c1","verbatim_text":"Claim A","source_id":"s1"}\n', encoding='utf-8')
    result = analyze_file(input_path, tmp_path / 'out')
    for value in result['truth_engine_score'].values():
        assert 0.0 <= value <= 1.0


def test_schema_validate_and_report_regeneration(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim A","source_id":"s1"}\n'
        '{"claim_id":"c2","verbatim_text":"Claim B","source_id":"s2"}\n',
        encoding='utf-8',
    )
    output_dir = tmp_path / 'out'
    analyze_file(input_path, output_dir, seed=42)
    validate = validate_input(output_dir / 'full_result.json')
    assert validate['valid'] is True
    render_report(output_dir / 'full_result.json', output_dir)
    assert (output_dir / 'citation_audit.csv').exists()
    assert (output_dir / 'scaffolding_analysis.csv').exists()
    assert (output_dir / 'information_gain_actions.csv').exists()
    assert (output_dir / 'limitations.md').exists()


def test_deterministic_output_with_fixed_seed(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim A","source_id":"s1"}\n'
        '{"claim_id":"c2","verbatim_text":"Claim B","source_id":"s2"}\n',
        encoding='utf-8',
    )
    out1 = tmp_path / 'out1'
    out2 = tmp_path / 'out2'
    result1 = analyze_file(input_path, out1, seed=7)
    result2 = analyze_file(input_path, out2, seed=7)
    assert result1 == result2


def test_refusal_to_fabricate_citations(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim with unknown citation","source_id":"s1","citations":["unknown_ref"]}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    status = result['citation_audit'][0]['status']
    assert status in {'SOURCE_NOT_FOUND', 'NOT_VERIFIED_OFFLINE'}


def test_safety_labels_present_for_risk_domains(tmp_path):
    input_path = tmp_path / 'claims.jsonl'
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Medical claim example","source_id":"s1","claim_type":"medical"}\n',
        encoding='utf-8',
    )
    result = analyze_file(input_path, tmp_path / 'out')
    labels = set(result['safety_labels'])
    assert 'medical_claims_warning' in labels
    assert 'legal_conclusions_warning' in labels
    assert 'investment_conclusions_warning' in labels
    assert 'patentability_warning' in labels
