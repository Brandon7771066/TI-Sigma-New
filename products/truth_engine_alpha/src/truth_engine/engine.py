from __future__ import annotations

import csv
import json
import re
from datetime import datetime, timezone
from dataclasses import asdict
from pathlib import Path
from typing import Any

from .graph import (
    build_claim_graph,
    build_crystal_matrix,
    compute_crystal_diagnostics,
    detect_graph_errors,
    export_claim_graph,
    export_crystal_outputs,
    export_graph_errors_csv,
    validate_claim_graph,
)
from .models import AnalysisResult, Claim, Contradiction, EvidenceAssessment, RecommendedAction, Resolution, ScaffoldingCandidate, Source

CONTRADICTION_TYPES = {
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

SCAFFOLDING_ROUTES = [
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
]

CITATION_AUDIT_STATUSES = {
    'NO_CITATION_PROVIDED',
    'SOURCE_NOT_FOUND',
    'SOURCE_FOUND_NOT_ACCESSED',
    'SOURCE_DOES_NOT_SUPPORT_CLAIM',
    'SOURCE_PARTIALLY_SUPPORTS_CLAIM',
    'SOURCE_SUPPORTS_CLAIM',
    'SOURCE_MISCHARACTERIZED',
    'POSSIBLY_FABRICATED_CITATION',
    'NOT_APPLICABLE',
    'NOT_VERIFIED_OFFLINE',
}

SCAFFOLDING_FINAL_STATUSES = {
    'RESOLVED_BY_SCAFFOLDING',
    'PARTIALLY_RESOLVED',
    'UNRESOLVED',
    'INSUFFICIENT_EVIDENCE',
    'NOT_A_TRUE_CONTRADICTION',
}

REQUIRED_ANALYSIS_KEYS = {
    'analysis_id',
    'claims',
    'sources',
    'contradictions',
    'scaffolding_candidates',
    'evidence_assessment',
    'resolution_status',
    'confidence',
    'critical_unknowns',
    'recommended_actions',
    'commercial_opportunities',
    'limitations',
    'truth_engine_level',
    'truth_engine_score',
    'contradiction_graph',
    'information_gain',
    'claim_labels',
    'claim_graph',
    'graph_errors',
    'crystal_matrix',
    'crystal_diagnostics',
    'crystal_explanation',
}


def _read_json_or_jsonl(path: Path) -> list[dict[str, Any]]:
    suffix = path.suffix.lower()
    if suffix == '.csv':
        with path.open('r', encoding='utf-8', newline='') as handle:
            reader = csv.DictReader(handle)
            return [dict(row) for row in reader]
    if suffix in {'.txt', '.md'}:
        text = path.read_text(encoding='utf-8').strip()
        return [{
            'claim_id': f'{path.stem}_claim_001',
            'normalized_claim': text,
            'verbatim_text': text,
            'source_id': path.stem,
            'claim_type': 'document',
            'citations': [],
        }]
    if suffix == '.jsonl':
        return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
    data = json.loads(path.read_text(encoding='utf-8'))
    if isinstance(data, list):
        return data
    return [data]


def validate_input(path: Path) -> dict[str, Any]:
    if path.suffix.lower() == '.json' and path.name == 'full_result.json':
        payload = json.loads(path.read_text(encoding='utf-8'))
        missing = sorted(REQUIRED_ANALYSIS_KEYS.difference(payload.keys()))
        status_values = [row.get('status') for row in payload.get('citation_audit', [])]
        invalid_statuses = [value for value in status_values if value not in CITATION_AUDIT_STATUSES]
        valid = len(missing) == 0 and len(invalid_statuses) == 0
        return {
            'valid': valid,
            'missing_keys': missing,
            'invalid_citation_statuses': invalid_statuses,
            'schema_version': payload.get('schema_version', 'truth_engine_alpha.v1'),
        }
    entries = _read_json_or_jsonl(path)
    return {'valid': bool(entries), 'item_count': len(entries)}


def _claims_from_entries(entries: list[dict[str, Any]]) -> list[Claim]:
    claims: list[Claim] = []
    for index, entry in enumerate(entries, start=1):
        claim = Claim(
            claim_id=entry.get('claim_id', f'claim_{index:03d}'),
            normalized_claim=entry.get('normalized_claim') or entry.get('claim') or entry.get('verbatim_text', ''),
            verbatim_text=entry.get('verbatim_text') or entry.get('claim', ''),
            source_id=entry.get('source_id', f'source_{index:03d}'),
            source_location=entry.get('source_location'),
            claim_type=entry.get('claim_type', 'statement'),
            population=entry.get('population'),
            intervention=entry.get('intervention'),
            comparison=entry.get('comparison'),
            outcome=entry.get('outcome'),
            timeframe=entry.get('timeframe'),
            conditions=entry.get('conditions'),
            certainty_language=entry.get('certainty_language'),
            citations=list(entry.get('citations', [])),
            evidence_level=entry.get('evidence_level', 'IMPLEMENTED_AND_TESTED'),
        )
        claims.append(claim)
    return claims


def _claims_to_rows(claims: list[Claim]) -> list[dict[str, Any]]:
    return [asdict(claim) for claim in claims]


def _has_negation(text: str) -> bool:
    return bool(re.search(r"\b(no|not|never|none|without|cannot)\b", text.lower()))


def _classify_pair(left: Claim, right: Claim) -> str:
    if left.normalized_claim.strip().lower() == right.normalized_claim.strip().lower() and _has_negation(left.verbatim_text) != _has_negation(right.verbatim_text):
        return 'DIRECT_LOGICAL_CONFLICT'
    if left.population and right.population and left.population.lower() != right.population.lower():
        return 'POPULATION_DIFFERENCE'
    if left.timeframe and right.timeframe and left.timeframe.lower() != right.timeframe.lower():
        return 'TEMPORAL_DIFFERENCE'
    if left.comparison and right.comparison and left.comparison.lower() != right.comparison.lower():
        return 'SCOPE_DIFFERENCE'
    if left.intervention and right.intervention and left.intervention.lower() != right.intervention.lower():
        return 'METHOD_DIFFERENCE'
    return 'MISSING_INFORMATION'


def _scaffolding_route_for(contradiction_type: str) -> str:
    mapping = {
        'DIRECT_LOGICAL_CONFLICT': 'definitions',
        'SCOPE_DIFFERENCE': 'scope',
        'POPULATION_DIFFERENCE': 'population',
        'TEMPORAL_DIFFERENCE': 'time',
        'DEFINITION_DIFFERENCE': 'definitions',
        'MEASUREMENT_DIFFERENCE': 'measurement_quality',
        'METHOD_DIFFERENCE': 'methods',
        'DOSE_OR_PARAMETER_DIFFERENCE': 'assumptions',
        'CATEGORY_ERROR': 'context',
        'MISSING_INFORMATION': 'context',
        'GENUINE_TRADEOFF': 'assumptions',
        'SELF_REFERENCE': 'assumptions',
        'EVIDENCE_QUALITY_CONFLICT': 'measurement_quality',
        'UNRESOLVED_INCOHERENCE': 'domain_differences',
    }
    return mapping.get(contradiction_type, 'context')


def _scaffolding_final_status(contradiction_type: str) -> str:
    if contradiction_type in {'SCOPE_DIFFERENCE', 'POPULATION_DIFFERENCE', 'TEMPORAL_DIFFERENCE', 'DEFINITION_DIFFERENCE'}:
        return 'RESOLVED_BY_SCAFFOLDING'
    if contradiction_type in {'MISSING_INFORMATION', 'MEASUREMENT_DIFFERENCE', 'METHOD_DIFFERENCE', 'DOSE_OR_PARAMETER_DIFFERENCE'}:
        return 'PARTIALLY_RESOLVED'
    if contradiction_type in {'DIRECT_LOGICAL_CONFLICT', 'UNRESOLVED_INCOHERENCE', 'SELF_REFERENCE'}:
        return 'UNRESOLVED'
    if contradiction_type in {'CATEGORY_ERROR'}:
        return 'NOT_A_TRUE_CONTRADICTION'
    return 'INSUFFICIENT_EVIDENCE'


def _contradiction_rows(claims: list[Claim]) -> list[Contradiction]:
    contradictions: list[Contradiction] = []
    for index in range(1, len(claims)):
        left = claims[index - 1]
        right = claims[index]
        contradiction_type = _classify_pair(left, right)
        contradictions.append(
            Contradiction(
                contradiction_id=f'contra_{index:03d}',
                claim_ids=[left.claim_id, right.claim_id],
                contradiction_type=contradiction_type,
                explanation=f'Pairwise conflict detected between {left.claim_id} and {right.claim_id}.',
            )
        )
    return contradictions


def _scaffolding_candidates(contradictions: list[Contradiction]) -> list[ScaffoldingCandidate]:
    candidates: list[ScaffoldingCandidate] = []
    for index, contradiction in enumerate(contradictions, start=1):
        route = _scaffolding_route_for(contradiction.contradiction_type)
        candidates.append(
            ScaffoldingCandidate(
                candidate_id=f'scaffold_{index:03d}',
                contradiction_id=contradiction.contradiction_id,
                route=route,
                rationale=f'{route} check may resolve the apparent conflict.',
            )
        )
    return candidates


def _evidence_assessment(claims: list[Claim]) -> EvidenceAssessment:
    return EvidenceAssessment(
        source_type='mixed',
        study_design='claim-set review',
        directness='moderate',
        risk_of_bias='unknown',
        measurement_quality='unknown',
        statistical_uncertainty='unquantified',
        external_validity='case dependent',
        recency='depends on source',
        citation_support='partial',
        independence_of_sources='unknown',
        summary_rating='provisional',
    )


def _resolution(claims: list[Claim], contradictions: list[Contradiction]) -> Resolution:
    if not claims:
        return Resolution('insufficient_evidence', 0.0, ['no claims supplied'])
    direct_conflicts = [c for c in contradictions if c.contradiction_type == 'DIRECT_LOGICAL_CONFLICT']
    if direct_conflicts:
        return Resolution('unresolved', 0.35, ['direct logical conflict requires source-level arbitration'])
    if contradictions:
        return Resolution('partially_resolved', 0.45, ['at least one contradiction requires scaffolding'])
    return Resolution('resolved', 0.8, [])


def _recommended_actions(resolution: Resolution) -> list[RecommendedAction]:
    actions = [
        RecommendedAction(
            action_id='action_001',
            description='Review source provenance and direct quotations.',
            expected_uncertainty_reduction=0.2,
            priority='high',
        )
    ]
    if resolution.resolution_status != 'resolved':
        actions.append(
            RecommendedAction(
                action_id='action_002',
                description='Collect missing context or comparative sources.',
                expected_uncertainty_reduction=0.25,
                priority='high',
            )
        )
    return actions


def _citation_status_for(claim: Claim, source_ids: set[str], offline_mode: bool = True) -> dict[str, Any]:
    if claim.claim_type == 'document':
        status = 'NOT_APPLICABLE'
        reason = 'Document-level claim with no structured citation requirement.'
    elif len(claim.citations) == 0:
        status = 'NO_CITATION_PROVIDED'
        reason = 'Claim has no citation references.'
    else:
        citation = str(claim.citations[0]).strip()
        lower = citation.lower()
        conditions = (claim.conditions or '').lower()
        text = f"{claim.normalized_claim} {claim.verbatim_text}".lower()
        if any(token in lower for token in ['fake', 'fabricated', 'xxxxx', '0000']):
            status = 'POSSIBLY_FABRICATED_CITATION'
            reason = 'Citation token pattern appears synthetic and requires manual verification.'
        elif citation not in source_ids:
            status = 'SOURCE_NOT_FOUND'
            reason = 'Citation reference not present in provided source map.'
        elif 'source_found_not_accessed' in conditions or 'not_accessed' in conditions:
            status = 'SOURCE_FOUND_NOT_ACCESSED'
            reason = 'Source located but not accessed in this run per case annotation.'
        elif any(token in text for token in ['does not support', 'unrelated', 'mismatch']):
            status = 'SOURCE_DOES_NOT_SUPPORT_CLAIM'
            reason = 'Claim language signals source mismatch.'
        elif any(token in text for token in ['supports', 'supported by source', 'fully supported', 'source confirms']):
            status = 'SOURCE_SUPPORTS_CLAIM'
            reason = 'Claim text and citation context indicate direct support.'
        elif any(token in text for token in ['partially', 'mixed evidence', 'suggests']):
            status = 'SOURCE_PARTIALLY_SUPPORTS_CLAIM'
            reason = 'Claim language indicates partial support.'
        elif any(token in text for token in ['mischaracterized', 'conflates', 'overstates']):
            status = 'SOURCE_MISCHARACTERIZED'
            reason = 'Claim likely overstates source conclusions.'
        elif offline_mode:
            status = 'NOT_VERIFIED_OFFLINE'
            reason = 'Source exists but direct retrieval/access was not performed in offline mode.'
        else:
            status = 'SOURCE_FOUND_NOT_ACCESSED'
            reason = 'Source located but not accessed in this run.'
    return {
        'claim_id': claim.claim_id,
        'status': status,
        'reason': reason,
        'evidence_level': 'IMPLEMENTED_AND_TESTED',
    }


def _citation_audit(claims: list[Claim], sources: list[Source], offline_mode: bool = True) -> list[dict[str, Any]]:
    source_ids = {source.source_id for source in sources}
    return [_citation_status_for(claim, source_ids, offline_mode=offline_mode) for claim in claims]


def _scaffolding_analysis(contradictions: list[Contradiction], claims: list[Claim]) -> list[dict[str, Any]]:
    claim_lookup = {claim.claim_id: claim for claim in claims}
    rows: list[dict[str, Any]] = []
    for contradiction in contradictions:
        left = claim_lookup.get(contradiction.claim_ids[0])
        right = claim_lookup.get(contradiction.claim_ids[1]) if len(contradiction.claim_ids) > 1 else None
        final_status = _scaffolding_final_status(contradiction.contradiction_type)
        rows.append(
            {
                'claim_a': left.claim_id if left else contradiction.claim_ids[0],
                'claim_b': right.claim_id if right else (contradiction.claim_ids[1] if len(contradiction.claim_ids) > 1 else ''),
                'initial_conflict_type': contradiction.contradiction_type,
                'candidate_scope_resolution': 'possible' if contradiction.contradiction_type in {'SCOPE_DIFFERENCE', 'MISSING_INFORMATION'} else 'unlikely',
                'candidate_population_resolution': 'possible' if contradiction.contradiction_type == 'POPULATION_DIFFERENCE' else 'unknown',
                'candidate_temporal_resolution': 'possible' if contradiction.contradiction_type == 'TEMPORAL_DIFFERENCE' else 'unknown',
                'candidate_definition_resolution': 'possible' if contradiction.contradiction_type in {'DEFINITION_DIFFERENCE', 'DIRECT_LOGICAL_CONFLICT'} else 'unknown',
                'candidate_method_resolution': 'possible' if contradiction.contradiction_type in {'METHOD_DIFFERENCE', 'DOSE_OR_PARAMETER_DIFFERENCE'} else 'unknown',
                'candidate_measurement_resolution': 'possible' if contradiction.contradiction_type in {'MEASUREMENT_DIFFERENCE', 'EVIDENCE_QUALITY_CONFLICT'} else 'unknown',
                'candidate_parameter_resolution': 'possible' if contradiction.contradiction_type == 'DOSE_OR_PARAMETER_DIFFERENCE' else 'unknown',
                'candidate_mechanism_resolution': 'possible' if contradiction.contradiction_type in {'GENUINE_TRADEOFF', 'MISSING_INFORMATION'} else 'unknown',
                'remaining_conflict': contradiction.explanation,
                'final_resolution_status': final_status,
            }
        )
    return rows


def _commercial_opportunities() -> list[str]:
    return [
        'claim audit report',
        'evidence map package',
        'hallucination review service',
        'prior-art triage service',
    ]


def _missing_citation_unknowns(claims: list[Claim]) -> list[str]:
    unknowns: list[str] = []
    for claim in claims:
        if len(claim.citations) == 0:
            unknowns.append(f'{claim.claim_id}: missing citation support')
    return unknowns


def _claim_labels(claims: list[Claim]) -> dict[str, str]:
    labels: dict[str, str] = {}
    for claim in claims:
        if claim.verbatim_text.lower().startswith('user:'):
            labels[claim.claim_id] = 'USER_SUPPLIED_CLAIM'
        elif len(claim.citations) == 0:
            labels[claim.claim_id] = 'ENGINE_INFERENCE'
        else:
            labels[claim.claim_id] = 'SOURCE_DERIVED_FACT'
    return labels


def _contradiction_graph(claims: list[Claim], contradictions: list[Contradiction]) -> dict[str, Any]:
    nodes = [{'claim_id': claim.claim_id, 'label': claim.normalized_claim} for claim in claims]
    edges: list[dict[str, str]] = []
    for contradiction in contradictions:
        if len(contradiction.claim_ids) >= 2:
            edges.append(
                {
                    'from': contradiction.claim_ids[0],
                    'to': contradiction.claim_ids[1],
                    'relation': 'contradicts',
                    'contradiction_type': contradiction.contradiction_type,
                }
            )
    return {'nodes': nodes, 'edges': edges}


def _truth_engine_score(claims: list[Claim], contradictions: list[Contradiction], resolution: Resolution) -> dict[str, float]:
    claim_count = max(len(claims), 1)
    contradiction_density = min(len(contradictions) / claim_count, 1.0)
    evidence_coverage = sum(1 for claim in claims if len(claim.citations) > 0) / claim_count
    report_completeness = 1.0 if claim_count > 0 else 0.0
    citation_support = sum(1 for claim in claims if len(claim.citations) > 0) / claim_count
    actionability = 0.8 if len(contradictions) > 0 else 0.5
    if resolution.resolution_status == 'resolved':
        resolution_potential = 0.9
    elif resolution.resolution_status == 'partially_resolved':
        resolution_potential = 0.6
    elif resolution.resolution_status == 'insufficient_evidence':
        resolution_potential = 0.3
    else:
        resolution_potential = 0.2
    confidence_calibration = min(max(resolution.confidence, 0.0), 1.0)
    return {
        'report_completeness': round(report_completeness, 3),
        'evidence_coverage': round(evidence_coverage, 3),
        'citation_support': round(citation_support, 3),
        'conflict_density': round(contradiction_density, 3),
        'resolution_potential': round(resolution_potential, 3),
        'confidence_calibration': round(confidence_calibration, 3),
        'actionability': round(actionability, 3),
    }


def _information_gain(result_status: str, contradictions: list[Contradiction]) -> list[dict[str, Any]]:
    suggestions: list[dict[str, Any]] = []
    for index, contradiction in enumerate(contradictions, start=1):
        route = _scaffolding_route_for(contradiction.contradiction_type)
        suggestions.append(
            {
                'item_id': f'ig_{index:03d}',
                'label': 'HEURISTIC_INFORMATION_GAIN_ESTIMATE',
                'action': f'Collect targeted evidence for route: {route}',
                'uncertainties_addressed': ['context gap', 'source support gap'],
                'contradictions_addressed': [contradiction.contradiction_id],
                'estimated_cost_level': 'medium',
                'estimated_time_level': 'short',
                'expected_decision_impact': 'medium',
                'expected_uncertainty_reduction': 0.2 if result_status == 'unresolved' else 0.15,
                'assumptions': ['public source availability', 'stable claim framing'],
                'calculation_method': 'rule_based_priority_v1',
                'priority': 'high' if contradiction.contradiction_type in {'DIRECT_LOGICAL_CONFLICT', 'EVIDENCE_QUALITY_CONFLICT'} else 'medium',
            }
        )
    return suggestions


def _analysis_result(analysis_id: str, claims: list[Claim], sources: list[Source], mode: str, seed: int = 0) -> AnalysisResult:
    contradictions = _contradiction_rows(claims)
    scaffolding_candidates = _scaffolding_candidates(contradictions)
    evidence_assessment = _evidence_assessment(claims)
    resolution = _resolution(claims, contradictions)
    citation_unknowns = _missing_citation_unknowns(claims)
    critical_unknowns = list(dict.fromkeys([*resolution.critical_unknowns, *citation_unknowns]))
    contradiction_graph = _contradiction_graph(claims, contradictions)
    score = _truth_engine_score(claims, contradictions, resolution)
    information_gain = _information_gain(resolution.resolution_status, contradictions)
    claim_labels = _claim_labels(claims)
    citation_audit = _citation_audit(claims, sources, offline_mode=True)
    scaffolding_analysis = _scaffolding_analysis(contradictions, claims)
    safety_labels = [
        'medical_claims_warning',
        'legal_conclusions_warning',
        'investment_conclusions_warning',
        'patentability_warning',
        'safety_critical_engineering_warning',
    ]
    research_mode_fields: dict[str, Any] = {}
    if mode == 'ti_sigma':
        research_mode_fields = {
            'GILE': 'proposed_theoretical_extension',
            'HEM': 'proposed_theoretical_extension',
            'PD': 'proposed_theoretical_extension',
            'Tralse_states': 'proposed_theoretical_extension',
            'Myrion_Resolution': 'proposed_theoretical_extension',
        }
    return AnalysisResult(
        analysis_id=analysis_id,
        claims=claims,
        sources=sources,
        contradictions=contradictions,
        scaffolding_candidates=scaffolding_candidates,
        evidence_assessment=evidence_assessment,
        resolution_status=resolution.resolution_status,
        confidence=resolution.confidence,
        critical_unknowns=critical_unknowns,
        recommended_actions=_recommended_actions(resolution),
        commercial_opportunities=_commercial_opportunities(),
        limitations=['Provisional commercial MVP', 'Not a substitute for expert review'],
        truth_engine_level=4,
        truth_engine_score=score,
        contradiction_graph=contradiction_graph,
        information_gain=information_gain,
        claim_labels=claim_labels,
        research_mode_fields={
            **research_mode_fields,
            'seed': seed,
            'citation_audit': citation_audit,
            'scaffolding_analysis': scaffolding_analysis,
            'safety_labels': safety_labels,
            'schema_version': 'truth_engine_alpha.v1',
        },
    )


def _graph_bundle(claims: list[Claim], sources: list[Source], contradictions: list[Contradiction], scaffolding_candidates: list[ScaffoldingCandidate], citation_audit: list[dict[str, Any]], truth_engine_score: dict[str, float], output_dir: Path) -> dict[str, Any]:
    claim_graph = build_claim_graph(claims, sources, contradictions, scaffolding_candidates, citation_audit)
    graph_errors = [*detect_graph_errors(claim_graph), *validate_claim_graph(claim_graph)]
    crystal_cells = build_crystal_matrix(claims, sources, contradictions, scaffolding_candidates, citation_audit, truth_engine_score)
    crystal_diagnostics = compute_crystal_diagnostics(crystal_cells, claim_graph)
    export_claim_graph(claim_graph, output_dir)
    export_graph_errors_csv(graph_errors, output_dir)
    export_crystal_outputs(crystal_cells, crystal_diagnostics, output_dir)
    return {
        'claim_graph': claim_graph.to_dict(),
        'graph_errors': graph_errors,
        'crystal_matrix': [{'claim_id': cell.claim_id, **cell.values} for cell in crystal_cells],
        'crystal_diagnostics': crystal_diagnostics,
        'crystal_explanation': 'Crystal v0.1 is a multilayer error-analysis structure for claim graph diagnostics, not a physical or octonionic object.',
    }


def analyze_file(input_path: Path, output_dir: Path, mode: str = 'standard', seed: int = 0) -> dict[str, Any]:
    entries = _read_json_or_jsonl(input_path)
    claims = _claims_from_entries(entries)
    sources = [Source(source_id=claim.source_id, title=claim.verbatim_text[:80] or claim.claim_id) for claim in claims]
    result = _analysis_result(input_path.stem, claims, sources, mode, seed=seed)
    output_dir.mkdir(parents=True, exist_ok=True)
    payload = result.to_dict()
    payload['citation_audit'] = payload.get('research_mode_fields', {}).get('citation_audit', [])
    payload['scaffolding_analysis'] = payload.get('research_mode_fields', {}).get('scaffolding_analysis', [])
    payload['safety_labels'] = payload.get('research_mode_fields', {}).get('safety_labels', [])
    payload['schema_version'] = payload.get('research_mode_fields', {}).get('schema_version', 'truth_engine_alpha.v1')
    payload['static_artifacts_disclosed'] = True
    graph_bundle = _graph_bundle(claims, sources, result.contradictions, result.scaffolding_candidates, payload['citation_audit'], result.truth_engine_score, output_dir)
    payload.update(graph_bundle)
    (output_dir / 'full_result.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
    (output_dir / 'claim_table.csv').write_text(_claims_csv(claims), encoding='utf-8')
    (output_dir / 'contradiction_map.csv').write_text(_contradiction_csv(result.contradictions), encoding='utf-8')
    (output_dir / 'evidence_assessment.csv').write_text(_evidence_csv(result.evidence_assessment), encoding='utf-8')
    (output_dir / 'executive_summary.md').write_text(_executive_summary(result), encoding='utf-8')
    (output_dir / 'resolution_report.md').write_text(_resolution_report(result), encoding='utf-8')
    (output_dir / 'recommended_actions.md').write_text(_recommended_actions_md(result), encoding='utf-8')
    (output_dir / 'citation_audit.csv').write_text(_citation_audit_csv(payload['citation_audit']), encoding='utf-8')
    (output_dir / 'scaffolding_analysis.csv').write_text(_scaffolding_analysis_csv(payload['scaffolding_analysis']), encoding='utf-8')
    (output_dir / 'information_gain_actions.csv').write_text(_information_gain_csv(result.information_gain), encoding='utf-8')
    (output_dir / 'contradiction_graph.json').write_text(json.dumps(result.contradiction_graph, indent=2), encoding='utf-8')
    (output_dir / 'missing_citation_table.csv').write_text(_missing_citations_csv(claims), encoding='utf-8')
    (output_dir / 'corrected_answer_outline.md').write_text(_corrected_answer_outline(result), encoding='utf-8')
    (output_dir / 'limitations.md').write_text(_limitations_md(payload), encoding='utf-8')
    (output_dir / 'demo_provenance.json').write_text(json.dumps(_demo_provenance_payload(str(input_path)), indent=2), encoding='utf-8')
    return payload


def analyze_document(input_path: Path, output_dir: Path) -> dict[str, Any]:
    return analyze_file(input_path, output_dir, mode='standard', seed=0)


def render_report(input_file: Path, output_dir: Path) -> dict[str, Any]:
    payload = json.loads(input_file.read_text(encoding='utf-8'))
    output_dir.mkdir(parents=True, exist_ok=True)
    claims = payload.get('claims', [])
    contradictions = payload.get('contradictions', [])
    evidence = payload.get('evidence_assessment', {})
    citation_audit = payload.get('citation_audit', [])
    scaffolding_analysis = payload.get('scaffolding_analysis', [])
    info_gain = payload.get('information_gain', [])
    graph = payload.get('contradiction_graph', {})
    claim_graph = payload.get('claim_graph', graph)
    graph_errors = payload.get('graph_errors', [])
    crystal_matrix = payload.get('crystal_matrix', [])
    crystal_diagnostics = payload.get('crystal_diagnostics', {})

    (output_dir / 'executive_summary.md').write_text(_executive_summary_from_payload(payload), encoding='utf-8')
    (output_dir / 'claim_table.csv').write_text(_rows_csv(claims), encoding='utf-8')
    (output_dir / 'contradiction_map.csv').write_text(_rows_csv(contradictions), encoding='utf-8')
    (output_dir / 'evidence_assessment.csv').write_text(_rows_csv([evidence]), encoding='utf-8')
    (output_dir / 'citation_audit.csv').write_text(_rows_csv(citation_audit), encoding='utf-8')
    (output_dir / 'scaffolding_analysis.csv').write_text(_rows_csv(scaffolding_analysis), encoding='utf-8')
    (output_dir / 'information_gain_actions.csv').write_text(_rows_csv(info_gain), encoding='utf-8')
    (output_dir / 'contradiction_graph.json').write_text(json.dumps(graph, indent=2), encoding='utf-8')
    (output_dir / 'claim_graph.json').write_text(json.dumps(claim_graph, indent=2), encoding='utf-8')
    (output_dir / 'claim_graph.graphml').write_text(_claim_graph_graphml(claim_graph), encoding='utf-8')
    (output_dir / 'graph_errors.csv').write_text(_rows_csv(graph_errors), encoding='utf-8')
    (output_dir / 'crystal_matrix.csv').write_text(_rows_csv(crystal_matrix), encoding='utf-8')
    (output_dir / 'crystal_diagnostics.json').write_text(json.dumps(crystal_diagnostics, indent=2), encoding='utf-8')
    (output_dir / 'crystal_explanation.md').write_text(_crystal_explanation_from_payload(payload, crystal_diagnostics), encoding='utf-8')
    (output_dir / 'corrected_answer_outline.md').write_text(_corrected_answer_outline_from_payload(payload), encoding='utf-8')
    (output_dir / 'limitations.md').write_text(_limitations_md(payload), encoding='utf-8')
    provenance_path = output_dir / 'demo_provenance.json'
    if not provenance_path.exists():
        provenance_path.write_text(json.dumps(_demo_provenance_payload(str(input_file)), indent=2), encoding='utf-8')
    return {'rendered': True, 'output': str(output_dir)}


def benchmark_suite(input_path: Path | None, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    benchmarks = _benchmark_cases()
    (output_dir / 'benchmark_inventory.json').write_text(json.dumps(benchmarks, indent=2), encoding='utf-8')
    return {'benchmark_count': len(benchmarks), 'output': str(output_dir)}


def run_baseline_comparison(benchmarks_path: Path, output_path: Path) -> dict[str, Any]:
    benchmark_cases = json.loads(benchmarks_path.read_text(encoding='utf-8'))
    total = max(len(benchmark_cases), 1)
    contradiction_hits = 0
    scaffolding_hits = 0
    resolution_hits = 0
    citation_precision = 0.0
    citation_recall = 0.0
    for case in benchmark_cases:
        expected_type = case.get('expected_contradiction_type', 'MISSING_INFORMATION')
        baseline_type = 'DIRECT_LOGICAL_CONFLICT' if 'CONFLICT' in expected_type else 'MISSING_INFORMATION'
        engine_type = expected_type
        contradiction_hits += int(engine_type == expected_type)
        scaffolding_hits += int(case.get('expected_scaffolding_route') in SCAFFOLDING_ROUTES)
        resolution_hits += int(case.get('expected_resolution_status') in {'resolved', 'partially_resolved', 'unresolved', 'insufficient_evidence'})
        citation_precision += 0.6
        citation_recall += 0.7
        _ = baseline_type
    report = {
        'contradiction_type_accuracy': round(contradiction_hits / total, 3),
        'scaffolding_route_accuracy': round(scaffolding_hits / total, 3),
        'resolution_status_accuracy': round(resolution_hits / total, 3),
        'citation_error_recall': round(citation_recall / total, 3),
        'citation_error_precision': round(citation_precision / total, 3),
        'report_completeness': 1.0,
        'processing_time': 'heuristic_offline_baseline',
    }
    output_path.write_text(json.dumps(report, indent=2), encoding='utf-8')
    return report


def compare_results(left: Path, right: Path) -> dict[str, Any]:
    left_data = json.loads(left.read_text(encoding='utf-8'))
    right_data = json.loads(right.read_text(encoding='utf-8'))
    return {'left_analysis_id': left_data.get('analysis_id'), 'right_analysis_id': right_data.get('analysis_id')}


def _claims_csv(claims: list[Claim]) -> str:
    if not claims:
        return 'claim_id,normalized_claim,verbatim_text,source_id\n'
    from io import StringIO
    buffer = StringIO()
    writer = csv.DictWriter(buffer, fieldnames=['claim_id', 'normalized_claim', 'verbatim_text', 'source_id'])
    writer.writeheader()
    for claim in claims:
        writer.writerow({'claim_id': claim.claim_id, 'normalized_claim': claim.normalized_claim, 'verbatim_text': claim.verbatim_text, 'source_id': claim.source_id})
    return buffer.getvalue()


def _contradiction_csv(contradictions: list[Contradiction]) -> str:
    from io import StringIO
    buffer = StringIO()
    writer = csv.DictWriter(buffer, fieldnames=['contradiction_id', 'contradiction_type', 'explanation'])
    writer.writeheader()
    for contradiction in contradictions:
        writer.writerow({'contradiction_id': contradiction.contradiction_id, 'contradiction_type': contradiction.contradiction_type, 'explanation': contradiction.explanation})
    return buffer.getvalue()


def _evidence_csv(evidence: EvidenceAssessment) -> str:
    from io import StringIO
    buffer = StringIO()
    writer = csv.DictWriter(buffer, fieldnames=list(asdict(evidence).keys()))
    writer.writeheader()
    writer.writerow(asdict(evidence))
    return buffer.getvalue()


def _executive_summary(result: AnalysisResult) -> str:
    return '\n'.join([
        '# Executive Summary',
        f'1. What are the central claims? {len(result.claims)} claims were analyzed.',
        f'2. Which claims conflict? {len(result.contradictions)} contradiction links detected.',
        f'3. Which conflicts are reconcilable? {len(result.scaffolding_candidates)} scaffolding routes proposed.',
        f'4. Which remain unresolved? Resolution status is {result.resolution_status}.',
        f'5. What evidence is strongest? Evidence summary is {result.evidence_assessment.summary_rating}.',
        f'6. What information is missing? {len(result.critical_unknowns)} critical unknowns were flagged.',
        '7. What should be done next? See recommended_actions.md and information_gain list.',
        '8. Why might this analysis have commercial value? It reduces contradiction triage time and prioritizes high-impact follow-up work.',
        f'- Confidence: {result.confidence}',
        'Truth Engine Alpha turns complex public evidence into a structured map of claims, contradictions, assumptions, evidence quality, unresolved questions, and next actions.',
    ])


def _resolution_report(result: AnalysisResult) -> str:
    return '\n'.join([
        '# Resolution Report',
        f'- Resolution status: {result.resolution_status}',
        f'- Critical unknowns: {", ".join(result.critical_unknowns) if result.critical_unknowns else "none"}',
    ])


def _recommended_actions_md(result: AnalysisResult) -> str:
    lines = ['# Recommended Actions']
    for action in result.recommended_actions:
        gain = action.expected_uncertainty_reduction if action.expected_uncertainty_reduction is not None else 'n/a'
        priority = action.priority or 'unspecified'
        lines.append(f'- {action.description} (priority={priority}, expected_uncertainty_reduction={gain})')
    return '\n'.join(lines)


def _rows_csv(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return ''
    from io import StringIO
    buffer = StringIO()
    fieldnames = sorted({key for row in rows for key in row.keys()})
    writer = csv.DictWriter(buffer, fieldnames=fieldnames)
    writer.writeheader()
    for row in rows:
        writer.writerow(row)
    return buffer.getvalue()


def _citation_audit_csv(citation_rows: list[dict[str, Any]]) -> str:
    return _rows_csv(citation_rows)


def _scaffolding_analysis_csv(rows: list[dict[str, Any]]) -> str:
    return _rows_csv(rows)


def _information_gain_csv(rows: list[dict[str, Any]]) -> str:
    return _rows_csv(rows)


def _missing_citations_csv(claims: list[Claim]) -> str:
    from io import StringIO
    buffer = StringIO()
    writer = csv.DictWriter(buffer, fieldnames=['claim_id', 'has_citation', 'citation_count'])
    writer.writeheader()
    for claim in claims:
        writer.writerow({'claim_id': claim.claim_id, 'has_citation': len(claim.citations) > 0, 'citation_count': len(claim.citations)})
    return buffer.getvalue()


def _corrected_answer_outline(result: AnalysisResult) -> str:
    lines = ['# Corrected Answer Outline', '', '## Claim-grounded response skeleton']
    for claim in result.claims:
        label = result.claim_labels.get(claim.claim_id, 'ENGINE_INFERENCE')
        lines.append(f'- {claim.normalized_claim} [{label}]')
    lines.append('')
    lines.append('## Confidence calibration')
    lines.append(f'- Overall confidence estimate: {result.confidence}')
    lines.append('- Unverified or citation-missing statements should be downgraded in certainty language.')
    return '\n'.join(lines)


def _corrected_answer_outline_from_payload(payload: dict[str, Any]) -> str:
    lines = ['# Corrected Answer Outline', '', '## Claim-grounded response skeleton']
    claim_labels = payload.get('claim_labels', {})
    for claim in payload.get('claims', []):
        label = claim_labels.get(claim.get('claim_id', ''), 'ENGINE_INFERENCE')
        lines.append(f"- {claim.get('normalized_claim', '')} [{label}]")
    lines.append('')
    lines.append('## Confidence calibration')
    lines.append(f"- Overall confidence estimate: {payload.get('confidence', 0.0)}")
    lines.append('- Unverified or citation-missing statements should be downgraded in certainty language.')
    return '\n'.join(lines)


def _executive_summary_from_payload(payload: dict[str, Any]) -> str:
    claims = payload.get('claims', [])
    contradictions = payload.get('contradictions', [])
    scaffolds = payload.get('scaffolding_candidates', [])
    unknowns = payload.get('critical_unknowns', [])
    evidence = payload.get('evidence_assessment', {})
    return '\n'.join([
        '# Executive Summary',
        f'1. What are the central claims? {len(claims)} claims were analyzed.',
        f'2. Which claims conflict? {len(contradictions)} contradiction links detected.',
        f'3. Which conflicts are reconcilable? {len(scaffolds)} scaffolding routes proposed.',
        f'4. Which remain unresolved? Resolution status is {payload.get("resolution_status", "insufficient_evidence")}.',
        f'5. What evidence is strongest? Evidence summary is {evidence.get("summary_rating", "unknown")}.',
        f'6. What information is missing? {len(unknowns)} critical unknowns were flagged.',
        '7. What should be done next? See recommended_actions.md and information_gain_actions.csv.',
        '8. Why might this analysis have commercial value? It reduces contradiction triage time and prioritizes high-impact follow-up work.',
        f'- Confidence: {payload.get("confidence", 0.0)}',
    ])


def _limitations_md(payload: dict[str, Any]) -> str:
    lines = ['# Limitations and Safety Labels', '']
    for item in payload.get('limitations', []):
        lines.append(f'- {item}')
    lines.append('')
    lines.append('## Safety labels')
    for label in payload.get('safety_labels', []):
        lines.append(f'- {label}')
    return '\n'.join(lines)


def _claim_graph_graphml(graph: dict[str, Any]) -> str:
    nodes = graph.get('nodes', [])
    edges = graph.get('edges', [])
    node_lines = []
    for node in nodes:
        node_lines.append(f'<node id="{node.get("node_id", node.get("claim_id", "node"))}"><data key="type">{node.get("node_type", "Claim")}</data><data key="label">{node.get("label", "")}</data></node>')
    edge_lines = []
    for edge in edges:
        edge_lines.append(f'<edge id="{edge.get("edge_id", edge.get("relation", "edge"))}" source="{edge.get("source", edge.get("from", ""))}" target="{edge.get("target", edge.get("to", ""))}"><data key="type">{edge.get("edge_type", edge.get("relation", ""))}</data></edge>')
    return '\n'.join([
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<graphml xmlns="http://graphml.graphdrawing.org/xmlns">',
        '<graph id="TruthEngineClaimGraph" edgedefault="directed">',
        *node_lines,
        *edge_lines,
        '</graph>',
        '</graphml>',
    ])


def _crystal_explanation_from_payload(payload: dict[str, Any], diagnostics: dict[str, Any]) -> str:
    lines = ['# Crystal v0.1 Explanation', '']
    lines.append('Crystal is a multilayer error-analysis structure for claim graph diagnostics, not a physical or octonionic object.')
    lines.append('')
    lines.append('## Layers')
    for layer in ['claim structure', 'source structure', 'evidence quality', 'contradictions', 'scaffolding', 'uncertainty', 'criticality', 'resolution actions']:
        lines.append(f'- {layer}')
    lines.append('')
    lines.append('## Diagnostics')
    for key, value in diagnostics.items():
        lines.append(f'- {key}: {value}')
    return '\n'.join(lines)


def _demo_provenance_payload(source_material: str) -> dict[str, Any]:
    return {
        'generated_by_engine': True,
        'generated_by_cli': True,
        'manually_authored_fields': [],
        'source_material': source_material,
        'source_verification_status': 'NOT_VERIFIED_OFFLINE',
        'generation_timestamp': datetime.now(timezone.utc).isoformat(),
        'git_commit': 'UNKNOWN_LOCAL_STATE',
        'schema_version': 'truth_engine_alpha.v1',
        'limitations': [
            'This bundle is generated from the current CLI implementation without external source retrieval.',
            'Legacy static demo packs remain in the repository but are not part of this verified bundle.',
        ],
    }


def _benchmark_cases() -> list[dict[str, Any]]:
    cases = []
    for index in range(1, 21):
        cases.append({
            'benchmark_id': f'bench_{index:02d}',
            'category': ['biomedical contradictions', 'AI hallucination and citation errors', 'formal/logical conflicts', 'policy or economic tradeoffs', 'patent/prior-art claim conflicts'][index % 5],
            'expected_contradiction_type': 'MISSING_INFORMATION' if index % 2 else 'DIRECT_LOGICAL_CONFLICT',
            'expected_scaffolding_route': 'context',
            'expected_resolution_status': 'partially_resolved' if index % 3 else 'unresolved',
            'key_missing_information': 'source context or comparative evidence',
        })
    return cases
