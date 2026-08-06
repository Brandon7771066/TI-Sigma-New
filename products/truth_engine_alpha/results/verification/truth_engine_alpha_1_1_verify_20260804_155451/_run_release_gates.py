import json
import sys
from copy import deepcopy
from pathlib import Path

root = Path(sys.argv[1])
baseline_dir = Path(sys.argv[2])
out_dir = Path(sys.argv[3])

sys.path.insert(0, str(root / "src"))

from truth_engine.engine import analyze_file
from truth_engine.research.pd_bridge import (
    attach_pd_shadow,
    build_pd_snapshot,
    default_pd_feature_gate,
    default_registry_paths,
    project_pd_to_truth_engine,
)

input_path = root / "data" / "inputs" / "ai_hallucination_audit_case_01.jsonl"
baseline_result_path = baseline_dir / "ai_hallucination_demo" / "full_result.json"
run_dir = out_dir / "pd_disabled_run"
run_dir.mkdir(parents=True, exist_ok=True)

analyze_file(input_path, run_dir, mode="standard", seed=0)

baseline_payload = json.loads(baseline_result_path.read_text(encoding="utf-8"))
current_payload = json.loads((run_dir / "full_result.json").read_text(encoding="utf-8"))

focus_keys = [
    "contradictions",
    "citation_audit",
    "scaffolding_analysis",
    "truth_engine_score",
    "recommended_actions",
    "resolution_status",
    "information_gain",
    "claim_graph",
    "graph_errors",
    "crystal_diagnostics",
]

payload_diffs = {}
for key in focus_keys:
    if baseline_payload.get(key) != current_payload.get(key):
        payload_diffs[key] = {
            "baseline": baseline_payload.get(key),
            "current": current_payload.get(key),
        }

file_checks = [
    "corrected_answer_outline.md",
    "citation_audit.csv",
    "scaffolding_analysis.csv",
    "recommended_actions.md",
    "resolution_report.md",
    "claim_graph.json",
    "crystal_diagnostics.json",
    "information_gain_actions.csv",
]

file_diffs = {}
for name in file_checks:
    baseline_text = (baseline_dir / "ai_hallucination_demo" / name).read_text(encoding="utf-8")
    current_text = (run_dir / name).read_text(encoding="utf-8")
    if baseline_text != current_text:
        file_diffs[name] = {
            "baseline_sha256": __import__("hashlib").sha256(baseline_text.encode("utf-8")).hexdigest(),
            "current_sha256": __import__("hashlib").sha256(current_text.encode("utf-8")).hexdigest(),
        }

eq_pass = len(payload_diffs) == 0 and len(file_diffs) == 0

(root / "results" / "verification").mkdir(parents=True, exist_ok=True)

equivalence_report = {
    "status": "PASS" if eq_pass else "FAIL",
    "baseline_result": str(baseline_result_path),
    "current_result": str(run_dir / "full_result.json"),
    "payload_diffs": payload_diffs,
    "file_diffs": file_diffs,
}
(out_dir / "pd_disabled_equivalence.json").write_text(json.dumps(equivalence_report, indent=2), encoding="utf-8")

threshold_path, ratio_path = default_registry_paths(root)
snapshot = build_pd_snapshot(
    pd_value=0.75,
    threshold_registry_path=threshold_path,
    ratio_registry_path=ratio_path,
)
projection = project_pd_to_truth_engine(snapshot, current_payload.get("truth_engine_score", {}))
gate = default_pd_feature_gate()
gate["pd"]["enabled"] = True
gate["pd"]["model"] = "continuous"
gate["pd"]["projection_target"] = "truth_engine_score"

shadow_payload = attach_pd_shadow(deepcopy(current_payload), gate, snapshot, projection)
shadow_clone = deepcopy(shadow_payload)
shadow_clone.pop("pd_research", None)

base_for_compare = deepcopy(current_payload)
isolation_pass = shadow_clone == base_for_compare and "pd_research" in shadow_payload and bool(shadow_payload["pd_research"].get("research_only"))

isolation_report = {
    "status": "PASS" if isolation_pass else "FAIL",
    "shadow_contains_pd_research": "pd_research" in shadow_payload,
    "shadow_research_only": bool(shadow_payload.get("pd_research", {}).get("research_only")),
    "production_payload_unchanged": shadow_clone == base_for_compare,
}
(out_dir / "pd_shadow_isolation.json").write_text(json.dumps(isolation_report, indent=2), encoding="utf-8")

summary_lines = [
    f"PD_DISABLED_PRODUCTION_EQUIVALENCE: {'PASS' if eq_pass else 'FAIL'}",
    f"PD_SHADOW_ISOLATION: {'PASS' if isolation_pass else 'FAIL'}",
]
(out_dir / "release_gate_summary.txt").write_text("\n".join(summary_lines) + "\n", encoding="utf-8")

if not eq_pass or not isolation_pass:
    raise SystemExit(2)
