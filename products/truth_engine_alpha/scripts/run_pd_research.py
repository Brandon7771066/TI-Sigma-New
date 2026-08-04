from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
import sys
from uuid import uuid4

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from truth_engine.research import (
    PDSoftTernaryModel,
    PDVariantMetadata,
    attach_pd_shadow,
    build_pd_snapshot,
    default_pd_feature_gate,
    default_registry_paths,
    load_threshold_registry,
    pd_variant_registry,
    project_pd_to_truth_engine,
    select_default_threshold,
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run standalone PD research artifact generation.")
    parser.add_argument("--variant", default="continuous", choices=["continuous", "ternary", "soft_ternary"])
    parser.add_argument("--value", type=float, default=0.0)
    parser.add_argument("--threshold-set", default="default")
    parser.add_argument("--decoder", default="gaussian_softmax")
    parser.add_argument("--pd-enabled", action="store_true", help="Attach PD snapshot/projection in shadow mode payload.")
    parser.add_argument("--projection-target", default="truth_engine_score")
    return parser.parse_args()


def _resolve_profile_id(arg_value: str) -> str | None:
    if arg_value in {"default", "historical_candidate_001"}:
        return None
    return arg_value


def main() -> None:
    args = _parse_args()
    root = ROOT
    threshold_path, ratio_path = default_registry_paths(root)
    profile_id = _resolve_profile_id(args.threshold_set)

    snapshot = build_pd_snapshot(
        pd_value=args.value,
        threshold_registry_path=threshold_path,
        ratio_registry_path=ratio_path,
        profile_id=profile_id,
    )

    thresholds = load_threshold_registry(threshold_path)
    active_profile = select_default_threshold(thresholds) if profile_id is None else next(p for p in thresholds if p.profile_id == profile_id)

    if args.variant == "soft_ternary":
        soft_model = PDSoftTernaryModel(
            metadata=PDVariantMetadata(
                pd_variant="PD-S",
                version="v0.1",
                range="simplex probabilities",
                threshold_set=active_profile.profile_id,
                provenance_ids=[active_profile.provenance_passage_id],
                calibration_status="UNCALIBRATED",
                validation_status="UNVALIDATED",
                research_only=True,
            )
        )
        soft_state = soft_model.encode({"p_false": 0.2, "p_indeterminate": 0.3, "p_true": 0.5})
        ternary_readout = soft_model.decode(soft_state)
    else:
        soft_state = snapshot["qutrit_state"]
        ternary_readout = {"hard_ternary": snapshot["pd_status"]}

    projection = project_pd_to_truth_engine(
        snapshot,
        {
            "report_completeness": 0.9,
            "conflict_density": 0.4,
            "actionability": 0.7,
        },
    )

    gate = default_pd_feature_gate()
    gate["pd"]["enabled"] = bool(args.pd_enabled)
    gate["pd"]["model"] = args.variant
    gate["pd"]["projection_target"] = args.projection_target
    shadow_payload = attach_pd_shadow({"mode": "standard", "truth_engine_score": {"report_completeness": 0.9}}, gate, snapshot, projection)

    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "_" + str(uuid4())[:8]
    out_dir = root / "results" / "research" / "pd_and_quantum" / "runs" / run_id
    out_dir.mkdir(parents=True, exist_ok=True)

    pd_input = {
        "variant": args.variant,
        "value": args.value,
        "threshold_set": args.threshold_set,
        "decoder": args.decoder,
        "gate": gate,
    }
    (out_dir / "pd_input.json").write_text(json.dumps(pd_input, indent=2), encoding="utf-8")
    (out_dir / "pd_snapshot.json").write_text(json.dumps(snapshot, indent=2), encoding="utf-8")
    (out_dir / "ternary_readout.json").write_text(json.dumps(ternary_readout, indent=2), encoding="utf-8")
    (out_dir / "pd_projection.json").write_text(json.dumps(projection, indent=2), encoding="utf-8")
    (out_dir / "provenance.json").write_text(
        json.dumps(
            {
                "generated_at": datetime.now(timezone.utc).isoformat(),
                "research_only": True,
                "threshold_profile": snapshot["threshold_profile"],
                "threshold_provenance": snapshot["threshold_profile"]["provenance_passage_id"],
                "ratio_provenance": [row["provenance_passage_id"] for row in snapshot["ratios"]],
                "variant_registry": pd_variant_registry(active_profile),
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    (out_dir / "validation.json").write_text(
        json.dumps(
            {
                "soft_ternary_sum": sum(snapshot["qutrit_state"][k] for k in ["p_false", "p_indeterminate", "p_true"]),
                "shadow_payload_has_pd": "pd_research" in shadow_payload,
                "gate": gate,
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    explanation = [
        "# PD Research Run",
        "",
        f"run_id: {run_id}",
        f"variant: {args.variant}",
        f"pd_value: {args.value}",
        f"threshold_set: {snapshot['threshold_profile']['profile_id']}",
        "",
        "This run is research-only and does not alter production report artifacts.",
        f"Feature gate enabled: {gate['pd']['enabled']}",
    ]
    (out_dir / "explanation.md").write_text("\n".join(explanation) + "\n", encoding="utf-8")

    print(json.dumps({"run_id": run_id, "output_dir": str(out_dir)}, indent=2))


if __name__ == "__main__":
    main()
