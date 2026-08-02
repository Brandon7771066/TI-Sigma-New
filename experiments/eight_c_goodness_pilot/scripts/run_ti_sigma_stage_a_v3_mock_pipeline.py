from __future__ import annotations

import sys
from pathlib import Path


def main() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    repo_root_str = str(repo_root)
    if repo_root_str not in sys.path:
        sys.path.insert(0, repo_root_str)

    from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import run_mock_pipeline

    pilot_root = repo_root / "experiments" / "eight_c_goodness_pilot"

    items_csv = pilot_root / "data" / "items" / "ti_sigma_stage_a_v3_items.csv"
    metadata_csv = pilot_root / "data" / "metadata" / "ti_sigma_stage_a_v3_metadata.csv"
    output_jsonl = pilot_root / "results" / "ratings" / "ti_sigma_stage_a_v3_mock_ratings.jsonl"
    output_metrics_json = pilot_root / "results" / "reports" / "ti_sigma_stage_a_v3_mock_reproducibility.json"

    summary = run_mock_pipeline(
        items_csv,
        metadata_csv,
        output_jsonl,
        attempts_per_item=3,
        output_metrics_json=output_metrics_json,
    )

    print("MOCK_PIPELINE_SUMMARY")
    print(f"items={summary['items']}")
    print(f"metadata={summary['metadata']}")
    print(f"attempts_per_item={summary['attempts_per_item']}")
    print(f"written={summary['written']}")
    print(f"exact_match_rate={summary['reproducibility']['exact_match_rate']}")
    print(f"output={output_jsonl}")
    print(f"reproducibility_metrics={output_metrics_json}")


if __name__ == "__main__":
    main()