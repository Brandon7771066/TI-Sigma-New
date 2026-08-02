from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    lines = path.read_text(encoding="utf-8").strip().splitlines()
    return [json.loads(line) for line in lines if line.strip()]


class StageAV3PipelinePhase4Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo_root = Path(__file__).resolve().parents[3]
        cls.pilot_root = cls.repo_root / "experiments" / "eight_c_goodness_pilot"

        repo_root_str = str(cls.repo_root)
        if repo_root_str not in sys.path:
            sys.path.insert(0, repo_root_str)

        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import io as io_mod
        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import mock_rater as mock_mod
        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import pipeline as pipeline_mod
        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import schema_check as schema_mod
        from experiments.eight_c_goodness_pilot.scripts import run_ti_sigma_stage_a_v3_mock_pipeline as runner_mod

        cls.io_mod = io_mod
        cls.mock_mod = mock_mod
        cls.schema_mod = schema_mod
        cls.pipeline_mod = pipeline_mod
        cls.runner_mod = runner_mod

        cls.items_csv = cls.pilot_root / "data" / "items" / "ti_sigma_stage_a_v3_items.csv"
        cls.metadata_csv = cls.pilot_root / "data" / "metadata" / "ti_sigma_stage_a_v3_metadata.csv"

    def test_merge_integrity(self):
        items = self.io_mod.load_items(self.items_csv)
        metadata = self.io_mod.load_metadata(self.metadata_csv)
        merged = self.io_mod.merge_items_with_metadata(items, metadata)

        self.assertEqual(len(items), 21)
        self.assertEqual(len(metadata), 21)
        self.assertEqual(len(merged), 21)
        self.assertIn("choice_bearer", merged[0])
        self.assertIn("choice_scope", merged[0])

    def test_mock_output_is_deterministic_and_schema_like(self):
        items = self.io_mod.load_items(self.items_csv)
        metadata = self.io_mod.load_metadata(self.metadata_csv)
        merged = self.io_mod.merge_items_with_metadata(items, metadata)
        row = merged[0]

        first = self.mock_mod.build_mock_rating(row, attempt_index=1)
        second = self.mock_mod.build_mock_rating(row, attempt_index=1)
        third = self.mock_mod.build_mock_rating(row, attempt_index=2)
        self.assertEqual(first, second)
        self.assertNotEqual(first, third)
        self.schema_mod.validate_rating_like_schema(first)

    def test_invalid_seed_strategy_raises(self):
        items = self.io_mod.load_items(self.items_csv)
        metadata = self.io_mod.load_metadata(self.metadata_csv)
        merged = self.io_mod.merge_items_with_metadata(items, metadata)
        with self.assertRaises(ValueError):
            self.mock_mod.build_mock_rating(merged[0], seed_strategy="bad_strategy")

        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "mock_ratings.jsonl"
            with self.assertRaises(ValueError):
                self.pipeline_mod.run_mock_pipeline(
                    self.items_csv,
                    self.metadata_csv,
                    output,
                    attempts_per_item=2,
                    seed_strategy="bad_strategy",
                )

    def test_pipeline_writes_attempt_expanded_jsonl_and_metrics(self):
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "mock_ratings.jsonl"
            metrics_path = Path(td) / "reproducibility.json"
            summary = self.pipeline_mod.run_mock_pipeline(
                self.items_csv,
                self.metadata_csv,
                output,
                attempts_per_item=3,
                output_metrics_json=metrics_path,
            )

            self.assertTrue(output.exists())
            self.assertTrue(metrics_path.exists())
            self.assertEqual(summary["attempts_per_item"], 3)
            self.assertEqual(summary["written"], 63)

            lines = output.read_text(encoding="utf-8").strip().splitlines()
            self.assertEqual(len(lines), 63)

            sample = json.loads(lines[0])
            self.schema_mod.validate_rating_like_schema(sample)

            metrics = json.loads(metrics_path.read_text(encoding="utf-8"))
            self.assertEqual(metrics["attempts_per_item"], 3)
            self.assertEqual(metrics["item_groups"], 21)
            self.assertGreaterEqual(metrics["exact_match_rate"], 0.0)
            self.assertLessEqual(metrics["exact_match_rate"], 1.0)
            self.assertIn("C_scores", metrics["mean_abs_diff"])
            self.assertIn("contradictions", metrics["mean_abs_diff"])

    def test_seed_strategy_fixed_is_exactly_reproducible(self):
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "mock_ratings_fixed.jsonl"
            metrics_path = Path(td) / "reproducibility_fixed.json"

            summary = self.pipeline_mod.run_mock_pipeline(
                self.items_csv,
                self.metadata_csv,
                output,
                attempts_per_item=3,
                output_metrics_json=metrics_path,
                seed_strategy="fixed",
                base_seed="TEST_FIXED_SEED",
            )

            self.assertEqual(summary["reproducibility"]["exact_match_rate"], 1.0)
            records = read_jsonl(output)
            self.assertEqual(len(records), 63)

            # For fixed strategy, attempt 1/2/3 records for each item should be identical.
            by_item: dict[str, list[dict]] = {}
            for record in records:
                by_item.setdefault(record["item_id"], []).append(record)
            self.assertEqual(len(by_item), 21)
            for group in by_item.values():
                self.assertEqual(len(group), 3)
                canonical = json.dumps(group[0], sort_keys=True)
                for entry in group[1:]:
                    self.assertEqual(json.dumps(entry, sort_keys=True), canonical)

    def test_markdown_report_render(self):
        metrics = {
            "attempts_per_item": 3,
            "item_groups": 21,
            "exact_match_rate": 0.25,
            "mean_abs_diff": {
                "goodness": 2.0,
                "C_scores": {"coherence": 1.0},
                "contradictions": {"true_incoherence": 0.5},
            },
        }
        md = self.runner_mod.render_reproducibility_markdown(metrics)
        self.assertIn("# TI Sigma Stage A v3 Mock Reproducibility Summary", md)
        self.assertIn("exact_match_rate: 0.250000", md)
        self.assertIn("| coherence | 1.000000 |", md)
        self.assertIn("| true_incoherence | 0.500000 |", md)


if __name__ == "__main__":
    unittest.main()