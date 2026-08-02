from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path


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

        cls.io_mod = io_mod
        cls.mock_mod = mock_mod
        cls.schema_mod = schema_mod
        cls.pipeline_mod = pipeline_mod

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

        first = self.mock_mod.build_mock_rating(row)
        second = self.mock_mod.build_mock_rating(row)
        self.assertEqual(first, second)
        self.schema_mod.validate_rating_like_schema(first)

    def test_pipeline_writes_one_json_per_item(self):
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "mock_ratings.jsonl"
            summary = self.pipeline_mod.run_mock_pipeline(self.items_csv, self.metadata_csv, output)

            self.assertTrue(output.exists())
            self.assertEqual(summary["written"], 21)

            lines = output.read_text(encoding="utf-8").strip().splitlines()
            self.assertEqual(len(lines), 21)

            sample = json.loads(lines[0])
            self.schema_mod.validate_rating_like_schema(sample)


if __name__ == "__main__":
    unittest.main()