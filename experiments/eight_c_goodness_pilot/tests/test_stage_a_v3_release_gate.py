from __future__ import annotations

import json
import socket
import sys
import tempfile
import unittest
from pathlib import Path


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows: list[dict] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


class StageAV3ReleaseGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo_root = Path(__file__).resolve().parents[3]
        repo_root_str = str(cls.repo_root)
        if repo_root_str not in sys.path:
            sys.path.insert(0, repo_root_str)

        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import schema_check as schema_mod
        from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import stage_a_v3 as stage_mod

        cls.schema_mod = schema_mod
        cls.stage_mod = stage_mod
        cls.default_paths = stage_mod.build_default_paths(cls.repo_root)
        cls.config = stage_mod.load_config(cls.default_paths.config_path)

    def make_paths(self, experiments_dir: Path, freeze_manifest_path: Path | None = None):
        paths = self.stage_mod.build_default_paths(self.repo_root, experiments_root=experiments_dir)
        if freeze_manifest_path is not None:
            paths.freeze_manifest_path = freeze_manifest_path
        return paths

    def test_registered_logical_plan_exact_63_and_no_64th(self):
        plan = self.stage_mod.build_registered_logical_plan(self.default_paths, self.config)
        self.stage_mod.assert_registered_plan(self.default_paths, self.config, plan)

        keys = [entry["logical_key"] for entry in plan]
        self.assertEqual(len(keys), 63)
        self.assertEqual(len(set(keys)), 63)
        self.assertNotIn("registered_stage_a:V3-21:4", keys)
        self.assertEqual(keys[0], "registered_stage_a:V3-01:1")
        self.assertEqual(keys[-1], "registered_stage_a:V3-21:3")

    def test_exactly_three_replicates_per_item(self):
        plan = self.stage_mod.build_registered_logical_plan(self.default_paths, self.config)
        per_item: dict[str, int] = {}
        for row in plan:
            per_item[row["item_id"]] = per_item.get(row["item_id"], 0) + 1
        self.assertEqual(len(per_item), 21)
        self.assertTrue(all(count == 3 for count in per_item.values()))

    def test_registered_plan_ignores_dev_attempt_override(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            result = self.stage_mod.run_mock_collection(
                paths,
                self.config,
                experiment_id="T_DEV_OVERRIDE",
                strict_freeze=True,
                dev_attempts_override=99,
            )
            manifest = result["terminal_manifest"]
            self.assertEqual(manifest["planned_logical_ratings"], 63)
            self.assertEqual(manifest["maximum_permitted_attempts_per_logical_rating"], 3)
            self.assertTrue(result["dev_attempts_override_ignored"])

    def test_retry_records_attached_to_single_logical_key(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            exp_id = "T_RETRY_ATTACH"
            result = self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)
            schedule = set(result["retry_schedule_keys"])
            attempts = read_jsonl(Path(result["experiment_dir"]) / "logical_results.jsonl")
            by_key = {row["logical_key"]: row for row in attempts}
            self.assertEqual(len(by_key), 63)

            state = read_json(Path(result["experiment_dir"]) / "logical_state.json")
            for key in schedule:
                entry = state[key]
                self.assertGreaterEqual(len(entry["attempt_files"]), 2)
                self.assertEqual(entry["terminal_status"], "TERMINAL_VALID")

    def test_attempt_accounting_and_maximum_limits(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            result = self.stage_mod.run_mock_collection(paths, self.config, "T_ACCOUNT", strict_freeze=True)
            manifest = result["terminal_manifest"]

            self.assertEqual(manifest["first_attempts"] + manifest["retry_attempts"], manifest["total_api_attempts"])
            self.assertLessEqual(manifest["total_api_attempts"], 189)
            self.assertEqual(manifest["logical_ratings_completed"], 63)
            self.assertEqual(manifest["logical_ratings_valid"], 63)
            self.assertEqual(manifest["logical_ratings_invalid_terminal"], 0)
            self.assertEqual(manifest["logical_ratings_failed_terminal"], 0)

    def test_metadata_non_leakage_in_requests(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            exp_id = "T_NO_LEAK"
            self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)

            request_path = Path(td) / exp_id / "requests.jsonl"
            payload_text = request_path.read_text(encoding="utf-8")
            prompt_text = self.default_paths.prompt_path.read_text(encoding="utf-8")

            for forbidden in self.stage_mod.FORBIDDEN_METADATA_FIELDS:
                self.assertNotIn(forbidden, payload_text)
                self.assertNotIn(forbidden, prompt_text)

    def test_raw_attempt_immutability_and_resume_behavior(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            exp_id = "T_RESUME"
            first = self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)
            exp_dir = Path(first["experiment_dir"])

            attempt_file = exp_dir / "attempts" / "attempt_000001.json"
            before_text = attempt_file.read_text(encoding="utf-8")

            state_path = exp_dir / "logical_state.json"
            state = read_json(state_path)
            target_key = sorted(state.keys())[0]
            unaffected_key = sorted(state.keys())[1]
            unaffected_count = len(state[unaffected_key]["attempt_files"])

            state[target_key]["terminal_status"] = ""
            state[target_key]["final_parsed_response"] = None
            state_path.write_text(json.dumps(state, indent=2), encoding="utf-8")

            second = self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)
            state_after = read_json(state_path)

            self.assertEqual(attempt_file.read_text(encoding="utf-8"), before_text)
            self.assertEqual(len(state_after[unaffected_key]["attempt_files"]), unaffected_count)
            self.assertEqual(state_after[target_key]["terminal_status"], "TERMINAL_VALID")
            self.assertGreaterEqual(len(state_after[target_key]["attempt_files"]), len(state[target_key]["attempt_files"]))
            self.assertEqual(second["terminal_manifest"]["logical_ratings_completed"], 63)

    def test_schema_and_unknown_property_rejection(self):
        valid = {
            "item_id": "X",
            "evaluated_entity": "e",
            "relevant_target": "t",
            "intended_purpose": "p",
            "domain": "d",
            "target_scope": "s",
            "target_contestability": "contestable",
            "choice_bearer": "b",
            "choice_scope": "c",
            "C_scores": {k: 5 for k in self.stage_mod.EIGHT_C_KEYS},
            "goodness": 5,
            "contradictions": {k: 1 for k in self.stage_mod.CONTRADICTION_KEYS},
            "notes": "ok",
        }
        self.schema_mod.validate_rating_like_schema(valid)
        bad = dict(valid)
        bad["unknown_key"] = "no"
        with self.assertRaises(ValueError):
            self.schema_mod.validate_rating_like_schema(bad)

    def test_freeze_hash_mismatch_blocks_execution(self):
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            bad_manifest = td_path / "bad_freeze.yaml"
            manifest = read_json(self.default_paths.freeze_manifest_path)
            manifest["frozen_hashes"]["items_csv"] = "0" * 64
            bad_manifest.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

            paths = self.make_paths(td_path / "experiments", freeze_manifest_path=bad_manifest)
            with self.assertRaises(ValueError):
                self.stage_mod.run_mock_collection(paths, self.config, "T_BAD_FREEZE", strict_freeze=True)

    def test_validate_seal_verify_and_report(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            exp_id = "T_SEAL"

            self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)
            validation = self.stage_mod.validate_experiment(paths, self.config, exp_id)
            self.assertEqual(validation["valid_logical_ratings"], 63)

            seal = self.stage_mod.seal_experiment(paths, self.config, exp_id)
            self.assertTrue(Path(seal["seal_manifest"]).exists())

            verify = self.stage_mod.seal_experiment(paths, self.config, exp_id, verify_only=True)
            self.assertTrue(verify["verified"])

            report = self.stage_mod.build_engineering_report(paths, self.config, exp_id)
            self.assertIn("synthetic engineering outputs", report["synthetic_disclaimer"].lower())

    def test_no_network_access_required_in_mock_mode(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self.make_paths(Path(td))
            exp_id = "T_NONET"

            original_create_connection = socket.create_connection

            def blocked(*args, **kwargs):
                raise RuntimeError("network disabled in test")

            socket.create_connection = blocked
            try:
                result = self.stage_mod.run_mock_collection(paths, self.config, exp_id, strict_freeze=True)
            finally:
                socket.create_connection = original_create_connection

            self.assertEqual(result["terminal_manifest"]["logical_ratings_valid"], 63)


if __name__ == "__main__":
    unittest.main()