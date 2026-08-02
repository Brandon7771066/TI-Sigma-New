from __future__ import annotations

import hashlib
import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path


def import_module(module_path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, module_path)
    module = importlib.util.module_from_spec(spec)
    assert spec is not None and spec.loader is not None
    spec.loader.exec_module(module)
    return module


class IngestionInfrastructureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo_root = Path(__file__).resolve().parents[3]
        cls.pilot_root = cls.repo_root / "experiments" / "eight_c_goodness_pilot"
        cls.manifest_path = cls.pilot_root / "docs" / "provenance" / "source_import_manifest.yaml"
        cls.canonical_path = cls.repo_root / "docs" / "ti_sigma_framework" / "canonical_definitions.md"

        cls.validate_mod = import_module(
            cls.pilot_root / "scripts" / "validate_source_imports.py", "validate_source_imports"
        )
        cls.index_mod = import_module(
            cls.pilot_root / "scripts" / "index_framework_sources.py", "index_framework_sources"
        )

        _, cls.manifest_entries = cls.validate_mod.load_manifest(cls.manifest_path)

    def flattened_manifest_files(self):
        flattened = []
        for entry in self.manifest_entries:
            for file_entry in self.validate_mod.iter_expected_files(entry):
                flattened.append((entry, file_entry))
        return flattened

    def test_manifest_loads(self):
        self.assertGreater(len(self.manifest_entries), 0)

    def test_source_ids_are_unique(self):
        ids = [entry["source_id"] for entry in self.manifest_entries]
        self.assertEqual(len(ids), len(set(ids)))

    def test_expected_filenames_are_unique(self):
        names = [file_entry["expected_filename"] for _, file_entry in self.flattened_manifest_files()]
        self.assertEqual(len(names), len(set(names)))

    def test_import_destinations_are_unique(self):
        destinations = [file_entry["import_destination"] for _, file_entry in self.flattened_manifest_files()]
        self.assertEqual(len(destinations), len(set(destinations)))

    def test_allowed_status_values(self):
        allowed_group_status = {"pending", "RECOVERED_VERBATIM"}
        allowed_review_status = {"NOT_RECEIVED", "READY_FOR_INDEXING"}
        for entry in self.manifest_entries:
            self.assertIn(entry.get("content_status", ""), allowed_group_status)
            self.assertIn(entry.get("review_status", ""), allowed_review_status)
            for file_entry in self.validate_mod.iter_expected_files(entry):
                self.assertIn(file_entry.get("content_status", ""), {"pending"})
                self.assertIn(file_entry.get("review_status", ""), {"NOT_RECEIVED"})

    def test_segmented_sources_declared(self):
        segmented_ids = {entry["source_id"] for entry in self.manifest_entries if entry.get("supports_segmented_imports")}
        self.assertIn("SRC-004", segmented_ids)
        self.assertIn("SRC-005", segmented_ids)

    def test_duplicate_hash_detection(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            d = root / "experiments" / "eight_c_goodness_pilot" / "docs" / "framework_sources" / "inbox"
            d.mkdir(parents=True, exist_ok=True)

            f1 = d / "SRC-001_alpha.md"
            f2 = d / "SRC-002_beta.md"
            same = "same-content-" * 4
            f1.write_text(same, encoding="utf-8")
            f2.write_text(same, encoding="utf-8")

            e1 = {
                "source_id": "SRC-001",
                "source_name": "A",
                "required": True,
                "reconstruction_allowed": True,
                "verbatim_recovery_required": False,
                "received": True,
                "content_status": "pending",
                "review_status": "NOT_RECEIVED",
                "supports_segmented_imports": False,
                "segment_filename_regex": "^SRC-001_alpha\\.md$",
                "files": [
                    {
                        "expected_filename": f1.name,
                        "import_destination": str(f1.relative_to(root)).replace("\\", "/"),
                        "part_number": 1,
                    }
                ],
            }
            e2 = {
                "source_id": "SRC-002",
                "source_name": "B",
                "required": True,
                "reconstruction_allowed": True,
                "verbatim_recovery_required": False,
                "received": True,
                "content_status": "pending",
                "review_status": "NOT_RECEIVED",
                "supports_segmented_imports": False,
                "segment_filename_regex": "^SRC-002_beta\\.md$",
                "files": [
                    {
                        "expected_filename": f2.name,
                        "import_destination": str(f2.relative_to(root)).replace("\\", "/"),
                        "part_number": 1,
                    }
                ],
            }

            r1 = self.validate_mod.classify(e1, root)
            r2 = self.validate_mod.classify(e2, root)
            self.validate_mod.apply_duplicate_detection([r1, r2])
            self.assertEqual(r1["status"], "DUPLICATE_CONTENT")
            self.assertEqual(r2["status"], "DUPLICATE_CONTENT")

    def test_empty_file_detection(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            d = root / "experiments" / "eight_c_goodness_pilot" / "docs" / "framework_sources" / "inbox"
            d.mkdir(parents=True, exist_ok=True)
            target = d / "SRC-001_alpha.md"
            target.write_text("", encoding="utf-8")

            entry = {
                "source_id": "SRC-001",
                "source_name": "A",
                "required": True,
                "reconstruction_allowed": True,
                "verbatim_recovery_required": False,
                "supports_segmented_imports": False,
                "segment_filename_regex": "^SRC-001_alpha\\.md$",
                "files": [{"expected_filename": target.name, "import_destination": str(target.relative_to(root)).replace("\\", "/") }],
            }
            result = self.validate_mod.classify(entry, root)
            self.assertEqual(result["status"], "EMPTY")

    def test_wrong_name_detection(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            d = root / "experiments" / "eight_c_goodness_pilot" / "docs" / "framework_sources" / "inbox"
            d.mkdir(parents=True, exist_ok=True)
            wrong = d / "SRC-001_unexpected_name.md"
            wrong.write_text("non-empty content for test", encoding="utf-8")
            expected = d / "SRC-001_expected_name.md"
            entry = {
                "source_id": "SRC-001",
                "source_name": "A",
                "required": True,
                "reconstruction_allowed": True,
                "verbatim_recovery_required": False,
                "supports_segmented_imports": False,
                "segment_filename_regex": "^SRC-001_expected_name\\.md$",
                "files": [{"expected_filename": expected.name, "import_destination": str(expected.relative_to(root)).replace("\\", "/") }],
            }
            result = self.validate_mod.classify(entry, root)
            self.assertEqual(result["status"], "INVALID_FILENAME")

    def test_passage_extraction_preserves_exact_text(self):
        lines = [
            "# Heading",
            "User: A line about GILE",
            "Second line with Concreteness",
            "",
            "Assistant: Closing line",
        ]
        passages = self.index_mod.build_passages(lines)
        self.assertEqual(passages[0][0], 1)
        self.assertEqual(passages[0][1], 3)
        self.assertEqual(passages[0][2], "# Heading\nUser: A line about GILE\nSecond line with Concreteness")

    def test_speaker_and_revision_detection(self):
        lines = [
            "User: Actually, Concreteness belongs to GILE and instantiation belongs to HEM.",
            "",
        ]
        _, speaker_at, _ = self.index_mod.annotate_lines(lines)
        speakers = self.index_mod.detect_speakers(speaker_at, 1, 1)
        self.assertEqual(speakers, ["USER"])
        self.assertEqual(self.index_mod.derive_authorship_status(speakers), "USER_AUTHORED")
        self.assertEqual(self.index_mod.derive_user_approval_status(lines[0], "USER"), "REJECTED_OR_CORRECTED")
        flags = self.index_mod.detect_candidate_flags(lines[0])
        self.assertIn("POTENTIAL_REVISION", flags)
        self.assertIn("CATEGORY_BOUNDARY_UPDATE", flags)

    def test_import_scripts_do_not_modify_canonical_files(self):
        before = hashlib.sha256(self.canonical_path.read_bytes()).hexdigest()
        subprocess.run(
            ["python", "experiments/eight_c_goodness_pilot/scripts/validate_source_imports.py"],
            cwd=self.repo_root,
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["python", "experiments/eight_c_goodness_pilot/scripts/index_framework_sources.py"],
            cwd=self.repo_root,
            check=True,
            capture_output=True,
            text=True,
        )
        after = hashlib.sha256(self.canonical_path.read_bytes()).hexdigest()
        self.assertEqual(before, after)

    def test_concreteness_seed_matches_canonical_definition(self):
        canonical = self.canonical_path.read_text(encoding="utf-8")
        canonical_sentence = (
            "> **Concreteness is the degree of tangibility or determinate intelligibility of the evaluated entity: "
            "how readily it can be understood, represented, or operationally grasped with minimal fuzziness, "
            "vagueness, or ambiguity.**"
        )
        definition = (
            "The degree of tangibility or determinate intelligibility of the evaluated entity: "
            "how readily it can be understood, represented, or operationally grasped with minimal fuzziness, "
            "vagueness, or ambiguity."
        )
        self.assertIn(canonical_sentence, canonical)
        definition_history = (self.pilot_root / "docs" / "provenance" / "definition_history.csv").read_text(encoding="utf-8")
        self.assertIn(definition, definition_history)


if __name__ == "__main__":
    unittest.main()
