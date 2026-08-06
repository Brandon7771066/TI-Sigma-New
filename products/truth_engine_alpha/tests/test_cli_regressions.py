from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from truth_engine.engine import analyze_file


def _pkg_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _env() -> dict[str, str]:
    env = os.environ.copy()
    env["PYTHONPATH"] = str(_pkg_root() / "src")
    return env


def _required_files() -> set[str]:
    return {
        "full_result.json",
        "executive_summary.md",
        "claim_table.csv",
        "citation_audit.csv",
        "contradiction_map.csv",
        "claim_graph.json",
        "claim_graph.graphml",
        "graph_errors.csv",
        "crystal_matrix.csv",
        "crystal_diagnostics.json",
        "scaffolding_analysis.csv",
        "information_gain_actions.csv",
        "corrected_answer_outline.md",
        "limitations.md",
        "demo_provenance.json",
    }


def test_module_cli_help_returns_success():
    result = subprocess.run(
        [sys.executable, "-m", "truth_engine.cli", "--help"],
        cwd=_pkg_root(),
        env=_env(),
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    assert "analyze" in result.stdout


def test_module_cli_analyze_populates_output_folder(tmp_path):
    input_path = tmp_path / "claims.jsonl"
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim one","source_id":"s1","citations":[]}\n'
        '{"claim_id":"c2","verbatim_text":"Claim two","source_id":"s2","citations":["s2"]}\n',
        encoding="utf-8",
    )
    output_dir = tmp_path / "out"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "truth_engine.cli",
            "analyze",
            "--input",
            str(input_path),
            "--output",
            str(output_dir),
            "--mode",
            "standard",
            "--seed",
            "0",
        ],
        cwd=_pkg_root(),
        env=_env(),
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    produced = {p.name for p in output_dir.iterdir() if p.is_file()}
    assert _required_files().issubset(produced)
    assert produced


def test_script_cli_analyze_populates_output_folder(tmp_path):
    input_path = tmp_path / "claims.jsonl"
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim one","source_id":"s1","citations":[]}\n'
        '{"claim_id":"c2","verbatim_text":"Claim two","source_id":"s2","citations":["s2"]}\n',
        encoding="utf-8",
    )
    output_dir = tmp_path / "out_script"
    result = subprocess.run(
        [
            sys.executable,
            "scripts/truth_engine.py",
            "analyze",
            "--input",
            str(input_path),
            "--output",
            str(output_dir),
            "--mode",
            "standard",
            "--seed",
            "0",
        ],
        cwd=_pkg_root(),
        env=_env(),
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    produced = {p.name for p in output_dir.iterdir() if p.is_file()}
    assert _required_files().issubset(produced)
    assert produced


def test_cli_returns_nonzero_for_invalid_input_path(tmp_path):
    output_dir = tmp_path / "out_bad"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "truth_engine.cli",
            "analyze",
            "--input",
            str(tmp_path / "missing_input.jsonl"),
            "--output",
            str(output_dir),
        ],
        cwd=_pkg_root(),
        env=_env(),
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode != 0


def test_citation_status_override_source_found_not_accessed(tmp_path):
    input_path = tmp_path / "claims.jsonl"
    input_path.write_text(
        '{"claim_id":"c1","normalized_claim":"claim","verbatim_text":"claim","source_id":"src_1","conditions":"source_found_not_accessed","citations":["src_1"]}\n',
        encoding="utf-8",
    )
    result = analyze_file(input_path, tmp_path / "out")
    statuses = {row["status"] for row in result["citation_audit"]}
    assert "SOURCE_FOUND_NOT_ACCESSED" in statuses


def test_cli_no_silent_success_with_empty_output(tmp_path):
    input_path = tmp_path / "claims.jsonl"
    input_path.write_text(
        '{"claim_id":"c1","verbatim_text":"Claim one","source_id":"s1","citations":[]}\n',
        encoding="utf-8",
    )
    output_dir = tmp_path / "out_no_silent"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "truth_engine.cli",
            "analyze",
            "--input",
            str(input_path),
            "--output",
            str(output_dir),
        ],
        cwd=_pkg_root(),
        env=_env(),
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    files = [p for p in output_dir.iterdir() if p.is_file()]
    assert len(files) > 0
    payload = json.loads((output_dir / "full_result.json").read_text(encoding="utf-8"))
    assert payload.get("analysis_id")
