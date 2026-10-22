"""Locks the 2026-10-20 Eight-C generator check and weight simulation.

The product-branch calibration schema is not in this tree. These checks
rerun the original Stage A mock functions from commit 58e78046 and the
seeded weight arithmetic, then require the committed JSON to match.
"""

import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "analyses/eight_c_instrument_2026_10_20"
SCRIPT = OUT / "run_eight_c_instrument.py"

_spec = importlib.util.spec_from_file_location("eight_c_instrument_2026_10_20", SCRIPT)
instrument = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(instrument)


def test_committed_results_match_a_fresh_run():
    fresh = instrument.build_report()
    committed = json.loads((OUT / "results.json").read_text(encoding="utf-8"))
    assert committed == fresh
    assert (OUT / "EIGHT_C_INSTRUMENT_REPORT.md").read_text(encoding="utf-8") == instrument.render_markdown(fresh)


def test_stored_mock_matches_the_cli_default_and_not_the_registered_seed():
    mock = json.loads((OUT / "results.json").read_text(encoding="utf-8"))["mock"]
    assert mock["status"] == "REPRODUCIBLE"
    assert mock["empirical_status"] == "ABSENT"
    assert mock["stored_json_matches_cli_default_seed"] is True
    assert mock["stored_json_matches_registered_seed"] is False
    assert mock["base_seed_matching_stored_json"] == "TI_SIGMA_STAGE_A_V3_MOCK"
    assert mock["registered_base_seed"] == "TI_SIGMA_STAGE_A_V3_REGISTERED"
    stored = mock["recomputed_vary_by_attempt_cli_default"]
    assert stored["exact_match_rate"] == 0.0
    assert stored["item_groups"] == 21
    assert stored["attempts_per_item"] == 3
    assert stored["mean_abs_diff"]["goodness"] == 4.031746031746032
    assert mock["fixed_strategy_exact_match_rate"] == 1.0
    assert mock["fixed_strategy_goodness_mad"] == 0.0
    assert mock["choice_fields_excluded_from_hash"] is True
    assert mock["uniform_expectation_score_mad"] == "440/121"
    assert mock["uniform_expectation_contradiction_mad"] == "20/16"
    assert "LFS" in mock["metadata_csv"]


def test_weight_simulation_separates_proportional_duplicate_and_independent():
    weights = json.loads((OUT / "results.json").read_text(encoding="utf-8"))["weights"]
    assert weights["status"] == "REPRODUCIBLE"
    assert weights["class"] == "SIMULATION"
    assert weights["empirical_status"] == "ABSENT"
    assert weights["domain_weights_assigned"] is False
    assert weights["closest_applicability"] == "not scored; no distance was defined"
    assert weights["proportional_all_tau_equal_1"] is True
    assert weights["duplicate_column_max_abs_composite_diff"] == 0
    assert weights["constructed_nonredundant_transfer_tau_b"] == -1.0
    assert weights["independent_fraction_tau_below_1"] == 1.0
    assert weights["independent_mean_kendall_tau_b"] < 0.5
    assert weights["seed"] == 20261020


def test_corpus_balance_disagrees_with_the_item_jsonl():
    corpus = json.loads((OUT / "results.json").read_text(encoding="utf-8"))["corpus"]
    assert corpus["status"] == "INCONSISTENT"
    assert corpus["jsonl_items"] == 21
    assert corpus["jsonl_cluster_roles_complete"] is True
    assert corpus["jsonl_domains"]["science"] == 4
    assert corpus["stored_domains"]["science"] == 5
    assert corpus["jsonl_domains"]["engineering"] == 3
    assert corpus["stored_domains"]["engineering"] == 4
    assert corpus["stored_domain_total"] == 23
    assert corpus["jsonl_scales"]["institutional"] == 6
    assert corpus["stored_scales"]["institutional"] == 5
    assert corpus["jsonl_scales"]["physical"] == 4
    assert corpus["stored_scales"]["physical"] == 5
    assert corpus["domains_match_jsonl"] is False
    assert corpus["scales_match_jsonl"] is False


def test_mock_schema_passes_and_fixed_icc_is_one():
    local = json.loads((OUT / "results.json").read_text(encoding="utf-8"))["local_mock_checks"]
    assert local["class"] == "GENERATOR"
    assert local["empirical_status"] == "ABSENT"
    assert local["schema_records"] == 63
    assert local["schema_failures"] == 0
    assert local["schema_status"] == "REPRODUCIBLE"
    assert local["fixed_strategy_goodness_icc_1_1"] == 1.0
    assert local["fixed_strategy_goodness_icc_2_1"] == 1.0
    assert local["moments"]["goodness"]["n"] == 63
    assert abs(local["icc"]["goodness"]["icc_1_1"]) < 0.5


def test_report_keeps_the_reliability_claim_absent():
    text = (OUT / "EIGHT_C_INSTRUMENT_REPORT.md").read_text(encoding="utf-8")
    payload = json.loads((OUT / "results.json").read_text(encoding="utf-8"))
    assert payload["eight_c_kappa"]["status"] == "ABSENT"
    assert payload["preregistered_discriminations"]["status"] == "PLANNED"
    assert "REPRODUCIBLE" in text
    assert "SIMULATION" in text
    assert "ABSENT" in text
    assert "paid_collection_started" in text
    assert "closest applicability" in text.lower() or "Closest applicability" in text
