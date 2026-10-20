"""Consistency checks for the TI Sigma core definition freeze.

The product-branch calibration schema is not in this tree. These checks
guard the prose freeze: required sources and conflict IDs stay present,
and the simulation weights are not described as universal empirical weights.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = (ROOT / "docs/theory/TI_SIGMA_CORE_SPECIFICATION.md").read_text(encoding="utf-8")
LOG = (ROOT / "docs/theory/TI_SIGMA_DEFINITION_CHANGELOG.md").read_text(encoding="utf-8")
OPEN = (ROOT / "docs/theory/TI_SIGMA_CORE_OPEN_QUESTIONS.md").read_text(encoding="utf-8")


REQUIRED_COMMITS = (
    "f9c08a02",
    "687167ab",
    "b3b2395d",
    "84335786",
    "47cd3cce",
    "b1053224",
)

REQUIRED_CONFLICTS = (
    "CONFLICT-GILE-NAME",
    "CONFLICT-GILE-WEIGHTS",
    "CONFLICT-EIGHT-C",
    "CONFLICT-HEM-DIMS",
    "CONFLICT-HEM-GILE-MAP",
    "CONFLICT-TRUTH-AXES",
    "CONFLICT-NA-PLACEMENT",
    "CONFLICT-TRUTH-LABELS",
    "CONFLICT-INDETERMINATE",
    "CONFLICT-ELEGANCE",
)


def test_spec_cites_the_six_registry_commits():
    for commit in REQUIRED_COMMITS:
        assert commit in SPEC
        assert commit in LOG


def test_conflicts_are_named_and_not_silently_dropped():
    for conflict_id in REQUIRED_CONFLICTS:
        assert conflict_id in SPEC


def test_simulation_weights_stay_simulation_parameters():
    assert "INFERRED_NOT_EXPLICIT" in SPEC
    assert "0.30" in SPEC and "0.25" in SPEC and "0.20" in SPEC
    assert "are not universal empirical weights" in SPEC
    assert "are universal empirical weights" not in SPEC
    assert "SIMULATION_DEFAULT" in SPEC


def test_eight_c_draft_is_not_described_as_validated():
    assert "NEW_CANONICAL_DRAFT" in SPEC
    assert "The Eight-C model is not a validated manifold." in SPEC


def test_hem_gile_bijection_stays_a_claim():
    assert "CONFLICT-HEM-GILE-MAP" in SPEC
    assert "provisionally maintained as a hypothesis" in SPEC
    assert "not a demonstrated bijection" in SPEC or "Not a bijection" in SPEC


def test_open_questions_ask_the_owner_and_do_not_edit_the_registry():
    assert "Decisions still needed" in OPEN
    assert "REG_TL_001" in OPEN
    assert "master_registry_v1.json" in OPEN
    assert "CERTIFIED_EXACT" in OPEN


def test_owner_reading_is_recorded_as_definition_not_measurement():
    assert "0.2.1-draft" in SPEC
    assert "deliberately unclear" in SPEC
    assert "base-5" in SPEC
    assert "two octonions" in SPEC
    assert "string theory" in SPEC
    assert "HYPOTHESIS" in SPEC
    assert "The Eight-C model is not a validated manifold." in SPEC
    assert "0.2.1-draft" in LOG
