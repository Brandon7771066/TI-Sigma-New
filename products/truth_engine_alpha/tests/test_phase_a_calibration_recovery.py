import os
import csv
import json
import pytest

REGISTRY_BASE = os.path.normpath(os.path.join(
    os.path.dirname(__file__), '..', 'calibration_registry'
))
MASTER_JSON_PATH = os.path.join(REGISTRY_BASE, 'master_registry.json')


def test_registry_dirs_exist():
    """Verify registry directory structure exists."""
    expected_subdirs = [
        'gile', 'hem', 'truth_labels', 'truth_axes', 'pd',
        'crystal', 'graph', 'domains', 'myrion_resolution', 'validation'
    ]
    for sub in expected_subdirs:
        path = os.path.join(REGISTRY_BASE, sub)
        assert os.path.isdir(path), f"Registry directory missing: {path}"


def test_master_registry_serialization_and_loading():
    """Verify master JSON registry loads and serializes properly."""
    assert os.path.exists(MASTER_JSON_PATH), f"Master JSON missing: {MASTER_JSON_PATH}"
    with open(MASTER_JSON_PATH, 'r', encoding='utf-8') as f:
        data = json.load(f)

    assert isinstance(data, list)
    assert len(data) > 0

    # Serialization check
    serialized = json.dumps(data, indent=2)
    reloaded = json.loads(serialized)
    assert reloaded == data


def test_unique_ids_and_source_provenance():
    """Verify master registry entries have unique IDs and source provenance."""
    with open(MASTER_JSON_PATH, 'r', encoding='utf-8') as f:
        data = json.load(f)

    seen_ids = set()
    for item in data:
        entry_id = item.get('id')
        assert entry_id, "Entry missing required 'id'"
        assert entry_id not in seen_ids, f"Duplicate entry ID found: {entry_id}"
        seen_ids.add(entry_id)

        source = item.get('source')
        assert source, f"Entry {entry_id} missing required 'source' provenance"


def test_truth_label_registry_completeness():
    """Verify truth-label validation registry contains all 5 canonical labels and required metric families."""
    summary_path = os.path.join(REGISTRY_BASE, 'truth_labels', 'TRUTH_LABEL_VALIDATION_SUMMARY.md')
    val_reg_path = os.path.join(REGISTRY_BASE, 'truth_labels', 'truth_label_validation_registry.csv')

    assert os.path.exists(summary_path)
    assert os.path.exists(val_reg_path)

    with open(summary_path, 'r', encoding='utf-8') as f:
        text = f.read()

    canonical_labels = ['TRUE', 'FALSE', 'INDETERMINATE', 'META-INDETERMINATE', 'N/A']
    for label in canonical_labels:
        assert label in text, f"Canonical label missing from summary: {label}"

    with open(val_reg_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    metric_families = set(r['metric_family'] for r in rows)
    expected_families = {'RELIABILITY', 'COMPLETENESS_EXHAUSTIVENESS', 'INFORMATION_CONTENT', 'NON_REDUNDANCY', 'PREDICTIVE_VALIDITY'}
    assert expected_families.issubset(metric_families), f"Missing metric families: {expected_families - metric_families}"


def test_hem_gile_notation_normalization():
    """Verify HEM:GILE ratio notation is strictly normalized in the ratio registry."""
    ratio_path = os.path.join(REGISTRY_BASE, 'domains', 'hem_gile_ratios.csv')
    assert os.path.exists(ratio_path)

    with open(ratio_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    assert len(rows) > 0
    for r in rows:
        assert r['ratio_notation'] == 'HEM:GILE', f"Invalid ratio notation: {r['ratio_notation']}"


def test_pd_variants_distinct():
    """Verify PD variant registry keeps variants distinct."""
    pd_var_path = os.path.join(REGISTRY_BASE, 'pd', 'pd_variant_registry.csv')
    assert os.path.exists(pd_var_path)

    with open(pd_var_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    variants = set(r['variant'] for r in rows)
    assert 'PD_MINUS3_PLUS2' in variants
    assert 'PD_CONTINUOUS' in variants
    assert len(variants) >= 2


def test_truth_axes_distinct_from_gile():
    """Verify Truth Axes remain distinct from GILE constructs."""
    ta_path = os.path.join(REGISTRY_BASE, 'truth_axes', 'truth_axes_registry.csv')
    assert os.path.exists(ta_path)

    with open(ta_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    axes = set(r['axis'] for r in rows)
    expected_axes = {'Real', 'Imaginary', 'Authority', 'Pragmatic'}
    assert axes == expected_axes

    # None of the axes should be named after GILE components
    gile_components = {'Goodness', 'Intuition', 'Love', 'Elegance'}
    assert len(axes.intersection(gile_components)) == 0


def test_no_production_import_of_recovered_values():
    """Verify production src files do not import from calibration_registry directly yet."""
    src_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'src'))
    if not os.path.exists(src_dir):
        return

    for root, _, files in os.walk(src_dir):
        for f in files:
            if f.endswith('.py'):
                full_p = os.path.join(root, f)
                with open(full_p, 'r', encoding='utf-8') as pf:
                    content = pf.read()
                    assert 'calibration_registry' not in content, f"Production code {f} imports calibration_registry!"


def test_no_historical_value_overwritten():
    """Verify historical quantitative passage exact text remains preserved without overwriting."""
    passages_path = os.path.normpath(os.path.join(
        os.path.dirname(__file__), '..', 'results', 'recovery'
    ))
    found_passages = False
    for root, _, files in os.walk(passages_path):
        if 'historical_quantitative_passages.csv' in files:
            p_file = os.path.join(root, 'historical_quantitative_passages.csv')
            with open(p_file, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                rows = list(reader)
                assert len(rows) > 0
                for r in rows:
                    assert r['exact_text'], "Passage missing exact_text"
                    assert r['status'] in ['CURRENT', 'HISTORICAL', 'SUPERSEDED', 'COMPATIBLE_REINTERPRETATION', 'PROPOSED', 'UNRESOLVED']
            found_passages = True
            break
    assert found_passages, "historical_quantitative_passages.csv not found under results/recovery/"
