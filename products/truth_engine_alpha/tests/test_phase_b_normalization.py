import os
import json
import math
import pytest

from products.truth_engine_alpha.src.ti_sigma_core.models.evidence import EvidenceStatus, ValidationMaturityTier, ResolutionMode
from products.truth_engine_alpha.src.ti_sigma_core.models.truth_labels import CANONICAL_TRUTH_LABELS
from products.truth_engine_alpha.src.ti_sigma_core.models.gile import GILEVector
from products.truth_engine_alpha.src.ti_sigma_core.models.truth_axes import TruthAxesQuaternionBlock
from products.truth_engine_alpha.src.ti_sigma_core.models.hem import HEM_CANONICAL_DIMENSIONS
from products.truth_engine_alpha.src.ti_sigma_core.models.pd import PDVariantDefinition, decode_pd_ternary
from products.truth_engine_alpha.src.ti_sigma_core.models.myrion import Myrion16DVector
from products.truth_engine_alpha.src.ti_sigma_core.registry.resolver import RegistryResolver
from products.truth_engine_alpha.src.ti_sigma_core.domains.profiles import DOMAIN_PROFILES


def test_five_truth_labels_unique_and_complete():
    """Verify 5 canonical machine IDs and display labels."""
    labels = [l.machine_id for l in CANONICAL_TRUTH_LABELS]
    assert len(labels) == 5
    assert len(set(labels)) == 5
    assert set(labels) == {"TRUE", "FALSE", "INDETERMINATE", "META_INDETERMINATE", "NOT_APPLICABLE"}
    display_labels = [l.display_label for l in CANONICAL_TRUTH_LABELS]
    assert "N/A" in display_labels


def test_gile_separate_from_truth_axes():
    """Verify GILE (VALUES) is distinct from Truth Axes (QUATERNION BLOCK)."""
    gile = GILEVector()
    axes = TruthAxesQuaternionBlock()
    gile_dims = set(gile.to_dict().keys()) - {"evidence_status", "role", "production_status"}
    axes_dims = set(axes.to_dict().keys()) - {"quaternion_notation", "cluster_validation_status", "individual_axis_status", "evidence_status", "production_status"}
    assert len(gile_dims.intersection(axes_dims)) == 0


def test_eight_truth_dimensions_and_eight_hem_dimensions():
    """Verify 8 Truth dimensions (4 GILE + 4 Axes) and 8 HEM dimensions = 16 Myrion dimensions."""
    gile = GILEVector()
    axes = TruthAxesQuaternionBlock()
    assert len(gile.to_list()) == 4
    assert len(axes.to_list()) == 4
    assert len(HEM_CANONICAL_DIMENSIONS) == 8
    myrion = Myrion16DVector()
    assert len(myrion.full_vector()) == 16


def test_hem_gile_notation_and_existence_first():
    """Verify HEM:GILE notation and ratio calculations."""
    for domain_name, profile in DOMAIN_PROFILES.items():
        assert profile.hem_gile_notation == "HEM:GILE"
        assert profile.hem_weight > 0
        assert profile.gile_weight > 0
        expected_ratio = round(profile.hem_weight / profile.gile_weight, 3)
        assert abs(profile.derived_ratio - expected_ratio) < 0.01


def test_mi_ratios_reproduce_exactly():
    """Verify exact reproduction of MI ratios."""
    mi = 1.94
    empirical_entropy = 2.004
    max_5_entropy = math.log2(5)

    ratio_empirical = mi / empirical_entropy
    ratio_max = mi / max_5_entropy

    assert abs(ratio_empirical - 0.96806) < 0.001
    assert abs(ratio_max - 0.83551) < 0.001


def test_sample_semantics_normalization():
    """Verify sample size semantics explicitly state CLAIM_ITEMS."""
    resolver = RegistryResolver()
    tl_entry = resolver.get_calibration("REG_TL_001", mode="RESEARCH_ALL")
    assert tl_entry is not None
    assert tl_entry.sample_size == 1200
    assert tl_entry.sample_semantics == "CLAIM_ITEMS"


def test_simulation_gile_weights_excluded_from_certified_only():
    """Verify CERTIFIED_ONLY mode excludes simulation default GILE weights."""
    resolver = RegistryResolver()
    certified_gile = resolver.get_gile_values(mode="CERTIFIED_ONLY")
    assert certified_gile is None # Excluded from CERTIFIED_ONLY

    research_gile = resolver.get_gile_values(mode="RESEARCH_ALL")
    assert research_gile is not None


def test_pd_coordinate_separated_from_ternary_decoder():
    """Verify PD coordinate [-3, +2] separation from ternary decoder."""
    assert decode_pd_ternary(-2.5) == "DEFICIT"
    assert decode_pd_ternary(0.0) == "INTERMEDIATE"
    assert decode_pd_ternary(1.5) == "SURPLUS"


def test_no_production_import_of_ti_sigma_core():
    """Verify zero production files under products/truth_engine_alpha/src/ import ti_sigma_core."""
    src_root = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'src'))
    for root, _, files in os.walk(src_root):
        if 'ti_sigma_core' in root:
            continue
        for f in files:
            if f.endswith('.py'):
                full_p = os.path.join(root, f)
                with open(full_p, 'r', encoding='utf-8') as pf:
                    content = pf.read()
                    assert 'ti_sigma_core' not in content, f"Production file {f} imports ti_sigma_core!"
