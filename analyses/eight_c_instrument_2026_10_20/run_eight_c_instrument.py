"""Eight-C instrument checks, 2026-10-20.

Two checks, both executable without a human rating table.

1. Generator check. Recompute the Stage A v3 mock reproducibility JSON on
   product commit 58e78046 from the original ``build_mock_rating`` and
   ``_compute_reproducibility`` functions. The item text is the plain JSONL
   in that commit. The items CSV and the metadata CSV are Git LFS pointers
   and were not downloaded: the repository LFS budget is exceeded. The hash
   seed is item id, scenario text, attempt index, and base seed. It does not
   include ``choice_bearer`` or ``choice_scope``.

2. Weight check. Seeded arithmetic on synthetic profiles. Proportional
   profiles keep the same ranking under every positive weight vector.
   Independent profiles do not. A duplicated column makes the split of weight
   between the two copies unidentified. This is a simulation. It does not
   assign a domain weight and it does not score closest applicability.

Neither check is an Eight-C kappa, a human reliability study, or a validation
of the Eight-C matrix.
"""

from __future__ import annotations

import hashlib
import importlib
import importlib.util
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

SOURCE_COMMIT = "58e78046101afdd58797e1f369f7b7ae4f204b5b"
SOURCE_PREFIX = "experiments/eight_c_goodness_pilot"
MOCK_SEED = "TI_SIGMA_STAGE_A_V3_MOCK"
REGISTERED_SEED = "TI_SIGMA_STAGE_A_V3_REGISTERED"
ATTEMPTS = 3
WEIGHT_SEED = 20261020
N_ITEMS = 24
N_MATRICES = 200
MAD_MC_SEED = 20261021
N_MC = 20000
CORR_PERM_SEED = 20261022
N_PERM = 5000

EIGHT_C = (
    "coherence",
    "consistency",
    "continuity",
    "concreteness",
    "completion",
    "criticality",
    "closeness",
    "choice",
)

MODULE_FILES = (
    "src/ti_sigma_pipeline/__init__.py",
    "src/ti_sigma_pipeline/contracts.py",
    "src/ti_sigma_pipeline/io.py",
    "src/ti_sigma_pipeline/schema_check.py",
    "src/ti_sigma_pipeline/mock_rater.py",
    "src/ti_sigma_pipeline/pipeline.py",
    "src/ti_sigma_pipeline/stage_a_v3.py",
)

ITEM_JSONL = f"{SOURCE_PREFIX}/data/items/ti_sigma_stage_a_v3_items.jsonl"
STORED_JSON = f"{SOURCE_PREFIX}/results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json"
CORPUS_MD = f"{SOURCE_PREFIX}/results/reports/ti_sigma_stage_a_v3_corpus_balance.md"
ICC_MC_SEED = 20261023
N_ICC_MC = 2000
ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = Path(__file__).resolve().parent


def _git_bytes(spec: str) -> bytes:
    try:
        return subprocess.check_output(["git", "show", spec], stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as exc:
        raise RuntimeError(
            f"git show {spec} failed. Fetch origin/product/truth-engine-alpha-1.1 "
            f"so commit {SOURCE_COMMIT} is present."
        ) from exc


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _load_original_pipeline():
    """Import the product-commit pipeline without copying it into this branch."""
    if "ti_sigma_pipeline" in sys.modules and hasattr(sys.modules["ti_sigma_pipeline"], "_eight_c_source_commit"):
        package = sys.modules["ti_sigma_pipeline"]
        return package.mock_rater, package.pipeline
    scratch = Path(tempfile.mkdtemp(prefix="eight_c_source_"))
    package_dir = scratch / "ti_sigma_pipeline"
    package_dir.mkdir()
    for relative in MODULE_FILES:
        name = relative.split("ti_sigma_pipeline/", 1)[1]
        target = package_dir / name
        target.write_bytes(_git_bytes(f"{SOURCE_COMMIT}:{SOURCE_PREFIX}/{relative}"))
    sys.path.insert(0, str(scratch))
    package = importlib.import_module("ti_sigma_pipeline")
    package._eight_c_source_commit = SOURCE_COMMIT
    return package.mock_rater, package.pipeline


def _items() -> list[dict]:
    raw = _git_bytes(f"{SOURCE_COMMIT}:{ITEM_JSONL}").decode("utf-8")
    items = [json.loads(line) for line in raw.splitlines() if line.strip()]
    if len(items) != 21:
        raise RuntimeError(f"expected 21 items, found {len(items)}")
    for item in items:
        # Constant stand-in. The LFS metadata CSV was not readable. These two
        # fields are copied onto the rating record and are not hashed.
        item["choice_bearer"] = "LFS_METADATA_NOT_READ"
        item["choice_scope"] = "LFS_METADATA_NOT_READ"
    return items


def _stored_metrics() -> dict:
    return json.loads(_git_bytes(f"{SOURCE_COMMIT}:{STORED_JSON}").decode("utf-8"))


def _records(mock_rater, items: list[dict], seed_strategy: str, base_seed: str) -> list[dict]:
    records = []
    for attempt in range(1, ATTEMPTS + 1):
        for item in items:
            records.append(
                mock_rater.build_mock_rating(
                    item,
                    attempt_index=attempt,
                    seed_strategy=seed_strategy,
                    base_seed=base_seed,
                )
            )
    return records


def _metrics_for(mock_rater, pipeline, items, seed_strategy: str, base_seed: str) -> dict:
    records = _records(mock_rater, items, seed_strategy, base_seed)
    return pipeline._compute_reproducibility(records, ATTEMPTS)


def _same_metrics(found: dict, expected: dict) -> bool:
    return found == expected


def _pearson(xs: list[float], ys: list[float]) -> float:
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den_x = sum((x - mean_x) ** 2 for x in xs) ** 0.5
    den_y = sum((y - mean_y) ** 2 for y in ys) ** 0.5
    if den_x == 0 or den_y == 0:
        return 0.0
    return num / (den_x * den_y)


def _goodness_association(records: list[dict]) -> dict:
    goodness = [float(record["goodness"]) for record in records]
    means = [sum(record["C_scores"][name] for name in EIGHT_C) / 8 for record in records]
    observed = _pearson(goodness, means)
    rng = random.Random(CORR_PERM_SEED)
    hits = 0
    for _ in range(N_PERM):
        shuffled = goodness[:]
        rng.shuffle(shuffled)
        if abs(_pearson(shuffled, means)) >= abs(observed):
            hits += 1
    return {
        "n_mock_rows": len(records),
        "pearson_r_goodness_vs_mean_c": observed,
        "permutation_draws": N_PERM,
        "permutation_seed": CORR_PERM_SEED,
        "two_sided_permutation_p": (hits + 1) / (N_PERM + 1),
        "generator_fact": (
            "build_mock_rating draws goodness from sha256(seed|goodness) and each C "
            "from sha256(seed|name). Goodness is a separate bucket, not a function of the eight Cs."
        ),
    }


def _expected_uniform_mad(maximum: int) -> str:
    """Exact E|X-Y| for two independent uniform draws on {0, ..., maximum}."""
    n = maximum + 1
    total = sum(distance * (n - distance) for distance in range(1, maximum + 1))
    numerator = 2 * total
    denominator = n * n
    return f"{numerator}/{denominator}"


def _one_mean_mad(rng: random.Random, n_items: int, maximum: int) -> float:
    total = 0.0
    for _ in range(n_items):
        draws = [rng.randrange(maximum + 1) for _ in range(3)]
        total += (abs(draws[0] - draws[1]) + abs(draws[0] - draws[2]) + abs(draws[1] - draws[2])) / 3
    return total / n_items


def _mad_reference(observed: float, maximum: int) -> dict:
    rng = random.Random(MAD_MC_SEED if maximum == 10 else MAD_MC_SEED + maximum)
    samples = [_one_mean_mad(rng, 21, maximum) for _ in range(N_MC)]
    center = sum(samples) / len(samples)
    distance = abs(observed - center)
    as_extreme = sum(abs(sample - center) >= distance - 1e-15 for sample in samples)
    return {
        "draws": N_MC,
        "seed": MAD_MC_SEED if maximum == 10 else MAD_MC_SEED + maximum,
        "monte_carlo_mean": center,
        "two_sided_tail": as_extreme / N_MC,
        "observed": observed,
    }


def _choice_fields_do_not_enter_scores(mock_rater, item: dict) -> bool:
    left = dict(item)
    right = dict(item)
    left["choice_bearer"] = "alpha"
    left["choice_scope"] = "local"
    right["choice_bearer"] = "beta"
    right["choice_scope"] = "global"
    a = mock_rater.build_mock_rating(left, attempt_index=1, seed_strategy="vary_by_attempt", base_seed=MOCK_SEED)
    b = mock_rater.build_mock_rating(right, attempt_index=1, seed_strategy="vary_by_attempt", base_seed=MOCK_SEED)
    return a["C_scores"] == b["C_scores"] and a["goodness"] == b["goodness"] and a["contradictions"] == b["contradictions"]


def recompute_mock() -> dict:
    mock_rater, pipeline = _load_original_pipeline()
    items = _items()
    stored = _stored_metrics()
    vary_mock = _metrics_for(mock_rater, pipeline, items, "vary_by_attempt", MOCK_SEED)
    vary_registered = _metrics_for(mock_rater, pipeline, items, "vary_by_attempt", REGISTERED_SEED)
    fixed_mock = _metrics_for(mock_rater, pipeline, items, "fixed", MOCK_SEED)
    records = _records(mock_rater, items, "vary_by_attempt", MOCK_SEED)
    c_values = list(vary_mock["mean_abs_diff"]["C_scores"].values())
    x_values = list(vary_mock["mean_abs_diff"]["contradictions"].values())
    mean_c = sum(c_values) / len(c_values)
    mean_x = sum(x_values) / len(x_values)
    file_hashes = {
        relative: _sha256(_git_bytes(f"{SOURCE_COMMIT}:{SOURCE_PREFIX}/{relative}"))
        for relative in (
            "src/ti_sigma_pipeline/mock_rater.py",
            "src/ti_sigma_pipeline/pipeline.py",
            "src/ti_sigma_pipeline/contracts.py",
            "data/items/ti_sigma_stage_a_v3_items.jsonl",
            "results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json",
            "config/stage_a_v3.yaml",
        )
    }
    return {
        "source_commit": SOURCE_COMMIT,
        "instrument": "stage_a_v3_mock_hash",
        "status": "REPRODUCIBLE",
        "empirical_status": "ABSENT",
        "paid_collection_started": False,
        "definitions_status": "NEW_CANONICAL_DRAFT",
        "seed_strategy_stored_run": "vary_by_attempt",
        "base_seed_matching_stored_json": MOCK_SEED,
        "registered_base_seed": REGISTERED_SEED,
        "stored_json_matches_cli_default_seed": _same_metrics(vary_mock, stored),
        "stored_json_matches_registered_seed": _same_metrics(vary_registered, stored),
        "recomputed_vary_by_attempt_cli_default": vary_mock,
        "recomputed_vary_by_attempt_registered_seed": vary_registered,
        "recomputed_fixed_cli_default": fixed_mock,
        "fixed_strategy_exact_match_rate": fixed_mock["exact_match_rate"],
        "fixed_strategy_goodness_mad": fixed_mock["mean_abs_diff"]["goodness"],
        "choice_fields_excluded_from_hash": _choice_fields_do_not_enter_scores(mock_rater, items[0]),
        "metadata_csv": (
            "Git LFS oid sha256:f5f3a276063af7f895ac4f61c49c349bb02cfbcc50327a9bd69a7819221f82e1 "
            "size 4549. Not downloaded. Repository LFS budget exceeded."
        ),
        "items_csv": (
            "Git LFS oid sha256:050b5590cf83bb8dca1cb0825141a7eac09b25771efb5b60a329a259c45464b9 "
            "size 10758. Not downloaded. Item text was read from the JSONL."
        ),
        "source_file_sha256": file_hashes,
        "uniform_expectation_score_mad": _expected_uniform_mad(10),
        "uniform_expectation_contradiction_mad": _expected_uniform_mad(3),
        "mean_of_eight_c_mads": mean_c,
        "mean_of_contradiction_mads": mean_x,
        "goodness_mad_versus_uniform": _mad_reference(vary_mock["mean_abs_diff"]["goodness"], 10),
        "mean_c_mad_versus_uniform": _mad_reference(mean_c, 10),
        "mean_contradiction_mad_versus_uniform": _mad_reference(mean_x, 3),
        "goodness_versus_mean_c": _goodness_association(records),
        "interpretation": (
            "exact_match_rate 0.0 is the vary_by_attempt hash on this item file. "
            "The fixed strategy on the same items returns exact_match_rate 1.0 and MAD 0. "
            "The stored JSON is the CLI default seed, not the registered config seed."
        ),
    }


def _kendall_tau_b(xs: list[float], ys: list[float]) -> float | None:
    n = len(xs)
    n0 = n * (n - 1) // 2
    nc = nd = n1 = n2 = 0
    for i in range(n):
        for j in range(i + 1, n):
            dx = xs[i] - xs[j]
            dy = ys[i] - ys[j]
            if dx == 0:
                n1 += 1
            if dy == 0:
                n2 += 1
            if dx != 0 and dy != 0:
                if (dx > 0) == (dy > 0):
                    nc += 1
                else:
                    nd += 1
    left = n0 - n1
    right = n0 - n2
    if left == 0 or right == 0:
        return None
    return (nc - nd) / (left * right) ** 0.5


def _independent_matrix(rng: random.Random) -> list[list[int]]:
    return [[rng.randrange(11) for _ in EIGHT_C] for _ in range(N_ITEMS)]


def _proportional_matrix() -> list[list[int]]:
    return [[item] * len(EIGHT_C) for item in range(N_ITEMS)]


def _duplicate_choice(matrix: list[list[int]]) -> list[list[int]]:
    copied = [row[:] for row in matrix]
    for row in copied:
        row[7] = row[0]
    return copied


def _dot(row: list[int], weights: list[int]) -> int:
    return sum(value * weight for value, weight in zip(row, weights))


def _column_scores(matrix: list[list[int]], weights: list[int]) -> list[int]:
    return [_dot(row, weights) for row in matrix]


def _sample_sd(values: list[float]) -> float:
    n = len(values)
    mean = sum(values) / n
    return (sum((value - mean) ** 2 for value in values) / (n - 1)) ** 0.5


def _icc_from_groups(groups: list[list[float]]) -> dict:
    """Shrout-Fleiss ICC(1,1) and two-way absolute ICC(2,1).

    Rows are items. Columns are attempt indices. Attempt index is a hash input,
    not a human rater.
    """
    n = len(groups)
    k = len(groups[0])
    grand = sum(sum(group) for group in groups) / (n * k)
    row_means = [sum(group) / k for group in groups]
    col_means = [sum(groups[i][j] for i in range(n)) / n for j in range(k)]
    ss_rows = k * sum((mean - grand) ** 2 for mean in row_means)
    ss_cols = n * sum((mean - grand) ** 2 for mean in col_means)
    ss_total = sum((value - grand) ** 2 for group in groups for value in group)
    ss_error = ss_total - ss_rows - ss_cols
    ms_rows = ss_rows / (n - 1)
    ms_within = (ss_total - ss_rows) / (n * (k - 1))
    ms_cols = ss_cols / (k - 1)
    ms_error = ss_error / ((n - 1) * (k - 1))
    if ms_within == 0:
        icc_1 = 1.0
    else:
        icc_1 = (ms_rows - ms_within) / (ms_rows + (k - 1) * ms_within)
    if ms_error == 0 and ms_cols == 0:
        icc_2 = 1.0
    else:
        icc_2 = (ms_rows - ms_error) / (ms_rows + (k - 1) * ms_error + k * (ms_cols - ms_error) / n)
    return {"icc_1_1": icc_1, "icc_2_1": icc_2, "n_items": n, "k_attempts": k}


def _groups_for(records: list[dict], key: str) -> list[list[float]]:
    by_item: dict[str, list[float]] = {}
    for record in records:
        if key == "goodness":
            value = float(record["goodness"])
        else:
            value = float(record["C_scores"][key])
        by_item.setdefault(record["item_id"], []).append(value)
    return [by_item[item_id] for item_id in sorted(by_item)]


def _icc_reference(observed: float) -> dict:
    rng = random.Random(ICC_MC_SEED)
    samples = []
    for _ in range(N_ICC_MC):
        groups = [[rng.randrange(11) for _ in range(3)] for _ in range(21)]
        samples.append(_icc_from_groups(groups)["icc_1_1"])
    center = sum(samples) / len(samples)
    distance = abs(observed - center)
    as_extreme = sum(abs(sample - center) >= distance - 1e-15 for sample in samples)
    return {
        "draws": N_ICC_MC,
        "seed": ICC_MC_SEED,
        "monte_carlo_mean": center,
        "two_sided_tail": as_extreme / N_ICC_MC,
        "null": "21 items, 3 independent uniform{0..10} attempts, ICC(1,1)",
    }


def local_planned_mock_checks() -> dict:
    """Primary analyses that the preregistration can run on the mock alone."""
    mock_rater, _pipeline = _load_original_pipeline()
    schema_mod = sys.modules["ti_sigma_pipeline"].schema_check
    items = _items()
    records = _records(mock_rater, items, "vary_by_attempt", MOCK_SEED)
    fixed = _records(mock_rater, items, "fixed", MOCK_SEED)
    failures = []
    for record in records:
        try:
            schema_mod.validate_rating_like_schema(record)
        except ValueError as exc:
            failures.append(str(exc))
    moments = {}
    icc = {}
    for key in ("goodness",) + EIGHT_C:
        values = [record["goodness"] if key == "goodness" else record["C_scores"][key] for record in records]
        moments[key] = {
            "n": len(values),
            "mean": sum(values) / len(values),
            "sample_sd": _sample_sd([float(value) for value in values]),
            "min": min(values),
            "max": max(values),
        }
        icc[key] = _icc_from_groups(_groups_for(records, key))
    fixed_icc = _icc_from_groups(_groups_for(fixed, "goodness"))
    return {
        "instrument": "stage_a_v3_mock_schema_moments_icc",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "schema_records": len(records),
        "schema_failures": len(failures),
        "schema_status": "REPRODUCIBLE" if not failures else "INCONSISTENT",
        "moments": moments,
        "icc": icc,
        "fixed_strategy_goodness_icc_1_1": fixed_icc["icc_1_1"],
        "fixed_strategy_goodness_icc_2_1": fixed_icc["icc_2_1"],
        "goodness_icc_1_1_versus_uniform": _icc_reference(icc["goodness"]["icc_1_1"]),
        "uniform_mean_on_0_to_10": 5.0,
    }


def _section_counts(text: str, heading: str, following: str) -> dict[str, int]:
    start = text.index(heading)
    end = text.index(following, start)
    counts = {}
    for line in text[start:end].splitlines():
        if not line.startswith("- "):
            continue
        name, value = line[2:].rsplit(": ", 1)
        counts[name] = int(value)
    return counts


def corpus_balance() -> dict:
    """Compare the stored balance report with the readable item JSONL."""
    raw = _git_bytes(f"{SOURCE_COMMIT}:{ITEM_JSONL}").decode("utf-8")
    items = [json.loads(line) for line in raw.splitlines() if line.strip()]
    report = _git_bytes(f"{SOURCE_COMMIT}:{CORPUS_MD}").decode("utf-8")
    stored_domains = _section_counts(report, "## Domain coverage", "## Scale coverage")
    stored_scales = _section_counts(report, "## Scale coverage", "## Design notes")
    jsonl_domains: dict[str, int] = {}
    jsonl_scales: dict[str, int] = {}
    for item in items:
        jsonl_domains[item["domain"]] = jsonl_domains.get(item["domain"], 0) + 1
        jsonl_scales[item["scale_level"]] = jsonl_scales.get(item["scale_level"], 0) + 1
    cluster_ids = sorted({item["cluster_id"] for item in items})
    roles_ok = cluster_ids == [f"C{cluster}{role}" for cluster in range(1, 8) for role in "ABC"]
    stored_domain_total = sum(stored_domains.values())
    stored_scale_total = sum(stored_scales.values())
    domains_match = stored_domains == jsonl_domains
    scales_match = stored_scales == jsonl_scales
    return {
        "instrument": "stage_a_v3_corpus_balance",
        "source_commit": SOURCE_COMMIT,
        "corpus_report_sha256": _sha256(report.encode("utf-8")),
        "jsonl_items": len(items),
        "jsonl_cluster_roles_complete": roles_ok,
        "jsonl_domains": jsonl_domains,
        "jsonl_scales": jsonl_scales,
        "stored_domains": stored_domains,
        "stored_scales": stored_scales,
        "stored_domain_total": stored_domain_total,
        "stored_scale_total": stored_scale_total,
        "domains_match_jsonl": domains_match,
        "scales_match_jsonl": scales_match,
        "status": "REPRODUCIBLE" if domains_match and scales_match and roles_ok else "INCONSISTENT",
        "empirical_status": "ABSENT",
        "note": (
            "The balance report is prose on the product commit. No script in that commit writes it. "
            "The item CSV is an unread LFS pointer, so this comparison uses the JSONL."
        ),
    }


def weight_identifiability() -> dict:
    rng = random.Random(WEIGHT_SEED)
    equal = [1, 1, 1, 1, 1, 1, 1, 1]
    choice_only = [0, 0, 0, 0, 0, 0, 0, 1]
    mass_on_coherence = [2, 1, 1, 1, 1, 1, 1, 0]
    mass_on_choice = [0, 1, 1, 1, 1, 1, 1, 2]
    mass_on_concreteness = [1, 1, 1, 2, 1, 1, 1, 0]

    independent_taus = []
    proportional_taus = []
    duplicate_max_abs = 0
    for _ in range(N_MATRICES):
        independent = _independent_matrix(rng)
        tau = _kendall_tau_b(_column_scores(independent, equal), _column_scores(independent, choice_only))
        if tau is None:
            raise RuntimeError("independent matrix produced an undefined Kendall tau")
        independent_taus.append(tau)
        proportional = _proportional_matrix()
        tau_p = _kendall_tau_b(_column_scores(proportional, equal), _column_scores(proportional, choice_only))
        if tau_p is None:
            raise RuntimeError("proportional matrix produced an undefined Kendall tau")
        proportional_taus.append(tau_p)
        duplicated = _duplicate_choice(independent)
        left = _column_scores(duplicated, mass_on_coherence)
        right = _column_scores(duplicated, mass_on_choice)
        duplicate_max_abs = max(duplicate_max_abs, max(abs(a - b) for a, b in zip(left, right)))

    reversal_matrix = [[0] * 8 for _ in range(2)]
    reversal_matrix[0][0] = 10
    reversal_matrix[1][3] = 10
    reversal_tau = _kendall_tau_b(
        _column_scores(reversal_matrix, mass_on_coherence),
        _column_scores(reversal_matrix, mass_on_concreteness),
    )
    mean_independent = sum(independent_taus) / len(independent_taus)
    return {
        "instrument": "seeded_weight_identifiability",
        "status": "REPRODUCIBLE",
        "class": "SIMULATION",
        "empirical_status": "ABSENT",
        "seed": WEIGHT_SEED,
        "n_items": N_ITEMS,
        "n_matrices": N_MATRICES,
        "score_support": "uniform integers {0..10}",
        "baseline_equal_weights_eighths": equal,
        "baseline_choice_only_eighths": choice_only,
        "null": "rank invariance, Kendall tau-b = 1, which is what proportional profiles satisfy",
        "independent_mean_kendall_tau_b": mean_independent,
        "independent_min_kendall_tau_b": min(independent_taus),
        "independent_fraction_tau_below_1": sum(tau < 1 for tau in independent_taus) / N_MATRICES,
        "proportional_all_tau_equal_1": all(tau == 1 for tau in proportional_taus),
        "duplicate_column_max_abs_composite_diff": duplicate_max_abs,
        "constructed_nonredundant_transfer_tau_b": reversal_tau,
        "closest_applicability": "not scored; no distance was defined",
        "domain_weights_assigned": False,
        "interpretation": (
            "A single Eight-C weight vector is unidentified when two columns carry the same profile. "
            "A composite ranking stays put when every C is the same latent value, and it moves when the "
            "eight profiles are drawn independently. No domain success history was used."
        ),
    }


def _remaining_module():
    name = "stage_a_remaining"
    if name in sys.modules:
        return sys.modules[name]
    script = Path(__file__).with_name("stage_a_remaining.py")
    spec = importlib.util.spec_from_file_location(name, script)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def build_report() -> dict:
    mock = recompute_mock()
    weights = weight_identifiability()
    local = local_planned_mock_checks()
    corpus = corpus_balance()
    remaining = _remaining_module()
    items = _items()
    records = _records(
        _load_original_pipeline()[0],
        items,
        "vary_by_attempt",
        MOCK_SEED,
    )
    config_text = _git_bytes(f"{SOURCE_COMMIT}:{SOURCE_PREFIX}/config/stage_a_v3.yaml").decode("utf-8")
    definitions_md = _git_bytes(
        f"{SOURCE_COMMIT}:{SOURCE_PREFIX}/docs/conceptual/eight_c_operational_definitions_v3.md"
    ).decode("utf-8")
    prompt_text = _git_bytes(
        f"{SOURCE_COMMIT}:{SOURCE_PREFIX}/prompts/ti_sigma_stage_a_v3_rater_prompt.txt"
    ).decode("utf-8")
    construct = remaining.common_construct(records)
    goodness_fit = remaining.goodness_accounted_for(records)
    profiles = remaining.blocked_profiles()
    return {
        "study": "eight_c_instrument_2026_10_20",
        "eight_c_names": list(EIGHT_C),
        "mock": mock,
        "local_mock_checks": local,
        "corpus": corpus,
        "weights": weights,
        "attempt_accounting": remaining.registered_attempt_accounting(items, config_text),
        "common_construct": construct,
        "goodness_accounted_for": goodness_fit,
        "named_pairs": remaining.named_pair_exchangeability(records),
        "contradiction_selectivity": remaining.contradiction_selectivity(records),
        "mock_fleiss_kappa": remaining.fleiss_kappa_mock(records),
        "definition_fidelity": remaining.definition_fidelity(definitions_md, prompt_text),
        "engineered_profiles": profiles,
        "preregistered_discriminations": {
            "status": "BLOCKED",
            "reason": profiles["reason"],
        },
        "eight_c_kappa": {"status": "ABSENT"},
    }


def _fmt(value: float) -> str:
    return repr(value)


def render_markdown(report: dict) -> str:
    mock = report["mock"]
    weights = report["weights"]
    local = report["local_mock_checks"]
    corpus = report["corpus"]
    attempts = report["attempt_accounting"]
    fidelity = report["definition_fidelity"]
    construct = report["common_construct"]
    goodness_fit = report["goodness_accounted_for"]
    stored = mock["recomputed_vary_by_attempt_cli_default"]
    registered = mock["recomputed_vary_by_attempt_registered_seed"]
    goodness = stored["mean_abs_diff"]["goodness"]
    registered_goodness = registered["mean_abs_diff"]["goodness"]
    association = mock["goodness_versus_mean_c"]
    lines = [
        "# Eight-C instrument check, 2026-10-20",
        "",
        "Generator check of the Stage A v3 mock, plus a seeded simulation of weight identifiability. Neither result is an Eight-C kappa or a human rating study.",
        "",
        f"Source commit: `{mock['source_commit']}`. Definitions status on that commit: `{mock['definitions_status']}`. `paid_collection_started`: false.",
        "",
        "## Generator",
        "",
        f"The stored file `results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json` matches `vary_by_attempt` with base seed `{MOCK_SEED}`. That is the default of `scripts/run_ti_sigma_stage_a_v3_mock_pipeline.py`. Match: `{mock['stored_json_matches_cli_default_seed']}`.",
        "",
        f"The registered config seed `{REGISTERED_SEED}` does not match that file. Match: `{mock['stored_json_matches_registered_seed']}`. Goodness mean absolute difference under the registered seed: `{_fmt(registered_goodness)}`.",
        "",
        f"CLI-default goodness mean absolute difference: `{_fmt(goodness)}`. Exact-match rate: `{stored['exact_match_rate']}`. Item groups: `{stored['item_groups']}`.",
        "",
        f"The `fixed` strategy on the same items and the same CLI seed returns exact-match rate `{mock['fixed_strategy_exact_match_rate']}` and goodness mean absolute difference `{mock['fixed_strategy_goodness_mad']}`.",
        "",
        f"Expected absolute difference of two independent uniform draws on {{0..10}}: `{mock['uniform_expectation_score_mad']}` (3.6363...). Expected absolute difference on {{0..3}}, the contradiction scale: `{mock['uniform_expectation_contradiction_mad']}`.",
        "",
        f"Mean of the eight stored C gaps: `{_fmt(mock['mean_of_eight_c_mads'])}`. Uniform reference, {N_MC} draws, seed {mock['mean_c_mad_versus_uniform']['seed']}: Monte Carlo mean `{_fmt(mock['mean_c_mad_versus_uniform']['monte_carlo_mean'])}`, two-sided tail `{_fmt(mock['mean_c_mad_versus_uniform']['two_sided_tail'])}`.",
        "",
        f"Goodness gap versus the same uniform reference: two-sided tail `{_fmt(mock['goodness_mad_versus_uniform']['two_sided_tail'])}`.",
        "",
        f"Mean contradiction gap `{_fmt(mock['mean_of_contradiction_mads'])}` versus uniform {{0..3}}: two-sided tail `{_fmt(mock['mean_contradiction_mad_versus_uniform']['two_sided_tail'])}`.",
        "",
        f"Pearson r between the separate goodness bucket and the mean of the eight Cs, {association['n_mock_rows']} mock rows: `{_fmt(association['pearson_r_goodness_vs_mean_c'])}`. Permutation p `{_fmt(association['two_sided_permutation_p'])}` from {N_PERM} shuffles, seed {CORR_PERM_SEED}.",
        "",
        "The items CSV and the metadata CSV remain LFS pointers. The hash does not read `choice_bearer` or `choice_scope`. A direct check with two different values in those fields left the scores unchanged: "
        f"`{mock['choice_fields_excluded_from_hash']}`.",
        "",
        "Status of the generator arithmetic: REPRODUCIBLE. Status of an Eight-C reliability coefficient: ABSENT.",
        "",
        "## Weights",
        "",
        f"Seed `{weights['seed']}`, `{weights['n_matrices']}` matrices, `{weights['n_items']}` items, scores uniform on {{0..10}}.",
        "",
        f"Proportional profiles, every C equal to the same item latent: every equal-weight versus choice-only Kendall tau-b equals 1: `{weights['proportional_all_tau_equal_1']}`.",
        "",
        f"Independent profiles, equal weights versus choice only: mean Kendall tau-b `{_fmt(weights['independent_mean_kendall_tau_b'])}`, minimum `{_fmt(weights['independent_min_kendall_tau_b'])}`, fraction below 1: `{_fmt(weights['independent_fraction_tau_below_1'])}`.",
        "",
        f"When the choice column is a copy of coherence, moving the choice weight onto coherence or onto choice leaves the integer composite unchanged. Maximum absolute difference across the {N_MATRICES} matrices: `{weights['duplicate_column_max_abs_composite_diff']}`.",
        "",
        f"A two-item matrix with the mass on coherence in one weighting and the same mass on concreteness in the other reverses order. Kendall tau-b: `{weights['constructed_nonredundant_transfer_tau_b']}`.",
        "",
        "Status: REPRODUCIBLE arithmetic, class SIMULATION. This weight check is not one of the Stage A primary analyses. No domain weight was assigned. Closest applicability was not scored.",
        "",
        "## Planned local checks",
        "",
        f"Schema validity of the {local['schema_records']} CLI-default mock records: failures `{local['schema_failures']}`. Status: {local['schema_status']}.",
        "",
        f"Fixed-strategy goodness ICC(1,1): `{_fmt(local['fixed_strategy_goodness_icc_1_1'])}`. ICC(2,1): `{_fmt(local['fixed_strategy_goodness_icc_2_1'])}`.",
        "",
        "Vary-by-attempt moments and agreement, 63 mock scores. The uniform mean on {0..10} is 5. These are hash summaries.",
        "",
        "| Score | Mean | Sample SD | ICC(1,1) | ICC(2,1) |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for key in ("goodness",) + EIGHT_C:
        moment = local["moments"][key]
        agreement = local["icc"][key]
        lines.append(
            f"| {key} | {_fmt(moment['mean'])} | {_fmt(moment['sample_sd'])} | {_fmt(agreement['icc_1_1'])} | {_fmt(agreement['icc_2_1'])} |"
        )
    goodness_icc = local["icc"]["goodness"]["icc_1_1"]
    icc_ref = local["goodness_icc_1_1_versus_uniform"]
    lines.extend(
        [
            "",
            f"Goodness ICC(1,1) `{_fmt(goodness_icc)}` against {icc_ref['draws']} independent uniform studies, seed {icc_ref['seed']}: Monte Carlo mean `{_fmt(icc_ref['monte_carlo_mean'])}`, two-sided tail `{_fmt(icc_ref['two_sided_tail'])}`.",
            "",
            f"Corpus balance status: {corpus['status']}. JSONL items: {corpus['jsonl_items']}. Cluster roles A/B/C for clusters 1–7 complete: `{corpus['jsonl_cluster_roles_complete']}`.",
            "",
            f"Stored domain counts sum to {corpus['stored_domain_total']}. JSONL domain counts sum to {corpus['jsonl_items']}. Domain counts match: `{corpus['domains_match_jsonl']}`. Scale counts match: `{corpus['scales_match_jsonl']}`.",
            "",
            "JSONL domains: " + ", ".join(f"{name} {count}" for name, count in sorted(corpus["jsonl_domains"].items())) + ".",
            "",
            "Stored domains: " + ", ".join(f"{name} {count}" for name, count in sorted(corpus["stored_domains"].items())) + ".",
            "",
            "JSONL scales: " + ", ".join(f"{name} {count}" for name, count in sorted(corpus["jsonl_scales"].items())) + ".",
            "",
            "Stored scales: " + ", ".join(f"{name} {count}" for name, count in sorted(corpus["stored_scales"].items())) + ".",
            "",
            corpus["note"],
            "",
            "## Registered attempt accounting",
            "",
            f"Original `_mock_response_for_attempt`, registered seed `{attempts['base_seed']}`. Planned logical ratings: {attempts['planned_logical_ratings']}. First-attempt valid: {attempts['first_attempt_valid']}. Eventual valid: {attempts['eventual_valid']}. Eventual invalid: {attempts['eventual_invalid']}. Total attempts: {attempts['total_attempts']}. Within the cap of {attempts['maximum_total_attempts']}: `{attempts['within_attempt_cap']}`.",
            "",
            "Retry keys: " + ", ".join(attempts["retry_keys"]) + ".",
            "",
            "## Common construct",
            "",
            f"Unit: {construct['unit']}. Cronbach alpha: `{_fmt(construct['cronbach_alpha'])}`. First eigenvalue: `{_fmt(construct['first_eigenvalue'])}`. Permutation p: `{_fmt(construct['first_eigenvalue_permutation_p'])}` from {construct['permutation_draws']} column shuffles, seed {construct['permutation_seed']}. Independence rejected at {construct['alpha']}: `{construct['independence_rejected']}`.",
            "",
            f"Horn retained components: {construct['retained_components']}. Seed {construct['horn_seed']}, {construct['horn_draws']} shuffles. PC1 share of variance: `{_fmt(construct['pc1_variance_share'])}`. Residual share after PC1: `{_fmt(construct['residual_variance_share_after_pc1'])}`. Mean PC1 communality: `{_fmt(construct['mean_communality_pc1'])}`. Effective rank: `{_fmt(construct['effective_rank'])}`.",
            "",
            f"Status: {construct['construct_status']}. One common construct accounts for the eight scores: `{construct['one_common_construct_accounts_for_the_eight']}`. {construct['n_limit']}",
            "",
            "## Goodness accounted for by the eight Cs",
            "",
            f"In-sample R-squared: `{_fmt(goodness_fit['in_sample_r2'])}`. Permutation p: `{_fmt(goodness_fit['in_sample_r2_permutation_p'])}`. Leave-one-out R-squared: `{_fmt(goodness_fit['loo_r2'])}`. Full linear accounting: `{goodness_fit['fully_accounted_for']}`.",
            "",
            f"Incremental Choice delta R-squared: `{_fmt(goodness_fit['incremental_choice_delta_r2'])}`. Permutation p: `{_fmt(goodness_fit['incremental_choice_permutation_p'])}`.",
            "",
            goodness_fit["cmi_note"],
            "",
            "## Named pairs and contradictions",
            "",
            "Exchangeability of the three named pairs in the mock item means. This is not the directional engineered contrast.",
            "",
        ]
    )
    flagged = []
    for name, pair in report["named_pairs"]["pairs"].items():
        lines.append(
            f"- {name}: mean difference `{_fmt(pair['mean_difference'])}`, p `{_fmt(pair['mean_difference_permutation_p'])}`; Pearson r `{_fmt(pair['pearson_r'])}`, p `{_fmt(pair['pearson_r_permutation_p'])}`."
        )
        if pair["mean_difference_permutation_p"] < 0.05 or pair["pearson_r_permutation_p"] < 0.05:
            flagged.append(name)
    lines.append("")
    lines.append(
        "Six exchangeability p-values were computed, with no multiplicity adjustment. "
        + (
            "Pairs with an unadjusted p-value below 0.05: " + ", ".join(flagged) + "."
            if flagged
            else "None of the six unadjusted p-values is below 0.05."
        )
        + " A single unadjusted p-value is not the registered directional contrast."
    )
    selectivity = report["contradiction_selectivity"]
    fleiss = report["mock_fleiss_kappa"]["kappa"]
    lines.extend(
        [
            "",
            f"Contradiction peak-minus-rest mean `{_fmt(selectivity['mean_peak_minus_rest'])}` versus independent uniform scores. One-sided permutation p `{_fmt(selectivity['permutation_p_greater'])}`. Designed type selectivity: {selectivity['designed_type_selectivity']}.",
            "",
            "Fleiss kappa treating the three hash attempts as raters and scores 0–10 as categories. Goodness kappa "
            f"`{_fmt(fleiss['goodness'])}`. This is generator agreement. A human or LLM Eight-C kappa remains ABSENT.",
            "",
            "## Still blocked",
            "",
            report["engineered_profiles"]["reason"],
            "",
            f"Metadata OID `{report['engineered_profiles']['lfs_oid_sha256']}`.",
            "",
            "## Definition fidelity",
            "",
            f"Mock reads the definition text: `{fidelity['mock_reads_definition_text']}`. Seed inputs: {', '.join(fidelity['mock_seed_inputs'])}.",
            "",
            f"Definition sentences contained in the rater prompt: {fidelity['definition_sentences_exact']} exact, {fidelity['definition_sentences_reworded']} reworded. Operational questions absent: {fidelity['operational_questions_absent']}. High-anchor sets absent: {fidelity['anchor_sets_absent']}. Do-not-confuse lines absent: {fidelity['do_not_confuse_absent']}.",
            "",
        ]
    )
    for row in fidelity["rows"]:
        lines.append(
            f"- {row['dimension']}: definition {row['definition_status']}; operational question {row['operational_question']}; anchors {row['high_anchor']}; do-not-confuse {row['do_not_confuse']}; HEM boundary {row['hem_boundary']}."
        )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    report = build_report()
    out_json = OUT_DIR / "results.json"
    out_md = OUT_DIR / "EIGHT_C_INSTRUMENT_REPORT.md"
    out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out_md.write_text(render_markdown(report), encoding="utf-8")
    mock = report["mock"]
    print(f"stored_match={mock['stored_json_matches_cli_default_seed']}")
    print(f"registered_match={mock['stored_json_matches_registered_seed']}")
    print(f"fixed_exact={mock['fixed_strategy_exact_match_rate']}")
    print(f"independent_mean_tau={report['weights']['independent_mean_kendall_tau_b']}")
    print(f"corpus_status={report['corpus']['status']}")
    print(f"schema_failures={report['local_mock_checks']['schema_failures']}")
    print(f"construct={report['common_construct']['construct_status']}")
    print(f"first_p={report['common_construct']['first_eigenvalue_permutation_p']}")
    print(f"loo_r2={report['goodness_accounted_for']['loo_r2']}")
    print(f"first_valid={report['attempt_accounting']['first_attempt_valid']}")
    print(f"wrote={out_json}")


if __name__ == "__main__":
    main()
