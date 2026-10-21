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
)

ITEM_JSONL = f"{SOURCE_PREFIX}/data/items/ti_sigma_stage_a_v3_items.jsonl"
STORED_JSON = f"{SOURCE_PREFIX}/results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json"
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


def build_report() -> dict:
    mock = recompute_mock()
    weights = weight_identifiability()
    return {
        "study": "eight_c_instrument_2026_10_20",
        "eight_c_names": list(EIGHT_C),
        "mock": mock,
        "weights": weights,
        "preregistered_discriminations": {
            "status": "PLANNED",
            "reason": (
                "Stage A names Choice versus Concreteness, Concreteness versus Completion, "
                "and Closeness versus Continuity. No ratings table is in the repo. "
                "paid_collection_started is false. Those contrasts were not estimated."
            ),
        },
        "eight_c_kappa": {"status": "ABSENT"},
    }


def _fmt(value: float) -> str:
    return repr(value)


def render_markdown(report: dict) -> str:
    mock = report["mock"]
    weights = report["weights"]
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
        "Status: REPRODUCIBLE arithmetic, class SIMULATION. No domain weight was assigned. Closest applicability was not scored.",
        "",
        "## Left unestimated",
        "",
        report["preregistered_discriminations"]["reason"],
        "",
        "Eight-C Fleiss kappa: ABSENT.",
        "",
    ]
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
    print(f"wrote={out_json}")


if __name__ == "__main__":
    main()
