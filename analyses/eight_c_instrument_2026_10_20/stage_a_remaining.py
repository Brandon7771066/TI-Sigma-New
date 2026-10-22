"""Remaining Stage A v3 calculations on the mock score matrix.

The preregistration authorizes local verification only. These functions use
the original retry rule and the hash scores. They do not create ratings.
Directional engineered contrasts stay blocked: the provisional profiles live
in the metadata CSV, and that Git LFS object was not downloaded.

Primary common-construct rules, fixed before the mock matrix is summarized:

- Unit: 21 item means. Three attempts are averaged. The 63 rows are dependent
  hash replicates and are not a second sample.
- H0 for a common construct: the eight columns are mutually independent.
  Statistic: the largest eigenvalue of the Pearson correlation matrix.
  Null: independently permute each column. 5,000 draws. Seed 20261024.
  Reject H0 when the permutation p-value is below 0.05.
- Exhaustiveness: Horn parallel analysis, 2,000 column shuffles, seed
  20260902, the seed named in the dossier's analyze_stage_a.py. A component
  is retained when its eigenvalue exceeds the null 95th percentile.
  One common construct accounts for the eight scores only when exactly one
  component is retained. Full accounting additionally requires the residual
  variance after that component to be zero. N=21 remains diagnostic.
- Goodness is a separate estimand. Full linear accounting means leave-one-out
  R-squared equals 1. The observed leave-one-out R-squared is the extent.
"""

from __future__ import annotations

import importlib
import json
import random

import numpy as np

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
CONTRADICTIONS = (
    "incomplete_information",
    "competing_domains",
    "category_error",
    "genuine_tradeoff",
    "self_reference",
    "temporal_inconsistency",
    "measurement_uncertainty",
    "true_incoherence",
)
NAMED_PAIRS = (
    ("choice", "concreteness"),
    ("concreteness", "completion"),
    ("closeness", "continuity"),
)
PERM_SEED = 20261024
HORN_SEED = 20260902
N_PERM = 5000
N_HORN = 2000
ALPHA = 0.05
METADATA_OID = "f5f3a276063af7f895ac4f61c49c349bb02cfbcc50327a9bd69a7819221f82e1"


def _as_float(value: float) -> float:
    return float(value)


def _permutation_p(observed: float, nulls: list[float], alternative: str) -> float:
    if alternative == "greater":
        hits = sum(null >= observed for null in nulls)
    elif alternative == "two-sided":
        center = sum(nulls) / len(nulls)
        distance = abs(observed - center)
        hits = sum(abs(null - center) >= distance for null in nulls)
    else:
        raise ValueError(alternative)
    return (hits + 1) / (len(nulls) + 1)


def _item_table(records: list[dict]) -> tuple[list[str], np.ndarray, np.ndarray, np.ndarray]:
    by_item: dict[str, list[dict]] = {}
    for record in records:
        by_item.setdefault(record["item_id"], []).append(record)
    item_ids = sorted(by_item)
    scores = []
    goodness = []
    contradictions = []
    for item_id in item_ids:
        rows = by_item[item_id]
        scores.append([sum(row["C_scores"][name] for row in rows) / len(rows) for name in EIGHT_C])
        goodness.append(sum(row["goodness"] for row in rows) / len(rows))
        contradictions.append(
            [sum(row["contradictions"][name] for row in rows) / len(rows) for name in CONTRADICTIONS]
        )
    return item_ids, np.asarray(scores, float), np.asarray(goodness, float), np.asarray(contradictions, float)


def _correlation(matrix: np.ndarray) -> np.ndarray:
    return np.corrcoef(matrix, rowvar=False)


def _eigenvalues(matrix: np.ndarray) -> np.ndarray:
    values = np.linalg.eigvalsh(_correlation(matrix))
    return np.sort(values)[::-1]


def _permute_columns(matrix: np.ndarray, rng: random.Random) -> np.ndarray:
    shuffled = matrix.copy()
    n_rows = matrix.shape[0]
    for column in range(matrix.shape[1]):
        order = list(range(n_rows))
        rng.shuffle(order)
        shuffled[:, column] = matrix[order, column]
    return shuffled


def _cronbach_alpha(matrix: np.ndarray) -> float:
    k = matrix.shape[1]
    item_variance = matrix.var(axis=0, ddof=1).sum()
    total_variance = matrix.sum(axis=1).var(ddof=1)
    if total_variance == 0:
        return 0.0
    return _as_float((k / (k - 1)) * (1 - item_variance / total_variance))


def _effective_rank(eigenvalues: np.ndarray) -> float:
    positive = eigenvalues[eigenvalues > 0]
    shares = positive / positive.sum()
    entropy = -sum(share * np.log(share) for share in shares)
    return _as_float(np.exp(entropy))


def _ols_r2(features: np.ndarray, target: np.ndarray) -> float:
    design = np.column_stack([np.ones(len(target)), features])
    beta = np.linalg.lstsq(design, target, rcond=None)[0]
    predicted = design @ beta
    total = ((target - target.mean()) ** 2).sum()
    if total == 0:
        return 0.0
    return _as_float(1 - ((target - predicted) ** 2).sum() / total)


def _loo_r2(features: np.ndarray, target: np.ndarray) -> float:
    n_rows = len(target)
    predicted = np.empty(n_rows)
    for index in range(n_rows):
        train = np.ones(n_rows, dtype=bool)
        train[index] = False
        design = np.column_stack([np.ones(train.sum()), features[train]])
        beta = np.linalg.lstsq(design, target[train], rcond=None)[0]
        row = np.concatenate([[1.0], features[index]])
        predicted[index] = row @ beta
    total = ((target - target.mean()) ** 2).sum()
    if total == 0:
        return 0.0
    return _as_float(1 - ((target - predicted) ** 2).sum() / total)


def _partial_r(target: np.ndarray, focus: np.ndarray, others: np.ndarray) -> float:
    def residual(outcome: np.ndarray) -> np.ndarray:
        design = np.column_stack([np.ones(len(outcome)), others])
        beta = np.linalg.lstsq(design, outcome, rcond=None)[0]
        return outcome - design @ beta

    left = residual(target)
    right = residual(focus)
    if left.std(ddof=1) == 0 or right.std(ddof=1) == 0:
        return 0.0
    return _as_float(np.corrcoef(left, right)[0, 1])


def _gaussian_cmi_bits(partial_r: float) -> float:
    clipped = min(abs(partial_r), 0.999999)
    return _as_float(-0.5 * np.log1p(-clipped**2) / np.log(2))


def common_construct(records: list[dict]) -> dict:
    item_ids, scores, goodness, _contradictions = _item_table(records)
    observed = _eigenvalues(scores)
    rng = random.Random(PERM_SEED)
    null_first = []
    for _ in range(N_PERM):
        null_first.append(float(_eigenvalues(_permute_columns(scores, rng))[0]))
    first_p = _permutation_p(float(observed[0]), null_first, "greater")
    horn = random.Random(HORN_SEED)
    horn_null = []
    for _ in range(N_HORN):
        horn_null.append(_eigenvalues(_permute_columns(scores, horn)))
    horn_matrix = np.vstack(horn_null)
    horn_95 = np.quantile(horn_matrix, 0.95, axis=0)
    retained = int(np.sum(observed > horn_95))
    communality = _correlation_loadings(scores, observed)
    mean_communality = _as_float(np.mean(communality))
    variance_share = _as_float(observed[0] / observed.sum())
    residual_share = _as_float(1 - variance_share)
    independence_rejected = first_p < ALPHA
    one_component = retained == 1
    fully_accounted = bool(one_component and residual_share == 0.0)
    if not independence_rejected and retained == 0:
        construct_status = "NO_COMMON_CONSTRUCT"
    elif one_component and independence_rejected:
        construct_status = "ONE_COMPONENT_DIAGNOSTIC"
    elif retained >= 2:
        construct_status = "MORE_THAN_ONE_COMPONENT"
    else:
        construct_status = "MIXED_DIAGNOSTIC"
    return {
        "instrument": "eight_c_common_construct",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "unit": "21 item means of 3 hash attempts",
        "item_ids": item_ids,
        "alpha": ALPHA,
        "permutation_draws": N_PERM,
        "permutation_seed": PERM_SEED,
        "horn_draws": N_HORN,
        "horn_seed": HORN_SEED,
        "cronbach_alpha": _cronbach_alpha(scores),
        "eigenvalues": [ _as_float(value) for value in observed ],
        "first_eigenvalue": _as_float(observed[0]),
        "first_eigenvalue_permutation_p": first_p,
        "independence_rejected": independence_rejected,
        "horn_95": [ _as_float(value) for value in horn_95 ],
        "retained_components": retained,
        "pc1_variance_share": variance_share,
        "residual_variance_share_after_pc1": residual_share,
        "mean_communality_pc1": mean_communality,
        "communalities_pc1": {name: _as_float(value) for name, value in zip(EIGHT_C, communality)},
        "effective_rank": _effective_rank(observed),
        "construct_status": construct_status,
        "one_common_construct_accounts_for_the_eight": fully_accounted,
        "n_limit": "N=21 is diagnostic. The preregistration forbids a strong completeness claim from 21 items.",
    }


def _correlation_loadings(matrix: np.ndarray, eigenvalues: np.ndarray) -> np.ndarray:
    _values, vectors = np.linalg.eigh(_correlation(matrix))
    order = np.argsort(_values)[::-1]
    first = vectors[:, order[0]]
    if first.sum() < 0:
        first = -first
    return (first * np.sqrt(eigenvalues[0])) ** 2


def goodness_accounted_for(records: list[dict]) -> dict:
    _item_ids, scores, goodness, _contradictions = _item_table(records)
    in_sample = _ols_r2(scores, goodness)
    loo = _loo_r2(scores, goodness)
    rng = random.Random(PERM_SEED)
    nulls = []
    for _ in range(N_PERM):
        order = list(range(len(goodness)))
        rng.shuffle(order)
        nulls.append(_ols_r2(scores, goodness[order]))
    choice_index = EIGHT_C.index("choice")
    without_choice = np.delete(scores, choice_index, axis=1)
    delta_choice = in_sample - _ols_r2(without_choice, goodness)
    choice_nulls = []
    for _ in range(N_PERM):
        shuffled = scores.copy()
        order = list(range(len(goodness)))
        rng.shuffle(order)
        shuffled[:, choice_index] = scores[order, choice_index]
        full = _ols_r2(shuffled, goodness)
        reduced = _ols_r2(np.delete(shuffled, choice_index, axis=1), goodness)
        choice_nulls.append(full - reduced)
    leave_one = {}
    conditional = {}
    for index, name in enumerate(EIGHT_C):
        reduced = np.delete(scores, index, axis=1)
        leave_one[name] = {
            "in_sample_r2_without_dimension": _ols_r2(reduced, goodness),
            "delta_r2": in_sample - _ols_r2(reduced, goodness),
        }
        others = np.delete(scores, index, axis=1)
        partial = _partial_r(goodness, scores[:, index], others)
        conditional[name] = {
            "partial_r_with_goodness_given_other_cs": partial,
            "gaussian_cmi_bits": _gaussian_cmi_bits(partial),
        }
    return {
        "instrument": "goodness_accounted_for_by_eight_cs",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "n_items": int(len(goodness)),
        "in_sample_r2": in_sample,
        "loo_r2": loo,
        "in_sample_r2_permutation_p": _permutation_p(in_sample, nulls, "greater"),
        "permutation_draws": N_PERM,
        "permutation_seed": PERM_SEED,
        "fully_accounted_for": bool(loo == 1.0),
        "extent": loo,
        "extent_definition": "leave-one-out R-squared of Goodness on the eight item-mean Cs",
        "incremental_choice_delta_r2": _as_float(delta_choice),
        "incremental_choice_permutation_p": _permutation_p(delta_choice, choice_nulls, "greater"),
        "leave_one_c_out": leave_one,
        "gaussian_cmi_with_goodness": conditional,
        "cmi_note": "Gaussian CMI from partial correlations. N=21 with seven conditioners is unstable and is not a confirmation sample.",
    }


def named_pair_exchangeability(records: list[dict]) -> dict:
    _item_ids, scores, _goodness, _contradictions = _item_table(records)
    columns = {name: scores[:, index] for index, name in enumerate(EIGHT_C)}
    rng = random.Random(PERM_SEED)
    pairs = {}
    for left_name, right_name in NAMED_PAIRS:
        difference = columns[left_name] - columns[right_name]
        observed = float(difference.mean())
        correlation = float(np.corrcoef(columns[left_name], columns[right_name])[0, 1])
        diff_nulls = []
        corr_nulls = []
        for _ in range(N_PERM):
            signs = np.array([1 if rng.random() < 0.5 else -1 for _ in range(len(difference))], float)
            diff_nulls.append(float((difference * signs).mean()))
            order = list(range(len(difference)))
            rng.shuffle(order)
            corr_nulls.append(float(np.corrcoef(columns[left_name], columns[right_name][order])[0, 1]))
        pairs[f"{left_name}_versus_{right_name}"] = {
            "mean_difference": observed,
            "mean_difference_permutation_p": _permutation_p(observed, diff_nulls, "two-sided"),
            "pearson_r": correlation,
            "pearson_r_permutation_p": _permutation_p(correlation, corr_nulls, "two-sided"),
        }
    return {
        "instrument": "named_pair_exchangeability",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "null": "the two columns are exchangeable in the mock item means",
        "pairs": pairs,
        "engineered_directional_contrast": "BLOCKED",
    }


def contradiction_selectivity(records: list[dict]) -> dict:
    rows = []
    for record in records:
        values = [record["contradictions"][name] for name in CONTRADICTIONS]
        peak = max(values)
        rest = [value for index, value in enumerate(values) if index != values.index(peak)]
        rows.append(peak - (sum(rest) / len(rest)))
    observed = sum(rows) / len(rows)
    rng = random.Random(PERM_SEED)
    nulls = []
    for _ in range(N_PERM):
        draws = []
        for _record in records:
            values = [rng.randrange(4) for _ in CONTRADICTIONS]
            peak = max(values)
            rest = [value for index, value in enumerate(values) if index != values.index(peak)]
            draws.append(peak - (sum(rest) / len(rest)))
        nulls.append(sum(draws) / len(draws))
    return {
        "instrument": "contradiction_selectivity_versus_independent_uniform",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "n_rows": len(records),
        "mean_peak_minus_rest": observed,
        "permutation_p_greater": _permutation_p(observed, nulls, "greater"),
        "permutation_draws": N_PERM,
        "permutation_seed": PERM_SEED,
        "null": "eight independent uniform{0,1,2,3} contradiction scores",
        "designed_type_selectivity": "BLOCKED",
    }


def fleiss_kappa_mock(records: list[dict]) -> dict:
    by_item: dict[str, list[dict]] = {}
    for record in records:
        by_item.setdefault(record["item_id"], []).append(record)
    categories = list(range(11))

    def kappa(extractor) -> float:
        n_items = len(by_item)
        k_raters = 3
        table = []
        for rows in by_item.values():
            counts = [0] * len(categories)
            for row in rows:
                counts[extractor(row)] += 1
            table.append(counts)
        agreement = []
        for counts in table:
            agreement.append((sum(count * count for count in counts) - k_raters) / (k_raters * (k_raters - 1)))
        p_bar = sum(agreement) / n_items
        category_totals = [sum(row[index] for row in table) for index in range(len(categories))]
        p_e = sum((total / (n_items * k_raters)) ** 2 for total in category_totals)
        if p_e == 1:
            return 1.0
        return (p_bar - p_e) / (1 - p_e)

    values = {name: kappa(lambda row, name=name: row["C_scores"][name]) for name in EIGHT_C}
    values["goodness"] = kappa(lambda row: row["goodness"])
    return {
        "instrument": "fleiss_kappa_hash_attempts_as_raters",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "categories": "integers 0..10",
        "raters": "three hash attempts, not human or LLM raters",
        "kappa": values,
        "human_or_llm_kappa": "ABSENT",
    }


def registered_attempt_accounting(items: list[dict], config_text: str) -> dict:
    importlib.import_module("ti_sigma_pipeline.stage_a_v3")
    stage = importlib.import_module("ti_sigma_pipeline.stage_a_v3")
    config = json.loads(config_text)
    retry = stage._retry_fail_set(config)
    base_seed = config["base_seed"]
    seed_strategy = config["seed_strategy"]
    max_attempts = int(config["maximum_attempts_per_logical_rating"])
    first_valid = 0
    eventual_valid = 0
    eventual_invalid = 0
    attempts = 0
    logical = 0
    for item in items:
        for replicate in range(1, int(config["ratings_per_item"]) + 1):
            logical += 1
            logical_key = f"registered_stage_a:{item['item_id']}:{replicate}"
            terminal = ""
            attempt_number = 0
            while attempt_number < max_attempts and not terminal:
                attempt_number += 1
                _raw, _parsed, _parse_status, _schema_status, terminal_status, _error = stage._mock_response_for_attempt(
                    item,
                    logical_key,
                    attempt_number,
                    seed_strategy,
                    base_seed,
                    retry,
                )
                attempts += 1
                if attempt_number == 1 and terminal_status == "TERMINAL_VALID":
                    first_valid += 1
                if terminal_status == "RETRY" and attempt_number >= max_attempts:
                    terminal_status = "TERMINAL_INVALID"
                if terminal_status == "TERMINAL_VALID":
                    terminal = terminal_status
                    eventual_valid += 1
                elif terminal_status in {"TERMINAL_INVALID", "TERMINAL_FAILED"}:
                    terminal = terminal_status
                    eventual_invalid += 1
            if not terminal:
                eventual_invalid += 1
    return {
        "instrument": "registered_mock_attempt_accounting",
        "class": "GENERATOR",
        "empirical_status": "ABSENT",
        "base_seed": base_seed,
        "seed_strategy": seed_strategy,
        "planned_logical_ratings": logical,
        "first_attempt_valid": first_valid,
        "first_attempt_valid_rate": first_valid / logical,
        "eventual_valid": eventual_valid,
        "eventual_invalid": eventual_invalid,
        "total_attempts": attempts,
        "maximum_total_attempts": int(config["maximum_total_attempts"]),
        "within_attempt_cap": attempts <= int(config["maximum_total_attempts"]),
        "retry_keys": sorted(retry),
        "source_function": "ti_sigma_pipeline.stage_a_v3._mock_response_for_attempt",
    }


def blocked_profiles() -> dict:
    return {
        "status": "BLOCKED",
        "missing_file": "experiments/eight_c_goodness_pilot/data/metadata/ti_sigma_stage_a_v3_metadata.csv",
        "lfs_oid_sha256": METADATA_OID,
        "lfs_size": 4549,
        "required_and_unread": [
            "intended_coherence",
            "intended_consistency",
            "intended_continuity",
            "intended_concreteness",
            "intended_completion",
            "intended_criticality",
            "intended_closeness",
            "intended_choice",
            "intended_goodness",
            "intended_contradiction_types",
            "intended_contrast",
            "predicted_profile_notes",
        ],
        "reason": (
            "The registered directional contrasts and the designed contradiction types "
            "are columns of the metadata CSV. Git LFS returned the budget error and the "
            "object was not downloaded. No provisional profile was inferred from item titles."
        ),
    }
