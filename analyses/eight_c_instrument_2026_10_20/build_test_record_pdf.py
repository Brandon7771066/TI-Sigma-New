"""Write the Eight-C Stage A test record as a PDF.

Numbers come from results.json in this directory. The PDF is a reading copy
of that file plus the decision about what remains. It does not add a result.
"""

from __future__ import annotations

import json
from pathlib import Path

from fpdf import FPDF

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results.json"
OUT = ROOT / "EIGHT_C_STAGE_A_TEST_RECORD.pdf"
FONT = "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"
FONT_BOLD = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"


def num(value: object) -> str:
    if isinstance(value, float):
        return repr(value)
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)


class Record(FPDF):
    def footer(self) -> None:
        self.set_y(-12)
        self.set_font("DejaVu", size=8)
        self.set_text_color(80, 80, 80)
        self.cell(0, 8, f"Eight-C Stage A test record  ·  page {self.page_no()}/{{nb}}", align="C")


def paragraph(pdf: Record, text: str, size: float, height: float, bold: bool = False) -> None:
    pdf.set_x(pdf.l_margin)
    pdf.set_font("DejaVu", "B" if bold else "", size)
    pdf.multi_cell(0, height, text, new_x="LMARGIN", new_y="NEXT")


def heading(pdf: Record, text: str) -> None:
    pdf.ln(2)
    pdf.set_text_color(20, 20, 20)
    paragraph(pdf, text, 13, 7, bold=True)
    pdf.ln(1)


def subhead(pdf: Record, text: str) -> None:
    pdf.ln(1)
    pdf.set_text_color(20, 20, 20)
    paragraph(pdf, text, 11, 6, bold=True)


def body(pdf: Record, text: str) -> None:
    pdf.set_text_color(30, 30, 30)
    paragraph(pdf, text, 9.5, 5)
    pdf.ln(1)


def table(pdf: Record, headers: list[str], rows: list[list[str]], widths: tuple[float, ...]) -> None:
    pdf.set_font("DejaVu", size=8)
    with pdf.table(col_widths=widths, line_height=4.2, text_align="LEFT") as grid:
        header = grid.row()
        for name in headers:
            header.cell(name)
        for row in rows:
            line = grid.row()
            for cell in row:
                line.cell(cell)
    pdf.ln(2)


def build() -> None:
    report = json.loads(RESULTS.read_text(encoding="utf-8"))
    mock = report["mock"]
    stored = mock["recomputed_vary_by_attempt_cli_default"]
    registered = mock["recomputed_vary_by_attempt_registered_seed"]
    local = report["local_mock_checks"]
    corpus = report["corpus"]
    construct = report["common_construct"]
    goodness = report["goodness_accounted_for"]
    attempts = report["attempt_accounting"]
    fidelity = report["definition_fidelity"]
    pairs = report["named_pairs"]
    selectivity = report["contradiction_selectivity"]
    fleiss = report["mock_fleiss_kappa"]
    weights = report["weights"]
    profiles = report["engineered_profiles"]

    pdf = Record(format="Letter")
    pdf.add_font("DejaVu", "", FONT)
    pdf.add_font("DejaVu", "B", FONT_BOLD)
    pdf.alias_nb_pages()
    pdf.set_auto_page_break(auto=True, margin=16)
    pdf.set_margins(16, 16, 16)
    pdf.add_page()

    pdf.set_text_color(20, 20, 20)
    paragraph(pdf, "TI Sigma Eight-C tests", 18, 8, bold=True)
    paragraph(pdf, "Stage A record: what was run, what it used, and what comes next", 11, 6)
    pdf.ln(1)
    body(
        pdf,
        "Reading copy of analyses/eight_c_instrument_2026_10_20/results.json. "
        "Prepared 24 October 2026, America/Chicago. The checks themselves are dated "
        "20–23 October 2026. Source of the instrument: product commit "
        f"{mock['source_commit']} (origin/product/truth-engine-alpha-1.1). "
        "Definitions status on that commit: NEW_CANONICAL_DRAFT. "
        "paid_collection_started: false.",
    )
    body(
        pdf,
        "Class labels used below. GENERATOR means the number describes the hash mock, "
        "not a human or LLM rater. SIMULATION means synthetic profiles drawn for a "
        "weight question. INSTRUMENT_TEXT means a comparison of two source files. "
        "BLOCKED means the registered input file could not be read. ABSENT means no "
        "rating table exists. A generator result is not a validation of the Eight Cs.",
    )

    heading(pdf, "1. The precise definitions were not the scoring rule")
    body(
        pdf,
        "The operational cards are eight_c_operational_definitions_v3.md. "
        "The rater prompt is ti_sigma_stage_a_v3_rater_prompt.txt. "
        f"The mock reads the definition text: {num(fidelity['mock_reads_definition_text'])}. "
        "Its seed inputs are " + ", ".join(fidelity["mock_seed_inputs"]) + ". "
        f"Definition sentences contained unchanged in the prompt: {fidelity['definition_sentences_exact']}. "
        f"Reworded: {fidelity['definition_sentences_reworded']}. "
        f"Operational questions absent: {fidelity['operational_questions_absent']} of 8. "
        f"High/mid/low anchor sets absent: {fidelity['anchor_sets_absent']} of 8. "
        f"Do-not-confuse lines absent: {fidelity['do_not_confuse_absent']} of 8. "
        "Goodness in the prompt is “Structural and evaluative adequacy expressed through the Eight Cs,” "
        f"and the prompt also says to rate Goodness independently: {num(fidelity['goodness_prompt_also_says_rate_independently'])}.",
    )
    body(
        pdf,
        "EXACT means the card’s definition sentence is contained in that C’s prompt block. "
        "REWORDED means the prompt uses a shorter or altered sentence. "
        "The six changes are: Coherence drops “stated aims.” "
        "Consistency changes “constraints, and” and “across” to “rules, or” and “within.” "
        "Continuity drops “developmental.” Completion drops “stages.” "
        "Closeness changes “adjacent” to “nearby.” Choice drops “evaluated.” "
        "Only Concreteness also carries its HEM boundary in the prompt.",
    )
    table(
        pdf,
        ["C", "Definition", "Question", "Anchors", "Do not confuse", "HEM boundary"],
        [
            [
                row["dimension"],
                row["definition_status"],
                row["operational_question"],
                row["high_anchor"],
                row["do_not_confuse"],
                row["hem_boundary"],
            ]
            for row in fidelity["rows"]
        ],
        (32, 28, 28, 24, 32, 32),
    )
    subhead(pdf, "Canonical sentence and the prompt sentence")
    for row in fidelity["rows"]:
        body(
            pdf,
            f"{row['dimension']} ({row['definition_status']}). Card: {row['canonical_definition']} "
            f"Prompt: {row['prompt_text'].replace(chr(10), ' / ')}",
        )

    heading(pdf, "2. Generator reproducibility")
    body(
        pdf,
        "The stored file results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json "
        f"matches vary_by_attempt with base seed {mock['base_seed_matching_stored_json']}: "
        f"{num(mock['stored_json_matches_cli_default_seed'])}. "
        f"The registered config seed {mock['registered_base_seed']} matches that file: "
        f"{num(mock['stored_json_matches_registered_seed'])}. "
        f"Item groups {stored['item_groups']}. Attempts per item {stored['attempts_per_item']}. "
        f"Exact-match rate {num(stored['exact_match_rate'])}. "
        f"Goodness mean absolute difference {num(stored['mean_abs_diff']['goodness'])}. "
        f"Registered-seed goodness mean absolute difference {num(registered['mean_abs_diff']['goodness'])}. "
        f"The fixed strategy on the CLI seed returns exact-match {num(mock['fixed_strategy_exact_match_rate'])} "
        f"and goodness mean absolute difference {num(mock['fixed_strategy_goodness_mad'])}.",
    )
    body(
        pdf,
        "Expected absolute difference of two independent uniform draws on {0..10} is "
        f"{mock['uniform_expectation_score_mad']} (440/121). On {{0..3}} it is "
        f"{mock['uniform_expectation_contradiction_mad']} (20/16). "
        f"Mean of the eight C gaps: {num(mock['mean_of_eight_c_mads'])}, "
        f"uniform two-sided tail {num(mock['mean_c_mad_versus_uniform']['two_sided_tail'])} "
        f"from {mock['mean_c_mad_versus_uniform']['draws']} draws, seed {mock['mean_c_mad_versus_uniform']['seed']}. "
        f"Goodness gap tail {num(mock['goodness_mad_versus_uniform']['two_sided_tail'])}. "
        f"Mean contradiction gap {num(mock['mean_of_contradiction_mads'])}, "
        f"tail {num(mock['mean_contradiction_mad_versus_uniform']['two_sided_tail'])}. "
        "choice_bearer and choice_scope are not hash inputs. Substituting them left the scores unchanged: "
        f"{num(mock['choice_fields_excluded_from_hash'])}. "
        "The items CSV and the metadata CSV were not downloaded. The repository LFS budget was exceeded.",
    )
    association = mock["goodness_versus_mean_c"]
    body(
        pdf,
        f"Pearson r of the separate goodness bucket with the mean of the eight Cs, "
        f"{association['n_mock_rows']} mock rows: {num(association['pearson_r_goodness_vs_mean_c'])}. "
        f"Permutation p {num(association['two_sided_permutation_p'])} from {association['permutation_draws']} shuffles, "
        f"seed {association['permutation_seed']}.",
    )
    c_rows = [
        [name, num(stored["mean_abs_diff"]["C_scores"][name]), num(registered["mean_abs_diff"]["C_scores"][name])]
        for name in report["eight_c_names"]
    ]
    c_rows.insert(0, ["goodness", num(stored["mean_abs_diff"]["goodness"]), num(registered["mean_abs_diff"]["goodness"])])
    table(
        pdf,
        ["Score", "CLI-default mean abs. diff.", "Registered-seed mean abs. diff."],
        c_rows,
        (50, 65, 70),
    )
    table(
        pdf,
        ["Contradiction", "CLI-default mean abs. diff."],
        [
            [name, num(stored["mean_abs_diff"]["contradictions"][name])]
            for name in stored["mean_abs_diff"]["contradictions"]
        ],
        (90, 90),
    )

    heading(pdf, "3. Corpus balance")
    body(
        pdf,
        f"Status: {corpus['status']}. JSONL items: {corpus['jsonl_items']}. "
        f"Cluster roles A/B/C for clusters 1–7 complete: {num(corpus['jsonl_cluster_roles_complete'])}. "
        f"Stored domain counts sum to {corpus['stored_domain_total']}. "
        f"Stored scale counts sum to {corpus['stored_scale_total']}. "
        f"Domains match the JSONL: {num(corpus['domains_match_jsonl'])}. "
        f"Scales match the JSONL: {num(corpus['scales_match_jsonl'])}. "
        + corpus["note"],
    )
    domain_names = sorted(set(corpus["jsonl_domains"]) | set(corpus["stored_domains"]))
    table(
        pdf,
        ["Domain", "JSONL", "Stored prose"],
        [
            [name, str(corpus["jsonl_domains"].get(name, 0)), str(corpus["stored_domains"].get(name, 0))]
            for name in domain_names
        ],
        (90, 40, 50),
    )
    scale_names = sorted(set(corpus["jsonl_scales"]) | set(corpus["stored_scales"]))
    table(
        pdf,
        ["Scale", "JSONL", "Stored prose"],
        [
            [name, str(corpus["jsonl_scales"].get(name, 0)), str(corpus["stored_scales"].get(name, 0))]
            for name in scale_names
        ],
        (70, 50, 60),
    )

    heading(pdf, "4. Schema, moments, and agreement")
    body(
        pdf,
        f"Schema records {local['schema_records']}. Failures {local['schema_failures']}. "
        f"Status {local['schema_status']}. Class {local['class']}. "
        f"Fixed-strategy goodness ICC(1,1) {num(local['fixed_strategy_goodness_icc_1_1'])}. "
        f"ICC(2,1) {num(local['fixed_strategy_goodness_icc_2_1'])}. "
        "The vary-by-attempt moments below are 63 hash scores. The uniform mean on {0..10} is 5. "
        f"Goodness ICC(1,1) versus {local['goodness_icc_1_1_versus_uniform']['draws']} independent uniform studies, "
        f"seed {local['goodness_icc_1_1_versus_uniform']['seed']}: "
        f"Monte Carlo mean {num(local['goodness_icc_1_1_versus_uniform']['monte_carlo_mean'])}, "
        f"two-sided tail {num(local['goodness_icc_1_1_versus_uniform']['two_sided_tail'])}.",
    )
    table(
        pdf,
        ["Score", "Mean", "Sample SD", "ICC(1,1)", "ICC(2,1)"],
        [
            [
                key,
                num(local["moments"][key]["mean"]),
                num(local["moments"][key]["sample_sd"]),
                num(local["icc"][key]["icc_1_1"]),
                num(local["icc"][key]["icc_2_1"]),
            ]
            for key in ("goodness",) + tuple(report["eight_c_names"])
        ],
        (36, 36, 36, 36, 36),
    )

    heading(pdf, "5. Registered attempt accounting")
    body(
        pdf,
        "Original function ti_sigma_pipeline.stage_a_v3._mock_response_for_attempt. "
        f"Seed strategy {attempts['seed_strategy']}. Base seed {attempts['base_seed']}. "
        f"Planned logical ratings {attempts['planned_logical_ratings']}. "
        f"First-attempt valid {attempts['first_attempt_valid']} "
        f"(rate {num(attempts['first_attempt_valid_rate'])}). "
        f"Eventual valid {attempts['eventual_valid']}. Eventual invalid {attempts['eventual_invalid']}. "
        f"Total attempts {attempts['total_attempts']}. Cap {attempts['maximum_total_attempts']}. "
        f"Inside the cap: {num(attempts['within_attempt_cap'])}. "
        "Retry keys: " + ", ".join(attempts["retry_keys"]) + ". "
        "The five keys fail the first attempt because the mock inserts an unknown property, then the second attempt is valid.",
    )

    heading(pdf, "6. Do the eight scores share a common construct?")
    body(
        pdf,
        "Unit: " + construct["unit"] + ". "
        f"Null: the eight columns are mutually independent. Statistic: the largest Pearson eigenvalue. "
        f"{construct['permutation_draws']} column shuffles, seed {construct['permutation_seed']}. "
        f"Reject when p < {num(construct['alpha'])}. "
        f"First eigenvalue {num(construct['first_eigenvalue'])}. "
        f"Permutation p {num(construct['first_eigenvalue_permutation_p'])}. "
        f"Independence rejected: {num(construct['independence_rejected'])}. "
        f"Cronbach alpha {num(construct['cronbach_alpha'])}. "
        f"Effective rank {num(construct['effective_rank'])} on a scale from 1 to 8. "
        f"Horn parallel analysis, {construct['horn_draws']} shuffles, seed {construct['horn_seed']}: "
        f"retained components {construct['retained_components']}. "
        f"PC1 share of variance {num(construct['pc1_variance_share'])}. "
        f"Residual share after PC1 {num(construct['residual_variance_share_after_pc1'])}. "
        f"Mean PC1 communality {num(construct['mean_communality_pc1'])}. "
        f"Status: {construct['construct_status']}. "
        "One common construct accounts for the eight scores: "
        f"{num(construct['one_common_construct_accounts_for_the_eight'])}. "
        + construct["n_limit"],
    )
    table(
        pdf,
        ["Component", "Observed eigenvalue", "Horn 95th percentile"],
        [
            [str(index + 1), num(observed), num(cutoff)]
            for index, (observed, cutoff) in enumerate(zip(construct["eigenvalues"], construct["horn_95"]))
        ],
        (40, 70, 70),
    )
    table(
        pdf,
        ["C", "PC1 communality"],
        [[name, num(construct["communalities_pc1"][name])] for name in report["eight_c_names"]],
        (70, 110),
    )

    heading(pdf, "7. Does that construct, or Goodness, get fully accounted for by the eight Cs?")
    body(
        pdf,
        "There is no retained common component, so there is no common factor for the eight scores to exhaust. "
        "The descriptive PC1 share above is the share of a component that did not clear the null. "
        "Goodness is a separate hash key. Full linear accounting was defined in advance as leave-one-out R-squared equal to 1. "
        f"In-sample R-squared {num(goodness['in_sample_r2'])}. "
        f"Permutation p {num(goodness['in_sample_r2_permutation_p'])}. "
        f"Leave-one-out R-squared {num(goodness['loo_r2'])}. "
        f"Fully accounted for: {num(goodness['fully_accounted_for'])}. "
        f"Incremental Choice delta R-squared {num(goodness['incremental_choice_delta_r2'])}. "
        f"Permutation p {num(goodness['incremental_choice_permutation_p'])}. "
        f"Draws {goodness['permutation_draws']}, seed {goodness['permutation_seed']}. "
        + goodness["cmi_note"],
    )
    table(
        pdf,
        ["Dropped C", "In-sample R² without it", "Delta R²"],
        [
            [
                name,
                num(goodness["leave_one_c_out"][name]["in_sample_r2_without_dimension"]),
                num(goodness["leave_one_c_out"][name]["delta_r2"]),
            ]
            for name in report["eight_c_names"]
        ],
        (50, 70, 60),
    )
    table(
        pdf,
        ["C", "Partial r with Goodness", "Gaussian CMI (bits)"],
        [
            [
                name,
                num(goodness["gaussian_cmi_with_goodness"][name]["partial_r_with_goodness_given_other_cs"]),
                num(goodness["gaussian_cmi_with_goodness"][name]["gaussian_cmi_bits"]),
            ]
            for name in report["eight_c_names"]
        ],
        (50, 70, 60),
    )

    heading(pdf, "8. Named pairs, contradictions, and a mock kappa")
    body(
        pdf,
        "Exchangeability of the three named pairs in the mock item means. "
        "Six p-values, no multiplicity adjustment. "
        "A single unadjusted p-value is not the registered directional contrast. "
        f"Engineered directional contrast: {pairs['engineered_directional_contrast']}.",
    )
    table(
        pdf,
        ["Pair", "Mean difference", "p", "Pearson r", "p"],
        [
            [
                name,
                num(pair["mean_difference"]),
                num(pair["mean_difference_permutation_p"]),
                num(pair["pearson_r"]),
                num(pair["pearson_r_permutation_p"]),
            ]
            for name, pair in pairs["pairs"].items()
        ],
        (55, 35, 30, 35, 25),
    )
    body(
        pdf,
        f"Contradiction peak-minus-rest mean {num(selectivity['mean_peak_minus_rest'])} "
        f"on {selectivity['n_rows']} mock rows. "
        f"One-sided permutation p {num(selectivity['permutation_p_greater'])} "
        f"against {selectivity['null']}. "
        f"Designed type selectivity: {selectivity['designed_type_selectivity']}.",
    )
    body(
        pdf,
        "Fleiss kappa treating the three hash attempts as raters and integer scores 0–10 as categories. "
        f"A human or LLM kappa: {fleiss['human_or_llm_kappa']}.",
    )
    table(
        pdf,
        ["Score", "Fleiss kappa"],
        [[name, num(fleiss["kappa"][name])] for name in ("goodness",) + tuple(report["eight_c_names"])],
        (70, 110),
    )

    heading(pdf, "9. Weight simulation")
    body(
        pdf,
        "This check is not a Stage A primary analysis. It follows the owner’s statement that the weights are deliberately unclear. "
        f"Seed {weights['seed']}. Matrices {weights['n_matrices']}. Items {weights['n_items']}. "
        f"Scores {weights['score_support']}. "
        f"Proportional profiles, every equal-weight versus choice-only Kendall tau-b equals 1: "
        f"{num(weights['proportional_all_tau_equal_1'])}. "
        f"Independent mean Kendall tau-b {num(weights['independent_mean_kendall_tau_b'])}. "
        f"Minimum {num(weights['independent_min_kendall_tau_b'])}. "
        f"Fraction below 1: {num(weights['independent_fraction_tau_below_1'])}. "
        f"Duplicate-column maximum absolute composite difference {weights['duplicate_column_max_abs_composite_diff']}. "
        f"Constructed transfer onto concreteness, Kendall tau-b {num(weights['constructed_nonredundant_transfer_tau_b'])}. "
        f"Domain weights assigned: {num(weights['domain_weights_assigned'])}. "
        f"Closest applicability: {weights['closest_applicability']}.",
    )

    heading(pdf, "10. What comes next")
    body(
        pdf,
        profiles["reason"]
        + f" File: {profiles['missing_file']}. LFS oid sha256:{profiles['lfs_oid_sha256']}. Size {profiles['lfs_size']} bytes. "
        "The unread columns are " + ", ".join(profiles["required_and_unread"]) + ". "
        "The prompt also requires choice_bearer and choice_scope, and both are in that same file. "
        "A rating pass was not started, and no profile was inferred from item titles.",
    )
    body(
        pdf,
        "The next tests, in the order the instrument requires them:",
    )
    steps = [
        "1. Read the metadata CSV once LFS access is restored. Confirm its sha256 is f5f3a276063af7f895ac4f61c49c349bb02cfbcc50327a9bd69a7819221f82e1 before using any intended profile.",
        "2. Run the directional A/B/C contrasts against intended_contrast and the intended_* score columns. Do not infer those directions from item titles.",
        "3. Run designed contradiction-type selectivity against intended_contradiction_types.",
        "4. Decide the rater text before any new kappa. The current prompt is a shortened gloss. A study that is compared with the v3 cards needs the definition sentence, the operational question, the three anchors, and the do-not-confuse line written into the instructions.",
        "5. Collect the 63 logical ratings under the registered stopping rule. paid_collection_started is false, and that collection was not authorized by the preregistration’s local-verification boundary.",
        "6. Estimate a human or LLM Fleiss kappa, the three named discriminations, and a common-factor test on those ratings. The hash results in this record do not transfer.",
        "7. Keep Goodness as its own rating. Ask again whether the eight Cs account for it. Full linear accounting, as defined here, is leave-one-out R-squared equal to 1.",
        "8. Leave N=21 diagnostic. The preregistration forbids a strong completeness claim from 21 items.",
    ]
    for step in steps:
        body(pdf, step)

    body(
        pdf,
        "Files. results.json is the numeric source. EIGHT_C_INSTRUMENT_REPORT.md is the short narrative. "
        "run_eight_c_instrument.py and stage_a_remaining.py recompute both. "
        "tests/test_eight_c_instrument.py locks the JSON. "
        "This PDF is produced by build_test_record_pdf.py from results.json.",
    )
    pdf.output(str(OUT))


if __name__ == "__main__":
    build()
    print(OUT)
