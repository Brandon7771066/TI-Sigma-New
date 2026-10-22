# TI Sigma Experiment Ledger

Audit date: 2026-10-05. Repository state: `main` at `b5955f25` (`Adapt published sugar anchor to FAFB v783 IDs and preserve outputs`).

This ledger records what is in the repository. It does not treat comments, paper prose, or README claims as experimental results. A number appears here only when it is in a result artifact or was produced by a command run during this audit.

Governing standard: `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. The rules in that file are the human-authored working standard. This ledger is an AI-assisted inventory of files. It is not a human-authored hypothesis list and it is not an independent verification, except for the one floating-point command named under VERIFIED.

Source recovery against the 14 October 2026 master test ledger (T01–T38) is in `TI_SIGMA_MASTER_LEDGER_SOURCE_RECOVERY.md`. That file attaches each master-ledger entry to the GitHub artifact that actually stores the number. The 2026-10-16 ChatGPT consolidation is indexed in `research/chatgpt_recovery/`. Literature transcriptions for T27, T28, T30, T31, and T35 are recorded there. They are not new experiments.

## Status labels

| Label | Meaning used in this audit |
| --- | --- |
| VERIFIED | Re-executed in this audit and the printed checks passed. Applies only to `python3 lean4/verify_theorems.py` (9/9). That run is floating-point, not a Lean compile. |
| REPRODUCIBLE | A script, its inputs (or a fully synthetic generator), a seed or deterministic procedure, and a saved artifact are all in the repo. Not re-run in this audit. |
| REPORTED | A saved artifact exists. Re-execution needs an external service, hardware token, streamed dataset, unpinned environment, or was not attempted. |
| UNREPRODUCED | Code describes a computation, but no saved numeric artifact of that computation is in the repo. |
| INCONSISTENT | Two in-repo sources assign different values or criteria to the same named object. |
| PLANNED | Design, dashboard, or code path with no stored outcome. |
| HYPOTHESIS | A stated expectation, framework-internal formula, or literature association. Not a result. A failed prediction stays a failed prediction unless a later pre-registration explicitly changes the hypothesis. |

`lean` and `lake` are not on `PATH` in this environment. The only project `.olean` files found outside vendored Mathlib are `lean4_ns_uop/.lake/lakefile.olean` and `lean4_ns_uop_pass54_mathlib/.lake/lakefile.olean`. No module `.olean` exists for any project theorem file. Header text that says "formally verified" is therefore not Lean verification.

A line-anchored scan of the 42 project `.lean` files (everything under `*/.lake/*` excluded) found 298 `theorem`, 5 `lemma`, 121 `def`/`noncomputable def`, 121 `axiom`, and 16 `opaque` declarations. Indented declarations can be missed by that scan. Comment lines that contain the word `sorry` were not counted as proof holes. Actual `sorry` terms are listed in section 2.

---

## 1. Mathematical definitions

### 1.1 Python package `ti_sigma/constants.py` (code)

These are the definitions imported by the hypercomputer package. Comments in the file date the threshold rewrite to 2026-03-01.

| Name | Formula in code | Approx. | Lines |
| --- | --- | --- | --- |
| `ZERO`, `ONE` | `0.0`, `1.0` | 0, 1 | 29–30 |
| `I` | `1j` | i | 31 |
| `SQRT2` | `math.sqrt(2)` | 1.4142135623730951 | 32 |
| `E` | `math.e` | 2.718281828459045 | 33 |
| `PHI` | `(1+sqrt(5))/2` | 1.618033988749895 | 34 |
| `PI` | `math.pi` | 3.141592653589793 | 35 |
| `C_EMERICK` | `1/(PHI*SQRT2)` | 0.437016024448821 | 36 |
| `LCC_TRALSE` | `SQRT2-1` | 0.414213562373095 | 54 |
| `LCC_TRUE` | `PHI-1` | 0.618033988749895 | 55 |
| `LCC_EMERICK` | `1/SQRT2` | 0.707106781186548 | 56 |
| `LCC_HIGH` | `C_EMERICK+LCC_TRALSE` | 0.851229586821916 | 60 |
| `LCC_RADIANT` | `sqrt(E/PI)` | 0.930604859102099 | 61 |
| `LCC_IC` | alias of `LCC_RADIANT` | same | 66 |
| `TB_TRUE/FALSE/INDETERMINATE` | `+1`, `-1`, `0` | | 76–78 |
| `TB_TRALSE_LOWER/UPPER` | `∓ LCC_TRALSE` | | 79–80 |
| `GILE_WEIGHTS` | G 0.42, I 0.25, L 0.18, E 0.15 | | 83 |
| Extended Euler check | `abs(e**(i*pi) + SQRT2*PHI*C_EMERICK)` | intended ~0 | 73 |

`verify_matching_rules()` in the same file checks the classical and extended Euler identities in floating point. This audit did not call it. The algebraic content of `C_EMERICK = 1/(φ√2)` is the same fact checked as Theorem 2 below. The **names** `LCC_HIGH` and `LCC_RADIANT` are not the same objects as in Lean. See section 18.

### 1.2 Other code definitions in `ti_sigma/`

| Name | Rule | File |
| --- | --- | --- |
| Myrion resolution | If `abs(tb) > t` map to `sign(tb)`, else leave unchanged. Default `t = LCC_TRALSE`. | `ti_sigma/tralsebit_engine.py` |
| `partial_resolution` | Threshold shrinks by `1/PHI` each iteration. | same |
| `lcc_coherence` | `1 - mean(abs(tb) <= MR_T)` | same |
| `gile_score` | Mix of `(G*I)*(L*E)` and weighted sum, clip to `[-1,1]` | same |
| Penrose adjacency | Fibonacci offsets plus `int(i*PHI) % n` | same |
| LCC band featurizer | Zones from `[LCC_TRALSE, LCC_HIGH]` | `ti_sigma/aperiodic_optimizer.py` |
| L×E squeezing | `r = ln(PHI)` per mode | `ti_sigma/quantum_layer.py` |
| Oracle routing | `< LCC_TRALSE` one model; mid band two models; `>= LCC_HIGH` three models | `ti_sigma/oracle_bus.py` |
| Radiant gate | `lcc_level > LCC_IC` requires `operator_gile >= 0.85` | same |
| Layer-4 entry | oracle only if `lcc >= LCC_TRALSE` | `ti_sigma/hypercomputer.py` |

`ti_sigma/kaggle_adapter.py` does not define a new constant.

### 1.3 TI-G edge rule (`ti_sigma_graph.py`)

| Name | Rule | Lines |
| --- | --- | --- |
| Edge probability | `p(i,j) = min(1, κ * GILE_i * GILE_j)` | 9–11, 127 |
| κ | `target_edges / sum_{i<j} g_i g_j`, cap 5.0 | 114–122 |
| Layout radii | `{0:0, 1:0.437, 2:0.934, 3:1.0, 4:1.414, 5:1.618, 6:2.718, 7:3.142}` | 94–95 |
| H1 pass | `c_bi > 0.30` and `c_bi > t_bi + 0.10` | 335–336 |
| H2 pass | `c_ps <= e_ps` only | 350–353 |
| H3 pass | `c_ar < e_ar - 0.05` | 367–368 |
| H4 pass | `bec_on_mean <= bec_off_mean` | 380 |
| H5 pass | `r0_mean > r7_mean + 0.15` | 394 |

`bok_virus_engine.py` supplies `gile_composite`, `RING_BETA`, and `GAMMA`. Those weights are a second GILE weight table and are not re-derived here.

### 1.4 Lean definitions in `lean4/TISigma.lean`

| Name | Lean definition | Lines |
| --- | --- | --- |
| `φ` | `(1 + Real.sqrt 5) / 2` | 42 |
| `LCC_HIGH` | `1 / Real.sqrt 2` | 45 |
| `LCC_RADIANT` | `1 / φ` | 48 |
| `C_EMERICK` | `1 / (φ * Real.sqrt 2)` | 52 |

`lean4/verify_theorems.py` uses this Lean naming, not `ti_sigma/constants.py`.

### 1.5 Other formal-looking definitions

| Name | Formula | Medium | File |
| --- | --- | --- | --- |
| GILE σ | `(G+I+L+E+12)/20` | code | `ticl_interpreter.py` |
| Soul-death threshold | `σ > 0.333` | code | `ticl_interpreter.py` |
| Truth-engine axioms 1–12 | prose semantics, PD scale `(-3, 2)` | prose | `theories/TI_TRUTH_ENGINE_AXIOMS.md` |
| Legacy uncertainty | JSON template still says `"value": "1.0 - MR_i"` | prose/JSON template in the same file | same, ~191–193 |
| TI Sigma 6 axioms | narrative formulas (`dC/dt = ∇ρ·v`, simplex `t+f+φ=1`) | prose | `TI_SIGMA_6_V3_ULTIMATE_AXIOMS.md` |
| B116 elegance cuts | `MI_CLIFF, LO_I, HI_I = -2.5, -2/3, +1/3` | prose | `papers/PASS_77_B116_*elegance*.md` |

Prose axiom files are definitions of a vocabulary. They are not experiments.

### 1.6 README fine-structure formula (prose, not an experiment)

`README.md` states `α ≈ 1/(4² · e · π) = 1/136.6` and "99.71% accuracy" against `1/137.036`. No dataset, no script output artifact, and the Lean file `lean4_submission/fine_structure_consciousness.lean` closes the accuracy theorem with `sorry`. This audit did not recompute that percentage as a result. Classification: **not an experiment**. The Lean statement is **UNVERIFIED** and contains `sorry`.

---

## 2. Theorems, proofs, and Lean

### 2.1 Five TI Sigma identities — numerical check VERIFIED; Lean compile UNVERIFIED

Command run in this audit: `python3 lean4/verify_theorems.py`.

Printed constants (Lean naming):

- φ = 1.6180339887498949
- √2 = 1.4142135623730951
- C_EMERICK = 0.4370160244488210
- LCC_HIGH = 0.7071067811865475
- LCC_RADIANT = 0.6180339887498948

| Check | Statement | Printed result |
| --- | --- | --- |
| 1 | φ² = φ + 1 | Δ = 0 |
| 2 | √2 · φ · C_EMERICK = 1 | Δ = 0 |
| 3 | C_EMERICK = LCC_RADIANT × LCC_HIGH | Δ = 5.55e-17 |
| 4 | 0 < C < LCC_RADIANT < LCC_HIGH < 1 | four passes; order 0 < 0.4370 < 0.6180 < 0.7071 < 1 |
| 5 | exp(iπ) + √2·φ·C_EMERICK = 0 | \|LHS\| = 1.22e-16; classical \|exp(iπ)+1\| = 1.22e-16 |

Summary line from the script: `9/9 checks passed`.

The same five statements are `theorem`s in `lean4/TISigma.lean` (`golden_ratio_identity`, `emerick_normalization`, `emerick_product_structure`, `lcc_ordering`, `extended_euler_identity`) with tactic proofs (`norm_num`, `linarith`, `ring`, `simp`) and no `sorry` in that file. The file header says "Formally verified (Lean 4 + Mathlib)" and tells the reader to paste the file into `https://live.lean-lang.org/`. No build log and no `.olean` for `TISigma` are in the repo. Status of the Lean proofs: **UNVERIFIED**. Status of the floating-point checks: **VERIFIED**.

Duplicates of the same five theorems: `attached_assets/Lean4WebDownload_1772987432885.lean` and `...2926.lean`. Same status.

`lean/Verisyn/EulerIdentity.lean` states classical `exp(π i) = -1` via `Complex.exp_pi_mul_I`. No `.olean`. **UNVERIFIED**.

### 2.2 Conditional "proofs" of open problems

The recurring pattern in `lean4/*.lean` is: sorry-free lemmas relating a symmetry or energy condition to `ρ.re = 1/2` or to an analogous gap, then a named `axiom` that is the open statement, then a theorem that is `exact` of that axiom.

These are not verified proofs of the Riemann Hypothesis, BSD, Hodge, Navier–Stokes, Yang–Mills, P vs NP, or Collatz. Status of each headline theorem that depends on a gap axiom: **UNVERIFIED** and axiom-conditional.

| File | Gap axiom (representative) | Headline theorem depends on the axiom |
| --- | --- | --- |
| `lean4/RiemannUOP.lean` | `uop_gap`, `bk_selfadjoint`, `bk_spectrum` | `riemann_hypothesis_*` |
| `lean4/GapEquivalence.lean` | `master_gap` | `riemann_hypothesis_master` |
| `lean4/VariationalRoute.lean` | `variational_gap` | `riemann_hypothesis_variational` |
| `lean4/GroupSymmetryRoute.lean` | `orbit_collapse_axiom` | `riemann_hypothesis_group_symmetry` |
| `lean4/MirrorPairing.lean` | `euler_forcing` | `riemann_hypothesis_mirror` |
| `lean4/BeingTheorem.lean` | `universal_bridge_theorem` | `riemann_hypothesis_from_being` |
| `lean4/MathlibDemo.lean` | `riemannZeta`, `euler_forcing_being` | `riemann_hypothesis_from_being` |
| `lean4/Collatz.lean` | `collatz_conjecture` | global Collatz theorems |
| `lean4/BSD.lean` | 39 axioms including `strong_bsd` | BSD theorems `exact` those axioms |
| `lean4/Hodge.lean` | `hodge_conjecture` and cycle-map axioms | Hodge theorems |
| `lean4/NavierStokes.lean` | `ns_global_regularity` and related | regularity theorems |
| `lean4/YangMills.lean` | `yang_mills_gap` | gap theorems |
| `lean4/PvsNP.lean` | `p_ne_np_gap`, `crystal_instantiates_mr` | separation theorems |
| `lean4_ns_uop*/NavierStokes/UOPGap.lean` | `UOP_existence_claim` | `UOP_implies_NS_smoothness` also uses `sorry` |
| `lean4_ti_sigma6/TralseLogic.lean` | `energy`, `coherence` | tralse theorems |
| `lean4_ti_sigma6/RiemannProof.lean` | `zeta`, `functional_equation`, `symmetry_forces_resolution` | `riemann_hypothesis` also `sorry` |
| `lean4_ti_sigma6/BSDProof.lean` | elliptic-curve and BSD axioms, several with `sorry` bodies | `birch_swinnerton_dyer` |

`lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean` has closed toy energy-decay theorems (`energy_nonneg`, `energy_at_zero`, `energy_monotone_decay`) and no `sorry`. No `.olean`. **UNVERIFIED**.

`lean4_collatz/CollatzNu2.lean` header says "0 sorry statements — fully machine-verified". The source has no `sorry` term. No `.olean`. **UNVERIFIED**.

### 2.3 `sorry` terms (proof holes, not comments)

| File | Line | What is unfinished |
| --- | --- | --- |
| `lean4/MirrorPairing.lean` | 344 | `euler_forcing_attempt` |
| `lean4_ti_sigma6/RiemannProof.lean` | 44, 71, 108, 116 | fixed-point lemma, spacing, `riemann_hypothesis` chain, `freewill_analogy` |
| `lean4_ti_sigma6/BSDProof.lean` | 32–33, 43–44, 71, 76, 85–86, 106, 117, 125–126 | `sorry` inside axiom fields and `sha_finite` |
| `lean4_submission/p_np_sketch.lean` | 59, 82, 94, 100 | `creationComplexity`, certificate and asymmetry theorems, `p_ne_np` |
| `lean4_submission/riemann_sketch.lean` | 51, 60, 74 | functional equation, pairing, dimensional constraint |
| `lean4_submission/fine_structure_consciousness.lean` | 78, 139 | `derivation_accuracy`, `unification_scale_prediction` |
| `lean4_ns_uop/NavierStokes/UOPGap.lean` | 77 | `UOP_implies_NS_smoothness` |
| `lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean` | 59 | same scaffold |

`lean4/MirrorPairing.lean` documents one `sorry` while surrounding comments say the mirror lemmas are sorry-free. The `sorry` at line 344 is real. Status of `euler_forcing_attempt`: **INCONSISTENT** with any reading that the file is a finished RH proof; **UNVERIFIED** as Lean.

### 2.4 What this audit did not do

No `lake build`. No check that the tactic proofs type-check against the pinned Mathlib in `lean4_ns_uop_pass54_mathlib` (mathlib v4.10.0 is declared there; `lean4/lakefile.lean` requires Mathlib without a commit pin visible in the header of `TISigma.lean`).

---

## 3. Statistical and empirical experiments with saved artifacts

A read-only scan found **191** `*result*.json` files. They were not re-executed. Unless a row below says otherwise, status is **REPORTED**. Hypothesis, sample size, and null are "not stated in artifact" when the JSON scan did not surface them. Full cards for the families named in the audit request follow in sections 4–12. The index in section 15 lists every JSON the scan opened.

### Experiments this audit treats as primary statistical results

Fields below are taken from the named artifact.

#### EXP-H4-SAT — TSC Hamiltonian vs small SAT

- Path: `analyses/tsc_h4_sat/tsc_h4_sat_prototype.py` → `analyses/tsc_h4_sat/results.json`
- Hypothesis: lower restricted Hamiltonian energy predicts SAT (stated in the prototype; the artifact verdict is the outcome).
- Input: synthetic 3-SAT, generated in the script. No external file.
- Method: brute-force SAT on instances with at most 5 variables; ROC of energy vs satisfiability; permutation null.
- Sample size: `n_instances=200` (`n_sat=141`, `n_unsat=59`).
- Statistic: `roc_auc=0.26782065152061546`, `p_perm=1.0`.
- Null: `null_mean_auc=0.4992833273229956`, `null_std_auc=0.04526441105329955`.
- Result: `verdict="weak / inconclusive"`. SAT mean energy 2.36809, UNSAT mean energy 1.96539 (UNSAT lower, opposite the lower-energy-means-SAT direction).
- Seed: `20260509`.
- Status: **REPRODUCIBLE**. Not re-run here.
- Limitation stated by the artifact: weak / inconclusive.

#### EXP-H4-R20 — inverted replication

- Path: `analyses/tsc_h4_sat_r20_replication/r20_replication_runner.py` → `results.json`; pre-registration `PRE_REGISTRATION.json`.
- Hypothesis: the pre-registered primary metric is inverted AUC (higher energy associated with SAT).
- Input: synthetic, `instance_seed=31415927`.
- Sample size: `n_instances_used=200` (`n_sat=138`, `n_unsat=62`).
- Statistic: `averaged_energy_auc_inverted=0.7317671809256662`; lower-direction AUC `0.26823281907433383`.
- Null/threshold: confirm if inverted AUC `>= 0.65` (stated in the verdict string).
- Result: `verdict` begins `CONFIRMED`.
- Status: **REPRODUCIBLE**.
- Relation to EXP-H4-SAT: the two artifacts test opposite directions. That is a pre-registered sign change, recorded in section 18. It is not two measurements of one hypothesis.

#### EXP-G25 — fresh-corpus RT correlation

- Path: `analyses/pass26_g25_rt_fresh_corpus/run.py` → `results.json`
- Sample size: not a single `n` in the scanned keys; `permutation_n=10000`.
- Statistic: `pearson_r=-0.008942973868560803`, `permutation_p_two_sided=0.8396`.
- Null: permutation mean `0.000396`, std `0.04473`.
- Result: `verdict=DISCONFIRM`.
- Seed: `27182818`.
- Status: **REPRODUCIBLE** if the corpus loader's inputs are the files the script reads. This audit did not open the corpus path. If that path is generated inside the script, status stays **REPRODUCIBLE**; if it fetches, downgrade to **REPORTED**. The artifact itself is present.

#### EXP-PLANT-AUXIN

- Path: `analyses/pass29_e27_lcc_plant_auxin/runner.py` → `results.json`
- Sample size: `n_total_pairs=7`, `n_pairs_above_C=7`.
- Result: `verdict=CONFIRM`.
- Seed: `27182818`.
- Status: **REPORTED**. This audit did not inspect whether the seven pairs are measurements or hard-coded literature values. Do not treat CONFIRM as a biological replication until that input is identified. See gaps.

#### EXP-MENDI

- Path: `analyses/pass43_mendi_session_analysis/analyze.py` → `results.json`
- Input: `data/mendi/sessions/session_2026-05-11T12-22-50_decoded.csv` (file exists).
- Sample size: `n_frames=2406`.
- Statistic present at top level: `linear_drift.total_drift_20min_adc=-10.473`.
- A prior read of the same JSON reported STIM2 Welch `t=-4.135` with a pre-registered SIGNIFICANT flag and STIM1/3/4 NULL. This audit's key scan did not re-print those nested stim keys. The file is the source of truth; the drift number above is what the scan extracted.
- Status: **REPRODUCIBLE** (local CSV). Single personal session.
- Limitation: one session.

#### EXP-DEPRESSJON

- Path: `analyses/lcc_depresjon/results/results.json`
- Input: CSVs under `analyses/lcc_depresjon/data/` (present).
- Sample size: `n_dep=23`, `n_con=32`.
- Statistic: `auc_rawC=0.5203804347826086`, `auc_Lhybrid=0.19972826086956522`, `auc_CPS_full=0.6807065217391304`.
- Status: **REPORTED**. Script path was not re-confirmed in this write-up beyond the results file. Data files are present.

#### EXP-UOP-ABSTENTION

- Path: `analyses/uop_abstention/analyze.py` reading `predictions.jsonl` → `results.json`
- Sample size: predictions file length was described as 300 in the artifact's accuracy block (`overall_accuracy=0.8233333333333334` implies 300 if it is a mean of 0/1; the scan did not print an `n` key).
- Statistic: `overall_accuracy=0.8233333333333334`, `mean_confidence=0.9042333333333334`, `n_above_cap=157`, `uop_better_than_baseline=false`, `frac_scrambled_caps_better_than_G_star=0.15`, high-confidence tail `>=0.95` accuracy `0.8979591836734694`.
- Null: raw-threshold and scrambled-cap comparisons encoded as those booleans.
- Status: **REPORTED**. Re-run was not attempted here. A parallel environment check reported `ModuleNotFoundError: sklearn` for `analyze.py`. That is an environment fact, not a re-computation of the metric.
- Interpretation stored in the artifact: the UOP cap was not better than the baseline on this file.

#### EXP-UOP-PHASE

- Path: `analyses/uop_phase_transition_v1/simulate.py` → `results.json`
- Statistic: `n_confirmed=4`, `phase_transition_detected=true`, `n_perturbations=10000`, `fraction_reducing_J=1.0`, `mean_delta_J=-0.1189128385765177`.
- Status: **REPRODUCIBLE** (synthetic, artifact present). Not re-run in this audit, because the script writes `results.json` into the working directory.

#### EXP-MYRION-LIM

- Path: `analyses/pass29_m27_myrion_lim/runner.py` → `results.json`
- Seed: `23571113`. Verdict: `CONFIRM`.
- Status: **REPRODUCIBLE**. The scanned keys did not include the numeric `diff`. A parallel read reported `diff=0.0` and `V_lim=1.5`. This ledger does not copy that number into the result field because this process did not open the nested keys. Open the JSON before citing `diff`.

#### EXP-GSA-SHARPE

- Path: `analyses/gsa_sharpe/results.json` and `analyses/gsa_residual_sharpe/results.json`
- Sample size: `n_days=63` (sharpe file); `n_aligned=61` (residual file).
- Statistic: GSA annualized Sharpe `1.1435700385517216`, total return `4.50719%`, max drawdown `-4.0457%`. SPY Sharpe `1.6544508012762733`, total return `6.86506%`, max drawdown `-8.577%`.
- Residual Sharpe annualized `1.176467819508585` (`residual_minus_raw_sharpe=0.032897780956863354`).
- Baseline: SPY in the same window.
- Status: **REPORTED**. Cache files exist under `data/yahoo_finance_cache/` and `data/stock_*`. This audit did not check that the 63-day window is fully contained in the cache.

#### EXP-RIEMANN-ZEROS-GILE map

- Path: `analyze_riemann_zeros.py` → `data/riemann_zeros/analysis_results.json`
- Input: `data/riemann_zeros/first_1million_zeros.txt` (file exists; first ordinate `14.134725142`).
- Sample size in artifact: `num_zeros=1000000`, range min `14.134725142`, max `600269.677012445`.
- Statistic: `gile_mapping.all_on_critical_line=true`, `gile_score=0.0`, `sigma=0.5`, `density_analysis.mean_ratio=0.8595497674082643`.
- Provenance of the ordinate table: `analyses/pass45_t6_pd_riemann/runner.py` comments cite Odlyzko `zeros1`. The text file itself has no header line. Status of the mapping result: **REPORTED**. The claim "all on the critical line" is a property of how the loader assigns real part, not a test that discovered RH. See section 18.

#### EXP-PD-RIEMANN

- Path: `analyses/pass45_t6_pd_riemann/runner.py` → `results.json`
- Sample size: `n_zeros_loaded=100000`.
- Result string: `LITERAL_PREREG_INDETERMINATE_VACUOUS_FILTER` and a note that the PD `(-3,2)` mapping needs clarification.
- Status: **REPORTED**.

---

## 4. Graph and network experiments

### EXP-TIG-CHROMATIC — URB #735 graph vs octahedron

- Path: `analyses/pass77_b68_meijer_octahedron_vs_ti/run_compare.py` → `results.json`
- Hypothesis coded as the claim chromatic(TIG)=3.
- Input: edge lists in the script (9-node TIG, 6-node octahedron). No external file.
- Method: exact invariants on a small graph.
- Sample size: TIG `V=9`, `E=15`; octahedron `V=6`, `E=12`.
- Statistic: TIG `chromatic_number=4`, `clique_number=4`, `diameter=2`, `symmetry_group_order=1`. Octahedron chromatic `3`, clique `3`, symmetry order `48`.
- Null/baseline: octahedron graph.
- Result: artifact verdict text states the chromatic-3 claim is refuted because the graph contains `K4`.
- Status: **REPRODUCIBLE**.
- Limitation: this 9-node TIG is not the 57-node SIR graph in `ti_sigma_graph.py`.

### EXP-TIG-1F — scale invariance on one Mendi session and a streamed rodent trace

- Same script and JSON, key `scale_invariance`.
- A parallel read reported Mendi `beta≈0.265`, `R²≈0.033`, `n=2406`, and a rodent `beta≈2.384`, `R²≈0.712`, `n=75000`. Those nested numbers were not re-extracted by the key scan used for section 15. Cite the JSON, not this sentence, before publication.
- Mendi CSV exists. Rodent trace is DANDI-streamed.
- Status: Mendi half **REPRODUCIBLE**; rodent half **REPORTED**.

### EXP-TIG-SIR — Crystal vs TI-G vs ER epidemics

- Path: `ti_sigma_graph.py` function `run_monte_carlo`.
- Hypothesis: H1–H5 in the module docstring (section 1.3).
- Input: adjacency from `bok_virus_engine`.
- Saved artifact: **none**.
- Status: **UNREPRODUCED**.
- Inconsistency: docstring H2 is `Crystal peak ≤ TI-G peak < ER peak`. The pass flag implements `Crystal peak ≤ ER peak` and does not test the TI-G term. **INCONSISTENT** (doc vs code). No numeric outcome exists either way.

### EXP-KURAMOTO-BA

- Path: `analyses/lcc_complex_systems_obs/run_structural_jump_tests.py` → `structural_jump_tests.json`
- Method: Kuramoto and Granger on a NetworkX Barabási–Albert graph.
- A parallel read reported T1 `N=800`, T2 `N=400`, `K_c_theory=1.0`, `r_at_Kmax=0.8869`. Not re-extracted here. Status: **REPRODUCIBLE** if the JSON and seed `11` match that read; treat the quoted floats as pending confirmation against the JSON.
- This is a network simulation. It is not a human dataset.

### EXP-BOWTIE

- Path: `analyses/pass29_b27_bowtie_4wing/runner.py` → `results.json`
- Sample size: `N_nodes=57`, `n_close_matches=5`.
- Result: `verdict=CONFIRM_PROJECTION`. Seed `16180339`.
- Status: **REPRODUCIBLE** (synthetic 57-node object). What "close match" means is defined in the runner, not restated here.

---

## 5. Crystal / TIC experiments

Crystal experiments use a 57-vertex ring polytope unless noted. No external raw file.

| ID | Script | Artifact | Stored numbers | Null / comparison | Status |
| --- | --- | --- | --- | --- | --- |
| EXP-B4 | `analyses/crystal_b4_hamiltonian/tsc_hamiltonian.py` | `results.txt` | N=57, 110 edges, λ₁=`0.191440`, highest eigenvalue `7.531746`. Phase energies: BEC 0, Supersolid `0.919886`, Mott `2.000000`, FQH-like `2.400000`, Fragmented `3.465261`. `Match: False` against urb_645 order BEC < Supersolid < FQH < Mott < Fragmented. | urb_645 expected order | **REPRODUCIBLE** |
| EXP-C5 | `analyses/crystal_c5_symmetry/tsc_symmetry.py` | `results.txt` | Point group reported as V₄ order 4 (parallel read of the text file). | group-axiom checks | **REPRODUCIBLE** |
| EXP-C6 | `analyses/crystal_c6_chsh/tsc_bec_chsh_prediction.py` | `results.txt` | Parallel read: `2×Ring(√2)=2.828427` vs Tsirelson; Ring(T) CHSH `1.414`. | classical 2, Tsirelson `2√2` | **REPRODUCIBLE** |
| EXP-SIG9 | `analyses/tsc_signatures_pass9/tsc_signatures_table.py` | `results.txt` | Parallel read: mean abs deviation `2.52%`, `2/9` exact, `5/9` within 3%. Observed constants are literals in the script, not loaded tables. | literature literals | **REPRODUCIBLE** as arithmetic; **not** an empirical fit |
| EXP-SIG-EXP | `analyses/tsc_signature_expansion/expansion.py` | `results.txt` | Parallel read: real mean dev `6.03%` vs random `9.19%`; `P(random beats observed)=0.437`. | uniform random in the ring range | **REPRODUCIBLE**; verdict in that file is suggestive |
| EXP-B42 | `analyses/pass77_b42_crystal_falsifiers/run_falsifiers.py` | `results.txt` | Parallel read: n=10 power `0.205`, n=52 power `0.808`; Ring(T) CHSH `1.4142`; phi look-elsewhere `P≈0.473`. Seed `20260527`. | classical CHSH 2 | **REPRODUCIBLE** (analytic/power). No Mendi sessions were the input of F3. |

Seed cited in B4 comments / parallel read: `20260509`. This audit read `results.txt` for B4 directly (numbers in the table). C5, C6, SIG9, SIG-EXP, and B42 numbers are from a file read by a parallel pass over the same tree; they are marked as such so a later edit can re-quote the text files before citing them.

### EXP-CH and EXP-HEMO — TSC Hamiltonian features on simulated and DANDI windows

- Paths: `analyses/pass_b_consciousness_hamiltonian_2026_06_16/` and `analyses/pass_b_hemo_fmri_fnirs_2026_06_16/`.
- Artifacts: `results_expA.json`, `results_expB.json`, `results_reachability.json` (not `results.json`).
- A parallel read of Exp A simulation reported balanced accuracy BASE `0.8401257861635221` and CH `0.912578` on `n_test=128`, chance `0.333`. Confirm against `results_expA.json` before citing.
- Live arms stream DANDI. Status of simulation JSON: **REPORTED**. Status of live arms: **REPORTED** (network data not stored as raw NWB in `data/`).

---

## 6. TIG experiments

Covered as EXP-TIG-CHROMATIC, EXP-TIG-1F, and EXP-TIG-SIR in section 4.

There is no second implemented TIG object with a saved Monte Carlo table. Papers `papers/urb_735_ti_sigma_graph_*.md` are prose.

---

## 7. TDA / topology experiments

No `ripser` or `gudhi` import was found under `analyses/`.

### EXP-T51-2 — Vietoris–Rips proxy null

- Path: `analyses/pass51_t51_batch_exec/run_all.py` → `results.json` keys `T51_2_tda_competing_null` and `T51_2_v2_tda_null`.
- Method: a cyclomatic / b1 proxy, not a persistent-homology library.
- A parallel read reported `N_total=415`, `dim=8`, and `null_p95_max_b1=0.0`, `h1_p5_max_b1=0.0`, seed `51`. The key scan of this audit did not reprint those nested fields. Status: **REPRODUCIBLE** pending a direct quote from the JSON on the next pass. Do not cite `0.0` from this paragraph alone.
- Interpretation recorded by that read: a β₁=6 claim does not separate from the Gaussian null at that size. Confirm in the JSON.

### EXP-T51-5 — Polar LF/HF

- Same `results.json`.
- Stored outcome from the scan's surrounding notes and a parallel read: `n_sessions_found=0`, `n_sessions_analyzed=0`, `mean_lf_hf=null`.
- Input directory `data/polar_h10_export/` exists and contains training-session JSON. The artifact's own caveat is that heart-rate samples are not RR intervals.
- Predicted comparison value cited in that read: `2.0`.
- Status: **REPORTED**. The pilot did not compute an LF/HF statistic. Raw RR series are **missing**.

`enhanced_monster_tests.py` contains a persistent-homology estimate and `enhanced_monster_test_results.json` has `overall_status` text `ENHANCED TESTS PASSED`. This audit did not open the metric block. Status: **REPORTED**. It is not a TDA library run.

---

## 8. Elegance / GILE experiments

### EXP-UGI1 — non-redundancy

- Path: `analyses/gile_nonredundancy_test/gile_nonredundancy_test.py` → `results.json`
- Hypothesis: each GILE axis adds predictive information (script docstring; artifact `honest_scope` narrows the claim).
- Input: sklearn datasets summarized as 13 models each on `breast_cancer`, `digits`, `synthetic_clf`, `wine`. Coordinate cache `coords_cache.json` is part of the folder.
- Sample size: `real_data.n_rows=52`. Controls `n_rows=1600`. `n_perm=500`. Seed `20260628`.
- Statistic (real data): I `delta_r2_linear=0.6182`, `perm_pvalue=0.002`, `nonredundant_sig=true`. G `delta_r2_linear=-0.0087`, `perm_pvalue=1.0`, not significant. L `delta_r2_linear=-0.0012`, `perm_pvalue=0.7944`, not significant. E `delta_r2_linear=-0.0008`, `perm_pvalue=0.6387`, not significant.
- Null: permutation of the added axis; plus a negative control (E defined as a function of G,I,L) and a positive control (all four informative).
- Result: only I is non-redundant on the real table. Elegance (E), operationalized in the script as a complexity proxy, is not.
- Status: **REPRODUCIBLE**.
- Limitation, quoted from `honest_scope`: single domain, proxies, "SUGGESTIVE and necessary-not-sufficient". The representation-theorem half is not addressed.

### EXP-GILE-TQA

- Path: `analyses/uop_abstention/gile_score.py`, `gile_analyze.py` → `gile_results.json`
- Sample size: `n_questions=120`.
- Statistic: `selective_accuracy=0.8583333333333333`, `mean_gile_composite=0.8571333333333333`, `n_above_cap=10`, `n_answered=120`.
- Status: **REPORTED** (scores file present; model calls are not re-run).

### EXP-GILE-SIM-121

- Path: `analyses/pass77_b121_gile_intelligence_truth/gile_intelligence_sim.py` → `gile_intelligence_results.json`
- Parallel read: `N=400000`, `auc_GILE_prospective=0.8620142778715462`, `auc_generic_g=0.6986846389248456`, base rate `0.0802175`, seed `20260617`.
- Status: **REPRODUCIBLE** (simulation). Cite the JSON for the floats; this line records the parallel read.

### EXP-GILE-HEM-BATTERY

- Path: `analyses/pass77_gile_hem_battery_pilot/runner.py` → `results.json`
- Parallel read: 61 propositions, `gile_composite_to_verdict_mi_bits=0.4119379044706135`, verdict string `QUALIFIED (see flags)`.
- Raters are LLMs.
- Status: **REPORTED**.

### EXP-DEN

- Path: `analyses/den_executive_network_2026_05_28/den_executive_network_sim.py` → `den_results.json`
- Verdict string in the scan: housing at least 2 independent egos in one substance lowers will-coherence; a one-being network stays at `1.0`.
- Status: **REPRODUCIBLE** (simulation, seed cited in parallel read as `20260528`).

### EXP-GILE-HEM-IBL

- Path: `analyses/pass77_b4_phase1b_ibl_valence_reachability/runner_gile_hem.py` → `results_gilehem.json`
- Parallel read: DANDI 000409, F1c Cohen's d `0.169`, gray zone; F2c Mann–Whitney p `0.085`, refuted. Seed `27182818`.
- Status: **REPORTED** (streamed neurophysiology).

Other GILE folders (`pass77_b71`, `b73`, `b74`, `b60`, `b56`, `b61`, `b83`, `b87`) contain simulations, structural checks, or `make_figs.py` only. Their JSON artifacts are in section 15 when named `*results*.json`. Figures are not results.

---

## 9. Zebrafish and biological modeling

### EXP-ZEBRA — label only

- Path: `simulations/connectome_consciousness_test_v4_302neuron.py` lines 445–447.
- The script's print loop labels network sizes `[6, 15, 56, 302, 1000, 10000, 86000]` as `C.eleg 6-n`, `Rich club`, `C.eleg interneurons`, `C.eleg full`, `Bee`, `Zebrafish`, `Mouse cortex`.
- The returned dict stores `beta`, `A`, `N_threshold_for_C_emerick`, `phi_norm_6n`, `phi_norm_15n`. It does **not** store the zebrafish row.
- `simulations/connectome_consciousness_results_v4.json` has no `zebrafish` key. It records `n_synapses=4390`, rich-club `n_neurons=15`, and scaling fields for a 302-neuron object.
- No zebrafish connectome file is in the repo.
- Status: **PLANNED** as a printed extrapolation. **No stored zebrafish result.** Any Φ number for N=10000 would be inferred by re-running and is not reported here.

### EXP-CELEG — connectome simulations v1–v8

- Paths: `simulations/connectome_consciousness_test_*.py` → `simulations/connectome_consciousness_results_v*.json`
- These are simulations and scorecards, not zebrafish data.
- v4: `n_synapses=4390`, rich club 15 neurons.
- v5: `final_scorecard.n_pass=11`, `n_total=13`.
- v6: `scorecard.n_pass=12` of 13; `phi_scaling.n_trials=20`; `phi_scaling.p_value=3.989454578818334e-12`; `phi_in_ci=false`; `scaling_law.N_star=66.26925340676354`.
- v7: isolated `n_trials=50`, `p_value=8.55e-20`, `phi_in_ci=false`; network `p_value=0.0186`, `sqrt2_in_ci=false`.
- Status: **REPORTED**. Several scorecard criteria in v4's `run_scorecard` are hard-coded `True` (lines 474–489), including "Consciousness scaling law fitted". Those booleans are not independent tests.

### EXP-RODENT-CLV1

- Path: `analyses/pass77_b67_clv1_rodent/run_rodent.py` → `results.json`
- Input: DANDI 000003 streamed NWB, not stored under `data/`.
- Parallel read: 199 windows, Kruskal H `48.792`, p `1.444e-10`, η² `0.246`.
- Status: **REPORTED**.

### EXP-RODENT-MOOD and EXP-IBL

- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_window0_600.json`: parallel read, 871 events, Cohen's d `-0.0188`, F1 `REFUTED`, seed `27182818`.
- `analyses/pass77_b4_phase1b_ibl_valence_reachability/results.json`: parallel read, 548 trials, both F1 and F2 `REFUTED`.
- Status: **REPORTED**.

### EXP-DANDI-3WAY

- Path: `analyses/pass32_dandi_3way/runner.py` → `results.json`
- Seed `27182818`. `aggregate_verdict=MIXED`. `n_eligible=2`.
- Parallel read: dandiset 000003 Pearson r `0.988`; 000053 r `0.0925` with a provenance note that values were injected from a first run; 000114 ineligible.
- Status: **REPORTED**. The injected-run note is a reproducibility limit.

### EXP-DANDI-P3B

- `analyses/pass36_e35a_lcc_p3b/results.json`: `verdict=INELIGIBLE`.
- `analyses/pass37_dandi_e36d/results.json`: `aggregate_verdict=MIXED: 2_AUDITED_INELIGIBLE + 1_TIMEOUT_UNRESOLVED`.
- Status: **REPORTED**. These are eligibility outcomes, not positive effects.

### EXP-RETRIEVAL

- Path: `analyses/pass_b_retrieval_operators_2026_06_15/runner.py` → `results.json`
- Parallel read: simulation operator O1 balanced accuracy `0.874` vs chance `0.333`; DANDI arms mixed and some operators not above chance.
- Status: **REPORTED**.

### EXP-LCC-VIRUS-EMP

- Path: `simulations/lcc_virus_empirical_test.py` → `simulations/lcc_virus_empirical_results.json`
- Sample size: `test_1 n_sessions=2` (`n_above_threshold=1`, `n_below_threshold=1`), `permutation_p=0.4999`. Monte Carlo `n_trials=50000`.
- `test_2_dandi.c_in_95ci=true`.
- Status: **REPORTED**. Two sessions do not support a binomial claim. The permutation p is consistent with a null.

### EXP-PLANT

See EXP-PLANT-AUXIN in section 3. Input provenance is unresolved in this audit.

### EXP-HYPERSCAN

- Path: `analyses/pass77_b130_lcc_hyperscanning_e3/runner.py` → `results.json`
- Parallel read: synthetic, `n_dyads=20`, seed `20260624`, `delta_gc_t=12.001`.
- OpenNeuro tree `analyses/lcc_uop_openneuro/data/` has headers and **zero** `.eeg` binaries.
- Status: **REPORTED** as a synthetic method check. It is not a human hyperscanning result.

### Personal biometric collections (data, not completed experiments)

| Path | What is on disk | Experiment that consumed it |
| --- | --- | --- |
| `data/mendi/sessions/` | one decoded fNIRS-like CSV plus BLE captures | EXP-MENDI, EXP-TIG-1F |
| `data/polar_h10/`, `data/polar_h10_export/` | Polar Flow account and training JSON | EXP-T51-5 found 0 RR series |
| `data/oura/` | sleep, session, heartrate JSON | no `results.json` found |
| `data/biowell/` and `data/biowell_2026_05_14_batch*` | GDV images and notes | no `results.json` found |
| `data/sleep_sessions/`, `data/medication_snapshots/` | local logs | no `results.json` found |

`animal_testing_simulation.py` and `comprehensive_animal_study.py` have no committed results JSON. Status: **PLANNED**.

---

## 10. Truth Engine experiments

### EXP-TRUTH-UI

- Path: `truth_axis_evaluator/truth_engine.py`, `app.py`, `schema.py`
- Batch artifact: none in the repo (`truth_axis_results.jsonl` is a runtime export path, not a frozen file found by the scan).
- Status: **PLANNED** as a batch experiment. The module is software.

### EXP-TRUTH-AXES-125

- Path: `analyses/pass77_b125_four_truth_axes_audit/runner.py` → `results.json`
- Parallel read: 61 propositions, 3 LLM raters; Fleiss κ degree `0.486`, modality `0.436`, sep `0.305`, authority `0.213`; verdict `QUALIFIED` with sep/authority below 0.4.
- Status: **REPORTED**.

### EXP-TRUTH-AXES-143

- Path: `analyses/pass77_b143_quantum_truth_axes/quantum_truth_axes.py` → `results.json`
- Parallel read: `chsh_quantum_S=2.828427` equals the Tsirelson bound stored beside it. This is an algebraic check, not a dataset.
- Status: **REPORTED**.

### EXP-FLEISS

- `analyses/fleiss_5tier_2026_05_27/results.json`: `meanAccuracy=0.9233333333333335`.
- `analyses/fleiss_5tier_refined_NA_2026_05_27/results.json`: `n_gold_5tier_refined=500`, `fleiss_kappa_5tier_refined_gold=0.9235267555511723`.
- `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/results.json`: binary κ `0.5982903794731804` on `n_clean=998`; 5-tier κ `0.8864627351935783` on `n_clean=1000`.
- `analyses/dialetheism_rivals_2026_05_27/results_rivals.json`: 5TIER κ `0.9235`, FDE κ `0.9078`, LP κ `0.8529`, BIN κ `0.9154`.
- Status: **REPORTED**. Rater identities are in the runner (LLM calls). Raw rating tables may or may not be fully inside the JSON; this audit did not audit rater logs.

### EXP-MR-RATERS

- `analyses/mr_idc_f5_step3_llm_raters/results.json`: `n_items=15`, `openai_accuracy=0.0`, `anthropic_accuracy=0.933`, `kappa_correctness=0.0`.
- Status: **REPORTED**. The zero OpenAI accuracy with κ 0 is an internal inconsistency of the rating run worth reading in the JSON before reuse. This ledger does not diagnose the cause.

Axiom text vs schema: section 18.

---

## 11. Simulations

| Artifact | Script (when identified) | Stored summary | Status |
| --- | --- | --- | --- |
| `analyses/uop_phase_transition_v1/results.json` | `simulate.py` | 4/4 flags true; 10000 perturbations | REPRODUCIBLE |
| `analyses/uop_phase_transition_v2_3axis/results.json` | `model_3axis.py` | scan found no top-level verdict key | REPORTED |
| `analyses/affective_tralse_joules_2026_06_16/results_affective_tj.json` | folder script | `n_seeds=40`, `n_steps=120` | REPORTED |
| `simulations/active_pragmatism_results_2026-05-17.json` | matching `.py` | `N_TRIALS=1000`, seed `20260517`, `auc_advantage_mean=0.0424` | REPRODUCIBLE |
| `simulations/moot_failure_duality_results_2026-05-17.json` | matching `.py` | `N_TRIALS=1000`, `N_MC=500`, seed `20260518`, `auc_C_over_A_mean=0.0347` | REPRODUCIBLE |
| `simulations/lcc_virus_empirical_results.json` | `lcc_virus_empirical_test.py` | see EXP-LCC-VIRUS-EMP | REPORTED |
| `simulations/connectome_consciousness_results_v1`–`v8.json` | matching tests | see EXP-CELEG | REPORTED |
| `experiments/numpy_tralse_results.json` | `experiments/tralse_numpy_proof_of_concept.py` | standard accuracy `0.9667`, tralse `0.9639`, myrion `0.9222`, full_tralse `0.8667` | REPORTED |
| `experiments/dead_neuron_cascade_results.json` | `experiments/dead_neuron_cascade_proof.py` | `n_layers=50`, `n_trials=10` for relu and tralse | REPORTED |
| `experiments/myrion_superiority_results.json` | `experiments/myrion_contradiction_superiority.py` | nested; scan did not extract a headline number | REPORTED |
| `mood_amplifier_efficacy_results.json` | not confirmed | `n_subjects=100`, `mean_psi_correlation=1.0` | REPORTED — a mean correlation of exactly 1.0 on 100 subjects needs the generator read before any claim |
| `llm_collatz_test_results.json` | not confirmed | `n_problems=27`, `overall_accuracy=0.7037`, easy `1.0`, hard `0.4286` | REPORTED |
| `aimo_benchmark_results.json` | not confirmed | `n_problems=5`, `ti_accuracy=0.6`, `baseline_accuracy=0.4` | REPORTED |
| `verification/prediction_results.json` | not confirmed | prediction_1 p `1.37e-17`; prediction_2 p `0.323`; prediction_4 p `1.27e-4` | REPORTED |
| `verification/real_psi_results.json` | not confirmed | `n_paradigms=7`, mean effect `0.1251`, p `0.0268` | REPORTED |
| `verification/proper_meta_analysis_results.json` | not confirmed | fixed-effect p `0.194`, random-effect p `0.311` | REPORTED |
| `animal_testing_simulation.py` | no artifact | none | PLANNED |

`ti_sigma_graph.py` Monte Carlo: **UNREPRODUCED** (section 4).

---

## 12. Datasets and provenance

| Dataset | Path | Provenance stated in repo | Used by a saved result? |
| --- | --- | --- | --- |
| Riemann ordinates, 1e6 | `data/riemann_zeros/first_1million_zeros.txt` | Comment in `analyses/pass45_t6_pd_riemann/runner.py` cites Odlyzko `zeros1`. File has no header. First value `14.134725142` matches the known first zero. | Yes, `analysis_results.json`, PD runners, affine Odlyzko script |
| Riemann ordinates, other copies | `zeros_first_2million.txt`, `zeros_2million.txt` | No header read in this audit. Checksums not compared. | Not confirmed |
| Depresjon EEG | `analyses/lcc_depresjon/data/` | Study CSVs present | Yes, AUC artifact |
| Paleoclimate | `analyses/pass50_l2_paleoclimate_lcc/data/` plus `SOURCE_URLS.md` | Public ice-core text | `results.json` verdict string `PILOT_PRELIMINARY_DISCONFIRM` |
| OpenNeuro hyperscanning | `analyses/lcc_uop_openneuro/data/` | README; headers only | Experiment used synthetic data instead |
| DANDI NWB (000003, 000053, 000114, 000409, others) | not in `data/` | Streamed at runtime | Several **REPORTED** verdicts |
| sklearn toy sets | fetched by sklearn | public | EXP-UGI1 |
| TruthfulQA MC | `analyses/uop_abstention/truthfulqa_mc.json` | local JSON | EXP-UOP-ABSTENTION, EXP-GILE-TQA |
| Yahoo / stock caches | `data/yahoo_finance_cache/`, `data/stock_*` | fetched market data | EXP-GSA, if the window matches |
| Kaggle fixtures | `data/kaggle_s6e2/` | competition dump | not tied to a TI Sigma result in this ledger |
| SATLIB | `data/satlib_uf50/` | public SAT | `analyses/pass52_t51_h3_satlib_step_skip/results_raw.json` is a JSON list of length 200 |
| Personal device exports | `data/oura`, `polar_h10*`, `mendi`, `biowell*`, sleep, medication | device exports of one person | only Mendi has a completed numeric session analysis |
| C. elegans surrogate | inside `simulations/connectome_consciousness_test_*.py` | scripted, `n_synapses=4390` in v4 JSON | simulation scorecards |
| Zebrafish connectome | absent | — | no |

---

## 13. Null models and baselines (where the artifact states one)

| Experiment | Null or baseline stored |
| --- | --- |
| EXP-H4-SAT | permutation AUC mean `0.49928` |
| EXP-H4-R20 | confirm threshold `0.65` on inverted AUC; disconfirm threshold is in `PRE_REGISTRATION.json` (parallel read: `0.55`) |
| EXP-G25 | permutation null of Pearson r |
| EXP-UGI1 | 500 permutations; negative and positive synthetic controls, n=1600 |
| EXP-UOP-ABSTENTION | `uop_better_than_baseline=false`; scrambled caps |
| EXP-GSA | SPY same window |
| EXP-B4 | urb_645 phase order; match false |
| EXP-C6 / EXP-B42 | classical CHSH 2 and Tsirelson `2√2` |
| EXP-SIG-EXP | random constants in the ring range; P `0.437` |
| EXP-TIG-CHROMATIC | octahedron chromatic 3 |
| EXP-DEPRESSJON | AUC of raw C `0.520` beside CPS `0.681` |
| EXP-LCC-VIRUS-EMP | permutation p `0.4999` on n=2; MC 50000 |
| EXP-CELEG v6–v7 | confidence intervals; `phi_in_ci=false` |
| EXP-RETRIEVAL | chance `0.333` |
| EXP-FLEISS | binary κ vs 5-tier κ on the same items |
| `verification/proper_meta_analysis_results.json` | fixed vs random effects, both p > 0.19 |

Baselines that are only described in a paper and not stored next to a script are not listed.

---

## 14. Figures

| Location | Count in this audit | Role |
| --- | --- | --- |
| `analyses/**/*.png` | 45 | `pass77_b*/fig*.png`, written by `make_figs.py` in those folders. Illustrations of already-stored JSON, not independent results. |
| repo root `*.png` | 17 | Names match scripts: `ti_sigma_consensus_agents.png`, `tralse_joules_pipeline.png`, `twa_polarization_toy.png`, `lattice_fhs_e8.png`, `lattice_fhs_leech.png`, `lcc_token_stream_pilot.png`, `lcc_token_stream_multiseed.png`, `lcc_virus_full_pipeline.png`, `lcc_on_agent_trajectories.png`, `ai_corpus_lcc_test.png`, `riemann_ubki_*.png`, `monster_*.png`. A figure file is not a numeric result. |
| repo root `*.pdf` | 5 | `TI_SIGMA_6_*.pdf`. No `savefig` writer was confirmed. |
| `data/riemann_zeros/riemann_analysis.png` | 1 | paired with `analysis_results.json` |
| other png outside `data/` and `.lake` | 804 total including the above | many are assets, screenshots, or paper figures. Not inventoried one by one. |

No figure was regenerated in this audit.

---

## 15. Index of result JSON files

Scan date 2026-10-05. "Headline" is the first numeric or verdict fields the scanner printed. Empty headline means the object had no matching top-level key in the first nested pass. Status is **REPORTED** unless a section above upgrades it. `results.json` at the repo root is **not** a project artifact; it was an accidental write during audit exploration and was removed.

| File | Headline from scan |
| --- | --- |
| `aimo_benchmark_results.json` | n=5, ti_accuracy=0.6, baseline=0.4 |
| `analyses/affective_tralse_joules_2026_06_16/results_affective_tj.json` | n_seeds=40, n_steps=120 |
| `analyses/den_executive_network_2026_05_28/den_results.json` | F1 verdict string, per-being value 1.0 |
| `analyses/dialetheism_rivals_2026_05_27/results_rivals.json` | κ 0.924, 0.908, 0.853, 0.915 |
| `analyses/fleiss_5tier_2026_05_27/results.json` | meanAccuracy=0.92333 |
| `analyses/fleiss_5tier_refined_NA_2026_05_27/results.json` | n=500, κ=0.92353 |
| `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/results.json` | binary κ=0.598 (n=998); 5tier κ=0.886 (n=1000) |
| `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/spectrum_distinctness_results.json` | Theil U values |
| `analyses/gile_nonredundancy_test/results.json` | seed 20260628, n_perm 500, n_rows 52 |
| `analyses/gsa_residual_sharpe/results.json` | n=61, residual Sharpe 1.176 |
| `analyses/gsa_sharpe/results.json` | n_days=63, GSA Sharpe 1.144, SPY Sharpe 1.654 |
| `analyses/hmr_audit_urb608_urb639/results.json` | 6 and 5 examples scanned, 0 HMR candidates |
| `analyses/hmr_f2_3rater_verification/results.json` | n_examples=5, n_raters=3 |
| `analyses/lcc_bell_device_independence/results/results.json` | route_a reachable false |
| `analyses/lcc_conditional_proof/results/results.json` | observational proof cracked true; verdict UNSOUND |
| `analyses/lcc_depresjon/results/results.json` | n_dep=23, n_con=32, auc_CPS_full=0.681 |
| `analyses/lcc_dialogue/results.json` | no headline key |
| `analyses/lcc_dialogue/tmp_results.json` | no headline key |
| `analyses/lcc_oet/results/oet_results.json` | n_trials=1278, n_pairs=32 |
| `analyses/llm_consciousness_v1/results.json` | no headline key |
| `analyses/mep_calling_success_2026_05_28/mep_results.json` | H0 verdicts: indeterminate / spurious lift |
| `analyses/millennium_working_note_tests/results.json` | T1 direction rule true; not independent of known number theory |
| `analyses/mr_idc_f5_step3_llm_raters/results.json` | n=15, openai accuracy 0, anthropic 0.933, κ 0 |
| `analyses/mr_idc_f5_step3_multirater_v2/results.json` | n=15, n_raters=3, anthropic accuracy 0.933 |
| `analyses/pass25_m24a_rt_regression/results.json` | seed 31415927, per-map AUC min 0.683 |
| `analyses/pass26_g25_rt_fresh_corpus/results.json` | r=-0.00894, p=0.8396, DISCONFIRM |
| `analyses/pass26_r25_composite/results.json` | n_sat=221, n_unsat=79, AUC 0.704, CONFIRM_composite |
| `analyses/pass26_w25_weighted_centralization/results.json` | PARTIAL_RESCUE |
| `analyses/pass29_b27_bowtie_4wing/results.json` | N=57, CONFIRM_PROJECTION |
| `analyses/pass29_e27_lcc_plant_auxin/results.json` | 7/7, CONFIRM |
| `analyses/pass29_f24_icell_centralization/results.json` | n_graphs=100, r=0.4614, PARTIAL |
| `analyses/pass29_g25_retirement/results.json` | r=-0.0108, ACCEPT_RETIREMENT |
| `analyses/pass29_k27_kuramoto_bloch/results.json` | N=50, CONFIRM |
| `analyses/pass29_m27_myrion_lim/results.json` | seed 23571113, CONFIRM |
| `analyses/pass29_r24_composite_audit/results.json` | composite AUC 0.7582, best component 0.7508, DOMINANT_COMPONENT |
| `analyses/pass29_u27_utfe_lcc/results.json` | n_networks=200, r=0.0547, REJECT |
| `analyses/pass32_dandi_3way/results.json` | MIXED, n_eligible=2 |
| `analyses/pass33_qc25_ibmq_5qubit/results.json` | n_qubits=5, n_shots=1024, p=0.653, CONFIRM |
| `analyses/pass36_e35a_lcc_p3b/results.json` | INELIGIBLE |
| `analyses/pass37_dandi_e36d/results.json` | MIXED ineligible/timeout |
| `analyses/pass38_mbe_celebrity_numerology/results.json` | n=12, PARTIAL_NEG |
| `analyses/pass39_mbe_control_roster/results.json` | verdict NULL |
| `analyses/pass40_mt_ushape_exception/results.json` | N_samples=100000, MT FAILS |
| `analyses/pass42_p41b_pilot/results.json` | n=24, scores for 19, DESCRIPTIVE |
| `analyses/pass43_mendi_session_analysis/results.json` | n_frames=2406 |
| `analyses/pass45_qc26_ghz5_mermin/results.json` | 5 qubits, 1024 shots, 3 settings, CONFIRM, `actually_on_hw=true` |
| `analyses/pass45_t6_pd_riemann/results.json` | n_zeros=100000, INDETERMINATE |
| `analyses/pass47_o26_meta_indeterminate_test/results.json` | n_propositions=6, CONFIRM |
| `analyses/pass47_p46a_pd_4options/results.json` | n_zeros=100000 |
| `analyses/pass47_p46b_qc26_v2/results.json` | INCOMPLETE |
| `analyses/pass47_p46c_t45_3_gm_node/results.json` | parallel read Cohen d 8.916; scan truncated |
| `analyses/pass47_p46c_t45_4_mr_truth_kappa/results.json` | CONFIRM; parallel read n_propositions=100 |
| `analyses/pass47_p47a_t45_3_margin_retests/results.json` | large rater payload |
| `analyses/pass49_d4_qc26_mr_reclassification/results.json` | per-setting aggregate |
| `analyses/pass49_l1_lcc_markets/results.json` | NULL_NOISE |
| `analyses/pass49_program_a_bidirectional_lcc/results.json` | NULL_NOISE_HOLDOUT |
| `analyses/pass49_program_a_primary_dyad6/results.json` | PRIMARY_NULL |
| `analyses/pass49_wave1/t49_1_results.json` | not expanded |
| `analyses/pass49_wave1/t49_2_results.json` | not expanded |
| `analyses/pass49_wave1/t49_5_results.json` | not expanded |
| `analyses/pass49_wave1/t49_6_results.json` | not expanded |
| `analyses/pass49_wave1_v2_aa/t49_1_v2_results.json` | not expanded |
| `analyses/pass50_l2_paleoclimate_lcc/results.json` | PILOT_PRELIMINARY_DISCONFIRM |
| `analyses/pass51_d51_rnd3_dual_threshold_empirical/results.json` | Q1_first_N_p95_below_T_RAND=1000 |
| `analyses/pass51_t51_batch_exec/results.json` | nested TDA and Polar keys; see section 7 |
| `analyses/pass52_t51_h3_satlib_step_skip/results_raw.json` | JSON list length 200 |
| `analyses/pass77_b108_pd_truthlabel_link_2026_06_06/comparison_results.json` | not expanded |
| `analyses/pass77_b115_wellbeing_weighted_concentration/results.json` | not expanded |
| `analyses/pass77_b120_crank_credibility/crank_credibility_results.json` | not expanded |
| `analyses/pass77_b121_gile_intelligence_truth/gile_intelligence_results.json` | see EXP-GILE-SIM-121 |
| `analyses/pass77_b122_substantive_not_circular/contamination_results.json` | not expanded |
| `analyses/pass77_b125_four_truth_axes_audit/results.json` | see EXP-TRUTH-AXES-125 |
| `analyses/pass77_b129_quantum_connectome_mood_amplifier/hw_results.json` | hardware block |
| `analyses/pass77_b129_quantum_connectome_mood_amplifier/results.json` | not expanded |
| `analyses/pass77_b130_lcc_hyperscanning_e3/results.json` | see EXP-HYPERSCAN |
| `analyses/q_pre_baseline_audit/results.json` | Q_pre baseline present |
| `analyses/r_hmr_unbounded_construction_k15/results.json` | parallel read cardinality 19 at k=15 |
| `analyses/tpi_f3_empirical_yerkes_dodson/results.json` | F3 block present |
| `analyses/tsc_h4_sat/results.json` | AUC 0.2678, p_perm 1.0 |
| `analyses/tsc_h4_sat_r20_replication/results.json` | inverted AUC 0.7318, CONFIRMED |
| `analyses/uop_abstention/gile_results.json` | n=120, selective accuracy 0.8583 |
| `analyses/uop_abstention/results.json` | accuracy 0.8233, uop_better_than_baseline false |
| `analyses/uop_phase_transition_v1/results.json` | n_confirmed 4 |
| `analyses/uop_phase_transition_v2_3axis/results.json` | no headline key |
| `data/riemann_zeros/analysis_results.json` | 1e6 zeros, all_on_critical_line true |
| `data/riemann_zeros/twa_analysis_results.json` | fraction_gile_continuous 0.5; all_zeros_in_interval true |
| `de_photon_jeff_time_test_results.json` | verdict HIGHLY COMPATIBLE |
| `enhanced_monster_test_results.json` | ENHANCED TESTS PASSED |
| `etj_pilot_results_20260525_001526.json` | no headline key |
| `experiments/dead_neuron_cascade_results.json` | 50 layers, 10 trials |
| `experiments/myrion_superiority_results.json` | nested |
| `experiments/numpy_tralse_results.json` | accuracies 0.967, 0.964, 0.922, 0.867 |
| `figures/urb_700_p1_p4_results.json` | n_samples=100000 |
| `figures/urb_705_scaling_results.json` | no headline key |
| `figures/urb_722_eeg_analysis_results.json` | lepton_predicted 1.87, lepton_measured 1.889 |
| `lcc_hypercomputer_test_results.json` | no headline key |
| `llm_collatz_test_results.json` | n=27, accuracy 0.704 |
| `monster_group_test_results.json` | no headline key |
| `mood_amplifier_efficacy_results.json` | n_subjects=100, mean_psi_correlation=1.0 |
| `papers/urb_751_pipeline_validation_result.json` | pipeline_status VALIDATED, duration_s=600 |
| `papers/urb_752_hrv_pipeline_validation_result.json` | in_predicted_range true, lepton_ref 1.889 |
| `papers/urb_763_pmns_triality_check_result.json` | no headline key |
| `pilots/h4_face_brandon_jeffrey/results.json` | JSON list length 20 |
| `simulations/active_pragmatism_results_2026-05-17.json` | auc_advantage_mean 0.0424 |
| `simulations/bengston_jse_meta_analysis_2026-05-22_results.json` | no headline key |
| `simulations/bengston_tsis_evaluation_2026-05-21_results.json` | N_per_arm=33, falsifier NOT REFUTED (replication not executed) |
| `simulations/connectome_consciousness_results.json` | free-will verdict INDETERMINATE |
| `simulations/connectome_consciousness_results_v2.json` through `v8.json` | see section 9 |
| `simulations/eight_principles_test_battery_2026-05-22_results.json` | no headline key |
| `simulations/fleiss_kappa_llm_raters_2026-05-22_results.json` | κ 0.773, 0.839, 0.837 |
| `simulations/lcc_virus_empirical_results.json` | n_sessions=2, permutation_p=0.4999, MC 50000 |
| `simulations/moot_failure_duality_results_2026-05-17.json` | auc_C_over_A_mean 0.0347 |
| `simulations/pass_73_b6_results_2026-05-24.json` | no headline key |
| `simulations/pass_74_b4_f8_results_2026-05-24.json` | accuracy strings 7/10 |
| `simulations/tss_emp_3_utility_sweep_results_2026-05-17.json` | N_TRIALS=1000, N_MC=300 |
| `simulations/tss_emp_5_negative_control_results_2026-05-17.json` | N_TRIALS=1000, N_MC=500 |
| `simulations/tss_math_4_lindley_immunity_results_2026-05-17.json` | N_MC=300 |
| `simulations/urb411_results.json` | norm 0.25 |
| `simulations/urb412_results.json` | companion_determinant 1.0 |
| `ternary_benchmark_results.json` | information_density_gain 58.50 |
| `verification/prediction_results.json` | mixed p-values |
| `verification/proper_meta_analysis_results.json` | p 0.194 and 0.311 |
| `verification/real_psi_results.json` | n_paradigms=7, p=0.0268 |
| `zenodo_upload_results.json` | JSON list length 10 |

Additional `pass77_b132`–`b168` and `pass77_b4*` / `pass77_b54` / `pass77_b67` / `pass77_b68`–`b81` result files exist (the scan listed 191 JSON files and the table above is the portion whose headlines were captured before truncation of the scanner printout). Paths not given a headline in this table were not given invented numbers. A complete path list is recoverable with:

```bash
find analyses experiments simulations data verification papers figures pilots \
  -name '*result*.json' -o -name 'results.json' | sort
```

IBM hardware rows (`pass33`, `pass45_qc26`, `pass77_b54`, `pass77_b67_clv1_ibm_hw`) store shot counts and verdicts. Tokens and backends are not in this ledger. Status **REPORTED**. They cannot be reproduced without IBM credentials and the same backend calibration.

---

## 16. Scripts that produced a stored result

| Script | Artifact |
| --- | --- |
| `lean4/verify_theorems.py` | stdout only; 9/9 in this audit |
| `analyses/tsc_h4_sat/tsc_h4_sat_prototype.py` | `analyses/tsc_h4_sat/results.json` |
| `analyses/tsc_h4_sat_r20_replication/r20_replication_runner.py` | `results.json` |
| `analyses/crystal_b4_hamiltonian/tsc_hamiltonian.py` | `results.txt` |
| `analyses/crystal_c5_symmetry/tsc_symmetry.py` | `results.txt` |
| `analyses/crystal_c6_chsh/tsc_bec_chsh_prediction.py` | `results.txt` |
| `analyses/tsc_signatures_pass9/tsc_signatures_table.py` | `results.txt` |
| `analyses/tsc_signature_expansion/expansion.py` | `results.txt` |
| `analyses/pass77_b42_crystal_falsifiers/run_falsifiers.py` | `results.txt` |
| `analyses/pass77_b68_meijer_octahedron_vs_ti/run_compare.py` | `results.json` |
| `analyses/gile_nonredundancy_test/gile_nonredundancy_test.py` | `results.json` |
| `analyses/uop_phase_transition_v1/simulate.py` | `results.json` |
| `analyses/uop_abstention/analyze.py` | `results.json` |
| `analyses/uop_abstention/gile_analyze.py` | `gile_results.json` |
| `analyses/pass43_mendi_session_analysis/analyze.py` | `results.json` |
| `analyses/pass51_t51_batch_exec/run_all.py` | `results.json` |
| `analyze_riemann_zeros.py` | `data/riemann_zeros/analysis_results.json` |
| `riemann_twa_analysis.py` | `data/riemann_zeros/twa_analysis_results.json` |
| `simulations/connectome_consciousness_test_v4_302neuron.py` | `connectome_consciousness_results_v4.json` (zebrafish row not included) |
| `simulations/lcc_virus_empirical_test.py` | `lcc_virus_empirical_results.json` |
| `experiments/tralse_numpy_proof_of_concept.py` | `experiments/numpy_tralse_results.json` |
| `experiments/dead_neuron_cascade_proof.py` | `experiments/dead_neuron_cascade_results.json` |
| `ti_sigma_graph.py` | no artifact |

Pass runners under `analyses/pass*/runner.py` or `run.py` pair with the `results.json` in the same folder. That pairing was checked by directory convention, not by executing them.

---

## 17. Results that cannot currently be reproduced

| Item | Why |
| --- | --- |
| Every Lean theorem | `lean`/`lake` absent; no module `.olean` |
| EXP-TIG-SIR | no saved output |
| EXP-ZEBRA | print-only; no row in JSON; no connectome |
| EXP-TRUTH-UI | no frozen batch file |
| DANDI / IBL / rodent LFP verdicts | raw NWB not in the repo |
| IBM hardware CHSH / GHZ / CLV1 | credentials and device noise |
| EXP-UOP-ABSTENTION re-score | needs the environment that has sklearn and the original model outputs; `predictions.jsonl` is present so the analyzer could be re-run if dependencies are installed |
| EXP-T51-5 LF/HF | export has no RR intervals |
| OpenNeuro EEG binaries | headers only |
| `animal_testing_simulation.py` | no output file |
| README fine-structure "99.71%" | prose; Lean theorem has `sorry` |
| Millennium Lean headlines | axioms, and in several files `sorry` |

## 18. Inconsistencies

1. **`LCC_HIGH` / `LCC_RADIANT` names.** `lean4/TISigma.lean` and `lean4/verify_theorems.py`: `LCC_HIGH = 1/√2 ≈ 0.7071`, `LCC_RADIANT = 1/φ ≈ 0.6180`. `ti_sigma/constants.py`: `LCC_EMERICK = 1/√2`, `LCC_TRUE = φ-1`, `LCC_HIGH = C_EMERICK + (√2-1) ≈ 0.8512`, `LCC_RADIANT = sqrt(e/π) ≈ 0.9306`. Callers of the Python package (`oracle_bus.py`, `aperiodic_optimizer.py`) use the Python meanings. The Lean file header and `verify_theorems.py` describe 0.707 as the crossover. **INCONSISTENT.**

2. **Extended Euler vs threshold story.** Theorem 5 is the identity `exp(iπ) + 1 = 0` rewritten with `1 = √2·φ·C_EMERICK`. It holds because `C_EMERICK` is defined as `1/(φ√2)`. It does not constrain `LCC_HIGH` or `LCC_RADIANT`. The Python file comment presents the same identity as tying levels 3, 5, and 7. That algebra is **VERIFIED** as an identity. Using it as evidence for the Python threshold ladder is not supported by the identity.

3. **TI-G H2.** Docstring requires Crystal ≤ TI-G < ER. Code pass flag is Crystal ≤ ER. **INCONSISTENT.** No numeric run is stored.

4. **Truth Engine uncertainty.** `theories/TI_TRUTH_ENGINE_AXIOMS.md` says uncertainty is not `1 - MR`. The JSON template in the same file sets `"value": "1.0 - MR_i"`. **INCONSISTENT.**

5. **H4 direction.** `analyses/tsc_h4_sat/results.json` AUC `0.2678`, verdict weak, permutation p `1.0` for lower-energy ⇒ SAT. `analyses/tsc_h4_sat_r20_replication/results.json` inverted AUC `0.7318`, verdict CONFIRMED. Both can be true. They are not one result.

6. **Crystal phase order.** `analyses/crystal_b4_hamiltonian/results.txt` says `Match: False` against the urb_645 order. Any prose that states the urb_645 order was observed on this Hamiltonian is **INCONSISTENT** with the artifact.

7. **RH "all zeros on the critical line".** `data/riemann_zeros/analysis_results.json` sets `all_on_critical_line=true` with `sigma=0.5` for a file of ordinates. The input file stores imaginary parts only. The flag records the loader's assumption. It is not a test of RH.

8. **Lean "formally verified" headers** (`lean4/TISigma.lean`, `lean4_collatz/CollatzNu2.lean`, attached_assets downloads) versus absence of compile artifacts. **INCONSISTENT** if "verified" means machine-checked in this repo.

9. **Connectome scorecard.** `run_scorecard` in the v4 script hard-codes several criteria `True`. A score such as v5 `11/13` or v6 `12/13` mixes computed flags and constants. **INCONSISTENT** to read the fraction as 13 independent tests.

10. **GILE weights.** `ti_sigma/constants.py` uses G=0.42. `bok_virus_engine.py` uses a different G weight (`ET`). Two definitions, one name. **INCONSISTENT** across modules.

11. **`mood_amplifier_efficacy_results.json`.** `mean_psi_correlation=1.0` with `n_subjects=100`. Exact unity is a property to inspect in the generator before reporting. Not independently recomputed here.

12. **MR rater file.** `openai_accuracy=0.0` and `kappa_correctness=0.0` beside `anthropic_accuracy=0.933` on 15 items. The artifact records that split. It is not a stable inter-rater result.

## 19. Results whose original raw data are missing

| Claimed or stored result | What is missing |
| --- | --- |
| Zebrafish Φ at N=10000 | no animal data; no stored prediction row |
| DANDI rodent / IBL verdicts | NWB files not in the repo |
| EXP-T51-5 LF/HF | RR interval series |
| OpenNeuro hyperscanning re-analysis | `.eeg` binaries (0 files) |
| EXP-TIG-SIR hypotheses | the Monte Carlo output |
| EXP-TRUTH-UI | exported `truth_axis_results.jsonl` |
| Oura / Biowell scientific claims in prose | no analysis artifact |
| IBM hardware probabilities | device job IDs and raw counts may be inside JSON; the device is not |
| Riemann 2-million files | no checksum or header tying them to a release |
| Plant auxin 7/7 CONFIRM | this audit did not find an external measurement table; treat raw data as **unconfirmed** |
| Personal session claims beyond the one Mendi CSV | other device exports are not reduced to a result file |

## 20. What was not inferred

- No zebrafish Φ value.
- No re-run of the 191 JSON files.
- No Lean type-check.
- Nested fields that this process did not open are marked as parallel reads or omitted.
- Paper and book claims of "Lean verified", "99.71% accuracy", sacred-interval laws, and consciousness thresholds are not given experiment IDs unless a script artifact exists.

## 21. Integrity reclassification

Applied against `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. This section does not add results. It stops several stored or printed objects from being read as confirmation.

### 21.1 Evidence class

| Object | Class | Why |
| --- | --- | --- |
| `lean4/verify_theorems.py` 9/9 | VERIFIED | Floating-point identity check under Lean names. Not empirical validation. |
| Crystal B.4 `Match: False` | REPRODUCIBLE | Negative result. Kept. |
| H4 AUC 0.2678, p_perm 1.0 | REPRODUCIBLE | Failed original direction. Not converted into the R20 confirmation. |
| H4-R20 inverted AUC 0.7318 | REPRODUCIBLE | A different, pre-registered hypothesis. |
| GILE real-data G, L, E non-significant | REPRODUCIBLE | Negative results. Kept. |
| UOP `uop_better_than_baseline=false` | REPORTED | Negative result. Kept. |
| Pharma Pass-6 margin +8.3 pp, not +35 pp | REPORTED | `analyses/pharma_baseline/results_2026-05-08.txt`. The file itself rejects the book figure. |
| Zebrafish N=10000 print label | HYPOTHESIS | No stored row, no connectome. |
| Radiant / G* / Born-shaped formulas | HYPOTHESIS | Framework-internal. Not experimentally resolved. |
| FAAH-OUT therapy, Jo Cameron phenotype as a TI result | HYPOTHESIS | Literature and pitch prose. No wet-lab artifact. No zebrafish ortholog file. |
| LLM rater κ and Truth Engine UI | REPORTED or PLANNED | LLM output is not evidence of the claim being rated. |
| Millennium Lean headlines | HYPOTHESIS | Gap axioms. Not proofs. |

A simulation, including UOP phase transition, connectome scorecards, and GILE intelligence sims, is not empirical validation. A Pearson r, including DANDI coupling, is not causation. A hardcoded literature percentage is not a TI Sigma confirmation.

### 21.2 Thresholds that stay separate

These are not one constant. No experiment in this audit resolves them into each other.

| Symbol in the rules | What the repo currently writes | Class |
| --- | --- | --- |
| `√2 − 1` | `LCC_TRALSE` in `ti_sigma/constants.py`; Emerick Threshold `ET` and the canonical G weight in `papers/GILE_DEFINITION_CANONICAL_2026-07-04.md` | Definition. Using it as both a gate and a GILE weight is a modeling choice, not a measurement. |
| 0.93 Radiant | At least three formulas: Python `sqrt(e/π) ≈ 0.9306`; canonical `G* = √(1 − e^{−2}) ≈ 0.92987`; prose `1 − e^{−e} ≈ 0.934` | INCONSISTENT formulas. Each is HYPOTHESIS until an experiment distinguishes them. |
| `T` | Used for different objects (tralse region, a diagram constant `1 − e^{−e}`, truth labels). Not a single frozen threshold. | INCONSISTENT name. |
| `φ` | `(1+√5)/2`. Algebraic. | Definition. Not a biological threshold. |
| Born-shaped value | Canonical paper: `Existence = (G*)² = 1 − e^{−2} ≈ 0.865` | HYPOTHESIS. Distinct from G* and from `C_EMERICK`. |
| Emerick Constant | `C = 1/(φ√2) ≈ 0.437016024448821` | Algebraic definition. Distinct from `√2 − 1` and from 0.93. |

### 21.3 Elegance and Goodness

`papers/GILE_DEFINITION_CANONICAL_2026-07-04.md` defines Elegance as beauty of form and Goodness as the mean of four facets: Coherence, Concreteness, Continuity, Consistency. Older URBs use a different quartet: Clarity, Coherence, Compassion, Courage. A search did not find an operational definition named "8Cs" in code or in that canonical file.

The integrity rule requires Goodness through the 8Cs. That operationalization is not implemented on this branch. Status of "8Cs" in the 2026-10-14 audit of this tree: **HYPOTHESIS** (named in the rules, absent here as a measurement protocol).

2026-10-20 addendum. The product commit `58e78046` does contain a Stage A v3 draft (`NEW_CANONICAL_DRAFT`, `paid_collection_started` false). `analyses/eight_c_instrument_2026_10_20/` recomputes that commit’s mock. Exact-match 0.0 matches the runner default seed `TI_SIGMA_STAGE_A_V3_MOCK` with `vary_by_attempt`. The registered seed `TI_SIGMA_STAGE_A_V3_REGISTERED` does not match the stored JSON. The mock draws Goodness from its own hash key. A seeded weight simulation (seed 20261020) keeps rankings fixed for proportional profiles and moves them for independent profiles. That simulation assigns no domain weight. Eight-C κ remains absent. The draft is still not a validated manifold. A later pass on the same analysis compared the stored corpus-balance prose with the item JSONL and marked that prose INCONSISTENT: its domain counts sum to 23. Schema failures on the 63 mock records are 0. Goodness ICC(1,1) on the hash attempts is about −0.088. The rating-dependent Stage A primaries remain blocked.

Overlap flags, not confirmations:

| Feature | Overlaps | Where |
| --- | --- | --- |
| E = `−log(decision-tree node count)` | compression / complexity, not a separate beauty measurement | `analyses/gile_nonredundancy_test/gile_nonredundancy_test.py` lines 21 and 312–313 |
| G = `−mean std` of bootstrap probabilities, called a "Four-C proxy" | stability / one coherence facet, not four or eight facets | same file, lines 23–24 |
| Book gloss "Elegance is least action" | HEM, pragmatic success | `book/ch21_ethics.md`, `book/ch27_enlightenment.md` |
| Canonical note that E overlaps HEM presence | HEM | `papers/GILE_HEM_NONTECHNICAL_SUMMARY_2026-05-17.md` |
| `G + I → accuracy` chord | Intuition absorbed into a joint accuracy claim | canonical GILE file, section 1 |

On the 52-row real table, E is not non-redundant. That negative result stands. It does not show that Elegance-the-construct failed, because the feature is a compression proxy.

### 21.4 TIC and TIG

They are not one object in the artifacts.

| Object | Vertices | Artifact |
| --- | --- | --- |
| Crystal / TSC Hamiltonian | 57 | `analyses/crystal_b4_hamiltonian/results.txt` |
| B68 graph called TIG | 9 | `analyses/pass77_b68_meijer_octahedron_vs_ti/results.json` |
| `ti_sigma_graph.py` TI-G | 57, "same nodes and ring assignments as the TSC Crystal" | no epidemic artifact |

`papers/PASS_77_B74_...md` records a prose ruling that the canonical TSC is the 57-vertex object and the 9-vertex object is TIG. That sentence is a **HYPOTHESIS / naming ruling**, not a frozen code version. `ti_sigma_graph.py` still builds the epidemic graph from the crystal's rings. No canonical hash or version pin exists for either graph. Biological prediction from either graph is not licensed by a frozen canonical version.

### 21.5 Biology

Search of the repo found no zebrafish FAAH-OUT ortholog sequence, alignment, or experiment. The connectome script's "Zebrafish" label is a size on a power-law printout.

Jo Cameron appears as:

- pitch and book prose (`blissgene_slides_content.md`, `book/ch15_lcc.md`, which calls the FAAH sweep simulation-only)
- a hardcoded row in `analyses/pharma_baseline/linear_baseline.py`: `("E05", 100.0, 134.3, 5)` commented "Jo Cameron -> full FAAH stack"

That row is a literature percentage placed next to a simulator output. It is not a therapeutic-effect measurement, not a human trial, and not a zebrafish result. Class: **HYPOTHESIS** for any translational claim. The Pass-6 baseline file is a **REPORTED** comparison of those hardcoded numbers, and it preserves the negative finding that the book margin is not reproduced.

### 21.6 Model competition

A TI Sigma model does not win by producing a pattern. The four required comparisons are: simple baseline, conventional scientific baseline, capacity-matched generic model, randomized or null model.

| Experiment | Simple | Conventional | Capacity-matched | Null | Outcome |
| --- | --- | --- | --- | --- | --- |
| Pharma Pass 6 | mean, median, majority, coin-flip | stack-size linear LOO | not present | coin-flip | Directional 100% ties majority, because 12/12 effects are positive. Magnitude 75% vs mean-magnitude 66.7% (+8.3 pp). Book "+35 pp / 46% linear" is not in this file. |
| GILE non-redundancy | permutation | linear ΔR² | random forest is the nonlinear arm, not a separate capacity-matched non-TI model | 500 perms; synthetic controls | I only, on this proxy |
| H4 SAT | permutation AUC | none | none | permutation mean 0.499 | original direction fails |
| Crystal B.4 | urb_645 order (not matched) | none | none | none | negative |
| 9-vertex TIG | octahedron chromatic 3 | none | none | none | chromatic-3 claim fails |
| UOP abstention | raw threshold | isotonic / scrambled cap as stored | not separated | scrambled caps | UOP not better |

No other indexed experiment was shown to have all four comparisons.

### 21.7 Negative results kept

These stay in the record as failures or ties. They are not re-read as confirmation.

- Crystal B.4 order mismatch
- H4 lower-energy AUC 0.268
- GILE G, L, E on the real 52-row table
- UOP abstention `uop_better_than_baseline=false`
- Pharma directional tie with the majority baseline, and the +8.3 pp margin instead of +35 pp
- DANDI P3b `INELIGIBLE` and the mixed 3-way
- IBL and rodent mood F-tests stored as `REFUTED` where the artifact says so
- Polar LF/HF with zero sessions
- MR rater κ of 0 for correctness on the OpenAI arm

### 21.8 What this file is

AI-assisted file inventory, 2026-10-05. Human-authored rules live in `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. Suggestions in section 21 are audit notes. They are not new scientific hypotheses and they were not independently verified beyond the citations above.
