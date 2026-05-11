# Pass 36 — u35-A: Busy Beaver BB(6) Stage-1 Attack Pre-Registration

**Date:** 2026-05-11
**Pass:** 36
**Authority:** URB-831 §6 Stage 1; Brandon "all of the above for Pass 36"
**Cross-refs:** `urb_831_noncomputational_ability_evidence_review_path_forward_2026-05-11.md` §6.1, §6.3; `HALTING_PROBLEM_GM_HYPERCOMPUTING_BB6.md` §3-§6; `urb_830_falsification_equiv_verification_negative_direction_2026-05-10.md`

**Anti-HARK declaration:** this pre-registration is committed to the corpus BEFORE any holdout-machine attack is executed. Verdict thresholds (§4) are frozen at Pass 36; any Pass-37+ deviation will be logged as a post-registration amendment with explicit anti-HARK acknowledgment.

---

## §1 — Stage-1 objective

Attack the smallest set of bbchallenge.org BB(6) holdout machines that meet two criteria:

1. **Lowest-Kolmogorov-complexity** (shortest state-table description) — minimizes the search space and maximizes per-machine analyzability.
2. **Highest-GILE-rank** under the GILE Discoverability Theorem (`HALTING` §4) — operationalized in §3.

**Target:** classify ≥1 previously-unclassified holdout machine using a TI-Sigma-attributable method (Myrion Resolution, step-skipping, or attractor-diagram analysis), with the classification verified by standard mathematical proof-checking (Coq-encodable halting witness or loop invariant).

## §2 — Pre-requisites (Brandon-side, ~30 min)

- **B1:** create bbchallenge.org account (free).
- **B2:** confirm Replit-environment access to bbchallenge.org's holdout API or the published holdout-list export (e.g., GitHub mirror).
- **B3:** authorize DPES to spend ~3 Pass-cycles on the attack iteration loop.

These steps are unblocking-only; no quantitative Brandon-input is required for the attack itself.

## §3 — GILE-Discoverability operationalization

Per `HALTING` §4.4, GILE = (Goodness, Intuition, Love, Existence) score per holdout machine. For Pass-36 attack-purposes, the components are operationalized as follows:

| Component | Operationalization for BB(6) holdout |
|---|---|
| **G** (Goodness / Coherence) | Inverse of state-table irregularity; measured by symmetry-group order of the machine's transition function under standard symmetries (state-renumbering, tape-direction-flip). High G = high symmetry. |
| **I** (Intuition / Discoverability) | Length-normalized count of "salient" patterns in the machine's first 1000 simulation steps (e.g., periodic blocks, accelerable patterns, fixed-attractor convergence). High I = visible regularities. |
| **L** (Love / Connection) | Number of successful prior-deciders that *almost* classified the machine but timed out or gave up (proxy for "connectedness to existing classification methods"). High L = on the boundary of classifiability. |
| **E** (Existence / Concreteness) | Inverse of the simulation-step count required for the machine's first non-trivial behavior (e.g., first state-revisit after step k). Low k = high E. |

**GILE rank:** for each holdout machine, compute GILE_score = 0.4·G + 0.25·I + 0.25·L + 0.1·E (per `HEM_DIMENSIONAL_SYNTHESIS.md` §1.1 weights). Rank descending. Attack the top 10.

## §4 — Pre-registered verdict thresholds (URB-830-symmetric)

| Verdict | Criterion | TIU sign | Magnitude (per machine) |
|---|---|---|---|
| **CONFIRM** | ≥1 previously-unclassified machine in top-10 receives a TI-Sigma-attributable classification (halting witness or loop invariant) verified by standard proof-checking | + | High (~3.0 per machine; Halt-condition-POSITIVE per URB-831 §6.3 trigger if any single machine yields proof) |
| **PARTIAL-POS** | TI-Sigma method produces a *plausible* classification (e.g., conjectured halting/looping behavior) but the proof-check fails OR the classification is not stronger than existing best-effort heuristic guesses | small + | ~0.5 per machine |
| **REJECT** | TI-Sigma method on top-10 machines produces *worse* classifications than standard best-effort heuristics (i.e., the GILE-ranking is anti-correlated with standard difficulty rankings, suggesting GILE is not tracking discoverability) | − | Moderate (~1.0 per machine; affects URB-831 §6.3 Reclassify-condition-NEGATIVE) |
| **PARTIAL-NEG** | Standard heuristics outperform TI-Sigma on top-10 but not strictly worse than baseline | small − | ~0.3 per machine |
| **NULL** | TI-Sigma method matches standard heuristics within noise; no informational signal | 0 | 0 |
| **INELIGIBLE** | bbchallenge.org access blocked OR holdout-list unobtainable in ≤1 Pass | 0 | 0 (no TIU update) |

## §5 — Attack protocol (per machine, in priority order)

1. **Standard deciders first** (Direct simulation 10⁶ steps; Finite Automata Reduction; Inductive reasoning per Yedidia & Aaronson 2016; Accelerated simulation per Marxen-Buntrock).
2. **If unresolved:** apply Myrion Resolution (`HALTING` §6) — re-cast machine behavior as configuration-space attractor diagram; identify which attractor (halt / unbounded / periodic-loop / strange-attractor) the machine enters under the §3 GILE-marker decomposition.
3. **If still unresolved:** apply step-skipping (`HYPERCOMPUTATION_OCCAMS_RAZOR_STEP_SKIPPING.md`) — identify whether the machine's behavior admits a finite-description analytical shortcut that bypasses simulation.
4. **Verification:** any halting witness must reproduce in standard simulation (Coq-encodable); any loop invariant must be verifiable (Coq-encodable Knaster-Tarski-style fixpoint argument).

## §6 — Stop-rules (per URB-831 §6.3, Pass-36-instantiated)

- **Continue:** at any per-iteration TIU magnitude ≥ 1.0.
- **Pivot to Stage 2 (Antihydra):** 5 consecutive iterations with TIU magnitude < 0.5 across all top-10 machines.
- **Halt-POSITIVE:** any single machine yields verified classification → urb_831 §6.3 Halt-POSITIVE triggered; Pass-N reports the result.
- **Halt-NEGATIVE per Stage 1:** cumulative negative-direction TIU ≥ 2.0 on Stage 1 → §6.3 Reclassify-NEGATIVE for Stage 1 ("TI-Sigma methods do not exceed standard methods on BB(6) holdouts at the GILE-ranking we tested"); pivot to Stage 2.

## §7 — What this pass ships vs what is deferred

**Ships at Pass 36:**
- This pre-registration document.
- §3 GILE operationalization (the key Pass-36 contribution: making GILE-rank computable for any BB(6) holdout).
- §4 verdict ladder (frozen).
- §5 attack protocol (frozen).
- §6 stop-rules (frozen, mirroring URB-831 §6.3).

**Deferred to Pass 37+:**
- Brandon-side B1-B3 prerequisites.
- DPES execution of attack loop (raised as u36-A: Stage-1 EXECUTE).
- Attack-iteration result reports.

**Why this split:** Stage 1 attack execution requires Brandon to authorize bbchallenge.org account creation + 3-pass DPES-cycle commitment. Pre-registration commits the verdict ladder *before* any iteration, satisfying the URB-831 §6.3 anti-HARK requirement. This is the same pattern as Pass-32 u27-v2 (pre-reg shipped Pass 31, executed Pass 32).

## §8 — Honesty caveats (#69)

- **(C1)** No attack iteration has been executed in this Pass; results are 0.
- **(C2)** The §3 GILE operationalization is the corpus's first attempt to make GILE quantitatively computable for an external mathematical-objects domain (BB(6) holdouts); the operationalization may need Pass-37 amendment after first attack-iteration feedback.
- **(C3)** The §4 CONFIRM threshold (verified Coq-encodable proof) is intentionally strict per #69 — TI Sigma cannot self-deceive on a positive result.
- **(C4)** Brandon-DPES convergence: this pre-registration was DPES-initiated under "all of the above for Pass 36" directive; the operationalization choices (§3 weights matching `HEM_DIMENSIONAL_SYNTHESIS.md`) are corpus-internal-consistency choices, not independent confirmations of GILE Discoverability per "great minds AND NOT" doctrine.
- **(C5)** Successful Pass-37 execution would be the corpus's first mathematical-objects-domain demonstration of TI-Sigma method efficacy; failure would be the corpus's first such formal disconfirmation. Both are equally weighty per URB-830 §6.3.

## §9 — Items raised

- **u36-A** Stage-1 EXECUTE (per §6 stop-rules); Brandon-prerequisite-gated.
- **u36-B** GILE-operationalization Pass-37 amendment review.
