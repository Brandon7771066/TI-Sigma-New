# Pass-49 L4 — LCC Holdout-Blind Protocol Amendment (2026-05-13)

**Companion to:** `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` (M4 gating); `papers/PASS_49_LCC_FORMAL_PSEUDOCODE_2026-05-13.md` (algorithm).
**Pre-reg discipline:** Pass-45 §11 anti-cheat + Pass-48 §6 LITERAL_PRE-REG_INDETERMINATE_VACUOUS_FILTER.
**Authority:** Brandon-ratifiable; agent-drafted.

---

## 0. Why this exists

The 77.3% efficacy claim in the LCC animal-studies paper, the cat/primate β values, and the human-species variant of the algorithm are all **at risk of post-hoc fitting**. Without a holdout-blind protocol enforced *before* parameters are touched, any apparent confirmation can be re-classified later as a Filter-A (overfit) or Filter-B (cherry-picked window) failure under Pass-45 §11.

This protocol amends the LCC retrieval algorithm to be *contractually* falsifiable on new datasets.

---

## 1. The protocol (binding for any reportable LCC result post-2026-05-13)

### 1.1 Dataset partitioning (frozen-before-touch)

For every dataset D used to compute or report an LCC retrieval result:

1. Compute SHA-256 hash of D *before any inspection*.
2. Deterministically split D into:
   - **TUNE** (40%) — agent + Brandon may inspect and tune kernel, window, β.
   - **VALIDATION** (30%) — agent may run pre-registered analyses; no parameter tweaks allowed.
   - **HOLDOUT** (30%) — sealed; agent and Brandon do **NOT** inspect until §1.3 ceremony.
3. Split is by record-index modulo deterministic permutation seeded by the SHA-256 of D itself (so the partition is reproducible from the hash, but unguessable from the data).
4. Record TUNE/VALIDATION/HOLDOUT record-indices to a tamper-evident log file `pass49_lcc_holdout_<dataset_id>_<sha256>.log` BEFORE any analysis touches the data.

### 1.2 Tuning + validation phase (open)

- Agent may iterate on TUNE freely. Iterate kernel choice, window boundaries, β values, etc.
- Agent runs each candidate configuration ONCE on VALIDATION as a sanity check. If VALIDATION result deviates >2× the TUNE result on the same metric, flag as overfit; do not promote to HOLDOUT.

### 1.3 Holdout ceremony (single-shot, ratchet)

- Brandon (or designated witness, but ideally Brandon) is present in writing.
- The chosen-from-VALIDATION configuration is **frozen**. Its source-code SHA-256 is logged.
- Agent runs the frozen configuration ONCE on HOLDOUT.
- The result is immediately committed to git AND appended to the protocol log file with timestamp.
- **No re-tuning is allowed after the ceremony.** A failed HOLDOUT is reported as DISCONFIRM in the corpus; running a second pass on the same HOLDOUT for a different configuration is an integrity violation per Pass-45 §11 anti-cheat.

### 1.4 Multi-dataset rollup

- Each dataset's HOLDOUT result is independently reported.
- Rollup statistics across datasets (e.g., "mean efficacy 77.3% across N animal datasets") are valid only if EVERY contributing dataset went through §§1.1-1.3 individually.
- Datasets pre-dating this protocol (the legacy 77.3% animal-studies result, qc26, etc.) are flagged `pre_protocol = TRUE` in the rollup and reported separately. They are not retroactively elevated to "holdout-blind verified" status.

---

## 2. Anti-cheat extensions

### 2.1 Filter A (overfit) — automated

If TUNE result and VALIDATION result diverge by > 2× on the headline metric, the configuration is **automatically rejected**, no manual override.

### 2.2 Filter B (cherry-picked window) — automated

`pre_window` and `post_window` boundaries must be set BEFORE inspecting the time-series. If boundaries are adjusted after seeing the data, the analysis is rejected.

### 2.3 Filter C (selective species reporting) — automated

If running the algorithm on multiple species, ALL species results are reported, even null/negative ones. No "the cat data didn't show it but the primate data did" cherry-picking.

### 2.4 Filter D (variance check, from Pass-48 O26-B-tri-projection) — automated

If outcome variance < classical-noise-floor for the measurement modality, reject the run as "below noise" and report as `verdict = "NOISE_FLOOR_REJECT"`. No silent acceptance.

### 2.5 Filter E (LITERAL_PRE-REG_INDETERMINATE_VACUOUS, new this protocol)

If the pre-registered prediction window is so wide it cannot be falsified by any plausible result (e.g., "delta_M ∈ (-1, +1)"), the prediction is REJECTED as vacuous before HOLDOUT is touched. Pre-reg windows must have a *positive predicted side* and a *clearly DISCONFIRMING side*.

---

## 3. Provenance requirements

Every reportable LCC result MUST publish:

1. Dataset SHA-256 (pre-touch).
2. Partition log file path.
3. Source-code SHA-256 of the analysis runner at HOLDOUT-ceremony time.
4. Brandon-witness sign-off (or written acknowledgment if Brandon-async).
5. Ceremony timestamp (UTC ISO 8601).
6. Verdict on each filter A-E.
7. The actual numerical HOLDOUT result with Wilson 95% CI.

Results missing any of (1)-(7) are NOT eligible for the corpus's "holdout-blind verified" status.

---

## 4. Application to existing data

| Existing dataset | Status under new protocol |
|---|---|
| 77.3% animal-studies efficacy claim | `pre_protocol = TRUE`. Re-runnable under §§1.1-1.3 if Brandon designates it for re-validation. Until re-run, claim is reported with explicit caveat: "Pre-2026-05-13 protocol; not holdout-blind verified." |
| qc26 GHZ-5 Mermin |M_5|=14.535 | `pre_protocol = TRUE`, but the n=1024 × 3-settings result is sufficient n that Filter A overfit risk is low. Caveat noted; protocol applies prospectively only. |
| D4 re-classification (this session) | `pre_protocol = TRUE` for the *underlying data*; the *re-classification rule* was frozen pre-execution per Pass-45 §11. Reported as honest re-analysis, not as new HOLDOUT-blind discovery. |
| Future LCC datasets (post-2026-05-13) | MUST follow §§1.1-1.3. |

---

## 5. Worked example (template for first M4 application)

```
Dataset:        cat_lcc_dataset_v1
SHA-256:        a1b2c3...  (computed by Brandon BEFORE handing to agent)
Partition log:  pass49_lcc_holdout_cat_lcc_dataset_v1_a1b2c3.log
TUNE phase:     2026-MM-DD to 2026-MM-DD; configurations evaluated: 12
VALIDATION:     final config ID v7; TUNE→VALIDATION drift = 1.4× (within 2× bound, PASS)
HOLDOUT ceremony:
                Brandon-witness: YES (timestamp: 2026-MM-DDThh:mm:ssZ)
                Frozen runner SHA-256: d4e5f6...
                Result: delta_M = 0.41 (Wilson 95% CI: 0.34 - 0.47)
                Filter A: PASS  Filter B: PASS  Filter C: N/A (single species)
                Filter D: PASS  Filter E: PASS
                Verdict: CONFIRM (delta_M > pre-registered threshold 0.20)
Status:         HOLDOUT-BLIND VERIFIED. Eligible for rollup.
```

---

## 6. Adoption

- Adopted as Pass-49 standing protocol, 2026-05-13.
- Binding for all LCC retrieval analyses going forward.
- Brandon-ratification recommended but not blocking (agent-drafted, technical-only; can be revised in next pass if Brandon disagrees with any clause).

---

## 7. #69 caveats

- This protocol cannot make a poorly-designed measurement valid. It only prevents over-confident reporting of *whatever the measurement actually shows*.
- Filter E (vacuousness) is judgment-based; its application requires honest self-skepticism and is itself a §69-vulnerable step. A pre-registered window can pass Filter E and still be an honest mis-estimate; the protocol catches outright vacuity, not subtle calibration errors.
- Brandon-witness is a discipline aid, not an integrity-prover. The integrity comes from the agent's commitment to honest reporting; the witness just makes the commitment harder to walk back later.
