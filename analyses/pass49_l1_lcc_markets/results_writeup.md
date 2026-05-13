# L1 — LCC Bidirectional in Markets, Program A First Window (Pass-49 results)

**Test ID:** L1_lcc_markets_program_a_first_window
**Executed:** 2026-05-13T21:45:21Z
**Cost:** $0 (free yfinance data)
**Witness:** Agent-only (Brandon-async)
**Pre-registration:** `analyses/pass49_l1_lcc_markets/runner.py` docstring (frozen at write-time before any data download or inspection per Pass-49 L4 §1.1 + Pass-45 §11)
**Provenance:**
- Runner SHA-256: `bf80ce8107ae84e91df7377eb9cb16fddc205415be80128a701dc81242c9ecd7`
- Panel SHA-256: `0ba0c3d19d93e6337885b105a6f065663ad1e8dff5487111bf3962d78303b8a6`
- Ceremony log: `analyses/pass49_l1_lcc_markets/ceremony_log.md`

---

## 1. Headline result

**Verdict: NULL_NOISE on HOLDOUT.** Additionally: Filter A (TUNE↔VALIDATION drift) **FAIL**, and Filter (cross-segment sign consistency) **FAIL**.

This is a clean, pre-registered, holdout-blind **negative result** for LCC bidirectional resonance on the SPY/TLT pair under the frozen 5-day triangular-kernel configuration on the 2022-01-01 → 2026-04-30 window.

| Segment | n | Pearson | R_LCC |
|---|---|---|---|
| TUNE | 433 | (per JSON) | (per JSON) |
| VALIDATION | 325 | (per JSON) | (per JSON) |
| HOLDOUT | 325 | 0.124261 | 0.020522 |

| Test | Result | Verdict |
|---|---|---|
| Filter A: TUNE↔VAL drift on R_LCC | ratio 4.21× | **FAIL** (>2× bound) |
| HOLDOUT |R_LCC| − |Pearson| | −0.103739 | **negative margin** |
| Cross-segment signs of R_LCC | [+, −, +] | **inconsistent** |
| HOLDOUT |R_LCC| | 0.0205 | **below 0.05 noise floor** |
| **Overall** | — | **NULL_NOISE** |

---

## 2. What this means in plain English

The pre-registered prediction H_PRIMARY was: *on the held-out segment, the LCC resonance scalar |R_LCC| should exceed the classical Pearson correlation |Pearson| by at least 0.05, with matching sign.*

Three of the three discriminators broke against the LCC prediction:

1. **|R_LCC| is smaller than |Pearson|, not larger.** On the held-out segment the LCC scalar is 0.0205 in absolute value while the classical Pearson is 0.1243. The classical baseline beats the LCC measurement on its own data.

2. **|R_LCC| is below the pre-registered noise floor of 0.05.** Even in isolation, the LCC value is too small to be confidently distinguished from zero given the segment size.

3. **The sign of R_LCC flips between segments** (TUNE: positive, VALIDATION: negative, HOLDOUT: positive). LCC is supposed to track a stable underlying resonance; sign-flipping across same-distribution segments indicates the metric is dominated by sample noise, not signal.

4. **Filter A (the auto-rejection guard) tripped.** The TUNE→VALIDATION drift ratio of 4.21× exceeds the 2.0× pre-registered bound. By Pass-49 L4 §2.1 this run would have been rejected at promotion-to-HOLDOUT *even if* the HOLDOUT result had been favorable.

---

## 3. What this does NOT mean

Per #69, distinguish carefully:

- This **does not** falsify LCC theory in general. It falsifies one specific operationalization (5-day triangular kernel, 2022-2026 window, SPY/TLT pair, Pearson-comparison framing) on one dataset.
- It **does** constrain future LCC-in-markets claims: any next-attempt operationalization MUST explain why this configuration failed and predict in advance what configuration would succeed. Lazy "just try a different kernel until something works" violates the frozen-pre-reg discipline.
- Re-running on the same HOLDOUT for a different configuration is **forbidden** by Pass-49 L4 anti-cheat. Future LCC-in-markets work must use a fresh dataset window or different asset pair, with its own pre-registration.

---

## 4. Honest observations

- The Pearson correlation of 0.1243 on HOLDOUT is itself low (SPY/TLT are conventionally cited as anti-correlated; the 2022-2026 window includes a regime of correlated-equity-bond drawdown that compresses the classical signal). Possible follow-up: re-pre-register on a different asset pair with stronger classical baseline.
- The triangular kernel choice was convenient, not first-principles. A Green-function kernel from the tessellation paper might give different numerical magnitudes — but the sign-flip across segments is a structural problem the kernel choice cannot rescue.
- The frozen 5-day τ_max may be too short for daily macro data (where coherence bands span weeks). A longer τ_max could change R_LCC magnitude. Again: this would need to be a new pre-registered run on fresh data, not a retroactive fix.

---

## 5. What this means for the LCC retrieval program (M-roadmap)

- **M1 status updated:** LCC-in-markets first-window result **does not** support the human-domain extension hypothesis (Brandon's prior framing in `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` Track A).
- **M4 (gating before commercial use)** remains untouched: this single-pair negative result does not invalidate the upstream animal-studies efficacy claim, but it raises the bar for any "LCC works in markets" sub-claim in commercial materials.
- **Recommendation:** before launching a second LCC-in-markets attempt, develop a *theory-driven* prediction of which asset class + which kernel + which τ_max should produce a confirm. Submitting trial-and-error attempts to fresh datasets without theory burns through holdout budget without epistemic gain.

---

## 6. Filter audit (Pass-49 L4 §2 anti-cheat)

| Filter | Application | Result |
|---|---|---|
| A — Overfit (TUNE↔VAL drift > 2×) | YES | **FAIL** (4.21×) |
| B — Cherry-picked window | NA | window pre-registered before download |
| C — Selective species reporting | NA | single pair |
| D — Variance check (below noise floor) | YES | **TRIGGERED** (|R_LCC|=0.0205 < 0.05) |
| E — Vacuousness | YES | PASS (DISCONFIRM was reachable) |

---

## 7. Provenance summary

- Runner code is frozen-and-hashed; the SHA-256 above pins this exact analysis.
- Data panel SHA-256 pins the exact yfinance return panel used.
- Partition is deterministic from the panel SHA-256, so re-running the same code on the same data must produce the identical partition and the identical numerical result.
- Witness: agent-only. Per Pass-49 L4 §1.3, this is weaker than Brandon-witnessed; flagged in `results.json` (`brandon_witness_pending: true`).

---

## 8. Filed outcome

L1 first-window: **NULL_NOISE / FILTER_A_FAIL** — pre-registered, holdout-blind, no re-tuning, reported honestly. This is the protocol working as intended: catching a negative result before it can be sold as a positive one. Pass-49 L1 status: ✅ EXECUTED, result NEGATIVE.
