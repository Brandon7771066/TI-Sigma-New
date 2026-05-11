# Pass 38 — MBE Celebrity Numerology Study: EXECUTION RESULTS

**Date:** 2026-05-11
**Pass:** 38
**Pre-reg:** `papers/PASS_37_MBE_CELEBRITY_NUMEROLOGY_STUDY_DESIGN_2026-05-11.md` (FROZEN at Pass 37)
**Anti-HARK gate:** `analyses/pass38_mbe_celebrity_numerology/archetypes_frozen.json` (committed BEFORE Step 4 MC and Step 5 verdict)
**Runner:** `analyses/pass38_mbe_celebrity_numerology/runner.py`
**Results:** `analyses/pass38_mbe_celebrity_numerology/results.json`

---

## §1 — Headline (one paragraph)

The Pass-37 MBE-celebrity prediction (≥9/12 matches, z ≥ 2.5) **does NOT survive** prospective test. Live Wikipedia fetch (12/12 succeeded after one Bobby-Fischer retry; revids recorded), deterministic Step-2 keyword extraction (per Pass-37 §4 Step 2b/2c frozen rubric), and 50,000-iter Monte Carlo null comparison yield: **3/12 matches; MC null mean = 4.746, sd = 1.695; z = −1.030; verdict = PARTIAL_NEG (TIU = −0.50)**. Per the Pass-37 §5 frozen verdict ladder, this is a *small-magnitude negative* update — the MBE-via-numerology-keyword-rubric prediction is *modestly disconfirmed*; it is NOT a strong REJECT (which would require ≤2/12 OR z ≤ −2.5). Per URB-830 symmetry, REJECT and PARTIAL-NEG carry the same epistemic-update structure as CONFIRM/PARTIAL-POS — the MBE-celebrity prediction takes a small-but-real Bayesian hit and the experiment was honest.

## §2 — Per-celebrity results table

| # | Celebrity | Wiki revid | Top-2 archetypes (frozen rubric) | Letter→mod9 | Phoneme→mod9 | Match? |
|---|---|---|---|---|---|---|
| 1 | Albert Einstein | live-fetched | [1 leadership, 2 cooperation] | 14→5 | 4→4 | ❌ |
| 2 | Nikola Tesla | live-fetched | [4 structure, 1 leadership] | 11→2 | 5→5 | ❌ |
| 3 | Srinivasa Ramanujan | live-fetched | [1 leadership, 2 cooperation] | 18→9 | 8→8 | ❌ |
| 4 | Carl Gustav Jung | live-fetched | [1 leadership, 2 cooperation] | 14→5 | 4→4 | ❌ |
| 5 | Wolfgang Pauli | live-fetched | [1 leadership, **4 structure**] | 13→**4** | 4→**4** | ✅ |
| 6 | Jiddu Krishnamurti | live-fetched | [**6 responsibility**, 5 freedom] | 17→8 | 6→**6** | ✅ |
| 7 | Ramana Maharshi | live-fetched | [1 leadership, 2 cooperation] | 14→5 | 6→6 | ❌ |
| 8 | Marie Curie | live-fetched | [**1 leadership**, 6 responsibility] | 10→**1** | 4→4 | ✅ |
| 9 | Kurt Gödel | live-fetched | [4 structure, 7 wisdom] | 9→9 | 3→3 | ❌ |
| 10 | Wayne Gretzky | live-fetched | [1 leadership, 2 cooperation] | 12→3 | 4→4 | ❌ |
| 11 | Bobby Fischer | revid 1353136368, 2026-05-08 | [1 leadership, 2 cooperation] | 12→3 | 4→4 | ❌ |
| 12 | Hildegard of Bingen | live-fetched | [1 leadership, 7 wisdom] | 17→8 | 6→6 | ❌ |

**Aggregate: 3/12 matches.**

## §3 — MC null comparison

50,000 Monte Carlo iterations, seed 27182818, draws letter_mod9 and phoneme_mod9 i.i.d. uniform from {1..9} for each of 12 celebrities, using each celebrity's *actual* top-2-archetype set from Step 2 (so the null preserves the empirical archetype distribution from the keyword rubric — only the name-derived numbers are randomized).

- **Mean matches under null:** 4.746
- **Standard deviation:** 1.695
- **Observed:** 3
- **Z-score:** (3 − 4.746) / 1.695 = **−1.030**
- **One-sided P(matches ≤ 3 | null):** ≈ 0.151 (not significant by either direction)

## §4 — Verdict per Pass-37 §5 frozen ladder

| Threshold | Criterion | Hit? |
|---|---|---|
| CONFIRM (MBE) | ≥9/12 AND z ≥ 2.5 | ❌ (3/12, z=−1.03) |
| PARTIAL_POS | 7-8/12 OR (≥9/12 with z=1.5-2.5) | ❌ |
| NULL | 5-6/12 AND \|z\| ≤ 1.5 | ❌ (matches not in 5-6 range) |
| **PARTIAL_NEG** | **3-4/12 OR z = −1.5 to −2.5** | **✅ (3/12 hits matches-criterion)** |
| REJECT (MBE) | ≤2/12 OR z ≤ −2.5 | ❌ |

**Verdict: PARTIAL_NEG. TIU = −0.50.**

## §5 — Interpretation under URB-830 symmetric framing

Per Pass-33 URB-830 ratification, **CONFIRM and REJECT are symmetric Bayesian updates**; PARTIAL_NEG with TIU = −0.50 means the MBE-celebrity-via-keyword-rubric prediction takes a *small* posterior hit, comparable in magnitude to a hypothetical PARTIAL_POS at z ≈ +1.0. The hypothesis is *not* strongly disconfirmed — it's *modestly disconfirmed*. The experiment is bidirectionally testable in the URB-830 sense (CONFIRM-criterion was specifiable in advance and the negative-direction landed in PARTIAL_NEG rather than NULL); the §6 caveats below identify the residual honesty constraints (rubric-bias in archetype-1; only one of multiple plausible operationalizations was tested).

**What this update means for MBE more broadly:**

- The *narrow* prediction tested (≥9/12 matches under this specific keyword rubric) takes a small Bayesian hit.
- The *broader* MBE hypothesis (heavy-tailed individual base rates of psi/synchronicity-class phenomena per Pass-15) is **not directly tested** by this study; numerology-keyword-match is one operationalization of one prediction-channel of MBE. Per Pass-37 §8 C3, "CONFIRM at §5 would update toward MBE-and-numerology-co-jointly; REJECT updates against MBE-via-numerology specifically." The Pass-38 result similarly updates against MBE-via-numerology-keyword-rubric specifically.
- The Pass-14 family-cluster result (T=2 P=0.57%) is *not refuted* by the Pass-38 result (different rubric, different sample, different selection criteria).

## §6 — Honesty caveats (#69)

- **(C1) Anti-HARK gate provenance — clean rerun executed:** initial Pass-38 attempt hit two Wikipedia 429 rate-limits (Krishnamurti + Bobby Fischer) which were resolved across multiple processes. After architect flagged that "single continuous log + freeze-then-MC sequence" was the load-bearing anti-HARK demonstration, runner.py was hardened (max_attempts=6, base_delay=2.0, exponential backoff up to 64s) and re-executed cleanly: ONE continuous run, 12/12 fetched, freeze→MC→verdict in monotonic order. The frozen artifact carries provenance: `_provenance.sha256_of_payload_pre_provenance = c09ca99f991cc0f3...` and `_provenance.git_head_at_freeze = bbac05a9d812...`. The clean log lives at `analyses/pass38_mbe_celebrity_numerology/runner.log`.
- **(C2) Wikipedia revision pinning:** revids and timestamps are recorded for all 12 celebrities in `archetypes_frozen.json`; reruns against same revids will reproduce.
- **(C3) Top-2 distribution skew:** archetype-1 (leadership) appears in the top-2 for **10/12** celebrities; the *exact* tuple [1 leadership, 2 cooperation] appears for **6/12** (Einstein, Ramanujan, Jung, Ramana, Gretzky, Bobby Fischer). The frozen keyword set for archetype-1 ("leader/leadership/leading/founder/pioneer/first/originator/head") is broad and Wikipedia bio openings frequently use words like "first" and "founder" — this *systematically biases* the rubric toward archetype-1 dominance. **This is a #69 design weakness in the Pass-37 rubric**, not a result-interpretation issue. A Pass-39+ refinement should rebalance the keyword sets to suppress this bias (raised as p38-A).
- **(C4) Tested operationalization is one of many:** the keyword-frequency-archetype-rubric is one specific operationalization. Alternative operationalizations (life-path number from birth date; expression number from full name; soul-urge from vowels-only) would test different things and might give different verdicts. Pass-38 settles only the Pass-37-frozen rubric.
- **(C5) Brandon-DPES convergence on roster:** per "great minds AND NOT" doctrine, the §3 result is independent evidence; the §4 verdict is from the §3 ladder applied mechanically.
- **(C6) MC null preserves archetype distribution:** the null randomizes only the name-derived numbers, holding archetype-2-tuples fixed at empirical values. This *correctly* tests "is the celebrity's name numerologically aligned with their archetype" (the MBE prediction) and does NOT spuriously reward the rubric's archetype-1 bias.

## §7 — Items raised

- **p38-A** — refine keyword rubric to suppress archetype-1 over-broadness (drop "first", "head", "leader" overlaps); rerun under refined rubric as sensitivity check; if refined rubric still yields PARTIAL_NEG or worse, this is a stronger MBE-via-numerology disconfirm.
- **p38-B** — alternative-rubric sensitivity check: test life-path number (from birth date) and expression number (vowel/consonant split) on same 12-celebrity roster; if any alternative rubric reaches CONFIRM, the MBE-via-numerology hypothesis survives at the meta-rubric level.
- **p38-C** — control-roster sensitivity check (Pass-37 §9 p37-P): apply same Pass-37 rubric to 12 celebrities NOT plausible-GM-Nodes (e.g., random Hollywood actors); if control roster also returns 3-4/12 matches, the Pass-38 PARTIAL_NEG is "rubric is null overall" not "MBE specifically failed."

## §8 — Update to Pass-37 corpus

The §3.3 prediction in `papers/PASS_37_PD_FINAL_VALUE_TRUTH_LABEL_PLUS_META_TRUTH_RULING_2026-05-11.md` is unrelated. The §5 verdict ladder in `papers/PASS_37_MBE_CELEBRITY_NUMEROLOGY_STUDY_DESIGN_2026-05-11.md` is the relevant pre-reg; this paper closes that pre-reg with verdict PARTIAL_NEG.

The Pass-15 MBE itself is *not* refuted; only one operationalization of one prediction channel is. Per Pass-37 §8 C3 of the Pass-37 design paper.
