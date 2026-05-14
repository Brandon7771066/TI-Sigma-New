# L-2 PILOT — Unsupervised LCC, Paleoclimate δ¹⁸O Cross-Site

**Date:** 2026-05-14
**Pre-reg source:** `papers/PASS_49_LCC_PLAIN_FRAMEWORK_SUPERVISED_VS_UNSUPERVISED_2026-05-13.md` §6.2
**Pre-reg SHA-256:** `a40789d46c03f07b29b8d1da75b6dcc1eeaa95ab5004998ac24b5d6c03d69ad3`
**Protocol-doc SHA-256 (first 16):** `e1627b094e782f17`
**Verdict:** **PILOT_PRELIMINARY_DISCONFIRM** (strict pre-reg §2.3 interpretation — corrected after architect code review)
**Initial-run verdict (BUGGED, retracted):** ~~PILOT_PRELIMINARY_TREND_CONFIRM~~ — see §5.0 Bug-Disclosure below.
**Budget:** $0/$50 corpus + $2k settlement reserve intact.

## §1 Background

Pass-49 batch-3 (2026-05-13) closed Program A's L-1 PRIMARY (UMCSENT × SPY monthly) and SECONDARY (SPY × ^VIX) tests as `NULL_NOISE_NO_ABOVE_C`. The plain framework (§4 P1) predicts the markets cell as the **weakest** unsupervised-LCC domain. P1 (Existence) further predicts Quantum > Ecosystems > Workplaces > Markets ordering, with Ecosystems as the highest-information-gain domain to test next. Brandon affirmed pivot 2026-05-13 ("Recommendation for next directive affirmed!!").

L-2 tests the Ecosystem cell using paleoclimate δ¹⁸O cross-site coupling. H_PRIMARY (§5):
> A randomly-selected pair of geographically-distant paleoclimate δ¹⁸O records over a 1000-year shared interval will exhibit S1+S2+U4 (Unsupervised LCC) AND $D_{\text{LCC}} > 0.5$ on the HOLDOUT segment.

Agent self-bound prediction (§6.2 anti-cheat): **CONFIRM_STRONG_PILOT** anticipated.

## §2 Deviations from pre-reg (per L-4 Filter B)

| ID | Pre-reg | Actual | Justification |
|---|---|---|---|
| **D1** | 5 sites, 10 pairs, 4 HOLDOUT | 3 sites, 3 pairs, 1 HOLDOUT | NOAA URL probing 2026-05-13 → 2026-05-14 confirmed only 3 records with bidecadal-or-finer resolution covering AD 1000-2000: GISP2 (Greenland Summit), GRIP (Greenland Summit, ~30 km from GISP2), TALDICE (Talos Dome, Antarctica). Dome Fuji available but 250-yr resolution = ~4 samples in window, dropped pre-analysis. Bulk PAGES-2k LiPD download deferred to Pass-51 (would expand to 10+ sites). |
| **D2** | Verdict matrix CONFIRM_STRONG/CONFIRM/WEAK/DISCONFIRM/NULL_NOISE on N≥4 HOLDOUT pairs | HOLDOUT N=1 → matrix degenerate. Reported as `PILOT_PRELIMINARY_*` | Direct consequence of D1. |
| **D3** | "100-year sliding windows" + "high-resolution decadal-or-finer δ¹⁸O records" (§6.2) | 20-yr common grid via linear interpolation | GISP2 native resolution = 20 yr; sets the shared ceiling. |
| **D4** | 100-yr windows + τ_max=10 samples (§3 paleo row) | 300-yr windows (15 samples) + Granger lag capped at WINDOW//5 = 3 (60 yr) | **Internal inconsistency in pre-reg.** §3 specifies τ_max=10 sample-units; §6.2 specifies 100-yr windows. At 20-yr grid, 100-yr window = 5 samples — fewer than τ_max. Granger F-stat with lag ≥ 1 + intercept needs len(Y) − Xf.cols ≥ 1, requiring window ≥ 2·lag+2. Window=5/lag=2 ⇒ dof=−1 (degenerate). Window expanded to 15 samples = 300 yr (smallest size yielding ≥1 dof at lag=3, the τ_max ÷ 3 cap). Step retained at 100 yr. **This is a structural infrastructure fix, not a hypothesis-favorable tweak.** Per #69 brutal honesty: D4 was selected on first run after seeing dof=0 traceback; no hypothesis-relevant outputs were inspected before the cap was set. |

## §3 Method (frozen pre-data)

- **Sites & files:** GISP2 (`d18o20y.txt`), GRIP (`gripd18o.txt`), TALDICE (`taldice2010d18o2k.txt`); URLs in `data/SOURCE_URLS.md`.
- **Common grid:** AD 1010, 1030, …, 1990 (20-yr step, 50 samples). Linear interpolation; out-of-bounds → NaN.
- **Window:** 300 yr (15 samples), step 100 yr (5 samples), per-window linear detrending.
- **τ_max:** ±10 samples (±200 yr).
- **ρ_min:** 0.40 (§3 ecosystems row).
- **Granger:** Hand-rolled OLS F-stat; lag = `max(1, min(|τ*|, 3))`. Phase-shuffle null: 200 surrogates, FFT-randomized phases preserving power spectrum. p = (#F_surrogate ≥ F_observed + 1) / 201.
- **S1:** max_τ |corr(X(t), Y(t+τ))| > 0.40.
- **S2:** argmax τ* > 0 (i.e., X leads Y).
- **S3:** Granger phase-shuffle p < 0.05.
- **S4 (must FAIL for U4):** OLS regression ΔX(t+1) ~ (Y(t) − ⟨Y⟩) yields |b| > 0.1 AND p < 0.05.
- **U4:** ¬S4.
- **Unsupervised-LCC window:** S1 ∧ S2 ∧ U4.
- **D_LCC:** fraction of consecutive-window pairs (k−1, k) with G_X→Y^(k) > G^(k−1) + ε; ε = 0.1 · stddev(G across windows).

Determinism: `seed_base = int(pre_reg_sha[:8], 16) % 2^31 = 753410261`; per-pair seed offset = pair_index · 1000; per-window offset = start_index. All RNG controlled.

Pair split (alphabetical by site-id, deterministic):
- **TUNE (n=2):** (GISP2, GRIP), (GISP2, TALDICE)
- **HOLDOUT (n=1):** (GRIP, TALDICE) ← cross-hemispheric

## §4 Results

### §4.1 Per-pair (corrected pre-reg-faithful run)

| Pair | Joint-valid samples | Windows | Unsup-LCC windows (strict §2.3 = S1∧S2∧S3∧U4) | D_LCC | Split |
|---|---|---|---|---|---|
| GISP2 ↔ GRIP | 49 | 7 | 0 (0%) | 0.500 | TUNE |
| GISP2 ↔ TALDICE | 49 | 7 | 0 (0%) | 0.333 | TUNE |
| **GRIP ↔ TALDICE** | **49** | **7** | **0 (0%)** | **0.667** | **HOLDOUT** |

Across all 21 windows in 3 pairs: **0 windows satisfy S1∧S2∧S3∧U4**. Driver: S3 (Granger phase-shuffle p<0.05) fires 0/21 — paleo δ¹⁸O lacks the lagged predictability the LCC framework requires once tested against a phase-shuffle null. Strict U4 (|b|<0.1 AND p>0.20) also drops some windows (the residual is S4-ambiguous, neither strict-S4 nor strict-U4).

### §4.2 Aggregate (corrected)

- **TUNE:** 0/2 pairs with ≥1 strict-unsup-LCC window; mean D_LCC = 0.417.
- **HOLDOUT:** 0/1 pairs with ≥1 strict-unsup-LCC window; D_LCC = 0.667.

H_PRIMARY pre-condition on HOLDOUT (S1+S2+S3+U4 AND D_LCC > 0.5): **NOT MET** (S3 fails 0/7 windows; U-LCC conjunction fails 0/7).

Note: D_LCC criterion alone (G_X→Y monotonically increasing across windows) IS satisfied on HOLDOUT (0.667 > 0.5), but the framework's H_PRIMARY requires BOTH conditions jointly. Per pre-reg §6.3 verdict matrix:

> DISCONFIRM: 0 pairs satisfy S1+S2+U4 OR mean D_LCC ≤ 0.5

Strict reading: 0 HOLDOUT pairs satisfy S1+S2+S3+U4 → **DISCONFIRM** branch triggered.

### §4.3 Verdict

**PILOT_PRELIMINARY_DISCONFIRM** — under strict pre-reg §2.3 interpretation, the framework's central prediction fails on this 3-site/1-HOLDOUT pilot. The drift signal (D_LCC=0.667 on HOLDOUT) is suggestive on its own but the conjunctive cross-sectional condition is not met.

### §4.4 Auxiliary: shorthand-interpretation run (§5/§6 phrasing)

The framework paper inconsistently uses "S1+S2+U4" shorthand in §2.4/§5/§6 (which omits S3). Under that lax interpretation but with strict-pre-reg U4 (|b|<0.1 AND p>0.20):

| Pair | Strict S1∧S2∧S3∧U4 | Lax S1∧S2∧strict-U4 |
|---|---|---|
| GISP2-GRIP | 0/7 | 0/7 (S3 isn't the binding constraint here; strict-U4 fails too) |
| GISP2-TALDICE | 0/7 | 0/7 |
| GRIP-TALDICE | 0/7 | 0/7 |

Both interpretations agree: 0 unsupervised-LCC windows. The verdict is robust to the §2.3-vs-§5 interpretive ambiguity.

## §5 Interpretation (#69 brutal-honesty section)

### §5.0 Bug disclosure (mandatory per #69)

The initial-run writeup claimed `PILOT_PRELIMINARY_TREND_CONFIRM` based on 4/7 HOLDOUT windows passing "S1+S2+U4". Architect code review (2026-05-14) caught two severe implementation bugs:

1. **S3 was dropped from the unsupervised-LCC conjunction.** Pre-reg §2.3 line 45 is canonical: "S1, S2, S3 hold AND S4 explicitly fails". The "S1+S2+U4" shorthand in §2.4/§5/§6 elides S3 but does not redefine it. Initial code: `S1 ∧ S2 ∧ U4`. Corrected: `S1 ∧ S2 ∧ S3 ∧ U4`.
2. **U4 was implemented as `not S4` instead of strict `|b|<0.1 AND p>0.20`.** Pre-reg §2.3 line 47 is explicit. The "not S4" implementation included a hypothesis-favorable middle ground (windows with ambiguous feedback signal). Corrected to strict U4.

Under both bug fixes: 0/21 windows satisfy strict-pre-reg unsupervised-LCC. **The initial TREND_CONFIRM was an artifact of two implementation errors that both happened to favor the framework**, which is exactly the failure mode #69 warns against.

This bug-disclosure is logged here permanently. The runner's frozen pre-reg SHA (a40789d4...) is unchanged because the parameters and protocol-doc hash did not change — only the implementation logic was corrected to match the protocol it was always supposed to implement. If a corpus reader regards this as protocol-altering rather than bug-fixing, the conservative interpretation is: treat the initial run as the binding result, in which case the verdict is the buggy `TREND_CONFIRM`. Brandon's call.

### §5.1 What the corrected result actually says

1. **S3 carries the disconfirm.** 0/21 windows have Granger F-stat exceeding the phase-shuffle null at p<0.05. This is the strongest single signal: at 20-yr / 300-yr-window resolution, paleo δ¹⁸O cross-site dynamics do not exceed what same-spectrum noise produces. The framework's "drift toward causation" prediction does not survive a phase-shuffle null at this resolution.
2. **D_LCC alone tells a different story.** HOLDOUT D_LCC = 0.667 (G_X→Y monotonically increasing across consecutive windows) IS suggestive. But the framework requires the conjunctive condition; D_LCC alone is not the test.
3. **Cross-hemispheric pair (GRIP-TALDICE) is still the strongest on D_LCC.** Same mechanistic interpretation as before (shared global radiative forcing drives common signal), but it doesn't translate into per-window Granger predictability above noise.

### §5.2 Disconfirms / weakens

1. **Agent-witnessed self-bound prediction was CONFIRM_STRONG_PILOT.** Actual: PILOT_PRELIMINARY_DISCONFIRM. The prediction was wrong in both direction and magnitude. Logged.
2. **Two implementation bugs both favored the framework.** Per §5.0: this is the canonical #69 failure mode. Architect-level review caught what the agent's self-review missed.
3. **D4 deviation still applies.** Window-size choice (100→300 yr) was post-traceback. This deviation is forced (degenerate dof) and deterministic ("smallest WINDOW yielding ≥1 dof at the lag cap"), but it remains protocol-altering and should be noted when pooling with future expansions.
4. **N=1 HOLDOUT is bad statistics.** A single pair cannot distinguish "signal" from "noise lottery." Pass-51 expansion to ≥4 HOLDOUT pairs (via PAGES-2k LiPD bulk download) is required for formal L-2 closure.
5. **The DISCONFIRM is also weak evidence.** With N=1 HOLDOUT and the §3 ecosystems-row thresholds (ρ_min=0.40 may be too high for 300-yr windows), the framework deserves a fair retest at the expanded site list before being declared falsified in the ecosystems cell.

### Filter A (drift) check

Pre-reg §1.5 Filter A: pre-data flags whether any cell has been observed-then-tuned. None of the LCC operational thresholds (ρ_min=0.40, G_crit p<0.05, ε=0.1·σ(G), 0.1/0.20 thresholds for U4 and S4) were modified after data inspection. D4 modified the WINDOW size only. The §5.0 bug-fix corrected implementation to match unchanged thresholds.

### Filter C (agent witness)

I, Replit Agent (Claude), pre-registered the following before fetching any data:
- Site list (alphabetical 3 confirmed-accessible)
- All pre-reg parameters listed in §3 (frozen by SHA-256 in `results.json`)
- Self-bound prediction: CONFIRM_STRONG_PILOT (above).

Outcome (corrected): DISCONFIRM, opposite direction from prediction. I am logging this without rationalization. The path from "self-bound STRONG_CONFIRM" to "actual DISCONFIRM" went through two hypothesis-favorable implementation bugs that an architect review caught — exactly the #69 failure mode. Single most important Pass-51 task: expand HOLDOUT to ≥4 pairs to give the framework a fair retest before declaring ecosystem-cell falsification.

## §6 Closing predictions for Pass-51+

- **P1 (within-corpus, REVISED post-§5.0):** Expanding to 8 sites (PAGES-2k subset) → 28 pairs → ~17 HOLDOUT after 60/40 split. With strict pre-reg §2.3 implementation: predict 0-3 of 17 HOLDOUT pairs satisfy S1∧S2∧S3∧U4 (S3 is the binding constraint at this resolution), mean D_LCC ∈ [0.45, 0.60]. If observed >5/17, the framework gets resurrected; if 0/17, ecosystems-cell falsification at expanded N. Self-bound by SHA-256 above.
- **P2 (markets contrast):** Even with expansion, markets cell will remain NULL_NOISE; ordering Quantum > Ecosystems > Workplaces > Markets (P1 §4) gains a second corroborating data point — though now ecosystems may collapse onto markets rather than separate from them.
- **P3 (workplaces L-3):** Conditional. If ecosystems expansion confirms framework, workplaces predicted intermediate. If ecosystems disconfirms at expanded N, the framework may need recalibration of S3 threshold (Granger vs phase-shuffle is a strict null) before any cross-cell comparison is meaningful.

## §7 Files

- `runner.py` — frozen analysis script.
- `results.json` — full output (per-window S1-S4, F-obs, p-Granger, D_LCC).
- `data/{gisp2_d18o20y,grip_d18o,taldice_d18o2k,domefuji_d18o}.txt` — raw NOAA fetches 2026-05-14.
- `data/SOURCE_URLS.md` — URL provenance.
