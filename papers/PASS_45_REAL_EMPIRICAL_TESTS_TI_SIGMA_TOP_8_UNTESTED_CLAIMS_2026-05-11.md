# Pass 45 — Real Empirical Tests for TI Sigma's Top-8 Untested Major Claims

**Date:** 2026-05-11
**Pass:** 45
**Mode:** DPES + #69 brutal honesty + brutal-cost-discipline ($0–$50 lifetime budget across all 8)
**Mandate:** Drive these claims forward — or **into the ground**. Each test has a kill criterion.

---

## §0 — Selection method (anti-Cherry-Pick)

Inventoried untested or under-tested major claims by re-reading replit.md §7.7.x + corpus. Filtered to claims that (a) Brandon-original (not standard physics/QM consistency checks), (b) load-bearing for some downstream theory, (c) currently lack any empirical validation OR have only n=1 / sim-only support, (d) admit a **falsifiable, ≤$50, ≤90-day** test design. Ranked by ratio (cost-of-being-wrong) ÷ (cost-to-test). Top 8 below. Eight chosen because that is roughly the number Brandon can realistically attempt in parallel under DPES given current open carry-overs (p38-A, p39-A/B/C, p40-A/B/C/D/E, p42-B, p42-C, p43-A/B/C/D = 14 open). These 8 are NEW priority items, not replacements; rank them against current carry-overs and pick which to drop.

Each test has the same skeleton: **Claim → H1 → H0 → Protocol → Kill → Promote → Cost → Owner → Status**.

---

## §1 — TEST T45-1: Mendi Cross-Session Replication of Breath-Hold Detrended Δ

**Claim being tested:** Pass-43 found STIM2_BREATHHOLD vs RECOVERY1 detrended t = -4.13 in n=1 session. The claim "Mendi 1-optode device can detect cerebrovascular CO₂ response above instrumental noise after linear detrending" requires multi-session replication.

**H1:** In ≥3 of 5 future 20-min sessions following the same Pass-42 protocol, STIM2_BREATHHOLD vs RECOVERY1 detrended Δ is negative AND |t| > 2.0 (one-tailed, since direction is pre-registered).

**H0:** The Pass-43 result is a Type-I error or session-specific artifact (drift-correction overfit).

**Protocol:**
- Run `mendi_session_20min.py` 5 more times across ≥7 calendar days (one-per-day cap; no clustering).
- Pre-reg: do not look at any session's results until all 5 are captured.
- Same script, same MAC, same protocol. Anti-HARK: log each session's git HEAD + script SHA256.
- Analysis: identical detrended Welch t-test from `analyses/pass43_mendi_session_analysis/analyze.py` applied per session.
- Aggregate: count of sessions with negative Δ AND |t| > 2.0.

**Kill criterion (REJECT):** ≤1/5 sessions show negative Δ with |t| > 2.0. Means Pass-43 STIM2 finding was not real.

**Promote criterion (CONFIRM):** ≥3/5 sessions; promote Mendi NIR-intensity hypothesis from "WEAKLY SUPPORTED" to "CROSS-SESSION REPLICATED."

**Cost:** $0 (device owned, script written). Time: ~2 hours total (5 × 20 min + 5 × ~5 min setup).

**Owner:** Brandon. **Status:** READY (Pass-42 script proven by Pass-43 session #1).

**Why this matters:** Pass-43 result is the only Brandon-collected biometric data with a positive stim-locked finding. Replicate or kill.

---

## §2 — TEST T45-2: qc26 GHZ-5 Entanglement Witness on IBMQ Hardware

**Claim being tested:** Pass-31 D2-HYBRID asserts GM-Network c25 native-state realizes ℂ^32. Pass-43 qc25 confirmed only the trivial product-state H^⊗5|0⟩^⊗5 (textbook QM consistency, no entanglement). The non-trivial structural claim — that the GM-Network 5-qubit instantiation supports genuinely entangled states — is untested.

**H1:** GHZ-5 = (|00000⟩ + |11111⟩)/√2 prepared on IBMQ free-tier hardware violates the Mermin inequality (M_5 ≤ 4 classical, ≤ 16 quantum) with measured M > 4 + 3σ.

**H0:** Hardware noise or implementation error masks any entanglement; M ≤ 4.

**Protocol:**
- New runner `analyses/pass45_qc26_ghz5_mermin/runner.py`:
  - Prepare GHZ-5 via H on q0 + CNOT(0,1), CNOT(1,2), CNOT(2,3), CNOT(3,4).
  - 4 measurement settings per Mermin protocol (3 X + 2 Y combinations, etc.).
  - 1024 shots × 5 settings = 5120 shots (free-tier OK).
  - Compute M_5 and 3σ bound.
- Pre-reg in runner.py docstring + sha256 frozen before execution.

**Kill criterion (REJECT):** M ≤ 4 + 3σ. GM-Network 5-qubit hardware-instantiation does not support detectable entanglement on free-tier hardware.

**Promote criterion (CONFIRM):** M > 4 + 3σ AND M consistent with theoretical 16 within hardware-noise envelope. Pass-31 D2-HYBRID structural claim survives next bar.

**Cost:** $0 (free-tier IBMQ + IBMQ_Secret already loaded per Pass-43). Time: ~1 hour to write + ~10 min queue.

**Owner:** Agent. **Status:** READY.

**Why this matters:** Pass-43 qc25 was the easiest possible test. qc26 is the first non-trivial one. If it fails, the GM-Network → ℂ^32 mapping is hardware-non-realizable on accessible devices; the theoretical claim retreats to "in principle realizable on better hardware."

---

## §3 — TEST T45-3: GM-Node Definition Discriminant Validity (Pass-42 p42-D follow-up)

**Claim being tested:** Pass-42 froze a 6-criterion non-circular GM-Node definition (network-position + originality-output + mentorship-density + cross-domain-fluency + self-direction + blinded-rater). The claim "GM-Nodes are a real cluster, not just 'high-achievement adjacent'" requires that the 6-criterion score discriminates GM-Nodes from generally-high-achievers who are NOT GM-Nodes.

**H1:** Among N=20 public figures (10 pre-registered as GM-candidates from URB-829 lineage + 10 pre-registered as high-achievement controls drawn from MacArthur 2024 winners), 3 blinded raters scoring on the 6-criterion rubric produce mean GM-score > control-score with Cohen's d ≥ 0.8.

**H0:** GM and control means differ by Cohen's d < 0.4 (definition fails to discriminate).

**Protocol:**
- Roster: pre-register 10 GM-candidates (named in URB-829) + 10 controls (random sample from MacArthur 2024 list); freeze roster + criteria SHA before scoring.
- Raters: 3 LLMs (GPT-4, Claude, Gemini) with identical rubric prompt. Each rater scores all 20 figures on each of 6 criteria 1-7, blinded to label. Architect-fix style anti-HARK: rubric prompt frozen + sha256 logged before scoring.
- Aggregate: mean of 3 raters per figure per criterion → 6-vector → sum → 1 score per figure. Welch t-test GM vs control + Cohen's d.

**Kill criterion (REJECT):** Cohen's d < 0.4. Definition is not discriminant; collapses to "high achievement."

**Promote criterion (CONFIRM):** d ≥ 0.8. GM-Node 6-criterion definition has measurable construct validity.

**Cost:** $0 (LLM access via existing integrations) or ≤$5 (API tokens). Time: ~3 hours (roster compile + scoring + analysis).

**Owner:** Agent. **Status:** READY pending roster pre-reg.

**Why this matters:** Pass-42 architect-fix flagged "correlates with general high achievement so SC3 doesn't alone discriminate M1/M2/M3." This test addresses that head-on. If it fails, the entire GM-Node concept is reframed as a label for "generally impressive people" with no discriminant value.

---

## §4 — TEST T45-4: MR Truth Labels Inter-Rater Reliability (Cohen's κ)

**Claim being tested:** Pass-37 established canonical base-4 MR Truth Labels {True, False, Indeterminate, Meta-Indeterminate}. The claim that this 4-class scheme is **operationally usable** by trained raters — not just theoretically defined — is untested. If raters disagree wildly on which class a proposition belongs to, the scheme is theoretical-only.

**H1:** 3 raters (2 humans trained on `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` + 1 LLM with full ruling in context) classify 100 propositions drawn from the public corpus into the 4 classes with Fleiss' κ ≥ 0.6 (substantial agreement).

**H0:** κ < 0.4 (fair / poor agreement); the scheme is not operationally reliable.

**Protocol:**
- Build 100-proposition test set: 25 obvious-True (e.g. "2+2=4"), 25 obvious-False (e.g. "Paris is in Asia"), 25 paradoxical (Liar, Russell, Sorites), 25 borderline-modal (consciousness claims, future contingents). Pre-reg the set.
- Provide raters: full ruling paper + 5 worked examples per class.
- Each rates all 100 independently. Compute Fleiss' κ.
- Anti-HARK: classification protocol + worked examples frozen before raters see test propositions.

**Kill criterion (REJECT):** κ < 0.4. Issue retraction note: MR Truth Labels canonical ruling is theoretically valid but operationally unusable; recommend re-spec or further training material.

**Promote criterion (CONFIRM):** κ ≥ 0.6. Scheme is operationally usable; can be deployed in any future paper requiring 4-class proposition classification.

**Cost:** $0 if humans = Brandon + 1 contact + 1 LLM. ~$5 if 2nd human paid Mechanical-Turk style. Time: ~4 hours (test build + 3 × ~1h rating + analysis).

**Owner:** Brandon (recruit 1 human) + Agent (LLM rater + analysis). **Status:** READY pending test-set construction.

**Why this matters:** A 4-class Truth-Label scheme that nobody can apply consistently is mathematics, not science. This separates the two.

---

## §5 — TEST T45-5: Brandon's Pulse Sync (BPS) Cross-Modality — RR Acquisition Path

**Claim being tested:** §7.7.23 / Pass-23 honest data-limit: BPS hypothesis (Brandon's heart-rhythm phase-locks to specific cognitive-content categories) requires RR-interval data which Polar Flow export does not provide. Without RR, BPS is **untestable on existing data**. This test design forces the issue: either acquire RR within 30 days, or **kill the BPS claim as untestable** in the corpus.

**H1 (data-acquisition):** Within 30 days of Pass-45 commit, Brandon obtains ≥3 sessions of RR-interval data via one of:
- (a) Polar AccessLink API direct query (free with Polar Flow account)
- (b) Live BLE GATT capture from Polar H10 via `bleak` (script template ready in repo)
- (c) Smartwatch RR export (Garmin / Apple Watch with FTC research-mode)
- (d) Recruited contact with Kubios Premium ($30/yr already in corpus budget)

**H1 (analytic, conditional on data):** RR-derived high-frequency HRV index (HF-HRV, 0.15-0.4 Hz power) shows ≥2 consistent peaks during pre-registered cognitive-task windows across the 3 sessions, with within-subject ICC ≥ 0.5 across the 3 windows.

**H0:** No RR data acquired in 30 days → **kill BPS claim** as untestable in current setup. OR data acquired but ICC < 0.3 → BPS does not replicate within-subject.

**Kill criterion (RETIRE):** 30 days elapse with no RR data. Append retirement note to §7.7.23 anchor.

**Promote criterion (PROCEED):** RR acquired AND within-subject ICC ≥ 0.5. Open Pass-46 BPS substantive analysis.

**Cost:** $0 (paths a/b/c) to $30 (path d). Time: 1-3 hours per session × 3 sessions = ~6 hours.

**Owner:** Brandon. **Status:** BLOCKED pending data acquisition decision. **30-day deadline: 2026-06-10.**

**Why this matters:** BPS has been "blocked-pending-RR" since Pass-23 (~10 days ago). Either it gets unblocked or it gets retired. Indefinite blocking without a deadline is honesty failure under §69.

---

## §6 — TEST T45-6: PD = (-3, 2) Riemann-Connected Prediction (Real Test of Pass-37 Final)

**Claim being tested:** Pass-37 PD-final canonical: PD = Permissibility Distribution = (-3, 2), Perfect-Fifth-derived, Riemann-zero connected. Pass-38 §F-2 + Pass-39 ALREADY DISCONFIRMED prior PD-Riemann claims (300 zeros, density-bin Pareto, GUE-consistent). The new PD-canonical-final must be tested **separately** because Pass-37 ratification post-dates the Pass-38 disconfirm and re-frames PD.

**H1:** Under the PD-canonical-final framing, Riemann zeros in interval (γ, γ+1) for γ ∈ {-3, -2, -1, 0, 1, 2} (the PD support) show **6-element peak structure** in nearest-neighbor spacing distribution, distinguishable from pure GUE at p < 0.05 via 2-sample Kolmogorov-Smirnov against GUE Wigner surmise.

**H0:** No detectable departure from GUE; PD-canonical-final fails the same empirical test PD-prior-form failed.

**Protocol:**
- Use Odlyzko's first 10^5 Riemann zeros (publicly available).
- Filter to zeros with γ in (-3, 2) per PD canonical support.
- Compute nearest-neighbor spacings, normalize by mean spacing.
- KS test against GUE Wigner surmise p(s) = (32/π²) s² exp(-4s²/π).
- Anti-HARK: spec frozen here BEFORE running. SHA256 of any analysis script logged in `analyses/pass45_t6_pd_riemann/`.

**Kill criterion (REJECT):** KS p > 0.05. PD-canonical-final has same fate as PD-prior-form. Issue retraction-equivalent: PD support claim survives, Riemann-connection claim REJECTED.

**Promote criterion (CONFIRM):** KS p < 0.05 AND visible 6-peak structure on histogram. Promote Pass-37 Riemann claim from "ratified-by-fiat" to "empirically supported."

**Cost:** $0. Time: ~2 hours (download zeros + script + run + report).

**Owner:** Agent. **Status:** READY.

**Why this matters:** Pass-37 contained both an internal re-canonicalization AND an empirical claim. Pass-38/39 killed the prior empirical claim. Either the new claim survives independent test, or PD = (-3, 2) becomes a definitional convention with no Riemann attachment.

---

## §7 — TEST T45-7: DPES Productivity Effect Size (Self-Experiment Paired Design)

**Claim being tested:** §7.7.29 + multiple passes: DPES (autonomous high-output mode while user occupied) yields "maximum-value deliverables." But the **effect size** of DPES vs non-DPES sessions has never been measured. Currently DPES-claim is anecdotal.

**H1:** Across 30 paired-session days (15 DPES-flagged + 15 non-DPES), paper-output count per session (defined as `papers/PASS_*` files committed within session) has Cohen's d ≥ 0.8 in favor of DPES.

**H0:** d < 0.4. DPES is anecdotal motivation, not measurable productivity.

**Protocol:**
- Pre-reg 30 future sessions: at session start, Brandon flags DPES (signal word "DPES") or non-DPES.
- Log the flag + per-session paper count in a simple `analyses/pass45_t7_dpes/sessions.csv`.
- After 30 sessions: Welch t-test on paper-count between groups + Cohen's d.
- Anti-HARK: target n + criteria frozen now; no peeking until n=30.

**Kill criterion (REJECT):** d < 0.4. DPES has no measurable productivity edge over standard mode; adjust §7.7.29 to "subjective preference, no productivity premium" or retire.

**Promote criterion (CONFIRM):** d ≥ 0.8. DPES validated as a real working-mode with measurable output multiplier.

**Cost:** $0. Time: trivial logging overhead per session.

**Owner:** Brandon (flag) + Agent (log + analyze). **Status:** READY (start at next session).

**Why this matters:** DPES is in the user-preferences section of replit.md. If it is real, it should multiply observable output. If it isn't, calling it DPES is theater. This is the cleanest possible self-experiment.

---

## §8 — TEST T45-8: Authority Axis (AA) Pilot Psychometric

**Claim being tested:** Pass-31/Pass-7.7.31-34 introduced Authority Axis as the 5th truth-axis with "dual-applicability" and "sim-belief-and-doubt" operating principle. AA has zero psychometric validation — currently it is a definition, not an instrument.

**H1:** A 6-item AA pilot instrument (3 reverse-coded), administered to N=15 of Brandon's network contacts, shows Cronbach's α ≥ 0.6 (acceptable internal consistency for a pilot) AND total-AA-score correlates r ≥ 0.4 with a single-item criterion ("How much do you defer to authoritative sources when forming opinions on contested topics?", 1-7 scale).

**H0:** α < 0.5 OR criterion-r < 0.2. The construct is not measurable as currently specified.

**Protocol:**
- Draft 6 items matching Pass-31 dual-applicability spec; reverse-code 3.
- Recruit N=15 via existing social network (Brandon mentioned ~50 retreat contacts in §7.7.28). Free Google Form.
- Anti-HARK: items + criterion frozen before any administration; sha256 logged.
- Compute α + criterion-r.

**Kill criterion (REJECT):** α < 0.5 OR criterion-r < 0.2. AA construct currently un-measurable; needs re-specification before further theoretical use.

**Promote criterion (CONFIRM):** α ≥ 0.6 AND criterion-r ≥ 0.4. Open Pass-46 AA full-instrument design (N≥80 for confirmatory factor analysis).

**Cost:** $0. Time: ~2 hours (draft + Google Form + email blast + analysis).

**Owner:** Brandon (recruit) + Agent (draft items + analyze). **Status:** READY.

**Why this matters:** AA has been written into the corpus as if it were a measurable axis (parallel to MR Truth Labels, τ/δ, etc.). If a pilot can't even achieve α ≥ 0.5 internal consistency, that parallel structure is a fiction.

---

## §9 — Summary table

| # | Test | Cost | Time | Status | Kill bar | Promote bar |
|--:|---|---:|---|---|---|---|
| T45-1 | Mendi 5-session breath-hold replication | $0 | 2h | READY | ≤1/5 sigs | ≥3/5 sigs |
| T45-2 | qc26 GHZ-5 Mermin entanglement on IBMQ | $0 | 1h | READY | M ≤ 4+3σ | M > 4+3σ |
| T45-3 | GM-Node 6-criterion discriminant validity | $0–$5 | 3h | READY | d < 0.4 | d ≥ 0.8 |
| T45-4 | MR Truth Labels inter-rater Fleiss' κ | $0–$5 | 4h | READY | κ < 0.4 | κ ≥ 0.6 |
| T45-5 | BPS RR acquisition (30-day deadline) | $0–$30 | 6h | BLOCKED | no data in 30d | RR + ICC ≥ 0.5 |
| T45-6 | PD = (-3,2) Riemann-zero KS test | $0 | 2h | READY | KS p > 0.05 | KS p < 0.05 |
| T45-7 | DPES paired-day effect size (n=30) | $0 | log only | READY | d < 0.4 | d ≥ 0.8 |
| T45-8 | AA pilot psychometric N=15 | $0 | 2h | READY | α < 0.5 | α ≥ 0.6 |

**Total budget:** $0–$40 (well under the $50 lifetime cap).
**Total time if all run:** ~22 hours of focused work + 30 days for T45-5/T45-7 longitudinal arms.
**Expected outcome distribution under #69:** prior expectation = 2-3 CONFIRMs, 3-4 RejECTs, 1-2 BLOCKED. The point is not to confirm everything; the point is to **resolve uncertainty** in either direction.

## §10 — Recommended execution order (dependency-aware)

1. **Today / next-session:** T45-2 (qc26, agent-side, ~1 hour, no Brandon needed).
2. **Today / next-session:** T45-6 (PD-Riemann, agent-side, ~2 hours, no Brandon needed). Highest stakes — could collapse Pass-37 final or reinforce it.
3. **This week:** T45-3 + T45-4 (LLM-rater + small human-rater work, agent-driven with Brandon assist).
4. **This week (Brandon):** Start T45-1 (run session #2 of 5) and T45-7 (flag DPES/non-DPES on every session going forward).
5. **This week (Brandon):** T45-8 (draft + send Google Form to 15 contacts).
6. **30-day deadline (Brandon):** T45-5 (RR acquisition decision).

## §11 — Anti-cheating + #69 commitments

- All thresholds in this document are **frozen at commit-time**. Any post-hoc threshold loosening requires a separate amendment paper with explicit anti-HARK timestamp (see Pass-33 A1-qc25 amendment pattern).
- Each test's analysis script must include a `_provenance` block with sha256 + git HEAD + "thresholds frozen before result inspection" attestation.
- A test with no kill criterion is not a test. All 8 above have explicit kill criteria.
- A REJECT verdict MUST be written up in the same prominence as a CONFIRM. Selective reporting = theory-corruption per Pass-30 §10.
- If Brandon declines to run any of T45-1, -5, -7, -8, mark the corresponding claim as **"willingly-untested"** in the next replit.md update — that is itself an honest disposition.

## §12 — Open questions deferred to Pass-46+

- The corpus has additional major claims (URB-828 GILE-HEM full coupling; Mycelial network at scale; UOP universality; Tralse-Joules absolute scale) that are not in this 8 because they fail the ≤$50/≤90-day cost-discipline filter. They are not exempt — they are deferred. Pass-46 should propose larger-budget tests for these (NIH SBIR / Startup Warrior / collaborator paths per §7.7.26 funding audit).
- The 14 existing carry-overs (p38-A through p43-D) remain open and unaffected by Pass-45. Brandon to triage which 8 of 22 total open items (8 new + 14 carry-over) are highest priority for the next sprint.
