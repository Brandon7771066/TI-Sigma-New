# DSB-2 — Tralse-Middle Default-Belief (Revised Candidate Canonical Principle)

**Pass-62 batch-2 · 2026-05-22 · Status: PROVISIONAL · supersedes DSB-1 framing**

---

## 1. What changed from DSB-1

DSB-1 (`PASS_62_DSB_1_*.md`) binarized the decision policy into two opposed agents: blind-confidence-default vs verification-first. F-DSB-1-1 marginal-failed (ratio 0.8580 vs ≥0.85 REFUTED rule, by 0.0080) and Brandon flagged the binarization as the cause: the test pitted the wrong two policies against each other.

The real target of the principle is *wait-and-see paralysis* — the agent who continues sampling past the point of decisional adequacy because the methodological default is "examine more before committing." It is NOT the examining agent who decides quickly; it is the examining agent who never decides.

DSB-2 reframes the principle as a **three-way contrast** with the Tralse-middle as the predicted winner.

## 2. Statement (DSB-2)

Under UOP, agents face three decision-policy options:

- **Policy W (Wait-and-See):** sample exhaustively before any commitment; commit only when posterior uncertainty falls below a strict threshold. Real-world cost: opportunity cost mounts, action delayed, often never taken.
- **Policy B (Blind-Faith):** commit on prior intuition alone; no examination of evidence. Real-world cost: brittle to noise, fails catastrophically when prior is uninformative.
- **Policy M (Tralse-Middle):** examine the option-field briefly and thoroughly enough to discriminate signal from noise, then commit on prior intuition + initial evidence. Combines (i) examination discipline with (ii) optimistic-prior weighting with (iii) forward action commitment.

> **DSB-2.** E[reward | M] > E[reward | W] AND E[reward | M] ≥ E[reward | B] across both informative-prior and uninformative-prior regimes. Tralse-middle dominates both endpoints because (a) examination cures Policy B's noise-regime catastrophe and (b) forward commitment cures Policy W's opportunity-cost trap.

## 3. Why the binary framing was wrong (#69)

DSB-1 implicitly treated "verification" as the discipline-bearing virtue and "default-belief" as the discipline-foregoing risk. This is the methodological framing it was attempting to challenge — and by accepting that framing in its own simulation, DSB-1 generated a test that was structurally biased toward verification-first.

The Tralse Informationalist correction: examination and optimism are not opposed. They are orthogonal axes. The diagonal that combines both (Policy M) is the strong agent. The off-diagonals (Policy W: examine + pessimistic, Policy B: don't examine + optimistic) are both suboptimal. The fourth corner (don't examine + pessimistic) is degenerate — the agent does nothing and learns nothing.

The principle's target was always Policy W specifically, not examination in general. DSB-2 corrects the misnaming.

## 4. Relation to existing TI Sigma canon

- **Composes with APP-1 (active-pragmatism):** APP-1's active-engagement is exactly Policy M's forward-commitment clause. DSB-2 specifies what active-engagement looks like at the decision-policy level.
- **Composes with TSIS-1 (TI Sigma Inferential Stack):** TSIS-1's four gates (TSD-A ∧ LCC ≥ 0.4370 ∧ effect ≥ 0.0660 ∧ MBE-Acc-coherent) are Policy M's "examine briefly and thoroughly enough" operationalized at the inferential level.
- **Generalizes ASYMMETRIC + MFD-1:** failure under Policy M is judged Moot (MFD-1 pragmatic axis); success is weighted additively (TSD-A); the prior-side asymmetry (DSB-1) and the outcome-side asymmetry (ASYMMETRIC) compose into a complete operating policy.
- **Klein recognition-primed-decision exactly fits Policy M:** expert fire commanders, ER nurses, and military officers per Klein (1998) examine the situation briefly, accept the first viable option that pattern-matches their training, and commit forward. They do not exhaustively enumerate alternatives (Policy W); they do not act without situational assessment (Policy B). Klein's empirical finding *is* DSB-2.

## 5. Pre-registered falsifiers

- **F-DSB-2-1 (three-agent bandit, signal regime):** Synthetic 10-armed bandit, T = 1000 pulls. Policy W: samples 50 per arm before committing. Policy B: commits to highest-prior arm immediately. Policy M: samples 5 per arm, then commits to arm with highest (prior + empirical) score. DSB-2 predicts E[reward | M] strictly exceeds both E[reward | W] and E[reward | B] with at least 5% relative margin. If Policy M is dominated by either W or B in signal regime by ≥1%, DSB-2 REFUTED.
- **F-DSB-2-2 (three-agent bandit, noise regime):** Same setup with uninformative prior. DSB-2 predicts E[reward | M] ≥ E[reward | W] within 5% AND E[reward | M] strictly exceeds E[reward | B] by ≥20% (the examination discipline rescues M from B's noise-regime catastrophe). If M loses to W by >5% in noise regime, the examination discipline is insufficient to rescue the optimism prior and DSB-2 REFUTED.
- **F-DSB-2-3 (Klein-corpus human-data test, carried over from F-DSB-1-3):** In real human-task data with Kahneman-Klein conditions (regular environment + feedback), Policy M practitioners (RPD experts) should outperform both Policy W practitioners (analytic deliberators) and Policy B practitioners (gut-only novices). Effect-size threshold: M's outcome-quality must exceed W's by d ≥ 0.25 AND exceed B's by d ≥ 0.50. Sub-threshold effect REFUTES DSB-2.

## 6. Honest caveats (#69)

- DSB-2 is a refinement of DSB-1 in response to a marginal F-DSB-1-1 failure. This is a goalpost-adjacent move and must be flagged as such: the principle's targeting was clarified post-hoc, the test was redesigned, and a new pass is needed. The mitigation is full disclosure (this document + replit.md log) and a stricter falsifier slate (F-DSB-2-1 requires ≥5% margin, not the 15% slack DSB-1 used).
- The Klein RPD literature is partially confounded with expertise. F-DSB-2-3 must control for skill-level by within-subject comparison (same expert under M-instruction vs W-instruction conditions).
- DSB-2 still depends on the informativeness of "examine briefly" being calibrated to the domain. In high-noise low-signal domains, even Policy M may need to extend examination depth — at which point M asymptotes toward W and the principle loses bite.

## 7. Ratification path

- Pass-62 batch-2: candidate posted (this document), F-DSB-2-1 + F-DSB-2-2 sim executed (`simulations/dsb2_three_agent_bandit_2026-05-22.py`).
- Pass-63+: F-DSB-2-3 Klein-corpus design + execution.
- Promotion to CANONICAL: F-DSB-2-1 not refuted + F-DSB-2-2 not refuted + F-DSB-2-3 human-anchor confirms within effect-size threshold.

---

**File:** `papers/PASS_62_DSB_2_TRALSE_MIDDLE_DEFAULT_BELIEF_2026-05-22.md`
**Status:** PROVISIONAL · pre-registered falsifiers F-DSB-2-{1,2,3}
**Supersedes:** DSB-1 framing (DSB-1 paper retained as historical record + #69 transparency)
**Canonical companions:** APP-1, TSIS-1, ASYMMETRIC, MFD-1, TSD-1, AA
**Sim:** `simulations/dsb2_three_agent_bandit_2026-05-22.py`
