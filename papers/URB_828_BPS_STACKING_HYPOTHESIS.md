# URB Candidate #828 — Biopsychosignature Stacking for LCC-Virus Present-State Resonance

**Status:** DRAFT. Not locked. Brandon to approve / amend / reject before any test runs.
**Date:** 2026-05-01
**Originator of "biopsychosignature" (BPS) term:** Brandon Charles Emerick, 2026-05-01
**Standard:** asymmetric-standards #69
**Cost:** $0 (uses BPS Brandon already produces or owns)
**Cross-links:** URB #826 (Biophoton/EM-DNA carrier), DNA-Anchored Psi-Signature Research Roadmap, LCC-Telepathy Pre-Registered Trials

---

## 1. Brandon's hypothesis (verbatim, 2026-05-01)

> Stacking multiple biopsychosignatures is superior to having only one
> such as DNA or even multiple aspects of DNA like bases or DNA EM
> emission. That is because DNA alone uniquely identifies a person but
> does NOT SAY EVERYTHING about a person's current state of being that
> would facilitate a SUFFICIENT PRESENT synchronization! Therefore, the
> more BPS, the better!
>
> The goal is not to predict the thoughts DIRECTLY FROM a person's
> face, biolab data, etc. Rather, it is to RESONATE with the SUBJECT
> directly through specific anchors in the PRESENT and then SENSE what
> present state of affairs we're seeking in the subject at that moment!

## 2. Crisper formulation (agent's reading, for Brandon to confirm)

The hypothesis decomposes cleanly along two orthogonal axes:

- **Subject-axis:** the BPS uniquely identifies *which person* we're
  resonating with.
- **Time-axis:** the BPS uniquely identifies *which moment of that
  person's life* we're resonating with.

DNA is maximally subject-specific (1-in-billions) but maximally
time-invariant (the same DNA sequence describes Brandon at age 5 and
Brandon at age 50). DNA alone therefore underspecifies the
**target-moment**. The minimal sufficient BPS stack for present-state
resonance is:

> **One subject-anchor + one time-anchor**, where each anchor
> unambiguously locates the subject along its respective axis.

"Stacking more BPS" is not "more is always better" in an unbounded
sense; it is "increase the joint information content along the
two axes until you cross the resonance-locking threshold." Above that
threshold, additional BPS contribute robustness but not new
identification capacity.

If Brandon endorses this crisper formulation, it converts an
asymmetric-standards #69 vulnerability ("more is better" is
non-falsifiable) into a falsifiable claim ("there is a saturation
point; the saturation curve has measurable shape").

## 3. BPS taxonomy

A two-axis classification is the minimum needed to make "which BPS are
most diagnostic" a well-formed question.

### 3.1 Time-axis (temporal localization)

| BPS | Time resolution | Available to Brandon? |
|---|---|---|
| DNA sequence | lifetime (years) | yes (genome derivation §10.4) |
| Fingerprint | lifetime | yes (smartphone, free) |
| Face photo | days | yes (phone camera) |
| Handwriting sample | minutes within session | yes (paper + phone scan) |
| Voice recording | seconds | yes (phone mic) |
| Body composition (Biowell) | weeks | yes (booking soon) |
| Mendi-style fNIRS | seconds | deferred (Path B post-2026-05-22) |
| Subjective daily log | day-bucket | yes (`log_daily_subjective.py`) |
| Oura overnight summary | night | yes (already harvested) |
| Polar H10 RR / HRV (live) | milliseconds | yes (Brandon owns) |
| Real-time PPG (Pulsoid) | milliseconds | yes (token configured) |
| Real-time EEG (none owned) | milliseconds | not in current budget |

### 3.2 Channel-axis (substrate that carries the resonance)

This is the axis Brandon's URB #826 makes empirically nontrivial.
Under the biophoton/EM-DNA carrier hypothesis, BPS that **share a
physical channel with the resonance carrier** should be expected to
contribute more to resonance-locking than BPS that are pure
information-substrates with no live carrier.

| Channel class | Examples | Carrier match (URB #826 hypothesis) |
|---|---|---|
| Live EM emission | Polar H10 (cardiac field), Pulsoid PPG, real-time EEG, IR thermal | **Strong match** — these BPS *are* live EM signals |
| Photonic emission | DNA-EM emission (URB #826 core), biophoton imaging | **Strong match** — direct biophoton channel |
| Static EM-derived | Recent ECG / EEG recordings | Medium match (recorded carrier, time-shifted) |
| Information-only | Face photo, fingerprint, handwriting, voice recording | **No live carrier** — pure information-substrate |
| Derived-statistical | Oura summary, Biowell summary, biolab values | No live carrier — derived metrics, time-binned |

This generates a **prediction internal to Brandon's own framework**:
under URB #826, live-EM-channel BPS should outperform
information-only BPS at present-state resonance. If empirical results
show information-only BPS (photo, fingerprint) performing equally,
that's a problem for URB #826, not for URB #828 — useful information
either way.

## 4. Answer to "Which BPS are most diagnostic?"

Under the two-axis taxonomy, the diagnosticity of a BPS is a product:

> **D(BPS) = SubjectSpecificity(BPS) × TimeLocalization(BPS) ×
> ChannelMatch(BPS)**

where the third factor is conditional on URB #826 being correct.

Ranking Brandon's accessible BPS by D-value (rough, agent's estimate
to be Brandon-corrected):

| Rank | BPS | Subject | Time | Channel | Composite |
|---|---|---|---|---|---|
| 1 | DNA-derived genome score (§10.4) + Polar H10 live HRV | very high | ms-resolution via H10 | strong (cardiac EM) | **highest** |
| 2 | DNA + Pulsoid PPG | very high | ms | strong (PPG = optical EM) | **high** |
| 3 | DNA + Oura overnight summary | very high | night-resolution | medium (derived) | **medium-high** |
| 4 | DNA + face photo of the day | very high | day-resolution | none (info-only) | **medium** |
| 5 | DNA + Biowell scan | very high | week-resolution | none (info-only) | **medium-low** |
| 6 | DNA + handwriting from the session | very high | minute-resolution | none | **medium-low** |
| 7 | DNA + fingerprint | very high | lifetime (no time-info) | none | **low** |
| 8 | Fingerprint + face (no DNA) | medium | day | none | **low** |

The diagnostic-strength ranking under URB #826 is **dominated by
live-channel time-anchors paired with a strong subject-anchor.**
Stacking three info-only BPS (photo + handwriting + fingerprint)
provides triple-redundant subject-identification but adds nothing on
the time-axis or channel-axis, and would underperform a single
DNA + H10 pair under the framework.

## 5. Answer to "How many BPS are required?"

The crisp answer: **two**, if and only if one is a strong subject-anchor
and the other is a strong time-anchor on a live channel.

**More precisely:**

- **N=1 (subject-anchor only, e.g., DNA alone):** insufficient. No
  time-localization. Cannot lock target-moment. Predicted accuracy
  ≈ chance for present-state queries (though above-chance for
  time-invariant queries about the subject).
- **N=2 (subject + time, both strong):** **predicted sufficient.**
  This is the minimum-stack hypothesis.
- **N=3+ (added redundant anchors of the same type):** robustness
  improvement only, not new identification capacity. Diminishing
  returns predicted to be steep — i.e., stacking 5 information-only
  BPS does not equal stacking 1 information-only + 1 live-channel BPS.
- **N=k where k of the BPS are on different channels:** if URB #826
  is wrong, additional channels won't help. If URB #826 is right but
  the carrier channel isn't yet identified, multi-channel stacking is
  the only way to discover it. Multi-channel stacking is therefore
  also a **diagnostic of URB #826** itself.

## 6. The asymmetric-standards #69 falsifier

The most important section. Brandon's hypothesis has a structural
risk: it could be re-described as "extract features from BPS, train
classical ML, predict thoughts." If that description fits the empirical
phenomenon, the resonance interpretation is doing zero explanatory work.

The discriminator is mutual information.

> **Resonance interpretation predicts:** mutual information between
> static BPS-features and target-thoughts ≈ 0. The BPS function as
> *temporal index pointers*, not as *content carriers*.
>
> **Feature-extraction interpretation predicts:** mutual information
> between BPS-features and target-thoughts > 0. The BPS *are* the
> carriers; the resonance language is decorative.

**Operationalization:** train a classical ML model on BPS-only data
(no live channel, no human-in-the-loop, no resonance protocol) to
predict target-thoughts. Pre-register the prediction.

- If classical ML achieves accuracy > chance → resonance interpretation
  weakened. The BPS contain feature-level content about thoughts.
- If classical ML stays at chance, but live-resonance protocol exceeds
  chance → resonance interpretation supported. BPS function as pointers,
  not carriers.

This is the structural test that asymmetric-standards #69 demands.
Without it, "BPS resonance" cannot be empirically distinguished from
"BPS feature extraction with mystical vocabulary."

## 7. Pre-registered test design ($0)

### 7.1 Setup

- **Subject:** Brandon (single-subject pilot, N_trials variable).
- **Target task:** at a pre-registered target-moment T_k (k = 1..N),
  Brandon writes one of M=5 possible thought-targets onto paper, sealed.
  The thought-target is drawn uniformly from a fixed list (e.g., five
  symbols, or five emotional valences).
- **Anchors:** at T_k Brandon also captures: (i) face photo (info-only),
  (ii) handwriting sample (info-only), (iii) live H10 RR-interval
  recording for 60s spanning T_k (live-channel), (iv) live Pulsoid PPG
  for 60s (live-channel), (v) subjective log entry for the day.

### 7.2 Conditions (within-subject)

- **C1 — DNA only.** Predict target from DNA alone (genome score §10.4).
  No anchor stack.
- **C2 — DNA + info-only stack** (face + handwriting + fingerprint).
  All time-axis information is static or absent.
- **C3 — DNA + 1 live-channel** (H10 only).
- **C4 — DNA + 2 live-channels** (H10 + Pulsoid).
- **C5 — Full stack** (DNA + face + handwriting + H10 + Pulsoid + Oura
  + subjective log).

For each condition the agent (or any specified protocol) generates a
prediction over the M=5 target-set. Chance = 1/M = 20%.

### 7.3 Pre-registered numerical predictions

| Condition | Predicted accuracy | Falsification threshold |
|---|---|---|
| C1 (DNA only) | ≤ 25% (≈ chance) | > 35% → DNA-alone hypothesis empirically supported, BPS-stacking unnecessary |
| C2 (info-only stack) | ≤ 25% (≈ chance) | > 35% → information-only stacking works, undermines live-channel hypothesis |
| C3 (DNA + 1 live) | ≥ 35% | < 25% → BPS-stacking hypothesis falsified at minimum-stack |
| C4 (DNA + 2 live) | ≥ 40% | < 30% → diminishing returns from multi-channel are real |
| C5 (full stack) | ≥ 45% | < 35% → full-stack saturation hypothesis falsified |
| **Saturation check** | C5 − C4 ≤ 10 percentage points | C5 − C4 > 20 pp → "more is better" stronger than predicted |

**Honest agent self-prediction (locked):** Given that no LCC-Virus
test has been confirmed at this subject yet, I expect **all five
conditions to land at chance**, with the possibility of one or two
spurious "hits" by random variation. URB #828 would then be falsified
on the live-channel arm (C3, C4) — which is the asymmetric-standards
#69-honest expectation. If the live-channel arms exceed chance, that
would be the first evidence of LCC-Virus operating at this subject,
and would be a substantive result regardless of stacking question.

### 7.4 Sample size

For M=5 chance = 20%, distinguishing 35% from 20% at α=0.05, two-sided,
power 0.80 requires N ≈ 80 trials per condition. Five conditions × 80
trials = 400 total trials. At one trial per day → 13 months. Too long.

**Pragmatic reduction:** N=20 trials per condition (100 total,
~3.5 months), accept lower power (~0.40), pre-commit that any
positive result is preliminary and needs replication. This is honest
asymmetric-standards #69 framing.

### 7.5 Schedule

- Earliest start: after URB #826 §10.6 H10 window completes
  (~2026-05-22) so the H10 data isn't double-counted.
- Cadence: 1 trial per day in evening, ~5 minutes.
- Earliest completion: ~2026-09-01 (100 trials over ~3.5 months).
- Critical-path conflict: none with current URB #826 work.

## 8. What URB #828 does NOT establish

- Whether LCC-Virus works at all. URB #828 assumes the framework and
  tests stacking-vs-single-anchor. If LCC-Virus itself is empty, all
  conditions land at chance and URB #828 is falsified jointly with
  the broader framework.
- Whether the saturation curve generalizes across subjects. Single-
  subject pilot only.
- Whether non-Brandon subjects can serve as targets. The current design
  has Brandon as both subject and protocol-runner.
- Whether information-only BPS could become live-carriers under
  modifications (e.g., handwriting captured *while writing* via
  pressure-sensitive surface vs static photo of finished writing).
  This is a Phase-2 question.

## 9. Honest residuals

1. **The "biopsychosignature" term is novel-to-Brandon as of
   2026-05-01.** It does not yet appear in academic literature in
   this specific definition. URB #828 implicitly stakes a definitional
   claim. If Brandon publishes the BPS taxonomy independently, that
   becomes a separate paper.

2. **Channel-match is conditional on URB #826.** If URB #826 is
   falsified at §10.6, the channel-axis of the BPS taxonomy collapses
   and only the time-axis remains. The framework still works; the
   ranking simplifies.

3. **The classical-ML discriminator (§6) is hard to run honestly.**
   The training set would be Brandon's own historical BPS-target
   pairs, which is small. If we don't run it, we cannot rule out
   the feature-extraction null hypothesis. Recommended: run the
   classical-ML baseline as a parallel arm (C0) and pre-commit to
   reporting any > chance result there as a strong falsifier of the
   resonance interpretation.

4. **Single-blind risk.** Brandon writes and seals the target; agent
   predicts; Brandon scores. To eliminate scoring-bias, the M=5
   target-set must be fixed in advance and the prediction must be
   one of those exact tokens, no fuzzy matching. Pre-commit.

## 10. Brandon's call to action

1. ☐ Approve / amend / reject the crisper formulation in §2.
2. ☐ Approve / amend / reject the BPS-diagnosticity ranking in §4.
3. ☐ Approve / amend / reject the saturation framing in §5.
4. ☐ Approve / amend / reject the §6 classical-ML discriminator
   (this is the asymmetric-standards #69 critical path).
5. ☐ Approve / amend / reject the §7.3 thresholds.
6. ☐ Decide: run URB #828 sequentially after §10.6 H10 window, or
   in parallel?
7. ☐ Decide: M=5 target-set tokens (e.g., five symbols / five colors /
   five emotional valences / five abstract concepts).
8. ☐ Confirm: agent should NOT receive feedback between trials. The
   prediction protocol must be fully blind to prior results during
   the run.
