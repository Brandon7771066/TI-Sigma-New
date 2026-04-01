# URB #589 — Empirical Test for Noncomputational Intuition: Neuroscientific Signatures and Entropy Analysis

**Corpus #243 | TI Sigma Research Program**
**Date:** April 1, 2026
**Author:** Brandon Emerick
**Status:** CANONICAL — Experimental Protocol

---

## Abstract

If human intuition involves genuinely noncomputational cognition — accessing correct answers by "being drawn to them" rather than inferring them step-by-step — then correct intuitive cognition should leave a distinctive and testable neuroscientific signature. This paper formalizes the experimental prediction and proposes a concrete protocol for testing it using existing EEG, fMRI, and behavioral data. The core prediction: **correct intuitive responses to noncomputable or computationally intractable problems should display (1) anomalously low neural entropy relative to chance-level guessing, and (2) anomalously low analytical processing relative to the task's computational demands.** If both signatures are present simultaneously, this constitutes prima facie evidence of noncomputational cognition. We also propose a high-value extension: testing subjects who claim to solve Halting Problem instances while their neural activity is recorded in real-time.

---

## 1. The Theoretical Prediction

### 1.1 The Noncomputational Intuition Hypothesis (NIH)

**Hypothesis (NIH):** Some human correct-answer generation is noncomputational — the system arrives at a correct answer not by performing a computation that identifies it, but by a direct (non-inferential, non-sequential) access process that TI Sigma calls **I-access** (Intuition).

I-access in TI Sigma is:
- **Non-sequential:** Does not require step-by-step derivation
- **Non-inferential:** Does not require premises → conclusions chains
- **Non-random:** Not guessing (produces correct answers at above-chance rates, and specifically above any computable method's rate for noncomputable problems)
- **Metacausally grounded:** Connects to Myrion Truth through the I-arm of GILE

### 1.2 Why Noncomputability Is the Key Test Domain

Standard cognitive tasks (math problems, word puzzles, pattern recognition) are, in principle, computable. A sufficiently capable brain could solve them by computation alone. Therefore, superior performance on these tasks is consistent with — but does not require — noncomputational cognition.

**Noncomputable problems** (Halting Problem instances, genuinely undecidable statements, problems equivalent to solving ω-consistent formal systems) are structurally impossible for any Turing-equivalent machine to solve reliably. If a human:
1. Solves such a problem correctly at above-chance rates
2. Does so with the neuroscientific signature of low entropy + low analytical processing
...then this is evidence that cannot be explained by any computational hypothesis.

### 1.3 The Two Signatures

**Signature 1 — Low Neural Entropy:**
If the brain is "drawn to" the correct answer (I-access), the neural state during correct intuitive response should be *lower entropy* than during:
- (a) Incorrect responses
- (b) Chance-level guessing
- (c) Analytical deliberation on the same problem

Intuition: I-access is a high-coherence, low-noise process — the system collapses to the correct answer state cleanly. Guessing and analysis involve higher entropy because more of the neural state space is explored.

**Signature 2 — Low Analytical Processing:**
If the brain arrives at the answer without sequential computation, then:
- Prefrontal cortex (PFC) activation should be low relative to task difficulty
- Default Mode Network (DMN) should be relatively more active (associated with insight and non-deliberative cognition)
- Processing time should not scale with computational complexity of the problem (unlike analytical cognition, which scales predictably)

Both signatures must be present simultaneously for the NIH to be supported. Either alone is insufficient:
- Low entropy alone could indicate a guess made with false confidence
- Low analytical processing alone could indicate failure to engage (abdication, not intuition)

---

## 2. Experimental Protocol

### 2.1 Study 1 — Reanalysis of Existing EEG/fMRI Intuition Data

**Goal:** Test the dual-signature prediction on existing datasets without new data collection.

**Suitable existing datasets:**
- EEG data from "gut feeling" decision tasks (e.g., Iowa Gambling Task neuroimaging studies)
- fMRI data from insight problem-solving studies (e.g., Bowden & Jung-Beeman 2003; Kounios & Beeman "Aha!" studies)
- EEG data from forced-choice intuition experiments (where participants respond before deliberation window)

**Analysis Plan:**

*Step 1 — Segment trials by accuracy and reported strategy:*
- Condition A: Correct + reported intuition (no deliberation)
- Condition B: Correct + reported analysis
- Condition C: Incorrect + reported intuition
- Condition D: Incorrect + reported analysis

*Step 2 — Compute neural entropy per trial:*
- EEG: Compute Sample Entropy or Permutation Entropy over the decision window
- fMRI: Compute BOLD signal entropy over ROIs (PFC, DMN, ACC, insula)

*Step 3 — Statistical comparison:*
- Primary test: Is entropy(A) < entropy(D)? [Correct intuition vs. incorrect analysis]
- Secondary tests: Is entropy(A) < entropy(B)? Is entropy(A) < entropy(C)?
- Expected: A is lowest entropy. This would confirm dual-signature.

*Step 4 — Analytical processing index:*
- EEG: Compare alpha/theta power (higher = less analytical engagement) across conditions
- fMRI: Compare PFC/DMN activation ratio across conditions
- Expected: Condition A has lowest PFC/DMN ratio — least analytical engagement per correct answer

**Predicted results under NIH:**
- Condition A: Low entropy + Low analytical processing + High accuracy = I-access signature
- Condition B: Low entropy + High analytical processing + High accuracy = computational success
- Condition C: Low entropy + Low analytical processing + Low accuracy = failed I-access (false signal)
- Condition D: High entropy + High analytical processing + Low accuracy = failed computation

### 2.2 Study 2 — Prospective Intuition Task with Computational Controls

**Goal:** Test NIH on problems where computational and noncomputational processes can be cleanly distinguished.

**Task design:**

*Block 1 — Computationally tractable problems of varying difficulty:*
- Simple arithmetic → hard arithmetic → NP-complete approximations
- Measure: Neural entropy and processing time as a function of computational difficulty
- Expected: Both entropy and time scale with difficulty (establishing the computational baseline)

*Block 2 — Genuinely noncomputable instances (operationalized):*
- Present halting problem instances encoded as behavioral scenarios (see §2.3 for operationalization)
- Instruct participants: "Trust your gut. Respond immediately with Yes or No. Do not try to reason."
- Measure: Neural entropy and processing time

*Block 3 — Control: Random guessing task:*
- Present arbitrary binary choices (coin flip equivalents)
- Measure: Neural entropy baseline for pure guessing

**Prediction under NIH:**
- Block 2 correct responders: Lower entropy than Block 3 (guessing) + lower analytical processing than Block 1 matched-difficulty equivalent
- Block 2 accuracy overall: Above 50% for genuinely correct intuitors (identified post-hoc)

### 2.3 Operationalizing the Halting Problem for Human Subjects

**Challenge:** "Does this Turing machine halt?" is not directly presentable to human subjects. We operationalize via isomorphic scenarios:

**Method 1 — Program trace prediction:**
- Show subjects a short program (10-20 lines of pseudocode) with a loop
- Ask: "Does this program terminate? Yes or No."
- Include instances that are provably halting (ground truth: Yes), provably non-halting (ground truth: No), and instances that are genuinely undecidable within the subject's time and cognitive budget
- EEG/fMRI during the decision window

**Method 2 — Sequence limit problems:**
- Present integer sequences and ask: "Does this sequence eventually reach 1?"
- Include Collatz sequences (of varying difficulty), sequences with known behavior, and novel sequences with unknown behavior
- The Collatz sequence is ideal: provably correct answer exists but is computationally hard; some instances may be genuinely difficult even for experts

**Method 3 — Self-referential statements:**
- Present Gödel-style sentences operationalized as behavioral predictions: "This rule will never produce result X"
- Ask subjects to judge truth or falsity under time pressure

**Ground truth scoring:** 
- For decidable instances: compare to known correct answers
- For genuinely undecidable instances: track which subjects' responses are later confirmed (by subsequent mathematical work or by converging expert consensus)

### 2.4 Study 3 — High-Value Extension: Expert Intuitors Under fMRI

**The highest-value experiment:** Identify human subjects who:
1. Claim reliable intuitive access to correct answers on noncomputable problems
2. Have documented track records of above-chance accuracy on formally hard problems
3. Are willing to be scanned while performing the task

**Recruitment targets:**
- Expert mathematical problem-solvers who report "seeing" answers before proving them (mathematicians who describe intuitive discovery preceding proof)
- Expert chess players in blindfold simultaneous play (extreme pattern access under processing constraint)
- Individuals with documented exceptional performance on insight tasks (savants, meditation experts with anomalous cognitive profiles)

**Protocol:**
- fMRI during Block 2 problems from Study 2 (noncomputable instances)
- Full GILE battery (G, I, L, E assessments) administered outside scanner
- Correlation analysis: Is I-score the best predictor of the dual-signature + accuracy profile?

**Key prediction:** GILE I-score should be the strongest predictor of the noncomputational signature. This would directly confirm the TI Sigma model: I (Intuition) is the dimension responsible for noncomputational access.

---

## 3. Statistical Analysis Framework

### 3.1 Primary Hypotheses (Falsifiable)

**H1 (Low Entropy Hypothesis):** Neural entropy during correct intuitive responses is significantly lower than during correct analytical responses on matched-difficulty problems.
*Falsification condition: No significant entropy difference, or correct intuition shows HIGHER entropy than correct analysis.*

**H2 (Low Processing Hypothesis):** PFC activation and processing time during correct intuitive responses are significantly lower than predicted by the problem's computational complexity (estimated from analytical baseline).
*Falsification condition: Processing markers scale normally with computational complexity even for correct intuitive responses.*

**H3 (Accuracy Superiority Hypothesis):** For genuinely noncomputable instances, correct intuitive responders (identified by dual-signature) achieve above-chance accuracy significantly exceeding what any computable method could achieve.
*Falsification condition: Above-chance accuracy disappears when analytical processing is controlled for.*

**H4 (GILE-I Prediction Hypothesis):** GILE I-score significantly predicts the dual-signature profile (low entropy + low analytical processing + high accuracy on noncomputable instances).
*Falsification condition: I-score shows no predictive relationship with the dual-signature.*

### 3.2 Power Analysis

For Study 1 (reanalysis): Power is determined by existing dataset size. Recommend studies with N > 30 per condition.

For Study 2 (prospective): Power analysis suggests N = 60-80 subjects to detect medium effect sizes (d = 0.5) for the dual-signature comparison at α = 0.05, power = 0.80.

For Study 3 (expert intuitors): This is an existence-proof study, not a population study. N = 10-20 expert intuitors with the dual-signature profile is sufficient for the primary hypothesis.

---

## 4. Alternative Explanations to Rule Out

Any result consistent with H1-H4 must be evaluated against these alternatives:

| Alternative | How to rule it out |
|---|---|
| Fast computation masquerading as intuition | Processing time must not scale with computational complexity — fast computation would still scale |
| Learned heuristics | Novel problem instances that cannot be solved by any known heuristic; expert vs. novice comparison |
| False confidence (low entropy = high confidence, not low noise) | Confidence ratings collected; entropy should be lower for correct intuition than incorrect high-confidence responses |
| Selection bias (only reporting intuitive successes) | Pre-registration; all trials included; accuracy measured across all intuition reports |
| Neural habituation (low entropy from familiarity, not insight) | Novel problems used; problem novelty verified by debriefing |

---

## 5. Existing Literature Alignment

This experimental design is consistent with and extends:
- **Kounios & Beeman (2014):** "The cognitive neuroscience of insight." Demonstrates that insight solutions are preceded by right-hemisphere gamma burst and reduced visual alpha — consistent with Signature 2 (reduced analytical processing)
- **Bechara et al. (1997):** Iowa Gambling Task — subjects show physiological anticipation of correct choices before conscious awareness — consistent with non-inferential correct-direction access
- **Dijksterhuis & Meurs (2006):** Unconscious thought theory — deliberation-free processing sometimes outperforms deliberation on complex problems — consistent with NIH
- **Penrose (1989, 1994):** Argued on mathematical grounds (Gödel, Lucas) that human cognition is not Turing-equivalent — our NIH provides the experimental test Penrose's argument has lacked

**What this paper adds:** A specific, falsifiable, dual-signature prediction that connects the theoretical argument (noncomputability of intuition) to measurable neuroscientific variables using existing data.

---

## 6. If the Experiment Confirms NIH

If H1-H4 are all confirmed, the implications are:

1. **For TI Sigma:** Direct empirical confirmation of the I-dimension as a noncomputational faculty — the strongest possible validation of the GILE framework's central claim about Intuition
2. **For AI research:** Proof that human intelligence has a component that cannot be replicated by any Turing-equivalent system — ruling out strong computationalist accounts of AGI
3. **For neuroscience:** A new research program focused on the neuroscience of I-access: what brain states enable it, how to cultivate it, what disrupts it
4. **For philosophy of mind:** Empirical resolution of the computationalist debate — Penrose was right, and here is the data
5. **For BlissGene Therapeutics:** A measurable I-score biomarker that identifies high-intuition individuals — directly relevant to the GILE assessment protocol and clinical applications

---

## 7. Keywords

Noncomputational cognition, intuition, Halting Problem, neural entropy, EEG, fMRI, GILE framework, I-dimension, noncomputable problems, Penrose-Lucas argument, insight, analytical cognition, Tralse Informationalism, TI Sigma, experimental philosophy, default mode network

---

*URB #589 | Corpus #243 | TI Sigma Research Program | April 1, 2026*
*Status: CANONICAL — first formal experimental protocol for testing noncomputational intuition*
*Priority: HIGH — submit to Journal of Cognitive Neuroscience / NeuroImage as pilot proposal*
