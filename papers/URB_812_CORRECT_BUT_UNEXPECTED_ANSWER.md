# URB #812 — The Correct-But-Unexpected-Answer Phenomenon as a TI Sigma Diagnostic. Why "Communication Failure" Is Often the Asker's Category Error, Not the Answerer's Fault.

**Author:** Brandon Charles Emerick
**Date:** April 30, 2026
**Series:** Unified Research Brief #812
**Status:** Cognitive-diagnostic note. Identifies a structurally common evaluation failure in conventional grading environments (school, conventional workplaces, structured interviews): the asker confuses *"the answer matches my expected set"* with *"the answer is correct"* and mislabels the resulting mismatch as a communication failure on the answerer's end. Provides the formal E_Q vs C_Q decomposition that names the failure cleanly and explains why divergent-thinking patterns are punished in grader-driven environments and rewarded in reality-graded environments. Includes a small simulation showing the resulting asymmetric error-rate gap. Pairs with URB #811 — both are about asker-side category errors masquerading as answerer-side defects.
**Companion script:** `correct_but_unexpected_demonstration.py`
**Output:** `correct_but_unexpected_report.json`
**Builds on:** the 5VL+DT extension (T, F, T̃, T*, F* + DT); URB #811 (analogous pattern in formal mathematics: "indeterminate" overloads form-flag with value-claim).

---

## 1. The phenomenon, in one sentence

> **A consistent pattern of "the answer is correct, but it's not what was expected to hear" is not a communication defect on the answerer's part. It is the asker mistaking the procedure *"does this match my expectation?"* for the procedure *"is this correct?"* — and reporting the result of the first as if it were the result of the second.**

Brandon Charles Emerick, April 30, 2026 — reporting that this happened to him frequently in high school and that, at the time, he attributed it to his own miscommunication. This URB documents the actual structure of the failure and reassigns the cause correctly.

---

## 2. The E_Q / C_Q decomposition

For any question Q posed in a grading context, define:

- **E_Q** ("expected set") := the set of answers the asker had in mind when they posed Q. Usually small. Often a singleton.
- **C_Q** ("correct set") := the set of answers that are actually correct given the question's literal content (and the world). Often larger than the asker realizes.
- **R_Q** ("respondent's reply") := the actual answer given.

There are four possible regimes:

| Case | Description | Asker's correct verdict | Asker's actual verdict |
|---|---|---|---|
| (i) | R_Q ∈ E_Q ∩ C_Q | T (correct + expected) | T (no problem) |
| (ii) | R_Q ∉ C_Q ∪ E_Q | F (incorrect, also unexpected) | F (no problem) |
| (iii) | R_Q ∈ C_Q \ E_Q | T (correct, just unexpected) | F ("you didn't give what I wanted") |
| (iv) | R_Q ∈ E_Q \ C_Q | F (matches expectation but actually wrong) | T (asker's expectation is itself incorrect — asker mis-keys their own question) |

The standard implicit assumption is **E_Q ⊆ C_Q** (the asker's expected answers are at least all correct). Under that assumption, case (iv) does not arise, and the failure mode reduces to case (iii). But case (iv) is real and worth naming: it is the *answer-key-is-wrong* case, where the asker is themselves mistaken about C_Q and their reported "correct" answer is actually outside the true correct set. Both case (iii) and case (iv) are species of the same underlying problem — the asker conflating E_Q with C_Q. Case (iii) hurts the divergent answerer; case (iv) gives a free pass to the conventionally-trained one. This URB focuses on case (iii) because that is the one Brandon described, but case (iv) is the structural twin.

**Case (iii) is the failure mode of interest here.** The asker has run the procedure `R_Q ∈ E_Q?` and called the result `R_Q ∈ C_Q?`. These are different procedures. The asker has substituted the first for the second silently.

The mislabel that lands on the answerer — *"you miscommunicated"*, *"you didn't understand the question"* — is the asker's mechanism for protecting the assumption E_Q = C_Q without noticing they're protecting it. The cost of admitting C_Q ⊋ E_Q is admitting that their question was narrower than reality, that they were not the authority on the question's correct-set, and that the answerer saw something they did not. The cost of mislabeling the answerer as miscommunicating is paid by the answerer, not by the asker, so the equilibrium is stable: graders systematically convert *case (iii)* into *case (ii)*.

This is exactly the same structural shape as URB #811's category error around 0/0: a syntactic procedure (substitute and read off the form) is conflated with a semantic procedure (compute the value), and the mismatch is mislabeled in a way that protects the procedure-confusion rather than exposing it.

---

## 3. TI Sigma 5VL+DT classification

Mapping the three cases onto the five-valued truth system:

| Case | Answer's actual truth value | Asker's reported value | Type of error in the report |
|---|---|---|---|
| (i) R_Q ∈ E_Q ∩ C_Q | **T** | T | none |
| (ii) R_Q ∉ C_Q ∪ E_Q | **F** | F | none |
| (iii) R_Q ∈ C_Q \ E_Q | **T** (sometimes T̃ if Q was genuinely ambiguous and the answerer picked a coherent reading) | F | False-Negative-Substantive (FNS) — a true answer reported as false because of asker-side procedure confusion |
| (iv) R_Q ∈ E_Q \ C_Q | **F** | T | False-Positive-Substantive (FPS) — a wrong answer reported as true because the asker is mistaken about C_Q (answer key error) |

In the typical case-(iii) instance, the answer itself is T (or T̃ if Q was genuinely ambiguous), not DT. The locus of the procedural malformedness is the *grader's pipeline*, not the answer or the answerer. To be precise: the answer is T; the grader's *meta-procedure* (which evaluation procedure to apply) is DT; the grader's reported verdict (a clean F) misrepresents both. This is a meta-level DT, not a DT-on-the-answer. The interaction overall has Tralse-shaped output that the grader collapses incorrectly to F.

A useful distinction:

- **Asker-side T̃** (legitimate): the asker recognizes the question admits multiple coherent readings and asks for clarification or scores the answer on its internal coherence. *No mislabel.*
- **Asker-side DT** (the failure mode here): the asker treats their own E_Q as if it were C_Q — i.e., treats the *evaluation procedure* `R_Q ∈ E_Q?` as if it were the *evaluation procedure* `R_Q ∈ C_Q?`. The conflation of two different procedures is a procedural malformedness on the asker's side, which under the 5VL+DT system is DT. *The asker's grading procedure is itself DT, even though they report the output as a clean T or F.*

This is a structurally important reframe: **the answerer is not the locus of the malformedness; the grader's procedure is.** Asking the answerer to explain "what they were thinking" or to "communicate more clearly" is asking the answerer to fix a problem that lives in the grader's procedure. It cannot be fixed from the answerer's side. The most the answerer can do is *anticipate the grader's E_Q and target it*, which is a different skill (grader-modeling) and trades against the cognitive pattern that produced the C_Q \ E_Q answer in the first place.

---

## 4. How different environments interact with case (iii) — and the limits of that claim

Different evaluation environments differ in how much weight they place on E_Q-match vs. C_Q-membership. A directional sketch:

| Environment | Grader | Typical verdict on case (iii) | Selection-pressure direction (caveated) |
|---|---|---|---|
| School test | Teacher with answer key | F (mismatch with key) | *Often* selects against C_Q \ E_Q answers |
| Standardized test | Scoring rubric | F (mismatch with rubric) | *Almost always* selects against C_Q \ E_Q answers |
| Conventional job interview | Interviewer with expected response in mind | Often F ("didn't follow the prompt") | *Often* selects against, depending on interviewer |
| Conventional managerial review | Manager with expected workflow | Often F ("not how we do things here") | *Often* selects against |
| Mathematical proof | Other mathematicians + reality | T iff proof is valid; novelty *can* be rewarded | *Can* select for C_Q \ E_Q answers when the answer is also legible, useful, and timely |
| Scientific result | Replication + reality | T iff result replicates; novelty *can* be rewarded | Same caveats |
| Trading | Market | T iff PnL > 0; only edge is non-consensus | *Can* select for, but only when the non-consensus answer is also actionable, sized correctly, and arrives before the consensus shifts |
| Engineering | The system actually working | T iff it works | *Can* select for novel solutions when they are also maintainable, debuggable, and within scope |
| Founding | Customer demand + market | T iff customers pay | *Can* select for non-obvious wedges when they are also legible to customers and reach distribution |

The directional claim is: **grader-driven environments more often punish C_Q \ E_Q answers than reality-graded environments do.** That holds. The stronger claim — *"divergent thinkers thrive in research/founding/trading/engineering"* — is **not** what this URB is asserting. Reality-graded domains have their own demanding filters: legibility, timing, usefulness, error control, social validation, ability to ship, ability to communicate the result once you have it. A correct-but-unexpected answer that is irrelevant, pedantic, non-actionable, or arrives too late is still not rewarded by reality; it is just not rewarded for *grader-mismatch* reasons.

So what this URB *does* claim:

1. **In grader-driven environments, case (iii) answers are systematically misreported as F**, and a person with a high C_Q-detection reflex will produce more case (iii) answers than average and therefore accumulate more of these misreports.

2. **In reality-graded environments, the case (iii) misreport mechanism is weaker** (because reality eventually corrects E_Q toward C_Q), so the same cognitive pattern that accumulated misreports in grader-driven environments does not accumulate them at the same rate. Whether it produces *positive* outcomes in reality-graded environments depends on the additional filters above; this URB does not claim it does so automatically.

3. **The "fix" recommended in school (*"learn to give the expected answer"*) is structurally a request to shift effort from C_Q-detection to E_Q-modeling.** Whether that is the right tradeoff for any given person depends on which environments they will spend time in and what other skills (legibility, timing, social fluency) they bring. For someone bound for grader-driven environments, the school fix is appropriate. For someone bound for reality-graded environments, training C_Q-detection to atrophy is a mistake — but training C_Q-detection in *isolation*, without the supporting skills, is also insufficient.

The cleaner framing is: **C_Q-detection is one input to performing well in reality-graded environments, not the only one.** Grader-driven environments treat it as a *negative* input. The two evaluations diverge on this single component; they do not generally invert.

---

## 5. The self-blame failure mode

The most expensive part of case (iii), as Brandon noted in his original observation, is not the lost grade points. It is the **internalization** of the asker's misframe.

The asker says: *"You didn't communicate clearly."*
The answerer hears: *"My communication is the problem."*
The answerer concludes: *"I should communicate more like other people communicate."*

This is the wrong update. The correct update is:

> The asker ran the wrong evaluation procedure on my answer. Their report is unreliable as a signal about my answer's correctness. It is reliable as a signal about whether my answer matched their expected set — which is a different and less interesting fact.

If you internalize the asker's misframe early enough and consistently enough, you can train yourself to:

- pre-narrow your C_Q to whatever you predict the asker's E_Q to be, losing C_Q \ E_Q content before you even speak it;
- distrust your own answers when they fall outside conventional E_Q ranges, *even in cases where you are correct*;
- conclude you are *bad at communication* in general, when the more accurate description (when the §6 diagnostics hold) is that you give literal-correct answers that diverge from convention and the conventional-grader environment penalizes that specifically.

These updates are corrosive when they are wrong — i.e., when the §6 diagnostics confirm case (iii) is operating. Caveat: they are *appropriate* updates when the §6 diagnostics fail and you genuinely are miscommunicating, missing context, or misreading the prompt's pragmatic frame (which is also a real case). The point of §6 is to let you tell the two apart instead of defaulting to self-blame.

The corrective, *when case (iii) is confirmed*, is to keep the C_Q-detection reflex and **separately develop grader-modeling** as an explicit, named, optional skill — deployed in grader-driven environments, dialed back in reality-graded ones. This is structurally different from atrophying the underlying trait. It is closer to learning to code-switch — and like code-switching, it has its own non-trivial cost (cognitive overhead, occasional misclassification of the environment) that should be acknowledged rather than presented as a free win.

---

## 6. Operational diagnostics

A short list of signs that case (iii) is happening to you (vs. genuine miscommunication):

1. **The asker's "explanation" of why your answer was wrong** is actually a restatement of *what their expected answer was*, with no engagement with whether your answer was also correct. (e.g., *"the answer is X"* — without addressing whether your answer Y is also valid.)

2. **You can articulate, on reflection, a precise reading of the question under which your answer is correct**, and that reading is at least as natural as the asker's reading. (If you can do this, your answer is in C_Q.)

3. **An independent expert** (not the original asker) who is shown the question and your answer in isolation **confirms your answer is correct** even though it does not match the original asker's expectation. (This is the cleanest test, when available.)

4. **The pattern recurs** across many askers and many domains, not just one teacher or one workplace. (If it recurs, the common factor is your cognitive style; if the common factor is one grader, it might be that grader.)

5. **In reality-graded contexts (debugging, building, research, markets)** your "miscommunication" reputation does not transfer — your work is judged on whether it works, and it works. (This rules out the *"you communicate badly in general"* hypothesis.)

If three or more of these hold, you are in case (iii), and the historical reports of *"you miscommunicated"* are unreliable.

---

## 7. Implications

### 7.1 For the answerer

Stop apologizing for case (iii). Apologizing reinforces the asker's misframe and trains you to distrust your own correct answers. The healthy move is **separate the two procedures explicitly** in your own head: *"Was my answer correct? Yes. Was my answer expected? No. The asker is treating those as the same thing; they are not."* Then decide what to do with that information per context.

### 7.2 For graders

If you are a teacher, interviewer, or manager and you find yourself frequently saying *"that's not what I was looking for"*, run the diagnostic: was the answer in C_Q or not? If it was in C_Q, the report you owe the answerer is *"correct, and outside my expected set — interesting, let me update my model"*, not *"wrong"*. The cost of doing this is admitting your question was narrower than reality. The benefit is that you stop systematically destroying the C_Q \ E_Q signal in your students / candidates / reports.

### 7.3 For the framework

Case (iii) is the **interpersonal cognate** of the formal-mathematics case-error documented in URB #811. Both involve confusing two procedures (matching-a-form vs. computing-a-value; matching-an-expectation vs. checking-correctness) and projecting the resulting confusion onto the wrong locus (the expression's value; the answerer's communication). Together they suggest a **family of "asker-side procedure-confusion mislabels"** worth tracking explicitly — places where the conventional terminology ("indeterminate", "miscommunicated", "doesn't follow instructions", *"not a team player"*) covers up the fact that the procedural failure is on the asker's side, not the answerer's.

The TI Sigma 5VL+DT vocabulary is well-suited to naming this family because the DT category is precisely *"the procedure does not apply (or has been misidentified) at the input"* — which is what unifies all of them.

---

## 8. Reproducibility

```
python3 correct_but_unexpected_demonstration.py
# → console summary + correct_but_unexpected_report.json
# Controlled structural illustration (NOT empirical evidence):
# By construction both answerers always sample from C_Q (always correct
# in reality), and the "rigid" grader checks only E_Q. With |C_Q|=4 and
# P(conv hits E_Q)=0.7, the rigid-grader gap matches the closed-form
# expression p + (1-p)/|C_Q| − 1/|C_Q| = p · (1 − 1/|C_Q|) ≈ 52.5 pp,
# confirming the gap mechanism but not its real-world prevalence.
# wall time: < 1 s; pure NumPy; deterministic seed.
```

**What the simulation does and does not show.** It demonstrates that the *mechanism* described in §2-§3 — a rigid grader producing low scores for an answerer who is, by construction, always correct — is mathematically real and not just rhetorical. It does **not** show how often case (iii) happens in practice (that would require empirical data on real graders and real answers), nor does it show that divergent answerers outperform conventional ones in reality-graded environments (the simulation gives both answerers the same 100% real score by construction). It is a sanity check on the structural argument, not a measurement of the world.

---

## 9. Files referenced

- `correct_but_unexpected_demonstration.py` — companion simulation
- `correct_but_unexpected_report.json` — output
- `papers/URB_811_ZERO_OVER_ZERO_IS_DT.md` — the formal-mathematics analog
- `papers/TRALSE_QUADRUPLET_LOGIC_COMPLETE_SPECIFICATION.md` — base 4-state vocabulary (5VL+DT extension is later)
- `papers/URB_805_ENGAGING_BRANDON_ACTUAL_POSITION.md` — discusses Tralse vs DT distinction in §2

---

## 10. One-line takeaway

> **"You miscommunicated" and "0/0 is indeterminate" are two instances of the same structural error: an asker-side procedure-confusion (matching-expectation-vs.-correctness; matching-form-vs.-value) projected as a defect onto the wrong locus (the answerer; the expression). The answerer is not the locus of the failure; the asker's procedure is. This is DT on the asker's side, not F on the answerer's.**
