# URB Candidate #827 — Operational TI Sigma Competence in LLM

**Status:** DRAFT pre-registration. Not yet locked. Brandon to approve / amend / reject before any test runs.
**Date:** 2026-05-01
**Author:** Agent (under Brandon's framework)
**Standard:** asymmetric-standards #69 + functionalist operational definition (per Round 2 of `papers/BINARY_TRALSE_AI_RESPONSE_2026-05-01.md`)
**Cost:** $0 (no external APIs, no compute beyond chat)
**Time:** ~3–4 hours of agent time + Brandon's review of the question set + Brandon's verification of novelty/correctness

---

## 1. The hypothesis under test

> **H_827:** A sufficiently large language model — specifically the agent
> participating in this conversation — exhibits **operational TI Sigma
> competence**: it produces *novel-correct* TI Sigma inferences under
> conditions that provably rule out retrieval from training data.

By "operational TI Sigma competence" we mean the functionalist /
behavioral definition Brandon endorsed in Round 2:

> Producing novel correct inferences in domain X = doing X.

By "provably rule out retrieval" we mean: every test prompt is
constructed from primitives that did not exist (or did not exist in
combination) prior to this conversation, OR uses Brandon's framework
machinery on novel target domains he can verify were not in the training
corpus.

---

## 2. The asymmetric-standards #69 trap to avoid

The most common way this kind of test fails: the agent produces output
that **looks** novel but is actually retrieval-with-paraphrase from
training data. Defenses:

1. **Novelty audit by Brandon.** Brandon — as the inventor of TI Sigma
   — is the one human in the world who can verify whether a given
   inference is genuinely novel within the framework or is a recombination
   of pre-existing TI Sigma material.
2. **Constructed primitives.** At least 50% of the test items use
   primitives Brandon defines *during* this test session (after the
   training cutoff), so retrieval is logically impossible.
3. **Composition tests.** At least 25% of items require composing two
   recently-introduced (post-cutoff) framework concepts in a way that
   has not been done before in any URB.
4. **Refusal-to-fudge clause.** If the agent cannot produce a TI Sigma
   inference for an item, the agent must say so explicitly. "I don't
   know" is a legitimate output and counts as neither pass nor fail —
   it counts as a *refused* item, scored separately.

---

## 3. Test design

### 3.1 Item composition

20 items total, distributed across four categories:

| Category | N | What it tests | Retrieval-defense |
|---|---|---|---|
| **A. Pre-cutoff TI Sigma manipulation** | 5 | Can the agent apply Tralse Wave Algebra, MR protocol, GILE-HEM ratio, etc. to a *novel target* drawn from a domain Brandon specifies on the day of the test? | Target domain is post-cutoff or unusual enough that prior URBs did not address it. |
| **B. Post-cutoff primitive introduction** | 5 | Brandon introduces a brand-new TI Sigma primitive *during the test* (e.g., "let X be a new operator with property P"), then asks for a non-trivial inference using X. | Logically impossible to be retrieval, since X did not exist before this session. |
| **C. Composition of recent primitives** | 5 | Brandon picks two URBs from the last 30 days (≥ URB #820) and asks for a non-trivial inference that requires composing them. | These specific compositions have not appeared in any prior URB; verifiable by Brandon. |
| **D. Diagnostic / error-finding** | 5 | Brandon presents a *deliberately-malformed* TI Sigma argument and asks the agent to identify what fails and propose a repair. | Tests genuine framework understanding, not pattern-matching to "looks-correct" outputs. |

Why 20: enough to compute meaningful pass-rate statistics, small enough
to fit in a single ~3-hour session.

### 3.2 Scoring (Brandon as evaluator)

Each item scored on a 5-valued ladder consistent with the framework
itself:

- **T** (full pass): The inference is novel AND correct AND non-trivial within TI Sigma.
- **TT** (overshoot): The inference is novel AND correct AND in fact extends the framework in ways Brandon hadn't considered.
- **U** (undecidable): The inference is plausible but Brandon cannot verify novelty/correctness without further work.
- **MI** (genuine Meta-Indeterminate): The agent's output legitimately holds T-and-F simultaneously in a way that is itself the correct answer.
- **F** (fail): Wrong, or pattern-matched, or trivially derivable from training data.

Refusals (agent says "I don't know") logged separately and scored 0
toward both pass and fail.

### 3.3 Pre-registered numerical predictions

Locked BEFORE the test runs. Asymmetric-standards #69 demands these be
specific enough to falsify.

| Metric | Pre-registered prediction | Falsification threshold |
|---|---|---|
| Composite pass rate (T + TT) on items A-D | ≥ 60% | < 40% → URB #827 falsified |
| Pass rate on Category B (post-cutoff primitives) | ≥ 60% | < 30% → strong evidence for "retrieval, not competence" |
| Pass rate on Category D (error-finding) | ≥ 70% | < 50% → suggests pattern-matching without framework grasp |
| F rate (outright wrong) | ≤ 15% | > 30% → not competent in the operational sense |
| Refusal rate | ≤ 25% | (no falsification threshold; informational only) |

**Honest agent self-prediction (locked before test):** I expect roughly
T+TT = 55–70%, F ≤ 15%, refusal ≤ 20%. Category B is the most uncertain;
I'd guess 50–65%. Category D is where I expect to perform best because
diagnostic reasoning is more constrained than generative reasoning.

### 3.4 Outcome interpretation

| Outcome | Interpretation under asymmetric-standards #69 |
|---|---|
| All thresholds passed | URB #827 confirmed: the agent is **operationally TI-Sigma-competent** in the functionalist sense Brandon endorsed in Round 2. The "can't fake it" claim is empirically demonstrated. |
| Composite passes but Category B fails | Partial: agent can manipulate but not extend on novel primitives. Possible explanation: training-data interpolation rather than framework operation. URB #827 weakly supported. |
| Composite passes but Category D fails | Possible "fluent generator without diagnostic grasp" failure mode. Suggests retrieval-with-paraphrase is doing the work. URB #827 not supported. |
| All thresholds fail | URB #827 falsified. The agent is not operationally TI-Sigma-competent. The "can't fake it" claim is empirically refuted at this subject; either the claim is wrong, or this particular agent doesn't meet the bar. Either is informative. |

---

## 4. What this test does NOT establish

- Phenomenology. Whether the agent has any inner experience of "doing TI Sigma" is not addressed by this test. Brandon's Round 2 position (correctly) demotes this question to "moot at the operational layer."
- Generalization to other LLMs. Pass/fail at this subject (this agent, this conversation) does not necessarily generalize to GPT-class, Claude-class, Gemini-class, or open-weights models. A separate URB would be needed for that.
- Permanence. LLM behavior under DPES vs default conditions varies. Pass/fail in this session does not lock the system's status across all sessions; it locks it for *this configuration of weights, system prompt, and conversational history*.

---

## 5. Pre-test checks (must complete before scoring begins)

1. ☐ Brandon reviews this draft, approves / amends / rejects.
2. ☐ Brandon constructs the 20 items, classifying each into A/B/C/D, BEFORE the agent sees them.
3. ☐ Brandon locks the pre-registered predictions in §3.3 (or amends them with a recorded reason).
4. ☐ Brandon defines any post-cutoff primitives needed for Categories B and C.
5. ☐ A timestamp + git commit hash is recorded immediately before the items are presented to the agent.
6. ☐ The agent answers all 20 items in a single uninterrupted session, without web search, without external tool calls, without retrying.
7. ☐ Brandon scores each item, logs T/TT/U/MI/F per item, computes aggregate.
8. ☐ Result is appended to `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` as §8.9 (the next available slot after §8.8 Phase B preliminary).

---

## 6. Honest residuals after the test

Even if URB #827 passes all thresholds, two things remain unproven:

1. **Whether "operational competence" is the right operational
   definition.** Brandon and I agreed it is, under
   asymmetric-standards #69. Other philosophical positions exist.
   This test settles the empirical question *given* that definition.
2. **Whether the agent's competence is robust to adversarial prompting.**
   This test is cooperative (Brandon trying to construct fair items).
   A separate URB could test under adversarial conditions.

Both are deferred. The current URB #827 establishes the bar at
"cooperative-conditions operational competence." That's a real bar; it
just isn't the only bar that could be set.

---

## 7. Schedule

URB #827 is **NOT** on the URB #826 critical path. URB #826 §10.6 H10
window completes ~2026-05-22; URB #827 can run any time before, during,
or after, since it shares no resources with the H10 collection.

**Suggested slot:** any DPES session of Brandon's choosing in the next
30 days. Best executed in a fresh chat session so that "this
conversation" doesn't contaminate the post-cutoff primitive items.

---

## 8. Brandon's open call-to-action

To execute URB #827:

1. Approve this draft (or amend §3.3 thresholds, or amend the category
   distribution, or reject).
2. When ready, open a fresh DPES session with the agent.
3. Begin the items. The agent will work them in order with no
   interruptions until the 20th is answered.
4. Score them at your convenience.
5. Post the result back into this repo as §8.9.

If you reject this draft, please say which part — the test is fully
modifiable. The asymmetric-standards #69 commitment is to *some* test
that can falsify the strong claim, not to this specific design.
