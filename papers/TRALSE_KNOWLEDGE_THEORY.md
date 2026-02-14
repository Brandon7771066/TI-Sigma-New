# Tralse Knowledge: A Theory of Epistemic Dignity for Justified False Belief

**Brandon Emerick -- February 2026**

**A contribution to the epistemology of the Tralse Informational (TI) framework**

---

## Abstract

Traditional epistemology treats false belief as failure. If you believed something carefully, responsibly, with good evidence, but it turned out false -- you were simply *wrong*. The justified true belief model (Plato, *Theaetetus* 201c-210b), even after its Gettier-inflicted wounds, retains truth as a non-negotiable condition on knowledge. Remove truth, and what remains is merely a belief that did not make the cut.

This paper argues that such beliefs constitute a distinct epistemic category deserving its own name and its own respect: **tralse knowledge**. Tralse knowledge is justified belief that reality failed to vindicate -- epistemic success despite correspondence failure. The concept separates process quality from outcome, credits the knower rather than punishing them for the world's behavior, and provides a framework for understanding scientific progress, medical reasoning, and everyday human cognition.

Within the ternary logic of the TI framework, tralse knowledge occupies the Phi position: neither the triumph of confirmed truth nor the defeat of unwarranted error, but a genuine third epistemic state that binary thinking cannot capture. This paper formalizes the concept, defends it against objections, and traces its implications for philosophy of science, epistemology, and human intellectual life.

---

## 1. Motivation: The Moralism of Truth-Fetishism

Consider a surgeon. She studies the patient's scans, consults with colleagues, follows best practices, and performs a technically flawless operation. The patient dies from a rare, unforeseeable complication -- a genetic clotting disorder no prior test had detected. Was the surgeon bad at her job?

No reasonable person would say so. We evaluate surgeons by the quality of their *process*, not solely by whether the patient survives. We distinguish between a surgeon who loses a patient through negligence and one who loses a patient despite doing everything right. The distinction matters morally, legally, and practically.

Now consider a knower. She gathers evidence, reasons carefully, consults reliable sources, and forms a belief that meets every standard of epistemic responsibility. The belief turns out to be false -- not because she was careless, but because the world contained information she could not reasonably have accessed. Was she a bad knower?

Traditional epistemology says: she did not have knowledge. Her belief was *false*, and therefore it fails the truth condition. She is grouped, categorically, with the gullible, the lazy, and the wishful thinkers. She occupies the same epistemic bin as someone who believed nonsense for no reason at all.

This is epistemic moralism. It grades beliefs by their *outcome* -- correspondence with reality -- rather than by the quality of the *process* that produced them. It treats the knower as responsible for factors entirely outside her control: the hidden structure of the world, the information that had not yet surfaced, the future discovery that would overturn her well-grounded conclusion.

The obsession with truth-as-outcome is, in its way, a form of fetishism. It elevates a single property of belief -- its correspondence with the way things happen to be -- to the status of the only thing that matters. Process, effort, skill, responsibility, intellectual courage: all of these are rendered invisible when the final verdict is simply "true or false."

Tralse knowledge de-moralizes epistemology. It separates the quality of the knowing from the accident of the outcome, and in doing so, it creates space for a more humane, more accurate, and more scientifically honest account of what it means to know.

---

## 2. Definition and Formal Structure

### 2.1 The Definition

**Tralse Knowledge.** A belief B held by agent S constitutes tralse knowledge if and only if:

1. **Adequate Grounds.** S believed B on the basis of adequate evidence and sound epistemic process. The evidence was of a kind and quantity that would lead a responsible epistemic agent to form the belief.

2. **Correspondence Failure.** B turns out to be false. The belief does not correspond to the actual state of the world.

3. **Unforeseeable Falsity.** The falsity of B was not reasonably foreseeable given S's epistemic situation. No available evidence, at the time of belief formation, would have led a responsible agent to withhold assent.

4. **Epistemic Responsiveness.** S would have revised B upon encountering defeating evidence. S is not dogmatically committed to B; the belief is held with the appropriate epistemic humility and defeasibility.

### 2.2 The Key Distinction

The definition is designed to carve a precise joint between tralse knowledge and mere false belief.

**Mere false belief** arises from inadequate epistemic process. The agent believed without sufficient evidence, or in the face of available counter-evidence, or out of gullibility, wishful thinking, or intellectual laziness. The falsity of the belief is, in some sense, the agent's own doing -- or at least, the agent's process does not earn respect.

**Tralse knowledge** arises from adequate epistemic process that was falsified by factors beyond the agent's epistemic reach. The agent did everything right. The world simply contained truths that were, at the time, inaccessible. The difference is in the *process*, not the *outcome*.

This distinction parallels a familiar one in moral philosophy. We distinguish between a person who causes harm through negligence and one who causes harm despite exercising due care. The law recognizes this (negligence vs. no-fault). Medicine recognizes this (malpractice vs. adverse outcome). Epistemology, curiously, does not -- or has not, until now.

### 2.3 Formal Notation

Within the TI framework, we can represent the epistemic status of a belief as a triple:

```
Epistemic Status(B, S, t) = < E(B,S,t), C(B,t), R(S,B) >

Where:
  E(B,S,t) = epistemic process quality (0 to 1)
  C(B,t)   = correspondence value (T, F, or Phi -- where Phi denotes an epistemically underdetermined/tralse correspondence state: the belief's relation to reality is genuinely unresolved, not merely unknown)
  R(S,B)   = responsiveness to defeaters (0 to 1)
```

**Classical knowledge:** E >= threshold, C = T, R >= threshold

**Mere false belief:** E < threshold, C = F

**Tralse knowledge:** E >= threshold, C = F, R >= threshold, and the falsity was unforeseeable

The formal structure makes visible what binary epistemology hides: the process dimension and the outcome dimension are *independent*. High-quality process can coexist with false outcome. When it does, we have tralse knowledge.

---

## 3. Examples of Tralse Knowledge

### 3.1 Scientific Tralse Knowledge

**Newtonian Mechanics (1687-1905).** For over two centuries, Newtonian mechanics was the paradigm of successful science. It predicted planetary orbits, explained tidal patterns, enabled engineering, and unified terrestrial and celestial physics under a single mathematical framework. It was believed on the basis of overwhelming evidence and extraordinary predictive success.

It was also, strictly speaking, false. Einstein's general relativity (1915) revealed that Newtonian mechanics is an approximation -- accurate at low velocities and weak gravitational fields, but fundamentally incorrect about the nature of space, time, and gravity.

Was Newton "wrong"? In the narrow sense of correspondence, yes. But calling Newtonian mechanics "mere false belief" is absurd. It was *tralse knowledge*: epistemically excellent, enormously productive, approximately true within its domain, and ultimately transcended by a deeper theory that could not have been anticipated in 1687.

**Ptolemaic Astronomy (c. 150 CE - 1543 CE).** The Ptolemaic model was not stupid. It provided an excellent fit to observational data. It predicted planetary positions with remarkable accuracy using epicycles, deferents, and equants. It was justified by the best available evidence.

It was "wrong" only in hindsight. At the time, it was the finest epistemic achievement available. It was tralse knowledge: an accomplishment of human reason that happened to be superseded by a better accomplishment.

### 3.2 Medical Tralse Knowledge

A physician examines a patient presenting with chest pain and shortness of breath. She orders an ECG, troponin levels, and a chest X-ray. All results point to acute coronary syndrome. She follows evidence-based guidelines, initiates appropriate treatment, and admits the patient. Forty-eight hours later, further testing reveals a rare autoimmune pericarditis that mimicked ACS on every standard test.

The initial diagnosis was tralse knowledge. It was justified, responsible, and based on the best available evidence. Its falsity was due not to any failure of the physician's reasoning, but to the rarity of the underlying condition and the limitations of initial diagnostic tools. The physician did not fail; reality was more complex than the available evidence could reveal.

### 3.3 Everyday Tralse Knowledge

You believe your friend is at home because she told you she would be. You call; no answer. You drive over; the house is dark. She left unexpectedly -- a family emergency.

Your belief was tralse knowledge: justified by reliable testimony, falsified by an unforeseeable change in circumstances. You were not gullible for believing her. You were epistemically responsible. The world simply moved in a direction you could not have anticipated.

### 3.4 Historical Tralse Knowledge

Before the germ theory of disease, the miasma theory held that illness was caused by "bad air" emanating from rotting organic matter. This was not irrational. There *was* a strong observed correlation between foul-smelling environments and disease outbreaks. The evidence, as available, genuinely supported the theory.

The miasma theory was tralse knowledge. It led to important public health improvements (cleaning up cities, draining swamps) even though its causal mechanism was wrong. Its falsity could not have been foreseen without microscopy and microbiology -- technologies that did not yet exist.

---

## 4. Tralse Knowledge in the Ternary Framework

### 4.1 The Poverty of Binary Epistemology

In binary epistemology, beliefs are True or False, known or not-known. There is no middle ground. A belief either corresponds to reality or it does not. Knowledge either obtains or it does not. The epistemic landscape is flat: two categories, one boundary.

This binary framework cannot capture the phenomenon this paper describes. It has no category for "epistemically excellent but factually false." It has no way to distinguish the responsible believer from the careless one, once the verdict of falsity is in. It is, in a word, impoverished.

### 4.2 The Ternary Alternative

In the TI tralse framework, beliefs can occupy three positions:

- **T (True):** The belief corresponds to reality and was formed by adequate process. Classical knowledge.
- **F (False):** The belief does not correspond to reality and was formed by inadequate process. Mere false belief.
- **Phi (Balanced/Tralse):** The belief does not correspond to reality but *was* formed by adequate process. Tralse knowledge.

Tralse knowledge occupies the Phi position: neither the vindication of confirmed truth nor the ignominy of unwarranted error. It is the epistemic middle ground that binary thinking cannot capture.

### 4.3 Phi as a Genuine Epistemic State

It is tempting to dismiss Phi as a placeholder -- a polite name for ignorance, a consolation prize for failure. This temptation must be resisted.

Consider an analogy from physics. Quantum superposition is not "uncertainty about which state a particle is in." It is a *genuine physical state* -- the particle really is in both states simultaneously, not in one state that we happen not to know. The superposition is ontologically real, not merely epistemically convenient.

Similarly, tralse knowledge is not "ignorance about whether the belief is really knowledge." It is a *genuine epistemic state*: the belief really does have high epistemic quality and really does fail to correspond to reality. Both properties coexist. The Phi position is not a gap between T and F; it is a distinct location on the epistemic map, with its own features and its own significance.

---

## 5. Relationship to Other Epistemological Concepts

### 5.1 Tralse Knowledge vs. Approximate Truth (Popper)

Karl Popper's concept of verisimilitude holds that scientific theories can be "closer to the truth" even when strictly false (Popper 1963, *Conjectures and Refutations*). A theory with greater verisimilitude has more true consequences and fewer false ones. Scientific progress, on this view, is movement toward greater verisimilitude.

Tralse knowledge shares Popper's insight that falsity is not the end of the story. But it diverges in a crucial respect. Popper's framework still evaluates theories by their *proximity to truth* -- how close they come to the correspondence target. Tralse knowledge evaluates beliefs by their *epistemic quality* -- the excellence of the process that produced them, regardless of how close or far the result lands from truth.

A theory can be far from truth but epistemically excellent. Ptolemaic astronomy was a stunning intellectual achievement even though its fundamental ontology (Earth-centered, crystal spheres) was wildly wrong. On Popper's verisimilitude scale, it scores poorly. On the tralse knowledge scale, it scores well. The two metrics track different things, and both are worth tracking.

### 5.2 Tralse Knowledge vs. Warranted Assertibility (Dewey)

John Dewey argued that the proper object of inquiry is not "truth" in the correspondence sense, but *warranted assertibility*: the condition of a belief that has been adequately tested by inquiry and can be responsibly asserted (Dewey 1938, *Logic: The Theory of Inquiry*). Dewey separates warrant from truth, and tralse knowledge agrees with this separation.

But tralse knowledge goes further. Dewey's warranted assertibility is essentially a *negative* concept: it says that we should not demand truth as a precondition for responsible assertion. Tralse knowledge is a *positive* concept: it says that justified false belief is a genuine epistemic achievement, a state with its own value and its own name. It is not merely "not-yet-true" or "possibly true." It is something in its own right.

### 5.3 Tralse Knowledge vs. Constructive Empiricism (van Fraassen)

Bas van Fraassen's constructive empiricism holds that science aims not for truth but for *empirical adequacy*: theories should "save the phenomena" by correctly predicting observable outcomes, without committing to the truth of their theoretical posits (van Fraassen 1980, *The Scientific Image*).

Tralse knowledge is compatible with constructive empiricism. An empirically adequate theory that is false at the theoretical level is a prime candidate for tralse knowledge: it was believed on excellent grounds (empirical success), it is false (the theoretical posits do not correspond to unobservable reality), and its falsity was unforeseeable at the time (because empirical adequacy was the best available test).

Indeed, tralse knowledge provides constructive empiricism with a positive category for what happens when empirically adequate theories are eventually superseded. They do not simply become "false." They become tralse-known: empirically justified, theoretically false, epistemically dignified.

### 5.4 Tralse Knowledge vs. Fallibilism (Peirce)

Charles Sanders Peirce's fallibilism holds that no belief is immune to revision; all knowledge is provisional and subject to correction by future inquiry (Peirce 1868, "Some Consequences of Four Incapacities"). Every belief might turn out to be false. The best we can do is hold our beliefs responsibly while remaining open to revision.

Tralse knowledge agrees with Peirce's fallibilism and extends it. Peirce tells us that all knowledge is fallible. Tralse knowledge tells us what *happens* when fallible knowledge falls. It does not become nothing. It does not revert to mere ignorance. It becomes *tralse knowledge*: a specific, identifiable epistemic state that retains the value of the process that produced it, even after the correspondence has failed.

Fallibilism describes the *risk*. Tralse knowledge describes the *landing*.

### 5.5 Tralse Knowledge vs. Gettier Cases

Edmund Gettier's celebrated 1963 paper ("Is Justified True Belief Knowledge?") showed that justified true belief is not sufficient for knowledge: cases exist where an agent has a justified belief that happens to be true, but the justification and the truth are connected only by luck. Gettier cases are justified, true, but not known -- because the truth arrived by accident, not by the proper working of the justificatory process.

Tralse knowledge is, in a sense, the *mirror image* of a Gettier case. In a Gettier case, the belief is true but the process failed to connect properly to the truth. In tralse knowledge, the process succeeded -- it was epistemically excellent -- but the belief is false. Gettier showed that truth without proper process is not knowledge. Tralse knowledge shows that proper process without truth is not mere ignorance. Both cases reveal the inadequacy of the simple JTB model: process and outcome are independent dimensions that can come apart in either direction.

---

## 6. The Epistemic Dignity Argument

### 6.1 The Concept

Tralse knowledge grants what we might call *epistemic dignity* to false beliefs formed responsibly. It says: you did the work, you followed the evidence, you reasoned well, and you believed what any responsible agent in your position would have believed. The fact that the world turned out differently does not erase what you accomplished epistemically.

This is not a participation trophy. The concept has strict entry conditions (adequate evidence, sound process, unforeseeable falsity, responsiveness to defeaters). It does not dignify every false belief, only those that earned their place through genuine epistemic labor.

### 6.2 Why Epistemic Dignity Matters

**It accurately describes how science actually works.** The history of science is largely a history of tralse knowledge. Most past scientific theories are, strictly speaking, false. Phlogiston, caloric, the luminiferous ether, Newtonian absolute space, the steady-state universe -- all false. But all were epistemically excellent in their time. Without tralse knowledge as a category, the history of science looks like a parade of failure. With it, the history of science looks like what it actually is: a story of progressive epistemic achievement.

**It reduces epistemic anxiety.** If the only way to be a good knower is to be *right*, then every inquiry carries the implicit threat of failure. The stakes are always all-or-nothing. Tralse knowledge lowers the stakes without lowering the standards. You do not have to be right to be a good knower. You have to be *responsible*. The difference is liberating.

**It encourages intellectual courage.** If false belief is always failure, then the safest strategy is to believe as little as possible, to hedge every claim, to avoid commitment. Tralse knowledge encourages a different posture: believe boldly, but responsibly. Hold your beliefs with conviction and with humility. If they turn out to be false, you have tralse knowledge -- not shame.

**It respects the effort and skill of inquiry.** Inquiry is hard. Gathering evidence, weighing considerations, reasoning under uncertainty, forming conclusions in the face of incomplete information -- these are genuine cognitive achievements. Tralse knowledge says: the achievement is real, even when the conclusion is wrong. The effort was not wasted. The skill was not illusory.

As Emerick puts it: "You played the game correctly; reality rolled a crit fail."

---

## 7. Objections and Responses

### 7.1 "This is just 'false belief with good reasons' -- why give it a special name?"

**Objection.** Tralse knowledge is nothing more than justified false belief. Every epistemologist already knows that justified beliefs can be false. Why dress up an obvious fact in new terminology?

**Response.** Because naming it changes how we treat it. "False belief" implies failure. "Tralse knowledge" implies epistemic accomplishment despite factual defeat. Language shapes epistemic practice.

Consider a parallel. Before the concept of "PTSD" existed, soldiers returning from war with psychological trauma were called "shell-shocked" or simply "weak." The introduction of a clinical category -- Post-Traumatic Stress Disorder -- changed how society understood and treated the condition. The phenomenon was the same, but the name created a framework for recognition, respect, and response.

Similarly, "tralse knowledge" creates a framework for recognizing and respecting a common epistemic phenomenon that has been systematically mischaracterized as failure. The name is not decoration; it is intervention.

### 7.2 "This undermines the pursuit of truth"

**Objection.** If we start treating false beliefs as a form of knowledge, we weaken the incentive to seek truth. Why bother getting things right if being wrong can also count as an epistemic achievement?

**Response.** Tralse knowledge does not undermine the pursuit of truth. It redirects it. Instead of fetishizing outcome, it values process. Scientists who hold tralse knowledge do not stop trying to find truth; they simply stop flagellating themselves for being provisionally wrong.

A surgeon who is evaluated by process quality, not just patient outcomes, does not stop trying to save patients. If anything, she is *more* motivated: her skill is recognized regardless of outcomes, so she can focus on improving her technique rather than on defensive medicine. Similarly, an epistemic agent who knows that responsible inquiry is valued -- even when it produces false conclusions -- is freed to inquire more boldly, more honestly, and more ambitiously.

Tralse knowledge is a waypoint, not a destination. It is what you pass through on the way to better knowledge. Recognizing it does not make you stop walking; it makes you less afraid of the journey.

### 7.3 "If false beliefs count as knowledge, anything goes"

**Objection.** This theory opens the floodgates. If false beliefs can qualify as tralse knowledge, then anti-vaxxers, flat-earthers, and conspiracy theorists can all claim epistemic dignity for their beliefs. The concept is dangerously permissive.

**Response.** No. Tralse knowledge has strict entry conditions, and most irresponsible beliefs fail them spectacularly.

Flat-earth belief fails **Condition 1** (adequate evidence): the evidence overwhelmingly favors a spherical Earth, and no responsible assessment of available evidence leads to flat-earth belief.

It fails **Condition 3** (unforeseeable falsity): the falsity of flat-earth belief is not only foreseeable but glaringly obvious from the evidence available to any literate person in the 21st century.

It fails **Condition 4** (epistemic responsiveness): flat-earth believers characteristically refuse to revise their beliefs in the face of defeating evidence. They are dogmatically committed, not epistemically responsive.

Anti-vaccination beliefs fail similarly: the evidence base is clear, the falsity is foreseeable, and adherents typically resist revision. These are paradigm cases of *mere false belief*, not tralse knowledge.

The theory is not permissive. It is demanding. It requires that the believer have done everything right -- and that the world have been genuinely uncooperative. That is a high bar.

---

## 8. Implications for Philosophy of Science

### 8.1 The Paradox of Scientific Progress

Philosophy of science faces a persistent puzzle: how can science progress if most past science was "wrong"? If Newtonian mechanics was false, and phlogiston theory was false, and the caloric theory of heat was false, then the history of science is a history of error. Progress, on this reading, is the gradual replacement of one set of errors with another -- and we have no assurance that our current theories will fare any better.

This is sometimes called the "pessimistic meta-induction" (Laudan 1981). If all past theories have been false, then probably our current theories are false too. And if they are false, then science has never produced knowledge. The conclusion is paradoxical: science is our best method of inquiry, yet it has never succeeded.

### 8.2 The Tralse Knowledge Resolution

Tralse knowledge dissolves this paradox. Past science was not "wrong" in the sense that implies failure. It was *tralse-known*: epistemically excellent, provisionally successful, and eventually superseded by better epistemic achievements.

Scientific progress, on this account, is the history of tralse knowledge being replaced by *better* tralse knowledge -- or, occasionally, by actual knowledge (beliefs that have not yet been superseded, though they remain fallible). Each generation of scientists does not start from ignorance; it starts from the tralse knowledge of its predecessors, which provides the evidential base and conceptual framework for the next advance.

Thomas Kuhn's "paradigm shifts" (Kuhn 1962, *The Structure of Scientific Revolutions*) are, in tralse knowledge terms, transitions between tralse knowledge regimes. The old paradigm is not refuted in the sense of being shown to be epistemically worthless. It is transcended: its tralse knowledge is incorporated, corrected, and extended by a new paradigm that is (we hope) closer to truth but is itself almost certainly tralse.

The pessimistic meta-induction loses its sting. The conclusion that our current theories are probably false is not a reason for despair. It is a prediction that our current tralse knowledge will eventually be superseded by better tralse knowledge. That is not failure; that is the normal, healthy functioning of the scientific enterprise.

### 8.3 Progress as Tralse Knowledge Improvement

We can define scientific progress more precisely:

**Scientific progress** occurs when a community transitions from tralse knowledge B1 to tralse knowledge B2, where B2 meets the following conditions:

1. B2 accounts for all the empirical successes of B1
2. B2 accounts for the failures that led to B1's falsification
3. B2 is formed by a process at least as epistemically rigorous as the one that produced B1
4. B2 has greater empirical scope, predictive accuracy, or explanatory depth than B1

This definition captures the intuition that science progresses even through falsehood. It does not require that we arrive at truth; it requires that each successive tralse knowledge state is epistemically superior to its predecessor.

---

## 9. Broader Implications

### 9.1 For Education

If tralse knowledge is a genuine epistemic category, then education should not be organized solely around the transmission of currently-believed truths. Students should also learn *how to form tralse knowledge well*: how to gather evidence, reason under uncertainty, hold beliefs responsibly, and revise gracefully when evidence shifts.

The student who believes Newtonian mechanics -- who really *understands* it, can apply it, can explain why the evidence supports it -- has genuine epistemic accomplishment, even though the theory is strictly false. She has tralse knowledge, and that tralse knowledge is a necessary stepping stone to understanding relativity.

### 9.2 For Everyday Life

Most of what we "know" in everyday life is probably tralse. Our beliefs about other people's intentions, about the likely consequences of our actions, about the way institutions work -- these are formed under conditions of radical uncertainty, with limited evidence and imperfect reasoning. Many of them are false. But many of them are formed responsibly, and when they turn out to be wrong, the appropriate response is not self-recrimination but the recognition that we held tralse knowledge and should update accordingly.

### 9.3 For Intellectual Humility

Tralse knowledge offers a framework for intellectual humility that is neither self-deprecating nor self-aggrandizing. You can say: "I believe this on good grounds, and I may be wrong. If I am wrong, that does not make me foolish -- it makes me someone who held tralse knowledge." This posture is humble (acknowledging possible falsity) without being paralyzed (refusing to commit). It is, perhaps, the ideal epistemic attitude for creatures like us: finite, fallible, and doing our best.

---

## 10. Conclusion

Tralse knowledge is not a consolation prize for failed belief. It is not a polite euphemism for error. It is not a participation trophy for epistemic also-rans.

It is a genuine epistemic category that captures what binary epistemology cannot: the phenomenon of beliefs that are epistemically excellent and factually false. It respects human cognitive achievement by separating process quality from outcome, just as we separate surgical skill from patient survival, and moral intention from actual consequences.

It aligns with how science, medicine, and everyday life actually work. Scientists do not discard their predecessors as fools; they build on their tralse knowledge. Doctors do not flagellate themselves for reasonable diagnoses that turned out wrong; they learn and update. Ordinary people do not collapse in shame when a well-grounded expectation fails to materialize; they adjust and continue.

The concept has deep roots in the history of epistemology -- in Popper's verisimilitude, Dewey's warranted assertibility, van Fraassen's empirical adequacy, Peirce's fallibilism, and Gettier's demonstration that process and outcome can come apart. But it goes beyond all of these by naming and dignifying a state that each of them approaches but none of them fully captures.

Knowledge is not binary. It is ternary. Some of our finest knowing is tralse.

---

## References

Dewey, J. (1938). *Logic: The Theory of Inquiry*. New York: Henry Holt and Company.

Gettier, E. (1963). "Is Justified True Belief Knowledge?" *Analysis*, 23(6), 121-123.

Kuhn, T. S. (1962). *The Structure of Scientific Revolutions*. Chicago: University of Chicago Press.

Laudan, L. (1981). "A Confutation of Convergent Realism." *Philosophy of Science*, 48(1), 19-49.

Peirce, C. S. (1868). "Some Consequences of Four Incapacities." *Journal of Speculative Philosophy*, 2, 140-157.

Plato. *Theaetetus*. (c. 369 BCE).

Popper, K. R. (1963). *Conjectures and Refutations: The Growth of Scientific Knowledge*. London: Routledge.

van Fraassen, B. C. (1980). *The Scientific Image*. Oxford: Clarendon Press.

---

*Brandon Emerick, February 2026. Part of the Tralse Informational (TI) framework.*
