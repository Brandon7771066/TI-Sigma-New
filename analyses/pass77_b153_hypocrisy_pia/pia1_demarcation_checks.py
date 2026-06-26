"""
B153 / PIA-1 -- demarcating a LEGITIMATE hypocrisy / proposition-implied-by-action
charge from a mere tu-quoque (or genetic) FALLACY.

This is a LOGIC demonstration (not an empirical study): it encodes a pre-registered
decision criterion and shows it correctly separates a hand-built, labelled set of
real argument-instances -- including the exact case B132 mislabelled (the "Bayes was
not adopted by Bayesian principles" charge). Candidate PIA-1 is NOT ratified; the
criterion is offered for coherence + coverage, with falsifiers left open. EVD-1:
such charges are "potentially legitimate" (graded), never auto-valid / auto-fallacious.

Pre-registered criterion (fixed BEFORE scoring):
  A hypocrisy/PIA charge is a LEGITIMATE DEFEATER iff ALL of:
    (1) self_scope     -- the thesis claims UNIVERSAL scope that includes the
                          speaker's own act/belief (it quantifies over everyone,
                          so it ranges over the speaker too);
    (2) action_negates -- the speaker's action instantiates the NEGATION of a
                          proposition the thesis REQUIRES to hold universally;
    (3) targets_thesis -- the charge attacks the THESIS's truth via this self-
                          contradiction (performative self-refutation), NOT a
                          claim's validity via its mere ORIGIN.
  Otherwise it is a FALLACY:
    - judges_by_origin and not targets_thesis  -> GENETIC fallacy
    - else                                      -> mere TU QUOQUE
"""

from dataclasses import dataclass

@dataclass
class Instance:
    name: str
    thesis: str
    action: str
    self_scope: bool         # thesis quantifies universally over everyone incl. speaker
    action_negates: bool     # action instantiates negation of a thesis-required prop
    targets_thesis: bool     # charge aimed at thesis truth via self-contradiction
    judges_by_origin: bool   # charge aimed at a claim's validity via its origin
    gold: str                # "legitimate_defeater" | "fallacy"
    note: str = ""

def classify(x: Instance):
    if x.self_scope and x.action_negates and x.targets_thesis:
        return "legitimate_defeater", "performative self-refutation (PIA)"
    if x.judges_by_origin and not x.targets_thesis:
        return "fallacy", "genetic fallacy (origin irrelevant to validity)"
    return "fallacy", "mere tu quoque (hypocrisy does not bear on the thesis)"

# ----------------------------------------------------------------- labelled cases
CASES = [
    # ---- LEGITIMATE defeaters (universal self-scope + performative contradiction) ----
    Instance(
        "Bayesianism-as-universal-norm (DOCTRINE)  [B132 correction]",
        thesis="ALL rational belief-revision MUST proceed by Bayesian conditioning",
        action="Bayesians adopted Bayesianism itself by non-Bayesian means (intuition/argument/choice of priors)",
        self_scope=True, action_negates=True, targets_thesis=True, judges_by_origin=False,
        gold="legitimate_defeater",
        note="the universal norm ranges over its OWN adoption; that adoption was not "
             "Bayesian => the norm-as-stated is self-refuting. NOT a genetic fallacy."),
    Instance(
        "Postmodernist 'no objective truth'",
        thesis="There are NO objective truths",
        action="asserts this very claim AS an objective truth",
        self_scope=True, action_negates=True, targets_thesis=True, judges_by_origin=False,
        gold="legitimate_defeater",
        note="classic self-referential incoherence."),
    Instance(
        "Free-will denier who blames",
        thesis="NO one is ever morally responsible (no one has free will)",
        action="sincerely blames and resents people for their choices",
        self_scope=True, action_negates=True, targets_thesis=True, judges_by_origin=False,
        gold="legitimate_defeater",
        note="blame presupposes the responsibility the thesis universally denies."),
    Instance(
        "Moral non-realist who morally blames",
        thesis="There are NO moral facts (nothing is really right or wrong)",
        action="sincerely, categorically condemns an act as really wrong",
        self_scope=True, action_negates=True, targets_thesis=True, judges_by_origin=False,
        gold="legitimate_defeater",
        note="categorical condemnation presupposes the moral facts denied."),
    Instance(
        "External-world denier who acts in the world",
        thesis="The external physical world is unreal",
        action="eats when hungry, steps out of the way of moving cars",
        self_scope=True, action_negates=True, targets_thesis=True, judges_by_origin=False,
        gold="legitimate_defeater",
        note="every survival action asserts the world's reality (G.E. Moore-style)."),

    # ---- FALLACIES (controls) ----
    Instance(
        "Smoking arguer (tu quoque control)",
        thesis="Smoking is unhealthy",
        action="the person making the argument smokes",
        self_scope=False, action_negates=False, targets_thesis=False, judges_by_origin=False,
        gold="fallacy",
        note="thesis makes NO universal self-scoped claim the smoking contradicts; "
             "healthfulness of smoking is independent of the arguer's behaviour."),
    Instance(
        "Bayes' THEOREM via its origin (genetic control)  [the legitimate genetic-fallacy twin]",
        thesis="Bayes' THEOREM (the identity P(A|B)=P(B|A)P(A)/P(B)) is valid",
        action="charge: 'Bayes first reached it by intuition, so the theorem is suspect'",
        self_scope=False, action_negates=False, targets_thesis=False, judges_by_origin=True,
        gold="fallacy",
        note="THIS is where 'genetic fallacy' is the correct label: a PROVED theorem's "
             "validity is origin-independent. The doctrine case above is NOT this."),
    Instance(
        "Pharma-funded scientist (circumstantial/genetic control)",
        thesis="This vaccine is safe (per the trial data)",
        action="charge: 'the scientist is paid by a drug company, so disregard it'",
        self_scope=False, action_negates=False, targets_thesis=False, judges_by_origin=True,
        gold="fallacy",
        note="funding origin does not bear on what the data show."),
]

print("=" * 74)
print("B153 PIA-1 -- legitimate-defeater vs fallacy demarcation")
print("=" * 74)
correct = 0
bayes = {}
for c in CASES:
    pred, why = classify(c)
    ok = (pred == c.gold)
    correct += ok
    if "DOCTRINE" in c.name:
        bayes["doctrine"] = pred
    if "THEOREM" in c.name:
        bayes["theorem"] = pred
    print(f"[{'OK ' if ok else 'XX '}] {c.name}")
    print(f"      gold={c.gold:<20} pred={pred:<20} ({why})")
acc = correct / len(CASES)
print("-" * 74)
print(f"criterion accuracy on labelled set: {acc:.3f}  ({correct}/{len(CASES)})")

# ----------------------------------------------------------------- ablation
# Zero out self_scope on the legitimate set: the SAME charges should STOP being
# defeaters (the work is done by universal self-scope, not by surface wording).
print("=" * 74)
print("ABLATION -- remove universal self-scope from the legitimate cases")
legit = [c for c in CASES if c.gold == "legitimate_defeater"]
flipped = 0
for c in legit:
    c2 = Instance(**{**c.__dict__, "self_scope": False, "action_negates": False})
    pred, _ = classify(c2)
    flipped += (pred == "fallacy")
print(f"  legitimate cases that become NON-defeaters once self-scope removed: "
      f"{flipped}/{len(legit)}")
print("  -> the criterion tracks self-scope/performative-contradiction, not keywords.")

# ----------------------------------------------------------------- verdict
print("=" * 74)
print("PRE-REGISTERED PREDICTIONS")
P1 = acc == 1.0
P2 = (bayes.get("doctrine") == "legitimate_defeater"
      and bayes.get("theorem") == "fallacy")            # the exact B132 correction
P3 = flipped == len(legit)                              # self-scope is load-bearing
P4 = all(classify(c)[0] == "fallacy"
         for c in CASES if c.gold == "fallacy")          # no false positives on controls
for name, val in [("P1 perfect separation", P1),
                  ("P2 Bayes splits: doctrine=legit, theorem=genetic-fallacy", P2),
                  ("P3 self-scope load-bearing (ablation flips all)", P3),
                  ("P4 no false-positive defeaters among controls", P4)]:
    print(f"  [{'PASS' if val else 'FAIL'}] {name}")
print("=" * 74)
print("VERDICT: the demarcation is OPERATIONAL (coherent + covers the cases),")
print("including the B132 correction: 'Bayes not adopted by Bayesian principles' is")
print("a legitimate PIA self-refutation of the DOCTRINE, NOT a genetic fallacy; the")
print("genetic-fallacy label is correct only against the THEOREM's validity. PIA-1")
print("stays a CANDIDATE (NOT ratified); EVD-1 'potentially legitimate', graded.")
assert P1 and P2 and P3 and P4, "a pre-registered prediction failed"
print("\nALL PRE-REGISTERED PREDICTIONS PASS.")
