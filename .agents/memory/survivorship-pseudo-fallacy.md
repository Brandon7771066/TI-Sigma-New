---
name: Survivorship as a pseudo-fallacy (memory-selection conditioning, SPF-1)
description: When the "survivorship bias!" charge is a misdiagnosis vs a real fallacy — the pre-outcome-vs-outcome selection distinction, and the honesty rails that keep the corpus's survivorship corrections intact.
---

# Survivorship as a (possibly/likely) pseudo-fallacy — SPF-1

CANDIDATE, not ratified; canonical count stays 79. The decisive idea is a **two-axis
selection distinction**; everything else follows.

## The core distinction (don't blur it)
- **Axis A — null-exclusion:** filter on a **pre-outcome** variable (seriousness / confidence
  logged *before* you know the result). "I only count the times I seriously tried" is THIS.
  It is harmless **reference-class conditioning** — it changes the *question* from the
  population rate to P(success | serious), which is the correct question for "what happens
  when I commit?" Excluding nulls is NOT a bias.
- **Axis B — outcome-asymmetry:** filter on the **outcome** (forget serious losses more than
  serious wins). THIS is the only thing that inflates = real survivorship (Wald's bombers).
- **The pseudo-fallacy = firing "survivorship!" at an Axis-A move.** It is a real fallacy only
  for Axis-B.

## Why it's only "possibly/likely" (the hinge)
The claim is **conditional on outcome-symmetric memory** ("memory quality" = how faithfully you
keep the serious *failures*). Quantify with **α = win-favoring forgetting = 1 − memory quality**.
Bias is ~0 at α=0 (pseudo-fallacy regime) and rises monotonically; finite crossover α*. So it's
a **regime claim, not an absolute** — matching the author's own "not *so much* a fallacy" hedge.

## Honesty rails (the parts to never drop)
- **#69 both ways on the crux:** real psych evidence FOR symmetry (Zeigarnik 1927 = failed/
  interrupted tasks remembered *better*; negativity bias Baumeister 2001 / Rozin-Royzman 2001;
  flashbulb Brown-Kulik 1977) AND AGAINST (self-serving Miller-Ross 1975; rosy retrospection
  Mitchell 1997; hindsight Fischhoff 1975; flashbulb-INaccuracy Neisser-Harsch 1992). Net sign
  of α is **person/domain-specific and unresolved** ⇒ verdict stays hedged.
- **The sim proves the CONDITIONAL only** — it is a logic/method demo, NOT a claim that real
  human α ≈ 0. Never present it as empirical.
- **Anti-cheat (SPF-1-F3):** the confidence defining "serious" must be **prospectively logged**,
  never recalled — hindsight inflates win-confidence and silently turns Axis-A into Axis-B
  (sim: +0.061 inflation even at α=0).
- **Does NOT weaken the corpus's existing survivorship CORRECTIONS** (vindicated-mavericks Ch4;
  MEP/#69 bias-sim +36→+43pp) — those are Axis-B outcome-selection, untouched. SPF-1 only carves
  out the misapplied Axis-A case.

## Where it sits in the canon
- Structural **twin of IPA-1** ("valid objection that becomes a pseudo-fallacy when misapplied");
  ratify near it.
- **Memory-side companion of HAN-1's "ignore-nulls-honestly"** (exclude nulls ✓, delete committed
  misses ✗); SPF-1 asks whether you actually *remember* the misses.
- **Reinforces SM-1** (sacred-mistakes ledger): the ledger is needed *because* you can't verify
  your own α from the inside; SPF-1 explains when it would be unnecessary but keeps it as default.
- EVD-1: survivorship-conditioned recall = graded **Weight**, not Proof; load-bearing only after
  independent validation. "TI Sigma Statistics" = this reference-class-conditioning stance.

## Pointers
- Anchor: `papers/PASS_77_B146_SURVIVORSHIP_AS_PSEUDO_FALLACY_MEMORY_SELECTION_CONDITIONING_2026-06-25.md`
- Harness: `analyses/pass77_b146_survivorship_pseudo_fallacy/survivorship_checks.py` (all checks pass; no numerology/no load-bearing constant).
- Book: `book/ch17_communication_fallacies.md` §"The survivorship pseudo-fallacy"; queued in `book/PENDING_RATIFICATION_PRINCIPLES.md`.
- Falsifiers SPF-1-F1 (prospective outcome-blind memory study) / F2 (population-target ⇒ fallacy stands) / F3 (retrospective confidence invalid) all OPEN.
