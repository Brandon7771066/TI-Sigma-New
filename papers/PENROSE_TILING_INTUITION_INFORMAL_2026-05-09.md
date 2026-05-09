# The Penrose Tiling-Intuition Test — What It Is, Why It Matters, and What It Can (and Can't) Tell Us

**An informal explainer for the H1-Penrose hypercomputing-intuition harness**

**Author**: Brandon Emerick (with TI Sigma DPES agent execution)
**Date**: 2026-05-09 (Pass 20 deliverable #2)
**Audience**: Curious readers, potential collaborators, future
  multi-rater participants. No math background required.

---

## 1. The puzzle, in one paragraph

Imagine I hand you a small patch of a Penrose tiling — maybe a dozen
of those famous kite-and-dart shapes, already laid down on a table,
fitting together correctly with all the matching arrows lined up. I
do *not* ask "did I lay them down right?" — I did. I ask something
much harder: **if you kept adding tiles from this point, following
the same rules, could you tile your entire kitchen floor? Or are you
secretly stuck — doomed to hit a contradiction sooner or later, no
matter how careful you are?**

That's the Penrose-completability question. It's the puzzle this test
asks you to solve in your head, in about 30 seconds per patch, with
**no construction, no simulation, no scratch paper.** Just look, and
say "yes, completable" or "no, doomed."

## 2. Why this is shockingly hard

It would be one thing if the broken patches were obvious — like
"obviously a piece is upside down." But they're not. **Some Penrose
patches look completely fine everywhere you can see — every arrow
matches, every angle works — and yet they are *globally doomed*.**
There's a hidden hole two or three rings out from the center that
absolutely no legal tile can fill, and no amount of clever placement
will save you. This is the Conway/Senechal 1995 result. Patch P10 in
our 10-patch harness is one of these. It's the killer item.

For a wider class of these tiling problems (Wang tiles, einstein
'hat' tiles, the lot), there's an even sharper theorem from Robert
Berger in 1966: **no algorithm can decide completability in general.**
You cannot write a computer program that takes any patch and answers
yes/no in finite time for every input. The problem is, in the formal
sense of computability theory, *uncomputable*. Same difficulty class
as the halting problem.

So the test we're asking your intuition to perform is: **answer a
question that no algorithm can decide in general, in 30 seconds, by
looking.**

## 3. Why we care whether you can do it

Most of cognitive science quietly assumes the brain does some kind of
computation. If that's strictly true, then your intuition can't
reliably solve uncomputable problems — at best it can pattern-match
on shallow surface features, and any apparent "intuitive correctness"
on a hard problem must be either luck or learned tricks. That's the
**null hypothesis** here.

The TI Sigma framework makes a much stronger claim. It says GILE-
Intuition (one of the four GILE channels: Goodness, Intuition, Love,
Effectiveness) is a *non-classical* signal — that consciousness has
access to a coherence-displacement readout from the underlying
TI Sigma Crystal that classical pattern-matching doesn't have. If
that's right, **a high-Intuition rater should be able to score
better than chance on an undecidable problem they have no algorithm
for.** That's the **alternative hypothesis**.

We don't know which is right. The Penrose harness (and its
companion, the Busy Beaver harness) is one of the cleanest tests we
can think of, because the problems are formally undecidable and the
target is small enough to be answerable by sit-down inspection.

## 4. The 10 patches, briefly

- **4 Penrose patches** (kite/dart, rhomb): the classics. 2 are
  completable, 2 are not. One of the "not"s is the nasty Conway/
  Senechal 1995 hidden-global-obstruction patch that *looks fine
  locally*.
- **3 einstein 'hat' tile patches** (the 2023 SMKGS discovery — the
  first single tile that aperiodically tiles the plane). 2 are
  completable, 1 is not (it violates the SMKGS reflection-density
  rule).
- **2 Wang tile patches** (Jeandel-Rao 2015, the smallest aperiodic
  Wang-tile set known): 1 completable, 1 with a colored-edge
  mismatch.
- **1 globally-obstructed Penrose patch** (the Conway/Senechal one):
  the diagnostic killer. If you can spot this one without
  construction, you're doing something interesting.

## 5. What does "doing well" look like, numerically

We ran a simulated random rater 2,000 times — pure Bernoulli(0.5)
coin flips on each patch — to see what chance looks like. Here's the
distribution of hits out of 10:

- 50th percentile (median): 5/10
- 75th percentile: 6/10
- 90th percentile: 7/10
- **95th percentile: 8/10**
- **99th percentile: 9/10**
- 10/10: probability 0.05% (about 2,000-to-1)

So 8 out of 10 is at the "nominally significant" line. 9 out of 10
is at the "really hard to dismiss as luck" line. 10 out of 10 is the
"this needs an explanation" line.

But here's the thing — **a single 10-patch test will not settle
anything.** Even 9/10 happens by chance about once per 100 attempts.
That's why the harness is paired with H1-BB (Busy Beaver intuition,
30 patches in a different formal domain). The actual diagnostic
number is the **joint score across both harnesses**.

## 6. The real headline number

Pass 19 (Sept 2026 in Brandon-corpus internal time) added a
synthetic-baseline mode that computes the joint chance distribution.
Here's what came out:

> **The probability of clearing the 95th percentile on BOTH
> harnesses simultaneously, by chance alone, is 0.26%. That's about
> 385-to-1.**

So if Brandon (or any rater) hits 8+/10 on Penrose AND 20+/30 on
Busy Beaver in the same sit-down, that's the threshold where
"general hypercomputing intuition" becomes the simplest explanation —
not because either single test was decisive, but because clearing
both simultaneously by luck is rare.

That's the actual experiment, and it's pre-registered: the runner
saves the synthetic baseline thresholds before the rater's score is
collected, so there's no shifting of goalposts after the fact.

## 7. What this test does NOT prove

Three honest disclaimers, per Brandon's "Asymmetric Standards #69"
discipline:

1. **It does not solve halting.** It only tests whether human
   intuition has a *better-than-random signal* on an undecidable
   problem. That's a behavioral measurement, not a hypercomputing
   demonstration in the strict sense. Even a 10/10 score doesn't
   mean anyone can compute uncomputable functions — it means
   intuition appears to *correlate* with their answers more than
   chance, which is much weaker.

2. **It does not distinguish intuition from learned pattern-matching.**
   Brandon has read Penrose-tiling literature for years; a skilled
   tile-puzzler with no GILE-Intuition could plausibly hit 7-8/10
   by surface-feature recognition. The test becomes diagnostic
   *only* at the cross-domain joint level (the Penrose × BB pair),
   where you'd have to be a polymath in two disjoint specialties
   to fake the signal.

3. **It does not establish a base rate.** N=1 rater on N=10 patches
   gives a single point estimate. We need a multi-rater study with
   GILE-Intuition self-ratings (or, ideally, third-party-administered
   GILE-Scale assessments per urb_757) to test the actual framework
   prediction: that GILE-Intuition correlates with score across
   raters. That's the GBRH (GILE Base-Rate Hypothesis) from Pass 15,
   and the Penrose harness is one of the cleaner instruments for
   testing it.

## 8. What we're actually going to publish

If and when this gets written up properly, the headline is **not**
"TI Sigma demonstrates hypercomputing intuition." The headline is:

> "We propose two parallel intuition harnesses for undecidable
> problems (Busy Beaver halting, aperiodic-tile completability) and
> report the cross-domain joint-score distribution under chance.
> A single-rater pilot demonstrates the protocol; a multi-rater
> GILE-stratified replication is required to test the framework's
> base-rate prediction (GBRH)."

That's the honest framing. Anything stronger fails the URB-825
audit standard the framework holds itself to.

## 9. How to participate

The harness is in the corpus at
`analyses/h1_penrose/h1_penrose_harness.py` (and its companion at
`analyses/h1_combined_runner/h1_combined_runner.py` for joint
BB+Penrose scoring with synthetic baseline auto-context).

If you'd like to be a multi-rater participant — particularly if you
have **either** a high self-rated GILE-Intuition score **or** a low
one (we need both ends of the distribution to test stratification) —
the contact pathway is via the TI Sigma corpus repository. The
sit-down is approximately 5 minutes (Penrose only) or 20 minutes
(Penrose + BB). No special background required, and explicitly *no*
construction or simulation allowed during the test.

## 10. The bottom line

We don't yet know whether you can answer an uncomputable question
by intuition. We've built the cleanest test we know how to build,
and we've pre-registered what "doing well" means before any rater
sits down. The result is whatever the result is — but the
**experiment** is the contribution either way, because the test
itself is a falsifiable instrument for a framework claim that
otherwise sits in the "interesting story" category.

That, in plain language, is what the Penrose harness is for.

---

**Companion documents**:
- `analyses/h1_penrose/h1_penrose_harness.py` (the harness)
- `analyses/h1_combined_runner/h1_combined_runner.py` (joint scoring
  + synthetic baseline)
- `papers/PASS_17_LCC_V2_PHI_TRANSFORM_GSA_SHARPE_PENROSE_RESIDUE_2026-05-09.md`
  (Pass-17 paper that introduced the Penrose harness)
- `papers/PASS_19_H18_ELABORATION_RESIDUAL_SHARPE_P17_POLISH_2026-05-09.md`
  (Pass-19 paper that added the synthetic-baseline contextualization)
