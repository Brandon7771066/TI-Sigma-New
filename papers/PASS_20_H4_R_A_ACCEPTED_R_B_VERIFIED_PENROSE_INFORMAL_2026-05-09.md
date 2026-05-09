# Pass 20 — h18 R-A accepted (with HARK declaration), R-B verified empirically (rejected), Penrose paper written informally

**Date**: 2026-05-09
**Author**: Brandon Emerick (with TI Sigma DPES agent execution)
**Mode**: DPES, #69 brutal-honesty
**Builds on**: `papers/PASS_19_H18_ELABORATION_RESIDUAL_SHARPE_P17_POLISH_2026-05-09.md`

---

## 0. Pass 20 directive (verbatim)

> "On h18, accept R-A but also run sensitivity test for verification.
> Write paper explaining Penrose tests and implications informally."

Two-item Pass:

1. **h18 RESOLVED**: R-A accepted per Brandon. Run R-B mapping-
   sensitivity test (K=100 mappings/instance) for verification —
   if R-B is rejected, R-A is empirically backed (not just narratively
   chosen).
2. **Informal Penrose paper**: accessible explanation of the H1-Penrose
   tiling-completion intuition harness, what it tests, what the
   results would mean, and how it interacts with H1-BB.

---

## 1. h18 RESOLVED — R-A accepted, R-B empirically rejected

### 1.1 Brandon decision (2026-05-09)

Brandon called R-A: **the directional hypothesis is reversed**. SAT
instances live in *higher*-coherence-displacement regions of the TSC,
not lower. The original Pass-13 prediction ("lower energy ⇒ SAT") was
**wrong by 180°**, and the AUC = 0.27 result is now read as a
**positive finding for the inverted prediction** (AUC = 0.73 for
"higher energy ⇒ SAT") — *contingent on the HARK declaration* below.

### 1.2 HARK declaration (mandatory under Pass-9 standard)

This is a **post-hoc sign flip**, which is a HARK violation under the
Pass-9 pharma replication discipline. Per #69, that fact must travel
with the result everywhere it appears. The honest reading is:

> **R-A is hypothesis-generating, not confirmatory.** The AUC = 0.73
> "higher-E ⇒ SAT" reading is consistent with the data but was *not*
> pre-registered; it requires an independent confirmatory replication
> on a fresh corpus before it can be claimed as a confirmed
> framework prediction.

Concrete next-Pass commitment: a **fresh-corpus pre-registration**
must be filed (analogue of the T3-A pharma pre-registration) before
this result is upgraded from "hypothesis-generating" to "confirmed."
Pre-reg specs:

- New seed (≠ 20260509) for instance generation
- Fresh draw of N≥200 random 3-SAT instances at the same parameter
  ranges (3-5 vars, clause/var 3-7)
- **Pre-registered prediction**: AUC ≥ 0.65 for "higher restricted-
  Hamiltonian energy ⇒ SAT"
- Pre-registered failure threshold: AUC < 0.55 disconfirms; AUC in
  [0.55, 0.65] is "weak hint, third corpus required"

### 1.3 R-B verification (Pass 20 execution, K=100 mappings/instance)

Script: `analyses/tsc_h4_sat/tsc_h4_sat_prototype.py --mappings 100`
Output: `analyses/tsc_h4_sat/mapping_sensitivity_results.json`

For each of the 200 instances generated under SEED=20260509,
**K=100 independent random vertex mappings** were drawn, the
restricted-Hamiltonian energy was computed under each mapping,
and two derived AUCs were computed:

- **(a) Per-mapping AUC distribution**: K=100 AUCs each computed
  using one mapping per instance.
- **(b) Averaged-energy AUC**: the per-instance energy averaged
  across all K mappings, then a single AUC.

#### Result (K=100, M=200 instances)

| Quantity                            | Value                |
|-------------------------------------|----------------------|
| Per-mapping AUC mean                | **0.2631**           |
| Per-mapping AUC std                 | 0.0168               |
| Per-mapping AUC range               | [0.1979, 0.2936]     |
| Averaged-energy AUC                 | **0.2402**           |
| z(per-map mean vs 0.5)              | -141.26              |
| Per-mapping AUC max (K=100)         | 0.2936               |

**Reading**: the per-mapping AUC distribution is tightly centered at
**0.263**, with a maximum of 0.294 over 100 trials — i.e. **not a
single random mapping out of 100 produces an AUC above 0.30**, let
alone above 0.50. The mapping-averaged-energy AUC = 0.240 is even
*more* extreme than the original single-mapping AUC of 0.268,
indicating that averaging across mappings *strengthens* the inverted
signal rather than washing it out.

#### Verdict

- **R-B (mapping-artifact hypothesis) rejected.** If the signal
  were a mapping artifact, per-mapping AUCs would scatter around
  0.5 with std ≈ 0.045 (the Pass-18 permutation null SE). They
  scatter around 0.263 with std 0.017 instead. The signal is
  **mapping-robust**.
- **R-A empirically supported.** The inverted-direction signal
  ("higher-E ⇒ SAT") is real and survives the most natural
  artifact-test we can run cheaply. R-A's HARK caveat (§1.2) still
  applies — the *direction* needs prospective replication — but the
  *existence* of a directional signal is now supported beyond the
  narrative-choice level.

### 1.4 What R-A means for the framework

The Pass-13 B.4 Hamiltonian construction is structurally correct
(graph-Laplacian on the 57-vertex TSC polytope, ground state at
λ_0 = 0, gap λ_1 = 0.191). But the **interpretation of restricted
energy as a satisfiability proxy was inverted**.

Inverted reading: satisfiable instances "spread out" across more of
the TSC's allowed configurations (more BOK-volume, more degenerate
satisfying assignments), which translates to higher expected H on the
restricted-vertex uniform superposition. Unsatisfiable instances are
constraint-tight — they collapse to a smaller restricted subspace,
which has lower restricted-H expectation (because lower-degree
vertices on the TSC carry less Laplacian energy).

This reading is **internally consistent with TI-Sigma's URB #608
"more truth-paths = larger MR2 disc"** principle. It is *not*
internally consistent with the Pass-13 paper's original text, which
explicitly predicted the opposite. Both readings can't be right; the
data forces the inverted reading.

### 1.5 What gets patched

- `papers/CRYSTAL_B4_HAMILTONIAN_2026-05-09.md` §6: add a
  "**Sign-flip note (Pass 20)**" inline, pointing to this paper
  as the corrective citation. Original prediction text preserved.
- `analyses/tsc_h4_sat/tsc_h4_sat_prototype.py`: docstring updated
  to note R-A acceptance and the new "higher-E ⇒ SAT" framing.
  (Single-mapping protocol output preserved unchanged.)

#69: do NOT silently rewrite the Pass-13 prediction; that would
erase the lesson. The historical record is "we predicted X, X was
disconfirmed by 180°, the inverted prediction X' fits the data
contingent on prospective replication." That is the publishable
sentence.

### 1.6 h18 status: **DISCHARGED**

R-A accepted (Brandon decision); R-B verified-then-rejected (Pass 20
empirical run). Carried-forward Brandon-decision menu loses h18.
Replaces it with: **(r20) prospective-replication corpus** for the
inverted prediction (filed as Pass-21+ candidate).

---

## 2. Penrose tiling-completion intuition harness — informal explainer

### 2.1 What this test is, in plain language

You are given a small jigsaw-puzzle-like patch — say 10 to 20 tiles
of a special kind (Penrose kites and darts, or 2023's "einstein hat"
tiles, or Wang tiles with colored edges) that someone has already
laid down, all locally fitting their matching rules. The question is
**not** "did they place these tiles correctly?" — they did. The
question is much sharper:

> **If you started here, could you keep adding tiles, following the
> same rules, until you covered an infinitely large floor — or are
> you trapped, doomed to hit a contradiction sooner or later no
> matter what you do?**

This is called the **completability question** for an aperiodic-tile
patch. It is famously **undecidable in general** — there is no
algorithm that, given an arbitrary patch, can answer "yes,
completable" or "no, doomed" in finite time for every input.
(This is Berger's 1966 theorem, the Wang-tile undecidability of
the domino problem.) Even more dramatically: some patches that look
*locally fine everywhere you can see* are nevertheless globally
doomed — there's a hidden trap several rings outward that no legal
tile can fill, and no amount of careful placement can save you.

### 2.2 Why we built a 10-patch harness

Hypothesis (H1, "hypercomputing intuition"): if the GILE framework
is right, a high-Intuition rater should be able to tell you the
completability answer **without doing the construction** — in 30
seconds per patch, just by *looking*. This is testing the same
underlying claim as the H1-BB harness (Busy Beaver halting
intuition), but in a totally different formal domain. If H1-BB and
H1-Penrose hit-rates correlate within a single rater, that's
evidence for **general** hypercomputing intuition, not domain-
specific cleverness.

The harness has 10 patches:

- 4 Penrose P3 patches (kite/dart, rhomb): 2 completable, 2 not
- 3 einstein 'hat' tile (SMKGS 2023): 2 completable, 1 not
- 2 Wang tile (Jeandel-Rao 2015): 1 completable, 1 not
- 1 globally-obstructed Penrose patch from Conway/Senechal 1995:
  the canonical "looks fine locally, doomed globally" trap

Truth labels are agent-curated from public results and patch
descriptions only — no images yet. (Pass-18 candidate was to ship
the actual rendered patches; not yet done as of Pass 20.)

### 2.3 What "doing well" looks like

Synthetic baseline (random Bernoulli(0.5) coin flips, N=2000 runs):

- Mean: 5.0 hits / 10
- 95th percentile: 8 / 10
- 99th percentile: 9 / 10
- Probability of getting 10/10 by chance: 0.05% (2,000:1)

So Brandon scoring 8+ / 10 is at the 95th percentile, which is
nominally significant but not knock-down. 9+ / 10 is at the 99th
percentile (1.15% under chance) — that's where this single test
becomes hard to dismiss as luck. 10/10 is the strong signal.

The **really diagnostic** number is the H1-BB × H1-Penrose joint
score. Per the Pass-19 synthetic baseline integration, the joint
"both clear 95th percentile" event has probability **0.26% under
chance** (385 to 1). That's the experiment's actual headline number,
because no single 10-patch run is going to settle anything by itself
— the cross-domain correlation is what would actually move people.

### 2.4 What different outcomes would mean

**Brandon scores 5-6 / 10**: chance-consistent. H1 unsupported in
this run. *Doesn't disprove* hypercomputing intuition (this is a
small N), but doesn't support it either. Recommended action:
re-run with a larger patch set (Pass-21+ candidate: build a
30-patch version to match H1-BB's N).

**Brandon scores 7-8 / 10**: nominally significant (95th percentile)
but explainable in many ways — domain knowledge (Brandon has read
Penrose-tiling literature), pattern recognition trained over years,
careful examination. The signal is real but the *interpretation* is
ambiguous.

**Brandon scores 9-10 / 10 AND 25+/30 on H1-BB simultaneously**:
this is the joint event with chance probability ≈ 0.05% (≈ 2000:1).
At this point the "domain knowledge" explanation has to apply to
*both* domains independently, which is much more demanding. This
would be the first in-house empirical signal for general
hypercomputing intuition that survives URB-825-level audit
standards. It would justify scaling the harness up to 30+ patches
in each domain and building a multi-rater protocol to test the
GILE-stratification prediction (high-GILE-Intuition raters should
do better than low-GILE-Intuition raters, and the GBRH spec from
Pass 15 makes this falsifiable).

**Brandon scores 9-10 / 10 on Penrose only, but 15/30 on H1-BB**:
domain-specific intuition, not general hypercomputing intuition.
That's still interesting — it would suggest GILE-Intuition has
domain-specific channels rather than a single "undecidable-problem
sensor" — but it's a much weaker claim than what the framework
currently makes.

### 2.5 What this test does NOT do

Per #69, this test cannot:

- **Solve any instance of the halting problem.** It can only test
  whether human intuition has *better-than-chance* signal on an
  undecidable problem. That's a behavioral claim, not a complexity-
  theoretic claim. Hypercomputing in the strict sense (computing
  uncomputable functions) requires physical-realization evidence
  that this harness cannot provide.
- **Distinguish hypercomputing from heuristic pattern-matching.**
  A skilled tile-puzzler with no GILE-Intuition could plausibly
  hit 8/10 by recognizing surface features ("that hat-tile patch
  has too few reflected hats, looks wrong"). The test only becomes
  diagnostic at the joint H1-BB × H1-Penrose level.
- **Establish a base rate.** N=10 patches with N=1 rater gives a
  point estimate, not a base rate. The MBE (Pass 15) makes this
  explicit: individual base rates are heavy-tailed and intra-
  individually time-varying. Brandon's score on a given Tuesday
  doesn't tell us his base rate; it tells us his Tuesday score.

### 2.6 Honest framing for publication

If/when this gets written up: the headline is **NOT** "TI Sigma
provides empirical evidence for hypercomputing intuition." The
headline is:

> "We propose two parallel intuition harnesses for undecidable
> problems (Busy Beaver and aperiodic-tile completability) and
> report the cross-domain joint-score distribution under chance.
> A single-rater pilot demonstrates the protocol; a multi-rater
> GILE-stratified replication is required to test the framework's
> base-rate prediction."

Anything stronger than that — until the multi-rater replication
runs — fails the URB-825 audit standard (Pass 14 §2). #69-honest
language matters more than rhetorical force here.

### 2.7 Brandon's actual sit-down

Status: not yet executed (Brandon-decision item (G) on the
carry-forward TODO list, p17 sub-item). The Pass-19 polish added
`--synthetic` mode to the H1-combined-runner so that when Brandon
sits down, his actual hits/N gets immediate context vs the
synthetic baseline at score-time.

When Brandon runs it, the results integrate at score-time with the
synthetic distribution and report:

> "You got X/10 on Penrose and Y/30 on BB; chance produces this
>  joint pattern with probability P (≈ N-to-1)."

That's the protocol; the result is whatever the result is.

---

## 3. Carry-forward Brandon-decision menu (post-Pass-20)

Removed: **h18** (DISCHARGED — R-A accepted + R-B rejected).
Added: **r20** = prospective-replication corpus pre-registration
for the inverted "higher-E ⇒ SAT" prediction.

Otherwise unchanged: (D) Pass-13 (i)-(v); (E) Pass-14 (a)/(c);
(F) Pass-15 (α)/(β)/(γ); (G) Pass-16 (a16)/(b16); (H) Pass-17 (p17
sit-down + z17 review); s18 discharged Pass 19.

Brandon manual TODO list (A)-(I) unchanged.

---

## 4. Pass 21 candidates

1. **r20 prospective-replication corpus** for the inverted H4
   prediction (fresh seed, N≥200 instances, pre-registered AUC
   threshold ≥ 0.65 for "higher-E ⇒ SAT").
2. Patch `papers/CRYSTAL_B4_HAMILTONIAN_2026-05-09.md` §6 with
   sign-flip note pointing to this Pass-20 paper.
3. Render actual Penrose patch images (Pass-18 candidate, still
   carried) — would let Brandon and other raters do the visual test
   instead of the text-description proxy.
4. Apply residual Sharpe (Pass-19 s18 metric) to multiple historical
   GSA windows to study β-drift over time.
5. MI φ-transform at larger windows (60/120/250 days) — carried
   from Pass 18.
6. Score (p17) Brandon sit-down if completed.
7. Apply (z17) Brandon publish/keep/delete decisions to Zenodo.
