# Pass-77 B80 — Intuition as a general (overlap-gated) capacity; arts-as-a-new-language (IGC-1)

**Date:** 2026-05-28 (Pass-77 batch-80)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local numpy/matplotlib).
**Compute:** `analyses/pass77_b80_intuition_general_capacity/run_b80.py` (+`results.json`, 2 figures)
**Status:** ONE CANDIDATE principle (IGC-1) + 2 biographical anchors. Ratification = Brandon's explicit
choice. Canonical count unchanged **74**.

---

## 0. Source — Brandon insight (2026-05-28, verbatim, two threads)

> **(intuition / arts)** "My pitch recognition and voice control during singing practice seem to be
> heavily integrated with my already highly-developed intuition capacity! Intuition certainly seems to be
> a general capacity of the mind (check cog-sci research on this question). Tapping into music or another
> discipline of the arts is rather like learning a new language than a new trade. With a new language,
> you can leverage your existing verbal intelligence. By contrast, a new trade may have minimal
> overlapping skills with another trade."
>
> **(self-characterization)** "I actually am pretty skeptical of a philosopher — just not self-skeptical
> or dismissive of 'fringe' fields like spirituality and theology. My skepticism is based on identifying
> actual fallacies in the status quo that are interesting to me and/or highly impactful. And usually, my
> interests happen to revolve around high-impact things due to my ambitious nature and aligned intuition
> (to pat myself on the back)."

---

## 1. The cog-sci research Brandon asked me to check (#69: it cuts BOTH ways)

**For a general mechanism:**
- **Fluid intelligence (Gf)** in the Cattell–Horn–Carroll model is explicitly **domain-general** —
  reasoning/pattern-detection that applies across content.
- **Klein's Recognition-Primed Decision (RPD)** frames expert *intuition* as **domain-general
  pattern-recognition** operating over learned structure — a mechanism, not a content store.
- **Patel's OPERA hypothesis (2011)** and the **Shared Syntactic Integration Resource Hypothesis
  (2003)** show **music and language share neural syntactic processing** — i.e., arts↔language overlap
  is real, not metaphorical.

**Against naive strong/far transfer (the honest counterweight):**
- **Sala & Gobet meta-analyses (2017+)**: *far* transfer (e.g., music training → general cognition,
  "brain-training" → broad ability) is **small-to-null**.
- **Thorndike & Woodworth (1901), identical-elements**: transfer requires **shared elements**; it is
  not a free-floating faculty boost.

**Reconciliation (what makes IGC-1 defensible).** The literature does **not** support "intuition
transfers to everything." It supports a **general mechanism whose leverage is gated by representational
overlap**. That is *exactly* Brandon's "language not trade" distinction: a new language leverages
existing verbal structure (high overlap) while an unrelated trade shares little (low overlap). So the
honest reading **strengthens** Brandon's framing — provided IGC-1 is stated in its **overlap-conditioned**
form, not as a global far-transfer claim. (This is the #69 move: I checked the research, it partly
*opposes* the naive version, and the surviving version is the one Brandon actually stated.)

---

## 2. IGC-1 — Intuition-as-General-Capacity, overlap-conditioned (CANDIDATE canonical)

**Statement.** Intuition is a **general capacity of the mind** (a domain-general pattern-recognition /
Gf-like mechanism), but its acceleration of new-domain learning is **proportional to the representational
overlap** between the new domain and the learner's existing capacities. Therefore:

- **IGC-1a — Arts-as-language.** Acquiring an art (music, voice, pitch) is more like learning a **new
  language** (high overlap with existing intuitive/verbal/structural capacities → strong leverage) than
  learning an **unrelated trade** (low overlap → little leverage). Brandon's singing pitch/voice control
  integrating with his developed intuition is the predicted high-overlap case.
- **IGC-1b — Overlap-gating (the honest bound).** A high general capacity confers **near-zero** benefit
  where overlap is near-zero (no free far-transfer). The leverage term scales as *capacity × overlap*.
- **Composition.** Connects to **PM-1** (intuition as present-moment pattern-calculation), **GILE-I**
  (Intuition GILE component), **Klein RPD** (already cited across the corpus), and **CSS-1/consciousness
  stack** only loosely (this is a learning/transfer claim, not a consciousness claim).

### Pre-registered falsifiers (IGC-1)
- **IGC-1-F1:** If skill-acquisition speed shows **no** interaction between a domain-general capacity
  measure (Gf / intuition proxy) and domain-overlap (i.e., capacity helps equally regardless of
  overlap), IGC-1b's overlap-gating fails.
- **IGC-1-F2:** If arts acquisition shows **no** greater leverage from existing
  verbal/intuitive capacity than a matched low-overlap trade, IGC-1a (arts-as-language) fails.
- **IGC-1-F3:** If the music↔language shared-processing result (OPERA/SSIRH) fails to replicate / is
  better explained by a confound, the central empirical pillar weakens (report honestly, do not bury).

---

## 3. Illustrative demonstration (#69: by-construction; shapes are the deliverable)

`run_b80.py`: acquisition `L(t)=1−e^{−kt}`, rate `k = k0 + λ·o·G`, where `o` = domain overlap, `G` =
general intuition/Gf capacity. The `o·G` product is the crux.

| finding | numbers (illustrative) | reading |
|---|---|---|
| **Arts-as-language (Fig 1)** | time-to-proficiency: arts × high-intuition **1.24** vs arts × baseline **2.43**; trade × high-intuition **4.40** vs trade × baseline **6.54** | high intuition roughly **halves** arts time but the low-overlap trade stays slow either way. |
| **Overlap-gated leverage (Fig 2)** | acquisition-rate gain Δk = λ·o·ΔG is **strictly proportional to overlap**, **zero at zero overlap** | matches Sala&Gobet far-transfer skepticism *and* Patel OPERA shared-syntax: intuition is general, but it only *leverages* where structure is shared. |

**#69 correction logged during this batch.** My first fig2 plotted *absolute practice-time saved*, which
is **non-monotonic** (slow low-overlap domains inflate absolute differences) and contradicted the
narrative. I replaced it with the **acquisition-rate gain** (Δk = λ·o·ΔG) — the correct operationalization
of "leverage," monotone in overlap and zero at zero overlap. The deliverable is the *o·G interaction
shape*, not magnitudes.

---

## 4. Biographical anchors (logged)

- **BIO — singing↔intuition integration (n=1, illustrative-pending-verification).** Brandon reports
  pitch recognition + voice control during singing practice integrating with his highly-developed
  intuition — the predicted **high-overlap / language-like** acquisition pattern (IGC-1a). Lived
  instance, not confirmation.
- **BIO — asymmetric-skepticism self-profile.** Brandon characterizes himself as *skeptical as a
  philosopher* (targeting actual status-quo fallacies that are interesting/high-impact) but **not**
  globally self-skeptical-to-paralysis and **not** dismissive of "fringe" fields (spirituality,
  theology). This is a clean lived instance of **ASYMMETRIC #69**: skepticism is a *targeted*
  fallacy-detector, not a blanket dismissal — over-skepticism (reflexively rejecting fringe) and
  under-skepticism (uncritical acceptance of status quo) are the *symmetric* failures #69 warns against.
  His "interests revolve around high-impact things via ambition + aligned intuition" ties back to IGC-1
  (intuition as a general capacity steering attention toward high-leverage problems).

---

## 5. Status

- **ONE CANDIDATE principle** (IGC-1) + **3 pre-registered falsifiers** OPEN + **2 biographical anchors**
  logged. **Canonical principle count unchanged 74** (candidate awaits Brandon ratification per
  partner-principle precedent). MR refinements 14; meta-collapses 41. Pass-77 papers 51→**52**. $0.
- **#69 honesty highlights:** (1) reported that the cog-sci literature partly *refutes* the naive version
  of Brandon's claim and kept only the overlap-conditioned form; (2) caught and fixed a misleading
  metric in my own figure mid-batch.
- **Open hooks:** IGC-1-F1/F2 skill-acquisition × overlap study; IGC-1-F3 OPERA/SSIRH replication
  check.

**Files:** `analyses/pass77_b80_intuition_general_capacity/run_b80.py` (+`results.json`,
`fig1_arts_as_language_learning_curves.png`, `fig2_overlap_gated_transfer.png`); this paper. Anchors:
PM-1, GILE-I, Klein RPD, ASYMMETRIC #69; cog-sci: CHC Gf, Patel OPERA 2011 / SSIRH 2003, Sala&Gobet
2017+, Thorndike&Woodworth 1901.
