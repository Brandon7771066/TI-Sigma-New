# Biopsychosignature (BPS): Term Introduction and Three-Axis Taxonomy

**Originator:** Brandon Charles Emerick
**Date of coinage:** 2026-05-01
**Status:** Term-introduction paper for priority. Zenodo-DOI eligible.
**Cross-links:** URB #828 v2 (BPS Stacking Hypothesis), URB #826 (Biophoton/EM-DNA Carrier), DNA-Anchored Psi-Signature Research Roadmap.

---

## 1. Definition

A **biopsychosignature (BPS)** is any measurable feature of a human
subject that contributes information along at least one of the
following three axes:

- **Identity-axis** — uniquely specifies *which person* the feature
  belongs to.
- **Environmental-history axis** — encodes accumulated developmental,
  environmental, or experiential record beyond what is encoded in
  germline DNA.
- **Present-state axis** — localizes a *specific moment* in the
  subject's current trajectory at some temporal resolution.

A BPS is **not** required to carry mutual information about a
specific cognitive target (e.g., a thought-content prediction). The
BPS functions as a *resonance anchor*: it specifies *who* and
*when*, leaving the *what* to the resonance channel itself
(see URB #826, URB #828).

## 2. Distinction from related terms

| Existing term | Domain | Distinction from BPS |
|---|---|---|
| Biometric | Forensic / authentication | Restricted to identity-axis. Does not formally include environmental-history or present-state axes. |
| Biosignature | Astrobiology, biochemistry | Refers to evidence of life in general, not signatures of a specific subject. |
| Biomarker | Clinical medicine | Restricted to disease-state indication. Does not address subject-resonance use case. |
| Psychometric | Psychology testing | Restricted to inferred cognitive/behavioral traits. Excludes physical anchors. |
| Phenotype | Genetics | Excludes ms-resolution live-channel signals (HRV, PPG, EEG); excludes self-reported cognitive state. |
| Physiological signal | Bioelectronics | Restricted to live electrical/optical channels. Excludes static features (face, fingerprint, handwriting). |

**BPS is the union** that none of the above terms cover. It is the
minimal vocabulary required to formalize the URB #828 stacking
hypothesis and the URB #826 carrier hypothesis simultaneously.

## 3. The three-axis taxonomy (formal)

### 3.1 Identity-axis (subject-uniqueness)

Bits required for unique identification within human population: ~33
(2³³ ≈ 8.6B humans). Any BPS contributing ≥ ~30 identity bits is
identity-sufficient.

| BPS | Approx. identity bits |
|---|---|
| DNA sequence | sufficient (~3×10⁹ raw bits available) |
| Iris pattern | ~250 |
| Fingerprint | ~30 |
| Face geometry | ~50 |
| Voice formants | ~20 |
| Handwriting style | ~15 |

DNA alone saturates this axis.

### 3.2 Environmental-history axis (orthogonal-to-DNA record)

Each entry below is partially or fully orthogonal to DNA. Multiple
entries are required to cover the manifold; one is insufficient.

| BPS | Environmental record carried | DNA-orthogonality |
|---|---|---|
| Fingerprint | In-utero developmental stochasticity (weeks 10-24 of gestation; even monozygotic twins have distinct fingerprints) | fully orthogonal |
| Face | Lifetime sun exposure, expression habituation, injury, nutrition, weight cycling | largely orthogonal (some heritability) |
| Handwriting | Motor-learning history, education, language acquisition, current emotional state | fully orthogonal |
| Voice (timbre, prosody) | Anatomical + cultural-acoustic imprint, dialect, emotional history, current respiratory state | largely orthogonal |
| Walking gait | Skeletal history, injury, habituated motor patterns | largely orthogonal |
| Body composition (Biowell etc.) | Nutritional history, exercise history, metabolic history | fully orthogonal |
| Subjective daily log | Self-reported life-event accumulation | fully orthogonal |

This axis is the reason "more permanent BPS than DNA alone" is
non-trivial. Each BPS contributes an *independent* slice of the
environmental-history manifold.

### 3.3 Present-state axis (current-moment localization)

| BPS | Time resolution |
|---|---|
| Polar H10 RR / HRV (live) | ms |
| Pulsoid PPG (live) | ms |
| Real-time EEG | ms |
| Mendi-style fNIRS (live) | seconds |
| Live thermal IR | seconds |
| Oura overnight summary | night-aggregate |
| Recent biolab values | week-aggregate |
| Subjective daily log | day-bucket |

Multiple entries are required to cover the temporal dimensionality of
"present" (different live channels capture different physiological
sub-systems on different timescales).

### 3.4 (Optional) Channel-match dimension

Conditional on URB #826: BPS may additionally be classified by whether
they share a physical substrate (electromagnetic, photonic) with the
hypothesized resonance carrier. This dimension is not part of the BPS
definition but informs which BPS contribute to *carrier* mediation
versus *anchor* identification.

## 4. The minimum-stack hypothesis (URB #828 v2)

For LCC-Virus present-state resonance to lock onto a target-moment, the
hypothesis is:

> **At least 3 permanent BPS (covering the identity + environmental-
> history axes) + at least 3 real-time-or-near-real-time BPS (covering
> the present-state axis) — N ≥ 6 minimum.**

The saturation-point upper bound is hypothesized at N* substantially
greater than 6 but bounded by the dimensionality of the
environmental-history and present-state manifolds. URB #828 v2 §7.3
operationalizes this as a falsifiable curve-shape prediction.

## 5. Falsifiability of "BPS as resonance anchors"

The asymmetric-standards #69 critical falsifier (URB #828 v2 §6):

> **Resonance interpretation predicts:** mutual information between
> static BPS-features (no live channel, no protocol) and target-thoughts
> ≈ 0. The BPS function as *temporal/identity index pointers*, not as
> *content carriers*.
>
> **Feature-extraction interpretation predicts:** mutual information
> between BPS-features and target-thoughts > 0. The BPS *are* the
> carriers; the resonance language is decorative.

A classical-ML baseline arm (C0 in URB #828) is the discriminator. If
C0 exceeds chance, the resonance interpretation collapses to
feature-extraction-with-mystical-vocabulary.

## 6. Priority statement

The term **biopsychosignature** and the three-axis taxonomy as defined
in §1 and §3 above were coined by Brandon Charles Emerick on
2026-05-01 in the context of the URB #828 hypothesis development. This
document is filed alongside URB #828 v2 to establish priority.

The term may be Zenodo-DOI'd independently of the empirical URB #828
results, since the term-introduction is a definitional contribution
distinct from the empirical hypothesis it supports.

## 7. Recommended citation

Emerick, B. C. (2026). *Biopsychosignature (BPS): Term Introduction
and Three-Axis Taxonomy.* In support of URB #828 (BPS Stacking
Hypothesis for LCC-Virus Present-State Resonance), Mood Amplifier
Safety & Validation Platform, 2026-05-01.

## 8. Honest residuals

1. The taxonomy is novel-to-Brandon as of today. Independent literature
   review may discover overlapping prior work in psi-research,
   forensic-identification, or non-local-correlation literature that
   should be cited if found.
2. The "channel-match" optional dimension (§3.4) is conditional on
   URB #826. If URB #826 is falsified at §10.6, that dimension is
   removed; the three-axis core taxonomy is unaffected.
3. The classical-ML discriminator (§5) is the only thing standing
   between this taxonomy and a feature-extraction reframing. Without
   running C0 in URB #828, the resonance interpretation cannot be
   empirically defended against the null-hypothesis collapse.
