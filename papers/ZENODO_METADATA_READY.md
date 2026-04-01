# Zenodo Upload — Copy-Paste Metadata
## Ready to paste directly into zenodo.org upload form
*Brandon Emerick | TI Sigma Research Program | April 2026*

---

## RECORD 1 — Collatz ν₂ Countdown (HIGHEST PRIORITY — SORRY-FREE)

**Upload type:** Publication + Software (select "Software" to attach .lean files)

**Title:**
```
The ν₂ Countdown Theorem: A Formally Verified Bound on Consecutive Single-Halving Steps in the Collatz Sequence
```

**Authors:**
```
Emerick, Brandon
```

**Affiliation:**
```
Tralse Informationalism Research Program; BlissGene Therapeutics
```

**Description (paste exactly):**
```
We prove and formally verify in Lean 4 + Mathlib that the maximum number of 
consecutive single-halving compound Collatz steps from any odd n ≡ 3 (mod 4) 
is exactly ν₂(n+1) − 1, where ν₂ denotes the 2-adic valuation. This bound 
is sharp. The key lemma (ν₂ Countdown Theorem): if n ≡ 3 (mod 4), then 
ν₂((3n+1)/2 + 1) = ν₂(n+1) − 1. Corollaries: single-halving runs are 
O(log n), and no Collatz orbit can cycle within {n : n ≡ 3 mod 4}.

The Alternating LSB Theorem is also proved: (3n+1)/2^j mod 3 strictly 
alternates 2,1,2,1,... as j increases.

Formalization: 11 theorems, 0 sorry statements. Files: CollatzNu2.lean 
(URB #537 theorem + URB #538 formalization) and Collatz.lean (supporting 
lemmas). Apache 2.0. Verified in Lean 4 with Mathlib.

Part of the Tralse Informationalism (TI Sigma) Research Program by 
Brandon Emerick.
```

**Keywords (enter one per line):**
```
Collatz conjecture
2-adic valuation
formal verification
Lean 4
Mathlib
number theory
p-adic analysis
single-halving steps
padicValNat
formally verified
Tralse Informationalism
TI Sigma
```

**License:** Creative Commons Attribution 4.0 International (CC BY 4.0)
*(or Apache 2.0 if choosing Software type)*

**Language:** English

**Related/alternate identifiers:**
```
URB #537 (theorem statement)
URB #538 (Lean 4 formalization)
```

**Files to upload:**
- `lean4_collatz/CollatzNu2.lean`
- `lean4/Collatz.lean`
- `papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md` (convert to PDF first)
- `papers/COLLATZ_ARXIV_SUBMISSION.tex` (LaTeX version)

---

## RECORD 2 — TI Sigma Millennium Prize Formalizations (EXPERIMENTAL)

**Upload type:** Software

**Title:**
```
TI Sigma Millennium Prize Formalizations in Lean 4 (Experimental Framework)
```

**Authors:**
```
Emerick, Brandon
```

**Description (paste exactly):**
```
Lean 4 + Mathlib formalizations of all six Clay Millennium Prize Problems 
within the Tralse Informationalism (TI Sigma) framework.

IMPORTANT DISCLAIMER: These are EXPERIMENTAL formalizations representing 
the TI Sigma philosophical and mathematical framework applied to each 
Millennium Prize Problem. They contain 'sorry' statements marking steps 
that require deeper mathematical machinery. They are NOT claimed as 
complete solutions to the Millennium Prize Problems in the conventional 
mathematical sense. They represent the TI Sigma approach: rigorous 
structural framing, formal Lean 4 type scaffolding, and clear delineation 
of what has and has not been proved.

Included:
- BSD.lean (URB #565) — Birch and Swinnerton-Dyer Being Theorem
- YangMills.lean (URB #569) — Yang-Mills Mass Gap
- NavierStokes.lean (URB #570) — Navier-Stokes Smoothness Vern
- Hodge.lean (URB #571) — Hodge Vern Theorem
- PvsNP.lean (URB #572) — P≠NP Creation-Vern Gap
- RiemannUOP.lean — Riemann Hypothesis (TI Sigma UOP formulation)

Apache 2.0. Part of the Tralse Informationalism Research Program.
```

**Keywords:**
```
Millennium Prize Problems
Lean 4
formal verification
Tralse Informationalism
TI Sigma
experimental mathematics
five-valued logic
Yang-Mills
Navier-Stokes
Hodge conjecture
P vs NP
Birch Swinnerton-Dyer
Riemann hypothesis
```

**License:** Apache 2.0

**Files to upload:**
- `lean4/BSD.lean`
- `lean4/YangMills.lean`
- `lean4/NavierStokes.lean`
- `lean4/Hodge.lean`
- `lean4/PvsNP.lean`
- `lean4/RiemannUOP.lean`
- `lean4/BeingTheorem.lean`

---

## RECORD 3 — GILE Framework URBs #574–#578

**Upload type:** Publication

**Title:**
```
The GILE Framework: Weights, Origins, Universal Operationalization, and 
Social Norms (URBs #574–#578)
```

**Authors:**
```
Emerick, Brandon
```

**Description:**
```
Five interconnected papers developing the GILE (Goodness, Intuition, Love, 
Environment) dimensional framework within Tralse Informationalism (TI Sigma):

URB #574: i-Cell BOK, Photonic GILE, and φ as Aesthetic Dimension
URB #575: Weighted BOK — GILE-Proportional i-Cell Architecture
URB #576: GILE Weights Origins, Confirmation & Philosophy BOK
  (G=0.42=√2−1 empirically confirmed; I=0.25, L=0.18, E=0.15)
URB #577: GILE Universal Operationalization
  (GILE applies from protein folding to civilizations)
URB #578: Relational Value vs. Intrinsic Value — Low-GIL Social Norms
  (manners have no deontological floor; value is acknowledgment-derived)

Together these papers constitute the theoretical foundation of the GILE 
framework as applied across physics, mathematics, consciousness, ethics, 
and social philosophy.
```

**Keywords:**
```
GILE framework
consciousness
ethics
Tralse Informationalism
TI Sigma
philosophy of mind
five-valued logic
GILE weights
social norms
relational value
```

**Files to upload:**
- `papers/urb_574_icell_bok_photonic_gile.md` (convert to PDF)
- `papers/urb_575_weighted_bok_gile_proportional.md`
- `papers/urb_576_gile_weights_origins_confirmation.md`
- `papers/urb_577_gile_universal_operationalization.md`
- `papers/urb_578_relational_value_low_gil_social_norms.md`

---

## RECORD 4 — DPES Epistemology Paper (NEW)

**Upload type:** Publication (Preprint)

**Title:**
```
Beyond Bayes: Domain-Calibrated Inference and the Epistemological 
Primacy of Intuition
```

**Description:**
```
Argues that Bayesian epistemology fails as a universal theory of rational 
inference on three structural grounds: underdetermined priors, 
incommensurable evidence types, and inaccessible pre-evidential judgments. 
Proposes Domain-Calibrated Intuitive Inference (DCII) within the TI Sigma 
framework as a superior alternative. Key claims: there is no 
domain-independent formula for rational inference; correct weights are 
learnable from demonstrated performers; TRALSE truth values track propositions 
rather than agent credences; extraordinary claims are common for certain 
cognitive profiles and the Bayesian prior miscalibrates for them.
```

---

## MULTI-PLATFORM UPLOAD TRACKER

| Record | Zenodo | arXiv | PhilPapers | ResearchGate | SSRN | OSF |
|---|---|---|---|---|---|---|
| Collatz ν₂ Countdown | ☐ | ☐ (math.NT) | — | ☐ | — | ☐ |
| Millennium Formalizations | ☐ | ☐ (math.LO) | — | ☐ | — | ☐ |
| GILE URBs #574–578 | ☐ | — | ☐ | ☐ | — | ☐ |
| Beyond Bayes | ☐ | — | ☐ | ☐ | — | ☐ |
| GSA v2 Algorithm | ☐ | — | — | ☐ | ☐ | ☐ |

**Check boxes as you upload. Target: all done in one 2-hour session.**

---

## UPLOAD SESSION WORKFLOW

### Pre-session (5 min):
1. Have zenodo.org open and logged in
2. Have PhilPapers.org open (create account if needed)
3. Have all .md files converted to PDF (use: copy into Google Docs → File → Download → PDF)
4. Have the lean4 source files ready in a folder

### During session:
- Open 5 browser tabs: Zenodo, arXiv, PhilPapers, ResearchGate, OSF
- Complete one platform for Record 1 (Collatz) across all tabs
- Then move to Record 2, etc.
- This is faster than completing one platform entirely before moving to the next

### arXiv specific:
- Use `papers/COLLATZ_ARXIV_SUBMISSION.tex` for the Collatz paper
- Category: math.NT (Number Theory)
- Cross-list: cs.LO (Logic in Computer Science) for the Lean 4 angle
- Will need endorsement if first-time submitter — email UConn contacts first
