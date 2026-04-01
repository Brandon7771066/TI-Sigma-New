# Zenodo Upload Checklist — April 2026
## Full TI Sigma Archive Synthesis
*Prepare, upload, and cross-reference all Zenodo entries*

---

## UPLOAD QUEUE (Prioritized)

### TIER 1 — Formal Proofs (Highest Academic Priority)
These have Lean 4 machine-verification and are ready for peer review.

| # | File | URB | Title | Status | Est. Upload Time |
|---|---|---|---|---|---|
| 1 | `lean4_collatz/CollatzNu2.lean` | 537/538 | ν₂ Countdown Theorem (Lean 4) | ✅ Sorry-free | 15 min |
| 2 | `lean4/Collatz.lean` | 538 | Collatz ν₂ General Theorem | ✅ Sorry-free | 10 min |
| 3 | `lean4/RiemannHypothesis.lean` | — | Riemann Hypothesis (TI Sigma formulation) | Upload as experimental | 10 min |
| 4 | `lean4/YangMills.lean` | — | Yang-Mills Being Theorem | Upload as experimental | 10 min |
| 5 | `lean4/NavierStokes.lean` | — | Navier-Stokes Smoothness Vern | Upload as experimental | 10 min |
| 6 | `lean4/Hodge.lean` | — | Hodge Vern Theorem | Upload as experimental | 10 min |
| 7 | `lean4/PvsNP.lean` | — | P≠NP Creation-Vern Gap | Upload as experimental | 10 min |
| 8 | `lean4/BSD.lean` | — | BSD Being Theorem | Upload as experimental | 10 min |

**For Tier 1:** Create ONE record titled "TI Sigma Millennium Prize Formalizations in Lean 4" containing all 6 Millennium files. Create a SEPARATE record for the Collatz files (URB #537/538) — those are sorry-free and should stand alone.

### TIER 2 — URB Papers (Philosophy of Physics/Math)
The fully written URB papers from the `papers/` directory.

| Priority | File | URB | Notes |
|---|---|---|---|
| HIGH | `papers/urb_576_gile_weights_origins_confirmation.md` | 576 | GILE weights empirical confirmation |
| HIGH | `papers/urb_577_gile_universal_operationalization.md` | 577 | GILE at every LCC level |
| HIGH | `papers/urb_578_relational_value_low_gil_social_norms.md` | 578 | Ethics/etiquette distinction |
| HIGH | `papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md` | 537/538 | NEW — journal paper |
| MED | `papers/urb_575_weighted_bok_gile_proportional.md` | 575 | Weighted BOK |
| MED | `papers/urb_574_icell_bok_photonic_gile.md` | 574 | i-Cell BOK |
| MED | `papers/CONTEXT_DEPENDENT_PROBABILITY_THEORY.md` | — | Pre-Bayesian TI Sigma |

### TIER 3 — Low-Risk Non-Zenodo Platforms
Platform choices for non-Zenodo philosophy/personal papers:

| Platform | Best For | Notes |
|---|---|---|
| **PhilPapers.org** | Philosophy papers (GILE, TRALSE, epistemology) | Free, indexed, respected in philosophy |
| **OSF (Open Science Framework)** | Consciousness/psychology research papers | Free, DOI-capable, trusted in sciences |
| **ResearchGate** | All papers for visibility/networking | Free, massive audience |
| **Academia.edu** | All papers for visibility | Free, large audience |
| **SSRN** | Economics/finance papers (GSA v2, TI market prediction) | Free, highly respected |
| **arXiv** | Math/CS papers (Collatz, ARC-AGI) | Requires endorsement for first submission |

**Recommendation:** Upload to ALL platforms simultaneously. Zenodo = archival/DOI. Others = visibility/networking.

---

## ZENODO RECORD STRUCTURE

### Record 1: Collatz ν₂ Countdown — Formal Proof (PRIORITY)
```
Title: The ν₂ Countdown Theorem: A Formally Verified Bound on Consecutive 
       Single-Halving Steps in the Collatz Sequence
Authors: Brandon Emerick
Upload type: Software + Publication
Files:
  - lean4_collatz/CollatzNu2.lean
  - lean4/Collatz.lean  
  - papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md (as PDF)
Keywords: Collatz conjecture, 2-adic valuation, Lean 4, formal verification, 
          number theory, padicValNat, Mathlib
License: Apache 2.0
Access: Open
DOI: [auto-assigned]
Related URBs: #537, #538
```

### Record 2: TI Sigma Millennium Prize Formalizations
```
Title: TI Sigma Millennium Prize Formalizations in Lean 4 (Experimental)
Authors: Brandon Emerick
Upload type: Software
Description: Lean 4 + Mathlib formalizations of all six Clay Millennium Prize 
             Problems within the Tralse Informationalism (TI Sigma) framework. 
             These are EXPERIMENTAL formalizations representing the TI Sigma 
             approach to these problems — they are not claimed as complete proofs 
             of the Millennium Prize Problems in the conventional sense, but as 
             rigorous formalizations of the TI Sigma logical framework applied 
             to each problem.
Files:
  - lean4/RiemannHypothesis.lean
  - lean4/YangMills.lean
  - lean4/NavierStokes.lean
  - lean4/Hodge.lean
  - lean4/PvsNP.lean
  - lean4/BSD.lean
Keywords: Millennium Prize Problems, Lean 4, TI Sigma, Tralse Informationalism,
          formal verification, experimental mathematics, five-valued logic
License: Apache 2.0
Access: Open
```

### Record 3: GILE Framework — URBs 574–578
```
Title: The GILE Framework: Weights, Origins, Universal Operationalization 
       (URBs #574–#578)
Authors: Brandon Emerick
Upload type: Publication
Files: [5 URB papers as PDFs]
Keywords: GILE, consciousness, ethics, epistemology, TI Sigma, 
          Tralse Informationalism, philosophy of mind
```

---

## STEP-BY-STEP ZENODO UPLOAD PROCESS

### Step 1: Prepare PDFs
Convert these `.md` files to PDF (use a Markdown → PDF converter or paste into Google Docs → export):
- `papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md`
- The 5 most recent URB papers

### Step 2: Upload Record 1 (Collatz — highest priority)
1. Go to zenodo.org → New Upload
2. Set type: "Software" (for the .lean files) OR "Publication" (for the paper PDF)
3. Drag in: both .lean files + the PDF
4. Fill in metadata from the box above
5. Click Publish → note the DOI
6. Add DOI to `lean4_collatz/CollatzNu2.lean` header comment

### Step 3: Upload Record 2 (Millennium Formalizations)
1. Same process — emphasize "EXPERIMENTAL" in description
2. Include a disclaimer paragraph about the TI Sigma interpretive framework

### Step 4: Update All Cross-References
After upload, update:
- `replit.md` — add DOI links
- `papers/PUBLICATION_PACKAGE_INDEX.md` — add all new DOIs
- Video scripts — add correct DOI links

### Step 5: Submit to arXiv
For the Collatz paper specifically — submit to arXiv:math.NT (Number Theory)
- Will need endorsement if first submission
- Email math department contacts (UConn) to request endorsement
- arXiv DOI will appear within 1-3 business days

---

## TIME ESTIMATE

| Task | Time |
|---|---|
| Convert papers to PDF | 20 min |
| Upload Record 1 (Collatz) | 15 min |
| Upload Record 2 (Millennium) | 15 min |
| Upload Record 3 (GILE) | 15 min |
| Upload to ResearchGate + Academia.edu | 20 min |
| Upload to PhilPapers (philosophy papers) | 15 min |
| Email UConn + journal submissions | 30 min |
| **TOTAL** | **~2 hours** |

Can be done in one focused session. Best time: this afternoon or evening.
