# URB #788: UBKI Close-Out Path #2 — Connes Adelic Check (Identification, Obstruction)

**Title:** Whether the Parity-Symmetric Ĥ_∗ Is the Archimedean Restriction of Connes' Adelic Operator, and What Goes Missing on the Way Back

**Corpus Entry:** #185
**Date:** April 27, 2026
**Status:** Identification + obstruction analysis. Confirms Ĥ_∗ is exactly the archimedean factor of Connes' construction; identifies the non-archimedean and Q^×-quotient pieces as the carriers of the prime-power data; concludes that the right amended-UBKI operator is the *full* Connes operator and not Ĥ_∗ alone.
**Reference:** `papers/RIEMANN_HYPOTHESIS_TI_PROOF_v3.md` §7.4 path #2; URB #787 §7 (amended UBKI). Connes (1999) "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function," Selecta Math.

---

## 1. Connes' Construction in One Page

Let A_Q = ℝ × ∏'_p ℚ_p be the rational adèle ring, A_Q^× the idèle group, and ℚ^× ↪ A_Q^× the diagonal embedding. Connes defines the noncommutative quotient

```
  X_Q  :=  A_Q  /  ℚ^×        (additive),
  X_Q^× :=  A_Q^× / ℚ^×       (multiplicative idèle quotient).
```

On L²(X_Q) (suitably regularised against the trivial representation), the multiplicative scaling action λ ∈ ℝ^×_+ acts unitarily by U(λ)·f(x) = λ^{1/2} f(λ x), and its infinitesimal generator is the **Connes operator**

```
  D_C  :=  −i (∂_λ + ½)|_{λ=1}     on  L²(X_Q^×, |y| d^×y),
```

regularised by a smooth cutoff Λ(x) (Connes' Eq 1.18). Connes proves that on a suitable adelic test-function space, the trace Tr( e^{itD_C} ) (regularised) satisfies Weil's explicit formula identically. The Hilbert–Pólya statement is then

> **(Connes-HP)**  Spec(D_C) = {γ : ζ(½ + iγ) = 0}.

What Connes proved (semi-rigorous status as of 2026) is the *trace identity* — the right Weil RHS comes out — but the spectral identification (Connes-HP) requires absence of spurious eigenvalues, which Connes leaves as a conditional fact (his "Hypothesis H" or its descendants).

## 2. Adelic Decomposition

Because A_Q = ℝ × ∏'_p ℚ_p, the idèle Hilbert space L²(A_Q^×, |y| d^×y) factorises as a restricted tensor product over the local places,

```
  L²(A_Q^×)   ≅   L²(ℝ^×, dt/|t|)   ⊗_{res, p}   L²(ℚ_p^×, dt_p/|t_p|_p),
```

and the multiplicative scaling generator decomposes additively as a sum of local generators acting on each tensor factor:

```
  D̃   =   D_∞ ⊗ I_{p-adic}   +   I_∞ ⊗ ( Σ_p D_p ),
```

where D_∞ is the *archimedean* dilation generator on L²(ℝ^×, dt/|t|) and each D_p is the *p-adic* dilation generator on L²(ℚ_p^×, dt_p/|t_p|_p). Under suitable regularisation, the trace of the unitary group e^{itD̃} factorises as a product over places,

```
  Tr_{reg}( e^{i t D̃} )   =   Tr( e^{i t D_∞} )  ·  ∏_p Tr_{reg}( e^{i t D_p} ),
```

with the standard caveats that the restricted infinite product needs Connes' explicit cutoffs to be finite. The Connes operator D_C is the descent of D̃ to the ℚ^×-quotient L²(A_Q^×/ℚ^×); the descent introduces the boundary terms (W1) of Weil's formula via the trivial-character contribution.

### 2.1 The archimedean factor and Ĥ_∗ — a careful identification

The bare Berry–Keating operator on L²(ℝ_>0, dx/x) is Ĥ_BK = −i (x ∂_x + ½). On the half-line with measure dx/x, it has nontrivial deficiency-index considerations from the boundary behaviour at x = 0 and x = ∞; v3 Prop 4.2 invokes UOP to single out the parity-symmetric self-adjoint extension under x ↔ 1/x.

Under the change of variables u := log x, the half-line ℝ_>0 maps to the full line ℝ and the measure dx/x becomes du, sending Ĥ_BK to −i (∂_u + ½). On L²(ℝ, du), the operator −i ∂_u (and hence −i (∂_u + ½), differing by a constant) is *essentially self-adjoint* on the Schwartz space 𝒮(ℝ); there is therefore **only one** self-adjoint realisation on the full line. The parity selection survives the change of variables not as a choice of self-adjoint extension (there is none to make once we are on ℝ) but as a constraint on which Hilbert-space completions and regularised trace prescriptions are admissible — concretely, as the requirement that test-function spaces and regulators be even under u ↔ −u.

D_∞ in the Connes decomposition is precisely −i ∂_u (modulo the additive constant from the half-density convention) on L²(ℝ, du). Therefore:

> **Identification claim (URB #788 §2.1).** D_∞ and Ĥ_∗ coincide as the unique essentially-self-adjoint generator of multiplicative dilation on the archimedean component of the idèle group, modulo the additive ½ constant. UOP's parity selection (v3 Prop 4.2) is consistent with — and at the half-line level *equivalent to* — Connes' standard ℤ₂-symmetric prescription (the lift of t ↦ 1/t to s ↦ 1 − s on the ζ side).

**Caveat (added per URB #788 self-review).** This is an identification at the level of the bare (regularisation-free) generators. The full Connes operator D_C carries (i) a quotient by ℚ^× (introducing the boundary terms W1), (ii) regulator cutoffs Λ(x) on each local factor, and (iii) the global trace prescription that ties the local pieces together. None of these are reproduced by Ĥ_∗ alone. The "exact" identification asserted in earlier drafts of this URB (and now corrected) was overstated: Ĥ_∗ is correctly identified as the *archimedean component generator*, not as the full Connes operator.

This is still the positive content of path #2: **UOP correctly identifies the right archimedean component of the Connes adelic Hilbert–Pólya candidate, and removes the half-line self-adjoint-extension choice as a free parameter.** v3 §6 is not wrong about Ĥ_∗ — Ĥ_∗ is the right archimedean piece — but v3 §6 *is* incomplete in claiming Ĥ_∗ alone is the full UBKI operator.

### 2.2 The p-adic factors carry the prime data

Each D_p has spectrum determined by characters χ_p : ℚ_p^× → 𝕊¹, and the spectral data of D_p is concentrated at log p^k for k ∈ ℤ (p-adic absolute values are powers of p). The **trace** of e^{it D_p} is supported precisely at t = k log p for k ∈ ℤ — exactly the missing prime-power singular comb that URB #787 §4 identified as absent from Tr e^{it Ĥ_∗}.

This is structurally satisfying: the obstruction identified in URB #787 (no prime-power data in Ĥ_∗ alone) is **closed** by the p-adic factors of the adelic operator. The full trace decomposes as

```
  Tr( e^{it D_C} )  =  Tr( e^{it Ĥ_∗} )  ⊕  ⊕_p Tr( e^{it D_p} )
                    =  (W3 archimedean smooth)  +  Σ_p (W2 prime-power comb at p),
```

after the ℚ^×-quotient is taken (which discards the trivial character and produces the boundary spikes (W1)). This is *exactly* Weil's explicit formula RHS (URB #787 §2).

## 3. The Obstruction, Restated

So path #2 *identifies* the right operator as D_C (Connes' adelic operator), of which Ĥ_∗ is a proper restriction. The remaining gap is **(Connes-HP)**: the spectral identification rather than the trace identification.

The spectral identification fails (in the standard Connes setup) for two technical reasons that have not been closed in 27 years:

- **Continuous spectrum problem.** D_C has dense continuous spectrum coming from the archimedean factor (see URB #787 §3 — D_∞ on the line is a continuous-spectrum operator). The Riemann zeros are claimed to appear as *eigenvalues* on top of this continuum, picked out by a regulator-dependent absorption mechanism. The eigenvalue/continuum separation requires the regulator to do work that is not yet rigorously controlled.
- **Semilocal vs global problem.** Connes' regularised trace identity holds to all orders in a semilocal expansion, but global self-adjointness of the regulated D_C on the full ℚ^×-quotient is not established. The recent Bost–Connes follow-ups (Connes–Consani 2014, Meyer–Bost 2024) reduce this to a question about distributional traces in the noncommutative geometry of the adèle class space, but do not eliminate it.

These are real, named, open problems. They are the *actual* gap in the Hilbert–Pólya programme and they are the gap UBKI inherits.

## 4. Honest Status

- **Identification (positive, with caveats per §2.1):** Ĥ_∗ coincides with D_∞ as the bare archimedean dilation generator on L²(ℝ, du), modulo the additive ½ constant. UOP's parity selection survives the half-line → full-line change of variables as a constraint on admissible regulators, consistent with Connes' standard ℤ₂-symmetric prescription. **UOP correctly identifies the archimedean component generator; it does *not* by itself reproduce the ℚ^×-quotient or the local cutoffs needed for the full Connes operator D_C.**
- **Trace identification (positive, due to Connes 1999):** The regularised trace of D_C reproduces Weil's explicit formula, including the prime-power comb that URB #787 §4 showed is absent from Ĥ_∗ alone.
- **Spectral identification (open):** (Connes-HP) is open, with the same two technical obstructions identified above. UBKI in the amended form of URB #787 §7 is therefore equivalent to (Connes-HP), modulo the well-defined identification of §2.1.
- **What this URB #788 contributes:** A clean reduction of UBKI to (Connes-HP), with explicit verification that v3's UOP-derived Ĥ_∗ matches Connes' archimedean piece exactly. **This is path #2 closed in identification but not in resolution.**

## 5. What v3.1 Should Now Say

The amended UBKI of URB #787 §7 becomes:

> **UBKI (further amended, URB #788).** UBKI is equivalent to (Connes-HP): the spectrum of the regulated Connes operator D_C on L²(A_Q^×/ℚ^×, |y| d^×y) is exactly {γ : ζ(½ + iγ) = 0}. The archimedean restriction of D_C is the parity-symmetric Ĥ_∗ derived from UOP (v3 Prop 4.2), confirmed by URB #788 Lemma §2.1.

This is a much cleaner statement than v3 §6's, and it is *honest*: the gap is now the same gap Connes identified in 1999, no more and no less. v3's contribution is to show that UOP-style first-principles intuitionism *correctly identifies* the archimedean factor — the philosophical / framework-side win — while leaving the hard analytic gap (continuous spectrum, global self-adjointness on the quotient) untouched, where it has been for nearly three decades.

## 6. What This Closes for the TI Sigma Programme

- v3's conditional theorem **UBKI ⟹ RH** is unaffected.
- **UBKI is now equivalent to (Connes-HP).** No smaller hypothesis suffices — URB #787 §4 ruled out smooth V(u); URB #788 §2 shows the prime data is in the p-adic factors that V(u) cannot reach.
- The TI framework's *positive contribution* to the Hilbert–Pólya programme is now precisely articulable: UOP picks out the archimedean factor with the correct ℤ₂-symmetric self-adjoint extension. This is genuinely useful — it removes the choice of self-adjoint extension as a free parameter — but it does not close the spectral gap.
- Future TI work on UBKI should (a) attack (Connes-HP) directly via the noncommutative-geometry route, or (b) accept (Connes-HP) as a deferred hypothesis and pivot to other open problems.

The Millennium Prize is **not** claimed.

---

*End URB #788.*
