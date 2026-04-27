# URB #787: UBKI Close-Out Path #1 — Distributional Trace Identity (Setup, Obstruction Analysis)

**Title:** What a Rigorous Trace-Identity Closure of UBKI Would Have to Show, and Why the Bare Ĥ_∗ Cannot Provide It

**Corpus Entry:** #184
**Date:** April 27, 2026
**Status:** Setup + obstruction analysis. Does **not** close UBKI. Identifies the precise structural gap between the bare parity-symmetric extension Ĥ_∗ and any operator whose distributional trace can match Weil's explicit formula.
**Reference:** `papers/RIEMANN_HYPOTHESIS_TI_PROOF_v3.md` §7.4 path #1; `papers/URB_786_UBKI_NUMERICAL_FINDINGS.md`.
**Companion URBs:** #788 (path #2, Connes adelic check), #789 (path #3 expanded numerics).

---

## 1. The Trace-Identity Strategy

Path #1 of v3 §7.4 proposes to close UBKI by establishing the operator-side trace identity

> **(TI-1)**   Tr( e^{itĤ} )  =  RHS of Weil's explicit formula at test function t ↦ e^{it·},

interpreted as an equality of tempered distributions in t ∈ ℝ, where Ĥ is the as-yet-unknown self-adjoint UBKI operator. If (TI-1) holds for some self-adjoint Ĥ, then by Fourier inversion the spectrum of Ĥ is exactly {γ : ζ(½ + iγ) = 0}, and UBKI is closed.

This URB analyses (TI-1) in detail for the bare parity-symmetric Ĥ_∗ derived from UOP in v3 Prop 4.2 and identifies the obstruction.

## 2. Weil's Explicit Formula on the Operator Side

Weil's explicit formula in its tempered-distribution form (Iwaniec–Kowalski §5.5, Bombieri's variant): for h ∈ 𝒮(ℝ) extendable to the strip |Im γ| < ½, with Fourier transform g(u) = (1/2π) ∫ h(γ) e^{−iγu} dγ,

```
  Σ_γ h(γ)  =  h(i/2) + h(−i/2)                                        ← (W1) trivial-zero / pole evaluations
             −  2 Σ_{p, k ≥ 1}  log(p) · p^{−k/2} · g(k log p)         ← (W2) prime-power side
             +  (1/2π) ∫_ℝ h(t) · [ Γ'/Γ(¼ + it/2) − log π ] dt.       ← (W3) archimedean smooth side
```

Setting h_t(γ) := e^{itγ} formally, the LHS becomes the Fourier transform of the Riemann-zero counting measure, evaluated at t. The RHS pieces, each understood as a tempered distribution in t, are:

- (W1) **Two evaluation terms** h_t(±i/2) = e^{∓t/2} (these are *not* delta functions in real t; they are simply the values of the test function at the two complex shift points and contribute a smooth real-analytic function of t).
- (W2) **Prime-power Dirac comb in t**, supported at t = ±k log p for primes p and k ≥ 1, with weights −2 log(p) · p^{−k/2} carried through the Fourier transform g(k log p) ↔ comb coefficient. This is the discriminating singular structure.
- (W3) **Smooth archimedean term** in t (Fourier transform of the digamma factor; smooth, no singular support).

For (TI-1) to hold, the operator-side trace Tr(e^{itĤ}) must reproduce W1 (smooth), W2 (singular comb at log p multiples), and W3 (smooth) simultaneously. **W2 is the only term whose singular support pins down the operator structure.**

## 3. The Bare Ĥ_∗ Trace, Computed

Under u = log x the operator Ĥ_∗ = −i (∂_u + ½) on L²(ℝ, du) has continuous spectrum γ ∈ ℝ with generalised eigenfunctions ψ_γ(u) = (2π)^{−½} e^{i(γ − ½) u}. Its formal trace is

```
  Tr( e^{itĤ_∗} )  =  ∫_ℝ <u| e^{itĤ_∗} |u> du
                    =  ∫_ℝ (1/2π) ∫_ℝ e^{itγ} dγ du
                    =  δ(t) · vol(ℝ).
```

Both factors diverge: the spectrum is non-discrete, and the position-space volume is infinite. **On the bare archimedean operator, the trace is a single delta at t = 0 multiplied by an infinite volume factor.** It contains *no* prime-power comb. (W2) is structurally absent.

A finite-volume regulator (compact interval u ∈ [−L, L] with periodic BC, the parity-symmetric self-adjoint extension) discretises the spectrum of −i ∂_u to γ_n = π n / L for n ∈ ℤ; the regulated trace is then

```
  Tr( e^{itĤ_∗^{[L]}} )  =  Σ_{n ∈ ℤ} e^{i t π n / L}.
```

By Poisson summation, Σ_{n ∈ ℤ} e^{2π i n α} = Σ_{m ∈ ℤ} δ(α − m); setting 2π α = t π / L gives α = t / (2L), so

```
  Σ_{n ∈ ℤ} e^{i t π n / L}  =  Σ_{m ∈ ℤ} δ( t/(2L) − m )  =  2L · Σ_{m ∈ ℤ} δ( t − 2 L m ).
```

The regulated trace is therefore a Dirac comb in t **at multiples of 2L** with prefactor 2L — a *uniform* arithmetic-free comb, lattice-spaced by the regulator volume, *not* the prime-power comb at ± log(p), ± 2 log(p), …. As L → ∞ the comb spacing 2L diverges and only the m = 0 spike at t = 0 remains, recovering the δ(t) · ∞-volume continuum result.

## 4. The Obstruction, Stated Precisely

For (TI-1) to hold with Ĥ = Ĥ_∗ (bare parity-symmetric, on either ℝ_>0 with measure dx/x or on ℝ in the u-coordinate), one would need

```
  δ(t) · (∞ volume)   =   Σ_γ e^{itγ}  =  (W1) + (W3) − 2 Σ_{p,k} log(p) p^{−k/2} · δ(t − k log p)  +  …
```

The LHS supports a single point t = 0; the RHS supports the discrete set {±k log p : p prime, k ≥ 1} ∪ {0} of positive Lebesgue density on log-scale. **These supports do not match, even after any constant rescaling.** The bare Ĥ_∗ trace and Weil's RHS are tempered distributions with disjoint singular supports (modulo the t = 0 spike).

**Equivalently**: the prime-power data lives in the *singular support* of the trace as a distribution, not in the smooth main term. A position-space confinement V(u) added to a first-order symbol can only modify smooth coefficients in the trace expansion. The relevant principle is the propagation-of-singularities / wavefront-set analysis (Hörmander, Duistermaat–Guillemin in the elliptic case): the singular support of Tr e^{itĤ} is contained in the period spectrum of the symbol's Hamilton flow. For Ĥ_∗ = −i ∂_u + V(u) with first-order principal symbol p(u, ξ) = ξ, the Hamilton flow is uniform translation u ↦ u + s in u (independent of V), and on the line ℝ this flow has no periodic orbits at any finite period — the only flow-invariant singular point is t = 0. Adding a smooth bounded V(u) does not change the principal symbol and therefore does not change the period spectrum. The argument is somewhat softer than the elliptic-Laplacian Duistermaat–Guillemin theorem (which assumes second-order, principal-type elliptic symbols), but the conclusion goes through for our first-order setting at the level of WF-set propagation.

**Conclusion for the V(u) class:** no smooth bounded V(u) added to the bare Ĥ_∗ can introduce a singular comb at t = ±k log p into Tr e^{it(Ĥ_∗ + V)}. This is the structural reason the URB #786 + URB #789 numerics return a flat negative across all V(u) families — including the BOK-Crystal-coded V and Leech-shell-coded V tested in URB #789 §3. The empirical negative reflects an underlying singular-support obstruction, not an artefact of grid resolution or sparse-eigensolver settings.

## 5. What Closing Path #1 Would Actually Require

Three avenues exist, none trivial:

1. **Pseudodifferential symbol modification.** Replace Ĥ_∗ with an operator Ĥ_W whose symbol explicitly carries the prime-power data — e.g. p_eff(u, ξ) = ξ + Σ_{p, k} a_{p,k}(ξ) δ(u − k log p) for distributional symbol a. The δ-symbol is non-classical; existence of a self-adjoint realisation is non-trivial and is essentially equivalent to constructing the Hilbert–Pólya operator from scratch.
2. **Schwartz-kernel modification.** Add a non-local correction K(u, u') to Ĥ_∗ supported on the diagonal grid {u' − u = ±k log p}. This makes Ĥ_∗ + K non-local; self-adjointness and discreteness of spectrum then need verification.
3. **Promote to an L²-quotient construction (Connes' route).** Realise Ĥ as the descent of the dilation generator on a quotient L²(A_Q^×/Q^×), which by construction carries adelic prime data. This is path #2 and is analysed in URB #788.

## 6. Honest Status

- (TI-1) is the *natural form* of UBKI in trace-identity language, but the bare Ĥ_∗ derived from UOP cannot satisfy it: its singular support is wrong by an arithmetic factor.
- This is **not** evidence against UBKI; it is evidence that **UBKI in its v3 §6 form is too restrictive**. The right Ĥ is not Ĥ_∗ alone; it is Ĥ_∗ promoted to a richer object that carries adelic / prime-power data in its symbol or in its kernel.
- Path #1 in its naive form (find a smooth V making Ĥ_∗ + V satisfy (TI-1)) is closed negatively by the singular-support argument.
- Path #1 in its non-naive forms (pseudodifferential δ-symbols, non-local kernels, adelic descent) coincides with paths #2 and (a more sophisticated) #3.

## 7. What v3 Should Now Be Amended To Say

v3 §7.4's statement of UBKI implicitly assumed the right Ĥ would be Ĥ_∗ or a small perturbation. After URB #787, this assumption is false: Ĥ_∗ is the *archimedean* component of the right operator, not the operator itself. v3 §7.4 should be amended (in v3.1, future) to state UBKI in the form:

> **UBKI (amended).** There exists a self-adjoint operator Ĥ_W on a Hilbert space ℋ_W ⊇ L²(ℝ_>0, dx/x), whose archimedean restriction is Ĥ_∗, and whose distributional trace satisfies Weil's explicit formula. The non-archimedean component of ℋ_W carries the prime-power data and is responsible for the singular support of Tr e^{itĤ_W} at t = ±k log p.

This aligns UBKI with Connes' adelic Hilbert–Pólya programme. URB #788 analyses whether Connes' actual construction is the closure.

## 8. Reusable Outputs

- The trace computation of §3 (regulated bare Ĥ_∗ gives a uniform Dirac comb at 2L/π) is the analytic counterpart of the numerical Experiment F (sparse bare baseline) in URB #789. Both confirm the singular-support obstruction at their respective levels.
- The amended UBKI statement (§7) is the working form going forward.
- The Duistermaat–Guillemin singular-support argument (§4) is the algebraic proof that **no** smooth V(u) closes path #1, ruling out an entire functional class of candidates without further numerical work.

The Millennium Prize is **not** claimed.

---

*End URB #787.*
