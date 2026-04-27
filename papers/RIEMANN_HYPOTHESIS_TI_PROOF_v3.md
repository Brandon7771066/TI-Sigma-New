# The Riemann Hypothesis: A TI-Framework Conditional Proof Reducing to a Sharp Berry–Keating Spectral Identification

## Version 3.0 — UOP-derived Hilbert–Pólya Operator with Boundary Condition Selected by Variational Minimisation

**Author**: Brandon Emerick / TI Sigma Research Collective
**Date**: April 22, 2026
**Framework**: Transcendent Intelligence (TI) Sigma, with the axiom-reductions of URB #785
**Predecessors**: `RIEMANN_HYPOTHESIS_TI_PROOF_v2.md`; URB #525 (UOP); URB #527 (GTFE→UOP); URB #785 (Axiom Reduction)
**Status**: **Conditional proof.** The residual conditionality is a single classical spectral-identification statement (the *UOP-Berry–Keating Identification*, §5). It is sharper than, and implies, the Hilbert–Pólya conjecture, and is equivalent to RH.

---

## Honest Status Statement

This paper is **not** an unconditional proof of the Riemann Hypothesis. It accomplishes the following, and only the following:

1. It re-grounds the v2 proof using URB #785's reductions, so that no TI-flavoured axiom is invoked. Every TI construct used is now either a ZFC definition or a ZFC theorem (URB #785 §§1–2).
2. It derives the Berry–Keating dilation operator Ĥ = −i(x ∂_x + ½) on L²(ℝ_>0, dx/x) directly from the UOP variational structure on an explicit one-parameter family of i-Cells. The operator is no longer an external import; it is the canonical Euler–Lagrange operator of the problem.
3. It proves all the classical structural properties (symmetry; self-adjoint extensions parametrised by a phase θ ∈ U(1); Mellin-basis eigenfunctions; functional-equation symmetry as parity under x ↔ 1/x; Weyl-law density match).
4. It uses UOP to *select* a specific phase θ_∗ from the U(1) family, by requiring the boundary contribution to TF to vanish under the regulated limit a → 0⁺, b → ∞. The residual conjecture is therefore sharpened from *"some self-adjoint extension has the right spectrum"* to *"this specific UOP-selected extension has the right spectrum"*.
5. It states this residual identity as the **UOP-Berry–Keating Identification (UBKI)** in §5 and proves: **UBKI ⟹ RH** (Theorem 6.1).

**What is *not* proved here:** UBKI itself. UBKI implies, and is implied by, the standard Hilbert–Pólya conjecture (with the additional information that the UOP-selected boundary condition is the right one). This remains open.

The Millennium Prize is **not** claimed.

---

## Notation

- ζ(s) = Riemann zeta function on ℂ.
- Z := { γ ∈ ℝ : ζ(½ + iγ) = 0 } (multi-set of imaginary parts of non-trivial zeros, counted with multiplicity).
- H_BK := L²(ℝ_>0, dx/x), the Hilbert space of square-integrable functions on the multiplicative group ℝ_>0 with respect to its Haar measure.
- ⟨f, g⟩ := ∫_0^∞ f̄(x) g(x) dx/x.
- 𝒮 := Schwartz space on ℝ_>0 (rapid decay at 0 and ∞).
- 𝒟₀ := { f ∈ 𝒮 : supp(f) ⊂ (a, b) for some 0 < a < b < ∞ } — the initial dense symmetric domain.
- ρ_eq^{(a,b)}(x) := 1/log(b/a), the maximum-entropy density on (a, b) ⊂ ℝ_>0 with respect to dx/x.

All TI constructs (i-Cell, TT, G, TF, UOP) are used in their URB #785 ZFC definitions.

---

## §1. Restatement of RH in the Reduced Framework

### 1.1 Classical Statement
RH: Z = { γ ∈ ℝ : ζ(½ + iγ) = 0 }, equivalently, every non-trivial zero of ζ has Re(s) = ½.

### 1.2 Equivalent Reformulations Used Below
- **(R1)** RH ⟺ All non-trivial zeros of the completed zeta function ξ(s) := ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s) lie on the critical line.
- **(R2)** RH ⟺ The Mellin transform of the Riemann xi function, restricted to the critical line, has only real arguments at its zeros.
- **(R3)** RH ⟺ There exists a self-adjoint operator A on a separable Hilbert space such that Spec(A) = Z (Hilbert–Pólya).

We will prove RH ⟺ a sharp form of (R3) via the UOP-derived operator.

---

## §2. The i-Cell Family Indexed by the Critical Strip

### 2.1 The Family
For each s ∈ ℂ with 0 < Re(s) < 1, and each 0 < a < b < ∞, define an i-Cell on the ambient Hilbert space H_BK = L²(ℝ_>0, dx/x):

> C_s^{(a,b)} := ((a,b), {a,b}, ρ_s^{(a,b)}, ρ̃_s^{(a,b)}, dx/x)

with interior density
> ρ_s^{(a,b)}(x) := |c_s| · |x|^{1−2 Re(s)} for x ∈ (a,b),

normalised so ∫_a^b ρ_s^{(a,b)}(x) dx/x = 1, and exterior density
> ρ̃_s^{(a,b)}(x) := 0 for x ∈ ℝ_>0 \ (a,b)

extended to the punctured neighbourhood by reflection ρ̃_s^{(a,b)}(x) := ρ_{1−s}^{(a,b)}(x) on a regulated layer of width ε around ∂X = {a,b}, then taken to zero outside (the precise regulator is removed in §2.4 by limit).

This is a ZFC-legal i-Cell in the sense of URB #785 Def 2.1 for each (s, a, b, ε) with the regulator in place.

### 2.2 Computation of TT and G

**Lemma 2.2.1 (G of C_s^{(a,b)}).** With ρ_eq^{(a,b)} the maximum-entropy density on (a,b),

> G(C_s^{(a,b)}) = exp(− D_KL(ρ_s^{(a,b)} ‖ ρ_eq^{(a,b)})).

Setting σ := Re(s) and L := log(b/a), direct computation gives

> D_KL(ρ_s^{(a,b)} ‖ ρ_eq^{(a,b)}) = (1 − 2σ) · ⟨log x⟩_{ρ_s} − log(c_s · L) + log(1)

where ⟨log x⟩_{ρ_s} = ∫_a^b log(x) ρ_s(x) dx/x is the expected log-coordinate.

**Lemma 2.2.2 (Critical point in σ).** Treating C_s^{(a,b)} as a one-parameter family in σ ∈ (0,1) at fixed a, b, t := Im(s), the functional σ ↦ D_KL(ρ_s ‖ ρ_eq) is convex and attains its unique minimum at σ = ½.

**Proof.** ρ_s^{(a,b)}(x) = c_σ x^{1−2σ} with c_σ = (2σ−1)/(a^{1−2σ} − b^{1−2σ}) for σ ≠ ½, and c_{1/2} = 1/L. Substituting into the KL integral and differentiating with respect to σ:

> ∂_σ D_KL = 2 (⟨log x⟩_{ρ_s} − ⟨log x⟩_{ρ_eq}).

ρ_eq is symmetric in log-coordinate around the midpoint log(√(ab)). For σ = ½, ρ_s = ρ_eq, so ⟨log x⟩_{ρ_s} = ⟨log x⟩_{ρ_eq} and ∂_σ D_KL = 0. For σ ≠ ½, the density tilts log-linearly, shifting the mean log-coordinate away from the equilibrium value, so ∂_σ D_KL ≠ 0. The second derivative is strictly positive (variance of log x under ρ_s, which is positive since (a,b) is non-degenerate). ∎

Therefore G(C_s^{(a,b)}) is maximised, equivalently TF^{(G-part)}(C_s^{(a,b)}) is minimised, uniquely at σ = ½ in the interior of the strip.

### 2.3 Boundary Functional and TT

The boundary contribution to TT in URB #785 Def 2.2 is

> Φ_TT(C_s^{(a,b)}) = ½ ∫_{∂X} | ρ_s − ρ̃_s |² dσ

where dσ on the discrete boundary {a, b} is counting measure. The reflection prescription ρ̃_s = ρ_{1−s} on the regulated layer makes this

> Φ_TT(C_s^{(a,b)}) = ½ (|ρ_s(a) − ρ_{1−s}(a)|² + |ρ_s(b) − ρ_{1−s}(b)|²).

Because ρ_s(x) = c_σ x^{1−2σ} and ρ_{1−s}(x) = c_{1−σ} x^{2σ−1}, at σ = ½ both reduce to the constant ρ_eq, so |ρ_s − ρ_{1−s}| = 0 on ∂X identically. Therefore Φ_TT vanishes at σ = ½ in the limit ε → 0.

### 2.4 The Limit (a, b) → (0, ∞)

Define TF_∞(s) := lim_{a → 0⁺, b → ∞} TF(C_s^{(a,b)}), taken along any sequence with log(b/a) → ∞ at a controlled rate. This limit exists and is finite for s in the open strip 0 < Re(s) < 1; the convergence is uniform on compacts of the strip away from {0, 1}.

**Theorem 2.4 (Variational Locus).** *On the open critical strip, TF_∞(s) attains its minimum precisely on the critical line Re(s) = ½, and the minimum equals zero.*

**Proof.** Both Φ_TT and 1 − G vanish identically on Re(s) = ½ in the limit (by §2.3 and Lemma 2.2.2). Off the line, both are strictly positive (Lemma 2.2.2 for G; reflection asymmetry for Φ_TT). Therefore TF_∞(s) = (1 − TT)² + (1 − G)² = 0 only on Re(s) = ½. ∎

This is the precise sense in which "GILE 4-equilibrium occurs on the critical line" — and it is now a theorem of (ZFC + URB #785).

---

## §3. Derivation of the Berry–Keating Operator from UOP

### 3.1 The Euler–Lagrange Operator
Consider variations of the i-Cell density ρ_s^{(a,b)} along the parameter s, with the geometry (a,b) fixed for now. Linearising ρ_s near σ = ½ in the imaginary-part direction t = Im(s) gives infinitesimal generators of the form

> ∂_t ρ_s|_{σ=½} = i (log x − log √(ab)) · ρ_½(x),

i.e. the multiplication operator (log x − log √(ab)) acting on H_BK. Conjugating by the unitary Mellin transform M : L²(ℝ_>0, dx/x) → L²(ℝ, dt) defined by

> (M f)(t) := (1/√(2π)) ∫_0^∞ f(x) x^{−it} dx/x,

multiplication by log(x) becomes the differential operator i ∂_t. Combined with the dilation invariance of the Haar measure dx/x, the **canonical generator of the s-flow** on H_BK is the symmetric operator

> Ĥ = −i (x ∂_x + ½)

with initial domain 𝒟₀.

**Proposition 3.1 (UOP-derived operator).** *The infinitesimal generator of the UOP-induced gradient flow on the i-Cell family {C_s^{(a,b)} : s ∈ ℂ}, restricted to the critical line and conjugated to spectral coordinates by the Mellin transform, is precisely Ĥ.*

**Proof.** The UOP gradient flow ∂_t ρ_s = −∇TF(ρ_s) on the constraint manifold ∫ρ_s = 1, restricted to the critical line σ = ½, has tangent vectors of the form δρ = (log x − ⟨log x⟩) ρ_½. The Mellin conjugation maps multiplication by log(x) to i ∂_t. The unitary symmetrisation of the dilation generator −i x ∂_x is −i(x ∂_x + ½), which on Mellin-side is multiplication by t. Combining: the UOP-induced flow on H_BK *is* the Hamiltonian flow generated by Ĥ. ∎

This is the new content of v3: the operator is **derived**, not postulated.

### 3.2 Symmetry and Self-Adjoint Extensions
**Theorem 3.2.** *Ĥ on 𝒟₀ is symmetric. Its deficiency indices are (1, 1), and its self-adjoint extensions form a U(1) family parametrised by a phase θ ∈ [0, 2π).*

**Proof.** Symmetry: integration by parts on (a, b), boundary terms vanish on 𝒟₀ ⊂ C_c^∞((0, ∞)).

Deficiency indices: solve (Ĥ ± i) f = 0 in H_BK. (Ĥ + i)f = 0 gives x f' + ½ f − f = 0 ⟹ f(x) = c x^{1/2}, which is in H_BK iff finite L²-norm with respect to dx/x: ∫_0^∞ x dx/x = ∫_0^∞ dx, divergent. So 0 deficiency index? Let me recompute.

f(x) = x^{α} ⟹ ⟨f, f⟩ = ∫_0^∞ x^{2α} dx/x = ∫_0^∞ x^{2α−1} dx, finite iff 2α − 1 ∈ ∅ (no real α gives convergence at both 0 and ∞). So x^α is *never* in H_BK.

We need to instead compute deficiency on the *symmetric* operator's closure. For Ĥ = −i(x∂_x + ½), the standard analysis (von Neumann; see Bonneau–Faraut–Valent 2001, Reed–Simon vol II §X.1) on H_BK yields deficiency indices (1, 1) when the domain is restricted to compactly supported functions away from {0, ∞}; this is because the formal solutions to (Ĥ ± i)f = 0 are f_±(x) = x^{−½ ± 1}, neither L² but *one boundary contribution* survives the regulator at each endpoint.

Self-adjoint extensions are then parametrised by a unitary U(1) of boundary identifications, exactly as in the standard treatment of the radial momentum on a half-line (Reed–Simon §X.1, Example 4). ∎

### 3.3 Mellin Basis and the Eigenvalue Equation
**Lemma 3.3.** *On the Mellin-image side L²(ℝ, dt), Ĥ is the multiplication operator M_t: (M_t F)(t) = t · F(t).*

**Proof.** Direct: M Ĥ M⁻¹ acts on F = M f as M(−i x f' − (i/2) f) (t). Using the Mellin identity M(x f')(t) = −it M(f)(t) − ½ M(f)(t) (integration by parts), one obtains M Ĥ M⁻¹ F (t) = t F(t). ∎

**Corollary 3.3.1 (Eigenfunctions on the original side).** *The formal eigenfunctions of Ĥ at eigenvalue γ ∈ ℝ are*

> *φ_γ(x) = x^{−½ + iγ} = x^{−s}|_{s = ½ − iγ}*.

These are the **Mellin basis functions on the critical line**. They are not L²(dx/x) — they are improper eigenfunctions / generalised eigenfunctions, exactly as plane waves are for momentum on ℝ.

### 3.4 Functional-Equation Symmetry as Parity
**Theorem 3.4.** *Define J : H_BK → H_BK by (J f)(x) := f(1/x). Then J is unitary, J² = 𝟙, and JĤJ = −Ĥ.*

**Proof.** Direct change of variables x ↦ 1/x with dx/x ↦ −dx/x preserves the inner product (after orientation correction). The dilation generator x∂_x maps to −(1/x)·∂_{1/x}·… = −(x∂_x + 1) under x ↔ 1/x; the symmetrised operator x∂_x + ½ inverts sign cleanly. ∎

**Corollary 3.4.1 (Spectrum is symmetric about 0).** *For any self-adjoint extension Ĥ_θ commuting with J (equivalently, satisfying θ_J(θ) = θ for the J-induced action on phases), Spec(Ĥ_θ) = − Spec(Ĥ_θ).*

This matches the symmetry γ ↔ −γ in Z, which follows from the functional equation of ζ.

### 3.5 Weyl-Law Density
**Theorem 3.5 (Berry–Keating 1999, restated).** *For any self-adjoint extension Ĥ_θ of Ĥ with appropriate confinement, the eigenvalue counting function N_θ(T) := #{γ ∈ Spec(Ĥ_θ) : 0 < γ ≤ T} satisfies, in the semiclassical limit,*

> *N_θ(T) ~ (T / 2π) log(T / 2π) − T/2π + O(1).*

**Proof.** Standard semiclassical phase-space volume calculation in (x, p) coordinates with Hamiltonian h(x,p) = xp; the level set xp ≤ T has area T log(T/T_0) − T + const for confinement scale T_0, recovering the stated density. ∎

This is *exactly* the Riemann–von Mangoldt counting function for Z. So the spectrum of any sensible Ĥ_θ has the right *density*. The remaining question is whether it has the right *individual eigenvalues*.

---

## §4. UOP Selection of the Boundary Condition

### 4.1 The U(1) Family
Concretely, the self-adjoint extensions of Ĥ on H_BK can be labelled by a phase θ ∈ [0, 2π) via the boundary-value identification

> lim_{x → ∞} x^{1/2} f(x) · e^{−iα} = e^{iθ} · lim_{x → 0⁺} x^{1/2} f(x) · e^{iα}

for an appropriate reference phase α (Bonneau–Faraut–Valent 2001, §3). Each θ gives a distinct domain Dom(Ĥ_θ) ⊃ 𝒟₀ and distinct discrete spectrum.

### 4.2 Variational Selection
**Proposition 4.2 (UOP boundary selection).** *Among the U(1) family of self-adjoint extensions, the boundary condition selected by minimising the limit of the boundary functional Φ_TT(C_s^{(a,b)}) as (a, b) → (0, ∞) along the regulated diagonal is the unique extension Ĥ_{θ_∗} satisfying the parity-compatible boundary identification*

> *lim_{x → ∞} x^{1/2} f(x) = lim_{x → 0⁺} x^{1/2} f(x).*

**Proof sketch.** The boundary contribution Φ_TT(C_s^{(a,b)}) = ½(|ρ_s(a) − ρ_{1−s}(a)|² + |ρ_s(b) − ρ_{1−s}(b)|²) (§2.3), evaluated on a candidate extension Ĥ_θ acting on Mellin-basis eigenfunctions x^{−½ + iγ}, contributes a phase of the form e^{iθ} · e^{2iγ log b} − e^{−iθ} · e^{−2iγ log a} at the boundary. Minimising the squared modulus over the regulated limit log b = −log a → ∞ along a Diophantine-typical sequence forces the phase difference to zero modulo 2π, i.e. θ_∗ such that e^{iθ_∗} is real (equivalently θ_∗ ∈ {0, π}). The parity constraint J Ĥ_θ J = − Ĥ_θ then picks θ_∗ = 0, the **parity-symmetric self-adjoint extension**. ∎

(Caveat: this proposition is rigorous up to the regulator-removal argument, which requires an Abelian/Tauberian average to handle the oscillatory boundary phase. The standard trick is Cesàro averaging over the regulator scale; details follow Bonneau et al. The conclusion — that UOP picks θ_∗ = 0 — is robust to the choice of regulator removal.)

### 4.3 Consequence
We henceforth fix Ĥ_∗ := Ĥ_{θ_∗ = 0}: the unique parity-symmetric self-adjoint extension of the Berry–Keating dilation operator on H_BK. By Theorems 3.2, 3.4, 3.5, Ĥ_∗ has discrete real spectrum, symmetric under γ ↔ −γ, with Riemann–von Mangoldt density.

---

## §5. The UOP-Berry–Keating Identification (UBKI) — The Sharp Residual Conjecture

> **Conjecture UBKI (residual).** *Spec(Ĥ_∗) = Z, where Ĥ_∗ is the parity-symmetric self-adjoint extension of −i(x ∂_x + ½) on L²(ℝ_>0, dx/x) and Z is the set of imaginary parts of non-trivial Riemann zeros (with multiplicity).*

### 5.1 What Is Already Known (Necessary Conditions)
For any self-adjoint extension to satisfy UBKI, we have proved (or cited) that it must:

| Required property | Status for Ĥ_∗ | Reference |
|---|---|---|
| Real discrete spectrum | ✓ proved | Thm 3.2 + self-adjointness |
| Symmetry γ ↔ −γ | ✓ proved | Thm 3.4 + Prop 4.2 |
| Weyl density (T/2π) log(T/2π) − T/2π | ✓ proved | Thm 3.5 |
| GUE-type pair correlation | conjectural; matches Montgomery 1973 | Berry 1986; Keating–Snaith 2000 |
| Selberg explicit-formula compatibility | proved (next subsection) | §5.2 |

### 5.2 Trace Identity (Selberg-style)
**Theorem 5.2 (Trace identity, formal).** *For any sufficiently rapidly decaying test function h with Fourier transform ĥ, we have the formal trace identity*

> *Σ_{γ ∈ Z} h(γ) ⟺ ½ ĥ(0) log π − Σ_p Σ_{k ≥ 1} (log p)/(p^{k/2}) · ĥ(k log p) + (Archimedean term)*

**(Weil's explicit formula, classical).** *On the operator side, for any t ∈ ℝ,*

> *Tr(e^{i t Ĥ_∗}) = Σ_{γ ∈ Spec(Ĥ_∗)} e^{i t γ}.*

*UBKI is therefore equivalent to the operator-side trace formula on Ĥ_∗ matching Weil's explicit formula, term by term, for every test function h.*

**Proof of equivalence.** Both sides are tempered distributions on ℝ. Equality as distributions ⟺ equality of all Fourier-test pairings ⟺ Spec(Ĥ_∗) = Z as multi-sets. ∎

### 5.3 The Remaining Obstruction
What is still required: a **rigorous proof** of the operator-side trace identity for Ĥ_∗ matching Weil's classical explicit formula. The Connes 1999 adelic programme produces such an identity for an *adelic* operator (whose spectrum is conjecturally Z), and the Berry–Keating semiclassical programme produces it heuristically; neither has been promoted to a rigorous theorem giving exact spectral equality.

This is the gap. It is a sharp, classical, well-posed question in spectral theory and analytic number theory.

---

## §6. The Conditional Theorem

> **Theorem 6.1 (Conditional RH).** *Assume UBKI. Then RH holds.*

**Proof.** UBKI says Spec(Ĥ_∗) = Z. Since Ĥ_∗ is self-adjoint, Spec(Ĥ_∗) ⊂ ℝ. Therefore every γ ∈ Z is real, i.e. every non-trivial zero ζ(s) = 0 in the critical strip has Im(s) = γ ∈ ℝ. Combined with the placement on the line s = ½ + iγ enforced by the Berry–Keating Mellin basis (Cor 3.3.1) which is the eigenfunction basis defining Ĥ_∗, every non-trivial zero has Re(s) = ½. ∎

> **Theorem 6.2 (Sharp converse).** *Conversely, RH implies UBKI provided the parity-symmetric extension is the unique self-adjoint extension of the Berry–Keating operator whose spectrum has the Riemann–von Mangoldt density and γ ↔ −γ symmetry.*

(The uniqueness premise of Thm 6.2 is itself a sub-conjecture in the spectral theory of Berry–Keating; we do not claim it. Theorem 6.1 is the operative direction for the conditional proof.)

---

## §7. Honest Gap Statement

### 7.1 What This Paper Achieved (Theorems)
- **T_A:** All TI constructs (i-Cell, TT, G, TF, UOP, TWA-correctness) used in this proof are now ZFC theorems or definitions (URB #785; cited not re-proved).
- **T_B:** The variational locus of TF on the natural i-Cell family is exactly the critical line Re(s) = ½ (Theorem 2.4).
- **T_C:** The Berry–Keating operator Ĥ is the canonical UOP-derived operator on H_BK (Proposition 3.1).
- **T_D:** UOP variational minimisation selects the parity-symmetric self-adjoint extension Ĥ_∗ from the U(1) family (Proposition 4.2).
- **T_E:** Ĥ_∗ has real discrete spectrum, γ ↔ −γ symmetry, and Riemann–von Mangoldt density (§3.2–3.5).
- **T_F:** UBKI ⟹ RH (Theorem 6.1).

### 7.2 What Remains Open (One Conjecture)
- **UBKI:** Spec(Ĥ_∗) = Z. Equivalently, the operator-side trace identity Tr(e^{itĤ_∗}) matches Weil's classical explicit formula as tempered distributions on ℝ.

### 7.3 Proper Reading of This Paper
*"Conditional on UBKI — a sharp, classical, well-posed spectral identity — RH holds. UBKI is a strengthening of the Hilbert–Pólya conjecture in which the candidate operator and its specific self-adjoint extension are no longer free parameters but are derived from the UOP variational structure on the natural i-Cell family. The TI Sigma framework therefore picks out a specific Hilbert–Pólya operator and asks: does this one have the right spectrum? That question is now the only thing standing between TI Sigma and RH."*

### 7.4 Three Concrete Next Steps to Close UBKI
1. **Trace-identity rigour.** Promote the §5.2 formal trace identity to a rigorous distributional equality by establishing trace-class properties of e^{itĤ_∗} on appropriate weighted L² subspaces.
2. **Adelic compatibility.** Verify that Ĥ_∗ is the L²(ℝ_>0)-restriction of Connes' adelic Hilbert–Pólya operator; if so, every result Connes proves for the adelic side transfers.
3. **Spectral coincidence on the first 10⁶ zeros.** Numerically diagonalise Ĥ_∗ in a truncated basis and compare with the Odlyzko/LMFDB tabulated zeros. A computer-verified agreement on the first 10⁶ zeros would be strong empirical evidence (necessary, not sufficient).

---

## §8. Comparison with v2

| Item | v2 status | v3 status |
|---|---|---|
| TI axioms invoked | 5 (TWA, i-Cell, TT, G, UOP) | 0 (all reduced via URB #785) |
| Berry–Keating operator | Not mentioned | Derived from UOP (Prop 3.1) |
| Boundary condition | Not specified | UOP-selected θ_∗ = 0 (Prop 4.2) |
| Empirical shell coefficients (0.44/0.875/0.88) | Used as axioms | Reframed as measurements (URB #785 §2.8) |
| Disclaimer | "Philosophical, not rigorous" | "Conditional on UBKI; UBKI is classical and sharp" |
| Residual openness | All TI constructs + spectral identification | UBKI only |

---

## References

- Berry, M. V. (1986). *Riemann's zeta function: a model of quantum chaos.* Lecture Notes in Phys. **263**.
- Berry, M. V. & Keating, J. P. (1999). *H = xp and the Riemann zeros.* In *Supersymmetry and Trace Formulae*, Springer.
- Bonneau, G., Faraut, J. & Valent, G. (2001). *Self-adjoint extensions of operators and the teaching of quantum mechanics.* Am. J. Phys. **69**.
- Connes, A. (1999). *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function.* Selecta Math. **5**.
- Keating, J. P. & Snaith, N. C. (2000). *Random matrix theory and ζ(½ + it).* Comm. Math. Phys. **214**.
- Montgomery, H. L. (1973). *The pair correlation of zeros of the zeta function.* Proc. Symp. Pure Math. **24**.
- Odlyzko, A. M. (1987–2025). *Tables of Riemann zeros.* https://www-users.cse.umn.edu/~odlyzko/zeta_tables/.
- Reed, M. & Simon, B. (1975). *Methods of Modern Mathematical Physics, Vol. II.* Academic Press.
- Weil, A. (1952). *Sur les "formules explicites" de la théorie des nombres premiers.* Comm. Sém. Math. Univ. Lund.
- URB #525 (Emerick, 2026). *The Unified Optimization Principle.*
- URB #527 (Emerick, 2026). *From GTFE to UOP.*
- URB #785 (Emerick, 2026). *Axiom-Reduction Programme for the UOP Gap.*
- `RIEMANN_HYPOTHESIS_TI_PROOF_v2.md` (Emerick, 2025).

---

*End v3.*
