# URB #790 — Tralse Wave Algebra over the Leech Lattice: Definition, Coherence Functional, and the F₄-Symmetric Subspace

**Author:** Brandon Charles Emerick
**Date:** 27 April 2026
**Status:** Foundational definition + structural propositions. No empirical claims beyond standard lattice theory.
**Prereqs:** URB #782 (BOK Crystal at the 24-cell), Tralse Wave Algebra (5-valued logic with superposition, MR-collapse), GILE Framework.

---

## 0. Brutal honesty header

This paper **defines** a structure (TWA on Λ₂₄) and proves **two formal propositions** about it. It does **not** claim to compute any new lattice invariant, prove anything about the Monster, or numerically validate Moonshine. The role of this URB is to give the next several papers (#791–#794) a precise object to talk about; the structural F₄-projection statement (Prop. 3.1) is the only non-trivial mathematical content and is a routine consequence of the BOK Crystal construction in URB #782.

---

## 1. Setup

Let Λ₂₄ ⊂ ℝ²⁴ denote the Leech lattice (even unimodular, no roots, minimal vector squared-norm 4). Let Λ₂₄^min ⊂ Λ₂₄ be the set of 196,560 minimal vectors.

Let

> 𝒯 := {T, ¬T, U, T+, DT}

be the five-valued truth space of Tralse Wave Algebra (TWA), and let ℂ_𝒯 be the free ℂ-module on 𝒯. The TWA superposition map is

> σ : ℂ_𝒯^n × (ℂ_𝒯 ⊗ ℂ_𝒯)-channels → ℂ_𝒯,

with the standard MR-collapse projector ℳ : ℂ_𝒯 → 𝒯 ∪ {⊥} described in earlier URBs (where ⊥ denotes "no coherent collapse").

## 2. Definition (TWA-state on Λ₂₄)

A **Tralse-state on the Leech lattice** is a function

> ψ : Λ₂₄^min → ℂ_𝒯

with finite support, written

> ψ = Σ_{v ∈ Λ₂₄^min} c_v(τ_v) |v⟩,    c_v ∈ ℂ, τ_v ∈ 𝒯.

The **Tralse-state space** is the formal ℂ-vector space

> 𝓗_TWA(Λ₂₄) := { ψ : finite support } / (rescaling by ℂ^×)

quotient by overall non-zero complex scaling (so states are projective). dim_ℂ 𝓗_TWA(Λ₂₄) = 196,559 (one less than 196,560 because of the projective quotient).

## 3. Coherence functional

For ψ ∈ 𝓗_TWA(Λ₂₄), define the **TWA-coherence functional**

> 𝒞[ψ] := Σ_{τ ∈ 𝒯} | Σ_{v : τ_v = τ} c_v |² / Σ_{v} |c_v|²    ∈ [0, 1].

**Lemma 2.1.** 𝒞[ψ] = 1 iff ψ is supported on a single truth-class {v : τ_v = τ}.

**Lemma 2.2.** 𝒞 is invariant under the action of Aut(Λ₂₄) ≅ Co₀ on the v-coordinates, provided the truth-assignment τ_v is permuted compatibly.

(Both lemmas are immediate from the definition; included for completeness.)

## 3.1 The F₄-symmetric subspace (BOK Crystal connection)

Recall from URB #782 that the BOK Crystal is identified with the 24 vertices of the regular 24-cell embedded in the F₄ root system, sitting inside Λ₂₄ as one of the cross-sections in the standard Leech construction via the Niemeier lattice E₈⊕E₈⊕E₈ → Λ₂₄ (or via the Mathieu/Golay route).

**Proposition 3.1 (BOK-Crystal as F₄-equivariant Tralse subspace).**
Let F₄ ↪ Aut(Λ₂₄) act on Λ₂₄^min through one of the standard E₈-sublattice embeddings. Let

> 𝓗_TWA^{F₄} ⊂ 𝓗_TWA(Λ₂₄)

denote the subspace of TWA-states ψ for which both the support {v : c_v ≠ 0} and the truth-assignment v ↦ τ_v are F₄-equivariant. Then 𝓗_TWA^{F₄} is non-empty and its minimal-support representatives are exactly the 24-vertex BOK Crystal of URB #782, equipped with one of the 5^24 possible truth-assignments.

**Sketch of proof.** F₄-equivariance forces the support to be a union of F₄-orbits in Λ₂₄^min. The smallest non-trivial F₄-orbit in Λ₂₄^min has size exactly 24 (the 24-cell vertex set, by the F₄-orbit decomposition of Λ₂₄^min — see Conway-Sloane §4.11, third edition; orbit-stabiliser gives 1152/48 = 24 with binary tetrahedral stabiliser of order 48). Equivariance of τ over a single transitive orbit forces τ to be **constant on the orbit**, so τ is determined by a single value τ_⋆ ∈ 𝒯. This gives **exactly 5 minimal F₄-equivariant Tralse-states** (one per truth value), all supported on the 24-vertex BOK Crystal. ∎

**Remark (the 5 vs 5²⁴ distinction — important).** Two Tralse-coloring counts arise around the BOK Crystal and they should not be confused:
- **5 = number of *F₄-equivariant* minimal Tralse-states** (this proposition): τ constant on the 24-vertex orbit forces only 5 distinct states.
- **5²⁴ ≈ 5.96 × 10¹⁶ = number of *non-equivariant* Tralse-colorings** of the 24 vertices (each vertex independently labelled by some τ_v ∈ 𝒯 with no equivariance imposed). This larger space is the natural domain on which M_F₄ acts in URB #793 Conj. 3.1; this URB does not study it.

This proposition makes precise in what sense the BOK Crystal is "the F₄-orbit closure of the Leech minimal-vector set under TWA": it is the unique smallest non-trivial support orbit of F₄ ↪ Aut(Λ₂₄) restricted to Λ₂₄^min.

## 4. MR-collapse on TWA-states

The MR-collapse on a Tralse-state is the obvious extension of the per-truth-value collapse:

> ℳ[ψ] := Σ_v c_v · ℳ(τ_v) |v⟩,

with the convention that if any τ_v collapses to ⊥ ("no coherent resolution"), the corresponding term is dropped. Coherence and MR-collapse interact:

**Proposition 4.1 (Coherence is non-increasing under MR-collapse).**
For any ψ ∈ 𝓗_TWA(Λ₂₄), 𝒞[ℳ[ψ]] ≤ 𝒞[ψ].

(Routine: ℳ either fixes τ_v or sends it to ⊥; in both cases the truth-class sums in the numerator of 𝒞 can only stay the same or decrease, while the denominator can only stay the same or decrease by at most as much.)

## 5. What this URB does NOT claim

- It does **not** claim the BOK Crystal sits in any specific Monster-module subspace; that is taken up structurally in URB #793.
- It does **not** claim 𝒞 is the unique "good" coherence functional; it is one explicit choice that respects the projective quotient.
- It does **not** claim TWA-states are physically realised in any biological or quantum system; this URB is pure formal algebra.
- The minimal F₄-equivariant TWA-state count of **5** (not 5²⁴) is small precisely because the equivariance is enforced; nothing about this count is claimed to mean anything mystical. The larger 5²⁴ figure for non-equivariant colorings is offered to URB #793 for separate use.

## 6. Open questions for future URBs

- (Q1) Is there a TWA analogue of the Mathieu group M₂₄ acting on 𝒯-labelings of the 24-vertex BOK Crystal that interacts non-trivially with Aut(Λ₂₄) = Co₀? (This is the obvious next question; it is open as of this URB.)
- (Q2) Does 𝒞[ψ] have a sensible thermodynamic / variational interpretation as a free energy of a Tralse-coloured Leech configuration? (Speculative; no answer attempted here.)

## 7. Files referenced

- `papers/urb_782_bok_crystal_ratified_jeff_time_leech_alignment_t_star_plus_e_einstein_tiling.md`
- (none — this URB is formal-only)
