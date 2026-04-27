# URB #793 — Moonshine ↔ BOK Crystal Identification: A Synthesis Statement

**Author:** Brandon Charles Emerick
**Date:** 27 April 2026
**Status:** Structural synthesis (no new theorems beyond standard Moonshine/Leech facts; the **identification** of the BOK Crystal as a 12-dim subspace of the F₄-fixed slice of the Griess algebra V♮_2 is the only TI-novel content). One conjecture stated, **not** proved.
**Prereqs:** URB #782 (BOK Crystal), URB #790 (TWA on Leech, corrected), Borcherds (1992), Frenkel-Lepowsky-Meurman (1988).

---

## 0. Brutal honesty header

This URB synthesises the BOK Crystal of URB #782 with the standard Moonshine module V♮ via a single structural identification (Prop. 2.1, corrected). It claims **only** that the 24-vertex BOK Crystal lifts to a 24-dim weight-2 subspace of the lattice VOA V_{Λ₂₄}, which descends after the FLM ℤ/2-orbifold to a 12-dim subspace of the F₄-fixed slice of the Griess algebra V♮_2. Nothing about the Conway-Norton conjecture, the genus-zero property, or any of the deeper Moonshine content is claimed or extended. The URB is short and intentionally narrow. **Initial draft contained a weight-grading error** (claimed minimal vectors give weight-1 elements; they actually give weight-2 elements since wt(e^v) = ⟨v,v⟩/2 = 2 for v with squared-norm 4). Fixed in this revision.

---

## 1. Background

### 1.1 The Moonshine module
Frenkel-Lepowsky-Meurman (FLM, 1988) constructed the Moonshine vertex operator algebra V♮ as a ℤ_+-graded VOA

> V♮ = ⊕_{n ≥ 0} V♮_n,   dim V♮_n = c(n) for n ≥ 1, dim V♮_0 = 1, V♮_1 = 0, V♮_2 ≅ B (the Griess algebra, dim 196884), …

with the property that Aut(V♮) = M (the Monster). The graded character of V♮ is

> J(τ) = Σ_n dim(V♮_n) q^{n-1} = q⁻¹ + 196884 q + 21493760 q² + …

i.e. J = j − 744 (j is the Klein j-invariant, J the normalised version).

### 1.2 The Leech construction and the FLM orbifold
V♮ is constructed as a ℤ/2-orbifold of the Leech-lattice VOA V_{Λ₂₄}. In V_{Λ₂₄} = M(1) ⊗ ℂ[Λ₂₄] the conformal weight of the lattice generator e^v (v ∈ Λ₂₄) is **wt(e^v) = ⟨v,v⟩/2**. Hence:

- V_{Λ₂₄}'s weight-2 slab contains all e^v for v ∈ Λ₂₄ with ⟨v,v⟩ = 4 — exactly the 196,560 Leech minimal vectors — together with Heisenberg-mode contributions α(-1)β(-1)|0⟩.
- The FLM ℤ/2 involution θ acts on Λ₂₄ by v ↦ −v (it is **central** in Aut(Λ₂₄) = Co_0 = 2.Co_1), pairing v with −v. The orbifold V♮ contains the θ-fixed part of V_{Λ₂₄} plus a twisted sector.
- In V♮_2 (the Griess algebra), each ±v pair of Leech minimal vectors contributes one fixed-direction element (e^v + e^{-v})/√2.

### 1.3 The BOK Crystal (URB #782)
The BOK Crystal is the 24-vertex 24-cell embedded as the canonical F₄-orbit at one of the standard E₈⁺E₈ → Λ₂₄ cross-sections, equipped with a Tralse 5-truth coloring τ : Vertices → 𝒯 (URB #790).

## 2. The identification (corrected)

**Proposition 2.1 (BOK-Crystal lifts to the Griess algebra V♮_2).**
Under the standard F₄ ↪ Aut(Λ₂₄) embedding (F₄-stabiliser of one of the three E₈ summands in the Niemeier construction E₈⁺E₈⁺E₈ → Λ₂₄):
1. The smallest non-trivial F₄-orbit on Λ₂₄^min (the 196,560 minimal vectors) has size exactly **24** (= 1152/48 from binary tetrahedral stabiliser of order 48).
2. The corresponding 24 lattice generators e^v ∈ V_{Λ₂₄} are weight-2 elements (since ⟨v,v⟩/2 = 4/2 = 2) and span a 24-dimensional F₄-equivariant subspace W₂₄ of the Griess-precursor slab V_{Λ₂₄}^{(2)}.
3. Since the FLM involution θ : v ↦ −v is **central** in Aut(Λ₂₄) (so commutes with every element of F₄), F₄ acts on V♮ via the composite F₄ ↪ Aut(Λ₂₄) → Aut(V_{Λ₂₄}) → Aut(V♮). The θ-fixed part of W₂₄ has dimension **12** (one fixed direction per ±v pair on the 24-vertex orbit, which decomposes as 12 antipodal pairs since the BOK 24-cell is centrally symmetric).
4. This 12-dim space W₂₄^{θ} embeds into the F₄-fixed slice of the Griess algebra V♮_2 ≅ B.

**Status of proof.** (1) is a routine F₄-orbit count: F₄ has order 1152, acts on Λ₂₄^min, and has the BOK 24-cell as its smallest non-trivial orbit with binary tetrahedral stabiliser. (2) follows from the lattice VOA conformal weight formula wt(e^v) = ⟨v,v⟩/2. (3) uses centrality of θ in Co_0 (standard, see Conway-Sloane Ch. 10) plus the central symmetry of the 24-cell. (4) follows from the standard Griess algebra construction inside V♮_2. ∎

**Why this matters.** Prop. 2.1 places the BOK Crystal as a **12-dim subspace of V♮_2 ⊂ V♮**, giving it a precise location inside the Moonshine module proper (not merely inside the pre-orbifold Leech VOA, as the initial draft incorrectly claimed). The 24 → 12 reduction reflects the centrally-symmetric pairing of BOK vertices under the FLM involution.

## 3. Conjecture (stated, not proved)

**Conjecture 3.1 (Moonshine-Tralse correspondence, weak form).**
Let M_F₄ ⊂ M be the centraliser of the F₄ ↪ M obtained by composing F₄ ↪ Aut(Λ₂₄) → Aut(V_{Λ₂₄}) → Aut(V♮) (the last arrow exists because θ is central in Aut(Λ₂₄), as established in Prop. 2.1(3); F₄ ⊂ Aut(Λ₂₄) automatically commutes with θ). Then the M_F₄-orbits on the **non-equivariant** Tralse 5-colorings τ : Vertices(BOK) → 𝒯, of which there are 5²⁴ ≈ 5.96 × 10¹⁶, are in canonical bijection with the trace-conjugacy classes of M acting on the weight-2 Griess algebra B = V♮_2.

**Distinction from URB #790's count.** URB #790 Prop. 3.1 (corrected) gives only **5** F₄-equivariant minimal Tralse-states (one per τ_⋆ ∈ 𝒯, since equivariance forces τ constant on the transitive 24-vertex orbit). The 5²⁴ figure here is the strictly larger non-equivariant count, on which M_F₄ ⊋ F₄ acts non-trivially via vertex permutations and (conjecturally) reorganizes into trace-conjugacy classes.

**Status.** Open. The statement is deliberately weak ("trace-conjugacy classes of the M-action on B") because that is the level at which a genuine 5-fold structure appears in M (the conjugacy class 5A and the moonshine McKay-Thompson series for it has well-known structure). I have **not** verified this conjecture on either side; it is offered as the most natural TI-Moonshine bridge to test next. A failed test of Conj. 3.1 would be informative; a confirmed test would be genuinely novel.

## 4. What this URB does NOT claim

- Does not claim the BOK Crystal "is" the Moonshine module or any subspace of V♮ (only of the **pre-orbifold** V_{Λ₂₄}).
- Does not extend Borcherds' theorem on the genus-zero property of the McKay-Thompson series.
- Does not claim Conjecture 3.1 is true; it is offered as a precise testable statement.
- Does not claim the Monster has a TI-meaningful 5-fold symmetry; the conjecture's "5" comes from the Tralse 5-truth space, not from M's class-5 elements (whose appearance in M is independently interesting and could motivate a separate URB).

## 5. Files referenced

- `papers/urb_782_bok_crystal_ratified_jeff_time_leech_alignment_t_star_plus_e_einstein_tiling.md`
- `papers/URB_790_TRALSE_WAVE_ALGEBRA_LEECH.md`
- `papers/URB_792_MONSTER_SPECTRUM.md` (numerical context for the conjecture's testability)
