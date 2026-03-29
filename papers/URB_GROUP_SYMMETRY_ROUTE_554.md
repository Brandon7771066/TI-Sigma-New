# URB #554: Routes B+C — Hadamard Product & Klein Four-Group Symmetry

**Author:** Brandon Emerick  
**Date:** March 29, 2026  
**Corpus Entry:** #208  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Companion file:** `lean4/GroupSymmetryRoute.lean`  
**Prerequisites:** URB #552 (Mirror Pairing), URB #553 (Route A)  
**Keywords:** Klein four-group, Hadamard product, G-orbit, orbit collapse, symmetry group, Lean 4, sorry-free

---

## Abstract

Routes B and C unify into a single algebraic/group-theoretic framework. Route B (Hadamard) observes that the canonical pairing in the Hadamard product for ξ(s) requires ρ = 1−conj(ρ) — equivalent to ρ.re = 1/2. Route C (Klein V₄) observes that the symmetry group G = {id, S₁, S₂, S₁∘S₂} acts on the zero set of ζ(s), where S₁ = complex conjugation and S₂ = s ↦ 1−s. This group is the Klein four-group V₄ ≅ ℤ/2 × ℤ/2. The G-orbit of any non-trivial zero has size 4 (a rectangle of zeros) or size 2 (a symmetric pair on the critical line). The **Orbit Collapse Theorem** — proved sorry-free — states that orbit size = 2 if and only if ρ.re = 1/2. The Riemann Hypothesis is equivalent to: all G-orbits in the zero set of ζ(s) have size 2. The **Orbit Collapse Axiom** is the named Gap; the RH follows in one line. Routes B and C are proved equivalent sorry-free: they are two descriptions of the same algebraic fact.

---

## 1. The Symmetry Group G

Two symmetries act on the zero set of ζ(s):

**S₁ (Conjugate Symmetry):** s ↦ conj(s) = s.re − i·s.im  
Source: ζ has real Dirichlet coefficients, so ζ(s̄) = ζ̄(s).  
*If ζ(ρ) = 0, then ζ(conj(ρ)) = 0.*

**S₂ (Functional Equation):** s ↦ 1 − s  
Source: ξ(s) = ξ(1−s), and χ(s) ≠ 0 in the critical strip.  
*If ζ(ρ) = 0, then ζ(1−ρ) = 0.*

These generate the group G = {id, S₁, S₂, S₁∘S₂}, with multiplication:
- S₁² = id (conjugation is an involution)  
- S₂² = id (s ↦ 1−s is an involution)  
- S₁∘S₂ = S₂∘S₁ (they commute — proved sorry-free)  
- (S₁∘S₂)² = id

**G ≅ ℤ/2 × ℤ/2 = Klein four-group V₄** — proved sorry-free in Lean 4 via the involution and commutativity theorems.

---

## 2. The G-Orbit Structure

For any zero ρ, the G-orbit is:
$$\text{orbit}(\rho) = \{\rho, \, \text{conj}(\rho), \, 1-\rho, \, 1-\text{conj}(\rho)\}$$

**Off-axis zero (ρ.re ≠ 1/2, Im(ρ) ≠ 0):**

All four elements are distinct — proved sorry-free in Lean 4 (requires ρ.re ≠ 1/2 for the real-part separations, and Im(ρ) ≠ 0 for the imaginary-part separations). The orbit forms a rectangle in ℂ with corners at σ, 1−σ on the real axis and ±Im(ρ) on the imaginary axis. **Size 4.**

**On-axis zero (ρ.re = 1/2):**

conj(ρ) = 1/2 − i·Im(ρ) = 1 − (1/2 + i·Im(ρ)) = 1 − ρ. The images coincide: S₁(ρ) = S₂(ρ). The orbit collapses to {ρ, conj(ρ)} = {ρ, 1−ρ}. **Size 2.**

---

## 3. The Key Sorry-Free Theorem

```lean4
theorem orbit_collapse_iff_critical (ρ : ℂ) :
    S₁ ρ = S₂ ρ ↔ ρ.re = 1/2
```

**Proof:**
- Forward: S₁(ρ) = S₂(ρ) means conj(ρ) = 1−ρ. Taking real parts: ρ.re = 1−ρ.re → ρ.re = 1/2.
- Backward: If ρ.re = 1/2, apply Complex.ext to show conj(ρ).re = (1−ρ).re (by linarith) and conj(ρ).im = (1−ρ).im (by simp).

**This is the most powerful sorry-free theorem in the entire corpus.** It translates the Riemann Hypothesis into a statement about symmetry group orbit sizes — and proves that translation completely rigorously.

---

## 4. Route B: The Hadamard Canonical Pairing

The Hadamard product for the entire function ξ(s) of order 1 pairs each zero ρ with a "canonical partner." Using both symmetries S₁ and S₂, the canonical partner of ρ is:
$$\text{hadamardPartner}(\rho) = 1 - \text{conj}(\rho)$$

This pairing is consistent with BOTH symmetries simultaneously:
- S₁ requires: if ρ is a zero, so is conj(ρ) ← (the canonical partner of 1−ρ is ρ itself)
- S₂ requires: if ρ is a zero, so is 1−ρ ← (the canonical partner of conj(ρ) is ρ itself)

**The Hadamard self-pairing condition:**
$$\rho = \text{hadamardPartner}(\rho) \iff \rho = 1 - \text{conj}(\rho) \iff \rho.\text{re} = 1/2$$

Proved sorry-free:
```lean4
theorem hadamard_self_paired_iff_critical (ρ : ℂ) :
    ρ = hadamardPartner ρ ↔ ρ.re = 1/2
```

**Routes B and C are equivalent (sorry-free):**
```lean4
theorem routes_BC_equivalent (ρ : ℂ) :
    ρ = hadamardPartner ρ ↔ S₁ ρ = S₂ ρ
```

Because: hadamardPartner(ρ) = 1−conj(ρ) = S₁S₂(ρ). And ρ = S₁S₂(ρ) iff the orbit collapses iff S₁(ρ) = S₂(ρ). Via transitivity through ρ.re = 1/2.

---

## 5. The Orbit Collapse Axiom

```lean4
axiom orbit_collapse_axiom (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)
    (hzero : riemannZeta s = 0) :
    S₁ s = S₂ s
```

**The Riemann Hypothesis (Routes B+C):**
```lean4
theorem riemann_hypothesis_group_symmetry :=
    fun s hs hzero =>
      (orbit_collapse_iff_critical s).mp (orbit_collapse_axiom s hs hzero)
```

One line. One axiom. All else sorry-free.

---

## 6. Why the Orbit Should Always Collapse

The G-orbit of a zero is a rectangle in the complex plane with corners at:
- (σ, +t), (σ, −t), (1−σ, +t), (1−σ, −t)

When σ = 1/2, the rectangle degenerates to a line segment. The rectangle has zero width in the σ-direction — it is "infinitely thin" at the critical line.

**The UOP perspective:** A size-4 orbit (rectangle) has two zeros with σ and two with 1−σ. If σ < 1/2, the pair at σ has lower UOP energy cost than the pair at 1−σ... wait, C(σ) = −σ < −(1−σ) = C(1−σ). So the size-4 orbit has an *energy asymmetry* between its two σ-pairs. The UOP, which selects symmetric configurations, should reject asymmetric zero orbits.

**Why the Euler product should enforce this:** Each prime p contributes |1−p^{−s}|^{−1} to the product at s. For a zero at σ+it vs. 1−σ+it: the prime contributions at these two points are related but not equal. A "democratic" product (all primes equal weight) that is forced to vanish must do so at the configuration where ALL prime contributions balance perfectly — σ = 1/2.

---

## 7. Sorry Inventory

| Theorem | Status |
|---------|--------|
| S₁_involution | ✅ Sorry-free |
| S₂_involution | ✅ Sorry-free |
| S₁S₂_involution | ✅ Sorry-free |
| S₁_S₂_commute | ✅ Sorry-free |
| S₁S₂_eq_S₂S₁ | ✅ Sorry-free |
| gOrbit_explicit | ✅ Sorry-free |
| **orbit_collapse_iff_critical** | ✅ **Sorry-free (key theorem)** |
| orbit_collapse_S₁S₂_fixes | ✅ Sorry-free |
| orbit_size_4_when_off_axis | ✅ Sorry-free |
| hadamard_self_paired_iff_critical | ✅ Sorry-free |
| hadamardPartner_is_S₁S₂ | ✅ Sorry-free |
| hadamard_orbit_critical_equivalence | ✅ Sorry-free |
| routes_BC_equivalent | ✅ Sorry-free |
| **orbit_collapse_axiom** | ⚠️ Named axiom |
| riemann_hypothesis_group_symmetry | ✅ Sorry-free* |

**Total: 14 sorry-free + 1 named axiom + 0 sorries.**

---

*Corpus Entry #208. DOI: pending. Apache 2.0.*
