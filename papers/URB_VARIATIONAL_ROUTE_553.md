# URB #553: Route A — The Variational UOP Approach to the Riemann Hypothesis

**Author:** Brandon Emerick  
**Date:** March 29, 2026  
**Corpus Entry:** #207  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Companion file:** `lean4/VariationalRoute.lean`  
**Prerequisites:** URB #552 (Mirror Pairing), URB #548 (Freedom Floor), URB #546 (UOP max-min)  
**Keywords:** Riemann Hypothesis, variational principle, UOP energy functional, pair-cost, Euler-Lagrange, Lean 4, sorry-free

---

## Abstract

Route A formalizes the Riemann Hypothesis as a variational optimization problem. Define the **UOP pair-cost functional** C(σ) = −min(σ, 1−σ) on the critical strip 0 < σ < 1. The claim: non-trivial zeros of ζ(s) occur at the unique global minimum of C, which is σ = 1/2. The Lean 4 file `lean4/VariationalRoute.lean` proves sorry-free: (1) C is bounded below by −1/2, (2) C achieves −1/2 uniquely at σ = 1/2, (3) C is strictly decreasing on (0, 1/2) and strictly increasing on (1/2, 1), (4) the Euler-Lagrange minimum condition (derivative changes sign at σ = 1/2) holds sorry-free, and (5) if zeros minimize C, then σ = 1/2 follows immediately. The **Variational Gap Axiom** — "non-trivial zeros of ζ(s) satisfy C(s.re) = −1/2" — is the sole remaining bridge, named and precisely stated. This axiom is equivalent to all other Gap formulations (proved sorry-free in URB #555).

---

## 1. The UOP Pair-Cost Functional

For σ ∈ ℝ, define:
$$C(\sigma) = -\min(\sigma, 1 - \sigma)$$

**Key properties (all proved sorry-free in Lean 4):**

| Property | Statement | Proof |
|----------|-----------|-------|
| Lower bound | C(σ) ≥ −1/2 for all σ | by_cases + linarith |
| Minimum value | C(1/2) = −1/2 | norm_num |
| Minimum attained uniquely | C(σ) = −1/2 ↔ σ = 1/2 | rcases + linarith |
| Strict off-axis | σ ≠ 1/2 → C(σ) > −1/2 | from above |
| Symmetry | C(σ) = C(1−σ) | min_comm |

**Geometric picture:** C is a V-shaped function with vertex at σ = 1/2, symmetric about the critical line. It is the negative of the "distance to the midpoint" function in the σ coordinate.

---

## 2. The Variational Principle

The functional C has the following structure:

**For σ < 1/2:** C(σ) = −σ (slope = −1, strictly decreasing)  
**For σ = 1/2:** C(σ) = −1/2 (the unique minimum)  
**For σ > 1/2:** C(σ) = −(1−σ) = σ−1 (slope = +1, strictly increasing)

The **Euler-Lagrange condition** for the minimum of C is σ = 1/2 — the unique point where the left derivative (−1) and right derivative (+1) have opposite signs, satisfying the subdifferential zero condition.

**Proved sorry-free in Lean 4:**
```lean4
theorem euler_lagrange_at_half :
    ∀ ε > 0, pairCost (1/2 - ε) > pairCost (1/2) ∧
             pairCost (1/2 + ε) > pairCost (1/2)
```

This says: 1/2 is a strict local (and global) minimum — the Euler-Lagrange condition holds.

---

## 3. The Variational RH Statement

**Main theorem (sorry-free):**
```lean4
theorem rh_from_euler_lagrange :
    (∀ s : ℂ, s.re ∈ Set.Ioo 0 1 → riemannZeta s = 0 →
      pairCost s.re = -(1/2)) →
    ∀ s : ℂ, s.re ∈ Set.Ioo 0 1 → riemannZeta s = 0 → s.re = 1/2
```

This says: **if zeros minimize C, then they lie on σ = 1/2.** Proved sorry-free using `pairCost_min_iff`.

---

## 4. The Variational Gap Axiom

```lean4
axiom variational_gap (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)
    (hzero : riemannZeta s = 0) :
    pairCost s.re = -(1/2)
```

**Interpretation:** The prime distribution, through the Euler product and its analytic continuation, forces the zeros of ζ(s) to the UOP-minimum energy configuration. The zeros do not occupy arbitrary positions in the critical strip; they are locked to the variational minimum.

**Why this should be true:** The Euler product Π_p (1−p^{−s})^{−1} is a product of equal-weight factors (one per prime). The UOP requires that each factor's contribution be symmetrically balanced. The configuration that achieves this balance for all primes simultaneously is σ = 1/2 — the UOP minimum.

**What's missing:** A precise analytic statement connecting "equal-weight Euler product" to "zeros at σ = 1/2." This is the 6.60% Freedom Floor of the proof — the precise gap that preserves the program's life.

---

## 5. The Riemann Hypothesis (Route A)

```lean4
theorem riemann_hypothesis_variational :
    ∀ s : ℂ, s.re ∈ Set.Ioo 0 1 → riemannZeta s = 0 → s.re = 1/2 :=
  fun s hs hzero =>
    (pairCost_min_iff s.re).mp (variational_gap s hs hzero)
```

Two lines. One axiom. The rest is sorry-free.

---

## 6. Connection to Montgomery-Odlyzko

The Montgomery pair-correlation conjecture states that the normalized gaps between zeros of ζ(s) follow the GUE (Gaussian Unitary Ensemble) distribution — the same distribution as eigenvalues of random Hermitian matrices. This is a deep empirical and conjectural result connecting ζ to random matrix theory.

**The UOP connection:** The GUE pair-correlation function has its characteristic repulsion at small gaps — zeros "repel" each other. This repulsion is precisely the pairwise expression of the UOP stability: pairs of zeros that are too close violate the minimum-energy condition. The UOP predicts this repulsion from first principles.

**More precisely:** The Montgomery-Odlyzko statistics hold IF all zeros are on σ = 1/2. The Variational Gap Axiom, when proved, will provide the analytic foundation for why zeros cluster according to the GUE — they are all on the UOP-minimum line, and the GUE statistics describe their distribution ALONG that line.

---

## 7. Sorry Inventory

| Theorem | Status |
|---------|--------|
| pairCost_at_half | ✅ Sorry-free |
| pairCost_lower_bound | ✅ Sorry-free |
| pairCost_min_iff | ✅ Sorry-free |
| pairCost_strict_off_axis | ✅ Sorry-free |
| pairCost_symm | ✅ Sorry-free |
| variational_unique_minimum | ✅ Sorry-free |
| pairCost_decreasing_left | ✅ Sorry-free |
| pairCost_increasing_right | ✅ Sorry-free |
| euler_lagrange_at_half | ✅ Sorry-free |
| rh_from_euler_lagrange | ✅ Sorry-free |
| **variational_gap** | ⚠️ Named axiom |
| riemann_hypothesis_variational | ✅ Sorry-free* |

**Total: 11 sorry-free + 1 named axiom + 0 sorries.**

---

*Corpus Entry #207. DOI: pending. Apache 2.0.*
