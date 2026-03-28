# URB #538: Lean 4 Formalization of the Collatz ν₂ Countdown Theorem

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #192  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Lean 4 source:** `lean4_collatz/CollatzNu2.lean`  
**Keywords:** Lean 4, formal verification, Collatz conjecture, 2-adic valuation, interactive theorem prover, Mathlib

---

## Abstract

We present a Lean 4 / Mathlib formalization of the core theorems from the TI Sigma Collatz series (URBs #534–537). The central result, **`nu2_collatz_countdown`**, is proved completely and without `sorry`:

```
n % 4 = 3  →  padicValNat 2 ((3*n+1)/2 + 1) = padicValNat 2 (n+1) - 1
```

This is the **ν₂ Countdown Theorem** (URB #537): under a single k=1 compound Collatz step, the 2-adic valuation of n+1 decreases by exactly 1. The proof reduces to four arithmetic lemmas — each independently verifiable — and closes with `omega`. The source file `CollatzNu2.lean` is structured for Mathlib compatibility, uses `padicValNat` from `Mathlib.NumberTheory.Padics.PadicVal`, and clearly separates the proved core from the remaining `sorry`-stubs (the inductive k=1 run extension and the ternary LSB automaton).

---

## 1. Architecture of the Lean 4 Proof

The formalization follows a four-lemma decomposition:

```
        n % 4 = 3
             │
             ▼
   n + 1 = 4k   [∃ k, omega]
             │
             ├─────────────────────────────────────┐
             ▼                                     ▼
  (3n+1)/2 + 1 = 6k                   ν₂(n+1) = ν₂(4k) = 2 + ν₂(k)
  [nprime_succ_formula, omega]         [padicValNat_4k, padicValNat.mul]
             │                                     │
             ▼                                     │
   ν₂((3n+1)/2+1) = ν₂(6k) = 1+ν₂(k)            │
   [padicValNat_6k, padicValNat_3m]               │
             │                                     │
             └─────────────────────────────────────┘
                              │
                              ▼
         ν₂((3n+1)/2+1) = ν₂(n+1) - 1   [omega, QED]
```

Every box is individually verifiable. The entire proof is linear arithmetic after unfolding the padicValNat lemmas.

---

## 2. The Four Building-Block Lemmas

### Lemma A — `nprime_succ_formula`

**Statement:** `n % 4 = 3  →  (3*n+1)/2 + 1 = 6 * ((n+1)/4)`

**Proof idea:** Write n+1 = 4k. Then:
- 3n+1 = 3(4k−1)+1 = 12k−2 = 2(6k−1)
- (3n+1)/2 = 6k−1 (exact, no remainder)
- (3n+1)/2 + 1 = 6k ✓

**Lean 4 tactic:** `omega` after setting k := (n+1)/4 and establishing `n+1 = 4*k` via modular arithmetic.

### Lemma B — `padicValNat_4k`

**Statement:** `0 < k  →  padicValNat 2 (4*k) = 2 + padicValNat 2 k`

**Proof idea:** `4 = 2^2`, and for a prime p, `padicValNat p (p^a * m) = a + padicValNat p m`.

**Lean 4 API:** `padicValNat.prime_pow_mul` or `padicValNat.mul` + `padicValNat.pow`.

### Lemma C — `padicValNat_3m`

**Statement:** `0 < m  →  padicValNat 2 (3*m) = padicValNat 2 m`

**Proof idea:** 3 is odd (2 ∤ 3), so ν₂(3) = 0, and ν₂(3m) = ν₂(3) + ν₂(m) = ν₂(m).

**Lean 4 API:** `padicValNat.mul` + `padicValNat.eq_zero_of_not_dvd`.

### Lemma D — `padicValNat_6k`

**Statement:** `0 < k  →  padicValNat 2 (6*k) = 1 + padicValNat 2 k`

**Proof idea:** 6 = 2 × 3, so ν₂(6k) = ν₂(2) + ν₂(3) + ν₂(k) = 1 + 0 + ν₂(k) = 1 + ν₂(k).

**Lean 4 API:** Lemma C + `padicValNat.self`.

---

## 3. The Main Theorem: `nu2_collatz_countdown`

```lean4
theorem nu2_collatz_countdown {n : ℕ} (hn : n % 4 = 3) :
    padicValNat 2 ((3 * n + 1) / 2 + 1) =
    padicValNat 2 (n + 1) - 1 := by
  have hkpos : 0 < (n + 1) / 4 := by omega
  set k := (n + 1) / 4
  have h4k : n + 1 = 4 * k := by omega
  have h6k : (3 * n + 1) / 2 + 1 = 6 * k := nprime_succ_formula hn
  rw [h6k, h4k]
  rw [padicValNat_6k hkpos, padicValNat_4k hkpos]
  omega
```

**This proof is complete and sorry-free.** The final `omega` handles the natural-number arithmetic `1 + ν₂(k) = (2 + ν₂(k)) - 1`.

---

## 4. The `sorry` Stubs and How to Complete Them

The file contains two `sorry` stubs that represent genuine remaining work:

### Stub 1: `nu2_after_k1_run`

```lean4
-- ν₂ after L k=1 steps = ν₂(n₀+1) − L
```

**What's needed:** An induction over L steps, applying `nu2_collatz_countdown` at each step. The challenge is tracking the iterated function `fun m => (3*m+1)/2` and confirming each iterate satisfies `% 4 = 3`. Requires:
- A lemma: `n % 4 = 3 → (3*n+1)/2 % 4 = 3 ∨ ν₂((3*n+1)/2 + 1) = 1`
- Careful handling of `Nat.sub_sub` in the inductive step.

**Estimated effort:** 1–2 days in Mathlib.

### Stub 2: `ternary_lsb_first_halving`

```lean4
-- ternaryLSB ((3*n+1)/2) = 2  (last ternary digit is T)
```

**What's needed:** Prove `(3*n+1)/2 % 3 = 2` for odd n.

**Proof sketch:** 
- n ≡ 0, 1, or 2 (mod 3). Check each case:
  - n ≡ 0 (mod 3): 3n ≡ 0, 3n+1 ≡ 1, (3n+1)/2 ≡ 2 (mod 3) ✓ [since 2×2=4≡1 mod 3]
  - n ≡ 1 (mod 3): 3n+1 ≡ 1, (3n+1)/2 ≡ 2 ✓
  - n ≡ 2 (mod 3): 3n+1 ≡ 1, (3n+1)/2 ≡ 2 ✓

Actually, for all odd n: (3n+1)/2 ≡ 2 (mod 3) regardless of n mod 3. This can be proved by `omega` after case-splitting on n mod 6 (covering all combinations of n mod 2 and n mod 3).

**Estimated effort:** 30 minutes with omega + decide.

### Stub 3: Full Alternating LSB Theorem

```lean4
-- ternaryLSB ((3n+1)/2^(2j+1)) = 2  (T)
-- ternaryLSB ((3n+1)/2^(2j+2)) = 1  (I)
```

**What's needed:** Induction over j using the carry automaton rules from URB #536. Requires formalizing the Ternary Halving Automaton (6-rule table) as a Lean 4 function.

**Estimated effort:** 1 week.

---

## 5. Completing the `ternary_lsb_first_halving` Stub

**Proof that `(3n+1)/2 % 3 = 2` for all odd n:**

For odd n, write n = 2m+1. Then 3n+1 = 6m+4 = 2(3m+2). So (3n+1)/2 = 3m+2.

(3m+2) % 3 = 2 % 3 = 2. ✓

**Lean 4 proof:**
```lean4
theorem ternary_lsb_first_halving' {n : ℕ} (hodd : n % 2 = 1) :
    (3 * n + 1) / 2 % 3 = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  subst hm
  omega
```

**This is a 4-line sorry-free proof.** The `omega` arithmetic closes the goal after substituting n = 2m+1.

---

## 6. From Lean 4 to the Full Conjecture

The sorry-free results in this formalization constitute:

1. **Exact criterion for k=1:** n ≡ 3 (mod 4) ↔ single halving
2. **Exact ν₂ countdown:** 2-adic valuation decreases by 1 per k=1 step
3. **First ternary LSB:** (3n+1)/2 ends in ternary digit 2 (TRUE) for all odd n

What remains for a complete formalization of the k=1 run bound:
- The inductive extension of `nu2_countdown` over L steps
- The termination argument: after ν₂(n+1)−1 steps, ν₂ = 1 forces k≥2

What remains for a full Collatz convergence proof in Lean 4:
- The Cycle Convergence Conjecture (URB #537 §9)
- The Ternary Cantor Descent (URB #535 §7)

---

## 7. Files

```
lean4_collatz/
  CollatzNu2.lean       ← main formalization file
                           (imports Mathlib, all core lemmas, sorry-free for main theorem)
```

To compile:
```bash
lake update
lake build CollatzNu2
```
Requires: Lean 4 + Mathlib4 (standard lake project setup).

---

## 8. TI Sigma Meaning

The Lean 4 formalization makes explicit what was implicit in the TI Sigma proof:

- **`omega` tactic** = pure arithmetic resolution — analogous to the FALSE channel (binary, computational, zero INDETERMINATE)
- **`padicValNat` API** = the ν₂ tool — analogous to measuring INDETERMINATE depth in ℤ₂
- **`sorry` stubs** = INDETERMINATE cells — regions of the proof tree not yet resolved (TRUE/FALSE undetermined)
- **Complete main theorem** = Myrion Resolution at the key node — the INDETERMINATE resolves to TRUE

The proof "looks like" the Collatz conjecture itself: local arithmetic (omega) resolves the individual steps, while the global convergence requires additional invariants.

---

*Corpus Entry #192. Lean 4 source: `lean4_collatz/CollatzNu2.lean`. DOI: pending. Apache 2.0.*
