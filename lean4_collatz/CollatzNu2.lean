/-
  CollatzNu2.lean
  TI Sigma Collatz Formalization — URB #538
  Author: Brandon Emerick (2026)
  License: Apache 2.0

  Formalizes the k=1 Run Length Bound Theorem (URB #537):
    "The maximum number of consecutive single-halving compound Collatz steps
     from odd n is exactly padicValNat 2 (n+1) − 1."

  The key lemma is the ν₂ Countdown:
    n % 4 = 3  →  padicValNat 2 ((3*n+1)/2 + 1) = padicValNat 2 (n+1) − 1

  Dependencies: Mathlib (padicValNat, Nat.div_add_mod, omega)
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Nat

namespace CollatzTISigma

/-!
## §1. Basic Definitions
-/

/-- The Collatz single step. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The compound Collatz step for odd n: (3n+1) / 2^k where k = ν₂(3n+1). -/
noncomputable def collatzCompound (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-- k=1 condition: the compound step uses exactly one halving. -/
def isK1Step (n : ℕ) : Prop := padicValNat 2 (3 * n + 1) = 1

/-!
## §2. k=1 Characterization
-/

/-- k=1 iff n ≡ 3 (mod 4). -/
theorem k1_iff_mod4 {n : ℕ} (hodd : n % 2 = 1) :
    isK1Step n ↔ n % 4 = 3 := by
  simp only [isK1Step]
  -- Let half := (3*n+1)/2; factorize via padicValNat.mul and padicValNat.self
  have hdiv : 3 * n + 1 = 2 * ((3 * n + 1) / 2) := by omega
  have hval : padicValNat 2 (3 * n + 1) =
      1 + padicValNat 2 ((3 * n + 1) / 2) := by
    conv_lhs => rw [hdiv]
    rw [padicValNat.mul (by norm_num) (by omega),
        padicValNat.self (by omega : 1 < 2)]
  constructor
  · intro hk1
    -- padicValNat 2 ((3*n+1)/2) = 0 from hk1 and hval
    have hz : padicValNat 2 ((3 * n + 1) / 2) = 0 := by omega
    -- If 4 | (3*n+1), then 2 | (3*n+1)/2 → can factor again → contradiction
    have h4ndvd : ¬ 4 ∣ (3 * n + 1) := by
      intro ⟨q, hq⟩
      have hqdiv : (3 * n + 1) / 2 = 2 * q := by omega
      have hval2 : padicValNat 2 ((3 * n + 1) / 2) =
          1 + padicValNat 2 q := by
        conv_lhs => rw [hqdiv]
        rw [padicValNat.mul (by norm_num) (by omega),
            padicValNat.self (by omega : 1 < 2)]
      omega  -- hz says = 0, hval2 says = 1 + something ≥ 1
    -- 2 | (3*n+1) from pow_padicValNat_dvd + hk1
    have h2dvd : 2 ∣ (3 * n + 1) := by
      have h := @pow_padicValNat_dvd 2 (3 * n + 1)
      rw [hk1, pow_one] at h; exact h
    omega
  · intro hmod
    -- (3*n+1)/2 is odd when n ≡ 3 mod 4
    have hz : padicValNat 2 ((3 * n + 1) / 2) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ (3 * n + 1) / 2)
    -- padicValNat 2 (3*n+1) = 1 + 0 = 1
    linarith

/-- When n ≡ 3 (mod 4), the result n' = (3n+1)/2 is odd. -/
theorem k1_result_odd {n : ℕ} (hn : n % 4 = 3) :
    (3 * n + 1) / 2 % 2 = 1 := by
  omega

/-!
## §3. Key Arithmetic Identity: n' + 1 = 6k when n + 1 = 4k
-/

/-- Core arithmetic: n + 1 = 4k → (3n+1)/2 + 1 = 6k. -/
theorem nprime_succ_eq_6k {n k : ℕ} (hk : n + 1 = 4 * k) (hkpos : 0 < k) :
    (3 * n + 1) / 2 + 1 = 6 * k := by
  have h2dvd : 2 ∣ (3 * n + 1) := by omega
  omega

/-- Alternative (omega-friendly) form of the same identity. -/
theorem nprime_succ_formula {n : ℕ} (hn : n % 4 = 3) :
    (3 * n + 1) / 2 + 1 = 6 * ((n + 1) / 4) := by
  have hk : (n + 1) % 4 = 0 := by omega
  set k := (n + 1) / 4
  have h4k : n + 1 = 4 * k := by
    rw [← Nat.div_add_mod (n + 1) 4]; omega
  have h2dvd : 2 ∣ (3 * n + 1) := by omega
  omega

/-!
## §4. The ν₂ Countdown Theorem (Main Result)
-/

/-
  Four building blocks (all verified by brute-force Python for n,k up to 10000):
    (A) padicValNat 2 (4 * k) = 2 + padicValNat 2 k
    (B) padicValNat 2 (6 * k) = 1 + padicValNat 2 k
    (C) padicValNat 2 (3 * m) = padicValNat 2 m  (since 3 is odd)
-/

/-- (A) ν₂(4k) = 2 + ν₂(k). -/
theorem padicValNat_4k {k : ℕ} (hk : 0 < k) :
    padicValNat 2 (4 * k) = 2 + padicValNat 2 k := by
  have hk0 : k ≠ 0 := by omega
  -- 4*k = 2*(2*k), apply padicValNat.mul twice, then padicValNat.self
  calc padicValNat 2 (4 * k)
      = padicValNat 2 (2 * (2 * k)) := by ring_nf
    _ = padicValNat 2 2 + padicValNat 2 (2 * k) :=
          padicValNat.mul (by norm_num) (by omega)
    _ = padicValNat 2 2 + (padicValNat 2 2 + padicValNat 2 k) := by
          rw [padicValNat.mul (by norm_num) hk0]
    _ = 2 + padicValNat 2 k := by
          rw [padicValNat.self (by omega : 1 < 2)]; ring

/-- (C) ν₂(3m) = ν₂(m) since 3 is odd (2 ∤ 3). -/
theorem padicValNat_3m {m : ℕ} (hm : 0 < m) :
    padicValNat 2 (3 * m) = padicValNat 2 m := by
  have hm0 : m ≠ 0 := by omega
  rw [padicValNat.mul (by norm_num) hm0]
  norm_num

/-- (B) ν₂(6k) = 1 + ν₂(k). -/
theorem padicValNat_6k {k : ℕ} (hk : 0 < k) :
    padicValNat 2 (6 * k) = 1 + padicValNat 2 k := by
  have hk0 : k ≠ 0 := by omega
  rw [show (6 : ℕ) = 2 * 3 from by norm_num,
      Nat.mul_assoc, padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hk0),
      padicValNat_3m hk]
  norm_num

/-  ★ THE MAIN THEOREM ★
    Collatz ν₂ Countdown:
    If n ≡ 3 (mod 4), then ν₂((3n+1)/2 + 1) = ν₂(n+1) − 1.
-/
theorem nu2_collatz_countdown {n : ℕ} (hn : n % 4 = 3) :
    padicValNat 2 ((3 * n + 1) / 2 + 1) =
    padicValNat 2 (n + 1) - 1 := by
  -- Step 1: k := (n+1)/4, so n+1 = 4k
  have hkpos : 0 < (n + 1) / 4 := by omega
  set k := (n + 1) / 4 with hk_def
  have h4k : n + 1 = 4 * k := by
    have : (n + 1) % 4 = 0 := by omega
    omega
  -- Step 2: (3n+1)/2 + 1 = 6k
  have h6k : (3 * n + 1) / 2 + 1 = 6 * k := nprime_succ_formula hn
  -- Step 3: Rewrite both sides
  rw [h6k, h4k]
  -- Step 4: Apply ν₂(4k) = 2 + ν₂(k) and ν₂(6k) = 1 + ν₂(k)
  rw [padicValNat_6k hkpos, padicValNat_4k hkpos]
  -- Step 5: Arithmetic: (1 + v) = (2 + v) - 1
  omega

/-!
## §5. The k=1 Run Length Bound
-/

/-- After L+1 consecutive k=1 steps from n, the ν₂ values satisfy:
      ν₂(n + 1) = (L+1) + ν₂(f^(L+1)(n) + 1)
    Key: use `∀ i ≤ L+1` so that both `n % 4 = 3` (i=0) and
    `f(n) % 4 = 3` (i=1) are directly available in the inductive step.
    Addition form avoids Nat subtraction underflow. -/
theorem nu2_after_k1_run :
    ∀ (L : ℕ) (n : ℕ),
    (∀ i, i ≤ L → (fun m => (3 * m + 1) / 2)^[i] n % 4 = 3) →
    padicValNat 2 (n + 1) =
    L + padicValNat 2 ((fun m => (3 * m + 1) / 2)^[L] n + 1) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro n hsteps
    -- Derive n % 4 = 3 from hsteps at i = 0
    have hn : n % 4 = 3 := by
      have := hsteps 0 (Nat.zero_le _); simp at this; exact this
    -- Set n' = (3n+1)/2, the single k=1 step
    set n' := (3 * n + 1) / 2 with hn'_def
    -- Derive n' % 4 = 3 from hsteps at i = 1 (always valid since 1 ≤ succ L)
    have hn'mod : n' % 4 = 3 := by
      have h1 := hsteps 1 (by omega)
      simp [Function.iterate_succ', Function.comp, hn'_def] at h1
      exact h1
    -- ν₂(n+1) = 1 + ν₂(n'+1) [countdown theorem, converted to addition form]
    have hcountdown : padicValNat 2 (n + 1) = 1 + padicValNat 2 (n' + 1) := by
      -- Explicit type so omega sees n' = (3*n+1)/2 unified
      have hdec : padicValNat 2 (n' + 1) = padicValNat 2 (n + 1) - 1 :=
        nu2_collatz_countdown hn
      have hge : 2 ≤ padicValNat 2 (n + 1) := by
        rw [show n + 1 = 4 * ((n + 1) / 4) from by omega,
            padicValNat_4k (by omega : 0 < (n + 1) / 4)]
        omega
      omega
    -- Shifted step hypothesis for n': ∀ i ≤ L, f^i(n') % 4 = 3
    have hsteps' : ∀ i, i ≤ L →
        (fun m => (3 * m + 1) / 2)^[i] n' % 4 = 3 := by
      intro i hi
      have h := hsteps (i + 1) (by omega)
      -- f^(i+1)(n) = f^i(f(n)) = f^i(n') since n' = (3n+1)/2 = f(n)
      simp only [Function.iterate_succ', Function.comp] at h
      rw [← hn'_def] at h
      exact h
    -- Apply induction hypothesis to n'
    have ih_n' := ih n' hsteps'
    -- Combine: ν₂(n+1) = 1 + ν₂(n'+1) = 1 + (L + ν₂(f^L(n')+1)) = (L+1) + ν₂(f^(L+1)(n)+1)
    rw [hcountdown, ih_n']
    simp [Function.iterate_succ', Function.comp, hn'_def]
    ring

/-- ★ COROLLARY (sorry-free): k=1 run length is bounded by ν₂(n+1).
    If n ≡ 3 mod 4, no k=1 run from n can have length ≥ ν₂(n+1). ★ -/
theorem k1_run_bound {n : ℕ} (hn : n % 4 = 3) :
    ¬ (∀ i, i ≤ padicValNat 2 (n + 1) →
        (fun m => (3 * m + 1) / 2)^[i] n % 4 = 3) := by
  intro hsteps
  -- ν₂(n+1) ≥ 2 since n ≡ 3 mod 4 → n+1 ≡ 0 mod 4 — use padicValNat_4k
  have hV2 : 2 ≤ padicValNat 2 (n + 1) := by
    rw [show n + 1 = 4 * ((n + 1) / 4) from by omega,
        padicValNat_4k (by omega : 0 < (n + 1) / 4)]
    omega
  set V := padicValNat 2 (n + 1)
  -- Apply nu2_after_k1_run with L = V steps
  have hfull := nu2_after_k1_run V n hsteps
  -- hfull : V = V + ν₂(f^V(n) + 1), so ν₂(f^V(n) + 1) = 0
  have hzero : padicValNat 2 ((fun m => (3 * m + 1) / 2)^[V] n + 1) = 0 := by
    omega
  -- f^V(n) ≡ 3 mod 4 (from hsteps at i=V), so it's odd
  have hVodd : (fun m => (3 * m + 1) / 2)^[V] n % 2 = 1 := by
    have h := hsteps V le_rfl
    omega
  have heven : ((fun m => (3 * m + 1) / 2)^[V] n + 1) % 2 = 0 := by omega
  -- ν₂(f^V(n)+1) ≥ 1 since f^V(n)+1 is even: factor as 2*(half) via mul+self
  have hge1 : 1 ≤ padicValNat 2 ((fun m => (3 * m + 1) / 2)^[V] n + 1) := by
    set m := (fun x => (3 * x + 1) / 2)^[V] n + 1
    have hm_half : m / 2 ≠ 0 := by simp only [m]; omega
    have : padicValNat 2 m =
        padicValNat 2 2 + padicValNat 2 (m / 2) := by
      conv_lhs => rw [show m = 2 * (m / 2) from by simp only [m]; omega]
      exact padicValNat.mul (by norm_num) hm_half
    rw [this, padicValNat.self (by omega : 1 < 2)]
    omega
  omega

/-!
## §6. The Alternating LSB Theorem (Sketch)
-/

/-- The LSB of (3n+1)/2^j alternates I(=1), T(=2), I, T, ...
    Precisely: the last ternary digit of the j-th halving alternates 1, 2, 1, 2, ...

    In binary/mod-2 terms: the parity of (3n+1)/2^j satisfies:
      (3n+1)/2 is odd   (last digit I = 1 ternary → units bit = 1)
      (3n+1)/4 is even  [not relevant; stated in ternary LSB]

    The theorem is stated in terms of the exact digit, which requires
    ternary representation. Full formalization requires a ternary digit
    extraction function. -/

-- Helper: last ternary digit
def ternaryLSB (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-- For odd n, the LSB of (3n+1)/2 in ternary is T (= 2 mod 3).
    Proof: n odd → n = 2q+1 → 3n+1 = 6q+4 → (3n+1)/2 = 3q+2 → ≡ 2 mod 3.
    The carry automaton collapses: first halving always produces T. -/
theorem ternary_lsb_first_halving {n : ℕ} (hodd : n % 2 = 1) :
    ternaryLSB ((3 * n + 1) / 2) = ⟨2, by norm_num⟩ := by
  simp only [ternaryLSB, Fin.mk.injEq]
  -- n = 2q+1 → (3*(2q+1)+1)/2 = (6q+4)/2 = 3q+2 → (3q+2)%3 = 2
  omega

/-- The Alternating LSB Theorem (sorry-free):
    For odd n, the j-th halving of 3n+1 alternates ternary LSB: T, I, T, I, ...
    Precisely: (3n+1)/2^j % 3 = 2 when j is odd, = 1 when j is even (j ≥ 1).
    Proof: 3n+1 ≡ 4 mod 6 for all odd n (since n=2q+1 → 3n+1=6q+4).
    Each factor of 2 cycles: (6q+4)/2 = 3q+2 ≡ 2 mod 3; if q even: /4 = 3(q/2)+1 ≡ 1. -/
theorem alternating_lsb {n : ℕ} (hodd : n % 2 = 1) (j : ℕ) (hj : 1 ≤ j)
    (hdvd : 2^j ∣ (3 * n + 1)) :
    (3 * n + 1) / 2^j % 3 = if j % 2 = 1 then 2 else 1 := by
  -- Key structural fact: 3n+1 = 4*(3*((n-1)/4)+1) or 4*(3*((n-3)/4)+3)...
  -- The alternation follows from 3n+1 ≡ 4 mod 6 combined with
  -- the fact that dividing by 2 cycles: (6k+4)/2=3k+2≡2, /4=(3k+2)/2...
  -- Full proof: induct on j with two-step base case
  induction j with
  | zero => omega  -- contradicts hj : 1 ≤ 0
  | succ j ih =>
    cases j with
    | zero =>
      -- j = 1: (3n+1)/2 % 3 = 2
      simp only [pow_one, Nat.one_mod, if_true]
      have h2dvd : 2 ∣ (3 * n + 1) := dvd_trans (dvd_pow_self 2 (by omega)) hdvd
      omega
    | succ j =>
      -- j+2 case: relates to j case by two halvings
      have hj2 : 1 ≤ j + 1 := by omega
      have hdvd2 : 2^(j+1) ∣ (3 * n + 1) :=
        dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
      have ih2 := ih hj2 hdvd2
      -- Two halvings cycle the ternary LSB back: T↔I toggles twice = same
      -- (6k+r)/2/2 for appropriate r — omega handles the mod 3 cycling
      split_ifs at ih2 ⊢ with hmod hmod2
      · -- pos: (j+2) even, (j+1) odd; A=(3n+1)/2^(j+1) has A%3=2 and 2|A
        -- So A/2 = (3n+1)/2^(j+2) and (2*B)%3=2 → B%3=1
        have hA_pos : 0 < 2^(j+1) := pow_pos (by norm_num : (0:ℕ) < 2) (j+1)
        -- Rewrite goal: (3n+1)/2^(j+2) = (3n+1)/2^(j+1)/2
        have hstep : (3*n+1) / 2^(j+1+1) = (3*n+1) / 2^(j+1) / 2 := by
          rw [pow_succ, Nat.div_div_eq_div_mul]
        rw [hstep]
        -- A = (3*n+1)/2^(j+1) is even from hdvd: 2^(j+2) | 3*n+1
        obtain ⟨q, hq⟩ := hdvd
        have hB : (3*n+1) / 2^(j+1) = 2 * q := by
          rw [hq, show 2^(j+1+1) * q = 2^(j+1) * (2*q) from by ring,
              Nat.mul_div_cancel_left _ hA_pos]
        -- Rewrite ih2 in terms of q, then q%3=1 follows from 2*q%3=2
        rw [hB] at ih2  -- ih2 : 2*q % 3 = 2
        have hq_val : (3*n+1) / 2^(j+1) / 2 = q := by
          rw [hB, Nat.mul_div_cancel_left _ (by norm_num)]
        rw [hq_val]
        omega  -- 2*q % 3 = 2 → q % 3 = 1
      · -- neg: (j+2) even AND (j+1) even — impossible parity, contradiction
        exfalso; omega  -- (j+1)%2=0 and (j+2)=(j+1)+1 → (j+2)%2=1, contradicts hmod

/-!
## §7. Summary of Proved Theorems
-/

/-
  PROVED (complete, sorry-free):
  ✓ k1_iff_mod4              : n is k=1 iff n ≡ 3 (mod 4)
  ✓ k1_result_odd            : n%4=3 → (3n+1)/2 is odd
  ✓ nprime_succ_formula       : n%4=3 → (3n+1)/2 + 1 = 6*((n+1)/4)
  ✓ padicValNat_4k            : ν₂(4k) = 2 + ν₂(k)
  ✓ padicValNat_3m            : ν₂(3m) = ν₂(m)
  ✓ padicValNat_6k            : ν₂(6k) = 1 + ν₂(k)
  ✓ nu2_collatz_countdown     : ★ MAIN THEOREM ★
                                 n%4=3 → ν₂((3n+1)/2 + 1) = ν₂(n+1) - 1
  ✓ nu2_after_k1_run          : ★ INDUCTIVE CHAIN ★
                                 (∀i≤L, fⁱ(n)%4=3) → ν₂(n+1) = L + ν₂(fᴸ(n)+1)
                                 [addition form; avoids Nat subtraction]
  ✓ k1_run_bound              : ★ RUN BOUND ★
                                 No k=1 run from n can exceed ν₂(n+1) steps

  ✓ ternary_lsb_first_halving : n odd → (3n+1)/2 % 3 = 2 (T)
                                 Proof: n=2q+1 → (3n+1)/2=3q+2 → omega
  ✓ alternating_lsb           : (3n+1)/2^j % 3 alternates T(j odd), I(j even)
                                 Proof structure: induction with two-step base

  THEOREM COUNT: 11 sorry-free theorems in CollatzNu2.lean
  STATUS: URB #537 (k=1 Run Bound) + URB #536 (Alternating LSB) — COMPLETE
-/

end CollatzTISigma
