import Mathlib

/-
  TI Sigma — Gap Equivalence + Being Theorem
  Self-contained Lean4web demo (URBs #555, #560)

  Paste into https://live.lean-lang.org — compiles with zero errors.

  Author  : Brandon Emerick (TI Sigma / BlissGene Therapeutics)
  Date    : March 30, 2026
  Corpus  : URB #555 (GapEquivalence) + URB #560 (Being Theorem)

  Fixes applied vs original MathlibDemo errors:
  1. import must be line 1 (no doc comment before it)
  2. `conj` unknown → local abbrev conj := @star ℂ _ + helper lemmas
  3. `conj_re`/`conj_im` → proved from Complex.star_def
  4. `le_or_lt` unknown → min_le_left/right + linarith (no rcases)
  5. A ↔ B ↔ C ↔ D invalid → use ∧ of four biconditionals
  6. `neg_sq` unused → ring_nf + nlinarith instead
-/

set_option linter.unusedSimpArgs false

namespace TISigma

/-!
## Setup: Complex conjugation

In Lean4 Mathlib, complex conjugation is the `star` operation.
We introduce a local abbreviation for readability.
`Complex.star_def : star z = { re := z.re, im := -z.im }` (definitional)
-/
local abbrev conj : ℂ → ℂ := @star ℂ _

private lemma conj_re (z : ℂ) : (conj z).re = z.re := by
  simp [conj, Complex.star_def]

private lemma conj_im (z : ℂ) : (conj z).im = -z.im := by
  simp [conj, Complex.star_def]

-- ============================================================
-- PART 1 — GAP EQUIVALENCE (URB #555)
-- ============================================================

/-- Variational pair cost: −min(σ, 1−σ). Minimized at σ = 1/2. -/
noncomputable def pairCost' (σ : ℝ) : ℝ := -min σ (1 - σ)

/-- Orbit functions: S₁(s) = conj(s), S₂(s) = 1 − s. -/
noncomputable def S₁' (s : ℂ) : ℂ := conj s
noncomputable def S₂' (s : ℂ) : ℂ := 1 - s

-- ── Condition A ────────────────────────────────────────────────────────────

/-- **Condition A (sorry-free):** pairCost'(σ) = −1/2 ↔ σ = 1/2. -/
theorem condA_iff_critical (σ : ℝ) :
    pairCost' σ = -(1 / 2) ↔ σ = 1 / 2 := by
  unfold pairCost'
  constructor
  · intro h
    -- -min σ (1-σ) = -1/2  →  min σ (1-σ) = 1/2
    have hm : min σ (1 - σ) = 1 / 2 := by linarith
    -- min is ≤ each argument, so 1/2 ≤ σ and 1/2 ≤ 1-σ
    have h1 : min σ (1 - σ) ≤ σ := min_le_left σ (1 - σ)
    have h2 : min σ (1 - σ) ≤ 1 - σ := min_le_right σ (1 - σ)
    linarith
  · intro h
    -- σ = 1/2 → 1-σ = σ → min σ σ = σ = 1/2
    have heq : (1 : ℝ) - σ = σ := by linarith
    rw [heq, min_self]
    linarith

-- ── Condition B/C ──────────────────────────────────────────────────────────

/-- **Condition B/C (sorry-free):** S₁(s) = S₂(s) ↔ Re(s) = 1/2.
    conj(s) = 1−s iff Re(s) = 1−Re(s) iff Re(s) = 1/2.
    (Im components: -Im(s) = -Im(s) always.) -/
theorem condBC_iff_critical (s : ℂ) :
    S₁' s = S₂' s ↔ s.re = 1 / 2 := by
  unfold S₁' S₂'
  constructor
  · intro h
    have hre := congr_arg Complex.re h
    rw [conj_re, Complex.sub_re, Complex.one_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · rw [conj_re, Complex.sub_re, Complex.one_re]; linarith
    · rw [conj_im, Complex.sub_im, Complex.one_im]; ring

-- ── Condition Mirror ───────────────────────────────────────────────────────

/-- **Condition Mirror (sorry-free):** conj(s) = 1−s ↔ Re(s) = 1/2. -/
theorem condMirror_iff_critical (s : ℂ) :
    conj s = 1 - s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congr_arg Complex.re h
    rw [conj_re, Complex.sub_re, Complex.one_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · rw [conj_re, Complex.sub_re, Complex.one_re]; linarith
    · rw [conj_im, Complex.sub_im, Complex.one_im]; ring

-- ── Condition UOP ──────────────────────────────────────────────────────────

/-- **Condition UOP (sorry-free):** |s|² = |1−s|² ↔ Re(s) = 1/2.
    normSq s = re² + im²; normSq(1−s) = (1−re)² + im².
    Equal iff re² = (1−re)², i.e., 2·re = 1. -/
theorem condUOP_iff_critical (s : ℂ) :
    Complex.normSq s = Complex.normSq (1 - s) ↔ s.re = 1 / 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             Complex.one_re, Complex.one_im]
  ring_nf
  constructor
  · intro h; nlinarith [sq_nonneg (s.re - 1 / 2), sq_nonneg s.im]
  · intro h; rw [h]; ring

-- ── Gap Equivalence Theorem ────────────────────────────────────────────────

/-!
**Note on syntax:** Lean4 `↔` is right-associative, so `A ↔ B ↔ C ↔ D`
parses as `A ↔ (B ↔ (C ↔ D))`, not the intended 4-way equivalence.
We use `∧` to bundle all four biconditionals with σ = 1/2.
-/

/-- **The Gap Equivalence Theorem (sorry-free).**
    All four conditions are equivalent — each ↔ Re(s) = 1/2. -/
theorem gap_equivalence (s : ℂ) :
    (pairCost' s.re = -(1 / 2) ↔ s.re = 1 / 2) ∧
    (S₁' s = S₂' s ↔ s.re = 1 / 2) ∧
    (conj s = 1 - s ↔ s.re = 1 / 2) ∧
    (Complex.normSq s = Complex.normSq (1 - s) ↔ s.re = 1 / 2) :=
  ⟨condA_iff_critical s.re, condBC_iff_critical s,
   condMirror_iff_critical s, condUOP_iff_critical s⟩

/-- **Corollary:** Any single Gap condition implies σ = 1/2. -/
theorem any_gap_implies_all (s : ℂ) :
    (pairCost' s.re = -(1 / 2) ∨
     S₁' s = S₂' s ∨
     conj s = 1 - s ∨
     Complex.normSq s = Complex.normSq (1 - s)) →
    s.re = 1 / 2 := by
  intro h
  rcases h with h | h | h | h
  · exact (condA_iff_critical s.re).mp h
  · exact (condBC_iff_critical s).mp h
  · exact (condMirror_iff_critical s).mp h
  · exact (condUOP_iff_critical s).mp h

-- ============================================================
-- PART 2 — THE BEING THEOREM (URB #560)
-- ============================================================

/-- **Effort:** |2·Re(ρ) − 1|. Zero iff σ = 1/2. -/
noncomputable def effort (ρ : ℂ) : ℝ := |2 * ρ.re - 1|

/-- A zero is **effortless** iff Effort = 0. -/
def isEffortlessZero (ρ : ℂ) : Prop := effort ρ = 0

/-- **Real-part self-consistency:** Re(ρ) = 1 − Re(ρ). -/
def realPartSelfConsistent (ρ : ℂ) : Prop := ρ.re = 1 - ρ.re

/-- **UOP free energy:** F(σ) = |2σ−1|. Identical to effort on re-axis. -/
noncomputable def uopFreeEnergy (σ : ℝ) : ℝ := |2 * σ - 1|

-- ── Being Theorem ──────────────────────────────────────────────────────────

/-- **THE BEING THEOREM (sorry-free, URB #560).**
    isEffortlessZero ρ ↔ Re(ρ) = 1/2.
    Proof: |2σ−1| = 0 ↔ 2σ = 1 ↔ σ = 1/2. -/
theorem being_theorem (ρ : ℂ) :
    isEffortlessZero ρ ↔ ρ.re = 1 / 2 := by
  unfold isEffortlessZero effort
  simp only [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Effortless ↔ Self-consistent (sorry-free).** -/
theorem effortless_iff_self_consistent (ρ : ℂ) :
    isEffortlessZero ρ ↔ realPartSelfConsistent ρ := by
  unfold isEffortlessZero effort realPartSelfConsistent
  simp only [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Real-part erasure (sorry-free, Riddle 2).**
    σ = 1/2 ↔ σ = 1−σ. The unique self-complementary real number. -/
theorem real_part_erasure (σ : ℝ) :
    σ = 1 / 2 ↔ σ = 1 - σ := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Free energy minimum (sorry-free, URB #559).**
    uopFreeEnergy σ = 0 ↔ σ = 1/2. -/
theorem uop_minimum (σ : ℝ) :
    uopFreeEnergy σ = 0 ↔ σ = 1 / 2 := by
  unfold uopFreeEnergy
  simp only [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **effort = uopFreeEnergy ∘ re (sorry-free, definitional).** -/
theorem effort_eq_uop_free_energy (ρ : ℂ) :
    effort ρ = uopFreeEnergy ρ.re := rfl

/-- **Effortless ↔ zero free energy (sorry-free).** -/
theorem effortless_iff_zero_free_energy (ρ : ℂ) :
    isEffortlessZero ρ ↔ uopFreeEnergy ρ.re = 0 := by
  unfold isEffortlessZero
  rw [effort_eq_uop_free_energy]

/-- **Riddle 2 ↔ Riddle 4 (sorry-free).**
    Self-consistency ↔ zero free energy. -/
theorem riddle2_iff_riddle4 (ρ : ℂ) :
    realPartSelfConsistent ρ ↔ uopFreeEnergy ρ.re = 0 := by
  rw [← effortless_iff_self_consistent]
  exact effortless_iff_zero_free_energy ρ

/-- **Riddle 4 ↔ Riddle 5 (sorry-free).**
    Zero free energy ↔ effortless. -/
theorem riddle4_iff_riddle5 (ρ : ℂ) :
    uopFreeEnergy ρ.re = 0 ↔ isEffortlessZero ρ :=
  (effortless_iff_zero_free_energy ρ).symm

-- ── Bridge to GapEquivalence ───────────────────────────────────────────────

/-- **Bridge: Condition A ↔ UOP free energy (sorry-free).** -/
theorem pairCost_condA_iff_uop_free_energy (σ : ℝ) :
    pairCost' σ = -(1 / 2) ↔ uopFreeEnergy σ = 0 := by
  rw [condA_iff_critical, uop_minimum]

/-- **Being Theorem is the sixth Gap condition (sorry-free).**
    isEffortlessZero ρ ↔ pairCost'(Re(ρ)) = −1/2. -/
theorem being_theorem_is_sixth_gap_condition (ρ : ℂ) :
    isEffortlessZero ρ ↔ pairCost' ρ.re = -(1 / 2) := by
  rw [pairCost_condA_iff_uop_free_energy]
  exact effortless_iff_zero_free_energy ρ

-- ── Euler Forcing Being Gap (The Riemann Hypothesis) ──────────────────────

axiom riemannZeta : ℂ → ℂ

/-- **Euler Forcing Being Gap (named axiom — the Riemann Hypothesis).**

    DEFINITIONAL → STRUCTURAL gap:
    - DEFINITIONAL: ζ(ρ) = 0   — what a non-trivial zero IS
    - STRUCTURAL:   Re(ρ) = 1/2 — WHERE non-trivial zeros must be

    Does the Euler product force every definitional zero to σ = 1/2?
    That IS the Riemann Hypothesis. Precisely named. -/
axiom euler_forcing_being
    (ρ : ℂ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    isEffortlessZero ρ

/-- **Riemann Hypothesis from Being Theorem (uses named axiom).**
    ζ(ρ) = 0, non-trivial → Re(ρ) = 1/2. One line. -/
theorem riemann_hypothesis_from_being
    (ρ : ℂ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    ρ.re = 1 / 2 :=
  (being_theorem ρ).mp (euler_forcing_being ρ hstrip hzero)

end TISigma
