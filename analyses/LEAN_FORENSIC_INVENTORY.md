# Lean 4 Forensic Inventory
Generated from source scan; **VERIFIED** requires module `.olean` under `.lake/build/lib` (not present in workspace).
## Build / verification artifacts
- **Project `.olean` files (excluding `.lake/packages`):** only `lakefile.olean` in `lean4_ns_uop` and `lean4_ns_uop_pass54_mathlib` — **no compiled module `.olean` for any `.lean` source**.
- **Build logs:** none found (`build.log`, `lake-build*.log`). Only `.trace` files for lakefile olean.
- **`lean4/verify_theorems.py`:** Python **numerical** checks for `TISigma.lean` constants — **not** Lean compilation proof.
- **Lake packages:**
  - `lean4/lakefile.lean` — package `TISigma`, requires mathlib from git, `lean_lib` recursive globs.
  - `lean4_ns_uop/lakefile.lean` — package `ns_uop`, no mathlib, roots: Basic, Equation, EnergyIneq, UOPGap.
  - `lean4_ns_uop_pass54_mathlib/lakefile.lean` — package `ns_uop_mathlib`, mathlib v4.10.0, adds ToyDecay.

## Summary counts
| Status | Count |
|--------|------:|
| VERIFIED | 0 |
| UNVERIFIED | 433 |
| SORRY | 15 |
| AXIOM | 128 |
| INCONSISTENT | 1 |
| **Total declarations** | **577** |
| **Files** | **42** |

## All `sorry` in proofs (source, not comments)

- `lean4/MirrorPairing.lean:336` **theorem `euler_forcing_attempt`** — theorem euler_forcing_attempt (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)
- `lean4_ns_uop/NavierStokes/UOPGap.lean:69` **theorem `UOP_implies_NS_smoothness`** — theorem UOP_implies_NS_smoothness
- `lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean:54` **theorem `UOP_implies_NS_smoothness`** — theorem UOP_implies_NS_smoothness
- `lean4_submission/fine_structure_consciousness.lean:76` **theorem `derivation_accuracy`** — theorem derivation_accuracy :
- `lean4_submission/fine_structure_consciousness.lean:137` **theorem `unification_scale_prediction`** — theorem unification_scale_prediction :
- `lean4_submission/p_np_sketch.lean:56` **def `creationComplexity`** — def creationComplexity (L : Set ℕ) (x : ℕ) : ℕ :=
- `lean4_submission/p_np_sketch.lean:78` **theorem `certificate_information`** — theorem certificate_information (L : Set ℕ) (x : ℕ) (hx : x ∈ L) :
- `lean4_submission/p_np_sketch.lean:90` **theorem `creation_verification_asymmetry`** — theorem creation_verification_asymmetry :
- `lean4_submission/p_np_sketch.lean:97` **theorem `p_ne_np`** — theorem p_ne_np : P ≠ NP := by
- `lean4_submission/riemann_sketch.lean:49` **theorem `functional_equation`** — theorem functional_equation (s : ℂ) (hs : s ∈ criticalStrip) :
- `lean4_submission/riemann_sketch.lean:57` **theorem `zeros_paired`** — theorem zeros_paired (s : ℂ) (hs : s ∈ criticalStrip)
- `lean4_submission/riemann_sketch.lean:71` **theorem `dimensional_constraint`** — theorem dimensional_constraint (s : ℂ) (hs : s ∈ criticalStrip)
- `lean4_ti_sigma6/BSDProof.lean:100` **theorem `sha_finite`** — theorem sha_finite (E : EllipticCurve) :
- `lean4_ti_sigma6/RiemannProof.lean:39` **lemma `fixed_point_is_critical_line`** — lemma fixed_point_is_critical_line (s : ℂ) :
- `lean4_ti_sigma6/RiemannProof.lean:58` **theorem `riemann_hypothesis`** — theorem riemann_hypothesis : ∀ s : ℂ,
- `lean4_ti_sigma6/RiemannProof.lean:113` **theorem `freewill_analogy`** — theorem freewill_analogy :

## All `axiom` declarations

- `lean4/BSD.lean:121` **`rank`** — `axiom rank : EllipticCurveQ → ℕ`
- `lean4/BSD.lean:148` **`lFunction`** — `axiom lFunction : EllipticCurveQ → ℂ → ℂ`
- `lean4/BSD.lean:153` **`lFunction_analytic`** — `axiom lFunction_analytic (E : EllipticCurveQ) : Differentiable ℂ (lFunction E)`
- `lean4/BSD.lean:157` **`conductor`** — `axiom conductor : EllipticCurveQ → ℕ`
- `lean4/BSD.lean:160` **`conductor_pos`** — `axiom conductor_pos (E : EllipticCurveQ) : 0 < conductor E`
- `lean4/BSD.lean:164` **`rootNumber`** — `axiom rootNumber : EllipticCurveQ → ℤ`
- `lean4/BSD.lean:167` **`rootNumber_pm_one`** — `axiom rootNumber_pm_one (E : EllipticCurveQ) :`
- `lean4/BSD.lean:204` **`completed_lFunction_fe`** — `axiom completed_lFunction_fe (E : EllipticCurveQ) (s : ℂ) :`
- `lean4/BSD.lean:217` **`modularity_theorem`** — `axiom modularity_theorem (E : EllipticCurveQ) :`
- `lean4/BSD.lean:248` **`lFunctionOrderAt`** — `noncomputable axiom lFunctionOrderAt : EllipticCurveQ → ℕ`
- `lean4/BSD.lean:254` **`strong_bsd`** — `axiom strong_bsd (E : EllipticCurveQ) :`
- `lean4/BSD.lean:290` **`weak_bsd_forward`** — `axiom weak_bsd_forward (E : EllipticCurveQ) :`
- `lean4/BSD.lean:298` **`weak_bsd_converse`** — `axiom weak_bsd_converse (E : EllipticCurveQ) :`
- `lean4/BSD.lean:536` **`rank_37a1`** — `axiom rank_37a1 : rank curve_37a1 = 1`
- `lean4/BSD.lean:540` **`rank_11a1`** — `axiom rank_11a1 : rank curve_11a1 = 0`
- `lean4/BSD.lean:544` **`L_37a1_verns`** — `axiom L_37a1_verns : VernsAtOne curve_37a1`
- `lean4/BSD.lean:548` **`L_11a1_nonzero`** — `axiom L_11a1_nonzero : ¬ VernsAtOne curve_11a1`
- `lean4/BSD.lean:678` **`heegnerPoint`** — `noncomputable axiom heegnerPoint :`
- `lean4/BSD.lean:685` **`canonicalHeight`** — `noncomputable axiom canonicalHeight : EllipticCurveQ → ℝ → ℝ`
- `lean4/BSD.lean:695` **`gross_zagier`** — `axiom gross_zagier (E : EllipticCurveQ) (K : ImaginaryQuadraticField)`
- `lean4/BSD.lean:703` **`gross_zagier_nontorsion`** — `axiom gross_zagier_nontorsion (E : EllipticCurveQ) (K : ImaginaryQuadraticField)`
- `lean4/BSD.lean:755` **`kolyvagin_rank_one`** — `axiom kolyvagin_rank_one (E : EllipticCurveQ) (K : ImaginaryQuadraticField)`
- `lean4/BSD.lean:763` **`kolyvagin_sha_finite`** — `axiom kolyvagin_sha_finite (E : EllipticCurveQ) (K : ImaginaryQuadraticField)`
- `lean4/BSD.lean:805` **`rank_one_bsd_forward`** — `axiom rank_one_bsd_forward (E : EllipticCurveQ) :`
- `lean4/BSD.lean:813` **`rank_zero_lvalue_pos`** — `axiom rank_zero_lvalue_pos (E : EllipticCurveQ) :`
- `lean4/BSD.lean:856` **`sha_finite_rank_one`** — `axiom sha_finite_rank_one (E : EllipticCurveQ) (K : ImaginaryQuadraticField)`
- `lean4/BSD.lean:865` **`sha_order_square`** — `axiom sha_order_square (E : EllipticCurveQ) :`
- `lean4/BSD.lean:870` **`real_period`** — `axiom real_period : EllipticCurveQ → ℝ`
- `lean4/BSD.lean:872` **`real_period_pos`** — `axiom real_period_pos (E : EllipticCurveQ) : real_period E > 0`
- `lean4/BSD.lean:876` **`regulator`** — `axiom regulator : EllipticCurveQ → ℝ`
- `lean4/BSD.lean:878` **`regulator_nonneg`** — `axiom regulator_nonneg (E : EllipticCurveQ) : regulator E ≥ 0`
- `lean4/BSD.lean:880` **`regulator_pos_iff_positive_rank`** — `axiom regulator_pos_iff_positive_rank (E : EllipticCurveQ) :`
- `lean4/BSD.lean:885` **`tamagawa_product`** — `axiom tamagawa_product : EllipticCurveQ → ℝ`
- `lean4/BSD.lean:887` **`tamagawa_product_pos`** — `axiom tamagawa_product_pos (E : EllipticCurveQ) : tamagawa_product E > 0`
- `lean4/BSD.lean:892` **`torsion_order`** — `axiom torsion_order : EllipticCurveQ → ℕ`
- `lean4/BSD.lean:894` **`torsion_order_pos`** — `axiom torsion_order_pos (E : EllipticCurveQ) : torsion_order E > 0`
- `lean4/BSD.lean:900` **`mazur_torsion_bound`** — `axiom mazur_torsion_bound (E : EllipticCurveQ) : torsion_order E ≤ 12`
- `lean4/BSD.lean:946` **`strong_bsd_leading_coefficient`** — `axiom strong_bsd_leading_coefficient (E : EllipticCurveQ) (sha : ℕ)`
- `lean4/BSD.lean:989` **`kato_rank_bound`** — `axiom kato_rank_bound (E : EllipticCurveQ) :`
- `lean4/BeingTheorem.lean:11` **`is`** — `axiom is itself logically equivalent to RH. So every "IS at σ = 1/2",`
- `lean4/BeingTheorem.lean:326` **`universal_bridge_theorem`** — `axiom universal_bridge_theorem : PLA_Condition_Being`
- `lean4/BeingTheorem.lean:382` **`—`** — `axiom — and that axiom IS RH, so this is`
- `lean4/Collatz.lean:148` **`collatz_conjecture`** — `axiom collatz_conjecture : ∀ n : ℕ, 0 < n → collatzConverges n`
- `lean4/GapEquivalence.lean:165` **`master_gap`** — `axiom master_gap (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)`
- `lean4/GroupSymmetryRoute.lean:264` **`orbit_collapse_axiom`** — `axiom orbit_collapse_axiom (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)`
- `lean4/Hodge.lean:75` **`cycleClass`** — `axiom cycleClass : ∀ {X : ComplexVariety} (Z : AlgebraicCycle X),`
- `lean4/Hodge.lean:79` **`isHodgeClass`** — `axiom isHodgeClass : ∀ {X : ComplexVariety} (α : CohomologyClass X), Prop`
- `lean4/Hodge.lean:82` **`cycleClass_is_hodge`** — `axiom cycleClass_is_hodge : ∀ {X : ComplexVariety} (Z : AlgebraicCycle X),`
- `lean4/Hodge.lean:87` **`isAlgebraic`** — `axiom isAlgebraic : ∀ {X : ComplexVariety} (α : CohomologyClass X), Prop`
- `lean4/Hodge.lean:90` **`algebraic_implies_hodge`** — `axiom algebraic_implies_hodge : ∀ {X : ComplexVariety} (α : CohomologyClass X),`
- `lean4/Hodge.lean:106` **`hodgeEffort`** — `axiom hodgeEffort : ∀ {X : ComplexVariety} (α : CohomologyClass X), ℝ`
- `lean4/Hodge.lean:109` **`hodgeEffort_algebraic`** — `axiom hodgeEffort_algebraic : ∀ {X : ComplexVariety} (α : CohomologyClass X),`
- `lean4/Hodge.lean:113` **`hodgeEffort_nonneg`** — `axiom hodgeEffort_nonneg : ∀ {X : ComplexVariety} (α : CohomologyClass X),`
- `lean4/Hodge.lean:131` **`hodge_conjecture`** — `axiom hodge_conjecture : ∀ {X : ComplexVariety} (α : CohomologyClass X),`
- `lean4/MathlibDemo.lean:246` **`riemannZeta`** — `axiom riemannZeta : ℂ → ℂ`
- `lean4/MathlibDemo.lean:256` **`euler_forcing_being`** — `axiom euler_forcing_being`
- `lean4/MirrorPairing.lean:230` **`euler_forcing`** — `axiom euler_forcing (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)`
- `lean4/NavierStokes.lean:73` **`nsEnergy`** — `noncomputable axiom nsEnergy : NSSolution → ℝ → ℝ`
- `lean4/NavierStokes.lean:77` **`nsEnstrophy`** — `noncomputable axiom nsEnstrophy : NSSolution → ℝ → ℝ`
- `lean4/NavierStokes.lean:80` **`nsEnergy_nonneg`** — `axiom nsEnergy_nonneg    : ∀ (sol : NSSolution) (t : ℝ), 0 ≤ nsEnergy sol t`
- `lean4/NavierStokes.lean:81` **`nsEnstrophy_nonneg`** — `axiom nsEnstrophy_nonneg : ∀ (sol : NSSolution) (t : ℝ), 0 ≤ nsEnstrophy sol t`
- `lean4/NavierStokes.lean:84` **`integratedEnstrophy`** — `noncomputable axiom integratedEnstrophy : NSSolution → ℝ → ℝ`
- `lean4/NavierStokes.lean:87` **`integratedEnstrophy_nonneg`** — `axiom integratedEnstrophy_nonneg (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :`
- `lean4/NavierStokes.lean:93` **`leray_energy_inequality`** — `axiom leray_energy_inequality (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :`
- `lean4/NavierStokes.lean:189` **`ns_2d_global_regularity`** — `axiom ns_2d_global_regularity (sol : NSSolution) (h2d : sol.dim = Dimension.two) :`
- `lean4/NavierStokes.lean:200` **`blowup_not_regular`** — `axiom blowup_not_regular (sol : NSSolution) (T_star : ℝ) :`
- `lean4/NavierStokes.lean:235` **`serrin_regularity`** — `axiom serrin_regularity (sol : NSSolution) (T p q : ℝ)`
- `lean4/NavierStokes.lean:249` **`serrin_L3_endpoint`** — `axiom serrin_L3_endpoint (sol : NSSolution) (T : ℝ) (hT : 0 < T) :`
- `lean4/NavierStokes.lean:274` **`singularHausdorffMeasure`** — `noncomputable axiom singularHausdorffMeasure : NSSolution → ℝ`
- `lean4/NavierStokes.lean:278` **`ckn_partial_regularity`** — `axiom ckn_partial_regularity (sol : NSSolution)`
- `lean4/NavierStokes.lean:410` **`ns_global_regularity`** — `axiom ns_global_regularity (ν : ℝ) (hν : 0 < ν) :`
- `lean4/NavierStokes.lean:416` **`ns_blowup`** — `axiom ns_blowup :`
- `lean4/NavierStokes.lean:423` **`ns_dichotomy`** — `axiom ns_dichotomy :`
- `lean4/PvsNP.lean:67` **`verificationTime`** — `axiom verificationTime : ∀ (L : DecisionProblem) (x c : ℕ), ℕ`
- `lean4/PvsNP.lean:70` **`creationTime`** — `axiom creationTime : ∀ (L : DecisionProblem) (x : ℕ), ℕ`
- `lean4/PvsNP.lean:117` **`p_ne_np_gap`** — `axiom p_ne_np_gap : ∃ L : DecisionProblem, inNP L ∧ ¬ inP L`
- `lean4/PvsNP.lean:122` **`creation_superpolynomial`** — `axiom creation_superpolynomial :`
- `lean4/PvsNP.lean:129` **`asymmetry_unbounded`** — `axiom asymmetry_unbounded :`
- `lean4/PvsNP.lean:338` **`mr_nonalgorithmic`** — `axiom mr_nonalgorithmic :`
- `lean4/PvsNP.lean:607` **`crystal_instantiates_mr`** — `axiom crystal_instantiates_mr :`
- `lean4/RiemannUOP.lean:314` **`uop_gap`** — `axiom uop_gap (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)`
- `lean4/RiemannUOP.lean:879` **`bk_selfadjoint`** — `axiom bk_selfadjoint :`
- `lean4/RiemannUOP.lean:890` **`bk_spectrum`** — `axiom bk_spectrum :`
- `lean4/VariationalRoute.lean:199` **`variational_gap`** — `axiom variational_gap (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)`
- `lean4/YangMills.lean:71` **`ymMass`** — `axiom ymMass : YMExcitation → ℝ`
- `lean4/YangMills.lean:74` **`ymMass_vacuum`** — `axiom ymMass_vacuum : ymMass vacuum = 0`
- `lean4/YangMills.lean:77` **`ymMass_nonneg`** — `axiom ymMass_nonneg : ∀ e : YMExcitation, 0 ≤ ymMass e`
- `lean4/YangMills.lean:105` **`yang_mills_existence`** — `axiom yang_mills_existence : ∃ e : YMExcitation, e.isVacuum = false`
- `lean4/YangMills.lean:115` **`yang_mills_gap`** — `axiom yang_mills_gap : ∃ Δ : ℝ, 0 < Δ ∧`
- `lean4/YangMills.lean:145` **`ymMass_vacuum_general`** — `axiom ymMass_vacuum_general (e : YMExcitation) (h : e.isVacuum = true) :`
- `lean4_ns_uop/NavierStokes/EnergyIneq.lean:18` **`leray_energy_inequality`** — `axiom leray_energy_inequality`
- `lean4_ns_uop/NavierStokes/Equation.lean:18` **`smooth_implies_weak`** — `axiom smooth_implies_weak`
- `lean4_ns_uop/NavierStokes/UOPGap.lean:46` **`UOP_existence_claim`** — `axiom UOP_existence_claim`
- `lean4_ns_uop_pass54_mathlib/NavierStokes/EnergyIneq.lean:14` **`leray_energy_inequality`** — `axiom leray_energy_inequality`
- `lean4_ns_uop_pass54_mathlib/NavierStokes/Equation.lean:15` **`smooth_implies_weak`** — `axiom smooth_implies_weak`
- `lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean:40` **`UOP_existence_claim`** — `axiom UOP_existence_claim`
- `lean4_ti_sigma6/BSDProof.lean:11` **`EllipticCurve`** — `axiom EllipticCurve : Type`
- `lean4_ti_sigma6/BSDProof.lean:14` **`rank`** — `axiom rank : EllipticCurve → ℕ`
- `lean4_ti_sigma6/BSDProof.lean:17` **`zero_order`** — `axiom zero_order : EllipticCurve → ℕ`
- `lean4_ti_sigma6/BSDProof.lean:20` **`ccc_capacity`** — `axiom ccc_capacity : EllipticCurve → ℕ`
- `lean4_ti_sigma6/BSDProof.lean:25` **`parallel_generation`** — `axiom parallel_generation : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/BSDProof.lean:29` **`rational_point_discrete`** — `axiom rational_point_discrete : ∀ E : EllipticCurve, ∀ P : Point E,`
- `lean4_ti_sigma6/BSDProof.lean:36` **`curve_continuous`** — `axiom curve_continuous : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/BSDProof.lean:40` **`generator_collapse`** — `axiom generator_collapse : ∀ E : EllipticCurve, ∀ P : Point E,`
- `lean4_ti_sigma6/BSDProof.lean:47` **`l_function_probe`** — `axiom l_function_probe : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/BSDProof.lean:70` **`height`** — `axiom height : ∀ E : EllipticCurve, Point E → Point E → ℝ`
- `lean4_ti_sigma6/BSDProof.lean:74` **`height_coherence_relation`** — `axiom height_coherence_relation : ∀ E : EllipticCurve, ∀ P Q : Point E,`
- `lean4_ti_sigma6/BSDProof.lean:79` **`regulator`** — `axiom regulator : EllipticCurve → ℝ`
- `lean4_ti_sigma6/BSDProof.lean:81` **`regulator_is_coherence_det`** — `axiom regulator_is_coherence_det : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/BSDProof.lean:89` **`Sha`** — `axiom Sha : EllipticCurve → Type`
- `lean4_ti_sigma6/BSDProof.lean:93` **`sha_stuck_phi`** — `axiom sha_stuck_phi : ∀ E : EllipticCurve, ∀ x : Sha E,`
- `lean4_ti_sigma6/BSDProof.lean:110` **`sha_perfect_square`** — `axiom sha_perfect_square (E : EllipticCurve) :`
- `lean4_ti_sigma6/BSDProof.lean:114` **`bsd_formula`** — `axiom bsd_formula : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/BSDProof.lean:121` **`sacred_seven_resonance`** — `axiom sacred_seven_resonance : ∀ E : EllipticCurve,`
- `lean4_ti_sigma6/MyrionOperators.lean:70` **`energy_conservation_split`** — `axiom energy_conservation_split (x : Tralse) :`
- `lean4_ti_sigma6/RiemannProof.lean:11` **`prime_is_discrete`** — `axiom prime_is_discrete : ∀ p : ℕ, Nat.Prime p → ∃ t : Tralse, t = Tralse.T`
- `lean4_ti_sigma6/RiemannProof.lean:14` **`complex_is_continuous`** — `axiom complex_is_continuous : ∀ s : ℂ, ∃ phi : Tralse, phi = Tralse.Phi`
- `lean4_ti_sigma6/RiemannProof.lean:17` **`zeta`** — `axiom zeta : ℂ → ℂ`
- `lean4_ti_sigma6/RiemannProof.lean:20` **`zero_is_collapse`** — `axiom zero_is_collapse : ∀ s : ℂ, zeta s = 0 →`
- `lean4_ti_sigma6/RiemannProof.lean:24` **`functional_equation`** — `axiom functional_equation : ∀ s : ℂ,`
- `lean4_ti_sigma6/RiemannProof.lean:33` **`symmetry_forces_resolution`** — `axiom symmetry_forces_resolution : ∀ s : ℂ,`
- `lean4_ti_sigma6/RiemannProof.lean:104` **`sacred_eleven_resonance`** — `axiom sacred_eleven_resonance : ∀ n : ℕ,`
- `lean4_ti_sigma6/TralseLogic.lean:87` **`energy`** — `axiom energy : Tralse → ℝ`
- `lean4_ti_sigma6/TralseLogic.lean:90` **`energy_nonneg`** — `axiom energy_nonneg (x : Tralse) : energy x ≥ 0`
- `lean4_ti_sigma6/TralseLogic.lean:93` **`energy_ordering`** — `axiom energy_ordering :`
- `lean4_ti_sigma6/TralseLogic.lean:99` **`coherence`** — `axiom coherence : Tralse → ℝ`
- `lean4_ti_sigma6/TralseLogic.lean:102` **`coherence_bounds`** — `axiom coherence_bounds (x : Tralse) : 0 ≤ coherence x ∧ coherence x ≤ 1`
- `lean4_ti_sigma6/TralseLogic.lean:105` **`coherence_levels`** — `axiom coherence_levels :`

---

## Per-file inventory (every declaration)

### `attached_assets/Lean4WebDownload_1772987432885.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 60 | def | `φ` | **UNVERIFIED** | — | `noncomputable def φ : ℝ := (1 + sqrt 5) / 2` |
| 63 | def | `LCC_HIGH` | **UNVERIFIED** | — | `noncomputable def LCC_HIGH : ℝ := 1 / sqrt 2` |
| 66 | def | `LCC_RADIANT` | **UNVERIFIED** | — | `noncomputable def LCC_RADIANT : ℝ := 1 / φ` |
| 74 | def | `C_EMERICK` | **UNVERIFIED** | — | `noncomputable def C_EMERICK : ℝ := 1 / (φ * sqrt 2)` |
| 81 | lemma | `sqrt5_pos` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt5_pos : 0 < sqrt 5 := sqrt_pos.mpr (by norm_num)` |
| 83 | lemma | `sqrt2_pos` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)` |
| 85 | lemma | `φ_pos` | **UNVERIFIED** | linarith, by (tactic) | `private lemma φ_pos : 0 < φ := by unfold φ; linarith [sqrt5_pos]` |
| 87 | lemma | `C_EMERICK_pos` | **UNVERIFIED** | — | `private lemma C_EMERICK_pos : 0 < C_EMERICK :=` |
| 90 | lemma | `φ_ne` | **UNVERIFIED** | — | `private lemma φ_ne : φ ≠ 0 := φ_pos.ne'` |
| 92 | lemma | `sqrt2_ne` | **UNVERIFIED** | — | `private lemma sqrt2_ne : sqrt 2 ≠ 0 := sqrt2_pos.ne'` |
| 94 | lemma | `sqrt2_gt_one` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt2_gt_one : 1 < sqrt 2 :=` |
| 98 | lemma | `φ_gt_one` | **UNVERIFIED** | linarith, by (tactic) | `private lemma φ_gt_one : 1 < φ := by unfold φ; linarith [sqrt5_pos]` |
| 122 | theorem | `golden_ratio_identity` | **UNVERIFIED** | by (tactic) | `theorem golden_ratio_identity : φ ^ 2 = φ + 1 := by` |
| 145 | theorem | `emerick_normalization` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_normalization : sqrt 2 * φ * C_EMERICK = 1 := by` |
| 171 | theorem | `emerick_product_structure` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_product_structure : C_EMERICK = LCC_RADIANT * LCC_HIGH := by` |
| 182 | lemma | `φ_gt_sqrt2` | **UNVERIFIED** | linarith, exact, by (tactic) | `private lemma φ_gt_sqrt2 : sqrt 2 < φ := by` |
| 204 | theorem | `lcc_ordering` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem lcc_ordering :` |
| 253 | theorem | `extended_euler_identity` | **UNVERIFIED** | norm_num, simp, by (tactic) | `theorem extended_euler_identity :` |

### `attached_assets/Lean4WebDownload_1772987432926.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 60 | def | `φ` | **UNVERIFIED** | — | `noncomputable def φ : ℝ := (1 + sqrt 5) / 2` |
| 63 | def | `LCC_HIGH` | **UNVERIFIED** | — | `noncomputable def LCC_HIGH : ℝ := 1 / sqrt 2` |
| 66 | def | `LCC_RADIANT` | **UNVERIFIED** | — | `noncomputable def LCC_RADIANT : ℝ := 1 / φ` |
| 74 | def | `C_EMERICK` | **UNVERIFIED** | — | `noncomputable def C_EMERICK : ℝ := 1 / (φ * sqrt 2)` |
| 81 | lemma | `sqrt5_pos` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt5_pos : 0 < sqrt 5 := sqrt_pos.mpr (by norm_num)` |
| 83 | lemma | `sqrt2_pos` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)` |
| 85 | lemma | `φ_pos` | **UNVERIFIED** | linarith, by (tactic) | `private lemma φ_pos : 0 < φ := by unfold φ; linarith [sqrt5_pos]` |
| 87 | lemma | `C_EMERICK_pos` | **UNVERIFIED** | — | `private lemma C_EMERICK_pos : 0 < C_EMERICK :=` |
| 90 | lemma | `φ_ne` | **UNVERIFIED** | — | `private lemma φ_ne : φ ≠ 0 := φ_pos.ne'` |
| 92 | lemma | `sqrt2_ne` | **UNVERIFIED** | — | `private lemma sqrt2_ne : sqrt 2 ≠ 0 := sqrt2_pos.ne'` |
| 94 | lemma | `sqrt2_gt_one` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt2_gt_one : 1 < sqrt 2 :=` |
| 98 | lemma | `φ_gt_one` | **UNVERIFIED** | linarith, by (tactic) | `private lemma φ_gt_one : 1 < φ := by unfold φ; linarith [sqrt5_pos]` |
| 122 | theorem | `golden_ratio_identity` | **UNVERIFIED** | by (tactic) | `theorem golden_ratio_identity : φ ^ 2 = φ + 1 := by` |
| 145 | theorem | `emerick_normalization` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_normalization : sqrt 2 * φ * C_EMERICK = 1 := by` |
| 171 | theorem | `emerick_product_structure` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_product_structure : C_EMERICK = LCC_RADIANT * LCC_HIGH := by` |
| 182 | lemma | `φ_gt_sqrt2` | **UNVERIFIED** | linarith, exact, by (tactic) | `private lemma φ_gt_sqrt2 : sqrt 2 < φ := by` |
| 204 | theorem | `lcc_ordering` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem lcc_ordering :` |
| 253 | theorem | `extended_euler_identity` | **UNVERIFIED** | norm_num, simp, by (tactic) | `theorem extended_euler_identity :` |

### `lean/Verisyn/EulerIdentity.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 29 | def | `V_RA` | **UNVERIFIED** | — | `def V_RA : ℂ → ℂ := id` |
| 33 | theorem | `V_RA_euler` | **UNVERIFIED** | simp, by (tactic) | `theorem V_RA_euler : V_RA (Complex.exp (Real.pi * Complex.I)) = -1 := by` |
| 38 | theorem | `V_RA_mul` | **UNVERIFIED** | by (tactic) | `theorem V_RA_mul (x y : ℂ) : V_RA (x * y) = V_RA x * V_RA y := by` |
| 42 | theorem | `V_RA_zero` | **UNVERIFIED** | rfl, by (tactic) | `theorem V_RA_zero : V_RA 0 = 0 := by unfold V_RA; rfl` |

### `lean/Verisyn/EulerIdentityRC.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 33 | inductive | `MRLabel` | **UNVERIFIED** | — | `inductive MRLabel` |
| 41 | def | `V_RC` | **UNVERIFIED** | rfl | `def V_RC : MRLabel → ℂ` |
| 53 | theorem | `V_RC_T_eq_exp_pi_I` | **UNVERIFIED** | by (tactic) | `theorem V_RC_T_eq_exp_pi_I : V_RC .T = Complex.exp (Real.pi * Complex.I) := by` |
| 57 | theorem | `V_RC_injective` | **UNVERIFIED** | norm_num, rfl, simp | `theorem V_RC_injective : Function.Injective V_RC := by` |

### `lean4/BSD.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 112 | structure | `EllipticCurveQ` | **UNVERIFIED** | — | `structure EllipticCurveQ where` |
| 121 | axiom | `rank` | **AXIOM** | — | `axiom rank : EllipticCurveQ → ℕ` |
| 148 | axiom | `lFunction` | **AXIOM** | — | `axiom lFunction : EllipticCurveQ → ℂ → ℂ` |
| 153 | axiom | `lFunction_analytic` | **AXIOM** | — | `axiom lFunction_analytic (E : EllipticCurveQ) : Differentiable ℂ (lFunction E)` |
| 157 | axiom | `conductor` | **AXIOM** | — | `axiom conductor : EllipticCurveQ → ℕ` |
| 160 | axiom | `conductor_pos` | **AXIOM** | — | `axiom conductor_pos (E : EllipticCurveQ) : 0 < conductor E` |
| 164 | axiom | `rootNumber` | **AXIOM** | — | `axiom rootNumber : EllipticCurveQ → ℤ` |
| 167 | axiom | `rootNumber_pm_one` | **AXIOM** | — | `axiom rootNumber_pm_one (E : EllipticCurveQ) :` |
| 204 | axiom | `completed_lFunction_fe` | **AXIOM** | — | `axiom completed_lFunction_fe (E : EllipticCurveQ) (s : ℂ) :` |
| 217 | axiom | `modularity_theorem` | **AXIOM** | — | `axiom modularity_theorem (E : EllipticCurveQ) :` |
| 233 | def | `bsdEffort` | **UNVERIFIED** | — | `noncomputable def bsdEffort (E : EllipticCurveQ) : ℝ :=` |
| 237 | def | `isBSDEffortless` | **UNVERIFIED** | — | `def isBSDEffortless (E : EllipticCurveQ) : Prop := VernsAtOne E` |
| 248 | axiom | `lFunctionOrderAt` | **AXIOM** | — | `noncomputable axiom lFunctionOrderAt : EllipticCurveQ → ℕ` |
| 254 | axiom | `strong_bsd` | **AXIOM** | — | `axiom strong_bsd (E : EllipticCurveQ) :` |
| 290 | axiom | `weak_bsd_forward` | **AXIOM** | — | `axiom weak_bsd_forward (E : EllipticCurveQ) :` |
| 298 | axiom | `weak_bsd_converse` | **AXIOM** | — | `axiom weak_bsd_converse (E : EllipticCurveQ) :` |
| 321 | lemma | `completedL_at_one_eq` | **UNVERIFIED** | simp, by (tactic) | `lemma completedL_at_one_eq (E : EllipticCurveQ) :` |
| 336 | theorem | `parity_vanishing` | **UNVERIFIED** | norm_num, simp, exact | `theorem parity_vanishing (E : EllipticCurveQ) (hodd : rootNumber E = -1) :` |
| 364 | theorem | `parity_principle` | **UNVERIFIED** | — | `theorem parity_principle (E : EllipticCurveQ) :` |
| 372 | theorem | `vernsAtOne_iff_effortless` | **UNVERIFIED** | rfl | `theorem vernsAtOne_iff_effortless (E : EllipticCurveQ) :` |
| 375 | theorem | `bsdEffort_zero_iff` | **UNVERIFIED** | simp, by (tactic) | `theorem bsdEffort_zero_iff (E : EllipticCurveQ) :` |
| 380 | theorem | `parity_vanishing_effort` | **UNVERIFIED** | — | `theorem parity_vanishing_effort (E : EllipticCurveQ) (hodd : rootNumber E = -1) :` |
| 413 | theorem | `bsd_conjecture_iff` | **UNVERIFIED** | — | `theorem bsd_conjecture_iff (E : EllipticCurveQ) :` |
| 418 | theorem | `bsd_effort_zero_iff_rank` | **UNVERIFIED** | — | `theorem bsd_effort_zero_iff_rank (E : EllipticCurveQ) :` |
| 423 | theorem | `bsd_rank_zero_iff` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem bsd_rank_zero_iff (E : EllipticCurveQ) :` |
| 434 | theorem | `bsdEffort_pos_iff_rank_zero` | **UNVERIFIED** | simp, exact, by (tactic) | `theorem bsdEffort_pos_iff_rank_zero (E : EllipticCurveQ) :` |
| 450 | theorem | `strong_bsd_rank_zero` | **UNVERIFIED** | by (tactic) | `theorem strong_bsd_rank_zero (E : EllipticCurveQ) :` |
| 455 | theorem | `strong_implies_weak_fwd` | **UNVERIFIED** | — | `theorem strong_implies_weak_fwd (E : EllipticCurveQ) (h : 1 ≤ rank E) :` |
| 492 | theorem | `euler_product_paradox` | **UNVERIFIED** | simp, by (tactic) | `theorem euler_product_paradox (E : EllipticCurveQ) :` |
| 502 | theorem | `parity_is_provable_bsd_fragment` | **UNVERIFIED** | — | `theorem parity_is_provable_bsd_fragment :` |
| 531 | def | `curve_37a1` | **UNVERIFIED** | — | `def curve_37a1 : EllipticCurveQ := ⟨37⟩` |
| 536 | axiom | `rank_37a1` | **AXIOM** | — | `axiom rank_37a1 : rank curve_37a1 = 1` |
| 540 | axiom | `rank_11a1` | **AXIOM** | — | `axiom rank_11a1 : rank curve_11a1 = 0` |
| 544 | axiom | `L_37a1_verns` | **AXIOM** | — | `axiom L_37a1_verns : VernsAtOne curve_37a1` |
| 548 | axiom | `L_11a1_nonzero` | **AXIOM** | — | `axiom L_11a1_nonzero : ¬ VernsAtOne curve_11a1` |
| 554 | theorem | `bsd_37a1` | **UNVERIFIED** | exact, by (tactic) | `theorem bsd_37a1 : VernsAtOne curve_37a1 ↔ 1 ≤ rank curve_37a1 := by` |
| 560 | theorem | `bsd_11a1` | **UNVERIFIED** | — | `theorem bsd_11a1 : rank curve_11a1 = 0 ↔ ¬ VernsAtOne curve_11a1 :=` |
| 564 | theorem | `curve_11a1_consistent` | **UNVERIFIED** | — | `theorem curve_11a1_consistent : rank curve_11a1 = 0 := rank_11a1` |
| 667 | structure | `ImaginaryQuadraticField` | **UNVERIFIED** | — | `structure ImaginaryQuadraticField where` |
| 678 | axiom | `heegnerPoint` | **AXIOM** | — | `noncomputable axiom heegnerPoint :` |
| 685 | axiom | `canonicalHeight` | **AXIOM** | — | `noncomputable axiom canonicalHeight : EllipticCurveQ → ℝ → ℝ` |
| 695 | axiom | `gross_zagier` | **AXIOM** | — | `axiom gross_zagier (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 703 | axiom | `gross_zagier_nontorsion` | **AXIOM** | — | `axiom gross_zagier_nontorsion (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 712 | theorem | `heegner_implies_verns` | **UNVERIFIED** | exact, by (tactic) | `theorem heegner_implies_verns (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 747 | structure | `ShaTateShafarevich` | **UNVERIFIED** | — | `structure ShaTateShafarevich where` |
| 755 | axiom | `kolyvagin_rank_one` | **AXIOM** | — | `axiom kolyvagin_rank_one (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 763 | axiom | `kolyvagin_sha_finite` | **AXIOM** | — | `axiom kolyvagin_sha_finite (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 770 | theorem | `gzk_rank_one` | **UNVERIFIED** | — | `theorem gzk_rank_one (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 805 | axiom | `rank_one_bsd_forward` | **AXIOM** | — | `axiom rank_one_bsd_forward (E : EllipticCurveQ) :` |
| 813 | axiom | `rank_zero_lvalue_pos` | **AXIOM** | — | `axiom rank_zero_lvalue_pos (E : EllipticCurveQ) :` |
| 817 | theorem | `bsd_rank_one` | **UNVERIFIED** | — | `theorem bsd_rank_one (E : EllipticCurveQ) (h1 : rank E = 1) :` |
| 823 | theorem | `two_case_bsd_proved` | **UNVERIFIED** | exact, by (tactic) | `theorem two_case_bsd_proved (E : EllipticCurveQ)` |
| 856 | axiom | `sha_finite_rank_one` | **AXIOM** | — | `axiom sha_finite_rank_one (E : EllipticCurveQ) (K : ImaginaryQuadraticField)` |
| 865 | axiom | `sha_order_square` | **AXIOM** | — | `axiom sha_order_square (E : EllipticCurveQ) :` |
| 870 | axiom | `real_period` | **AXIOM** | — | `axiom real_period : EllipticCurveQ → ℝ` |
| 872 | axiom | `real_period_pos` | **AXIOM** | — | `axiom real_period_pos (E : EllipticCurveQ) : real_period E > 0` |
| 876 | axiom | `regulator` | **AXIOM** | — | `axiom regulator : EllipticCurveQ → ℝ` |
| 878 | axiom | `regulator_nonneg` | **AXIOM** | — | `axiom regulator_nonneg (E : EllipticCurveQ) : regulator E ≥ 0` |
| 880 | axiom | `regulator_pos_iff_positive_rank` | **AXIOM** | — | `axiom regulator_pos_iff_positive_rank (E : EllipticCurveQ) :` |
| 885 | axiom | `tamagawa_product` | **AXIOM** | — | `axiom tamagawa_product : EllipticCurveQ → ℝ` |
| 887 | axiom | `tamagawa_product_pos` | **AXIOM** | — | `axiom tamagawa_product_pos (E : EllipticCurveQ) : tamagawa_product E > 0` |
| 892 | axiom | `torsion_order` | **AXIOM** | — | `axiom torsion_order : EllipticCurveQ → ℕ` |
| 894 | axiom | `torsion_order_pos` | **AXIOM** | — | `axiom torsion_order_pos (E : EllipticCurveQ) : torsion_order E > 0` |
| 900 | axiom | `mazur_torsion_bound` | **AXIOM** | — | `axiom mazur_torsion_bound (E : EllipticCurveQ) : torsion_order E ≤ 12` |
| 930 | theorem | `bsd_coefficient_nonneg` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem bsd_coefficient_nonneg (E : EllipticCurveQ) (sha : ℕ) (hsha : 0 < sha) :` |
| 946 | axiom | `strong_bsd_leading_coefficient` | **AXIOM** | — | `axiom strong_bsd_leading_coefficient (E : EllipticCurveQ) (sha : ℕ)` |
| 989 | axiom | `kato_rank_bound` | **AXIOM** | — | `axiom kato_rank_bound (E : EllipticCurveQ) :` |
| 996 | theorem | `kato_and_strong_bsd_agree` | **UNVERIFIED** | — | `theorem kato_and_strong_bsd_agree (E : EllipticCurveQ) :` |
| 1003 | theorem | `kato_implies_weak_bsd_forward` | **UNVERIFIED** | exact, by (tactic) | `theorem kato_implies_weak_bsd_forward (E : EllipticCurveQ) (h : 1 ≤ rank E) :` |
| 1107 | theorem | `ti_sigma_bsd_kato_fragment` | **UNVERIFIED** | — | `theorem ti_sigma_bsd_kato_fragment (E : EllipticCurveQ) :` |
| 1114 | theorem | `ti_sigma_bsd_complete` | **UNVERIFIED** | — | `theorem ti_sigma_bsd_complete (E : EllipticCurveQ) :` |

### `lean4/BeingTheorem.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 11 | axiom | `is` | **AXIOM** | — | `axiom is itself logically equivalent to RH. So every "IS at σ = 1/2",` |
| 92 | def | `isEffortlessZero` | **UNVERIFIED** | — | `def isEffortlessZero (ρ : ℂ) : Prop := effort ρ = 0` |
| 97 | def | `realPartSelfConsistent` | **UNVERIFIED** | — | `def realPartSelfConsistent (ρ : ℂ) : Prop := ρ.re = 1 - ρ.re` |
| 107 | theorem | `being_theorem` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem being_theorem (ρ : ℂ) :` |
| 118 | theorem | `effortless_iff_self_consistent` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem effortless_iff_self_consistent (ρ : ℂ) :` |
| 133 | theorem | `real_part_erasure` | **UNVERIFIED** | linarith, by (tactic) | `theorem real_part_erasure (σ : ℝ) :` |
| 141 | theorem | `zero_has_no_sigma_preference` | **UNVERIFIED** | — | `theorem zero_has_no_sigma_preference (σ : ℝ) :` |
| 151 | def | `uopFreeEnergy` | **UNVERIFIED** | — | `noncomputable def uopFreeEnergy (σ : ℝ) : ℝ := \|2 * σ - 1\|` |
| 154 | theorem | `uop_minimum` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem uop_minimum (σ : ℝ) :` |
| 164 | theorem | `effort_eq_uop_free_energy` | **UNVERIFIED** | rfl | `theorem effort_eq_uop_free_energy (ρ : ℂ) :` |
| 168 | theorem | `effortless_iff_zero_free_energy` | **UNVERIFIED** | rfl, exact, by (tactic) | `theorem effortless_iff_zero_free_energy (ρ : ℂ) :` |
| 200 | theorem | `riddle2_iff_riddle4` | **UNVERIFIED** | exact, by (tactic) | `theorem riddle2_iff_riddle4 (ρ : ℂ) :` |
| 206 | theorem | `riddle4_iff_riddle5` | **UNVERIFIED** | — | `theorem riddle4_iff_riddle5 (ρ : ℂ) :` |
| 244 | theorem | `pairCost_condA_iff_uop_free_energy` | **UNVERIFIED** | by (tactic) | `theorem pairCost_condA_iff_uop_free_energy (σ : ℝ) :` |
| 251 | theorem | `being_theorem_is_sixth_gap_condition` | **UNVERIFIED** | exact, by (tactic) | `theorem being_theorem_is_sixth_gap_condition (ρ : ℂ) :` |
| 257 | theorem | `being_theorem_is_gap_condition_E` | **UNVERIFIED** | — | `theorem being_theorem_is_gap_condition_E (ρ : ℂ) :` |
| 309 | def | `PLA_Condition_Being` | **UNVERIFIED** | — | `def PLA_Condition_Being : Prop :=` |
| 326 | axiom | `universal_bridge_theorem` | **AXIOM** | — | `axiom universal_bridge_theorem : PLA_Condition_Being` |
| 333 | theorem | `euler_forcing_being` | **UNVERIFIED** | exact, by (tactic) | `theorem euler_forcing_being` |
| 346 | theorem | `riemann_hypothesis_from_being` | **UNVERIFIED** | — | `theorem riemann_hypothesis_from_being` |
| 382 | axiom | `—` | **AXIOM** | — | `axiom — and that axiom IS RH, so this is` |
| 460 | theorem | `ubt_bridge_closed` | **UNVERIFIED** | — | `theorem ubt_bridge_closed (ρ : ℂ) :` |

### `lean4/Collatz.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 35 | def | `collatzStep` | **UNVERIFIED** | — | `def collatzStep (n : ℕ) : ℕ :=` |
| 40 | def | `collatzAcc` | **UNVERIFIED** | — | `def collatzAcc (n : ℕ) : ℕ :=` |
| 44 | def | `collatzIter` | **UNVERIFIED** | — | `def collatzIter : ℕ → ℕ → ℕ` |
| 57 | theorem | `collatzStep_even` | **UNVERIFIED** | simp, by (tactic) | `theorem collatzStep_even (n : ℕ) (h : n % 2 = 0) :` |
| 63 | theorem | `collatzStep_odd` | **UNVERIFIED** | simp, by (tactic) | `theorem collatzStep_odd (n : ℕ) (h : n % 2 = 1) :` |
| 69 | theorem | `collatzStep_one` | **UNVERIFIED** | by (tactic) | `theorem collatzStep_one : collatzStep 1 = 4 := by` |
| 73 | theorem | `collatzStep_two` | **UNVERIFIED** | by (tactic) | `theorem collatzStep_two : collatzStep 2 = 1 := by` |
| 77 | theorem | `collatzIter_four` | **UNVERIFIED** | decide, by (tactic) | `theorem collatzIter_four : collatzIter 2 4 = 1 := by decide` |
| 80 | theorem | `collatz_one_converges` | **UNVERIFIED** | decide, by (tactic) | `theorem collatz_one_converges : collatzConverges 1 := ⟨0, by decide⟩` |
| 83 | theorem | `collatz_two_converges` | **UNVERIFIED** | decide, by (tactic) | `theorem collatz_two_converges : collatzConverges 2 := ⟨1, by decide⟩` |
| 86 | theorem | `collatz_four_converges` | **UNVERIFIED** | decide, by (tactic) | `theorem collatz_four_converges : collatzConverges 4 := ⟨2, by decide⟩` |
| 93 | theorem | `collatz_odd_step_even` | **UNVERIFIED** | by (tactic) | `theorem collatz_odd_step_even (n : ℕ) (h : n % 2 = 1) :` |
| 97 | theorem | `collatz_mod4_1` | **UNVERIFIED** | by (tactic) | `theorem collatz_mod4_1 (n : ℕ) (h : n % 4 = 1) :` |
| 101 | theorem | `collatz_mod4_3` | **UNVERIFIED** | by (tactic) | `theorem collatz_mod4_3 (n : ℕ) (h : n % 4 = 3) :` |
| 107 | theorem | `padicVal_collatz_mod4_3` | **UNVERIFIED** | norm_num, ring, exact | `theorem padicVal_collatz_mod4_3 (n : ℕ) (hn : n % 4 = 3) (hpos : 0 < n) :` |
| 127 | theorem | `collatz_mod4_3_div2_not_div4` | **UNVERIFIED** | exact, by (tactic) | `theorem collatz_mod4_3_div2_not_div4 (n : ℕ) (h : n % 4 = 3) :` |
| 136 | theorem | `collatz_mod4_1_div4` | **UNVERIFIED** | exact, by (tactic) | `theorem collatz_mod4_1_div4 (n : ℕ) (h : n % 4 = 1) :` |
| 148 | axiom | `collatz_conjecture` | **AXIOM** | — | `axiom collatz_conjecture : ∀ n : ℕ, 0 < n → collatzConverges n` |
| 155 | theorem | `collatz_reaches_one` | **UNVERIFIED** | — | `theorem collatz_reaches_one (n : ℕ) (hn : 0 < n) :` |
| 160 | theorem | `collatz_step_converges` | **UNVERIFIED** | decide, simp, exact | `theorem collatz_step_converges {n : ℕ} (hconv : collatzConverges n) (hn : 0 < n) :` |
| 172 | theorem | `collatz_even_converges` | **UNVERIFIED** | — | `theorem collatz_even_converges (n : ℕ) (hn : 0 < n) (heven : n % 2 = 0) :` |
| 177 | theorem | `collatz_odd_converges` | **UNVERIFIED** | — | `theorem collatz_odd_converges (n : ℕ) (hn : 0 < n) (hodd : n % 2 = 1) :` |
| 182 | theorem | `collatz_infinitely_many` | **UNVERIFIED** | — | `theorem collatz_infinitely_many : ∀ n : ℕ, 0 < n → collatzConverges n :=` |
| 186 | theorem | `collatz_one_is_vacuum` | **UNVERIFIED** | rfl | `theorem collatz_one_is_vacuum :` |
| 234 | theorem | `collatz_being_theorem` | **UNVERIFIED** | — | `theorem collatz_being_theorem (n : ℕ) (hn : 0 < n) :` |
| 239 | theorem | `collatz_vacuum_zero_effort` | **UNVERIFIED** | rfl | `theorem collatz_vacuum_zero_effort :` |
| 244 | theorem | `collatz_being_iff` | **UNVERIFIED** | — | `theorem collatz_being_iff (n : ℕ) (hn : 0 < n) :` |
| 250 | theorem | `collatz_vacuum_uniqueness` | **UNVERIFIED** | — | `theorem collatz_vacuum_uniqueness :` |

### `lean4/GapEquivalence.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 15 | mutual | `implication.` | **UNVERIFIED** | — | `mutual implication. This means:` |
| 41 | def | `S₁'` | **UNVERIFIED** | — | `noncomputable def S₁' (s : ℂ) : ℂ := conj s` |
| 53 | theorem | `condA_iff_critical` | **UNVERIFIED** | norm_num, simp, linarith | `theorem condA_iff_critical (σ : ℝ) :` |
| 64 | theorem | `condBC_iff_critical` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem condBC_iff_critical (s : ℂ) :` |
| 78 | theorem | `condMirror_iff_critical` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem condMirror_iff_critical (s : ℂ) :` |
| 91 | theorem | `condUOP_iff_critical` | **UNVERIFIED** | simp, ring, by (tactic) | `theorem condUOP_iff_critical (s : ℂ) :` |
| 116 | theorem | `gap_equivalence` | **UNVERIFIED** | by (tactic) | `theorem gap_equivalence (s : ℂ) :` |
| 128 | theorem | `any_gap_implies_all` | **UNVERIFIED** | exact, by (tactic) | `theorem any_gap_implies_all (s : ℂ) :` |
| 165 | axiom | `master_gap` | **AXIOM** | — | `axiom master_gap (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)` |
| 174 | theorem | `riemann_hypothesis_master` | **UNVERIFIED** | — | `theorem riemann_hypothesis_master :` |
| 214 | theorem | `all_gaps_equivalent` | **UNVERIFIED** | by (tactic) | `theorem all_gaps_equivalent :` |

### `lean4/GroupSymmetryRoute.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 48 | def | `S₁` | **UNVERIFIED** | — | `noncomputable def S₁ (s : ℂ) : ℂ := conj s` |
| 51 | def | `S₂` | **UNVERIFIED** | — | `noncomputable def S₂ (s : ℂ) : ℂ := 1 - s` |
| 54 | def | `S₁S₂` | **UNVERIFIED** | — | `noncomputable def S₁S₂ (s : ℂ) : ℂ := S₁ (S₂ s)` |
| 57 | def | `S₂S₁` | **UNVERIFIED** | — | `noncomputable def S₂S₁ (s : ℂ) : ℂ := S₂ (S₁ s)` |
| 64 | theorem | `S₁_involution` | **UNVERIFIED** | by (tactic) | `theorem S₁_involution (s : ℂ) : S₁ (S₁ s) = s := by` |
| 68 | theorem | `S₂_involution` | **UNVERIFIED** | by (tactic) | `theorem S₂_involution (s : ℂ) : S₂ (S₂ s) = s := by` |
| 72 | theorem | `S₁S₂_involution` | **UNVERIFIED** | by (tactic) | `theorem S₁S₂_involution (s : ℂ) : S₁S₂ (S₁S₂ s) = s := by` |
| 76 | theorem | `S₁_S₂_commute` | **UNVERIFIED** | simp, by (tactic) | `theorem S₁_S₂_commute (s : ℂ) : S₁ (S₂ s) = S₂ (S₁ s) := by` |
| 83 | theorem | `S₁S₂_eq_S₂S₁` | **UNVERIFIED** | — | `theorem S₁S₂_eq_S₂S₁ (s : ℂ) : S₁S₂ s = S₂S₁ s := S₁_S₂_commute s` |
| 104 | def | `gOrbit` | **UNVERIFIED** | — | `noncomputable def gOrbit (ρ : ℂ) : Set ℂ :=` |
| 108 | theorem | `gOrbit_explicit` | **UNVERIFIED** | simp, by (tactic) | `theorem gOrbit_explicit (ρ : ℂ) :` |
| 125 | theorem | `orbit_collapse_iff_critical` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem orbit_collapse_iff_critical (ρ : ℂ) :` |
| 140 | theorem | `orbit_collapse_S₁S₂_fixes` | **UNVERIFIED** | simp, by (tactic) | `theorem orbit_collapse_S₁S₂_fixes (ρ : ℂ) (h : S₁ ρ = S₂ ρ) :` |
| 148 | theorem | `orbit_size_4_when_off_axis` | **UNVERIFIED** | simp, linarith, exact | `theorem orbit_size_4_when_off_axis (ρ : ℂ) (him : ρ.im ≠ 0) (hre : ρ.re ≠ 1/2) :` |
| 196 | def | `hadamardPartner` | **UNVERIFIED** | — | `noncomputable def hadamardPartner (ρ : ℂ) : ℂ := 1 - conj ρ` |
| 199 | theorem | `hadamard_self_paired_iff_critical` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem hadamard_self_paired_iff_critical (ρ : ℂ) :` |
| 222 | theorem | `hadamardPartner_is_S₁S₂` | **UNVERIFIED** | simp, by (tactic) | `theorem hadamardPartner_is_S₁S₂ (ρ : ℂ) :` |
| 227 | theorem | `hadamard_orbit_critical_equivalence` | **UNVERIFIED** | by (tactic) | `theorem hadamard_orbit_critical_equivalence (ρ : ℂ) :` |
| 264 | axiom | `orbit_collapse_axiom` | **AXIOM** | — | `axiom orbit_collapse_axiom (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)` |
| 275 | theorem | `riemann_hypothesis_group_symmetry` | **UNVERIFIED** | — | `theorem riemann_hypothesis_group_symmetry :` |
| 296 | theorem | `routes_BC_equivalent` | **UNVERIFIED** | by (tactic) | `theorem routes_BC_equivalent (ρ : ℂ) :` |

### `lean4/Hodge.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 61 | structure | `ComplexVariety` | **UNVERIFIED** | — | `structure ComplexVariety where` |
| 65 | structure | `CohomologyClass` | **UNVERIFIED** | — | `structure CohomologyClass (X : ComplexVariety) where` |
| 70 | structure | `AlgebraicCycle` | **UNVERIFIED** | — | `structure AlgebraicCycle (X : ComplexVariety) where` |
| 75 | axiom | `cycleClass` | **AXIOM** | — | `axiom cycleClass : ∀ {X : ComplexVariety} (Z : AlgebraicCycle X),` |
| 79 | axiom | `isHodgeClass` | **AXIOM** | — | `axiom isHodgeClass : ∀ {X : ComplexVariety} (α : CohomologyClass X), Prop` |
| 82 | axiom | `cycleClass_is_hodge` | **AXIOM** | — | `axiom cycleClass_is_hodge : ∀ {X : ComplexVariety} (Z : AlgebraicCycle X),` |
| 87 | axiom | `isAlgebraic` | **AXIOM** | — | `axiom isAlgebraic : ∀ {X : ComplexVariety} (α : CohomologyClass X), Prop` |
| 90 | axiom | `algebraic_implies_hodge` | **AXIOM** | — | `axiom algebraic_implies_hodge : ∀ {X : ComplexVariety} (α : CohomologyClass X),` |
| 106 | axiom | `hodgeEffort` | **AXIOM** | — | `axiom hodgeEffort : ∀ {X : ComplexVariety} (α : CohomologyClass X), ℝ` |
| 109 | axiom | `hodgeEffort_algebraic` | **AXIOM** | — | `axiom hodgeEffort_algebraic : ∀ {X : ComplexVariety} (α : CohomologyClass X),` |
| 113 | axiom | `hodgeEffort_nonneg` | **AXIOM** | — | `axiom hodgeEffort_nonneg : ∀ {X : ComplexVariety} (α : CohomologyClass X),` |
| 131 | axiom | `hodge_conjecture` | **AXIOM** | — | `axiom hodge_conjecture : ∀ {X : ComplexVariety} (α : CohomologyClass X),` |
| 141 | theorem | `hodge_vern_theorem` | **UNVERIFIED** | — | `theorem hodge_vern_theorem {X : ComplexVariety} (α : CohomologyClass X)` |
| 147 | theorem | `hodge_effort_theorem` | **UNVERIFIED** | — | `theorem hodge_effort_theorem {X : ComplexVariety} (α : CohomologyClass X)` |
| 154 | theorem | `hodge_iff_algebraic` | **UNVERIFIED** | — | `theorem hodge_iff_algebraic {X : ComplexVariety} (α : CohomologyClass X)` |
| 161 | theorem | `no_phantom_hodge_classes` | **UNVERIFIED** | linarith, by (tactic) | `theorem no_phantom_hodge_classes {X : ComplexVariety} (α : CohomologyClass X)` |
| 169 | theorem | `hodge_being_theorem` | **UNVERIFIED** | — | `theorem hodge_being_theorem {X : ComplexVariety} (α : CohomologyClass X)` |
| 211 | theorem | `hodge_metacausal_gap_statement` | **UNVERIFIED** | simp, by (tactic) | `theorem hodge_metacausal_gap_statement {X : ComplexVariety} :` |

### `lean4/MathlibDemo.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 33 | def | `conj` | **UNVERIFIED** | — | `noncomputable def conj (z : ℂ) : ℂ := star z` |
| 35 | lemma | `conj_re` | **UNVERIFIED** | by (tactic) | `private lemma conj_re (z : ℂ) : (conj z).re = z.re := by` |
| 38 | lemma | `conj_im` | **UNVERIFIED** | by (tactic) | `private lemma conj_im (z : ℂ) : (conj z).im = -z.im := by` |
| 46 | def | `pairCost'` | **UNVERIFIED** | — | `noncomputable def pairCost' (σ : ℝ) : ℝ := -min σ (1 - σ)` |
| 49 | def | `S₁'` | **UNVERIFIED** | — | `noncomputable def S₁' (s : ℂ) : ℂ := conj s` |
| 55 | theorem | `condA_iff_critical` | **UNVERIFIED** | linarith, by (tactic) | `theorem condA_iff_critical (σ : ℝ) :` |
| 77 | theorem | `condBC_iff_critical` | **UNVERIFIED** | ring, linarith, by (tactic) | `theorem condBC_iff_critical (s : ℂ) :` |
| 93 | theorem | `condMirror_iff_critical` | **UNVERIFIED** | ring, linarith, by (tactic) | `theorem condMirror_iff_critical (s : ℂ) :` |
| 110 | theorem | `condUOP_iff_critical` | **UNVERIFIED** | simp, ring, by (tactic) | `theorem condUOP_iff_critical (s : ℂ) :` |
| 129 | theorem | `gap_equivalence` | **UNVERIFIED** | — | `theorem gap_equivalence (s : ℂ) :` |
| 138 | theorem | `any_gap_implies_all` | **UNVERIFIED** | exact, by (tactic) | `theorem any_gap_implies_all (s : ℂ) :` |
| 156 | def | `effort` | **UNVERIFIED** | — | `noncomputable def effort (ρ : ℂ) : ℝ := \|2 * ρ.re - 1\|` |
| 159 | def | `isEffortlessZero` | **UNVERIFIED** | — | `def isEffortlessZero (ρ : ℂ) : Prop := effort ρ = 0` |
| 162 | def | `realPartSelfConsistent` | **UNVERIFIED** | — | `def realPartSelfConsistent (ρ : ℂ) : Prop := ρ.re = 1 - ρ.re` |
| 165 | def | `uopFreeEnergy` | **UNVERIFIED** | — | `noncomputable def uopFreeEnergy (σ : ℝ) : ℝ := \|2 * σ - 1\|` |
| 172 | theorem | `being_theorem` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem being_theorem (ρ : ℂ) :` |
| 181 | theorem | `effortless_iff_self_consistent` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem effortless_iff_self_consistent (ρ : ℂ) :` |
| 191 | theorem | `real_part_erasure` | **UNVERIFIED** | linarith, by (tactic) | `theorem real_part_erasure (σ : ℝ) :` |
| 199 | theorem | `uop_minimum` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem uop_minimum (σ : ℝ) :` |
| 208 | theorem | `effort_eq_uop_free_energy` | **UNVERIFIED** | rfl | `theorem effort_eq_uop_free_energy (ρ : ℂ) :` |
| 212 | theorem | `effortless_iff_zero_free_energy` | **UNVERIFIED** | by (tactic) | `theorem effortless_iff_zero_free_energy (ρ : ℂ) :` |
| 219 | theorem | `riddle2_iff_riddle4` | **UNVERIFIED** | exact, by (tactic) | `theorem riddle2_iff_riddle4 (ρ : ℂ) :` |
| 226 | theorem | `riddle4_iff_riddle5` | **UNVERIFIED** | — | `theorem riddle4_iff_riddle5 (ρ : ℂ) :` |
| 233 | theorem | `pairCost_condA_iff_uop_free_energy` | **UNVERIFIED** | by (tactic) | `theorem pairCost_condA_iff_uop_free_energy (σ : ℝ) :` |
| 239 | theorem | `being_theorem_is_sixth_gap_condition` | **UNVERIFIED** | exact, by (tactic) | `theorem being_theorem_is_sixth_gap_condition (ρ : ℂ) :` |
| 246 | axiom | `riemannZeta` | **AXIOM** | — | `axiom riemannZeta : ℂ → ℂ` |
| 256 | axiom | `euler_forcing_being` | **AXIOM** | — | `axiom euler_forcing_being` |
| 264 | theorem | `riemann_hypothesis_from_being` | **UNVERIFIED** | — | `theorem riemann_hypothesis_from_being` |

### `lean4/MirrorPairing.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 65 | theorem | `mirror_pairing_iff_critical` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem mirror_pairing_iff_critical (s : ℂ) :` |
| 82 | theorem | `mirror_pairing_re` | **UNVERIFIED** | — | `theorem mirror_pairing_re (s : ℂ) (h : conj s = 1 - s) : s.re = 1 / 2 :=` |
| 89 | theorem | `mirror_pairing_im_free` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem mirror_pairing_im_free (s : ℂ) (h : conj s = 1 - s) (t : ℝ) :` |
| 107 | def | `zeroQuadruple` | **UNVERIFIED** | — | `def zeroQuadruple (ρ : ℂ) : Finset ℂ :=` |
| 116 | def | `zeroPair` | **UNVERIFIED** | — | `def zeroPair (ρ : ℂ) : Finset ℂ := {ρ, conj ρ}` |
| 127 | theorem | `quadruple_to_pair` | **UNVERIFIED** | simp, ring, exact | `theorem quadruple_to_pair (ρ : ℂ) (h : conj ρ = 1 - ρ) :` |
| 145 | theorem | `off_axis_gives_quadruple` | **UNVERIFIED** | exact, by (tactic) | `theorem off_axis_gives_quadruple (ρ : ℂ) (h : ρ.re ≠ 1 / 2) :` |
| 164 | theorem | `mirror_pairing_equiv_equidistance` | **UNVERIFIED** | simp, ring, by (tactic) | `theorem mirror_pairing_equiv_equidistance (s : ℂ) :` |
| 203 | structure | `of` | **UNVERIFIED** | — | `structure of the Euler product.` |
| 230 | axiom | `euler_forcing` | **AXIOM** | — | `axiom euler_forcing (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 250 | theorem | `riemann_hypothesis_mirror` | **UNVERIFIED** | exact, by (tactic) | `theorem riemann_hypothesis_mirror :` |
| 296 | def | `uopEnergy` | **UNVERIFIED** | — | `noncomputable def uopEnergy (σ : ℝ) : ℝ := -min σ (1 - σ)` |
| 299 | theorem | `uopEnergy_minimum` | **UNVERIFIED** | simp, linarith, exact | `theorem uopEnergy_minimum (σ : ℝ) : uopEnergy (1 / 2) ≤ uopEnergy σ := by` |
| 307 | theorem | `uopEnergy_unique_min` | **UNVERIFIED** | norm_num, simp, linarith | `theorem uopEnergy_unique_min (σ : ℝ) (h : uopEnergy σ = uopEnergy (1 / 2)) :` |
| 336 | theorem | `euler_forcing_attempt` | **INCONSISTENT** | sorry, by (tactic) | `theorem euler_forcing_attempt (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |

### `lean4/NavierStokes.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 63 | inductive | `Dimension` | **UNVERIFIED** | — | `inductive Dimension \| two \| three` |
| 66 | structure | `NSSolution` | **UNVERIFIED** | — | `structure NSSolution where` |
| 73 | axiom | `nsEnergy` | **AXIOM** | — | `noncomputable axiom nsEnergy : NSSolution → ℝ → ℝ` |
| 77 | axiom | `nsEnstrophy` | **AXIOM** | — | `noncomputable axiom nsEnstrophy : NSSolution → ℝ → ℝ` |
| 80 | axiom | `nsEnergy_nonneg` | **AXIOM** | — | `axiom nsEnergy_nonneg    : ∀ (sol : NSSolution) (t : ℝ), 0 ≤ nsEnergy sol t` |
| 81 | axiom | `nsEnstrophy_nonneg` | **AXIOM** | — | `axiom nsEnstrophy_nonneg : ∀ (sol : NSSolution) (t : ℝ), 0 ≤ nsEnstrophy sol t` |
| 84 | axiom | `integratedEnstrophy` | **AXIOM** | — | `noncomputable axiom integratedEnstrophy : NSSolution → ℝ → ℝ` |
| 87 | axiom | `integratedEnstrophy_nonneg` | **AXIOM** | — | `axiom integratedEnstrophy_nonneg (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :` |
| 93 | axiom | `leray_energy_inequality` | **AXIOM** | — | `axiom leray_energy_inequality (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :` |
| 107 | def | `hasBlowup` | **UNVERIFIED** | — | `def hasBlowup (sol : NSSolution) (T_star : ℝ) : Prop :=` |
| 113 | def | `isSmoothnessVern` | **UNVERIFIED** | — | `def isSmoothnessVern (sol : NSSolution) : Prop :=` |
| 117 | theorem | `viscosity_pos` | **UNVERIFIED** | — | `theorem viscosity_pos (sol : NSSolution) : 0 < sol.ν := sol.ν_pos` |
| 120 | theorem | `smoothnessVern_eq_globallyRegular` | **UNVERIFIED** | rfl | `theorem smoothnessVern_eq_globallyRegular (sol : NSSolution) :` |
| 146 | theorem | `leray_energy_bounded` | **UNVERIFIED** | norm_num, by (tactic) | `theorem leray_energy_bounded (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :` |
| 154 | theorem | `leray_dissipation_nonneg` | **UNVERIFIED** | linarith, by (tactic) | `theorem leray_dissipation_nonneg (sol : NSSolution) (t : ℝ) (ht : 0 ≤ t) :` |
| 162 | theorem | `larger_viscosity_tighter_ceiling` | **UNVERIFIED** | by (tactic) | `theorem larger_viscosity_tighter_ceiling (ν₁ ν₂ Z E₀ : ℝ)` |
| 189 | axiom | `ns_2d_global_regularity` | **AXIOM** | — | `axiom ns_2d_global_regularity (sol : NSSolution) (h2d : sol.dim = Dimension.two) :` |
| 194 | theorem | `ns_2d_smoothness_vern` | **UNVERIFIED** | — | `theorem ns_2d_smoothness_vern (sol : NSSolution) (h2d : sol.dim = Dimension.two) :` |
| 200 | axiom | `blowup_not_regular` | **AXIOM** | — | `axiom blowup_not_regular (sol : NSSolution) (T_star : ℝ) :` |
| 203 | theorem | `ns_2d_no_blowup` | **UNVERIFIED** | — | `theorem ns_2d_no_blowup (sol : NSSolution) (h2d : sol.dim = Dimension.two)` |
| 230 | def | `satisfiesSerrin` | **UNVERIFIED** | — | `def satisfiesSerrin (sol : NSSolution) (T p q : ℝ) : Prop :=` |
| 235 | axiom | `serrin_regularity` | **AXIOM** | — | `axiom serrin_regularity (sol : NSSolution) (T p q : ℝ)` |
| 242 | theorem | `serrin_critical_case` | **UNVERIFIED** | — | `theorem serrin_critical_case (sol : NSSolution) (T p q : ℝ)` |
| 249 | axiom | `serrin_L3_endpoint` | **AXIOM** | — | `axiom serrin_L3_endpoint (sol : NSSolution) (T : ℝ) (hT : 0 < T) :` |
| 274 | axiom | `singularHausdorffMeasure` | **AXIOM** | — | `noncomputable axiom singularHausdorffMeasure : NSSolution → ℝ` |
| 278 | axiom | `ckn_partial_regularity` | **AXIOM** | — | `axiom ckn_partial_regularity (sol : NSSolution)` |
| 285 | theorem | `ckn_regular_set_full` | **UNVERIFIED** | — | `theorem ckn_regular_set_full (sol : NSSolution)` |
| 310 | def | `reynoldsNumber` | **UNVERIFIED** | — | `noncomputable def reynoldsNumber (L U ν : ℝ) : ℝ := L * U / ν` |
| 313 | theorem | `reynoldsNumber_pos` | **UNVERIFIED** | exact, by (tactic) | `theorem reynoldsNumber_pos (L U ν : ℝ) (hL : 0 < L) (hU : 0 < U) (hν : 0 < ν) :` |
| 319 | theorem | `larger_viscosity_lower_Re` | **UNVERIFIED** | exact, by (tactic) | `theorem larger_viscosity_lower_Re (L U ν₁ ν₂ : ℝ)` |
| 332 | def | `isMRDominated` | **UNVERIFIED** | — | `def isMRDominated (L U ν : ℝ) : Prop := reynoldsNumber L U ν < 1` |
| 335 | theorem | `high_viscosity_MR_dominated` | **UNVERIFIED** | exact, by (tactic) | `theorem high_viscosity_MR_dominated (L U ν : ℝ)` |
| 360 | def | `kolmogorovScale` | **UNVERIFIED** | — | `noncomputable def kolmogorovScale (ν ε : ℝ) : ℝ :=` |
| 364 | theorem | `kolmogorovScale_pos` | **UNVERIFIED** | exact, by (tactic) | `theorem kolmogorovScale_pos (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :` |
| 371 | theorem | `viscosity_improves_kolmogorov` | **UNVERIFIED** | norm_num, by (tactic) | `theorem viscosity_improves_kolmogorov (ν₁ ν₂ ε : ℝ)` |
| 410 | axiom | `ns_global_regularity` | **AXIOM** | — | `axiom ns_global_regularity (ν : ℝ) (hν : 0 < ν) :` |
| 416 | axiom | `ns_blowup` | **AXIOM** | — | `axiom ns_blowup :` |
| 423 | axiom | `ns_dichotomy` | **AXIOM** | — | `axiom ns_dichotomy :` |
| 435 | theorem | `ns_smoothness_vern_theorem` | **UNVERIFIED** | exact, by (tactic) | `theorem ns_smoothness_vern_theorem (ν : ℝ) (hν : 0 < ν) :` |
| 443 | theorem | `ns_not_regular_implies_unbounded` | **UNVERIFIED** | exact, by (tactic) | `theorem ns_not_regular_implies_unbounded (sol : NSSolution) (h : ¬ isGloballyRegular sol) :` |
| 453 | theorem | `ns_dichotomy_corollary` | **UNVERIFIED** | exact, by (tactic) | `theorem ns_dichotomy_corollary :` |
| 468 | theorem | `two_d_always_regular_three_d_open` | **UNVERIFIED** | exact, by (tactic) | `theorem two_d_always_regular_three_d_open :` |
| 479 | theorem | `leray_serrin_bridge` | **UNVERIFIED** | — | `theorem leray_serrin_bridge (sol : NSSolution) (T p q : ℝ)` |
| 487 | theorem | `ckn_generic_regularity` | **UNVERIFIED** | — | `theorem ckn_generic_regularity (sol : NSSolution) (h3d : sol.dim = Dimension.three) :` |
| 517 | theorem | `ns_euler_forcing_gap_is_millennium_problem` | **UNVERIFIED** | — | `theorem ns_euler_forcing_gap_is_millennium_problem :` |

### `lean4/PvsNP.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 59 | def | `DecisionProblem` | **UNVERIFIED** | — | `def DecisionProblem := Set ℕ` |
| 62 | structure | `Certificate` | **UNVERIFIED** | — | `structure Certificate (L : DecisionProblem) (x : ℕ) where` |
| 67 | axiom | `verificationTime` | **AXIOM** | — | `axiom verificationTime : ∀ (L : DecisionProblem) (x c : ℕ), ℕ` |
| 70 | axiom | `creationTime` | **AXIOM** | — | `axiom creationTime : ∀ (L : DecisionProblem) (x : ℕ), ℕ` |
| 77 | def | `inNP` | **UNVERIFIED** | — | `def inNP (L : DecisionProblem) : Prop :=` |
| 86 | def | `verificationEffort` | **UNVERIFIED** | — | `noncomputable def verificationEffort (L : DecisionProblem) (x : ℕ) : ℕ :=` |
| 91 | def | `creationEffort` | **UNVERIFIED** | — | `noncomputable def creationEffort (L : DecisionProblem) (x : ℕ) : ℕ :=` |
| 95 | def | `asymmetryRatio` | **UNVERIFIED** | — | `noncomputable def asymmetryRatio (L : DecisionProblem) (x : ℕ) : ℝ :=` |
| 117 | axiom | `p_ne_np_gap` | **AXIOM** | — | `axiom p_ne_np_gap : ∃ L : DecisionProblem, inNP L ∧ ¬ inP L` |
| 122 | axiom | `creation_superpolynomial` | **AXIOM** | — | `axiom creation_superpolynomial :` |
| 129 | axiom | `asymmetry_unbounded` | **AXIOM** | — | `axiom asymmetry_unbounded :` |
| 144 | theorem | `creation_is_np_hard` | **UNVERIFIED** | — | `theorem creation_is_np_hard : ∃ L : DecisionProblem, inNP L ∧` |
| 151 | theorem | `asymmetry_ratio_diverges` | **UNVERIFIED** | — | `theorem asymmetry_ratio_diverges : ∃ L : DecisionProblem, inNP L ∧` |
| 159 | theorem | `creation_verification_asymmetry` | **UNVERIFIED** | exact, by (tactic) | `theorem creation_verification_asymmetry :` |
| 203 | theorem | `pvsnp_creation_vern_gap` | **UNVERIFIED** | simp, linarith, exact | `theorem pvsnp_creation_vern_gap :` |
| 251 | structure | `FORCE` | **UNVERIFIED** | — | `structure FORCE the desired structural consequence?"` |
| 312 | def | `vern_guided_collapse` | **UNVERIFIED** | — | `def vern_guided_collapse (L : DecisionProblem) (x c : ℕ) : Prop :=` |
| 318 | def | `blind_mr_collapse` | **UNVERIFIED** | — | `def blind_mr_collapse (L : DecisionProblem) (x : ℕ) : Prop :=` |
| 338 | axiom | `mr_nonalgorithmic` | **AXIOM** | — | `axiom mr_nonalgorithmic :` |
| 346 | theorem | `sat_requires_blind_mr` | **UNVERIFIED** | exact, by (tactic) | `theorem sat_requires_blind_mr :` |
| 356 | theorem | `p_ne_np_from_mr` | **UNVERIFIED** | — | `theorem p_ne_np_from_mr : ∃ L : DecisionProblem, inNP L ∧ ¬ inP L :=` |
| 369 | theorem | `mr_beats_kolmogorov_explanation` | **UNVERIFIED** | — | `theorem mr_beats_kolmogorov_explanation :` |
| 380 | theorem | `mr_p_ne_np_proof_chain` | **UNVERIFIED** | — | `theorem mr_p_ne_np_proof_chain :` |
| 524 | inductive | `TruthVal` | **UNVERIFIED** | — | `inductive TruthVal : Type` |
| 535 | def | `TuringComputation` | **UNVERIFIED** | — | `def TuringComputation := ℕ → Bool` |
| 538 | def | `embed_turing` | **UNVERIFIED** | — | `def embed_turing (f : TuringComputation) : CrystalComputation :=` |
| 544 | theorem | `tralse_not_turing` | **UNVERIFIED** | simp, exact, by (tactic) | `theorem tralse_not_turing :` |
| 555 | theorem | `crystal_incompleteness` | **UNVERIFIED** | exact, by (tactic) | `theorem crystal_incompleteness :` |
| 566 | theorem | `ctt_incompleteness_of_scope` | **UNVERIFIED** | exact, by (tactic) | `theorem ctt_incompleteness_of_scope :` |
| 607 | axiom | `crystal_instantiates_mr` | **AXIOM** | — | `axiom crystal_instantiates_mr :` |
| 619 | theorem | `crystal_defeats_ctt_from_axiom` | **UNVERIFIED** | — | `theorem crystal_defeats_ctt_from_axiom :` |

### `lean4/RiemannUOP.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 66 | theorem | `fixedPoint_real` | **UNVERIFIED** | linarith, by (tactic) | `theorem fixedPoint_real (σ : ℝ) : σ = 1 - σ ↔ σ = 1 / 2 := by` |
| 72 | theorem | `fixedPoint_re` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem fixedPoint_re (s : ℂ) (h : s = 1 - s) : s.re = 1 / 2 := by` |
| 78 | theorem | `fixedPoint_im` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem fixedPoint_im (s : ℂ) (h : s = 1 - s) : s.im = 0 := by` |
| 84 | theorem | `fixedPoint_complex` | **UNVERIFIED** | simp, ring, exact | `theorem fixedPoint_complex (s : ℂ) : s = 1 - s ↔ s = (1 / 2 : ℝ) := by` |
| 106 | theorem | `ear_equidistance` | **UNVERIFIED** | simp, ring, by (tactic) | `theorem ear_equidistance (s : ℂ) :` |
| 121 | theorem | `critical_line_is_equidistant_locus` | **UNVERIFIED** | — | `theorem critical_line_is_equidistant_locus :` |
| 136 | theorem | `uop_upper_bound` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem uop_upper_bound (σ : ℝ) : min σ (1 - σ) ≤ 1 / 2 := by` |
| 143 | theorem | `uop_bound_achieved` | **UNVERIFIED** | by (tactic) | `theorem uop_bound_achieved : min (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 := by` |
| 147 | theorem | `uop_max_iff` | **UNVERIFIED** | norm_num, linarith, by (tactic) | `theorem uop_max_iff (σ : ℝ) : min σ (1 - σ) = 1 / 2 ↔ σ = 1 / 2 := by` |
| 158 | theorem | `uop_argmax` | **UNVERIFIED** | — | `theorem uop_argmax :` |
| 167 | theorem | `uop_unique_maximizer` | **UNVERIFIED** | exact, by (tactic) | `theorem uop_unique_maximizer (σ₁ σ₂ : ℝ)` |
| 186 | def | `lcc` | **UNVERIFIED** | — | `noncomputable def lcc (pd : ℝ) : ℝ := 1 - Real.exp (-pd)` |
| 189 | theorem | `lcc_hasDerivAt` | **UNVERIFIED** | simp, linarith, exact | `theorem lcc_hasDerivAt (pd : ℝ) : HasDerivAt lcc (Real.exp (-pd)) pd := by` |
| 199 | theorem | `lcc_deriv_pos` | **UNVERIFIED** | — | `theorem lcc_deriv_pos (pd : ℝ) : 0 < Real.exp (-pd) :=` |
| 203 | theorem | `lcc_strictMono` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem lcc_strictMono : StrictMono lcc := by` |
| 212 | theorem | `lcc_no_finite_max` | **UNVERIFIED** | linarith, by (tactic) | `theorem lcc_no_finite_max : ¬ ∃ pd : ℝ, ∀ x : ℝ, lcc x ≤ lcc pd := by` |
| 242 | theorem | `three_path_convergence` | **UNVERIFIED** | by (tactic) | `theorem three_path_convergence (s : ℂ) :` |
| 256 | theorem | `convergence_to_critical_line` | **UNVERIFIED** | exact, by (tactic) | `theorem convergence_to_critical_line (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 314 | axiom | `uop_gap` | **AXIOM** | — | `axiom uop_gap (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 335 | theorem | `riemann_hypothesis_conditional` | **UNVERIFIED** | exact, by (tactic) | `theorem riemann_hypothesis_conditional :` |
| 351 | theorem | `riemann_hypothesis_via_uop_maxmin` | **UNVERIFIED** | exact, by (tactic) | `theorem riemann_hypothesis_via_uop_maxmin :` |
| 423 | def | `zeroAction` | **UNVERIFIED** | — | `noncomputable def zeroAction (σ : ℝ) : ℝ := (σ - 1 / 2) ^ 2` |
| 426 | theorem | `zeroAction_nonneg` | **UNVERIFIED** | — | `theorem zeroAction_nonneg (σ : ℝ) : 0 ≤ zeroAction σ := sq_nonneg _` |
| 429 | theorem | `zeroAction_zero_iff` | **UNVERIFIED** | ring, linarith, by (tactic) | `theorem zeroAction_zero_iff (σ : ℝ) : zeroAction σ = 0 ↔ σ = 1 / 2 := by` |
| 439 | theorem | `zeroAction_symmetric` | **UNVERIFIED** | by (tactic) | `theorem zeroAction_symmetric (σ : ℝ) : zeroAction σ = zeroAction (1 - σ) := by` |
| 443 | theorem | `zeroAction_global_min` | **UNVERIFIED** | by (tactic) | `theorem zeroAction_global_min (σ : ℝ) : zeroAction (1 / 2) ≤ zeroAction σ := by` |
| 447 | theorem | `zeroAction_unique_minimizer` | **UNVERIFIED** | — | `theorem zeroAction_unique_minimizer (σ : ℝ) (hs : σ ∈ Set.Ioo (0 : ℝ) 1)` |
| 476 | theorem | `equidist_iff_critical` | **UNVERIFIED** | — | `theorem equidist_iff_critical (s : ℂ) :` |
| 482 | theorem | `off_critical_different_moduli` | **UNVERIFIED** | exact, by (tactic) | `theorem off_critical_different_moduli (s : ℂ) (h : s.re ≠ 1 / 2) :` |
| 489 | theorem | `zero_pair_total_action` | **UNVERIFIED** | ring, by (tactic) | `theorem zero_pair_total_action (σ : ℝ) :` |
| 494 | theorem | `critical_pair_zero_action` | **UNVERIFIED** | norm_num, by (tactic) | `theorem critical_pair_zero_action :` |
| 499 | theorem | `off_critical_pair_positive_action` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem off_critical_pair_positive_action (σ : ℝ) (h : σ ≠ 1 / 2) :` |
| 510 | theorem | `action_minimizer_iff_critical` | **UNVERIFIED** | norm_num, exact, by (tactic) | `theorem action_minimizer_iff_critical (σ : ℝ) :` |
| 552 | structure | `SpectralWitness` | **UNVERIFIED** | — | `structure SpectralWitness where` |
| 570 | theorem | `hilbert_polya_witness` | **UNVERIFIED** | simp, by (tactic) | `theorem hilbert_polya_witness (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 582 | theorem | `hilbert_polya_implies_uop_gap` | **UNVERIFIED** | simp, exact, by (tactic) | `theorem hilbert_polya_implies_uop_gap (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 592 | theorem | `riemann_hypothesis_via_hilbert_polya` | **UNVERIFIED** | — | `theorem riemann_hypothesis_via_hilbert_polya :` |
| 628 | def | `PLA_Condition` | **UNVERIFIED** | — | `def PLA_Condition : Prop :=` |
| 633 | theorem | `pla_implies_uop_gap` | **UNVERIFIED** | exact, by (tactic) | `theorem pla_implies_uop_gap (hpla : PLA_Condition) (s : ℂ)` |
| 641 | theorem | `riemann_hypothesis_via_pla` | **UNVERIFIED** | — | `theorem riemann_hypothesis_via_pla (hpla : PLA_Condition) :` |
| 651 | theorem | `rh_three_gap_formulations` | **UNVERIFIED** | — | `theorem rh_three_gap_formulations :` |
| 718 | theorem | `ubt_grounds_uop_gap` | **UNVERIFIED** | — | `theorem ubt_grounds_uop_gap :` |
| 727 | theorem | `rh_full_equivalence` | **UNVERIFIED** | exact, by (tactic) | `theorem rh_full_equivalence (s : ℂ) (hs : s.re ∈ Set.Ioo 0 1)` |
| 786 | def | `BK_Action` | **UNVERIFIED** | — | `def BK_Action (u : ℝ → ℂ) (u_deriv : ℝ → ℂ) : ℝ → ℂ :=` |
| 810 | theorem | `bk_formal_symmetry_algebra` | **UNVERIFIED** | simp, ring, by (tactic) | `theorem bk_formal_symmetry_algebra (a b c d : ℂ) :` |
| 822 | def | `bk_lagrangian` | **UNVERIFIED** | — | `noncomputable def bk_lagrangian (s : ℂ) : ℂ := s * (1 - s)` |
| 827 | theorem | `bk_lagrangian_critical` | **UNVERIFIED** | simp, ring, linarith | `theorem bk_lagrangian_critical (s : ℂ) :` |
| 838 | theorem | `bk_lagrangian_critical_re` | **UNVERIFIED** | ring, linarith, by (tactic) | `theorem bk_lagrangian_critical_re (σ : ℝ) :` |
| 847 | theorem | `bk_classical_selects_critical_line` | **UNVERIFIED** | by (tactic) | `theorem bk_classical_selects_critical_line :` |
| 879 | axiom | `bk_selfadjoint` | **AXIOM** | — | `axiom bk_selfadjoint :` |
| 890 | axiom | `bk_spectrum` | **AXIOM** | — | `axiom bk_spectrum :` |
| 908 | theorem | `bk_zero_on_critical` | **UNVERIFIED** | simp, by (tactic) | `theorem bk_zero_on_critical (t : ℝ) :` |
| 914 | theorem | `bk_form_implies_equidistance` | **UNVERIFIED** | exact, by (tactic) | `theorem bk_form_implies_equidistance (t : ℝ) :` |
| 923 | theorem | `bk_zero_re` | **UNVERIFIED** | — | `theorem bk_zero_re (t : ℝ) (ht : riemannZeta ((1 / 2 : ℂ) + Complex.I * t) = 0) :` |
| 932 | theorem | `rh_from_bk_spectral_form` | **UNVERIFIED** | exact, by (tactic) | `theorem rh_from_bk_spectral_form` |
| 953 | theorem | `bk_decomposition_certificate` | **UNVERIFIED** | — | `theorem bk_decomposition_certificate :` |
| 968 | theorem | `pla_bk_convergence` | **UNVERIFIED** | — | `theorem pla_bk_convergence (σ : ℝ) :` |
| 982 | theorem | `four_path_convergence` | **UNVERIFIED** | by (tactic) | `theorem four_path_convergence (σ : ℝ) (s : ℂ) (hs_eq : s.re = σ)` |

### `lean4/TI/LxE.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 20 | structure | `Love` | **UNVERIFIED** | — | `structure Love where` |
| 27 | structure | `Existence` | **UNVERIFIED** | — | `structure Existence where` |
| 38 | def | `causation_threshold` | **UNVERIFIED** | — | `def causation_threshold : ℝ := 0.85` |
| 42 | def | `noise_floor` | **UNVERIFIED** | — | `def noise_floor : ℝ := 0.42` |
| 45 | theorem | `LxE_bounded` | **UNVERIFIED** | rfl, linarith, exact | `theorem LxE_bounded (L : Love) (E : Existence) :` |
| 54 | def | `true_tralseness` | **UNVERIFIED** | — | `def true_tralseness : ℝ := 0.92 * 0.92` |
| 59 | theorem | `causation_threshold_theorem` | **UNVERIFIED** | norm_num, rfl, by (tactic) | `theorem causation_threshold_theorem (L : Love) (E : Existence)` |
| 68 | theorem | `LxE_comm` | **UNVERIFIED** | — | `theorem LxE_comm (L : Love) (E : Existence) :` |
| 72 | def | `in_signal_range` | **UNVERIFIED** | — | `def in_signal_range (x : ℝ) : Prop := noise_floor ≤ x ∧ x ≤ 1` |
| 77 | theorem | `sqrt_causation` | **UNVERIFIED** | norm_num, linarith, by (tactic) | `theorem sqrt_causation (L : Love) (E : Existence)` |
| 96 | structure | `Tralse` | **UNVERIFIED** | — | `structure Tralse where` |
| 102 | inductive | `TralseCategory` | **UNVERIFIED** | — | `inductive TralseCategory` |
| 116 | theorem | `binary_is_special_case` | **UNVERIFIED** | simp, by (tactic) | `theorem binary_is_special_case (t : Tralse) (h : t.val = 0 ∨ t.val = 1) :` |
| 129 | theorem | `tralse_existence_implies_binary_incomplete` | **UNVERIFIED** | linarith, by (tactic) | `theorem tralse_existence_implies_binary_incomplete (t : Tralse)` |

### `lean4/TISigma.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 42 | def | `φ` | **UNVERIFIED** | — | `noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2` |
| 45 | def | `LCC_HIGH` | **UNVERIFIED** | — | `noncomputable def LCC_HIGH : ℝ := 1 / Real.sqrt 2` |
| 48 | def | `LCC_RADIANT` | **UNVERIFIED** | — | `noncomputable def LCC_RADIANT : ℝ := 1 / φ` |
| 52 | def | `C_EMERICK` | **UNVERIFIED** | — | `noncomputable def C_EMERICK : ℝ := 1 / (φ * Real.sqrt 2)` |
| 59 | lemma | `sqrt5_pos` | **UNVERIFIED** | — | `private lemma sqrt5_pos : 0 < Real.sqrt 5 :=` |
| 62 | lemma | `sqrt2_pos` | **UNVERIFIED** | — | `private lemma sqrt2_pos : 0 < Real.sqrt 2 :=` |
| 65 | lemma | `φ_pos` | **UNVERIFIED** | by (tactic) | `private lemma φ_pos : 0 < φ := by` |
| 68 | lemma | `C_EMERICK_pos` | **UNVERIFIED** | — | `private lemma C_EMERICK_pos : 0 < C_EMERICK :=` |
| 71 | lemma | `φ_ne` | **UNVERIFIED** | — | `private lemma φ_ne : φ ≠ 0 := φ_pos.ne'` |
| 73 | lemma | `sqrt2_ne` | **UNVERIFIED** | — | `private lemma sqrt2_ne : Real.sqrt 2 ≠ 0 := sqrt2_pos.ne'` |
| 76 | lemma | `sqrt2_gt_one` | **UNVERIFIED** | norm_num, by (tactic) | `private lemma sqrt2_gt_one : 1 < Real.sqrt 2 :=` |
| 81 | lemma | `φ_gt_one` | **UNVERIFIED** | by (tactic) | `private lemma φ_gt_one : 1 < φ := by` |
| 85 | lemma | `φ_gt_sqrt2` | **UNVERIFIED** | norm_num, linarith, by (tactic) | `private lemma φ_gt_sqrt2 : Real.sqrt 2 < φ := by` |
| 110 | theorem | `golden_ratio_identity` | **UNVERIFIED** | by (tactic) | `theorem golden_ratio_identity : φ ^ 2 = φ + 1 := by` |
| 130 | theorem | `emerick_normalization` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_normalization : Real.sqrt 2 * φ * C_EMERICK = 1 := by` |
| 155 | theorem | `emerick_product_structure` | **UNVERIFIED** | ring, by (tactic) | `theorem emerick_product_structure : C_EMERICK = LCC_RADIANT * LCC_HIGH := by` |
| 179 | theorem | `lcc_ordering` | **UNVERIFIED** | linarith, exact, by (tactic) | `theorem lcc_ordering :` |
| 218 | theorem | `extended_euler_identity` | **UNVERIFIED** | norm_num, by (tactic) | `theorem extended_euler_identity :` |

### `lean4/VariationalRoute.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 49 | def | `pairCost` | **UNVERIFIED** | — | `noncomputable def pairCost (σ : ℝ) : ℝ := -min σ (1 - σ)` |
| 52 | theorem | `pairCost_at_half` | **UNVERIFIED** | by (tactic) | `theorem pairCost_at_half : pairCost (1/2) = -(1/2) := by` |
| 56 | theorem | `pairCost_lower_bound` | **UNVERIFIED** | simp, linarith, exact | `theorem pairCost_lower_bound (σ : ℝ) : pairCost σ ≥ -(1/2) := by` |
| 64 | theorem | `pairCost_min_iff` | **UNVERIFIED** | norm_num, linarith, by (tactic) | `theorem pairCost_min_iff (σ : ℝ) : pairCost σ = -(1/2) ↔ σ = 1/2 := by` |
| 75 | theorem | `pairCost_strict_off_axis` | **UNVERIFIED** | linarith, by (tactic) | `theorem pairCost_strict_off_axis (σ : ℝ) (h : σ ≠ 1/2) :` |
| 82 | theorem | `pairCost_symm` | **UNVERIFIED** | by (tactic) | `theorem pairCost_symm (σ : ℝ) : pairCost σ = pairCost (1 - σ) := by` |
| 97 | theorem | `variational_unique_minimum` | **UNVERIFIED** | norm_num, exact, by (tactic) | `theorem variational_unique_minimum :` |
| 114 | theorem | `pairCost_decreasing_left` | **UNVERIFIED** | simp, linarith, exact | `theorem pairCost_decreasing_left : StrictMonoOn (fun σ => pairCost σ)` |
| 126 | theorem | `pairCost_increasing_right` | **UNVERIFIED** | simp, linarith, by (tactic) | `theorem pairCost_increasing_right : StrictMonoOn (fun σ => pairCost σ)` |
| 148 | theorem | `euler_lagrange_at_half` | **UNVERIFIED** | linarith, by (tactic) | `theorem euler_lagrange_at_half :` |
| 177 | theorem | `rh_from_euler_lagrange` | **UNVERIFIED** | exact, by (tactic) | `theorem rh_from_euler_lagrange :` |
| 199 | axiom | `variational_gap` | **AXIOM** | — | `axiom variational_gap (s : ℂ) (hs : s.re ∈ Set.Ioo (0:ℝ) 1)` |
| 210 | theorem | `riemann_hypothesis_variational` | **UNVERIFIED** | — | `theorem riemann_hypothesis_variational :` |

### `lean4/YangMills.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 63 | structure | `YMExcitation` | **UNVERIFIED** | — | `structure YMExcitation where` |
| 71 | axiom | `ymMass` | **AXIOM** | — | `axiom ymMass : YMExcitation → ℝ` |
| 74 | axiom | `ymMass_vacuum` | **AXIOM** | — | `axiom ymMass_vacuum : ymMass vacuum = 0` |
| 77 | axiom | `ymMass_nonneg` | **AXIOM** | — | `axiom ymMass_nonneg : ∀ e : YMExcitation, 0 ≤ ymMass e` |
| 89 | theorem | `vacuum_is_effortless` | **UNVERIFIED** | — | `theorem vacuum_is_effortless : ymEffort vacuum = 0 := ymMass_vacuum` |
| 92 | theorem | `ymEffort_nonneg` | **UNVERIFIED** | — | `theorem ymEffort_nonneg (e : YMExcitation) : 0 ≤ ymEffort e := ymMass_nonneg e` |
| 105 | axiom | `yang_mills_existence` | **AXIOM** | — | `axiom yang_mills_existence : ∃ e : YMExcitation, e.isVacuum = false` |
| 115 | axiom | `yang_mills_gap` | **AXIOM** | — | `axiom yang_mills_gap : ∃ Δ : ℝ, 0 < Δ ∧` |
| 125 | theorem | `ymGap_theorem` | **UNVERIFIED** | exact, by (tactic) | `theorem ymGap_theorem : ∃ Δ : ℝ, 0 < Δ ∧` |
| 132 | theorem | `ymEffortless_is_vacuum` | **UNVERIFIED** | rfl, linarith, exact | `theorem ymEffortless_is_vacuum (e : YMExcitation) (h : ymEffort e = 0) :` |
| 145 | axiom | `ymMass_vacuum_general` | **AXIOM** | — | `axiom ymMass_vacuum_general (e : YMExcitation) (h : e.isVacuum = true) :` |
| 151 | theorem | `ymBeing_theorem` | **UNVERIFIED** | — | `theorem ymBeing_theorem (e : YMExcitation) :` |
| 196 | theorem | `ym_being_duality` | **UNVERIFIED** | exact, by (tactic) | `theorem ym_being_duality :` |
| 250 | theorem | `ym_spectral_gap` | **UNVERIFIED** | exact, by (tactic) | `theorem ym_spectral_gap :` |
| 277 | theorem | `ym_euler_forcing_gap_statement` | **UNVERIFIED** | simp, by (tactic) | `theorem ym_euler_forcing_gap_statement :` |

### `lean4_collatz/CollatzNu2.lean`

*File prose claims machine verification / sorry-free.*

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 51 | def | `collatzStep` | **UNVERIFIED** | — | `def collatzStep (n : ℕ) : ℕ :=` |
| 55 | def | `collatzCompound` | **UNVERIFIED** | — | `noncomputable def collatzCompound (n : ℕ) : ℕ :=` |
| 59 | def | `isK1Step` | **UNVERIFIED** | — | `def isK1Step (n : ℕ) : Prop := padicValNat 2 (3 * n + 1) = 1` |
| 66 | theorem | `k1_iff_mod4` | **UNVERIFIED** | norm_num, simp, linarith | `theorem k1_iff_mod4 {n : ℕ} (hodd : n % 2 = 1) :` |
| 103 | theorem | `k1_result_odd` | **UNVERIFIED** | by (tactic) | `theorem k1_result_odd {n : ℕ} (hn : n % 4 = 3) :` |
| 112 | theorem | `nprime_succ_eq_6k` | **UNVERIFIED** | by (tactic) | `theorem nprime_succ_eq_6k {n k : ℕ} (hk : n + 1 = 4 * k) (hkpos : 0 < k) :` |
| 118 | theorem | `nprime_succ_formula` | **UNVERIFIED** | by (tactic) | `theorem nprime_succ_formula {n : ℕ} (hn : n % 4 = 3) :` |
| 139 | theorem | `padicValNat_4k` | **UNVERIFIED** | norm_num, ring, by (tactic) | `theorem padicValNat_4k {k : ℕ} (hk : 0 < k) :` |
| 153 | theorem | `padicValNat_3m` | **UNVERIFIED** | norm_num, by (tactic) | `theorem padicValNat_3m {m : ℕ} (hm : 0 < m) :` |
| 160 | theorem | `padicValNat_6k` | **UNVERIFIED** | norm_num, by (tactic) | `theorem padicValNat_6k {k : ℕ} (hk : 0 < k) :` |
| 172 | theorem | `nu2_collatz_countdown` | **UNVERIFIED** | by (tactic) | `theorem nu2_collatz_countdown {n : ℕ} (hn : n % 4 = 3) :` |
| 199 | theorem | `nu2_after_k1_run` | **UNVERIFIED** | simp, ring, exact | `theorem nu2_after_k1_run :` |
| 247 | theorem | `k1_run_bound` | **UNVERIFIED** | norm_num, simp, exact | `theorem k1_run_bound {n : ℕ} (hn : n % 4 = 3) :` |
| 295 | def | `ternaryLSB` | **UNVERIFIED** | norm_num, by (tactic) | `def ternaryLSB (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩` |
| 300 | theorem | `ternary_lsb_first_halving` | **UNVERIFIED** | simp, by (tactic) | `theorem ternary_lsb_first_halving {n : ℕ} (hodd : n % 2 = 1) :` |
| 311 | theorem | `alternating_lsb` | **UNVERIFIED** | norm_num, simp, ring | `theorem alternating_lsb {n : ℕ} (hodd : n % 2 = 1) (j : ℕ) (hj : 1 ≤ j)` |

### `lean4_ns_uop/NavierStokes/EnergyIneq.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 18 | axiom | `leray_energy_inequality` | **AXIOM** | — | `axiom leray_energy_inequality` |

### `lean4_ns_uop/NavierStokes/Equation.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 18 | axiom | `smooth_implies_weak` | **AXIOM** | — | `axiom smooth_implies_weak` |

### `lean4_ns_uop/NavierStokes/UOPGap.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 46 | axiom | `UOP_existence_claim` | **AXIOM** | — | `axiom UOP_existence_claim` |
| 69 | theorem | `UOP_implies_NS_smoothness` | **SORRY** | sorry, by (tactic) | `theorem UOP_implies_NS_smoothness` |
| 84 | def | `UOP_falsifier_specification` | **UNVERIFIED** | — | `def UOP_falsifier_specification : Prop :=` |

### `lean4_ns_uop_pass54_mathlib/NavierStokes/EnergyIneq.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 14 | axiom | `leray_energy_inequality` | **AXIOM** | — | `axiom leray_energy_inequality` |

### `lean4_ns_uop_pass54_mathlib/NavierStokes/Equation.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 15 | axiom | `smooth_implies_weak` | **AXIOM** | — | `axiom smooth_implies_weak` |

### `lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 32 | def | `Energy` | **UNVERIFIED** | — | `noncomputable def Energy (u₀ c t : ℝ) : ℝ := u₀^2 * Real.exp (-(c * t))` |
| 35 | theorem | `energy_nonneg` | **UNVERIFIED** | exact, by (tactic) | `theorem energy_nonneg (u₀ c t : ℝ) : 0 ≤ Energy u₀ c t := by` |
| 40 | theorem | `energy_at_zero` | **UNVERIFIED** | by (tactic) | `theorem energy_at_zero (u₀ c : ℝ) : Energy u₀ c 0 = u₀^2 := by` |
| 46 | theorem | `energy_monotone_decay` | **UNVERIFIED** | linarith, by (tactic) | `theorem energy_monotone_decay` |

### `lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 40 | axiom | `UOP_existence_claim` | **AXIOM** | — | `axiom UOP_existence_claim` |
| 54 | theorem | `UOP_implies_NS_smoothness` | **SORRY** | sorry, by (tactic) | `theorem UOP_implies_NS_smoothness` |
| 62 | def | `UOP_falsifier_specification` | **UNVERIFIED** | — | `def UOP_falsifier_specification : Prop :=` |

### `lean4_submission/fine_structure_consciousness.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 24 | def | `e` | **UNVERIFIED** | — | `noncomputable def e : ℝ := Real.exp 1` |
| 27 | def | `π` | **UNVERIFIED** | — | `noncomputable def π : ℝ := Real.pi` |
| 30 | def | `d_spacetime` | **UNVERIFIED** | — | `def d_spacetime : ℕ := 4` |
| 33 | def | `d_mtheory` | **UNVERIFIED** | — | `def d_mtheory : ℕ := 11` |
| 36 | def | `α_measured` | **UNVERIFIED** | — | `noncomputable def α_measured : ℝ := 1 / 137.035999` |
| 44 | theorem | `dimension_decomposition` | **UNVERIFIED** | by (tactic) | `theorem dimension_decomposition : 137 = 11^2 + 4^2 := by` |
| 48 | theorem | `dimension_decomposition'` | **UNVERIFIED** | norm_num, by (tactic) | `theorem dimension_decomposition' : 137 = d_mtheory^2 + d_spacetime^2 := by` |
| 60 | def | `α_derived` | **UNVERIFIED** | — | `noncomputable def α_derived : ℝ := 1 / (d_spacetime^2 * e * π)` |
| 76 | theorem | `derivation_accuracy` | **SORRY** | by sorry, sorry, by (tactic) | `theorem derivation_accuracy :` |
| 92 | structure | `ObservationStructure` | **UNVERIFIED** | — | `structure ObservationStructure where` |
| 101 | def | `our_universe` | **UNVERIFIED** | — | `noncomputable def our_universe : ObservationStructure :=` |
| 107 | theorem | `α_from_observation` | **UNVERIFIED** | simp, by (tactic) | `theorem α_from_observation :` |
| 120 | theorem | `euler_identity` | **UNVERIFIED** | simp, by (tactic) | `theorem euler_identity :` |
| 134 | def | `α_unified` | **UNVERIFIED** | — | `noncomputable def α_unified : ℝ := 1 / (d_mtheory^2 * e * π)` |
| 137 | theorem | `unification_scale_prediction` | **SORRY** | by sorry, sorry, by (tactic) | `theorem unification_scale_prediction :` |
| 156 | inductive | `AlphaDerivability` | **UNVERIFIED** | — | `inductive AlphaDerivability where` |

### `lean4_submission/p_np_sketch.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 17 | def | `P` | **UNVERIFIED** | — | `def P : Set (Set ℕ) :=` |
| 22 | def | `NP` | **UNVERIFIED** | — | `def NP : Set (Set ℕ) :=` |
| 48 | def | `certificateComplexity` | **UNVERIFIED** | — | `def certificateComplexity (L : Set ℕ) (x : ℕ) : ℕ :=` |
| 52 | def | `verificationComplexity` | **UNVERIFIED** | — | `def verificationComplexity (V : TuringMachine) (x c : ℕ) : ℕ :=` |
| 56 | def | `creationComplexity` | **SORRY** | sorry | `def creationComplexity (L : Set ℕ) (x : ℕ) : ℕ :=` |
| 78 | theorem | `certificate_information` | **SORRY** | by sorry, sorry, by (tactic) | `theorem certificate_information (L : Set ℕ) (x : ℕ) (hx : x ∈ L) :` |
| 90 | theorem | `creation_verification_asymmetry` | **SORRY** | by sorry, sorry, by (tactic) | `theorem creation_verification_asymmetry :` |
| 97 | theorem | `p_ne_np` | **SORRY** | by sorry, sorry, by (tactic) | `theorem p_ne_np : P ≠ NP := by` |

### `lean4_submission/riemann_sketch.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 18 | def | `criticalStrip` | **UNVERIFIED** | — | `def criticalStrip : Set ℂ := {s : ℂ \| 0 < s.re ∧ s.re < 1}` |
| 21 | def | `criticalLine` | **UNVERIFIED** | — | `def criticalLine : Set ℂ := {s : ℂ \| s.re = 1/2}` |
| 45 | def | `chi` | **UNVERIFIED** | — | `noncomputable def chi (s : ℂ) : ℂ :=` |
| 49 | theorem | `functional_equation` | **SORRY** | by sorry, sorry, by (tactic) | `theorem functional_equation (s : ℂ) (hs : s ∈ criticalStrip) :` |
| 57 | theorem | `zeros_paired` | **SORRY** | by sorry, sorry, by (tactic) | `theorem zeros_paired (s : ℂ) (hs : s ∈ criticalStrip)` |
| 71 | theorem | `dimensional_constraint` | **SORRY** | by sorry, sorry, by (tactic) | `theorem dimensional_constraint (s : ℂ) (hs : s ∈ criticalStrip)` |
| 77 | theorem | `riemann_hypothesis` | **UNVERIFIED** | exact, by (tactic) | `theorem riemann_hypothesis : ∀ s ∈ criticalStrip,` |

### `lean4_ti_sigma6/BSDProof.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 11 | axiom | `EllipticCurve` | **AXIOM** | — | `axiom EllipticCurve : Type` |
| 14 | axiom | `rank` | **AXIOM** | — | `axiom rank : EllipticCurve → ℕ` |
| 17 | axiom | `zero_order` | **AXIOM** | — | `axiom zero_order : EllipticCurve → ℕ` |
| 20 | axiom | `ccc_capacity` | **AXIOM** | — | `axiom ccc_capacity : EllipticCurve → ℕ` |
| 25 | axiom | `parallel_generation` | **AXIOM** | — | `axiom parallel_generation : ∀ E : EllipticCurve,` |
| 29 | axiom | `rational_point_discrete` | **AXIOM** | := sorry, sorry | `axiom rational_point_discrete : ∀ E : EllipticCurve, ∀ P : Point E,` |
| 36 | axiom | `curve_continuous` | **AXIOM** | — | `axiom curve_continuous : ∀ E : EllipticCurve,` |
| 40 | axiom | `generator_collapse` | **AXIOM** | := sorry, sorry | `axiom generator_collapse : ∀ E : EllipticCurve, ∀ P : Point E,` |
| 47 | axiom | `l_function_probe` | **AXIOM** | — | `axiom l_function_probe : ∀ E : EllipticCurve,` |
| 51 | lemma | `geometric_capacity` | **UNVERIFIED** | exact, by (tactic) | `lemma geometric_capacity (E : EllipticCurve) :` |
| 57 | lemma | `analytic_capacity` | **UNVERIFIED** | exact, by (tactic) | `lemma analytic_capacity (E : EllipticCurve) :` |
| 64 | theorem | `birch_swinnerton_dyer` | **UNVERIFIED** | by (tactic) | `theorem birch_swinnerton_dyer (E : EllipticCurve) :` |
| 70 | axiom | `height` | **AXIOM** | sorry | `axiom height : ∀ E : EllipticCurve, Point E → Point E → ℝ` |
| 74 | axiom | `height_coherence_relation` | **AXIOM** | sorry | `axiom height_coherence_relation : ∀ E : EllipticCurve, ∀ P Q : Point E,` |
| 79 | axiom | `regulator` | **AXIOM** | — | `axiom regulator : EllipticCurve → ℝ` |
| 81 | axiom | `regulator_is_coherence_det` | **AXIOM** | := sorry, sorry | `axiom regulator_is_coherence_det : ∀ E : EllipticCurve,` |
| 89 | axiom | `Sha` | **AXIOM** | — | `axiom Sha : EllipticCurve → Type` |
| 93 | axiom | `sha_stuck_phi` | **AXIOM** | — | `axiom sha_stuck_phi : ∀ E : EllipticCurve, ∀ x : Sha E,` |
| 100 | theorem | `sha_finite` | **SORRY** | by sorry, sorry, by (tactic) | `theorem sha_finite (E : EllipticCurve) :` |
| 110 | axiom | `sha_perfect_square` | **AXIOM** | — | `axiom sha_perfect_square (E : EllipticCurve) :` |
| 114 | axiom | `bsd_formula` | **AXIOM** | — | `axiom bsd_formula : ∀ E : EllipticCurve,` |
| 121 | axiom | `sacred_seven_resonance` | **AXIOM** | sorry | `axiom sacred_seven_resonance : ∀ E : EllipticCurve,` |
| 130 | theorem | `geometric_analytic_duality` | **UNVERIFIED** | rfl, exact, by (tactic) | `theorem geometric_analytic_duality (E : EllipticCurve) :` |

### `lean4_ti_sigma6/MyrionOperators.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 10 | def | `myrion_split` | **UNVERIFIED** | — | `def myrion_split : Tralse → Tralse × Tralse` |
| 17 | def | `myrion_merge` | **UNVERIFIED** | — | `def myrion_merge : Tralse × Tralse → Tralse` |
| 29 | def | `myrion_resolve` | **UNVERIFIED** | — | `def myrion_resolve : Tralse → Tralse → Tralse` |
| 44 | theorem | `myrion_reversibility_psi` | **UNVERIFIED** | rfl, by (tactic) | `theorem myrion_reversibility_psi :` |
| 49 | theorem | `myrion_reversibility_phi` | **UNVERIFIED** | rfl, by (tactic) | `theorem myrion_reversibility_phi :` |
| 55 | theorem | `contradiction_resolves_to_psi` | **UNVERIFIED** | rfl, by (tactic) | `theorem contradiction_resolves_to_psi :` |
| 60 | theorem | `myrion_resolve_comm` | **UNVERIFIED** | rfl, by (tactic) | `theorem myrion_resolve_comm (x y : Tralse) :` |
| 65 | theorem | `self_resolve_identity` | **UNVERIFIED** | rfl, by (tactic) | `theorem self_resolve_identity (x : Tralse) :` |
| 70 | axiom | `energy_conservation_split` | **AXIOM** | — | `axiom energy_conservation_split (x : Tralse) :` |
| 76 | theorem | `myrion_completeness` | **UNVERIFIED** | rfl, exact, by (tactic) | `theorem myrion_completeness (P : Tralse) :` |
| 85 | def | `dialectic` | **UNVERIFIED** | — | `def dialectic (thesis antithesis : Tralse) : Tralse :=` |
| 89 | theorem | `dialectic_opposites` | **UNVERIFIED** | simp, by (tactic) | `theorem dialectic_opposites (x : Tralse) :` |

### `lean4_ti_sigma6/RiemannProof.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 11 | axiom | `prime_is_discrete` | **AXIOM** | — | `axiom prime_is_discrete : ∀ p : ℕ, Nat.Prime p → ∃ t : Tralse, t = Tralse.T` |
| 14 | axiom | `complex_is_continuous` | **AXIOM** | — | `axiom complex_is_continuous : ∀ s : ℂ, ∃ phi : Tralse, phi = Tralse.Phi` |
| 17 | axiom | `zeta` | **AXIOM** | — | `axiom zeta : ℂ → ℂ` |
| 20 | axiom | `zero_is_collapse` | **AXIOM** | — | `axiom zero_is_collapse : ∀ s : ℂ, zeta s = 0 →` |
| 24 | axiom | `functional_equation` | **AXIOM** | — | `axiom functional_equation : ∀ s : ℂ,` |
| 33 | axiom | `symmetry_forces_resolution` | **AXIOM** | — | `axiom symmetry_forces_resolution : ∀ s : ℂ,` |
| 39 | lemma | `fixed_point_is_critical_line` | **SORRY** | sorry, simp, by (tactic) | `lemma fixed_point_is_critical_line (s : ℂ) :` |
| 48 | lemma | `discrete_continuous_boundary` | **UNVERIFIED** | rfl, by (tactic) | `lemma discrete_continuous_boundary :` |
| 58 | theorem | `riemann_hypothesis` | **SORRY** | by sorry, sorry, rfl | `theorem riemann_hypothesis : ∀ s : ℂ,` |
| 93 | theorem | `zeros_symmetric_or_critical` | **UNVERIFIED** | exact, by (tactic) | `theorem zeros_symmetric_or_critical : ∀ s : ℂ,` |
| 104 | axiom | `sacred_eleven_resonance` | **AXIOM** | — | `axiom sacred_eleven_resonance : ∀ n : ℕ,` |
| 113 | theorem | `freewill_analogy` | **SORRY** | by sorry, sorry, by (tactic) | `theorem freewill_analogy :` |

### `lean4_ti_sigma6/TralseLogic.lean`

Module olean: `NONE`

| Line | Kind | Name | Proof status | Proof style | Excerpt |
|-----:|------|------|--------------|-------------|--------|
| 8 | inductive | `Tralse` | **UNVERIFIED** | — | `inductive Tralse : Type where` |
| 15 | def | `tralse_not` | **UNVERIFIED** | — | `def tralse_not : Tralse → Tralse` |
| 22 | def | `tralse_and` | **UNVERIFIED** | — | `def tralse_and : Tralse → Tralse → Tralse` |
| 38 | def | `tralse_or` | **UNVERIFIED** | rfl, by (tactic) | `def tralse_or : Tralse → Tralse → Tralse` |
| 58 | theorem | `tralse_and_comm` | **UNVERIFIED** | by (tactic) | `theorem tralse_and_comm (x y : Tralse) : x ∧ₜ y = y ∧ₜ x := by` |
| 62 | theorem | `tralse_or_comm` | **UNVERIFIED** | by (tactic) | `theorem tralse_or_comm (x y : Tralse) : x ∨ₜ y = y ∨ₜ x := by` |
| 66 | theorem | `tralse_and_false` | **UNVERIFIED** | by (tactic) | `theorem tralse_and_false (x : Tralse) : x ∧ₜ Tralse.F = Tralse.F := by` |
| 70 | theorem | `tralse_or_true` | **UNVERIFIED** | by (tactic) | `theorem tralse_or_true (x : Tralse) : x ∨ₜ Tralse.T = Tralse.T := by` |
| 74 | def | `is_classical` | **UNVERIFIED** | — | `def is_classical : Tralse → Bool` |
| 81 | theorem | `classical_and_preserved` | **UNVERIFIED** | simp, by (tactic) | `theorem classical_and_preserved (x y : Tralse)` |
| 87 | axiom | `energy` | **AXIOM** | — | `axiom energy : Tralse → ℝ` |
| 90 | axiom | `energy_nonneg` | **AXIOM** | — | `axiom energy_nonneg (x : Tralse) : energy x ≥ 0` |
| 93 | axiom | `energy_ordering` | **AXIOM** | — | `axiom energy_ordering :` |
| 99 | axiom | `coherence` | **AXIOM** | — | `axiom coherence : Tralse → ℝ` |
| 102 | axiom | `coherence_bounds` | **AXIOM** | — | `axiom coherence_bounds (x : Tralse) : 0 ≤ coherence x ∧ coherence x ≤ 1` |
| 105 | axiom | `coherence_levels` | **AXIOM** | — | `axiom coherence_levels :` |
| 113 | def | `threshold_freewill` | **UNVERIFIED** | — | `def threshold_freewill : ℝ := 0.667` |

