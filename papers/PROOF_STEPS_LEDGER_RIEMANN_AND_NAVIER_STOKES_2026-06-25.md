# Proof-Steps Ledger — Riemann Hypothesis & Navier–Stokes (2026-06-25)

**Purpose.** A consolidated, *honest* inventory of the genuine machine-checked
proof steps accomplished across the corpus toward the two priority Millennium
problems. These steps **do not close either problem** — they are real, reusable
lemmas and clean conditional reductions that any genuine proof would build on or
plug into. This ledger exists so the audited reality lives next to the work.

**Honesty rails (#69 / UGI-1).** Real status only. The classification was
extracted from the Lean sources and verified by **reading the proof bodies**
after stripping comments/docstrings — including **transitive** axiom dependence
(a lemma that calls a helper which consumes a bridge axiom is counted
axiom-dependent, even though a surface grep, or a grep fooled by the word
"sorry" inside a docstring, would miss it).

## Key honest finding (read this first)

Across the five RH files (`RiemannUOP`, `VariationalRoute`, `GroupSymmetryRoute`,
`MirrorPairing`, `GapEquivalence`), `NavierStokes.lean`, and the pass54 NS scaffold
(`lean4_ns_uop_pass54_mathlib/NavierStokes/{ToyDecay,UOPGap}.lean`), there are
**exactly two genuine `sorry` stubs in the entire stack**:

1. `euler_forcing_attempt` (`lean4/MirrorPairing.lean`) — the one place someone
   tried to *derive* a bridge axiom from ζ's structure; still `sorry`.
2. `UOP_implies_NS_smoothness` (`lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean`).

Everything else is `sorry`-free. **But `sorry`-free does not mean "proves the
problem":** the RH capstones are `sorry`-free *because* they consume a single
bridge **axiom** that is itself a restatement of RH (these are VIA-AXIOM). The
genuine, content-bearing work is the **CLEAN** geometry + the **CLEAN-CONDITIONAL**
reductions that reduce RH to a *named, more tractable* condition.

## Legend

| Tag | Meaning |
|---|---|
| **CLEAN** | No `sorry`, no transitive dependence on any axiom. A genuine self-contained result. |
| **CLEAN-CONDITIONAL** | `sorry`-free implication *IF (independently-stated hypothesis) THEN …*; the hypothesis is a parameter, **not** an axiom. Real content. |
| **VIA-AXIOM** | Complete (no `sorry`) but consumes a bridge axiom (directly or transitively). For RH the bridge axioms are *equivalent to RH itself*, so these add **no** content beyond the assumption. |
| **SORRY** | Incomplete. **Not** a proof step. |
| **AXIOM** | A pure assumption. **Not** a proof step (either the conclusion itself, or a real literature theorem encoded as an axiom and not reproven here). |

---

# PART I — Riemann Hypothesis

**What is genuinely established.** Across multiple independent characterizations,
the critical line `Re(s) = 1/2` is the **unique** locus selected, and these
characterizations are proven **mutually equivalent**, all `sorry`-free and
axiom-free. This is real, reusable geometry. What remains *unproven* is the
single analytic fact that the non-trivial zeros of ζ actually satisfy any one of
these conditions — that fact is `uop_gap` (and its four equivalents), which is
logically equivalent to RH.

## I.1 Closed-clean building blocks (no `sorry`, no axiom)

### Fixed-point / equidistance geometry — `lean4/RiemannUOP.lean`
| Lemma | Statement (verbatim) | Establishes |
|---|---|---|
| `fixedPoint_real` | `(σ : ℝ) : σ = 1 - σ ↔ σ = 1 / 2` | 1/2 is the unique real reflection fixed point |
| `fixedPoint_re` | `(s : ℂ) (h : s = 1 - s) : s.re = 1 / 2` | fixed point of `s ↦ 1−s` forces `Re = 1/2` |
| `fixedPoint_im`, `fixedPoint_complex` | — | imaginary part free; full ℂ statement |
| `ear_equidistance` | `(s : ℂ) : normSq s = normSq (1 - s) ↔ s.re = 1 / 2` | critical line = locus equidistant from 0 and 1 |
| `equidist_iff_critical`, `critical_line_is_equidistant_locus` | — | restatements used downstream |
| `off_critical_different_moduli` | — | off-line zeros break equidistance |

### UOP max-min selection — `lean4/RiemannUOP.lean`
`uop_max_iff` (`min σ (1-σ) = 1/2 ↔ σ = 1/2`), `uop_upper_bound`,
`uop_bound_achieved`, `uop_argmax`, `uop_unique_maximizer` — the max-min
principle uniquely selects 1/2 (bound, attainment, uniqueness).

### Zero-action (variational) cost — `lean4/RiemannUOP.lean`
`zeroAction_zero_iff` (`zeroAction σ = 0 ↔ σ = 1/2`), `zeroAction_nonneg`,
`zeroAction_symmetric`, `zeroAction_global_min`, `zeroAction_unique_minimizer`,
`zero_pair_total_action`, `critical_pair_zero_action`,
`off_critical_pair_positive_action`, `action_minimizer_iff_critical`,
`lcc_hasDerivAt`, `lcc_deriv_pos`, `lcc_strictMono`, `lcc_no_finite_max` — the
cost vanishes only on the critical line; the LCC utility is strictly monotone
with no finite max.

### Berry–Keating Lagrangian — *classical* part only — `lean4/RiemannUOP.lean`
`bk_formal_symmetry_algebra`, `bk_lagrangian_critical`,
`bk_lagrangian_critical_re`, `bk_classical_selects_critical_line`,
`bk_zero_on_critical`, `bk_form_implies_equidistance`, `bk_zero_re`,
`pla_bk_convergence`, `four_path_convergence` — the classical Lagrangian
`L = s(1−s)` has its critical point at `s = 1/2`, and a zero of the algebraic
form `1/2 + it` provably has `Re = 1/2`. **The self-adjoint operator / spectrum
is still open** (see I.4).

### Variational route — `lean4/VariationalRoute.lean`
`pairCost_at_half`, `pairCost_lower_bound`, `pairCost_min_iff`,
`pairCost_strict_off_axis`, `pairCost_symm`, `variational_unique_minimum`,
`pairCost_decreasing_left`, `pairCost_increasing_right`, `euler_lagrange_at_half`
— the pair-cost functional has a unique minimum `-(1/2)` at `σ = 1/2`, strictly
increasing off-axis.

### Group-symmetry route — `lean4/GroupSymmetryRoute.lean`
`S₁_involution`, `S₂_involution`, `S₁S₂_involution`, `S₁_S₂_commute`,
`S₁S₂_eq_S₂S₁`, `gOrbit_explicit`, `orbit_collapse_iff_critical`,
`orbit_collapse_S₁S₂_fixes`, `orbit_size_4_when_off_axis`,
`hadamard_self_paired_iff_critical`, `hadamardPartner_is_S₁S₂`,
`hadamard_orbit_critical_equivalence`, `routes_BC_equivalent` — the reflection
group acts by commuting involutions; the orbit of a zero collapses **iff** it is
on the critical line (off-axis ⇒ orbit size 4).

### Mirror-pairing route — `lean4/MirrorPairing.lean`
`mirror_pairing_iff_critical`, `mirror_pairing_re`, `mirror_pairing_im_free`,
`quadruple_to_pair`, `off_axis_gives_quadruple`,
`mirror_pairing_equiv_equidistance`, `uopEnergy_minimum`, `uopEnergy_unique_min`
— `conj s = 1 − s ⟺ Re(s) = 1/2`; off-axis zeros come in quadruples; UOP energy
minimized on-line.

### Equivalence of the routes — `lean4/GapEquivalence.lean`
`condA_iff_critical`, `condBC_iff_critical`, `condMirror_iff_critical`,
`condUOP_iff_critical`, `gap_equivalence`, `any_gap_implies_all`,
`all_gaps_equivalent` — the geometric, group/Hadamard, mirror, and UOP
characterizations are proven **mutually equivalent** (each reduces to `Re = 1/2`),
all `sorry`-free.

### Cross-cutting algebraic identities — `lean4/TISigma.lean`
`golden_ratio_identity` (`φ² = φ + 1`), `emerick_normalization`
(`√2·φ·C = 1`), `emerick_product_structure`, `lcc_ordering`,
`extended_euler_identity` (+ positivity helpers `φ_pos`, `sqrt2_pos`, …) —
`sorry`-free, axiom-free constants/identities.

## I.2 Genuine clean conditional reductions (real "IF–THEN" content)

These take an **independently-stated** condition as a hypothesis and discharge it
to RH (or to the equidistance gap) with no axiom — honest theorems *reducing* RH
to a named, more tractable condition:

| Theorem | File | Content |
|---|---|---|
| `pla_implies_uop_gap (hpla : PLA_Condition)` | `RiemannUOP.lean` | IF every zero minimizes the zero-action THEN equidistance holds (uses only `zeroAction_zero_iff` + `ear_equidistance`). |
| `riemann_hypothesis_via_pla (hpla : PLA_Condition)` | `RiemannUOP.lean` | IF PLA THEN RH. |
| `rh_three_gap_formulations` | `RiemannUOP.lean` | IF (all zeros equidistant) THEN RH — the shared clean final step. |
| `convergence_to_critical_line` | `RiemannUOP.lean` | IF (a zero satisfies fixed-point ∨ equidistance ∨ UOP-maxmin) THEN `Re = 1/2`. |
| `rh_from_bk_spectral_form` | `RiemannUOP.lean` | IF (all zeros have the form `1/2 + it`, real `t`) THEN RH. |
| `bk_decomposition_certificate` | `RiemannUOP.lean` | strategic certificate (= `rh_from_bk_spectral_form`): the BK path is a *decomposition* of `uop_gap`. |
| `rh_from_euler_lagrange` | `VariationalRoute.lean` | clean Euler–Lagrange ⇒ critical-line step. |

## I.3 Reductions that consume a bridge axiom (VIA-AXIOM — *no new content*)

Each is a complete proof, but consumes a single bridge axiom that **is itself a
restatement of RH** (the five bridge axioms are proven equivalent by
`gap_equivalence` / `all_gaps_equivalent`). So these establish nothing beyond the
assumption — they are honest "GIVEN-RH-in-one-form, RH-in-another-form" packaging:

| Bridge axiom consumed | VIA-AXIOM theorems |
|---|---|
| `uop_gap` (`RiemannUOP.lean`) | `riemann_hypothesis_conditional`, `riemann_hypothesis_via_uop_maxmin`, `hilbert_polya_witness`, `hilbert_polya_implies_uop_gap`, `riemann_hypothesis_via_hilbert_polya`, `rh_full_equivalence` |
| `variational_gap` (`VariationalRoute.lean`) | `riemann_hypothesis_variational` |
| `orbit_collapse_axiom` (`GroupSymmetryRoute.lean`) | `riemann_hypothesis_group_symmetry` |
| `euler_forcing` (`MirrorPairing.lean`) | `riemann_hypothesis_mirror` |
| `master_gap` (`GapEquivalence.lean`) | `riemann_hypothesis_master` |

*Transitive note:* `hilbert_polya_witness` calls `uop_gap` directly
(`RiemannUOP.lean:573`); therefore `hilbert_polya_implies_uop_gap` and
`riemann_hypothesis_via_hilbert_polya` (which call it) are axiom-dependent even
though they never name `uop_gap`. By contrast `pla_implies_uop_gap` takes
`PLA_Condition` as an explicit *hypothesis* — which is why it lands in I.2, not
here.

## I.4 The open frontier (NOT proof steps)

- **Five equivalent bridge axioms** — `uop_gap` (equidistance, `RiemannUOP.lean`),
  `variational_gap`, `orbit_collapse_axiom`, `euler_forcing`, `master_gap`. Each
  asserts that ζ's non-trivial zeros satisfy a critical-line condition; `uop_gap`
  is self-labelled in source as *"THE SINGLE AXIOM — the RH itself."* They are
  proven mutually equivalent, so all five are the same gap = RH.
- **`bk_selfadjoint`, `bk_spectrum`** (`RiemannUOP.lean` §13) — the
  Berry–Keating / Hilbert–Pólya decomposition. **Honesty flag:** their stated
  bodies are currently *placeholders* (`True`, and a `t = t` tautology), not yet
  the real self-adjoint-operator / spectral-identification statements. No
  completed theorem in the file actually consumes them — they mark the intended
  decomposition, not realized content.
- **The one genuine RH `sorry`:** `euler_forcing_attempt` (`MirrorPairing.lean`)
  — the attempt to *prove* the `euler_forcing` bridge axiom from ζ's structure;
  still incomplete. This is the honest location of the real open work.

## I.5 How this is reusable toward RH

The clean substrate (I.1) + the clean reductions (I.2) mean: **a genuine analytic
proof that ζ-zeros minimize the zero-action (`PLA_Condition`), or that every zero
has the form `1/2 + it` (the BK spectral form), plugs straight in** — via
`pla_implies_uop_gap` / `rh_three_gap_formulations` / `rh_from_bk_spectral_form`
— to yield RH with no further geometry to redo. The single missing input is
sharply localized: replace the placeholder `bk_spectrum` with the real Connes /
Selberg spectral identification (and discharge `bk_selfadjoint`), **or** prove
`PLA_Condition` / discharge `euler_forcing_attempt` analytically. The formal
"last mile" after that point is already machine-checked.

---

# PART II — Navier–Stokes (3D global regularity)

**What is genuinely established.** A small set of clean elementary facts plus a
**toy** scalar-ODE energy-decay result proven end-to-end over real Mathlib reals
with **no `sorry` and no axiom** — demonstrating the pipeline produces real
proofs — together with an honest conditional scaffold that exposes its own
axiom/`sorry` dependence via `#print axioms`. The actual 3D regularity statement
remains a pure axiom.

## II.1 Closed-clean results (no `sorry`, no axiom)

### Toy energy decay — `lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean`
Verified over `ℝ` (`AxiomsCheck.lean` confirms **no** `sorryAx`):

| Theorem | Statement (verbatim) | Establishes |
|---|---|---|
| `energy_nonneg` | `(u₀ c t : ℝ) : 0 ≤ Energy u₀ c t` | toy energy `u₀²·exp(−ct)` is non-negative |
| `energy_at_zero` | `(u₀ c : ℝ) : Energy u₀ c 0 = u₀^2` | initial energy normalization |
| `energy_monotone_decay` | `(u₀ c : ℝ) (hc : 0 ≤ c)(t : ℝ)(ht : 0 ≤ t) : Energy u₀ c t ≤ Energy u₀ c 0` | toy analogue of the Leray energy inequality, **proven** |

This is explicitly a 1D linear damped scalar ODE — **not** the Millennium
problem — but a genuine closed result in the exact Mathlib pipeline used by the
NS scaffold.

### Elementary positivity / monotonicity — `lean4/NavierStokes.lean`
`viscosity_pos`, `reynoldsNumber_pos`, `larger_viscosity_lower_Re`,
`high_viscosity_MR_dominated`, `kolmogorovScale_pos`,
`smoothnessVern_eq_globallyRegular`, `larger_viscosity_tighter_ceiling`,
`viscosity_improves_kolmogorov`, `ns_smoothness_vern_theorem`,
`ns_euler_forcing_gap_is_millennium_problem` — viscosity / Reynolds number /
Kolmogorov scale are positive and well-defined; monotonicity in ν; and the gap is
*named* as the Millennium problem.

## II.2 Honest conditional scaffold (the disciplined frontier)

`lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean : UOP_implies_NS_smoothness`
— a **conditional** theorem over genuine Mathlib reals
(`(u₀)(ν : ℝ)(hν : 0 < ν) : ∃ u, IsSmoothNSSolution u u₀ ν`). It still contains
`sorry` (the Step-2/Step-3 chain) and draws its witness from
`axiom UOP_existence_claim`. The companion `AxiomsCheck.lean` runs `#print axioms`
precisely to **expose** that this result depends on `sorryAx` +
`UOP_existence_claim` — the correct epistemic hygiene (it does not pretend to be
closed).

## II.3 Real literature theorems encoded as axioms (NOT reproven here)

These are **true** PDE-literature results, stated as axioms so the scaffold can
reason from them — usable as scaffold hypotheses, but the corpus did **not**
prove them: `leray_energy_inequality` (Leray 1934), `ns_2d_global_regularity`
(2D regularity), `serrin_regularity`, `serrin_L3_endpoint` (Serrin /
Escauriaza–Seregin–Šverák endpoint), `ckn_partial_regularity`
(Caffarelli–Kohn–Nirenberg), plus structural/opaque quantities
(`nsEnergy`, `nsEnstrophy`, `integratedEnstrophy`, `singularHausdorffMeasure` and
their non-negativity). Every NavierStokes.lean theorem that *applies* one of these
is **VIA-AXIOM** (e.g. `leray_energy_bounded`, `ns_2d_smoothness_vern`,
`serrin_critical_case`, `ckn_regular_set_full`, `leray_serrin_bridge`,
`ckn_generic_regularity`, `two_d_always_regular_three_d_open`,
`ns_dichotomy_corollary`) — complete *given* the imported axiom, no new content.

## II.4 The open frontier (NOT proof steps)

- **`axiom ns_global_regularity`** — asserts 3D smooth solutions exist for all
  time. This **is the prize**; `ns_euler_forcing_gap_is_millennium_problem` names
  it as such.
- **`axiom ns_blowup`, `axiom ns_dichotomy`, `axiom blowup_not_regular`** — the
  alternative branch and dichotomy, asserted not derived.
- **The one genuine NS `sorry`:** the `sorry` inside `UOP_implies_NS_smoothness`
  (II.2). `NavierStokes.lean` itself contains **no** `sorry` — its non-elementary
  results are all VIA-AXIOM, not incomplete.

## II.5 How this is reusable toward Navier–Stokes

The reusable asset is **process plus a closed toy result, not a partial closure
of the prize**: a Mathlib-backed harness (`ToyDecay` proves the pipeline yields
genuine `sorry`-free analysis over `ℝ`) plus an `AxiomsCheck`/`#print axioms`
discipline that mechanically flags any hidden `sorry`/axiom. The honest next
milestone is sharply named — discharge the single `sorry` in
`UOP_implies_NS_smoothness` (the Step-2/Step-3 chain) and upgrade the literature
axioms (`leray_energy_inequality`, Serrin, CKN) to proven Mathlib theorems as the
library matures — at which point the conditional becomes a real *conditional*
theorem (still gated on `UOP_existence_claim`, the genuine analytic gap).

---

# PART III — Honest scope statement

1. **Nothing here proves RH or Navier–Stokes.** Each routes through a single,
   explicitly-named bridge axiom (`uop_gap` + its four equivalents for RH;
   `ns_global_regularity` / `UOP_existence_claim` for NS) that is logically
   equivalent to (or asserts) the conclusion.
2. **The genuine, reusable work is real and localized:** (RH) the complete
   axiom-free geometry of the critical line under multiple proven-equivalent
   characterizations + clean conditional reductions of RH to a named variational
   / spectral condition; (NS) a closed toy energy-decay theorem over Mathlib
   reals + the `#print axioms` honesty harness + elementary positivity facts.
3. **`sorry`-free ≠ proved.** Most capstones are `sorry`-free only because they
   consume a bridge axiom equal to the conclusion; the entire stack contains just
   **two** genuine `sorry` stubs (`euler_forcing_attempt`,
   `UOP_implies_NS_smoothness`), which honestly mark where the real derivations
   are missing.
4. **The frontier is named, not hidden:** RH needs the real (non-placeholder)
   `bk_spectrum` operator/spectrum or an analytic proof of `PLA_Condition` /
   `euler_forcing`; NS needs the `UOP_existence_claim` discharge plus upgrading
   the literature axioms to theorems.
5. Consistent with the working note's spine: the UOP supplies conviction and a
   blueprint but **does not shortcut** RH/NS — solving them removes the asserted
   bridge axioms rather than routing through them.

*Companion: the full corpus-wide sweep is*
`papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md` *(Appendix A); this ledger
is the RH/NS-focused, reusable-step view of the same reality.*
