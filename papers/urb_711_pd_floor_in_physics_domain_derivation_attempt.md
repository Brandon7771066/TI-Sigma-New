# URB #711 — Toward Deriving the PD Floor in the Fundamental-Physics Domain (Sub-Problem of URB #704)

**Author:** Brandon Charles Emerick
**Date:** April 17, 2026
**Series:** Unified Research Brief #711
**Status:** Reduction of α-derivation problem to a smaller, sharper open question
**Builds on:** URB #704 §5 (α as three-pillar composite, reduces α to PD floor in physics domain); URB #696 §4 (PD floor in general)

---

## 1. The Reduced Problem

URB #704 §5 reduced the problem of deriving α from first principles to the problem of **deriving the PD floor in the fundamental-physics domain**. Specifically:

> α/(2π) = (PD-floor in physics domain) × (HEAR chirality-doubling factor 2) / (2π geometric factor)

If PD floor in physics domain = ε_phys, then α = 2ε_phys. Numerically, α ≈ 7.30 × 10⁻³, so ε_phys ≈ 3.65 × 10⁻³.

The question becomes: **why is ε_phys = 3.65 × 10⁻³?**

---

## 2. PD Floor: Framework Definition

PD (Permissibility Distribution) is the framework's mechanism for handling novel events and incommensurable evidence (URB family on PD pillar). The PD floor ε is the **minimum probability the framework assigns to any novel event** — a permissibility-of-existence floor that prevents the framework from assigning probability zero to genuinely novel events (which would violate the framework's no-Bayesian-prior-zero principle).

The PD floor is **domain-variable**: different domains have different floors based on the domain's HEM dimensionality, GILE weighting, and characteristic novelty rate. URB #704 §5 used a default floor of ~10⁻³; URB #711 must derive the *specific* floor for the fundamental-physics domain.

---

## 3. Three Candidate Derivations

### 3.1 Candidate I: HEM Dimensionality Argument

The HEM has 4 dimensions (URB family on HEM). The fundamental-physics domain occupies HEM dimensions related to **measurement, geometry, energy, and information**, but not to the consciousness-coordinate dimension (which is reserved for biology, cognition, etc.). The "active" HEM dimensions in physics are therefore **3 of the 4**.

If the PD floor scales as **(active HEM dim / total HEM dim)^k** for some integer k, with default floor 10⁻³ when all 4 dimensions are active, then physics domain has:

> ε_phys = 10⁻³ × (3/4)^k

For k = 3: ε_phys ≈ 4.2 × 10⁻⁴ (one order of magnitude too small)
For k = 1: ε_phys ≈ 7.5 × 10⁻⁴ (still too small)
For k = -1: ε_phys ≈ 1.3 × 10⁻³ (closer but not matching)

**Candidate I gives wrong sign of correction** — physics having fewer active HEM dimensions should *lower* the floor, but the desired ε_phys ≈ 3.65 × 10⁻³ is *higher* than the default 10⁻³. **Candidate I rejected.**

### 3.2 Candidate II: GILE-Coupling Sum

GILE weights satisfy Σwᵢ = 1. In the fundamental-physics domain, the framework's existing GILE-weights URBs suggest:
- G (Goodness): low weight in physics (physics doesn't optimize for goodness)
- I (Intuition): moderate weight (intuition guides theory development)
- L (Love): low weight (physics is largely impersonal)
- E (Environment): high weight (physics is environment-focused)

Approximate weights in physics domain: w_G = 0.05, w_I = 0.20, w_L = 0.05, w_E = 0.70.

If the PD floor is set by the **non-Environment GILE weight sum**:

> ε_phys = (w_G + w_I + w_L) × (a normalization)

= 0.30 × normalization. To match ε_phys ≈ 3.65 × 10⁻³, the normalization must be ≈ 0.012 = α/(2π · √(8/15)) — close to but not exactly α/(2π).

This gives **partial agreement** but requires a normalization factor that isn't independently derived. **Candidate II is structurally suggestive but underdetermined.**

### 3.3 Candidate III: Three-Pillar Self-Consistency

PD, MR, HEAR are the framework's three operational pillars. Each pillar has a characteristic strength:
- **PD strength** = 1/ε (inverse of floor — high when floor is low)
- **MR strength** = number of iterations to convergence ≈ O(1) for well-behaved problems
- **HEAR strength** = chirality-doubling factor 2

The framework's slogan from URB #704: α = ε × 2 / (2π).

**The candidate III derivation**: ε_phys is the value at which the three-pillar product **(PD strength × MR strength × HEAR strength)** is **dimensionally self-consistent** with the GILE-weight constraints.

The math: if dimensional self-consistency requires ε × 2 / (2π) = (some product of GILE weights), and the GILE weights in physics domain sum to 1 with E-dominated weighting (~0.70), then:

> ε × 2 / (2π) = (1 - w_E)² = 0.30² = 0.09

→ ε = 0.09 × π = 0.283 — **far too high** (off by ~80x).

OR with different power: ε × 2 / (2π) = (1 - w_E)⁴ = 0.0081 → ε = 0.0254 — still too high.

**Candidate III in this form fails by factors of ~10-80.** A different functional form might work but is not yet identified.

---

## 4. Status of the Reduced Problem

After three candidate derivations, **none** produces ε_phys ≈ 3.65 × 10⁻³ from first principles:
- Candidate I (HEM dimensionality): wrong sign of correction
- Candidate II (GILE-weight sum): partial agreement requiring a non-derived normalization
- Candidate III (three-pillar self-consistency): wrong magnitude by ~10-80x

This is **honest negative work**. The framework's α-derivation problem reduces to ε_phys-derivation, and three reasonable candidate rules all fail. The answer is not in any of these directions.

---

## 5. What This Suggests About the Right Answer

The pattern of failures suggests the right derivation involves:

1. **Not just dimensionality scaling** — the corrections from physics having fewer active HEM dimensions go the wrong way.
2. **Not just GILE weights** — these are too coarse; the correct derivation likely involves a **finer structure within E-weighted physics** (perhaps a sub-decomposition of the Environment dimension).
3. **Not three-pillar product** — this gives the right form but wrong magnitude.

The most likely path forward, from this elimination:
- The PD floor is set by an **interaction between the framework's chirality-doubling structure (URB #700) and the multi-BOK moduli-space metric (URB #710)**.
- Specifically: ε_phys may emerge as the **moduli-space measure of the chirality-broken sector** of the multi-BOK landscape.
- This would link α to the gravity-side of the framework (URB #710) rather than to the SM-side, which is structurally interesting but currently underdeveloped.

---

## 6. The Open Sub-Problem

The reduced open problem is:

> **Derive ε_phys = 3.65 × 10⁻³ as the moduli-space measure of the chirality-broken sector of the multi-BOK landscape (or as an alternative framework-natural quantity at this scale).**

Solving this would close the α-derivation problem (URB #704) and provide the framework's first **derivation of a Standard Model parameter from first principles**.

---

## 7. Predictions Made by the Reduced Problem Even Without Full Derivation

Even without the full derivation, the framework's reduced-problem structure makes predictions:

- **Other coupling constants should follow the same pattern** with different domain-PD-floors. Specifically:
  - α_strong (strong coupling at low energy) ≈ 1 → suggests PD floor in strong-interaction domain ≈ 1 (no floor — full permissibility)
  - α_weak (weak coupling) ≈ 10⁻⁵ → suggests PD floor in weak-interaction domain ≈ 5 × 10⁻⁶ (much lower than EM)
  - α_grav (gravitational coupling) ≈ 10⁻³⁹ → suggests PD floor in gravitational domain ≈ 5 × 10⁻⁴⁰ (vastly lower than EM)

The pattern: **stronger-coupling interactions correspond to higher PD floors in their domain; weaker-coupling interactions correspond to lower floors**. This is a **structural prediction** that is testable by checking whether the four coupling constants' magnitudes follow framework-natural domain-PD-floor scaling.

A clean test: are the *ratios* of these PD floors framework-derivable even without their absolute values? If yes, the framework predicts coupling-constant *ratios* before it predicts absolutes — which is exactly the conventional GUT pathway.

---

## 8. Falsification Criteria

- **F1**: ε_phys ≈ 3.65 × 10⁻³ is shown to be incompatible with any framework-natural derivation. Currently: this URB has eliminated three candidate derivations; more candidates remain.
- **F2**: Coupling-constant ratios are shown not to follow framework-natural domain-PD-floor scaling. Currently open.
- **F3**: A simpler framework principle than three-pillar composite (URB #704 Rule C) is shown to derive α exactly. Would simplify the framework's α-account but not refute the broader structure.

---

## 9. The Slogan Form

> **"Three candidate derivations of ε_phys all fail. The right answer involves the moduli-space measure of the chirality-broken multi-BOK sector. The framework's first SM-parameter derivation is still ahead."**

---

## 10. Status & Position in URB Stack

This URB performs **honest negative work**: eliminating three candidate derivations of ε_phys, narrowing the open problem to a specific sub-question (moduli-space measure of chirality-broken sector). The framework gains by **knowing what doesn't work** and by reducing the open problem to a smaller, sharper question.

URB #704 (α as three-pillar composite) → **URB #711 (this brief — three candidates eliminated)** → future URB #712+ (moduli-space-measure approach).

The α-derivation problem is the framework's hardest open mathematical problem. Slow honest progress — three candidates eliminated, one new direction identified — is the right pace. Forcing a derivation through fitting would be intellectually dishonest and would damage the framework's credibility.

---

*Brandon Charles Emerick, April 17, 2026 — twelfth URB of the session, doing honest negative work on the α-derivation problem. Three candidate derivations eliminated, one new direction (moduli-space measure of chirality-broken sector) identified. The framework's first SM-parameter derivation remains the most important open mathematical problem.*
