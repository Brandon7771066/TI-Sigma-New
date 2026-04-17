# URB #709 — Coupled Knotted-Light + Dirac-Fermion Experimental Proposal: Direct BOK Realization in the Lab

**Author:** Brandon Charles Emerick
**Date:** April 17, 2026
**Series:** Unified Research Brief #709
**Status:** Concrete experimental proposal; deliverable to optics + AMO labs (Irvine group, structured-light groups)
**Builds on:** URB #573, URB #699, URB #701, URB #707

---

## 1. The Proposal in One Sentence

> **Shoot a Hopfion-knotted laser beam at a Bose-Einstein condensate of fermionic atoms, and look for chirality-locking between the optical knot's topology and the BEC's internal-state spinor structure.**

If the BOK is real, the optical knot's linking number should couple to the fermion's spin/chirality with a measurable, framework-predictable signature.

---

## 2. The Physics Setup

### 2.1 Light source: Hopfion-knotted laser
A laser beam in a Hopfion configuration, as produced by Kedia/Irvine/Bialynicki-Birula 2013 (PRL 111:150404). Key parameters:
- Linking number L = +1 (or −1 for the opposite chirality Hopfion)
- Wavelength λ = 800 nm (Ti:Sapphire) or 1064 nm (Nd:YAG)
- Beam waist w₀ ~ 50 μm (smaller than the BEC)
- Pulse duration: long enough for adiabatic interaction (~ms or CW)

### 2.2 Target: fermionic BEC (or degenerate Fermi gas)
- ⁶Li or ⁴⁰K atoms in a magnetic trap, cooled below T_F
- Number ~10⁵-10⁶ atoms
- Two-component spinor state (two hyperfine levels), playing the role of the Dirac spinor's two-Weyl-component substructure
- Trap geometry: cylindrical, with axis aligned to laser propagation direction

### 2.3 Coupling mechanism
The Hopfion's knotted electromagnetic field carries **orbital angular momentum (OAM)** — already routinely transferred to BECs in OAM-light experiments. The framework's prediction goes further: the knot's **topological linking number** should couple to the BEC's **chirality state** (relative phase between the two spinor components) in a way that goes beyond ordinary OAM transfer.

---

## 3. The Framework Prediction

In standard OAM-light + BEC experiments, the angular momentum transferred is determined by ℓ (the topological charge of the OAM beam), and there's no chirality-locking — left-circularly-polarized light with ℓ = +1 transfers angular momentum identically to right-circularly-polarized light with ℓ = +1.

**The BOK framework predicts** that for **Hopfion-knotted light** (which carries linking number L, not just OAM ℓ), there should be an **additional chirality-locking term**:

> P(spinor-flip) = P_OAM + **P_BOK · L · ⟨σ_z⟩**

where:
- P_OAM is the standard OAM-driven spinor coupling
- P_BOK is the BOK-mediated coupling coefficient (predicted to be of order 10⁻³ — α/(2π) scale, from URB #700)
- L is the optical knot's linking number
- ⟨σ_z⟩ is the BEC's average internal-state polarization

**This term is zero in conventional theory** (Maxwell + standard Dirac without BOK identification). **It is non-zero in the BOK framework** because the Maxwell knot's topology directly couples to the Dirac spinor's chirality through the BOK structure.

### 3.1 Expected signal
For a typical experiment:
- L = ±1 (Hopfion or anti-Hopfion)
- ⟨σ_z⟩ ≈ 0.1 (10% polarization, achievable)
- P_BOK ≈ 10⁻³ (framework prediction)

→ **Predicted spinor-flip excess** for L = +1 vs L = −1: **(10⁻³)(1)(0.1) = 10⁻⁴ relative excess**

This is **measurable** with standard BEC interferometry (which routinely achieves 10⁻⁵ precision). The signature is a **non-zero L-asymmetry in spinor-flip rate** that should reverse sign when the optical knot chirality reverses.

---

## 4. Experimental Procedure

1. **Prepare a fermionic BEC** in a known spinor state (say, ⟨σ_z⟩ = +0.1).
2. **Apply a Hopfion-knotted laser pulse** with linking number L = +1 for time τ.
3. **Measure the post-pulse spinor distribution** via Stern-Gerlach or absorption imaging.
4. **Repeat with L = −1** (anti-Hopfion) and same pulse parameters.
5. **Compare spinor-flip rates** between L = +1 and L = −1 experiments.
6. **Repeat for several values of ⟨σ_z⟩** (0, ±0.1, ±0.3, ±0.5).
7. **Plot spinor-flip excess vs ⟨σ_z⟩** for each L.

### 4.1 Predicted signature
The framework predicts a **linear dependence**: spinor-flip excess ∝ L · ⟨σ_z⟩, with slope P_BOK ≈ 10⁻³.

### 4.2 Null result interpretation
If the spinor-flip excess is consistent with zero across all (L, ⟨σ_z⟩) combinations to precision better than 10⁻⁴, the framework's BOK coupling prediction is **falsified at the order-of-magnitude level**. This would not refute URBs #573, #699, etc. (those have other empirical anchoring), but it would refute the specific quantitative claim that BOK coupling is at the α/(2π) scale.

---

## 5. Why This Experiment Matters

### 5.1 First direct BOK measurement
Existing experimental confirmations are **indirect**: URB #707 confirms Maxwell-knot existence; URB #699 confirms BOK 4+4 structure in a recovered equation. **No experiment to date has directly measured the predicted Maxwell-Dirac coupling that defines the full BOK.** This proposal is the first concrete test.

### 5.2 Bridge to GUT pathway
A confirmed BOK coupling would be the **first laboratory test of URB #701's Standard Model bridge claim**. If the coupling is at the predicted scale, the framework's GUT-pathway URBs (#702, #706) gain substantial empirical credibility. If the coupling is absent, the framework's GUT pathway needs reformulation.

### 5.3 Cheap relative to particle physics
This experiment uses **existing AMO laboratory infrastructure**. No new accelerator or detector required. Total estimated cost: **$200K-$500K** (pulse-shaping optics + standard BEC apparatus). Compare to the $10B+ scale of particle-physics BSM searches.

### 5.4 Fast turnaround
If executed by an existing optics+BEC group, results within **6-12 months** of approval. Compare to multi-year BSM searches.

---

## 6. Lab Recommendations

Groups with relevant capability:
1. **William Irvine group, U Chicago** — has Hopfion production capability
2. **Norman Yao group, UC Berkeley** — has fermionic BEC + OAM-light expertise
3. **Markus Greiner group, Harvard** — fermionic BEC microscopy
4. **MPQ Munich / Bloch group** — fermionic BEC + structured light
5. **JILA Boulder (Ye, Holland, Rey)** — degenerate Fermi gas + spinor physics

A collaboration between **a knotted-light group (Irvine-style)** and **a fermionic BEC group (Yao/Greiner/Bloch-style)** is the natural pairing.

---

## 7. Pre-Registration of Predictions

To preempt any "I always predicted that" charges, this URB pre-registers the framework's quantitative prediction:

- **Spinor-flip excess vs L · ⟨σ_z⟩ slope: P_BOK ≈ 10⁻³** (range 3 × 10⁻⁴ to 3 × 10⁻³ allowing for unknown geometric factors of order unity)
- **Sign**: positive for the conventional sign of the Hopfion linking number
- **Linearity**: linear in both L and ⟨σ_z⟩ in the small-coupling limit
- **Frequency dependence**: independent of laser wavelength to first order
- **Atom-species dependence**: same coupling for ⁶Li and ⁴⁰K (universal lepton-like chirality coupling)

---

## 8. Falsification Criteria

The framework's BOK coupling is **falsified** if:
- **F1**: Spinor-flip excess is consistent with zero to better than 3 × 10⁻⁴ slope precision, across multiple (L, ⟨σ_z⟩) settings.
- **F2**: Spinor-flip excess does not reverse sign when L reverses sign.
- **F3**: Spinor-flip excess depends on laser wavelength in a way inconsistent with the topological-coupling interpretation.

The framework's BOK coupling is **confirmed and sharpened** if:
- The slope is in the predicted range (3 × 10⁻⁴ to 3 × 10⁻³)
- The sign matches prediction
- The linearity holds within experimental error
- The signal is universal across atom species

---

## 9. The Slogan Form

> **"Shoot a knot of light at a knot of matter. Watch the chiralities lock. That's the BOK in the lab."**

---

## 10. Status & Position in URB Stack

This URB provides the **first concrete laboratory test** of the framework's Standard Model bridge. It is feasible with existing technology, costs orders of magnitude less than particle-physics BSM searches, and produces results on a 6-12 month timescale.

The proposal can be shared with the recommended labs in §6 immediately. Even a brief expression of interest from one such group would constitute substantial validation of the framework's seriousness as a physics-grounded research program.

URB #573 → URB #699 → URB #700 → URB #701 → URB #702 → URB #703 → URB #704 → URB #705 → URB #706 → URB #707 → URB #708 → **URB #709 (this brief — direct BOK measurement proposal)**.

---

*Brandon Charles Emerick, April 17, 2026 — first URB proposing a concrete laboratory experiment to directly test the BOK framework. The experiment uses existing technology, is cheap relative to particle physics, and produces sharp predictions. A null result refutes the specific quantitative claim about BOK coupling strength; a confirmation establishes the framework's first direct laboratory anchor.*
