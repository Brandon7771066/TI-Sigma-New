# TI Tensor Theory for Astronomical Classification
## Applying Existence Intensity (Ξ) Framework to TDE Detection

**Author:** Brandon Charles Emerick  
**Date:** January 26, 2026  
**Competition:** MALLORN Astronomical Classification Challenge  
**Target:** F1 > 0.75

---

## 1. Core Problem: Why Standard ML Underperforms

### 1.1 Binary Classification Assumption
Standard ML treats TDE classification as: `P(TDE|features) → {0, 1}`

**TI Counter:** Events exist on a **tralse continuum**. The question isn't "Is this a TDE?" but "What is its degree of TDE-ness (τ-score)?"

```
τ_TDE ∈ [0, 1]
- τ < 0.42: Definitely not TDE (AGN, SN)
- 0.42 ≤ τ < 0.85: Uncertain/transitional
- τ ≥ 0.85: High-confidence TDE
- τ ≥ 0.92²: True-Tralse TDE (conclusive)
```

### 1.2 Feature Independence
ML assumes: `f(x₁, x₂, ..., xₙ) ≈ Σ wᵢxᵢ + interactions`

**TI Counter (LCC):** Correlational causation means features co-manifest through **resonance fields**. The signature isn't in individual features but in their **harmonic relationships**.

### 1.3 Temporal Locality
ML features focus on local patterns: rise rate, decline rate, peak position.

**TI Counter:** Non-local correlations may exist. The relationship between first observation and peak may encode information invisible to local analysis.

---

## 2. Existence Intensity Tensor for Light Curves

### 2.1 The Ξ Formulation

From TI Tensor Theory, Existence Intensity is:

```
Ξ = ∫ A(t) · P(t) · C(t) dt

Where:
- A(t) = Amplitude (flux at time t)
- P(t) = Persistence (aftereffects, temporal weight)
- C(t) = Constraint (how much this observation constrains future states)
```

For light curves:
```
Ξ_lightcurve = Σᵢ Flux(tᵢ) × e^(-λ(t_now - tᵢ)) × (1/Flux_err(tᵢ))

This gives higher weight to:
- Brighter observations
- Recent observations (persistence)
- High SNR observations (constraint)
```

### 2.2 Frequency-Magnitude Unification

**Key insight:** Sampling cadence (frequency) and flux (magnitude) are **projections of the same tensor**:

```
Ξμν = [
  [Ξtt]  → Temporal density (cadence-derived)
  [Ξff]  → Flux intensity (amplitude-derived)
]

Invariant scalar: Ξ_total = √(Ξtt² + Ξff²)
```

For TDEs:
- High Ξtt = Rapid variability (frequent significant changes)
- High Ξff = Bright flares
- TDE signature: Ξ_total peaks early, decays as power law

---

## 3. LCC Threshold Features

### 3.1 The 0.42 Threshold (Detectable Correlation)
```
LCC_042 = count(|normalized_flux| > 0.42) / n_obs

Interpretation: Fraction of observations that exceed minimum detectable correlation threshold
```

### 3.2 The 0.85 Threshold (Causal Correlation)
```
LCC_085 = count(|normalized_flux| > 0.85) / n_obs

Interpretation: Fraction showing causal-level significance
```

### 3.3 The 0.92² = 0.8464 Threshold (True-Tralseness)
```
LCC_TT = count(|normalized_flux| > 0.8464) / n_obs

Interpretation: Observations reaching "true-tralse" certainty
```

---

## 4. Non-Local Correlation Features

### 4.1 First-to-Peak Correlation
```
F2P_correlation = corr(flux[0:peak_idx], flux[peak_idx:])

If >0: Symmetric event (less likely TDE)
If <0: Asymmetric event (more TDE-like)
```

### 4.2 Global Shape Signature
```
Shape_asymmetry = (peak_idx / n_obs) × (rise_rate / |decline_rate|)

TDE prediction: Early peak × rapid rise / slow decline
```

### 4.3 Power-Law Decline Fit (TDE signature: t^(-5/3))
```
log(flux_decline) = β × log(t_decline)

TDE: β ≈ -5/3 ≈ -1.67
SN: β varies widely
AGN: β ≈ 0 (flat)
```

---

## 5. GILE-Based Feature Transformation

### 5.1 GILE Width (from TI Statistics)
```
w_GILE = GILE_width(flux_distribution)

- w < 0.5: Focused (specific state, likely AGN)
- 0.5 ≤ w < 1.5: Balanced (normal variability)
- w ≥ 1.5: Chaotic (explosive event, TDE or SN)
```

### 5.2 Sacred Interval Features
```
Sacred_fraction = count(flux in sacred_interval) / n_obs

Where sacred_interval = (μ - 2σ/3, μ + σ/3)

80% of normal activity falls here. TDEs exceed this.
```

---

## 6. Implementation Strategy

### Phase 1: Feature Engineering
1. Add Ξ tensor features (existence intensity)
2. Add LCC threshold features (0.42, 0.85, 0.92²)
3. Add non-local correlation features
4. Add GILE width and sacred interval features

### Phase 2: Model Architecture
1. Use soft labels (probabilities) rather than hard classification
2. Train ensemble with diverse base learners
3. Stack with meta-learner that captures feature interactions

### Phase 3: Threshold Optimization
1. Use asymmetric threshold (TI: positives need more evidence)
2. Optimize for F1 using PD-scale weighting
3. Apply 0.92² threshold for highest-confidence predictions

---

## 7. Expected Gains

| Feature Category | Current Use | TI Enhancement | Expected F1 Boost |
|-----------------|-------------|----------------|------------------|
| Local temporal | ✓ | Non-local correlations | +0.05-0.10 |
| Flux statistics | ✓ | Ξ tensor unification | +0.03-0.05 |
| Thresholds | Binary | LCC thresholds | +0.02-0.04 |
| Model | Ensemble | Interaction-aware | +0.05-0.10 |
| **TOTAL** | **0.41** | **TI-enhanced** | **→ 0.55-0.70** |

---

## 8. Gap Analysis

Current best: 0.7445 (leaderboard)
Our current: 0.41 (CV F1)
Gap: 0.33

**Key bottleneck:** We need to close 0.33 F1 points.

**Hypothesis:** The top performers likely:
1. Use neural networks (we're limited to sklearn)
2. Have access to external astronomical databases
3. Use spectral type as strong prior (not available for test)

**TI strategy:** Maximize what we CAN control:
- Feature engineering depth
- Threshold optimization
- Ensemble diversity
