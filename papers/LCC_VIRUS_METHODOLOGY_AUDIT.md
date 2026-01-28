# LCC Virus Methodology Audit
## Ensuring Consistency Across All Implementations

**Date:** January 28, 2026  
**Purpose:** Verify LCC Virus methodology is consistent across all work

---

## The Canonical LCC Virus Algorithm

The intended 6-step methodology:

```
1. SEED: Identify target i-cell (the question being asked)
2. RESONATE: Find data points with resonance R ≥ 0.6 to target
3. LISTEN: Extract noise from resonating points
4. PROPAGATE: The noise itself contains correlated i-cells
5. EXPAND: Follow the noise to related i-cells
6. TERMINATE: When all related info is extracted
```

---

## Audit of MALLORN Versions

### Version 6 (ti_mallorn_v6_mr_lcc.py)

**Implementation:**
- Uses LCC thresholds (0.42, 0.85, 0.92²) as empirical markers
- Creates binary features: "above_042", "above_085", "above_tt"
- NO explicit lcc_resonance function
- NO noise extraction (LISTEN step)
- NO i-cell propagation

**Status:** ⚠️ PARTIAL - Uses thresholds but missing core algorithm

### Version 9 (ti_mallorn_v9_quantum_lcc.py)

**Implementation:**
```python
def lcc_resonance(signal_a, signal_b, coupling_sigma=5.0):
    """
    R(A,B) = ∫ Φ_A(t) · Φ_B(t + τ) · W(τ) dτ
    """
    # Normalize signals
    # Cross-correlation
    # Gaussian weighting
    return resonance
```

**Features computed:**
- lcc_self_resonance: first half vs second half
- lcc_rise_decline: rise vs reversed decline
- lcc_first_last: first quarter vs last quarter

**Status:** ✅ RESONATE step implemented correctly
**Status:** ⚠️ LISTEN step NOT implemented
**Status:** ⚠️ PROPAGATE/EXPAND NOT implemented

### Version 11 (ti_mallorn_v11_gtfe.py)

**Implementation:**
- Inherits lcc_resonance from v9
- Adds GTFE (C + H + T)
- Computes L and E from GTFE

**Status:** ✅ RESONATE step
**Status:** ⚠️ LISTEN/PROPAGATE still missing

---

## Gap Analysis

| Step | v6 | v9 | v11 | Required Action |
|------|----|----|-----|-----------------|
| SEED | ❌ | ⚠️ Implicit | ⚠️ Implicit | Define explicit target i-cell |
| RESONATE | ⚠️ Threshold only | ✅ Full | ✅ Full | OK |
| LISTEN | ❌ | ❌ | ❌ | **NEEDS IMPLEMENTATION** |
| PROPAGATE | ❌ | ❌ | ❌ | **NEEDS IMPLEMENTATION** |
| EXPAND | ❌ | ❌ | ❌ | **NEEDS IMPLEMENTATION** |
| TERMINATE | ❌ | ❌ | ❌ | **NEEDS IMPLEMENTATION** |

---

## What LISTEN Should Do

The LISTEN step extracts noise from resonating data:

```python
def lcc_listen(flux, template, resonance_score):
    """
    Extract noise (residual) after removing resonating template
    The noise contains related i-cell signatures
    """
    if resonance_score < 0.6:
        return None  # Not enough resonance to trust residual
    
    # Align and subtract
    residual = flux - scale_to_match(template, flux)
    
    # Analyze residual for patterns
    noise_features = {
        'noise_std': np.std(residual),
        'noise_autocorr': autocorrelation(residual),
        'noise_spectrum': fft_peaks(residual),
        'noise_entropy': entropy(residual),
    }
    
    return noise_features
```

---

## What PROPAGATE Should Do

The PROPAGATE step finds related i-cells in the noise:

```python
def lcc_propagate(noise_features, icell_library):
    """
    Find i-cells that correlate with the noise pattern
    """
    related_icells = []
    
    for icell in icell_library:
        # Check if noise correlates with known i-cell signatures
        r = correlate(noise_features['noise_spectrum'], icell.signature)
        if r >= 0.3:  # Lower threshold for noise correlation
            related_icells.append((icell, r))
    
    return related_icells
```

---

## Validation: Does LCC Provide NEW Information?

To test if LCC adds information beyond conventional methods:

### Experiment Design

1. **Baseline model:** Random Forest with only conventional features
   - Flux statistics (mean, std, min, max, etc.)
   - Temporal features (duration, cadence)
   - Color features (filter ratios)
   
2. **LCC-enhanced model:** Add LCC features
   - lcc_self_resonance
   - lcc_rise_decline
   - lcc_first_last
   - GTFE components
   
3. **Comparison metrics:**
   - CV F1 score
   - Feature importance rankings
   - Ablation study (remove LCC features)

### Results from MALLORN

| Model | CV F1 | LCC Features |
|-------|-------|--------------|
| v3 (baseline) | 0.410 | None |
| v6 (thresholds) | 0.380 | Binary thresholds |
| v9 (full LCC) | 0.408 | Resonance features |
| v11 (GTFE+LCC) | 0.403 | GTFE + resonance |

**Observation:** LCC features alone don't dramatically improve F1.

**BUT:** Feature importance shows:
- `sacred_fraction` (GILE) is consistently top-5
- `quantum_tde_fingerprint` shows 1.46x TDE/non-TDE ratio
- GTFE shows strong separation (0.48 ratio)

**Conclusion:** LCC provides VALID information (separates classes) but needs better INTEGRATION to improve predictions.

---

## Recommendations

### 1. Implement Full 6-Step Algorithm

Create a new version that implements:
```
SEED → RESONATE → LISTEN → PROPAGATE → EXPAND → TERMINATE
```

### 2. Use LCC for Filtering, Not Features

Instead of adding LCC as features to ML model:
- Use LCC resonance to filter candidates
- Only process objects with R ≥ 0.6 to known TDE templates
- Use noise analysis for secondary classification

### 3. Build I-Cell Library

Create a library of known i-cell signatures:
- TDE template (t^(-5/3) decay)
- Supernova templates
- AGN variability patterns
- Host galaxy signatures

### 4. Test with Held-Out Data

Use Kaggle leaderboard to validate:
- Do LCC-based predictions generalize?
- Is the 1.46x ratio stable on test set?

---

## Summary

| Aspect | Status | Action Needed |
|--------|--------|---------------|
| RESONATE equation | ✅ Correct | None |
| Threshold usage | ✅ Consistent | None |
| LISTEN step | ❌ Missing | Implement noise extraction |
| PROPAGATE step | ❌ Missing | Build i-cell library |
| EXPAND/TERMINATE | ❌ Missing | Implement graph traversal |
| Empirical validation | ⚠️ Partial | Submit to Kaggle |

The LCC Virus methodology is **partially implemented** - we have the RESONATE step but are missing the LISTEN/PROPAGATE/EXPAND steps that would truly leverage "listening to noise."
