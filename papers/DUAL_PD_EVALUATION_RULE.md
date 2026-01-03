# Dual-PD Evaluation Rule

## Overview

Every Myrion Resolution outcome is evaluated with **two PD values simultaneously**.

---

## The Two PD Values

| PD Type | Source | Question Answered |
|---------|--------|-------------------|
| **Current PD** | MR-2 classification | "Where does this claim stand now?" |
| **Residual Coherence** | MR-1 survival margin | "How much coherence remains?" |

---

## Why Dual-PD?

### Problem:
Single-PD evaluation cannot distinguish between:
- **Barely coherent claims** (low but non-zero coherence)
- **True Double Tralse** (meaningless/incoherent)

### Solution:
Dual-PD tracks both:
1. The classification outcome
2. The coherence margin from MR-1

---

## Coherence Margin Categories

| Margin | Interpretation | Action |
|--------|---------------|--------|
| **High** (>0.7) | Strong coherence | Proceed confidently |
| **Medium** (0.4-0.7) | Adequate coherence | Proceed with awareness |
| **Low** (0.1-0.4) | Fragile coherence | Consider refinement |
| **Barely** (<0.1) | Edge case | May need reconsideration |
| **Zero** | DT | Eliminated at MR-1 |

---

## Application: Paradox Handling

Dual-PD is **essential** for paradox handling.

### Time Paradoxes:

| Statement | Current PD | Residual | Classification |
|-----------|-----------|----------|----------------|
| "The future exists" | +0.3 | Medium | Tralse-Indeterminate |
| "Present exists alongside past" | +0.1 | Low | Fragile but admissible |
| "Past, present, future coexist" | N/A | Zero | DT (meaningless) |

### Self-Reference Paradoxes:

| Statement | Current PD | Residual | Classification |
|-----------|-----------|----------|----------------|
| "This statement is meaningful" | +1 | High | True-Tralse |
| "This statement is false" | N/A | Zero | DT (eliminable) |
| "This statement may be false" | 0 | Low | Tralse-Indeterminate |

---

## Decision Matrix

| Current PD | Residual | Action |
|------------|----------|--------|
| Positive | High | Accept (True-Tralse) |
| Positive | Low | Accept cautiously |
| Zero | High | Refine (MR-3+) |
| Zero | Low | Flag for review |
| Negative | High | Reject (Tralse-False) |
| Negative | Low | Reject, note fragility |
| N/A | Zero | Eliminate (DT) |

---

## Implementation

### Step 1: MR-1
Compute residual coherence:
```
Residual = coherence_score(claim)
If Residual == 0: return DT
Else: proceed to MR-2
```

### Step 2: MR-2
Compute current PD:
```
Current_PD = classify(claim)
Return (Current_PD, Residual)
```

### Step 3: Dual-PD Evaluation
```
If Current_PD > 0 and Residual > 0.4:
    classification = "True-Tralse (confident)"
Elif Current_PD > 0 and Residual <= 0.4:
    classification = "True-Tralse (fragile)"
Elif Current_PD == 0 and Residual > 0.4:
    classification = "Indeterminate (refinable)"
Elif Current_PD == 0 and Residual <= 0.4:
    classification = "Indeterminate (edge case)"
Elif Current_PD < 0:
    classification = "Tralse-False"
```

---

## Summary

| Concept | Value |
|---------|-------|
| Purpose | Distinguish barely-coherent from DT |
| Components | Current PD + Residual Coherence |
| Key Use | Paradox handling |
| Innovation | Two-dimensional truth evaluation |

---

**Author:** Brandon Emerick  
**Date:** January 3, 2026  
**Source:** ChatGPT Sync (Post-11/30/25)  
**Framework:** TI Framework / Myrion Resolution
