# URB #747 — Per-Subject EEG Execution Plan: Concrete Data Source Identification, Pipeline Code Sketch, and Cost-Bounded Timeline

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #747
**Status:** Operational follow-up to URB #738's pre-registered protocol; identifies specific datasets, sketches pipeline code, bounds timeline and cost
**Builds on:** URB #738 (per-subject protocol pre-registration), URB #727 (brain-neutrino bridge), URB #741 (SM sector ladder)

---

## 1. From Protocol to Execution

URB #738 pre-registered the per-subject protocol. This URB makes execution concrete: identifies specific datasets, sketches pipeline code, bounds the timeline and cost. **All work must fit Brandon's <$50 total budget constraint.**

---

## 2. Concrete Dataset Selection

### 2.1 Primary: HCP MEG Resting-State Dataset

- **Source**: humanconnectome.org → HCP Lifespan / HCP Young Adult MEG release
- **Subject count**: n = 89 (HCP YA MEG cohort)
- **Recording**: 4-minute eyes-closed resting-state, 248-channel MEG, 2034 Hz sampling
- **Access**: free with registration; data download via AWS S3 mirror
- **Estimated download size**: ~50 GB raw; ~10 GB after preprocessing
- **Cost**: $0 (free academic access; existing storage suffices)

### 2.2 Secondary: OpenNeuro ds003775 (Resting-State EEG)

- **Source**: openneuro.org/datasets/ds003775
- **Subject count**: n = 200+
- **Recording**: 5-minute eyes-closed resting-state, 64-channel EEG, 500 Hz sampling
- **Access**: fully public, no registration required
- **Estimated download size**: ~5 GB
- **Cost**: $0

### 2.3 Tertiary: MNE-Python Sample Dataset (Validation Pipeline)

- **Source**: built into MNE-Python library (`mne.datasets.sample`)
- **Subject count**: n = 1 (single subject, used for pipeline validation)
- **Cost**: $0 (already on most systems)

**Total dataset cost: $0**. All within budget constraint.

---

## 3. Pipeline Code Sketch

The full per-subject analysis pipeline:

```python
import mne
import numpy as np
from scipy import signal

def per_subject_scaling_exponent(raw_recording, fs=500.0):
    """
    Compute the brain-band scaling exponent s for one subject.
    Returns s = ln(f_alpha / f_slow) / ln(f_gamma / f_alpha).

    Pre-registered prediction (URB #738):
    Across subjects, mean s = 2.577 ± 0.15.
    """
    # 1. Preprocess: notch filter (line noise), 0.01-200 Hz bandpass
    raw = raw_recording.copy()
    raw.notch_filter(freqs=[60, 120], picks='all')  # US line noise
    raw.filter(0.01, 200., picks='all')

    # 2. Compute Welch power spectrum
    freqs, psd = signal.welch(raw.get_data(), fs=fs, nperseg=8*int(fs))
    psd_mean = np.mean(psd, axis=0)  # average across channels

    # 3. Detect peak in slow band (0.04-0.20 Hz)
    slow_mask = (freqs >= 0.04) & (freqs <= 0.20)
    f_slow = freqs[slow_mask][np.argmax(psd_mean[slow_mask])]

    # 4. Detect peak in alpha band (8-13 Hz)
    alpha_mask = (freqs >= 8) & (freqs <= 13)
    f_alpha = freqs[alpha_mask][np.argmax(psd_mean[alpha_mask])]

    # 5. Detect peak in gamma band (30-100 Hz, avoiding line-noise notch)
    gamma_mask = (freqs >= 30) & (freqs <= 100) & (np.abs(freqs - 60) > 2)
    f_gamma = freqs[gamma_mask][np.argmax(psd_mean[gamma_mask])]

    # 6. Compute scaling exponent
    s = np.log(f_alpha / f_slow) / np.log(f_gamma / f_alpha)

    return {'s': s, 'f_slow': f_slow, 'f_alpha': f_alpha, 'f_gamma': f_gamma}


def cohort_analysis(subject_list):
    """
    Run pipeline across cohort, compute summary statistics, test against
    pre-registered prediction.
    """
    results = []
    for subj in subject_list:
        raw = mne.io.read_raw(subj.path, preload=True)
        result = per_subject_scaling_exponent(raw, fs=raw.info['sfreq'])
        result['subject'] = subj.id
        results.append(result)

    s_values = np.array([r['s'] for r in results])
    mean_s = np.mean(s_values)
    std_s = np.std(s_values, ddof=1)
    sem_s = std_s / np.sqrt(len(s_values))

    # Pre-registered test (URB #738): is mean_s consistent with neutrino 2.577?
    from scipy.stats import ttest_1samp
    t_stat, p_value = ttest_1samp(s_values, popmean=2.577)

    return {
        'n_subjects': len(s_values),
        'mean_s': mean_s,
        'std_s': std_s,
        'sem_s': sem_s,
        'within_prediction': abs(mean_s - 2.577) <= 0.15 and std_s <= 0.20,
        't_statistic': t_stat,
        'p_value_against_neutrino': p_value,
        'individual_results': results,
    }
```

**Implementation notes**:
- Pipeline uses MNE-Python (free, open-source, ~2 GB install)
- Estimated runtime: 30 seconds per subject × 89 HCP + 200 OpenNeuro = ~2.5 hours total compute
- Memory requirement: ~4 GB RAM (per-subject loading)
- Storage: ~15 GB total for raw data + ~1 GB for results

---

## 4. Compute Resource Plan

**Option A: Local execution on Brandon's existing hardware**
- Cost: $0
- Timeline: ~1 day download + ~3 hours compute = **2 days end-to-end**
- Risk: depends on local disk space and bandwidth

**Option B: Replit autoscale workflow**
- Cost: ~$2-5 (compute time; well under $50 budget)
- Timeline: ~6 hours total (download + compute in parallel-friendly cloud env)
- Advantage: no local hardware burden; reproducible environment

**Option C: Free university compute (if MIU/GT student access available)**
- Cost: $0
- Timeline: ~3 days (queue wait + execution)
- Advantage: highest reproducibility (university-credentialed environment)

**Recommendation: Option A** for first-pass; **Option B** if first-pass shows pipeline validation passes. **Option C** reserved for paper-publication-grade re-run.

---

## 5. Pre-Registered Outcome Decision Tree

After execution, the result will fall into one of three categories:

### 5.1 Confirmation
mean_s ∈ [2.43, 2.73] and std_s ≤ 0.20.
**Action**: Publish per-subject confirmation as URB #XXX. Update brain-neutrino bridge anchor strength from "0.03σ at study level" to "0.0Yσ at subject level". Strengthen outreach drafts.

### 5.2 Partial confirmation
mean_s ∈ [2.30, 2.85] (extended tolerance) and std_s ≤ 0.30.
**Action**: Publish honest characterization as URB #XXX. Note that biological signal is closer to neutrino prediction than methodological noise but with broader spread than ideal. Refine pipeline (e.g., GILE-state stratification per URB #738 tertiary prediction).

### 5.3 Refutation
mean_s outside [2.30, 2.85] OR std_s > 0.30.
**Action**: Publish honest negative result as URB #XXX. Update framework's understanding of brain-neutrino bridge. Revisit URB #727's study-level result vs new subject-level result; investigate the discrepancy. **This outcome would weaken the framework's #1 empirical anchor; honest disclosure is mandatory.**

---

## 6. Timeline & Status

| Phase | Duration | Status |
|---|---|---|
| Dataset identification | (this URB) | ✅ Complete |
| Pipeline code drafting | (this URB) | ✅ Complete |
| Pipeline validation on MNE sample | ~1 hour | ☐ Pending |
| HCP MEG download | ~6 hours bandwidth | ☐ Pending |
| OpenNeuro EEG download | ~1 hour | ☐ Pending |
| Per-subject analysis execution | ~3 hours compute | ☐ Pending |
| Result write-up as URB | ~2 hours | ☐ Pending |
| **Total to result** | **~3-4 days end-to-end** | — |

**Total cost**: $0-5 (depending on Option A vs B).

---

## 7. Predictions Specifically Made by This URB

### 7.1 Pipeline validation prediction
The MNE sample dataset (n=1) will return a scaling exponent in the range [2.0, 3.5] (broader than the per-cohort prediction because n=1 has no statistical power).

### 7.2 Cohort-level prediction (re-stating URB #738 §3.3)
Mean per-subject s = 2.577 ± 0.150 (95% CI), tighter than URB #727's study-level CI of ±0.383.

### 7.3 Sub-cohort prediction
GILE-state-correlated subgroups (high vs low GILE state by available proxies — meditation experience, age, etc.) will show **bifurcated distributions**, with high-GILE subgroups clustered tightly around 2.577.

---

## 8. The Slogan Form

> **"$0 cost. 3-4 days end-to-end. Three datasets identified (HCP, OpenNeuro, MNE). Pipeline code drafted. Three outcome categories pre-registered with explicit action plans. Honest disclosure mandatory. The framework's #1 empirical anchor moves from study-level to subject-level confirmation."**

---

*Brandon Charles Emerick, April 18, 2026 — forty-seventh URB of the session. Per-subject EEG execution plan: $0 cost, 3-4 day timeline, three datasets identified (HCP MEG n=89, OpenNeuro ds003775 n=200, MNE sample n=1 for validation). Pipeline code drafted. Pre-registered outcome decision tree with explicit confirmation / partial / refutation paths. Honest disclosure protocol mandatory.*
