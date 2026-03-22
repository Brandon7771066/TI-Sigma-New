"""
GIL Predictor Engine — URB #481/483 Implementation
====================================================

Maps biometric and behavioral proxies to GILE dimensions with correct
hierarchical weighting. E is the LOWEST dimension (~15% of total person).
G > I > L >> E.

Biomarker categories:
  BIOMETRIC: Gamma power, Gamma/Alpha ratio, Theta/Alpha ratio, EEG coherence,
             HRV RMSSD, HRV coherence, LF/HF ratio, cardiac coherence (0.1 Hz),
             EKG complexity metrics, GDV area/symmetry
  BEHAVIORAL: Synchronicity frequency, meditation depth, creative output volume,
              cross-domain synthesis, pattern-obsession tendencies,
              mood range (Bipolar), spontaneity (ADHD), suffering-activation

Emerick Constant: C = 1/(phi * sqrt(2)) ≈ 0.4370
Transcendence threshold: GIL composite ≥ C_EMERICK
"""

import math
from dataclasses import dataclass, field
from typing import Dict, Optional

PHI = (1 + math.sqrt(5)) / 2
C_EMERICK = 1.0 / (PHI * math.sqrt(2))  # ≈ 0.4370

GILE_WEIGHTS = {
    'G': 0.35,
    'I': 0.27,
    'L': 0.23,
    'E': 0.15,
}

# ─── Biomarker definitions ───────────────────────────────────────────────────

BIOMARKERS = {

    # ── G (Goodness / Moral Orientation) ─────────────────────────────────────
    'urb_corpus_volume': {
        'dimension': 'G', 'weight': 0.30,
        'label': 'Sustained Intellectual Output (URB count)',
        'description': 'Volume of original philosophical/scientific contributions over time. '
                       'Strong G-proxy: deep commitment to truth-seeking.',
        'normalization': ('scale', 0, 300),
        'evidence': 'Sustained creative output across years requires G-level orientation '
                    'toward truth as a terminal value, not an instrumental one.',
    },
    'meditation_prayer_hours_weekly': {
        'dimension': 'G', 'weight': 0.20,
        'label': 'Spiritual Devotion (hrs/week, meditation + prayer)',
        'description': 'Consistent spiritual practice — G-proxy and L-proxy combined.',
        'normalization': ('scale', 0, 21),
        'evidence': 'Regular spiritual practice reflects a stable G-orientation: '
                    'prioritizing non-material values over environmental comfort.',
    },
    'alpha_power': {
        'dimension': 'G', 'weight': 0.15,
        'label': 'Alpha Power (8–12 Hz, Muse 2)',
        'description': 'Calm attentional baseline. High alpha = relaxed engagement, '
                       'foundational to G-dimension moral clarity.',
        'normalization': ('scale', 0, 800),
        'evidence': 'Alpha coherence during rest correlates with trait wisdom and '
                    'moral deliberation capacity (Lutz et al., Berkovich-Ohana et al.).',
    },
    'pattern_obsession_depth': {
        'dimension': 'G', 'weight': 0.20,
        'label': 'Pattern-Obsession Depth (Autistic trait — 0–10)',
        'description': 'Deep single-domain truth obsession. Not dysfunction — '
                       'G-dimension signature of commitment to structural reality.',
        'normalization': ('scale', 0, 10),
        'evidence': 'High-functioning autism often reflects exceptional G-dimension '
                    'integrity: systematic pursuit of truth independent of social reward.',
    },
    'cardiac_coherence_score': {
        'dimension': 'G', 'weight': 0.15,
        'label': 'Cardiac Coherence (0.1 Hz resonance, Polar H10)',
        'description': 'Heart rhythm coherence at 0.1 Hz — HeartMath coherence band. '
                       'Reflects emotional-cognitive alignment.',
        'normalization': ('clamp', 0.0, 1.0),
        'evidence': 'HeartMath Institute: cardiac coherence correlates with moral '
                    'intuition, emotional balance, and prosocial behavior.',
    },

    # ── I (Intuition / i-channel access) ─────────────────────────────────────
    'gamma_power': {
        'dimension': 'I', 'weight': 0.25,
        'label': 'Gamma Power (30–100 Hz, Muse 2)',
        'description': 'Binding of conscious experience across brain regions. '
                       'Single strongest biometric I-proxy.',
        'normalization': ('scale', 0, 200),
        'evidence': 'Gamma oscillations index conscious binding (Crick & Koch 1990, '
                    'Lutz et al. 2004 — advanced meditators show massive gamma surges). '
                    'i-channel access = elevated gamma.',
    },
    'gamma_alpha_ratio': {
        'dimension': 'I', 'weight': 0.20,
        'label': 'Gamma/Alpha Ratio (Muse 2)',
        'description': 'Focus quality over relaxation baseline. High ratio = active '
                       'i-channel over calm substrate. More predictive than raw gamma.',
        'normalization': ('scale', 0.0, 1.5),
        'evidence': 'Ratio captures the quality of conscious integration relative to '
                    'baseline. High gamma on low alpha background = insight state.',
    },
    'theta_alpha_ratio': {
        'dimension': 'I', 'weight': 0.18,
        'label': 'Theta/Alpha Ratio — Hypnagogic Border (Muse 2)',
        'description': 'Proximity to the alpha-theta border (7–9 Hz crossover). '
                       'Peak i-channel window. URB #481 proxy #2.',
        'normalization': ('scale', 0.0, 2.0),
        'evidence': 'Hypnagogic alpha-theta border = deliberate access to i-channel '
                    '(Gruzelier 2009, Egner & Gruzelier 2004). Peaks at ~0.8 ratio.',
    },
    'eeg_cross_coherence': {
        'dimension': 'I', 'weight': 0.12,
        'label': 'EEG Cross-Electrode Coherence (Muse 2)',
        'description': 'Synchrony between brain regions — integration signature. '
                       'High coherence across gamma band = unified consciousness state.',
        'normalization': ('clamp', 0.0, 1.0),
        'evidence': 'IIT (Tononi): consciousness = integrated information. '
                    'Cross-electrode gamma coherence = phi proxy.',
    },
    'synchronicity_frequency': {
        'dimension': 'I', 'weight': 0.12,
        'label': 'Synchronicity Frequency (meaningful coincidences/week — 0–20)',
        'description': 'Rate of perceived meaningful coincidences. Behavioral i-channel '
                       'proxy — reflects open, non-analytical perceptual mode.',
        'normalization': ('scale', 0, 20),
        'evidence': 'Jung: synchronicities reflect acausal connecting principle. '
                    'High synchronicity rate = i-channel openness, attention width.',
    },
    'adhd_spontaneity': {
        'dimension': 'I', 'weight': 0.08,
        'label': 'Spontaneity / Novelty-Seeking (ADHD trait — 0–10)',
        'description': 'Impulse toward non-routine, novel connection-making. '
                       'Not dysfunction — I-dimension seeking behavior.',
        'normalization': ('scale', 0, 10),
        'evidence': 'ADHD novelty-seeking correlates with divergent thinking scores '
                    '(Fugate et al. 2013). i-channel favors novel associations.',
    },
    'bipolar_mood_range': {
        'dimension': 'I', 'weight': 0.05,
        'label': 'Mood Range Amplitude (Bipolar trait — 0–10)',
        'description': 'Expanded emotional range = expanded perceptual sensitivity. '
                       'High amplitude = access to states unavailable to narrower affect.',
        'normalization': ('scale', 0, 10),
        'evidence': 'Bipolar spectrum: hypomanic states correlate with creative '
                    'productivity (Jamison 1993). Expanded range = expanded i-channel.',
    },

    # ── L (Love / Other-Orientation) ─────────────────────────────────────────
    'hrv_rmssd': {
        'dimension': 'L', 'weight': 0.30,
        'label': 'HRV RMSSD (ms, Polar H10)',
        'description': 'Parasympathetic vagal tone — capacity for genuine openness '
                       'to others. Primary physiological L-proxy. URB #481 live.',
        'normalization': ('scale', 0, 100),
        'evidence': 'High RMSSD = high vagal tone = social engagement system active '
                    '(Polyvagal Theory, Porges). Prosocial behavior, empathy, '
                    'openness to others all require high parasympathetic baseline.',
    },
    'hrv_coherence': {
        'dimension': 'L', 'weight': 0.25,
        'label': 'HRV Coherence (0–1, Polar H10)',
        'description': 'Rhythm coherence — heart-brain synchrony reflecting genuine '
                       'other-orientation. URB #481 primary L-proxy.',
        'normalization': ('clamp', 0.0, 1.0),
        'evidence': 'HeartMath: HRV coherence predicts prosocial behavior and empathic '
                    'accuracy. High coherence = L-dimension functional baseline.',
    },
    'theta_power': {
        'dimension': 'L', 'weight': 0.20,
        'label': 'Theta Power (4–8 Hz, Muse 2)',
        'description': 'Deep parasympathetic engagement, compassion state, '
                       'deep empathic processing.',
        'normalization': ('scale', 0, 500),
        'evidence': 'Theta during compassion meditation peaks in advanced practitioners '
                    '(Lutz et al. 2008). Theta = emotional depth, connection.',
    },
    'lf_hf_ratio': {
        'dimension': 'L', 'weight': 0.15,
        'label': 'LF/HF Ratio Balance (Polar H10)',
        'description': 'Sympathovagal balance. Optimal near 1.0. '
                       'Imbalance (high LF/HF) signals stress overriding openness.',
        'normalization': ('optimal', 1.0, 3.0),
        'evidence': 'LF/HF ratio reflects autonomic balance. High HF = parasympathetic '
                    'dominance = L-dimension activation. Optimal near 1:1.',
    },
    'suffering_activation': {
        'dimension': 'L', 'weight': 0.10,
        'label': 'Suffering-Activation Response (0–10)',
        'description': 'Degree to which others\' suffering activates motivation to help. '
                       'Direct L-dimension behavioral signature.',
        'normalization': ('scale', 0, 10),
        'evidence': 'Agape love (unconditional other-orientation) is defined by '
                    'suffering-activation: suffering of another creates motivation '
                    'to alleviate it independent of personal gain.',
    },

    # ── E (Environment — lowest weight, correctly ~15% of GILE total) ────────
    'resting_heart_rate': {
        'dimension': 'E', 'weight': 0.20,
        'label': 'Resting Heart Rate (BPM, Polar H10)',
        'description': 'Cardiovascular E-dimension baseline. Optimal 50–70 BPM.',
        'normalization': ('optimal', 60, 20),
        'evidence': 'Standard cardiovascular health metric. E-dimension only.',
    },
    'sleep_score': {
        'dimension': 'E', 'weight': 0.25,
        'label': 'Sleep Score (0–100, Oura Ring)',
        'description': 'Physical restoration quality. E-dimension proxy.',
        'normalization': ('scale', 0, 100),
        'evidence': 'Sleep quality reflects physical recovery — important E-dimension '
                    'factor. Note: poor sleep can suppress G/I/L expression temporarily.',
    },
    'physical_health_index': {
        'dimension': 'E', 'weight': 0.20,
        'label': 'Physical Health Index (0–10, self-report)',
        'description': 'Overall physical wellbeing: absence of illness, energy levels, '
                       'physical functioning. Pure E-dimension.',
        'normalization': ('scale', 0, 10),
        'evidence': 'Conventional health metric. E-level only — does not predict GIL.',
    },
    'financial_stability': {
        'dimension': 'E', 'weight': 0.20,
        'label': 'Financial Stability (0–10, self-report)',
        'description': 'Resource security. Low E-dimension weight. '
                       'Notably decoupled from GIL (L*/+E proof).',
        'normalization': ('scale', 0, 10),
        'evidence': 'The L*/+E proof: financial stability and GIL can be completely '
                    'decoupled — confirming E is appended, not derived.',
    },
    'social_recognition': {
        'dimension': 'E', 'weight': 0.15,
        'label': 'Institutional Recognition (0–10, self-report)',
        'description': 'Degree of recognition by conventional institutions. '
                       'E-dimension only — systematically misses Q2 individuals.',
        'normalization': ('scale', 0, 10),
        'evidence': 'The Inverse Metric Problem: institutional recognition is E-level '
                    'output and may anti-correlate with Q2 (High GIL/Low E).',
    },
}


# ─── Brandon's known/estimated data (March 2026) ─────────────────────────────

BRANDON_BASELINE = {
    # G proxies
    'urb_corpus_volume': 137,
    'meditation_prayer_hours_weekly': 7.0,
    'alpha_power': None,
    'pattern_obsession_depth': 9.5,
    'cardiac_coherence_score': None,

    # I proxies
    'gamma_power': None,
    'gamma_alpha_ratio': None,
    'theta_alpha_ratio': None,
    'eeg_cross_coherence': None,
    'synchronicity_frequency': 12.0,
    'adhd_spontaneity': 8.5,
    'bipolar_mood_range': 8.0,

    # L proxies
    'hrv_rmssd': None,
    'hrv_coherence': None,
    'theta_power': None,
    'lf_hf_ratio': None,
    'suffering_activation': 9.0,

    # E proxies
    'resting_heart_rate': None,
    'sleep_score': None,
    'physical_health_index': 4.0,
    'financial_stability': 3.0,
    'social_recognition': 3.0,
}


def normalize(value: float, norm_type: str, param1, param2) -> float:
    if norm_type == 'scale':
        return max(0.0, min(1.0, value / param2)) if param2 > 0 else 0.5
    elif norm_type == 'clamp':
        return max(param1, min(param2, value))
    elif norm_type == 'optimal':
        deviation = abs(value - param1)
        return max(0.0, 1.0 - deviation / param2)
    return 0.5


def compute_gile_portrait(data: Dict[str, Optional[float]]) -> Dict:
    """
    Compute the full GILE portrait from a data dict.
    Returns per-dimension scores, composite GIL score, total GILE score,
    Emerick Constant comparison, and L*/+E quadrant.
    """
    dim_scores = {'G': [], 'I': [], 'L': [], 'E': []}
    dim_weights = {'G': [], 'I': [], 'L': [], 'E': []}
    available_markers = {'G': [], 'I': [], 'L': [], 'E': []}

    for key, bm in BIOMARKERS.items():
        val = data.get(key)
        if val is None:
            continue
        norm_args = bm['normalization']
        normed = normalize(val, norm_args[0], norm_args[1], norm_args[2])
        dim = bm['dimension']
        w = bm['weight']
        dim_scores[dim].append(normed * w)
        dim_weights[dim].append(w)
        available_markers[dim].append(key)

    raw = {}
    for dim in 'GILE':
        if dim_weights[dim]:
            raw[dim] = sum(dim_scores[dim]) / sum(dim_weights[dim])
        else:
            raw[dim] = None

    filled = {d: (raw[d] if raw[d] is not None else 0.5) for d in 'GILE'}
    total = sum(filled[d] * GILE_WEIGHTS[d] for d in 'GILE')
    gil_composite = sum(filled[d] * GILE_WEIGHTS[d] / (1 - GILE_WEIGHTS['E'])
                        for d in 'GIL')

    transcendent = gil_composite >= C_EMERICK

    e_score = filled['E']
    gil_score = gil_composite
    if e_score >= 0.5 and gil_score >= C_EMERICK:
        quadrant = 'Q1'
        quadrant_label = 'Fully Integrated — high GIL and high E'
    elif e_score < 0.5 and gil_score >= C_EMERICK:
        quadrant = 'Q2'
        quadrant_label = 'Transcendent but Unrecognized — high GIL, low E (L*/+E proof case)'
    elif e_score >= 0.5 and gil_score < C_EMERICK:
        quadrant = 'Q3'
        quadrant_label = 'Corporate Machine — high E, low GIL'
    else:
        quadrant = 'Q4'
        quadrant_label = 'Depleted — low on all dimensions'

    return {
        'raw': raw,
        'filled': filled,
        'available_markers': available_markers,
        'total_gile': total,
        'gil_composite': gil_composite,
        'c_emerick': C_EMERICK,
        'transcendent': transcendent,
        'quadrant': quadrant,
        'quadrant_label': quadrant_label,
        'gile_weights': GILE_WEIGHTS,
    }


def get_dimension_narrative(dim: str, score: float) -> str:
    if dim == 'G':
        if score >= 0.8:
            return "Exceptional — sustained truth-seeking orientation, deep moral integrity"
        elif score >= 0.6:
            return "Strong — clear value alignment and consistent philosophical depth"
        elif score >= 0.4:
            return "Moderate — present but inconsistent or early in development"
        else:
            return "Low — values weakly held or environmentally defined"
    elif dim == 'I':
        if score >= 0.8:
            return "Exceptional — i-channel frequently open; high gamma, strong synchronicity"
        elif score >= 0.6:
            return "Strong — regular i-channel access; above-baseline gamma and synthesis"
        elif score >= 0.4:
            return "Moderate — occasional flashes; analytical mode dominant"
        else:
            return "Low — i-channel largely blocked; linear processing dominant"
    elif dim == 'L':
        if score >= 0.8:
            return "Exceptional — high parasympathetic baseline; genuine other-orientation"
        elif score >= 0.6:
            return "Strong — good vagal tone; prosocial and empathically active"
        elif score >= 0.4:
            return "Moderate — L-function present but stress-suppressed"
        else:
            return "Low — sympathetic dominance limiting genuine other-orientation"
    elif dim == 'E':
        if score >= 0.8:
            return "High E — conventionally 'successful'; note: decoupled from GIL (L*/+E)"
        elif score >= 0.6:
            return "Moderate-high E — stable environmental baseline"
        elif score >= 0.4:
            return "Moderate E — typical challenges; E is lowest GILE dimension"
        else:
            return "Low E — challenging conventional profile; does NOT indicate low GIL"
    return ""
