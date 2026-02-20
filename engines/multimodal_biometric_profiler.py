"""
MULTI-MODAL BIOMETRIC PROFILER ENGINE
========================================
Integrates 12+ biometric data channels for comprehensive consciousness
measurement, health assessment, and human compatibility matching.

MODALITIES:
1. Typing Patterns (Keystroke Dynamics)
2. Fingerprint Analysis (Dermatoglyphics)
3. Genetic Data (SNPs, Pharmacogenomics)
4. Spirometry (Breath Monitoring)
5. Apple Watch Metrics (Gait, Temperature, HRV)
6. Facial Ratios (Morphological Analysis)
7. Digit Ratios (2D:4D Prenatal Hormones)
8. Oura Ring Data (Sleep, Readiness, Activity)
9. Voice Analysis (F0, Formants, Emotion)
10. Name/Birthday Numerology & Astrology
11. Compatibility Matching Engine
12. Online Stranger Profiling

Each modality maps to GILE dimensions:
G (Goodness/Existence) - Physical measurements
I (Intuition) - Pattern recognition metrics
L (Love/Connection) - Relational indicators
E (Environment) - Context-dependent adaptations

Tralse confidence scoring ensures honest uncertainty reporting.
"""

import os
import json
import math
import time
import hashlib
import numpy as np
import psycopg2
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple, Any
from collections import defaultdict


MODALITY_WEIGHTS = {
    'genetic': {'G': 0.95, 'I': 0.80, 'L': 0.75, 'E': 0.70, 'evidence': 'strong'},
    'oura': {'G': 0.80, 'I': 0.70, 'L': 0.85, 'E': 0.75, 'evidence': 'strong'},
    'apple_watch': {'G': 0.85, 'I': 0.60, 'L': 0.70, 'E': 0.80, 'evidence': 'strong'},
    'spirometry': {'G': 0.75, 'I': 0.65, 'L': 0.70, 'E': 0.80, 'evidence': 'strong'},
    'typing': {'G': 0.40, 'I': 0.85, 'L': 0.60, 'E': 0.70, 'evidence': 'moderate'},
    'voice': {'G': 0.70, 'I': 0.75, 'L': 0.80, 'E': 0.65, 'evidence': 'moderate'},
    'digit_ratio': {'G': 0.80, 'I': 0.60, 'L': 0.50, 'E': 0.45, 'evidence': 'moderate'},
    'facial': {'G': 0.65, 'I': 0.50, 'L': 0.55, 'E': 0.40, 'evidence': 'moderate'},
    'fingerprint': {'G': 0.70, 'I': 0.55, 'L': 0.45, 'E': 0.50, 'evidence': 'moderate'},
    'numerology': {'G': 0.20, 'I': 0.30, 'L': 0.35, 'E': 0.25, 'evidence': 'tralse'},
}

COMPATIBILITY_WEIGHTS = {
    'romantic': {
        'genetic_mhc': 0.25, 'voice_match': 0.20, 'gile_alignment': 0.20,
        'emotional_resonance': 0.15, 'physical_compat': 0.10, 'symbolic_resonance': 0.10
    },
    'business': {
        'cognitive_complement': 0.30, 'communication_align': 0.25,
        'stress_complement': 0.20, 'gile_alignment': 0.15, 'symbolic_harmony': 0.10
    },
    'friendship': {
        'gile_alignment': 0.30, 'communication_style': 0.25,
        'emotional_resonance': 0.20, 'shared_traits': 0.15, 'symbolic_resonance': 0.10
    }
}


class KeystrokeDynamicsAdapter:
    """Extracts consciousness indicators from typing patterns."""

    def extract_features(self, raw_data) -> Dict:
        if isinstance(raw_data, dict):
            if 'summary' in raw_data:
                s = raw_data['summary']
                return {
                    'mean_dwell_time': s.get('mean_dwell_time', 100),
                    'mean_flight_time': s.get('mean_flight_time', 150),
                    'typing_speed_wpm': s.get('typing_speed_wpm', 40),
                    'error_rate': s.get('error_rate', 0.05),
                    'rhythm_variance': s.get('rhythm_variance', 40),
                    'total_keys': s.get('total_keys', 0),
                    'fatigue_index': 0.0,
                    'consciousness_state': self._detect_state(
                        s.get('mean_dwell_time', 100), s.get('mean_flight_time', 150),
                        s.get('rhythm_variance', 40), s.get('error_rate', 0.05)),
                }
            keystroke_events = raw_data.get('keystroke_events', [])
        else:
            keystroke_events = raw_data

        if not keystroke_events:
            return self._empty_features()

        dwell_times = []
        flight_times = []
        errors = 0
        total_keys = len(keystroke_events)

        for i, event in enumerate(keystroke_events):
            if isinstance(event, dict):
                if 'dwell_time' in event:
                    dwell_times.append(event['dwell_time'])
                if 'flight_time' in event and event['flight_time'] is not None:
                    flight_times.append(event['flight_time'])
                if event.get('key') == 'Backspace':
                    errors += 1

        duration_sec = 1.0
        if len(keystroke_events) > 1 and isinstance(keystroke_events[0], dict):
            duration_sec = (keystroke_events[-1].get('timestamp', 0) -
                           keystroke_events[0].get('timestamp', 0)) / 1000.0
            if duration_sec <= 0:
                duration_sec = 1.0
        words = total_keys / 5.0
        wpm = (words / duration_sec) * 60 if duration_sec > 0 else 0

        mean_dwell = np.mean(dwell_times) if dwell_times else 100.0
        mean_flight = np.mean(flight_times) if flight_times else 150.0
        rhythm_var = np.std(flight_times) if len(flight_times) > 2 else 0.0
        error_rate = errors / total_keys if total_keys > 0 else 0.0

        return {
            'mean_dwell_time': round(mean_dwell, 2),
            'mean_flight_time': round(mean_flight, 2),
            'typing_speed_wpm': round(wpm, 1),
            'error_rate': round(error_rate, 4),
            'rhythm_variance': round(rhythm_var, 2),
            'total_keys': total_keys,
            'fatigue_index': self._compute_fatigue(dwell_times),
            'consciousness_state': self._detect_state(mean_dwell, mean_flight, rhythm_var, error_rate),
        }

    def compute_gile(self, features: Dict) -> Dict:
        dwell = features.get('mean_dwell_time', 100)
        flight = features.get('mean_flight_time', 150)
        var = features.get('rhythm_variance', 50)
        err = features.get('error_rate', 0.05)
        wpm = features.get('typing_speed_wpm', 40)

        g = max(0, min(1, 1.0 - (err * 5)))
        i = max(0, min(1, (wpm / 100.0)))
        l = max(0, min(1, 1.0 - (var / 200.0)))
        e = max(0, min(1, 0.5 + (0.5 if dwell < 120 else -0.2)))

        return {'G': round(g, 3), 'I': round(i, 3), 'L': round(l, 3), 'E': round(e, 3)}

    def _compute_fatigue(self, dwell_times: List[float]) -> float:
        if len(dwell_times) < 20:
            return 0.0
        first_half = np.mean(dwell_times[:len(dwell_times)//2])
        second_half = np.mean(dwell_times[len(dwell_times)//2:])
        return round((second_half - first_half) / first_half, 4) if first_half > 0 else 0.0

    def _detect_state(self, dwell, flight, var, err):
        if var < 30 and err < 0.02:
            return 'flow'
        elif dwell > 120 and flight < 100:
            return 'concentrated'
        elif dwell < 80 and flight > 200:
            return 'scattered'
        elif err > 0.1:
            return 'agitated'
        else:
            return 'normal'

    def _empty_features(self):
        return {'mean_dwell_time': 0, 'mean_flight_time': 0, 'typing_speed_wpm': 0,
                'error_rate': 0, 'rhythm_variance': 0, 'total_keys': 0,
                'fatigue_index': 0, 'consciousness_state': 'unknown'}


class DermatoglyphicsAdapter:
    """Analyzes fingerprint patterns for prenatal development indicators."""

    PATTERN_TRAITS = {
        'loop': {'personality': 'Adaptable, flexible', 'testosterone': 'moderate', 'prevalence': 0.625},
        'whorl': {'personality': 'Independent, determined', 'testosterone': 'high', 'prevalence': 0.30},
        'arch': {'personality': 'Practical, conventional', 'testosterone': 'low', 'prevalence': 0.05},
        'composite': {'personality': 'Complex, multifaceted', 'testosterone': 'variable', 'prevalence': 0.025},
    }

    def extract_features(self, fingerprint_data: Dict) -> Dict:
        patterns = fingerprint_data.get('patterns', {})
        ridge_count = fingerprint_data.get('total_ridge_count', 0)

        pattern_counts = defaultdict(int)
        for finger, pattern in patterns.items():
            pattern_counts[pattern.lower()] += 1

        dominant = max(pattern_counts, key=pattern_counts.get) if pattern_counts else 'unknown'
        symmetry = self._compute_symmetry(patterns)

        return {
            'dominant_pattern': dominant,
            'pattern_distribution': dict(pattern_counts),
            'total_ridge_count': ridge_count,
            'symmetry_score': round(symmetry, 3),
            'developmental_quality': self._developmental_score(ridge_count, symmetry),
            'personality_indicator': self.PATTERN_TRAITS.get(dominant, {}).get('personality', 'Unknown'),
            'prenatal_testosterone': self.PATTERN_TRAITS.get(dominant, {}).get('testosterone', 'unknown'),
        }

    def compute_gile(self, features: Dict) -> Dict:
        dev_q = features.get('developmental_quality', 0.5)
        sym = features.get('symmetry_score', 0.5)
        dominant = features.get('dominant_pattern', 'loop')

        g = dev_q
        i = 0.7 if dominant == 'whorl' else 0.5 if dominant == 'loop' else 0.4
        l = sym * 0.8
        e = dev_q * 0.7

        return {'G': round(g, 3), 'I': round(i, 3), 'L': round(l, 3), 'E': round(e, 3)}

    def _compute_symmetry(self, patterns: Dict) -> float:
        left = ['left_thumb', 'left_index', 'left_middle', 'left_ring', 'left_little']
        right = ['right_thumb', 'right_index', 'right_middle', 'right_ring', 'right_little']
        matches = sum(1 for l, r in zip(left, right)
                     if patterns.get(l, '').lower() == patterns.get(r, '').lower())
        return matches / 5.0

    def _developmental_score(self, ridge_count: int, symmetry: float) -> float:
        ridge_norm = min(1.0, ridge_count / 200.0) if ridge_count > 0 else 0.5
        return round((ridge_norm * 0.6 + symmetry * 0.4), 3)


class GeneticDataAdapter:
    """Processes genetic SNP data for consciousness and health profiling."""

    KEY_SNPS = {
        'rs4680': {
            'name': 'COMT Val158Met',
            'alleles': {
                'GG': {'label': 'Warrior (Val/Val)', 'dopamine': 'fast_clearance', 'stress_resilience': 0.8},
                'AG': {'label': 'Mixed (Val/Met)', 'dopamine': 'moderate', 'stress_resilience': 0.6},
                'AA': {'label': 'Worrier (Met/Met)', 'dopamine': 'slow_clearance', 'stress_resilience': 0.4},
            },
            'gile_dimension': 'I',
        },
        'rs324420': {
            'name': 'FAAH C385A',
            'alleles': {
                'CC': {'label': 'Standard FAAH', 'anandamide': 'normal', 'baseline_mood': 0.5},
                'CA': {'label': 'Enhanced FAAH', 'anandamide': 'elevated', 'baseline_mood': 0.7},
                'AA': {'label': 'High Anandamide', 'anandamide': 'high', 'baseline_mood': 0.85},
            },
            'gile_dimension': 'L',
        },
        'rs6265': {
            'name': 'BDNF Val66Met',
            'alleles': {
                'CC': {'label': 'Val/Val (Normal)', 'neuroplasticity': 'high', 'attractor_malleability': 0.8},
                'CT': {'label': 'Val/Met', 'neuroplasticity': 'moderate', 'attractor_malleability': 0.6},
                'TT': {'label': 'Met/Met', 'neuroplasticity': 'reduced', 'attractor_malleability': 0.4},
            },
            'gile_dimension': 'I',
        },
        'rs1800497': {
            'name': 'DRD2/ANKK1 Taq1A',
            'alleles': {
                'CC': {'label': 'Normal D2', 'reward_sensitivity': 'normal', 'nfc_indicator': 0.5},
                'CT': {'label': 'Reduced D2', 'reward_sensitivity': 'elevated', 'nfc_indicator': 0.7},
                'TT': {'label': 'Low D2', 'reward_sensitivity': 'high', 'nfc_indicator': 0.85},
            },
            'gile_dimension': 'I',
        },
    }

    PHARMACOGENOMIC_SNPS = {
        'rs3892097': {'name': 'CYP2D6', 'enzyme': 'Drug metabolism (codeine, SSRIs, beta-blockers)'},
        'rs4244285': {'name': 'CYP2C19', 'enzyme': 'Drug metabolism (PPIs, clopidogrel, SSRIs)'},
        'rs776746': {'name': 'CYP3A5', 'enzyme': 'Drug metabolism (tacrolimus, statins)'},
        'rs1801133': {'name': 'MTHFR C677T', 'enzyme': 'Folate metabolism (mood, cognition)'},
    }

    def extract_features(self, genetic_data: Dict) -> Dict:
        snp_results = genetic_data.get('snps', {})
        features = {
            'analyzed_snps': {},
            'consciousness_genes': {},
            'pharmacogenomics': {},
            'gile_genetic_score': {},
            'wood_fire_indicators': {},
        }

        g_scores, i_scores, l_scores, e_scores = [], [], [], []

        for rsid, info in self.KEY_SNPS.items():
            genotype = snp_results.get(rsid, 'Unknown')
            if genotype in info['alleles']:
                allele_data = info['alleles'][genotype]
                features['consciousness_genes'][rsid] = {
                    'name': info['name'],
                    'genotype': genotype,
                    'label': allele_data['label'],
                    'details': {k: v for k, v in allele_data.items() if k != 'label'},
                }

                dim = info['gile_dimension']
                score_val = list(allele_data.values())[-1]
                if isinstance(score_val, (int, float)):
                    if dim == 'G': g_scores.append(score_val)
                    elif dim == 'I': i_scores.append(score_val)
                    elif dim == 'L': l_scores.append(score_val)
                    elif dim == 'E': e_scores.append(score_val)

        for rsid, info in self.PHARMACOGENOMIC_SNPS.items():
            genotype = snp_results.get(rsid, 'Unknown')
            features['pharmacogenomics'][rsid] = {
                'name': info['name'],
                'genotype': genotype,
                'enzyme': info['enzyme'],
            }

        comt = snp_results.get('rs4680', '')
        drd2 = snp_results.get('rs1800497', '')
        features['wood_fire_indicators'] = {
            'comt_type': 'warrior' if comt == 'GG' else 'worrier' if comt == 'AA' else 'mixed',
            'nfc_genetic_indicator': 'high' if drd2 in ('CT', 'TT') else 'standard',
            'predicted_yerkes_dodson': 'inverted' if comt == 'GG' and drd2 in ('CT', 'TT') else 'standard',
        }

        features['gile_genetic_score'] = {
            'G': round(np.mean(g_scores), 3) if g_scores else 0.5,
            'I': round(np.mean(i_scores), 3) if i_scores else 0.5,
            'L': round(np.mean(l_scores), 3) if l_scores else 0.5,
            'E': round(np.mean(e_scores), 3) if e_scores else 0.5,
        }

        return features

    def compute_gile(self, features: Dict) -> Dict:
        return features.get('gile_genetic_score', {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5})


class SpirometryAdapter:
    """Processes breathing pattern data for consciousness state detection."""

    def extract_features(self, breath_data: Dict) -> Dict:
        rate = breath_data.get('respiratory_rate', 15)
        ie_ratio = breath_data.get('ie_ratio', 2.0)
        tidal_vol = breath_data.get('tidal_volume', 500)
        hold_time = breath_data.get('breath_hold_seconds', 0)
        rsa = breath_data.get('rsa_amplitude', 0)
        regularity = breath_data.get('regularity', 0.5)

        coherence_dist = abs(rate - 6.0) / 6.0
        coherence_score = max(0, 1.0 - coherence_dist)

        if rate < 8 and ie_ratio >= 2.5:
            state = 'deep_relaxation'
        elif 5 <= rate <= 7 and regularity > 0.8:
            state = 'heart_coherence'
        elif rate > 20:
            state = 'stress_hyperventilation'
        elif regularity < 0.3:
            state = 'erratic_processing'
        else:
            state = 'normal'

        return {
            'respiratory_rate': rate,
            'ie_ratio': ie_ratio,
            'tidal_volume': tidal_vol,
            'breath_hold_seconds': hold_time,
            'rsa_amplitude': rsa,
            'regularity': regularity,
            'coherence_score': round(coherence_score, 3),
            'consciousness_state': state,
            'lcc_readiness': coherence_score > 0.7,
            'vagal_tone_indicator': round(min(1.0, hold_time / 60.0), 3),
        }

    def compute_gile(self, features: Dict) -> Dict:
        vagal = features.get('vagal_tone_indicator', 0.5)
        coh = features.get('coherence_score', 0.5)
        reg = features.get('regularity', 0.5)

        return {
            'G': round(vagal * 0.8 + 0.2, 3),
            'I': round(coh * 0.7 + reg * 0.3, 3),
            'L': round(coh * 0.9, 3),
            'E': round(reg * 0.8 + 0.1, 3),
        }


class AppleWatchAdapter:
    """Processes Apple Watch / Apple Health data."""

    def extract_features(self, watch_data: Dict) -> Dict:
        cardio = watch_data.get('cardiovascular', {})
        movement = watch_data.get('movement', {})
        temp = watch_data.get('temperature', {})
        sleep = watch_data.get('sleep', {})

        gait_sym = movement.get('gait_symmetry', 50.0)
        walk_steady = movement.get('walking_steadiness', 'OK')
        wrist_temp_dev = temp.get('wrist_deviation', 0.0)

        gait_balance = gait_sym / 100.0
        neuro_health = 1.0 if walk_steady == 'OK' else 0.7 if walk_steady == 'Low' else 0.4

        return {
            'resting_hr': cardio.get('resting_hr', 70),
            'hrv_sdnn': cardio.get('hrv_sdnn', 40),
            'vo2_max': cardio.get('vo2_max', 35),
            'spo2': cardio.get('spo2', 97),
            'steps': movement.get('steps', 0),
            'gait_symmetry': gait_sym,
            'walking_steadiness': walk_steady,
            'double_support_time': movement.get('double_support_time', 28),
            'walking_speed': movement.get('walking_speed', 1.2),
            'step_length': movement.get('step_length', 0.7),
            'wrist_temp_deviation': wrist_temp_dev,
            'sleep_duration': sleep.get('duration_hours', 7),
            'sleep_deep_pct': sleep.get('deep_pct', 15),
            'sleep_rem_pct': sleep.get('rem_pct', 20),
            'gait_balance_score': round(gait_balance, 3),
            'neurological_health': round(neuro_health, 3),
            'temp_stability': round(max(0, 1.0 - abs(wrist_temp_dev) / 2.0), 3),
        }

    def compute_gile(self, features: Dict) -> Dict:
        vo2 = min(1.0, features.get('vo2_max', 35) / 60.0)
        spo2 = min(1.0, features.get('spo2', 97) / 100.0)
        hrv = min(1.0, features.get('hrv_sdnn', 40) / 100.0)
        gait = features.get('gait_balance_score', 0.5)
        neuro = features.get('neurological_health', 0.5)
        temp = features.get('temp_stability', 0.5)

        return {
            'G': round((vo2 + spo2 + neuro) / 3, 3),
            'I': round((gait + neuro) / 2, 3),
            'L': round(hrv, 3),
            'E': round((temp + gait) / 2, 3),
        }


class FacialRatioAdapter:
    """Analyzes facial proportions for trait indicators."""

    GOLDEN_RATIO = 1.618033988749895

    def extract_features(self, facial_data: Dict) -> Dict:
        fwhr = facial_data.get('fwhr', 1.8)
        symmetry = facial_data.get('symmetry_score', 0.85)
        golden_dev = facial_data.get('golden_ratio_deviation', 0.1)
        neoteny = facial_data.get('neoteny_index', 0.5)
        thirds = facial_data.get('thirds_ratio', [0.33, 0.33, 0.34])

        thirds_balance = 1.0 - np.std(thirds) * 3 if len(thirds) == 3 else 0.5

        dominance = 'high' if fwhr > 2.0 else 'moderate' if fwhr > 1.7 else 'low'

        return {
            'fwhr': fwhr,
            'symmetry_score': symmetry,
            'golden_ratio_deviation': golden_dev,
            'neoteny_index': neoteny,
            'thirds_balance': round(max(0, thirds_balance), 3),
            'dominance_indicator': dominance,
            'developmental_stability': round(symmetry * 0.7 + thirds_balance * 0.3, 3),
            'perceived_trustworthiness': round(neoteny * 0.6 + symmetry * 0.4, 3),
        }

    def compute_gile(self, features: Dict) -> Dict:
        sym = features.get('symmetry_score', 0.5)
        dev_stab = features.get('developmental_stability', 0.5)
        trust = features.get('perceived_trustworthiness', 0.5)
        neo = features.get('neoteny_index', 0.5)

        return {
            'G': round(dev_stab, 3),
            'I': round(0.5 + (features.get('fwhr', 1.8) - 1.8) * 0.5, 3),
            'L': round(trust, 3),
            'E': round(sym * 0.6 + neo * 0.4, 3),
        }


class DigitRatioAdapter:
    """Analyzes 2D:4D digit ratio for prenatal hormone indicators."""

    POPULATION_NORMS = {
        'male': {'mean': 0.947, 'sd': 0.029},
        'female': {'mean': 0.965, 'sd': 0.026},
    }

    def extract_features(self, digit_data: Dict) -> Dict:
        ratio_right = digit_data.get('right_hand_ratio', 0.95)
        ratio_left = digit_data.get('left_hand_ratio', 0.96)
        sex = digit_data.get('biological_sex', 'unknown')

        mean_ratio = (ratio_right + ratio_left) / 2
        asymmetry = abs(ratio_right - ratio_left)

        if sex in self.POPULATION_NORMS:
            norm = self.POPULATION_NORMS[sex]
            z_score = (ratio_right - norm['mean']) / norm['sd']
        else:
            z_score = (ratio_right - 0.956) / 0.03

        testosterone_level = 'high' if ratio_right < 0.94 else 'moderate' if ratio_right < 0.97 else 'low'
        spatial_indicator = max(0, min(1, 1.0 - (ratio_right - 0.90) * 5))
        risk_taking = max(0, min(1, 1.0 - (ratio_right - 0.92) * 8))

        return {
            'right_hand_ratio': ratio_right,
            'left_hand_ratio': ratio_left,
            'mean_ratio': round(mean_ratio, 4),
            'asymmetry': round(asymmetry, 4),
            'z_score': round(z_score, 2),
            'prenatal_testosterone': testosterone_level,
            'spatial_ability_indicator': round(spatial_indicator, 3),
            'risk_taking_indicator': round(risk_taking, 3),
            'adhd_risk_indicator': 'elevated' if ratio_right < 0.94 else 'normal',
            'wood_fire_relevance': 'high' if ratio_right < 0.94 else 'moderate',
        }

    def compute_gile(self, features: Dict) -> Dict:
        spatial = features.get('spatial_ability_indicator', 0.5)
        risk = features.get('risk_taking_indicator', 0.5)

        return {
            'G': round(0.5 + (spatial - 0.5) * 0.4, 3),
            'I': round(spatial * 0.8, 3),
            'L': round(0.5 + (1.0 - risk) * 0.3, 3),
            'E': round(risk * 0.6, 3),
        }


class OuraRingAdapter:
    """Processes Oura Ring data for consciousness tracking."""

    def extract_features(self, oura_data: Dict) -> Dict:
        sleep = oura_data.get('sleep', {})
        readiness = oura_data.get('readiness', {})
        activity = oura_data.get('activity', {})

        sleep_score = sleep.get('score', 70)
        deep_pct = sleep.get('deep_sleep_pct', 15)
        rem_pct = sleep.get('rem_sleep_pct', 20)
        hrv_sleep = sleep.get('average_hrv', 40)
        rhr_sleep = sleep.get('lowest_resting_hr', 55)
        resp_rate = sleep.get('respiratory_rate', 15)
        temp_dev = sleep.get('temperature_deviation', 0.0)

        readiness_score = readiness.get('score', 70)
        activity_score = activity.get('score', 70)
        steps = activity.get('steps', 5000)

        consciousness_recovery = min(1.0, (deep_pct + rem_pct) / 50.0)
        vagal_tone = min(1.0, hrv_sleep / 80.0)
        homeostatic = max(0, 1.0 - abs(temp_dev) / 2.0)

        return {
            'sleep_score': sleep_score,
            'deep_sleep_pct': deep_pct,
            'rem_sleep_pct': rem_pct,
            'average_hrv': hrv_sleep,
            'lowest_resting_hr': rhr_sleep,
            'respiratory_rate': resp_rate,
            'temperature_deviation': temp_dev,
            'readiness_score': readiness_score,
            'activity_score': activity_score,
            'steps': steps,
            'consciousness_recovery': round(consciousness_recovery, 3),
            'vagal_tone_indicator': round(vagal_tone, 3),
            'homeostatic_stability': round(homeostatic, 3),
            'lcc_capacity_estimate': round(vagal_tone * consciousness_recovery, 3),
        }

    def compute_gile(self, features: Dict) -> Dict:
        vagal = features.get('vagal_tone_indicator', 0.5)
        recovery = features.get('consciousness_recovery', 0.5)
        homeo = features.get('homeostatic_stability', 0.5)
        readiness = min(1.0, features.get('readiness_score', 70) / 100.0)

        return {
            'G': round((readiness + homeo) / 2, 3),
            'I': round(recovery * 0.7 + vagal * 0.3, 3),
            'L': round(vagal, 3),
            'E': round(homeo * 0.6 + readiness * 0.4, 3),
        }


class VoiceAnalysisAdapter:
    """Analyzes vocal characteristics for personality and emotional profiling."""

    def extract_features(self, voice_data: Dict) -> Dict:
        f0 = voice_data.get('fundamental_frequency', 150)
        f0_range = voice_data.get('f0_range', 50)
        jitter = voice_data.get('jitter', 0.01)
        shimmer = voice_data.get('shimmer', 0.03)
        hnr = voice_data.get('hnr', 20)
        speaking_rate = voice_data.get('speaking_rate_wpm', 130)
        pause_ratio = voice_data.get('pause_ratio', 0.15)

        vocal_health = max(0, min(1, (hnr - 5) / 25.0))
        stress_index = min(1.0, jitter * 20 + shimmer * 10)
        emotional_range = min(1.0, f0_range / 100.0)

        if stress_index > 0.7:
            emotion = 'stressed'
        elif f0 > 200 and speaking_rate > 150:
            emotion = 'excited'
        elif f0 < 120 and speaking_rate < 100:
            emotion = 'sad'
        elif jitter < 0.01 and shimmer < 0.02:
            emotion = 'calm'
        else:
            emotion = 'neutral'

        return {
            'fundamental_frequency': f0,
            'f0_range': f0_range,
            'jitter': jitter,
            'shimmer': shimmer,
            'hnr': hnr,
            'speaking_rate_wpm': speaking_rate,
            'pause_ratio': pause_ratio,
            'vocal_health': round(vocal_health, 3),
            'stress_index': round(stress_index, 3),
            'emotional_range': round(emotional_range, 3),
            'detected_emotion': emotion,
            'warmth_indicator': round(max(0, min(1, 1.0 - (f0 - 150) / 200)), 3),
            'cognitive_complexity': round(pause_ratio * 2 + emotional_range * 0.5, 3),
        }

    def compute_gile(self, features: Dict) -> Dict:
        health = features.get('vocal_health', 0.5)
        complexity = features.get('cognitive_complexity', 0.5)
        warmth = features.get('warmth_indicator', 0.5)
        stress = features.get('stress_index', 0.3)

        return {
            'G': round(health, 3),
            'I': round(min(1, complexity * 0.8), 3),
            'L': round(warmth * 0.8 + (1 - stress) * 0.2, 3),
            'E': round((1 - stress) * 0.7 + health * 0.3, 3),
        }


class NumerologyAstrologyAdapter:
    """Computes numerological and astrological profiles."""

    PYTHAGOREAN = {chr(i): (i - ord('a')) % 9 + 1 for i in range(ord('a'), ord('z') + 1)}

    LIFE_PATH_MEANINGS = {
        1: 'Leader, Pioneer, Independent',
        2: 'Diplomat, Partner, Peacemaker',
        3: 'Creator, Communicator, Artist',
        4: 'Builder, Organizer, Pragmatist',
        5: 'Adventurer, Freedom-Seeker, Dynamic',
        6: 'Nurturer, Healer, Responsible',
        7: 'Seeker, Analyst, Spiritual',
        8: 'Achiever, Authority, Ambitious',
        9: 'Humanitarian, Idealist, Compassionate',
        11: 'Master Intuitive, Visionary, Inspired',
        22: 'Master Builder, Architect, Practical Visionary',
        33: 'Master Teacher, Healer, Selfless Service',
    }

    ZODIAC_SIGNS = [
        ('Capricorn', (1, 1), (1, 19)), ('Aquarius', (1, 20), (2, 18)),
        ('Pisces', (2, 19), (3, 20)), ('Aries', (3, 21), (4, 19)),
        ('Taurus', (4, 20), (5, 20)), ('Gemini', (5, 21), (6, 20)),
        ('Cancer', (6, 21), (7, 22)), ('Leo', (7, 23), (8, 22)),
        ('Virgo', (8, 23), (9, 22)), ('Libra', (9, 23), (10, 22)),
        ('Scorpio', (10, 23), (11, 21)), ('Sagittarius', (11, 22), (12, 21)),
        ('Capricorn', (12, 22), (12, 31)),
    ]

    ELEMENT_MAP = {
        'Aries': 'Fire', 'Leo': 'Fire', 'Sagittarius': 'Fire',
        'Taurus': 'Earth', 'Virgo': 'Earth', 'Capricorn': 'Earth',
        'Gemini': 'Air', 'Libra': 'Air', 'Aquarius': 'Air',
        'Cancer': 'Water', 'Scorpio': 'Water', 'Pisces': 'Water',
    }

    GILE_ELEMENT_MAP = {
        'Fire': {'G': 0.7, 'I': 0.8, 'L': 0.6, 'E': 0.5},
        'Earth': {'G': 0.8, 'I': 0.5, 'L': 0.6, 'E': 0.8},
        'Air': {'G': 0.5, 'I': 0.9, 'L': 0.7, 'E': 0.6},
        'Water': {'G': 0.6, 'I': 0.7, 'L': 0.9, 'E': 0.7},
    }

    def extract_features(self, identity_data: Dict) -> Dict:
        name = identity_data.get('full_name', '')
        birth_date = identity_data.get('birth_date', '')
        birth_time = identity_data.get('birth_time', '')
        birth_location = identity_data.get('birth_location', '')

        life_path = self._life_path(birth_date) if birth_date else 0
        expression = self._reduce_name(name) if name else 0
        soul_urge = self._soul_urge(name) if name else 0
        personality = self._personality_number(name) if name else 0
        sun_sign = self._sun_sign(birth_date) if birth_date else 'Unknown'
        element = self.ELEMENT_MAP.get(sun_sign, 'Unknown')

        return {
            'life_path_number': life_path,
            'life_path_meaning': self.LIFE_PATH_MEANINGS.get(life_path, 'Standard Path'),
            'expression_number': expression,
            'soul_urge_number': soul_urge,
            'personality_number': personality,
            'sun_sign': sun_sign,
            'element': element,
            'name_vibration': self._name_vibration(name),
            'birth_day_power': self._birth_day_power(birth_date),
            'master_number': life_path in (11, 22, 33),
            'tralse_confidence': 'tralse',
            'modality_note': 'Pattern-based assessment. Mechanism not scientifically established.',
        }

    def compute_gile(self, features: Dict) -> Dict:
        element = features.get('element', 'Unknown')
        base = self.GILE_ELEMENT_MAP.get(element, {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5})

        master_boost = 0.1 if features.get('master_number') else 0
        return {
            'G': round(min(1, base['G'] + master_boost), 3),
            'I': round(min(1, base['I'] + master_boost), 3),
            'L': round(min(1, base['L'] + master_boost), 3),
            'E': round(min(1, base['E'] + master_boost), 3),
        }

    def _reduce(self, n: int) -> int:
        if n in (11, 22, 33):
            return n
        while n > 9:
            n = sum(int(d) for d in str(n))
        return n

    def _life_path(self, birth_date: str) -> int:
        try:
            digits = [int(c) for c in birth_date if c.isdigit()]
            return self._reduce(sum(digits))
        except:
            return 0

    def _reduce_name(self, name: str) -> int:
        total = sum(self.PYTHAGOREAN.get(c.lower(), 0) for c in name if c.isalpha())
        return self._reduce(total)

    def _soul_urge(self, name: str) -> int:
        vowels = 'aeiou'
        total = sum(self.PYTHAGOREAN.get(c.lower(), 0) for c in name if c.lower() in vowels)
        return self._reduce(total)

    def _personality_number(self, name: str) -> int:
        vowels = 'aeiou'
        total = sum(self.PYTHAGOREAN.get(c.lower(), 0) for c in name if c.isalpha() and c.lower() not in vowels)
        return self._reduce(total)

    def _sun_sign(self, birth_date: str) -> str:
        try:
            parts = birth_date.replace('/', '-').split('-')
            if len(parts[0]) == 4:
                month, day = int(parts[1]), int(parts[2])
            else:
                month, day = int(parts[0]), int(parts[1])

            for sign, (sm, sd), (em, ed) in self.ZODIAC_SIGNS:
                if (month == sm and day >= sd) or (month == em and day <= ed):
                    return sign
            return 'Unknown'
        except:
            return 'Unknown'

    def _name_vibration(self, name: str) -> float:
        if not name:
            return 0.0
        values = [self.PYTHAGOREAN.get(c.lower(), 0) for c in name if c.isalpha()]
        return round(np.mean(values), 3) if values else 0.0

    def _birth_day_power(self, birth_date: str) -> int:
        try:
            parts = birth_date.replace('/', '-').split('-')
            day = int(parts[2]) if len(parts[0]) == 4 else int(parts[1])
            return self._reduce(day)
        except:
            return 0


class MultiModalBiometricProfiler:
    """
    Master engine integrating all biometric modalities into unified
    GILE profiles with Tralse confidence scoring and compatibility matching.
    """

    def __init__(self):
        self.adapters = {
            'typing': KeystrokeDynamicsAdapter(),
            'fingerprint': DermatoglyphicsAdapter(),
            'genetic': GeneticDataAdapter(),
            'spirometry': SpirometryAdapter(),
            'apple_watch': AppleWatchAdapter(),
            'facial': FacialRatioAdapter(),
            'digit_ratio': DigitRatioAdapter(),
            'oura': OuraRingAdapter(),
            'voice': VoiceAnalysisAdapter(),
            'numerology': NumerologyAstrologyAdapter(),
        }
        self.db_url = os.environ.get('DATABASE_URL', '')

    def _get_conn(self):
        return psycopg2.connect(self.db_url)

    def create_subject(self, name: str, external_id: str = None, consent_flags: Dict = None) -> int:
        conn = self._get_conn()
        try:
            cur = conn.cursor()
            ext_id = external_id or hashlib.md5(name.encode()).hexdigest()[:16]
            cur.execute("""
                INSERT INTO biometric_subjects (name, external_id, consent_flags)
                VALUES (%s, %s, %s)
                ON CONFLICT (external_id) DO UPDATE SET name = EXCLUDED.name
                RETURNING id
            """, (name, ext_id, json.dumps(consent_flags or {})))
            subject_id = cur.fetchone()[0]
            conn.commit()
            return subject_id
        finally:
            conn.close()

    def ingest_modality(self, subject_id: int, modality: str, raw_data: Dict, source: str = 'manual') -> Dict:
        if modality not in self.adapters:
            return {'error': f'Unknown modality: {modality}'}

        adapter = self.adapters[modality]
        features = adapter.extract_features(raw_data)
        gile_scores = adapter.compute_gile(features)
        quality = self._assess_quality(features, modality)

        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO modality_samples (subject_id, modality, raw_data, source, quality_score)
                VALUES (%s, %s, %s, %s, %s)
            """, (subject_id, modality, json.dumps(raw_data), source, quality))

            cur.execute("""
                INSERT INTO modality_features (subject_id, modality, features, gile_scores, quality_score)
                VALUES (%s, %s, %s, %s, %s)
            """, (subject_id, modality, json.dumps(features), json.dumps(gile_scores), quality))
            conn.commit()
        finally:
            conn.close()

        return {
            'modality': modality,
            'features': features,
            'gile_scores': gile_scores,
            'quality': quality,
        }

    def build_unified_profile(self, subject_id: int) -> Dict:
        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                SELECT DISTINCT ON (modality) modality, features, gile_scores, quality_score
                FROM modality_features
                WHERE subject_id = %s
                ORDER BY modality, timestamp DESC
            """, (subject_id,))
            rows = cur.fetchall()
        finally:
            conn.close()

        if not rows:
            return {'error': 'No modality data found for this subject'}

        gile_weighted = {'G': [], 'I': [], 'L': [], 'E': []}
        modality_details = {}
        total_quality = 0

        for modality, features_json, gile_json, quality in rows:
            features = json.loads(features_json) if isinstance(features_json, str) else features_json
            gile = json.loads(gile_json) if isinstance(gile_json, str) else gile_json
            weights = MODALITY_WEIGHTS.get(modality, {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5})

            for dim in ['G', 'I', 'L', 'E']:
                if dim in gile:
                    w = weights.get(dim, 0.5) * quality
                    gile_weighted[dim].append((gile[dim], w))

            modality_details[modality] = {
                'features': features,
                'gile': gile,
                'quality': quality,
                'evidence_level': weights.get('evidence', 'unknown'),
            }
            total_quality += quality

        unified_gile = {}
        for dim in ['G', 'I', 'L', 'E']:
            if gile_weighted[dim]:
                vals, ws = zip(*gile_weighted[dim])
                total_w = sum(ws)
                unified_gile[dim] = round(sum(v * w for v, w in zip(vals, ws)) / total_w, 3) if total_w > 0 else 0.5
            else:
                unified_gile[dim] = 0.5

        mood = round((unified_gile['L'] * 0.4 + unified_gile['I'] * 0.3 +
                      unified_gile['E'] * 0.2 + unified_gile['G'] * 0.1), 3)
        health = round((unified_gile['G'] * 0.5 + unified_gile['E'] * 0.25 +
                        unified_gile['L'] * 0.15 + unified_gile['I'] * 0.1), 3)
        consciousness = round(sum(unified_gile.values()) / 4, 3)
        lcc_est = round(min(1.0, consciousness * 1.2), 3)

        n_strong = sum(1 for m in modality_details.values() if m['evidence_level'] == 'strong')
        n_total = len(modality_details)
        tralse_conf = round(min(1.0, (n_strong * 0.3 + n_total * 0.1)), 3)
        tralse_state = 'true' if tralse_conf > 0.85 else 'tralse' if tralse_conf > 0.40 else 'false'

        profile = {
            'gile': unified_gile,
            'mood_score': mood,
            'health_score': health,
            'consciousness_level': consciousness,
            'lcc_estimate': lcc_est,
            'tralse_confidence': tralse_conf,
            'tralse_state': tralse_state,
            'modalities_used': list(modality_details.keys()),
            'modality_count': n_total,
            'modality_details': modality_details,
        }

        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO unified_profiles
                (subject_id, profile_json, gile_g, gile_i, gile_l, gile_e,
                 mood_score, health_score, consciousness_level, lcc_estimate, tralse_confidence)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (subject_id, json.dumps(profile),
                  unified_gile['G'], unified_gile['I'], unified_gile['L'], unified_gile['E'],
                  mood, health, consciousness, lcc_est, tralse_conf))
            conn.commit()
        finally:
            conn.close()

        return profile

    def compute_compatibility(self, subject_a: int, subject_b: int, context: str = 'romantic') -> Dict:
        profile_a = self.build_unified_profile(subject_a)
        profile_b = self.build_unified_profile(subject_b)

        if 'error' in profile_a or 'error' in profile_b:
            return {'error': 'Both subjects need profile data'}

        gile_a = profile_a['gile']
        gile_b = profile_b['gile']

        gile_sim = 1.0 - np.mean([abs(gile_a[d] - gile_b[d]) for d in ['G', 'I', 'L', 'E']])
        gile_complement = np.mean([abs(gile_a[d] - gile_b[d]) for d in ['G', 'I', 'L', 'E']])

        weights = COMPATIBILITY_WEIGHTS.get(context, COMPATIBILITY_WEIGHTS['friendship'])

        if context == 'romantic':
            score = (gile_sim * weights.get('gile_alignment', 0.2) +
                    (1 - abs(profile_a.get('mood_score', 0.5) - profile_b.get('mood_score', 0.5))) *
                    weights.get('emotional_resonance', 0.15) +
                    gile_complement * weights.get('voice_match', 0.2) +
                    gile_sim * weights.get('genetic_mhc', 0.25) +
                    gile_sim * weights.get('physical_compat', 0.1) +
                    gile_sim * weights.get('symbolic_resonance', 0.1))
        elif context == 'business':
            score = (gile_complement * weights.get('cognitive_complement', 0.3) +
                    gile_sim * weights.get('communication_align', 0.25) +
                    gile_complement * weights.get('stress_complement', 0.2) +
                    gile_sim * weights.get('gile_alignment', 0.15) +
                    gile_sim * weights.get('symbolic_harmony', 0.1))
        else:
            score = (gile_sim * weights.get('gile_alignment', 0.3) +
                    gile_sim * weights.get('communication_style', 0.25) +
                    gile_sim * weights.get('emotional_resonance', 0.2) +
                    gile_sim * weights.get('shared_traits', 0.15) +
                    gile_sim * weights.get('symbolic_resonance', 0.1))

        overall = round(score * 100, 1)

        strengths = []
        growth_areas = []
        for dim in ['G', 'I', 'L', 'E']:
            diff = abs(gile_a[dim] - gile_b[dim])
            if diff < 0.15:
                strengths.append(f"Strong {dim}-dimension alignment ({gile_a[dim]:.2f} / {gile_b[dim]:.2f})")
            elif diff > 0.3:
                growth_areas.append(f"{dim}-dimension gap ({gile_a[dim]:.2f} vs {gile_b[dim]:.2f})")

        result = {
            'overall_score': overall,
            'context': context,
            'gile_similarity': round(gile_sim, 3),
            'gile_complementarity': round(gile_complement, 3),
            'dimension_comparison': {
                d: {'a': gile_a[d], 'b': gile_b[d], 'diff': round(abs(gile_a[d] - gile_b[d]), 3)}
                for d in ['G', 'I', 'L', 'E']
            },
            'strengths': strengths,
            'growth_areas': growth_areas,
            'tralse_confidence': min(profile_a['tralse_confidence'], profile_b['tralse_confidence']),
        }

        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO compatibility_scores
                (subject_a, subject_b, context, overall_score, score_breakdown, strengths, growth_areas)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
            """, (subject_a, subject_b, context, overall,
                  json.dumps(result), strengths, growth_areas))
            conn.commit()
        finally:
            conn.close()

        return result

    def estimate_stranger_profile(self, public_data: Dict) -> Dict:
        available = {}
        if 'name' in public_data or 'birth_date' in public_data:
            adapter = self.adapters['numerology']
            features = adapter.extract_features(public_data)
            gile = adapter.compute_gile(features)
            available['numerology'] = {'features': features, 'gile': gile}

        if 'voice_f0' in public_data:
            voice_data = {
                'fundamental_frequency': public_data.get('voice_f0', 150),
                'f0_range': public_data.get('voice_range', 50),
                'jitter': public_data.get('voice_jitter', 0.015),
                'shimmer': public_data.get('voice_shimmer', 0.04),
                'hnr': public_data.get('voice_hnr', 18),
                'speaking_rate_wpm': public_data.get('speaking_rate', 130),
            }
            adapter = self.adapters['voice']
            features = adapter.extract_features(voice_data)
            gile = adapter.compute_gile(features)
            available['voice'] = {'features': features, 'gile': gile}

        if 'fwhr' in public_data or 'facial_symmetry' in public_data:
            facial_data = {
                'fwhr': public_data.get('fwhr', 1.8),
                'symmetry_score': public_data.get('facial_symmetry', 0.85),
                'golden_ratio_deviation': public_data.get('golden_deviation', 0.1),
                'neoteny_index': public_data.get('neoteny', 0.5),
            }
            adapter = self.adapters['facial']
            features = adapter.extract_features(facial_data)
            gile = adapter.compute_gile(features)
            available['facial'] = {'features': features, 'gile': gile}

        if not available:
            return {'error': 'No public data provided'}

        gile_fused = {'G': [], 'I': [], 'L': [], 'E': []}
        for mod, data in available.items():
            weights = MODALITY_WEIGHTS.get(mod, {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5})
            for dim in ['G', 'I', 'L', 'E']:
                gile_fused[dim].append(data['gile'][dim] * weights.get(dim, 0.5))

        estimated_gile = {d: round(np.mean(v), 3) if v else 0.5 for d, v in gile_fused.items()}

        return {
            'estimated_gile': estimated_gile,
            'modalities_available': list(available.keys()),
            'modality_details': available,
            'tralse_confidence': 'low_tralse',
            'confidence_note': 'Profile estimated from limited public data. Treat as preliminary.',
            'data_sources': len(available),
        }

    def _assess_quality(self, features: Dict, modality: str) -> float:
        non_zero = sum(1 for v in features.values()
                      if isinstance(v, (int, float)) and v != 0)
        total = max(1, sum(1 for v in features.values() if isinstance(v, (int, float))))
        completeness = non_zero / total

        evidence = MODALITY_WEIGHTS.get(modality, {}).get('evidence', 'tralse')
        evidence_mult = {'strong': 1.0, 'moderate': 0.8, 'tralse': 0.5}.get(evidence, 0.5)

        return round(completeness * evidence_mult, 3)

    def get_subject_history(self, subject_id: int) -> Dict:
        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                SELECT modality, COUNT(*), MAX(timestamp)
                FROM modality_features
                WHERE subject_id = %s
                GROUP BY modality
                ORDER BY MAX(timestamp) DESC
            """, (subject_id,))
            modalities = [{'modality': r[0], 'samples': r[1], 'latest': str(r[2])} for r in cur.fetchall()]

            cur.execute("""
                SELECT gile_g, gile_i, gile_l, gile_e, mood_score, health_score,
                       consciousness_level, tralse_confidence, updated_at
                FROM unified_profiles
                WHERE subject_id = %s
                ORDER BY updated_at DESC LIMIT 10
            """, (subject_id,))
            profiles = [{'gile': {'G': r[0], 'I': r[1], 'L': r[2], 'E': r[3]},
                        'mood': r[4], 'health': r[5], 'consciousness': r[6],
                        'confidence': r[7], 'timestamp': str(r[8])} for r in cur.fetchall()]

            return {'modalities': modalities, 'profile_history': profiles}
        finally:
            conn.close()

    def list_subjects(self) -> List[Dict]:
        conn = self._get_conn()
        try:
            cur = conn.cursor()
            cur.execute("""
                SELECT bs.id, bs.name, bs.external_id, bs.created_at,
                       COUNT(DISTINCT mf.modality) as modality_count
                FROM biometric_subjects bs
                LEFT JOIN modality_features mf ON bs.id = mf.subject_id
                GROUP BY bs.id, bs.name, bs.external_id, bs.created_at
                ORDER BY bs.created_at DESC
            """)
            return [{'id': r[0], 'name': r[1], 'external_id': r[2],
                    'created_at': str(r[3]), 'modality_count': r[4]} for r in cur.fetchall()]
        finally:
            conn.close()
