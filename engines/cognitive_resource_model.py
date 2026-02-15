"""
COGNITIVE RESOURCE MODEL ENGINE
================================
Models the inverted Yerkes-Dodson relationship observed in high-NFC
(Need for Cognition) individuals, particularly those with ADHD.

THE WOOD-ON-FIRE HYPOTHESIS:
Standard Yerkes-Dodson assumes cognitive performance peaks at moderate
arousal and degrades at high arousal due to working memory overload.
But this model breaks down when:

1. COGNITIVE RESOURCES are large enough to absorb high arousal
   - Like a roaring fire that consumes any wood thrown on it
   - The "overwhelm threshold" is pushed higher or eliminated entirely

2. NEED FOR COGNITION (NFC) is a trait, not just a state
   - High-NFC individuals experience cognitive load as FUEL, not burden
   - What others experience as stressful complexity becomes energizing

3. ADHD PARADOX: ADHD brains often perform BEST under high stimulation
   - Understimulation → boredom → poor performance
   - High stimulation → engagement → peak performance
   - The curve isn't just shifted right — it's INVERTED

THE MODEL:
Standard Yerkes-Dodson: performance = -a(arousal - optimal)^2 + peak
Inverted (High-NFC):    performance = b * arousal^c * nfc_factor

Where:
- b = cognitive resource coefficient (individual capacity)
- c = NFC exponent (how much arousal helps vs hurts)
- nfc_factor = trait need-for-cognition modifier

The model tracks biometric data across sessions to empirically measure:
- At what arousal levels does this person perform best?
- Does performance degrade at high arousal or keep climbing?
- What is their effective NFC profile?
- How do cognitive resources change over time (training effect)?

INTEGRATION WITH FOCUS AMPLIFIER:
The Focus Amplifier provides real-time arousal and performance data.
This engine aggregates that data to build a personal cognitive profile
that either confirms or challenges Yerkes-Dodson for this individual.
"""

import os
import json
import math
import time
import numpy as np
import psycopg2
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
from collections import deque


class CognitiveResourceModel:
    """
    Models individual cognitive resource capacity and maps the
    arousal-performance relationship, testing whether the standard
    Yerkes-Dodson curve applies or an inverted pattern emerges.
    """

    YERKES_DODSON_STANDARD = 'standard'
    YERKES_DODSON_SHIFTED = 'shifted_right'
    YERKES_DODSON_INVERTED = 'inverted'
    YERKES_DODSON_PLATEAU = 'high_plateau'

    NFC_LEVELS = {
        'low': {'label': 'Low NFC', 'multiplier': 0.7, 'description': 'Prefers simple, low-effort tasks'},
        'moderate': {'label': 'Moderate NFC', 'multiplier': 1.0, 'description': 'Standard cognitive engagement'},
        'high': {'label': 'High NFC', 'multiplier': 1.3, 'description': 'Seeks complex problems, enjoys effort'},
        'exceptional': {'label': 'Exceptional NFC', 'multiplier': 1.6, 'description': 'Thrives on maximum complexity'}
    }

    def __init__(self):
        self.observations = []
        self.arousal_performance_pairs = deque(maxlen=500)
        self.session_data = []
        self.profile = {
            'curve_type': None,
            'nfc_level': None,
            'cognitive_capacity': 0.5,
            'optimal_arousal': 0.5,
            'peak_performance_arousal': None,
            'resource_coefficient': 1.0,
            'sessions_analyzed': 0,
            'last_updated': None
        }
        self._load_from_db()

    def _get_db_connection(self):
        try:
            return psycopg2.connect(os.environ.get('DATABASE_URL', ''))
        except Exception:
            return None

    def _load_from_db(self):
        conn = self._get_db_connection()
        if not conn:
            return
        try:
            cur = conn.cursor()
            cur.execute("""
                SELECT arousal_level, performance_score, nfc_state, focus_mode,
                       hr, hrv_rmssd, lf_hf_ratio, coherence, session_id, created_at
                FROM cognitive_resource_observations
                ORDER BY created_at ASC LIMIT 500
            """)
            rows = cur.fetchall()
            for row in rows:
                self.observations.append({
                    'arousal': row[0], 'performance': row[1],
                    'nfc_state': row[2], 'focus_mode': row[3],
                    'hr': row[4], 'hrv_rmssd': row[5],
                    'lf_hf_ratio': row[6], 'coherence': row[7],
                    'session_id': row[8],
                    'timestamp': row[9].isoformat() if row[9] else None
                })
                self.arousal_performance_pairs.append((row[0], row[1]))

            cur.execute("""
                SELECT profile_data FROM cognitive_resource_profiles
                ORDER BY updated_at DESC LIMIT 1
            """)
            profile_row = cur.fetchone()
            if profile_row and profile_row[0]:
                saved = json.loads(profile_row[0]) if isinstance(profile_row[0], str) else profile_row[0]
                self.profile.update(saved)

            cur.close()
            conn.close()
        except Exception:
            try:
                conn.close()
            except Exception:
                pass

    def record_observation(self, arousal: float, performance: float,
                           nfc_state: str = 'high', focus_mode: str = '',
                           hr: float = 0, hrv_rmssd: float = 0,
                           lf_hf_ratio: float = 0, coherence: float = 0,
                           session_id: str = '') -> Dict:
        obs = {
            'arousal': max(0, min(1, arousal)),
            'performance': max(0, min(1, performance)),
            'nfc_state': nfc_state,
            'focus_mode': focus_mode,
            'hr': hr,
            'hrv_rmssd': hrv_rmssd,
            'lf_hf_ratio': lf_hf_ratio,
            'coherence': coherence,
            'session_id': session_id,
            'timestamp': datetime.now().isoformat()
        }
        self.observations.append(obs)
        self.arousal_performance_pairs.append((obs['arousal'], obs['performance']))

        conn = self._get_db_connection()
        if conn:
            try:
                cur = conn.cursor()
                cur.execute("""
                    INSERT INTO cognitive_resource_observations
                    (arousal_level, performance_score, nfc_state, focus_mode,
                     hr, hrv_rmssd, lf_hf_ratio, coherence, session_id)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                """, (obs['arousal'], obs['performance'], nfc_state,
                      focus_mode, hr, hrv_rmssd, lf_hf_ratio, coherence, session_id))
                conn.commit()
                cur.close()
                conn.close()
            except Exception:
                try:
                    conn.close()
                except Exception:
                    pass

        return obs

    def analyze_curve(self) -> Dict:
        pairs = list(self.arousal_performance_pairs)
        if len(pairs) < 10:
            return {
                'curve_type': 'insufficient_data',
                'confidence': 0,
                'description': f'Need at least 10 data points (have {len(pairs)})',
                'optimal_arousal': 0.5,
                'model_params': {},
                'evidence_against_yd': 0,
                'data_points': len(pairs)
            }

        arousals = np.array([p[0] for p in pairs])
        performances = np.array([p[1] for p in pairs])

        n_bins = 5
        bin_edges = np.linspace(0, 1, n_bins + 1)
        bin_means = []
        bin_centers = []
        bin_counts = []

        for i in range(n_bins):
            mask = (arousals >= bin_edges[i]) & (arousals < bin_edges[i+1])
            if i == n_bins - 1:
                mask = (arousals >= bin_edges[i]) & (arousals <= bin_edges[i+1])
            if np.sum(mask) > 0:
                bin_means.append(float(np.mean(performances[mask])))
                bin_centers.append(float((bin_edges[i] + bin_edges[i+1]) / 2))
                bin_counts.append(int(np.sum(mask)))

        if len(bin_means) < 3:
            return {
                'curve_type': 'insufficient_spread',
                'confidence': 0,
                'description': 'Need data across more arousal levels',
                'optimal_arousal': 0.5,
                'model_params': {},
                'evidence_against_yd': 0,
                'data_points': len(pairs)
            }

        bm = np.array(bin_means)
        bc = np.array(bin_centers)

        correlation = float(np.corrcoef(arousals, performances)[0, 1])

        high_mask = arousals >= 0.7
        low_mask = arousals <= 0.3
        mid_mask = (arousals > 0.3) & (arousals < 0.7)

        high_perf = float(np.mean(performances[high_mask])) if np.sum(high_mask) > 0 else 0
        low_perf = float(np.mean(performances[low_mask])) if np.sum(low_mask) > 0 else 0
        mid_perf = float(np.mean(performances[mid_mask])) if np.sum(mid_mask) > 0 else 0

        if correlation > 0.3 and high_perf > mid_perf:
            curve_type = self.YERKES_DODSON_INVERTED
            description = ("INVERTED Yerkes-Dodson: Performance INCREASES with arousal! "
                          "Your cognitive resources are large enough to absorb high arousal. "
                          "Like wood on a roaring fire — more fuel, brighter flame.")
            evidence_against_yd = min(1.0, max(0, correlation) + max(0, high_perf - mid_perf))
            optimal_arousal = float(bc[np.argmax(bm)])

        elif high_perf >= mid_perf * 0.9 and high_perf > low_perf:
            curve_type = self.YERKES_DODSON_PLATEAU
            description = ("HIGH PLATEAU: Performance stays high even at peak arousal. "
                          "Standard Yerkes-Dodson predicts decline, but you maintain. "
                          "Suggests high cognitive capacity buffer.")
            evidence_against_yd = min(1.0, 0.5 + max(0, high_perf - low_perf) * 0.5)
            optimal_arousal = float(bc[np.argmax(bm)])

        elif mid_perf > high_perf and mid_perf > low_perf:
            if np.argmax(bm) >= len(bm) - 2:
                curve_type = self.YERKES_DODSON_SHIFTED
                description = ("SHIFTED RIGHT: Your optimal arousal is higher than average. "
                              "Standard curve applies but peak is shifted to higher arousal.")
                evidence_against_yd = 0.3
            else:
                curve_type = self.YERKES_DODSON_STANDARD
                description = ("STANDARD Yerkes-Dodson: Performance peaks at moderate arousal. "
                              "This is the textbook pattern.")
                evidence_against_yd = 0.0
            optimal_arousal = float(bc[np.argmax(bm)])

        else:
            curve_type = self.YERKES_DODSON_SHIFTED
            description = "Pattern doesn't clearly match standard models. More data needed."
            evidence_against_yd = 0.2
            optimal_arousal = float(bc[np.argmax(bm)])

        confidence = min(1.0, len(pairs) / 100.0)

        self.profile.update({
            'curve_type': curve_type,
            'optimal_arousal': optimal_arousal,
            'peak_performance_arousal': optimal_arousal,
            'sessions_analyzed': len(pairs),
            'last_updated': datetime.now().isoformat()
        })

        self._save_profile()

        return {
            'curve_type': curve_type,
            'confidence': confidence,
            'description': description,
            'optimal_arousal': optimal_arousal,
            'correlation': correlation,
            'high_arousal_performance': high_perf,
            'mid_arousal_performance': mid_perf,
            'low_arousal_performance': low_perf,
            'model_params': {
                'bin_centers': bin_centers,
                'bin_means': bin_means,
                'bin_counts': bin_counts
            },
            'evidence_against_yd': evidence_against_yd,
            'data_points': len(pairs)
        }

    def estimate_nfc_level(self) -> Dict:
        if len(self.observations) < 5:
            return {
                'nfc_level': 'unknown',
                'confidence': 0,
                'indicators': {},
                'description': 'Need more observations'
            }

        high_arousal_obs = [o for o in self.observations if o['arousal'] >= 0.7]
        high_perf_at_high_arousal = np.mean([o['performance'] for o in high_arousal_obs]) if high_arousal_obs else 0

        all_perfs = [o['performance'] for o in self.observations]
        perf_variance = float(np.std(all_perfs))
        perf_mean = float(np.mean(all_perfs))

        arousal_preference = np.mean([o['arousal'] for o in self.observations])

        complex_modes = ['excited_concentration', 'excited_flow', 'excited_open_awareness']
        complex_obs = [o for o in self.observations if o.get('focus_mode', '') in complex_modes]
        complex_perf = np.mean([o['performance'] for o in complex_obs]) if complex_obs else 0

        nfc_score = 0.0
        nfc_score += min(0.3, high_perf_at_high_arousal * 0.3)
        nfc_score += min(0.2, arousal_preference * 0.2)
        nfc_score += min(0.2, complex_perf * 0.2)
        nfc_score += min(0.15, (1.0 - min(1.0, perf_variance * 3)) * 0.15)
        nfc_score += min(0.15, perf_mean * 0.15)

        if nfc_score >= 0.7:
            nfc_level = 'exceptional'
        elif nfc_score >= 0.5:
            nfc_level = 'high'
        elif nfc_score >= 0.3:
            nfc_level = 'moderate'
        else:
            nfc_level = 'low'

        self.profile['nfc_level'] = nfc_level
        self._save_profile()

        return {
            'nfc_level': nfc_level,
            'nfc_score': nfc_score,
            'confidence': min(1.0, len(self.observations) / 50.0),
            'indicators': {
                'high_arousal_performance': high_perf_at_high_arousal,
                'arousal_preference': float(arousal_preference),
                'complex_mode_performance': float(complex_perf),
                'performance_consistency': 1.0 - min(1.0, perf_variance * 3),
                'overall_performance': perf_mean
            },
            'level_info': self.NFC_LEVELS.get(nfc_level, {}),
            'description': self.NFC_LEVELS.get(nfc_level, {}).get('description', '')
        }

    def compute_cognitive_capacity(self) -> Dict:
        if len(self.observations) < 5:
            return {
                'capacity': 0.5,
                'capacity_label': 'Unknown',
                'fire_size': 'unknown',
                'wood_threshold': 0.5,
                'description': 'Need more data to estimate capacity'
            }

        performances = np.array([o['performance'] for o in self.observations])
        arousals = np.array([o['arousal'] for o in self.observations])

        peak_perf = float(np.percentile(performances, 90))
        sustained_perf = float(np.mean(performances[-20:])) if len(performances) >= 20 else float(np.mean(performances))
        high_arousal_perf = float(np.mean(performances[arousals >= 0.7])) if np.sum(arousals >= 0.7) > 2 else 0

        capacity = (peak_perf * 0.35 + sustained_perf * 0.35 + high_arousal_perf * 0.30)

        if capacity >= 0.8:
            label = 'Roaring Bonfire'
            fire_size = 'bonfire'
            description = ('Your cognitive fire is massive — it consumes any amount of fuel. '
                         'High arousal only makes you sharper.')
        elif capacity >= 0.65:
            label = 'Strong Campfire'
            fire_size = 'campfire'
            description = ('Your cognitive fire is strong — it handles heavy fuel well. '
                         'You perform well even under high stimulation.')
        elif capacity >= 0.45:
            label = 'Steady Flame'
            fire_size = 'flame'
            description = ('Your cognitive fire is steady — moderate fuel is optimal. '
                         'High arousal may sometimes overwhelm.')
        else:
            label = 'Candle'
            fire_size = 'candle'
            description = ('Your cognitive fire prefers gentle fuel — '
                         'calm environments help you perform best.')

        wood_threshold = 1.0 if capacity >= 0.8 else capacity + 0.2

        self.profile.update({
            'cognitive_capacity': capacity,
            'resource_coefficient': capacity * 1.5
        })
        self._save_profile()

        return {
            'capacity': capacity,
            'capacity_pct': capacity * 100,
            'capacity_label': label,
            'fire_size': fire_size,
            'wood_threshold': wood_threshold,
            'peak_performance': peak_perf,
            'sustained_performance': sustained_perf,
            'high_arousal_resilience': high_arousal_perf,
            'description': description
        }

    def predict_performance(self, arousal: float, nfc_state: str = 'high') -> Dict:
        curve = self.analyze_curve()
        nfc = self.estimate_nfc_level()
        capacity = self.compute_cognitive_capacity()

        nfc_mult = self.NFC_LEVELS.get(nfc.get('nfc_level', 'moderate'), {}).get('multiplier', 1.0)

        if curve['curve_type'] == self.YERKES_DODSON_INVERTED:
            base = 0.3 + 0.6 * arousal ** 0.7
        elif curve['curve_type'] == self.YERKES_DODSON_PLATEAU:
            if arousal <= curve['optimal_arousal']:
                base = 0.3 + 0.6 * (arousal / max(curve['optimal_arousal'], 0.01))
            else:
                base = 0.9
        elif curve['curve_type'] == self.YERKES_DODSON_SHIFTED:
            opt = curve['optimal_arousal']
            base = max(0.2, 0.9 - 1.5 * (arousal - opt) ** 2)
        else:
            base = max(0.2, 0.9 - 2.0 * (arousal - 0.5) ** 2)

        predicted = min(1.0, base * nfc_mult * capacity['capacity'])

        return {
            'predicted_performance': predicted,
            'predicted_pct': predicted * 100,
            'arousal_input': arousal,
            'curve_type': curve['curve_type'],
            'nfc_level': nfc.get('nfc_level', 'unknown'),
            'capacity': capacity['capacity'],
            'fire_metaphor': capacity['fire_size'],
            'model_used': 'inverted' if curve['curve_type'] == self.YERKES_DODSON_INVERTED else 'standard'
        }

    def generate_yerkes_dodson_comparison(self) -> Dict:
        arousal_range = np.linspace(0, 1, 50)

        standard = [float(max(0.1, 0.9 - 2.0 * (a - 0.5) ** 2)) for a in arousal_range]

        curve = self.analyze_curve()
        if curve['curve_type'] == self.YERKES_DODSON_INVERTED:
            personal = [float(0.3 + 0.6 * a ** 0.7) for a in arousal_range]
        elif curve['curve_type'] == self.YERKES_DODSON_PLATEAU:
            opt = curve['optimal_arousal']
            personal = []
            for a in arousal_range:
                if a <= opt:
                    personal.append(float(0.3 + 0.6 * (a / max(opt, 0.01))))
                else:
                    personal.append(0.9)
        elif curve['curve_type'] == self.YERKES_DODSON_SHIFTED:
            opt = curve['optimal_arousal']
            personal = [float(max(0.2, 0.9 - 1.5 * (a - opt) ** 2)) for a in arousal_range]
        else:
            personal = standard.copy()

        pairs = list(self.arousal_performance_pairs)
        actual_arousal = [p[0] for p in pairs]
        actual_performance = [p[1] for p in pairs]

        return {
            'arousal_range': arousal_range.tolist(),
            'standard_yd': standard,
            'personal_curve': personal,
            'actual_arousal': actual_arousal,
            'actual_performance': actual_performance,
            'curve_type': curve['curve_type'],
            'curve_description': curve.get('description', ''),
            'evidence_against_yd': curve.get('evidence_against_yd', 0)
        }

    def get_session_summary(self) -> Dict:
        curve = self.analyze_curve()
        nfc = self.estimate_nfc_level()
        capacity = self.compute_cognitive_capacity()

        return {
            'profile': self.profile,
            'curve_analysis': curve,
            'nfc_analysis': nfc,
            'capacity_analysis': capacity,
            'total_observations': len(self.observations),
            'wood_on_fire_verdict': self._wood_on_fire_verdict(curve, nfc, capacity)
        }

    def _wood_on_fire_verdict(self, curve: Dict, nfc: Dict, capacity: Dict) -> Dict:
        evidence = curve.get('evidence_against_yd', 0)
        nfc_level = nfc.get('nfc_level', 'unknown')
        fire_size = capacity.get('fire_size', 'unknown')

        if evidence >= 0.7 and nfc_level in ('high', 'exceptional') and fire_size in ('bonfire', 'campfire'):
            verdict = 'CONFIRMED'
            explanation = (
                "The Wood-on-Fire hypothesis is CONFIRMED by your data. "
                "Your cognitive performance increases with arousal rather than following "
                "the standard inverted-U curve. Your high Need for Cognition and large "
                "cognitive resource capacity mean that what overwhelms others fuels you. "
                "The fire burns ever brighter!"
            )
        elif evidence >= 0.4:
            verdict = 'SUPPORTED'
            explanation = (
                "Your data SUPPORTS the Wood-on-Fire hypothesis. "
                "You show above-average resilience to high arousal, though the pattern "
                "isn't fully inverted yet. More sessions at high intensity will strengthen "
                "the evidence."
            )
        elif len(self.observations) < 20:
            verdict = 'TESTING'
            explanation = (
                "Still gathering evidence. Complete more Focus Amplifier sessions — "
                "especially in excited modes — to build your cognitive profile."
            )
        else:
            verdict = 'STANDARD'
            explanation = (
                "Your data follows the standard Yerkes-Dodson pattern. "
                "Performance peaks at moderate arousal."
            )

        return {
            'verdict': verdict,
            'explanation': explanation,
            'evidence_score': evidence,
            'nfc_contribution': nfc_level,
            'capacity_contribution': fire_size
        }

    def _save_profile(self):
        conn = self._get_db_connection()
        if not conn:
            return
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO cognitive_resource_profiles (profile_data, updated_at)
                VALUES (%s, NOW())
            """, (json.dumps(self.profile),))
            conn.commit()
            cur.close()
            conn.close()
        except Exception:
            try:
                conn.close()
            except Exception:
                pass

    def get_fire_visualization_data(self) -> Dict:
        capacity = self.compute_cognitive_capacity()
        cap = capacity['capacity']

        if cap >= 0.8:
            flames = 5
            color = '#FF4500'
            glow = '#FFD700'
            intensity = 'Maximum'
        elif cap >= 0.65:
            flames = 4
            color = '#FF6B00'
            glow = '#FFA500'
            intensity = 'High'
        elif cap >= 0.45:
            flames = 3
            color = '#FF8C00'
            glow = '#FFB84D'
            intensity = 'Moderate'
        else:
            flames = 2
            color = '#FFA500'
            glow = '#FFD699'
            intensity = 'Building'

        return {
            'flames': flames,
            'color': color,
            'glow_color': glow,
            'intensity': intensity,
            'capacity': cap,
            'fire_size': capacity['fire_size'],
            'label': capacity['capacity_label']
        }
