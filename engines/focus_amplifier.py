"""
FOCUS AMPLIFIER ENGINE
============================
Biometric-driven focus optimization system for ADHD management
and sustained attention training. Uses Polar H10 heart data via
Pulsoid to create a real-time focus feedback loop.

KEY INSIGHT: Focus is NOT one thing. Research identifies at least
three distinct attentional states, each with different physiological
signatures and optimal conditions:

1. CONCENTRATION (Focused Attention)
   - Narrow, sustained attention on a single object/task
   - Physiological signature: moderate-high sympathetic tone,
     stable HR, LOW HRV variability, beta-dominant EEG
   - Optimal LF/HF ratio: 2.0-4.0 (sympathetic-leaning)
   - Breathing: 5-6 breaths/min, equal inhale/exhale
   - Use case: studying, coding, writing, detail work
   - ADHD relevance: the "can't sit still and focus" problem

2. OPEN AWARENESS (Open Monitoring)
   - Broad, receptive attention without specific focus
   - Physiological signature: balanced autonomic tone,
     moderate HR, HIGH HRV, theta/alpha-dominant EEG
   - Optimal LF/HF ratio: 0.8-1.5 (balanced)
   - Breathing: 4-5 breaths/min, slightly extended exhale
   - Use case: brainstorming, creative ideation, meditation,
     noticing patterns, "big picture" thinking
   - ADHD relevance: the "scattered attention" can be CHANNELED

3. FLOW STATE
   - Effortless, absorbed engagement in challenging activity
   - Physiological signature: parasympathetic-leaning BUT with
     high engagement, VERY high HRV, alpha-theta crossover,
     reduced self-referential processing
   - Optimal LF/HF ratio: 1.0-2.0 (balanced to slight sympathetic)
   - Breathing: natural, unforced, rhythm emerges spontaneously
   - Use case: creative work, sports, performance, deep coding
   - ADHD relevance: ADHD brains excel at flow (hyperfocus)
   - Flow is NOT forced — it's INVITED by matching challenge to skill

MECHANISM:
    1. Baseline calibration (2 min resting HR + HRV)
    2. Mode-specific breathing and arousal optimization
    3. Real-time feedback on focus-relevant HRV markers
    4. Phase progression: Calibrate → Activate → Sustain → Deepen → (optional) Flow
    5. Session logging for attractor basin tracking over time

ADHD-SPECIFIC DESIGN:
    - Sessions are TIME-BOUNDED (30/60/90/custom minutes)
    - Visual timer creates urgency (ADHD responds to deadlines)
    - Progress tracking gives dopamine hits
    - Mode switching allowed (ADHD minds shift naturally)
    - No punishment for breaks — just gentle re-engagement prompts
    - Focus score is RELATIVE to personal baseline, not absolute

SCIENTIFIC BASIS:
    - Csikszentmihalyi: Flow requires challenge-skill balance
    - Lutz et al. (2008): FA vs OM meditation distinct neural signatures
    - Thayer & Lane: Neurovisceral integration model (HRV ↔ attention)
    - Yerkes-Dodson: Optimal arousal varies by task complexity
    - Kuo & Taylor: Nature exposure improves ADHD attention
    - Heart coherence: 0.1Hz resonance frequency entrainment
"""

import os
import time
import json
import math
import numpy as np
import requests
from datetime import datetime
from collections import deque
from typing import Dict, List, Tuple, Optional


class FocusPhysiologyAnalyzer:
    """
    Analyzes physiological signals for focus state detection and optimization.
    Different from sleep (parasympathetic surrender) and PSI (information exchange).
    Focus requires TASK-APPROPRIATE autonomic state maintenance.
    """

    def __init__(self):
        self.hr_series = deque(maxlen=1800)
        self.rr_series = deque(maxlen=1800)
        self.hrv_trend = deque(maxlen=120)
        self.hr_trend = deque(maxlen=120)
        self.focus_scores = deque(maxlen=120)
        self.baseline_hr = None
        self.baseline_rmssd = None
        self.baseline_lf_hf = None
        self._calibration_hrs = []
        self._calibration_rmssd = []
        self._calibration_lf_hf = []

    def add_heartbeat(self, hr: float, timestamp: float = None):
        ts = timestamp or time.time()
        self.hr_series.append((ts, hr))
        if hr > 0:
            rr = 60000.0 / hr
            self.rr_series.append((ts, rr))

    def compute_focus_hrv(self) -> Dict:
        if len(self.rr_series) < 10:
            return {
                'rmssd': 0, 'sdnn': 0, 'pnn50': 0,
                'hf_power': 0, 'lf_power': 0, 'lf_hf_ratio': 1.0,
                'hr_stability': 0, 'arousal_level': 0,
                'sufficient_data': False
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]

        diffs = np.diff(rr_vals)
        rmssd = float(np.sqrt(np.mean(diffs ** 2)))
        sdnn = float(np.std(rr_vals))
        pnn50 = float(np.sum(np.abs(diffs) > 50) / len(diffs) * 100)

        lf_power, hf_power, lf_hf = self._frequency_domain(rr_vals)

        recent_hr = list(self.hr_series)[-10:]
        if len(recent_hr) >= 5:
            hr_vals = [h for _, h in recent_hr]
            hr_stability = 1.0 - min(1.0, float(np.std(hr_vals)) / 10.0)
        else:
            hr_stability = 0.5

        avg_hr = sum(h for _, h in recent_hr) / len(recent_hr) if recent_hr else 70
        if avg_hr > 90:
            arousal_level = min(1.0, (avg_hr - 60) / 60.0)
        elif avg_hr > 70:
            arousal_level = (avg_hr - 60) / 60.0
        else:
            arousal_level = max(0.1, (avg_hr - 40) / 60.0)

        self.hrv_trend.append(rmssd)
        self.hr_trend.append(avg_hr)

        if self.baseline_hr is None and len(self._calibration_hrs) < 30:
            self._calibration_hrs.append(avg_hr)
            self._calibration_rmssd.append(rmssd)
            self._calibration_lf_hf.append(lf_hf)
            if len(self._calibration_hrs) >= 30:
                self.baseline_hr = float(np.mean(self._calibration_hrs))
                self.baseline_rmssd = float(np.mean(self._calibration_rmssd))
                self.baseline_lf_hf = float(np.mean(self._calibration_lf_hf))

        return {
            'rmssd': rmssd,
            'sdnn': sdnn,
            'pnn50': pnn50,
            'hf_power': hf_power,
            'lf_power': lf_power,
            'lf_hf_ratio': lf_hf,
            'hr_stability': hr_stability,
            'arousal_level': arousal_level,
            'current_hr': avg_hr,
            'sufficient_data': True
        }

    def _frequency_domain(self, rr_vals: List[float]) -> Tuple[float, float, float]:
        if len(rr_vals) < 20:
            return 0.0, 0.0, 1.0

        rr_ms = np.array(rr_vals)
        cumulative_time = np.cumsum(rr_ms) / 1000.0
        cumulative_time -= cumulative_time[0]

        resample_rate = 4.0
        t_uniform = np.arange(0, cumulative_time[-1], 1.0 / resample_rate)
        if len(t_uniform) < 16:
            return 0.0, 0.0, 1.0

        rr_uniform = np.interp(t_uniform, cumulative_time, rr_ms)
        rr_uniform -= np.mean(rr_uniform)

        n = len(rr_uniform)
        fft = np.fft.rfft(rr_uniform)
        power = np.abs(fft) ** 2
        freq = np.fft.rfftfreq(n, d=1.0 / resample_rate)

        lf_mask = (freq >= 0.04) & (freq < 0.15)
        hf_mask = (freq >= 0.15) & (freq < 0.40)

        lf_power = float(np.sum(power[lf_mask]))
        hf_power = float(np.sum(power[hf_mask]))

        lf_hf = lf_power / max(hf_power, 0.001)
        return lf_power, hf_power, lf_hf

    def compute_focus_coherence(self) -> Dict:
        if len(self.rr_series) < 30:
            return {
                'coherence': 0, 'coherence_pct': 0,
                'peak_frequency': 0, 'in_focus_band': False,
                'resonance_quality': 0
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]
        rr_ms = np.array(rr_vals)
        cumulative_time = np.cumsum(rr_ms) / 1000.0
        cumulative_time -= cumulative_time[0]

        resample_rate = 4.0
        t_uniform = np.arange(0, cumulative_time[-1], 1.0 / resample_rate)
        if len(t_uniform) < 16:
            return {
                'coherence': 0, 'coherence_pct': 0,
                'peak_frequency': 0, 'in_focus_band': False,
                'resonance_quality': 0
            }

        rr_uniform = np.interp(t_uniform, cumulative_time, rr_ms)
        rr_uniform -= np.mean(rr_uniform)

        n = len(rr_uniform)
        fft = np.fft.rfft(rr_uniform)
        power = np.abs(fft) ** 2
        freq = np.fft.rfftfreq(n, d=1.0 / resample_rate)

        focus_band = (freq >= 0.06) & (freq <= 0.14)
        broad_band = (freq >= 0.01) & (freq <= 0.40)

        focus_power = float(np.sum(power[focus_band]))
        broad_power = float(np.sum(power[broad_band]))

        coherence = focus_power / max(broad_power, 0.001)

        if np.any(focus_band):
            focus_freqs = freq[focus_band]
            focus_powers = power[focus_band]
            if len(focus_powers) > 0:
                peak_idx = np.argmax(focus_powers)
                peak_freq = float(focus_freqs[peak_idx])
            else:
                peak_freq = 0
        else:
            peak_freq = 0

        in_focus_band = 0.08 <= peak_freq <= 0.12
        resonance_quality = min(1.0, coherence * 1.5) if in_focus_band else min(0.5, coherence)

        return {
            'coherence': min(1.0, coherence),
            'coherence_pct': min(100.0, coherence * 100),
            'peak_frequency': peak_freq,
            'in_focus_band': in_focus_band,
            'resonance_quality': resonance_quality
        }

    def compute_focus_score(self, mode: str = 'concentration') -> Dict:
        hrv = self.compute_focus_hrv()
        coherence = self.compute_focus_coherence()

        if not hrv['sufficient_data']:
            return {
                'focus_score': 0, 'focus_pct': 0,
                'grade': 'CALIBRATING', 'mode': mode,
                'components': {}, 'in_zone': False,
                'recommendation': 'Calibrating... breathe normally'
            }

        if mode == 'concentration':
            score, components = self._score_concentration(hrv, coherence)
        elif mode == 'open_awareness':
            score, components = self._score_open_awareness(hrv, coherence)
        elif mode == 'flow':
            score, components = self._score_flow(hrv, coherence)
        else:
            score, components = self._score_concentration(hrv, coherence)

        self.focus_scores.append(score)

        if score > 0.8:
            grade = 'DEEP FOCUS'
        elif score > 0.65:
            grade = 'FOCUSED'
        elif score > 0.5:
            grade = 'BUILDING'
        elif score > 0.3:
            grade = 'WARMING UP'
        else:
            grade = 'SETTLING'

        return {
            'focus_score': score,
            'focus_pct': score * 100,
            'grade': grade,
            'mode': mode,
            'components': components,
            'in_zone': score > 0.6,
            'recommendation': self._focus_recommendation(mode, score, hrv, coherence)
        }

    def _score_concentration(self, hrv: Dict, coherence: Dict) -> Tuple[float, Dict]:
        stability_score = hrv['hr_stability']

        lf_hf = hrv['lf_hf_ratio']
        if 1.5 <= lf_hf <= 4.0:
            sympathetic_score = 1.0
        elif 1.0 <= lf_hf <= 6.0:
            sympathetic_score = 0.7
        else:
            sympathetic_score = 0.3

        coh_score = coherence['resonance_quality']

        arousal = hrv['arousal_level']
        if 0.4 <= arousal <= 0.7:
            arousal_score = 1.0
        elif 0.3 <= arousal <= 0.8:
            arousal_score = 0.7
        else:
            arousal_score = 0.4

        total = (
            stability_score * 0.30 +
            sympathetic_score * 0.25 +
            coh_score * 0.25 +
            arousal_score * 0.20
        )

        components = {
            'hr_stability': {'score': stability_score, 'weight': 0.30,
                           'label': 'Heart Rate Stability'},
            'sympathetic_tone': {'score': sympathetic_score, 'weight': 0.25,
                                'lf_hf': lf_hf, 'label': 'Activation Level'},
            'coherence': {'score': coh_score, 'weight': 0.25,
                        'pct': coherence['coherence_pct'], 'label': 'Heart Coherence'},
            'arousal': {'score': arousal_score, 'weight': 0.20,
                       'level': arousal, 'label': 'Arousal Zone'}
        }
        return min(1.0, total), components

    def _score_open_awareness(self, hrv: Dict, coherence: Dict) -> Tuple[float, Dict]:
        rmssd = hrv['rmssd']
        hrv_score = min(1.0, rmssd / 60.0)

        lf_hf = hrv['lf_hf_ratio']
        if 0.7 <= lf_hf <= 1.5:
            balance_score = 1.0
        elif 0.4 <= lf_hf <= 2.5:
            balance_score = 0.7
        else:
            balance_score = 0.3

        coh_score = coherence['resonance_quality']

        arousal = hrv['arousal_level']
        if 0.25 <= arousal <= 0.55:
            calm_score = 1.0
        elif 0.15 <= arousal <= 0.65:
            calm_score = 0.7
        else:
            calm_score = 0.4

        total = (
            hrv_score * 0.30 +
            balance_score * 0.25 +
            coh_score * 0.25 +
            calm_score * 0.20
        )

        components = {
            'hrv_flexibility': {'score': hrv_score, 'weight': 0.30,
                              'rmssd': rmssd, 'label': 'Heart Flexibility'},
            'autonomic_balance': {'score': balance_score, 'weight': 0.25,
                                 'lf_hf': lf_hf, 'label': 'Autonomic Balance'},
            'coherence': {'score': coh_score, 'weight': 0.25,
                        'pct': coherence['coherence_pct'], 'label': 'Heart Coherence'},
            'calm_alertness': {'score': calm_score, 'weight': 0.20,
                             'level': arousal, 'label': 'Calm Alertness'}
        }
        return min(1.0, total), components

    def _score_flow(self, hrv: Dict, coherence: Dict) -> Tuple[float, Dict]:
        rmssd = hrv['rmssd']
        hrv_score = min(1.0, rmssd / 50.0)

        lf_hf = hrv['lf_hf_ratio']
        if 0.8 <= lf_hf <= 2.5:
            balance_score = 1.0
        elif 0.5 <= lf_hf <= 3.5:
            balance_score = 0.7
        else:
            balance_score = 0.4

        coh_score = min(1.0, coherence['coherence'] * 1.3)

        stability = hrv['hr_stability']
        sustained = min(1.0, stability * 1.2)

        recent_scores = list(self.focus_scores)
        if len(recent_scores) >= 10:
            variance = float(np.std(recent_scores[-10:]))
            consistency = 1.0 - min(1.0, variance * 5)
        else:
            consistency = 0.5

        total = (
            hrv_score * 0.20 +
            balance_score * 0.20 +
            coh_score * 0.20 +
            sustained * 0.20 +
            consistency * 0.20
        )

        components = {
            'hrv_flexibility': {'score': hrv_score, 'weight': 0.20,
                              'rmssd': rmssd, 'label': 'Heart Flexibility'},
            'engagement_balance': {'score': balance_score, 'weight': 0.20,
                                  'lf_hf': lf_hf, 'label': 'Engagement Balance'},
            'coherence': {'score': coh_score, 'weight': 0.20,
                        'pct': coherence['coherence_pct'], 'label': 'Heart Coherence'},
            'sustained_absorption': {'score': sustained, 'weight': 0.20,
                                    'stability': stability, 'label': 'Absorption'},
            'flow_consistency': {'score': consistency, 'weight': 0.20,
                               'label': 'Flow Consistency'}
        }
        return min(1.0, total), components

    def _focus_recommendation(self, mode: str, score: float,
                              hrv: Dict, coherence: Dict) -> str:
        if score > 0.8:
            if mode == 'flow':
                return "You're in the zone. Don't change anything. Let it ride."
            elif mode == 'concentration':
                return "Deep focus achieved. Maintain steady breathing. You've got this."
            else:
                return "Beautiful open awareness. Stay receptive. Notice without grasping."

        if score > 0.6:
            if hrv['hr_stability'] < 0.5:
                return "Focus is building. Steady your breathing to stabilize heart rhythm."
            if coherence['resonance_quality'] < 0.4:
                return "Good progress. Try breathing at 5-6 breaths per minute for coherence."
            return "Almost there. Keep doing what you're doing."

        if score > 0.4:
            if mode == 'concentration':
                if hrv['arousal_level'] > 0.7:
                    return "Arousal is high. Take 3 slow breaths: 4 in, 6 out. Then return to task."
                elif hrv['arousal_level'] < 0.3:
                    return "Energy is low. Sit up straight. Take a few energizing breaths: 4 in, 2 out."
                return "Building focus. Minimize distractions. One thing at a time."
            elif mode == 'open_awareness':
                return "Soften your gaze. Don't chase thoughts. Let them come and go."
            else:
                return "Flow needs challenge-skill match. Is your task too easy or too hard?"

        if mode == 'concentration':
            return "Settling in. Start with 5 slow breaths: 4 in, 6 out. Then focus on one task."
        elif mode == 'open_awareness':
            return "Find a comfortable posture. Close your eyes. Notice sounds around you without judging."
        else:
            return "Flow takes time. Start with concentration first, then let go when engagement rises."

    def get_trend_data(self) -> Dict:
        hr_data = list(self.hr_trend)
        hrv_data = list(self.hrv_trend)
        focus_data = list(self.focus_scores)

        return {
            'hr_trend': hr_data,
            'hrv_trend': hrv_data,
            'focus_trend': focus_data,
            'avg_focus': float(np.mean(focus_data)) if focus_data else 0,
            'peak_focus': float(max(focus_data)) if focus_data else 0,
            'time_in_zone': sum(1 for s in focus_data if s > 0.6) / max(len(focus_data), 1) * 100
        }


FOCUS_MODES = {
    'concentration': {
        'name': 'Concentration',
        'icon': '🎯',
        'description': 'Narrow, sustained attention on a single task',
        'best_for': 'Studying, coding, writing, detail work',
        'adhd_tip': 'Set a specific task before starting. One thing only.',
        'breathing': {'inhale': 4, 'hold': 0, 'exhale': 6, 'pause': 2},
        'target_arousal': 'moderate-high',
        'target_lf_hf': '2.0-4.0',
    },
    'open_awareness': {
        'name': 'Open Awareness',
        'icon': '🌊',
        'description': 'Broad, receptive attention without specific focus',
        'best_for': 'Brainstorming, creative ideation, pattern recognition',
        'adhd_tip': 'Your scattered attention is a FEATURE here, not a bug.',
        'breathing': {'inhale': 4, 'hold': 0, 'exhale': 7, 'pause': 3},
        'target_arousal': 'low-moderate',
        'target_lf_hf': '0.8-1.5',
    },
    'flow': {
        'name': 'Flow State',
        'icon': '⚡',
        'description': 'Effortless, absorbed engagement in challenging activity',
        'best_for': 'Creative work, deep coding, performance, music',
        'adhd_tip': 'ADHD brains EXCEL at flow. Match challenge to skill level.',
        'breathing': {'inhale': 0, 'hold': 0, 'exhale': 0, 'pause': 0},
        'target_arousal': 'balanced',
        'target_lf_hf': '1.0-2.0',
    }
}


class FocusAmplifierProtocol:
    """
    The complete Focus Amplifier Protocol.

    Unlike Sleep (parasympathetic surrender) or PSI (information exchange),
    Focus optimizes for TASK-APPROPRIATE sustained autonomic state.

    The LCC principle applied: deep focus IS an attractor basin.
    ADHD creates shallow basins that are easily disrupted.
    This protocol DEEPENS the focus attractor basin over time.
    """

    PHASES = {
        1: {
            'name': 'CALIBRATE',
            'description': 'Establish personal baseline',
            'target_duration': 120,
            'guidance': 'Sit comfortably. Breathe normally for 2 minutes. '
                       'We are learning your personal baseline heart patterns.',
        },
        2: {
            'name': 'ACTIVATE',
            'description': 'Mode-specific arousal optimization',
            'target_duration': 180,
            'guidance': 'Follow the breathing pattern. We are tuning your '
                       'nervous system for the focus mode you selected.',
        },
        3: {
            'name': 'SUSTAIN',
            'description': 'Maintain focus state with biofeedback',
            'target_duration': 0,
            'guidance': 'Focus is engaged. Your heart data provides real-time '
                       'feedback. When focus dips, use the breathing cue.',
        },
        4: {
            'name': 'DEEPEN',
            'description': 'Strengthen the focus attractor basin',
            'target_duration': 0,
            'guidance': 'Excellent sustained focus. The attractor basin is deepening. '
                       'Each session makes the next one easier.',
        }
    }

    def __init__(self, pulsoid_token: str = None):
        self.token = pulsoid_token or os.environ.get('PULSOID_TOKEN')
        self.api_url = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"
        self.analyzer = FocusPhysiologyAnalyzer()

        self.current_phase = 0
        self.phase_start_time = None
        self.session_start_time = None
        self.session_active = False
        self.session_duration_target = 30 * 60
        self.focus_mode = 'concentration'

        self.phase_history = []
        self.session_log = []
        self.distraction_count = 0
        self.zone_entries = 0
        self.was_in_zone = False

        self.last_valid_hr = 0
        self.last_valid_time = None

    def start_session(self, mode: str = 'concentration',
                      duration_minutes: int = 30) -> Dict:
        if mode not in FOCUS_MODES:
            mode = 'concentration'

        self.session_active = True
        self.session_start_time = time.time()
        self.current_phase = 1
        self.phase_start_time = time.time()
        self.phase_history = []
        self.session_log = []
        self.focus_mode = mode
        self.session_duration_target = duration_minutes * 60
        self.distraction_count = 0
        self.zone_entries = 0
        self.was_in_zone = False
        self.analyzer = FocusPhysiologyAnalyzer()

        mode_info = FOCUS_MODES[mode]
        return {
            'status': 'SESSION_STARTED',
            'phase': 1,
            'phase_name': 'CALIBRATE',
            'mode': mode,
            'mode_name': mode_info['name'],
            'duration_minutes': duration_minutes,
            'message': f"Focus Amplifier started in {mode_info['name']} mode. "
                      f"{mode_info['adhd_tip']}",
            'breathing': mode_info['breathing'],
            'timestamp': datetime.now().isoformat()
        }

    def stop_session(self) -> Dict:
        self.session_active = False
        duration = time.time() - self.session_start_time if self.session_start_time else 0

        trends = self.analyzer.get_trend_data()

        summary = {
            'status': 'SESSION_ENDED',
            'mode': self.focus_mode,
            'duration_minutes': duration / 60,
            'phases_completed': max(0, self.current_phase - 1),
            'avg_focus_score': trends['avg_focus'],
            'peak_focus_score': trends['peak_focus'],
            'time_in_zone_pct': trends['time_in_zone'],
            'zone_entries': self.zone_entries,
            'distraction_count': self.distraction_count,
            'phase_history': self.phase_history,
            'timestamp': datetime.now().isoformat()
        }

        self._save_session(summary)
        return summary

    def read_heart(self) -> Dict:
        if not self.token:
            return {'hr': 0, 'connected': False}

        try:
            headers = {"Authorization": f"Bearer {self.token}"}
            response = requests.get(self.api_url, headers=headers, timeout=5)
            if response.status_code == 200:
                data = response.json()
                hr = data.get('data', {}).get('heart_rate', 0)
                if hr > 0:
                    self.analyzer.add_heartbeat(hr)
                    self.last_valid_hr = hr
                    self.last_valid_time = time.time()
                return {'hr': hr if hr > 0 else self.last_valid_hr, 'connected': True}
        except:
            pass

        if self.last_valid_hr > 0 and self.last_valid_time:
            if time.time() - self.last_valid_time < 30:
                return {'hr': self.last_valid_hr, 'connected': True}
        return {'hr': 0, 'connected': False}

    def get_focus_state(self) -> Dict:
        heart = self.read_heart()
        hrv = self.analyzer.compute_focus_hrv()
        coherence = self.analyzer.compute_focus_coherence()
        focus = self.analyzer.compute_focus_score(self.focus_mode)

        phase_info = self.PHASES.get(self.current_phase, self.PHASES[1])
        phase_elapsed = time.time() - self.phase_start_time if self.phase_start_time else 0
        session_elapsed = time.time() - self.session_start_time if self.session_start_time else 0
        session_remaining = max(0, self.session_duration_target - session_elapsed)

        if focus['in_zone'] and not self.was_in_zone:
            self.zone_entries += 1
        elif not focus['in_zone'] and self.was_in_zone:
            self.distraction_count += 1
        self.was_in_zone = focus['in_zone']

        self._check_phase_advancement(hrv, coherence, focus, phase_elapsed)

        mode_info = FOCUS_MODES[self.focus_mode]

        trends = self.analyzer.get_trend_data()

        state = {
            'heart': heart,
            'hrv': hrv,
            'coherence': coherence,
            'focus': focus,
            'trends': trends,
            'phase': {
                'number': self.current_phase,
                'name': self.PHASES[self.current_phase]['name'],
                'description': self.PHASES[self.current_phase]['description'],
                'elapsed': phase_elapsed,
                'guidance': self._get_phase_guidance(focus),
            },
            'session': {
                'elapsed': session_elapsed,
                'elapsed_minutes': session_elapsed / 60,
                'remaining': session_remaining,
                'remaining_minutes': session_remaining / 60,
                'target_minutes': self.session_duration_target / 60,
                'progress_pct': min(100, session_elapsed / max(self.session_duration_target, 1) * 100),
                'mode': self.focus_mode,
                'mode_info': mode_info,
                'zone_entries': self.zone_entries,
                'distraction_count': self.distraction_count,
                'active': self.session_active
            },
            'breathing': mode_info['breathing'] if self.current_phase <= 2 else
                        {'inhale': 0, 'hold': 0, 'exhale': 0, 'pause': 0},
        }

        self.session_log.append({
            'timestamp': time.time(),
            'hr': heart['hr'],
            'focus_score': focus['focus_score'],
            'phase': self.current_phase,
            'in_zone': focus['in_zone']
        })

        return state

    def _check_phase_advancement(self, hrv: Dict, coherence: Dict,
                                  focus: Dict, phase_elapsed: float):
        if self.current_phase == 1 and phase_elapsed >= 120:
            if self.analyzer.baseline_hr is not None:
                self._advance_phase()
            elif phase_elapsed >= 180:
                self._advance_phase()

        elif self.current_phase == 2 and phase_elapsed >= 120:
            if focus['focus_score'] > 0.4:
                self._advance_phase()
            elif phase_elapsed >= 300:
                self._advance_phase()

        elif self.current_phase == 3:
            recent_scores = list(self.analyzer.focus_scores)
            if len(recent_scores) >= 20:
                avg_recent = float(np.mean(recent_scores[-20:]))
                if avg_recent > 0.7:
                    self._advance_phase()

    def _advance_phase(self):
        if self.current_phase < 4:
            self.phase_history.append({
                'phase': self.current_phase,
                'name': self.PHASES[self.current_phase]['name'],
                'duration': time.time() - self.phase_start_time,
                'timestamp': datetime.now().isoformat()
            })
            self.current_phase += 1
            self.phase_start_time = time.time()

    def _get_phase_guidance(self, focus: Dict) -> str:
        base = self.PHASES[self.current_phase]['guidance']
        if self.current_phase >= 3:
            return focus['recommendation']
        return base

    def switch_mode(self, new_mode: str) -> Dict:
        if new_mode in FOCUS_MODES:
            old_mode = self.focus_mode
            self.focus_mode = new_mode
            mode_info = FOCUS_MODES[new_mode]
            return {
                'status': 'MODE_SWITCHED',
                'old_mode': old_mode,
                'new_mode': new_mode,
                'message': f"Switched to {mode_info['name']}. {mode_info['adhd_tip']}",
                'breathing': mode_info['breathing']
            }
        return {'status': 'INVALID_MODE', 'message': f'Unknown mode: {new_mode}'}

    def _save_session(self, summary: Dict):
        try:
            log_dir = "focus_sessions"
            os.makedirs(log_dir, exist_ok=True)
            filename = f"{log_dir}/focus_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
            with open(filename, 'w') as f:
                json.dump(summary, f, indent=2, default=str)
        except:
            pass

    def get_session_history(self) -> List[Dict]:
        try:
            log_dir = "focus_sessions"
            if not os.path.exists(log_dir):
                return []
            sessions = []
            for fname in sorted(os.listdir(log_dir), reverse=True)[:20]:
                if fname.endswith('.json'):
                    with open(os.path.join(log_dir, fname)) as f:
                        sessions.append(json.load(f))
            return sessions
        except:
            return []
