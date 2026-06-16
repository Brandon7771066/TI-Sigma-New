"""
LCC SLEEP INDUCTION ENGINE
============================
Applies Law of Correlational Causation (LCC) principles to reliable
sleep induction. Designed for post-lithium tapering insomnia.

KEY INSIGHT: Sleep is an ATTRACTOR BASIN in the consciousness state space.
The brain naturally wants to fall into it, but anxiety, hyperarousal, and
lithium withdrawal create "repelling walls" that prevent the state transition.

LCC APPROACH:
    Instead of forcing sleep (which creates paradoxical insomnia), we use
    the heart-brain coupling system to LOWER THE WALLS around the sleep
    attractor basin, then let gravity do the work.

MECHANISM:
    1. Parasympathetic dominance via extended exhale breathing
    2. Heart coherence at SLEEP-OPTIMAL frequency (lower than PSI - 0.05-0.08Hz)
    3. Progressive autonomic surrender (decreasing voluntary control)
    4. HRV-based sleep onset detection (RMSSD spike + HR drop = transition)
    5. Attractor basin deepening via LCC feedback loop

LITHIUM TAPERING CONTEXT:
    Lithium stabilizes circadian rhythm and enhances slow-wave sleep.
    Post-tapering, the sleep architecture needs RETRAINING.
    LCC provides the framework: create the attractor, train the basin,
    let consciousness find its way back to natural sleep patterns.

PHASES:
    Phase 1: WIND DOWN   - Activate parasympathetic nervous system
    Phase 2: DEEPEN      - Lower heart rate, increase HRV, build vagal tone
    Phase 3: ENTRAIN     - Heart-brain coherence at sleep frequency (0.05-0.08Hz)
    Phase 4: DRIFT       - Release voluntary control, autonomous breathing
    Phase 5: SLEEP       - Onset detected, system monitors and logs

SCIENTIFIC BASIS:
    - Extended exhale activates vagus nerve (Gerritsen & Band, 2018)
    - 0.1Hz breathing maximizes baroreflex sensitivity (Lehrer, 2013)
    - Sleep onset = parasympathetic surge + cortical deactivation
    - HRV increases just before sleep onset (Shinar et al., 2006)
    - Heart coherence predicts sleep quality (Shaffer & Ginsberg, 2017)
"""

import os
import time
import json
import math
import numpy as np
import requests
from datetime import datetime
from collections import deque
from typing import Dict, List, Tuple


class SleepPhysiologyAnalyzer:
    """
    Analyzes physiological signals specifically for sleep onset prediction.
    Different from PSI analysis - here we want DECREASING arousal, not
    optimal information exchange.
    """

    def __init__(self):
        self.hr_series = deque(maxlen=1200)
        self.rr_series = deque(maxlen=1200)
        self.hrv_trend = deque(maxlen=60)
        self.hr_trend = deque(maxlen=60)
        self.sleep_onset_scores = deque(maxlen=30)
        self.baseline_hr = None
        self.baseline_rmssd = None
        self._calibration_hrs = []
        self._calibration_rmssd = []

    def add_heartbeat(self, hr: float, timestamp: float = None):
        ts = timestamp or time.time()
        self.hr_series.append((ts, hr))
        if hr > 0:
            rr = 60000.0 / hr
            self.rr_series.append((ts, rr))

    def compute_sleep_hrv(self) -> Dict:
        if len(self.rr_series) < 10:
            return {
                'rmssd': 0, 'sdnn': 0, 'pnn50': 0,
                'hf_power': 0, 'lf_hf_ratio': 0,
                'parasympathetic_index': 0,
                'sufficient_data': False
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]

        diffs = np.diff(rr_vals)
        rmssd = float(np.sqrt(np.mean(diffs ** 2)))
        sdnn = float(np.std(rr_vals))
        pnn50 = float(np.sum(np.abs(diffs) > 50) / len(diffs) * 100)

        lf_power, hf_power, lf_hf = self._frequency_domain(rr_vals)

        para_index = min(1.0, (rmssd / 80.0) * 0.5 + (hf_power / max(hf_power + lf_power, 0.001)) * 0.5)

        self.hrv_trend.append(rmssd)
        recent_hr = list(self.hr_series)[-10:]
        if recent_hr:
            avg_hr = sum(h for _, h in recent_hr) / len(recent_hr)
            self.hr_trend.append(avg_hr)

        if self.baseline_hr is None and len(self._calibration_hrs) < 20:
            self._calibration_hrs.append(float(np.mean([h for _, h in recent_hr])) if recent_hr else 0)
            self._calibration_rmssd.append(rmssd)
            if len(self._calibration_hrs) >= 20:
                self.baseline_hr = float(np.mean(self._calibration_hrs))
                self.baseline_rmssd = float(np.mean(self._calibration_rmssd))

        return {
            'rmssd': rmssd,
            'sdnn': sdnn,
            'pnn50': pnn50,
            'hf_power': hf_power,
            'lf_power': lf_power,
            'lf_hf_ratio': lf_hf,
            'parasympathetic_index': para_index,
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

    def compute_sleep_coherence(self) -> Dict:
        """
        Sleep coherence targets a LOWER frequency than PSI coherence.
        PSI wants 0.1Hz (alertness + coherence).
        Sleep wants 0.05-0.08Hz (deep relaxation coherence).
        """
        if len(self.rr_series) < 30:
            return {
                'sleep_coherence': 0, 'sleep_coherence_pct': 0,
                'peak_frequency': 0, 'in_sleep_band': False,
                'relaxation_depth': 0
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]
        rr_ms = np.array(rr_vals)
        cumulative_time = np.cumsum(rr_ms) / 1000.0
        cumulative_time -= cumulative_time[0]

        resample_rate = 4.0
        t_uniform = np.arange(0, cumulative_time[-1], 1.0 / resample_rate)
        if len(t_uniform) < 16:
            return {
                'sleep_coherence': 0, 'sleep_coherence_pct': 0,
                'peak_frequency': 0, 'in_sleep_band': False,
                'relaxation_depth': 0
            }

        rr_uniform = np.interp(t_uniform, cumulative_time, rr_ms)
        rr_uniform -= np.mean(rr_uniform)

        n = len(rr_uniform)
        fft = np.fft.rfft(rr_uniform)
        power = np.abs(fft) ** 2
        freq = np.fft.rfftfreq(n, d=1.0 / resample_rate)

        sleep_band = (freq >= 0.04) & (freq <= 0.10)
        broad_band = (freq >= 0.01) & (freq <= 0.40)

        sleep_power = float(np.sum(power[sleep_band]))
        broad_power = float(np.sum(power[broad_band]))
        if broad_power > 0:
            sleep_coherence = sleep_power / broad_power
        else:
            sleep_coherence = 0

        if np.any(sleep_band):
            sleep_freqs = freq[sleep_band]
            sleep_powers = power[sleep_band]
            if len(sleep_powers) > 0:
                peak_idx = np.argmax(sleep_powers)
                peak_freq = float(sleep_freqs[peak_idx])
            else:
                peak_freq = 0
        else:
            peak_freq = 0

        in_sleep_band = 0.04 <= peak_freq <= 0.10

        deep_sleep_band = (freq >= 0.04) & (freq <= 0.07)
        deep_power = float(np.sum(power[deep_sleep_band]))
        relaxation_depth = min(1.0, deep_power / max(broad_power, 0.001) * 3.0)

        return {
            'sleep_coherence': min(1.0, sleep_coherence),
            'sleep_coherence_pct': min(100.0, sleep_coherence * 100),
            'peak_frequency': peak_freq,
            'in_sleep_band': in_sleep_band,
            'relaxation_depth': relaxation_depth
        }

    def compute_sleep_onset_probability(self) -> Dict:
        """
        Estimates probability of sleep onset based on physiological markers.

        Sleep onset indicators:
        1. HR dropping below personal resting baseline
        2. RMSSD increasing (parasympathetic surge)
        3. LF/HF ratio decreasing (vagal dominance)
        4. HR variability pattern shifting to sleep signature
        """
        if len(self.hr_trend) < 5 or len(self.hrv_trend) < 5:
            return {
                'onset_probability': 0, 'onset_pct': 0,
                'indicators': {}, 'stage': 'insufficient_data',
                'trend': 'stable',
                'recommendation': 'Keep breathing slowly'
            }

        hr_values = list(self.hr_trend)
        hrv_values = list(self.hrv_trend)

        hr_dropping = 0
        if len(hr_values) >= 3:
            recent_hr = np.mean(hr_values[-3:])
            earlier_hr = np.mean(hr_values[:min(5, len(hr_values))])
            if earlier_hr > 0:
                hr_drop_pct = (earlier_hr - recent_hr) / earlier_hr * 100
                hr_dropping = min(1.0, max(0.0, hr_drop_pct / 10.0))

        hrv_rising = 0
        if len(hrv_values) >= 3:
            recent_hrv = np.mean(hrv_values[-3:])
            earlier_hrv = np.mean(hrv_values[:min(5, len(hrv_values))])
            if earlier_hrv > 0:
                hrv_rise_pct = (recent_hrv - earlier_hrv) / earlier_hrv * 100
                hrv_rising = min(1.0, max(0.0, hrv_rise_pct / 20.0))

        current_hr = hr_values[-1] if hr_values else 80
        hr_target = (self.baseline_hr - 10) if self.baseline_hr else 65
        low_hr_score = min(1.0, max(0.0, (hr_target - current_hr + 10) / 15.0))

        current_rmssd = hrv_values[-1] if hrv_values else 0
        rmssd_target = max(60.0, (self.baseline_rmssd * 1.5) if self.baseline_rmssd else 60.0)
        high_hrv_score = min(1.0, current_rmssd / rmssd_target)

        onset_prob = (
            hr_dropping * 0.25 +
            hrv_rising * 0.25 +
            low_hr_score * 0.25 +
            high_hrv_score * 0.25
        )

        onset_prob = min(1.0, max(0.0, onset_prob))

        self.sleep_onset_scores.append(onset_prob)

        if onset_prob > 0.7:
            stage = 'approaching_sleep'
        elif onset_prob > 0.4:
            stage = 'deepening_relaxation'
        elif onset_prob > 0.2:
            stage = 'calming'
        else:
            stage = 'awake'

        recent_scores = list(self.sleep_onset_scores)
        if len(recent_scores) >= 5:
            trend = np.mean(recent_scores[-3:]) - np.mean(recent_scores[:3])
        else:
            trend = 0

        return {
            'onset_probability': onset_prob,
            'onset_pct': onset_prob * 100,
            'indicators': {
                'hr_dropping': hr_dropping,
                'hrv_rising': hrv_rising,
                'low_hr': low_hr_score,
                'high_hrv': high_hrv_score
            },
            'stage': stage,
            'trend': 'improving' if trend > 0.05 else ('stable' if abs(trend) < 0.05 else 'fluctuating'),
            'recommendation': self._sleep_recommendation(stage, onset_prob, current_hr, current_rmssd)
        }

    def _sleep_recommendation(self, stage, prob, hr, rmssd):
        if stage == 'approaching_sleep':
            return "You're almost there. Let go of the breathing pattern. Let your body breathe itself."
        elif stage == 'deepening_relaxation':
            if hr > 65:
                return "Good progress. Lengthen your exhale by one more second."
            else:
                return "Heart rate is low. Focus on warmth spreading through your body."
        elif stage == 'calming':
            if rmssd < 20:
                return "HRV still low. Try 4-7-8 breathing: inhale 4, hold 7, exhale 8."
            else:
                return "Building relaxation. Imagine a warm wave washing over you with each exhale."
        else:
            if hr > 80:
                return "Start with slow breathing: 4 seconds in, 6 seconds out. No rush."
            else:
                return "Begin extending your exhale. Each breath out is slightly longer than the last."


class LCCSleepProtocol:
    """
    The complete LCC Sleep Induction Protocol.

    Unlike PSI Tuning (which optimizes for INFORMATION EXCHANGE),
    this protocol optimizes for PARASYMPATHETIC SURRENDER.

    The LCC principle: consciousness creates attractor basins.
    Sleep IS an attractor basin. We just need to lower the walls.
    """

    PHASES = {
        1: {
            'name': 'WIND DOWN',
            'description': 'Activate parasympathetic nervous system',
            'target_duration': 180,
            'gates': {
                'hr_below': 75,
                'min_samples': 20
            },
            'breathing': {'inhale': 4, 'hold': 0, 'exhale': 6, 'pause': 2},
            'guidance': 'Settle in. Close your eyes. Breathe slowly - 4 seconds in, 6 seconds out. '
                       'There is nothing to do, nowhere to be. Just breathe.',
            'audio_suggestion': 'Rain or ocean sounds at low volume'
        },
        2: {
            'name': 'DEEPEN',
            'description': 'Build vagal tone, lower arousal',
            'target_duration': 240,
            'gates': {
                'hr_below': 70,
                'parasympathetic_above': 0.3,
            },
            'breathing': {'inhale': 4, 'hold': 0, 'exhale': 8, 'pause': 3},
            'guidance': 'Extend the exhale. Let each out-breath carry away tension. '
                       'Feel heaviness in your limbs - arms, legs, sinking into the bed. '
                       'The exhale is twice as long as the inhale now.',
            'audio_suggestion': 'Binaural beats at 3Hz (delta entrainment)'
        },
        3: {
            'name': 'ENTRAIN',
            'description': 'Heart-brain coherence at sleep frequency',
            'target_duration': 300,
            'gates': {
                'hr_below': 65,
                'sleep_coherence_above': 0.3,
                'parasympathetic_above': 0.4,
            },
            'breathing': {'inhale': 4, 'hold': 7, 'exhale': 8, 'pause': 0},
            'guidance': 'The 4-7-8 breath. Inhale for 4, hold gently for 7, exhale slowly for 8. '
                       'This is the most powerful natural sleep trigger known. '
                       'Your heart is synchronizing with sleep rhythms. Let it happen.',
            'audio_suggestion': 'Pink noise fading to silence'
        },
        4: {
            'name': 'DRIFT',
            'description': 'Release voluntary control, let body breathe itself',
            'target_duration': 300,
            'gates': {
                'onset_probability_above': 0.4,
                'hr_below': 62,
            },
            'breathing': {'inhale': 0, 'hold': 0, 'exhale': 0, 'pause': 0},
            'guidance': 'Release the breathing pattern. Your body knows how to breathe for sleep. '
                       'Let go of all effort. You are safe. You are warm. '
                       'Thoughts may come - let them pass like clouds in a night sky. '
                       'Do not try to sleep. Just allow.',
            'audio_suggestion': 'Silence or very faint drone'
        },
        5: {
            'name': 'SLEEP',
            'description': 'Sleep onset detected - monitoring continues',
            'target_duration': 0,
            'gates': {},
            'breathing': {'inhale': 0, 'hold': 0, 'exhale': 0, 'pause': 0},
            'guidance': 'Sleep transition detected. System is now monitoring. Sweet dreams.',
            'audio_suggestion': 'Silence'
        }
    }

    def __init__(self, pulsoid_token: str = None):
        self.token = pulsoid_token or os.environ.get('PULSOID_TOKEN')
        self.api_url = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"
        self.sleep_analyzer = SleepPhysiologyAnalyzer()

        self.current_phase = 0
        self.phase_start_time = None
        self.session_start_time = None
        self.session_active = False
        self.sleep_detected = False
        self.sleep_detected_time = None

        self.phase_history = []
        self.session_log = []

        self.last_valid_hr = 0
        self.last_valid_time = None

        self.baseline_hr = None
        self.baseline_samples = []

    def start_session(self) -> Dict:
        self.session_active = True
        self.session_start_time = time.time()
        self.current_phase = 1
        self.phase_start_time = time.time()
        self.phase_history = []
        self.session_log = []
        self.sleep_detected = False
        self.sleep_detected_time = None
        self.baseline_hr = None
        self.baseline_samples = []

        return {
            'status': 'SESSION_STARTED',
            'phase': 1,
            'phase_name': 'WIND DOWN',
            'message': 'LCC Sleep Protocol initiated. Get comfortable. Close your eyes after reading the guidance.',
            'timestamp': datetime.now().isoformat()
        }

    def stop_session(self) -> Dict:
        self.session_active = False
        duration = time.time() - self.session_start_time if self.session_start_time else 0

        summary = {
            'status': 'SESSION_ENDED',
            'duration_minutes': duration / 60,
            'phases_completed': max(0, self.current_phase - 1),
            'sleep_detected': self.sleep_detected,
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
                    self.sleep_analyzer.add_heartbeat(hr)
                    self.last_valid_hr = hr
                    self.last_valid_time = time.time()

                    if self.baseline_hr is None and len(self.baseline_samples) < 10:
                        self.baseline_samples.append(hr)
                        if len(self.baseline_samples) >= 10:
                            self.baseline_hr = np.mean(self.baseline_samples)

                return {'hr': hr if hr > 0 else self.last_valid_hr, 'connected': True}
        except:
            pass

        if self.last_valid_hr > 0 and self.last_valid_time:
            if time.time() - self.last_valid_time < 30:
                return {'hr': self.last_valid_hr, 'connected': True}
        return {'hr': 0, 'connected': False}

    def get_sleep_state(self) -> Dict:
        heart = self.read_heart()
        hrv = self.sleep_analyzer.compute_sleep_hrv()
        coherence = self.sleep_analyzer.compute_sleep_coherence()
        onset = self.sleep_analyzer.compute_sleep_onset_probability()

        phase_info = self.PHASES.get(self.current_phase, self.PHASES[1])
        phase_elapsed = time.time() - self.phase_start_time if self.phase_start_time else 0
        session_elapsed = time.time() - self.session_start_time if self.session_start_time else 0

        gate_status = self._check_gates(heart, hrv, coherence, onset)

        ai_guidance = self._generate_sleep_guidance(
            heart, hrv, coherence, onset, gate_status
        )

        relaxation_score = self._compute_relaxation_score(hrv, coherence, onset)

        state = {
            'heart': heart,
            'hrv': hrv,
            'coherence': coherence,
            'onset': onset,
            'relaxation_score': relaxation_score,
            'phase': {
                'number': self.current_phase,
                'name': phase_info['name'],
                'description': phase_info['description'],
                'elapsed': phase_elapsed,
                'target_duration': phase_info['target_duration'],
                'breathing': phase_info['breathing'],
                'base_guidance': phase_info['guidance'],
                'audio_suggestion': phase_info.get('audio_suggestion', ''),
            },
            'gates': gate_status,
            'ai_guidance': ai_guidance,
            'session_elapsed': session_elapsed,
            'baseline_hr': self.baseline_hr,
            'sleep_detected': self.sleep_detected,
            'timestamp': datetime.now().isoformat()
        }

        self.session_log.append({
            'phase': self.current_phase,
            'hr': heart.get('hr', 0),
            'rmssd': hrv.get('rmssd', 0),
            'coherence': coherence.get('sleep_coherence', 0),
            'onset_prob': onset.get('onset_probability', 0),
            'relaxation': relaxation_score,
            'timestamp': time.time()
        })

        return state

    def _check_gates(self, heart, hrv, coherence, onset) -> Dict:
        phase = self.PHASES.get(self.current_phase, self.PHASES[1])
        gates = phase['gates']
        results = {}
        all_passed = True

        if 'hr_below' in gates:
            current_hr = heart.get('hr', 100)
            passed = 0 < current_hr < gates['hr_below']
            results['heart_rate'] = {
                'target': f"< {gates['hr_below']} BPM",
                'current': current_hr,
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'min_samples' in gates:
            n_samples = len(self.sleep_analyzer.rr_series)
            passed = n_samples >= gates['min_samples']
            results['data_collected'] = {
                'target': f">= {gates['min_samples']} samples",
                'current': n_samples,
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'parasympathetic_above' in gates:
            para = hrv.get('parasympathetic_index', 0)
            passed = para >= gates['parasympathetic_above']
            results['parasympathetic'] = {
                'target': f">= {gates['parasympathetic_above']:.0%}",
                'current': f"{para:.0%}",
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'sleep_coherence_above' in gates:
            coh = coherence.get('sleep_coherence', 0)
            passed = coh >= gates['sleep_coherence_above']
            results['sleep_coherence'] = {
                'target': f">= {gates['sleep_coherence_above']:.0%}",
                'current': f"{coh:.0%}",
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'onset_probability_above' in gates:
            prob = onset.get('onset_probability', 0)
            passed = prob >= gates['onset_probability_above']
            results['sleep_onset'] = {
                'target': f">= {gates['onset_probability_above']:.0%}",
                'current': f"{prob:.0%}",
                'passed': passed
            }
            if not passed:
                all_passed = False

        phase_elapsed = time.time() - self.phase_start_time if self.phase_start_time else 0
        target = phase.get('target_duration', 120)
        time_passed = phase_elapsed >= target
        results['duration'] = {
            'target': f">= {target}s",
            'current': f"{phase_elapsed:.0f}s",
            'passed': time_passed
        }
        if not time_passed:
            all_passed = False

        results['all_passed'] = all_passed

        if all_passed and self.current_phase < 5:
            self._advance_phase()

        return results

    def _advance_phase(self):
        self.phase_history.append({
            'phase': self.current_phase,
            'name': self.PHASES[self.current_phase]['name'],
            'duration': time.time() - self.phase_start_time,
            'completed_at': datetime.now().isoformat()
        })

        self.current_phase = min(5, self.current_phase + 1)
        self.phase_start_time = time.time()

        if self.current_phase == 5:
            self.sleep_detected = True
            self.sleep_detected_time = time.time()

    def _compute_relaxation_score(self, hrv, coherence, onset) -> float:
        para = hrv.get('parasympathetic_index', 0) if hrv.get('sufficient_data') else 0
        coh = coherence.get('sleep_coherence', 0)
        prob = onset.get('onset_probability', 0)

        score = para * 0.35 + coh * 0.30 + prob * 0.35
        return min(1.0, max(0.0, score))

    def _generate_sleep_guidance(self, heart, hrv, coherence, onset, gates) -> str:
        hr = heart.get('hr', 0)
        phase = self.current_phase
        phase_info = self.PHASES.get(phase, self.PHASES[1])

        if not heart.get('connected'):
            return "Waiting for heart rate data. Make sure your Polar H10 is on."

        if phase == 1:
            if hr > 80:
                return "Heart rate is still elevated. Focus on slow, deep breaths. No rush - just breathe."
            elif hr > 70:
                return "Good, coming down. Continue the 4-6 pattern. Feel your body getting heavier."
            else:
                return "Nice and calm. You're building the foundation for sleep."

        elif phase == 2:
            rmssd = hrv.get('rmssd', 0)
            if rmssd < 20:
                return "Extend your exhale even more. Try 4 in, 8 out. Each exhale activates your vagus nerve."
            elif rmssd < 40:
                return "Vagal tone building. Imagine warmth spreading from your chest to your fingertips."
            else:
                return "Beautiful parasympathetic activation. Your body is remembering how to relax."

        elif phase == 3:
            coh = coherence.get('sleep_coherence', 0)
            if coh < 0.2:
                return "Begin the 4-7-8 breath. Inhale 4... hold 7... exhale 8. This is the key."
            elif coh < 0.4:
                return "Heart rhythm aligning with sleep frequency. Keep the 4-7-8 pattern. You're doing great."
            else:
                return "Sleep coherence established. Your heart and brain are synchronizing for sleep."

        elif phase == 4:
            prob = onset.get('onset_probability', 0)
            if prob < 0.3:
                return "Release the breathing pattern. Let your body breathe on its own. Just... be."
            elif prob < 0.6:
                return "Drifting deeper. No effort needed. You are safe. You are warm."
            else:
                return "Almost there. Let go completely. Sleep is coming to you."

        elif phase == 5:
            return "Sleep transition detected. Sweet dreams."

        return phase_info['guidance']

    def get_breathing_animation_state(self) -> Dict:
        """
        Returns the current state of the breathing animation.
        For Phase 4+ (DRIFT), returns autonomous/no guidance.
        """
        phase_info = self.PHASES.get(self.current_phase, self.PHASES[1])
        breathing = phase_info['breathing']

        if breathing['inhale'] == 0:
            return {
                'active': False,
                'phase_name': 'autonomous',
                'message': 'Let your body breathe itself'
            }

        total_cycle = breathing['inhale'] + breathing['hold'] + breathing['exhale'] + breathing['pause']
        if total_cycle == 0:
            return {'active': False, 'phase_name': 'rest', 'message': 'Rest'}

        elapsed = time.time() % total_cycle
        t = 0

        if elapsed < breathing['inhale']:
            progress = elapsed / breathing['inhale']
            return {
                'active': True,
                'phase_name': 'inhale',
                'progress': progress,
                'seconds_left': breathing['inhale'] - elapsed,
                'message': f"Breathe in... ({breathing['inhale']}s)",
                'size_factor': 0.5 + progress * 0.5
            }
        t += breathing['inhale']

        if breathing['hold'] > 0 and elapsed < t + breathing['hold']:
            hold_elapsed = elapsed - t
            progress = hold_elapsed / breathing['hold']
            return {
                'active': True,
                'phase_name': 'hold',
                'progress': progress,
                'seconds_left': breathing['hold'] - hold_elapsed,
                'message': f"Hold gently... ({breathing['hold']}s)",
                'size_factor': 1.0
            }
        t += breathing['hold']

        if elapsed < t + breathing['exhale']:
            exhale_elapsed = elapsed - t
            progress = exhale_elapsed / breathing['exhale']
            return {
                'active': True,
                'phase_name': 'exhale',
                'progress': progress,
                'seconds_left': breathing['exhale'] - exhale_elapsed,
                'message': f"Breathe out... ({breathing['exhale']}s)",
                'size_factor': 1.0 - progress * 0.5
            }
        t += breathing['exhale']

        if breathing['pause'] > 0:
            pause_elapsed = elapsed - t
            progress = pause_elapsed / breathing['pause']
            return {
                'active': True,
                'phase_name': 'pause',
                'progress': progress,
                'seconds_left': breathing['pause'] - pause_elapsed,
                'message': f"Pause... ({breathing['pause']}s)",
                'size_factor': 0.5
            }

        return {'active': True, 'phase_name': 'inhale', 'progress': 0, 'message': 'Breathe in...', 'size_factor': 0.5}

    def _save_session(self, summary: Dict):
        try:
            log_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'sleep_sessions')
            os.makedirs(log_dir, exist_ok=True)

            filename = f"sleep_session_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
            filepath = os.path.join(log_dir, filename)

            session_data = {
                'summary': summary,
                'log': list(self.session_log),
                'baseline_hr': self.baseline_hr
            }

            with open(filepath, 'w') as f:
                json.dump(session_data, f, indent=2, default=str)
        except Exception:
            pass

    def get_session_history(self) -> List[Dict]:
        try:
            log_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'sleep_sessions')
            if not os.path.exists(log_dir):
                return []

            sessions = []
            for f in sorted(os.listdir(log_dir), reverse=True)[:10]:
                if f.endswith('.json'):
                    with open(os.path.join(log_dir, f)) as fh:
                        sessions.append(json.load(fh))
            return sessions
        except Exception:
            return []


if __name__ == '__main__':
    print("=" * 70)
    print("LCC SLEEP INDUCTION ENGINE")
    print("=" * 70)
    print()
    print("Applying LCC principles to create sleep attractor basins.")
    print("Sleep is not forced - the walls around the basin are lowered.")
    print()

    protocol = LCCSleepProtocol()
    result = protocol.start_session()
    print(f"Session: {result['status']}")
    print(f"Phase: {result['phase']} - {result['phase_name']}")
    print()

    state = protocol.get_sleep_state()

    print(f"Heart Connected: {state['heart']['connected']}")
    print(f"Heart Rate: {state['heart']['hr']} BPM")
    print()

    print("HRV Metrics:")
    print(f"  RMSSD: {state['hrv']['rmssd']:.1f} ms")
    print(f"  Parasympathetic Index: {state['hrv']['parasympathetic_index']:.0%}")
    print()

    print(f"Sleep Coherence: {state['coherence']['sleep_coherence_pct']:.1f}%")
    print(f"In Sleep Band: {state['coherence']['in_sleep_band']}")
    print()

    print(f"Sleep Onset Probability: {state['onset']['onset_pct']:.1f}%")
    print(f"Stage: {state['onset']['stage']}")
    print()

    print(f"Relaxation Score: {state['relaxation_score']:.2f}")
    print()

    print(f"AI Guidance:")
    print(f"  > {state['ai_guidance']}")
    print()

    breathing = protocol.get_breathing_animation_state()
    print(f"Breathing: {breathing['message']}")
