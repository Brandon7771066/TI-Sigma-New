"""
PSI TUNING PROTOCOL ENGINE
============================
Pre-experiment optimization of heart-brain dynamics for maximum
PSI performance. This goes far beyond simple HRV biofeedback.

KEY INSIGHT: PSI isn't just about high HRV - it requires maximum
INFORMATION EXCHANGE between heart and brain. The heart-brain coupling
must be optimized so that pre-cognitive heart signals can propagate
to conscious awareness.

TUNING PHASES:
    Phase 1: GROUND    - Calm autonomic nervous system, establish baseline
    Phase 2: COHERE    - Build heart coherence (target: >85% CHSH threshold)
    Phase 3: COUPLE    - Maximize heart-brain information transfer
    Phase 4: AMPLIFY   - AI-guided resonance amplification
    Phase 5: READY     - All gates passed, system primed for PSI

SCIENTIFIC BASIS:
    - HeartMath: Heart coherence precedes intuitive access
    - McCraty et al.: Heart pre-stimulus response 4-7s before events
    - Transfer Entropy: Measures directed information flow H→B
    - Cross-coherence: Heart-brain frequency coupling strength
    - CHSH 0.85: Quantum probability boundary for nonlocal correlations

MULTI-MODAL VISION:
    - Polar H10: Heart channel (HRV, coherence, pre-cognitive signals)
    - Muse 2: Brain channel (EEG alpha/theta, attention, meditation)
    - Mendi: Photonic channel (fNIRS, cerebral blood flow, i-cell proxy)
    When all three converge, we have a complete consciousness lab.
"""

import numpy as np
import os
import time
import requests
from datetime import datetime
from collections import deque
from typing import Optional, Dict, List, Tuple


class HeartBrainCouplingAnalyzer:
    """
    Analyzes the COUPLING between heart and brain - not just individual metrics.
    This is the key insight: PSI performance depends on how well information
    flows between heart and brain, not just how calm each system is.
    """

    def __init__(self):
        self.hr_series = deque(maxlen=600)
        self.rr_series = deque(maxlen=600)
        self.coupling_history = deque(maxlen=120)
        self.transfer_entropy_history = deque(maxlen=60)

    def add_heartbeat(self, hr: float, timestamp: float = None):
        ts = timestamp or time.time()
        self.hr_series.append((ts, hr))
        if hr > 0:
            rr = 60000.0 / hr
            self.rr_series.append((ts, rr))

    def compute_hrv_metrics(self) -> Dict:
        if len(self.rr_series) < 10:
            return {
                'rmssd': 0, 'sdnn': 0, 'pnn50': 0,
                'lf_power': 0, 'hf_power': 0, 'lf_hf_ratio': 0,
                'sufficient_data': False
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]

        diffs = np.diff(rr_vals)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        sdnn = np.std(rr_vals)
        pnn50 = np.sum(np.abs(diffs) > 50) / len(diffs) * 100

        lf_power, hf_power, lf_hf = self._estimate_frequency_domain(rr_vals)

        return {
            'rmssd': rmssd,
            'sdnn': sdnn,
            'pnn50': pnn50,
            'lf_power': lf_power,
            'hf_power': hf_power,
            'lf_hf_ratio': lf_hf,
            'sufficient_data': True
        }

    def _estimate_frequency_domain(self, rr_vals: List[float]) -> Tuple[float, float, float]:
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
        hf_mask = (freq >= 0.15) & (freq < 0.4)

        lf_power = np.sum(power[lf_mask]) if np.any(lf_mask) else 0.0
        hf_power = np.sum(power[hf_mask]) if np.any(hf_mask) else 0.0

        lf_hf = lf_power / hf_power if hf_power > 1e-10 else 1.0

        return float(lf_power), float(hf_power), float(lf_hf)

    def compute_coherence_ratio(self) -> Dict:
        if len(self.rr_series) < 30:
            return {'coherence_ratio': 0, 'coherence_pct': 0, 'peak_frequency': 0, 'above_chsh': False, 'chsh_distance': -85}

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]
        rr_ms = np.array(rr_vals)
        cumulative_time = np.cumsum(rr_ms) / 1000.0
        cumulative_time -= cumulative_time[0]

        resample_rate = 4.0
        t_uniform = np.arange(0, cumulative_time[-1], 1.0 / resample_rate)
        if len(t_uniform) < 16:
            return {'coherence_ratio': 0, 'coherence_pct': 0, 'peak_frequency': 0, 'above_chsh': False, 'chsh_distance': -85}

        rr_uniform = np.interp(t_uniform, cumulative_time, rr_ms)
        rr_uniform -= np.mean(rr_uniform)

        n = len(rr_uniform)
        fft = np.fft.rfft(rr_uniform)
        power = np.abs(fft) ** 2
        freq = np.fft.rfftfreq(n, d=1.0 / resample_rate)

        coherence_band = (freq >= 0.04) & (freq < 0.26)
        coherence_center = (freq >= 0.08) & (freq < 0.12)

        total_coherence_power = np.sum(power[coherence_band]) if np.any(coherence_band) else 1e-10
        center_power = np.sum(power[coherence_center]) if np.any(coherence_center) else 0

        coherence_ratio = center_power / total_coherence_power if total_coherence_power > 1e-10 else 0
        coherence_pct = coherence_ratio * 100

        peak_idx = np.argmax(power[1:]) + 1
        peak_freq = freq[peak_idx] if peak_idx < len(freq) else 0

        return {
            'coherence_ratio': coherence_ratio,
            'coherence_pct': coherence_pct,
            'peak_frequency': float(peak_freq),
            'above_chsh': coherence_pct > 85.0,
            'chsh_distance': coherence_pct - 85.0
        }

    def compute_transfer_entropy_proxy(self) -> Dict:
        """
        Transfer Entropy proxy for heart→brain information flow.

        True TE requires simultaneous EEG, but we can estimate the
        heart's information generation rate from RR interval patterns.
        Higher sample entropy in RR intervals = more information being
        generated by the cardiac neural network for the brain to process.

        For PSI: We want MODERATE complexity (not too regular, not chaotic)
        which indicates the heart is generating meaningful predictive signals.
        """
        if len(self.rr_series) < 30:
            return {
                'heart_info_rate': 0, 'complexity': 'insufficient_data',
                'psi_optimal': False, 'te_proxy': 0
            }

        rr_vals = [r[1] for r in list(self.rr_series)[-60:]]

        sample_entropy = self._sample_entropy(rr_vals, m=2, r_factor=0.2)

        if sample_entropy < 0:
            return {
                'heart_info_rate': 0, 'complexity': 'insufficient_data',
                'psi_optimal': False, 'te_proxy': 0, 'info_quality': 0
            }

        if sample_entropy < 0.3:
            complexity = 'too_regular'
            psi_optimal = False
            info_quality = 0.3
        elif sample_entropy < 0.8:
            complexity = 'low_moderate'
            psi_optimal = False
            info_quality = 0.6
        elif sample_entropy < 1.5:
            complexity = 'optimal'
            psi_optimal = True
            info_quality = 1.0
        elif sample_entropy < 2.0:
            complexity = 'high_moderate'
            psi_optimal = True
            info_quality = 0.8
        else:
            complexity = 'chaotic'
            psi_optimal = False
            info_quality = 0.3

        te_proxy = info_quality * min(1.0, sample_entropy / 1.5)
        self.transfer_entropy_history.append(te_proxy)

        return {
            'heart_info_rate': sample_entropy,
            'complexity': complexity,
            'psi_optimal': psi_optimal,
            'te_proxy': te_proxy,
            'info_quality': info_quality
        }

    def _sample_entropy(self, data: List[float], m: int = 2, r_factor: float = 0.2) -> float:
        data = np.array(data, dtype=float)
        n = len(data)
        std = np.std(data)
        if std < 1e-10:
            return 0.0
        r = r_factor * std

        if n < m + 3:
            return 0.0

        max_n = min(n, 80)
        data = data[:max_n]
        n = len(data)

        def count_matches(template_len):
            count = 0
            templates = [data[i:i+template_len] for i in range(n - template_len)]
            for i in range(len(templates)):
                for j in range(i + 1, len(templates)):
                    if np.max(np.abs(templates[i] - templates[j])) < r:
                        count += 1
            return count

        b = count_matches(m)
        a = count_matches(m + 1)

        if b <= 1:
            return -1.0
        if a == 0:
            a = 0.5

        return -np.log(a / b)

    def compute_coupling_score(self) -> Dict:
        """
        The MASTER coupling metric: how well is the heart-brain
        information channel functioning for PSI?
        """
        hrv = self.compute_hrv_metrics()
        coherence = self.compute_coherence_ratio()
        te = self.compute_transfer_entropy_proxy()

        if not hrv['sufficient_data']:
            return {
                'coupling_score': 0, 'grade': 'INSUFFICIENT_DATA',
                'components': {}, 'ready_for_psi': False
            }

        hrv_score = min(1.0, hrv['rmssd'] / 60.0)

        coh_score = min(1.0, coherence['coherence_pct'] / 100.0)

        te_score = te['te_proxy']

        lf_hf = hrv['lf_hf_ratio']
        if 0.5 <= lf_hf <= 2.0:
            balance_score = 1.0
        elif 0.3 <= lf_hf <= 3.0:
            balance_score = 0.7
        else:
            balance_score = 0.3

        coupling_score = (
            hrv_score * 0.20 +
            coh_score * 0.30 +
            te_score * 0.30 +
            balance_score * 0.20
        )

        self.coupling_history.append(coupling_score)

        if coupling_score > 0.8:
            grade = 'EXCEPTIONAL'
        elif coupling_score > 0.65:
            grade = 'STRONG'
        elif coupling_score > 0.5:
            grade = 'MODERATE'
        elif coupling_score > 0.3:
            grade = 'BUILDING'
        else:
            grade = 'WARMING_UP'

        return {
            'coupling_score': coupling_score,
            'grade': grade,
            'components': {
                'hrv_health': {'score': hrv_score, 'rmssd': hrv['rmssd'], 'weight': 0.20},
                'coherence': {'score': coh_score, 'pct': coherence['coherence_pct'],
                              'above_chsh': coherence['above_chsh'], 'weight': 0.30},
                'information_flow': {'score': te_score, 'complexity': te['complexity'],
                                     'psi_optimal': te['psi_optimal'], 'weight': 0.30},
                'autonomic_balance': {'score': balance_score, 'lf_hf': lf_hf, 'weight': 0.20}
            },
            'ready_for_psi': coupling_score > 0.6 and te['psi_optimal'] and coherence['coherence_pct'] > 50
        }


class PSITuningProtocol:
    """
    The complete PSI Tuning Protocol with 5 progressive phases.

    Each phase has specific targets and gates. The AI guides you
    through the progression, adapting in real-time to your physiology.
    """

    PHASES = {
        1: {
            'name': 'GROUND',
            'description': 'Calm autonomic nervous system, establish baseline',
            'target_duration': 120,
            'gates': {
                'hr_below': 80,
                'hrv_rmssd_above': 20,
                'min_samples': 30
            },
            'breathing': {'inhale': 4, 'hold': 0, 'exhale': 6, 'pause': 0},
            'guidance': 'Slow your breathing. 4 seconds in, 6 seconds out. '
                       'Feel your feet on the ground. Let thoughts pass like clouds.'
        },
        2: {
            'name': 'COHERE',
            'description': 'Build heart coherence toward CHSH threshold',
            'target_duration': 180,
            'gates': {
                'coherence_above': 60,
                'coupling_above': 0.4,
            },
            'breathing': {'inhale': 5, 'hold': 2, 'exhale': 5, 'pause': 2},
            'guidance': 'Focus on your heart area. Breathe as if through your heart. '
                       'Activate a feeling of genuine appreciation or love. '
                       'This emotion is the key that opens the coherence channel.'
        },
        3: {
            'name': 'COUPLE',
            'description': 'Maximize heart-brain information transfer',
            'target_duration': 180,
            'gates': {
                'coupling_above': 0.6,
                'te_optimal': True,
                'coherence_above': 70,
            },
            'breathing': {'inhale': 5, 'hold': 3, 'exhale': 7, 'pause': 2},
            'guidance': 'Maintain heart focus while expanding awareness to your whole body. '
                       'Feel the connection between heart and head. '
                       'You are opening the information highway between them. '
                       'The heart knows before the brain - let it speak.'
        },
        4: {
            'name': 'AMPLIFY',
            'description': 'AI-guided resonance amplification',
            'target_duration': 120,
            'gates': {
                'coupling_above': 0.7,
                'coherence_above': 80,
            },
            'breathing': {'inhale': 6, 'hold': 4, 'exhale': 8, 'pause': 2},
            'guidance': 'You are approaching the quantum threshold. '
                       'The AI is now actively tracking your resonance patterns. '
                       'Allow the system to synchronize with you. '
                       'Trust the process - accuracy emerges from function.'
        },
        5: {
            'name': 'READY',
            'description': 'All gates passed - system primed for PSI',
            'target_duration': 60,
            'gates': {
                'coupling_above': 0.7,
                'coherence_above': 85,
            },
            'breathing': {'inhale': 4, 'hold': 2, 'exhale': 4, 'pause': 2},
            'guidance': 'You have crossed the CHSH threshold. '
                       'Heart and brain are in quantum-level coherence. '
                       'Information flows freely between all channels. '
                       'You are READY for the experiment. '
                       'Maintain this state and proceed when you feel called.'
        }
    }

    def __init__(self, pulsoid_token: str = None):
        self.token = pulsoid_token or os.environ.get('PULSOID_TOKEN')
        self.api_url = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"
        self.coupling_analyzer = HeartBrainCouplingAnalyzer()

        self.current_phase = 0
        self.phase_start_time = None
        self.session_start_time = None
        self.session_active = False

        self.phase_history = []
        self.tuning_log = []

        self.last_valid_hr = 0
        self.last_valid_time = None
        self.mendi_available = False
        self.mendi_data = {}

    def start_tuning_session(self) -> Dict:
        self.session_active = True
        self.session_start_time = time.time()
        self.current_phase = 1
        self.phase_start_time = time.time()
        self.phase_history = []
        self.tuning_log = []

        return {
            'status': 'TUNING_STARTED',
            'phase': 1,
            'phase_name': 'GROUND',
            'message': 'PSI Tuning Protocol initiated. Beginning Phase 1: GROUND.',
            'timestamp': datetime.now().isoformat()
        }

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
                    self.coupling_analyzer.add_heartbeat(hr)
                    self.last_valid_hr = hr
                    self.last_valid_time = time.time()
                return {'hr': hr if hr > 0 else self.last_valid_hr, 'connected': True}
        except:
            pass

        if self.last_valid_hr > 0 and self.last_valid_time:
            if time.time() - self.last_valid_time < 30:
                return {'hr': self.last_valid_hr, 'connected': True}
        return {'hr': 0, 'connected': False}

    def get_tuning_state(self) -> Dict:
        heart = self.read_heart()
        hrv = self.coupling_analyzer.compute_hrv_metrics()
        coherence = self.coupling_analyzer.compute_coherence_ratio()
        te = self.coupling_analyzer.compute_transfer_entropy_proxy()
        coupling = self.coupling_analyzer.compute_coupling_score()

        phase_info = self.PHASES.get(self.current_phase, self.PHASES[1])
        phase_elapsed = time.time() - self.phase_start_time if self.phase_start_time else 0
        session_elapsed = time.time() - self.session_start_time if self.session_start_time else 0

        gate_status = self._check_gates(heart, hrv, coherence, te, coupling)

        ai_guidance = self._generate_ai_guidance(
            heart, hrv, coherence, te, coupling, gate_status
        )

        state = {
            'heart': heart,
            'hrv': hrv,
            'coherence': coherence,
            'transfer_entropy': te,
            'coupling': coupling,
            'phase': {
                'number': self.current_phase,
                'name': phase_info['name'],
                'description': phase_info['description'],
                'elapsed': phase_elapsed,
                'target_duration': phase_info['target_duration'],
                'breathing': phase_info['breathing'],
                'base_guidance': phase_info['guidance'],
            },
            'gates': gate_status,
            'ai_guidance': ai_guidance,
            'session_elapsed': session_elapsed,
            'mendi': self._get_mendi_state(),
            'psi_readiness': self._compute_psi_readiness(coupling, coherence, te),
            'timestamp': datetime.now().isoformat()
        }

        self.tuning_log.append({
            'phase': self.current_phase,
            'coupling_score': coupling['coupling_score'],
            'coherence': coherence.get('coherence_pct', 0),
            'hr': heart.get('hr', 0),
            'timestamp': time.time()
        })

        return state

    def _check_gates(self, heart, hrv, coherence, te, coupling) -> Dict:
        phase = self.PHASES.get(self.current_phase, self.PHASES[1])
        gates = phase['gates']
        results = {}
        all_passed = True

        if 'hr_below' in gates:
            passed = heart.get('hr', 100) < gates['hr_below'] and heart.get('hr', 0) > 0
            results['heart_rate'] = {
                'target': f"< {gates['hr_below']} BPM",
                'current': heart.get('hr', 0),
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'hrv_rmssd_above' in gates:
            passed = hrv['rmssd'] > gates['hrv_rmssd_above']
            results['hrv_rmssd'] = {
                'target': f"> {gates['hrv_rmssd_above']} ms",
                'current': round(hrv['rmssd'], 1),
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'min_samples' in gates:
            n = len(self.coupling_analyzer.rr_series)
            passed = n >= gates['min_samples']
            results['data_samples'] = {
                'target': f">= {gates['min_samples']}",
                'current': n,
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'coherence_above' in gates:
            coh_pct = coherence.get('coherence_pct', 0)
            passed = coh_pct > gates['coherence_above']
            results['coherence'] = {
                'target': f"> {gates['coherence_above']}%",
                'current': round(coh_pct, 1),
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'coupling_above' in gates:
            passed = coupling['coupling_score'] > gates['coupling_above']
            results['coupling'] = {
                'target': f"> {gates['coupling_above']:.0%}",
                'current': round(coupling['coupling_score'], 3),
                'passed': passed
            }
            if not passed:
                all_passed = False

        if 'te_optimal' in gates:
            passed = te.get('psi_optimal', False)
            results['information_flow'] = {
                'target': 'Optimal complexity',
                'current': te.get('complexity', 'unknown'),
                'passed': passed
            }
            if not passed:
                all_passed = False

        results['all_passed'] = all_passed
        return results

    def advance_phase(self) -> Dict:
        if self.current_phase >= 5:
            return {
                'advanced': False,
                'message': 'Already at Phase 5: READY. Begin your experiment!',
                'phase': 5
            }

        self.phase_history.append({
            'phase': self.current_phase,
            'duration': time.time() - self.phase_start_time,
            'completed_at': datetime.now().isoformat()
        })

        self.current_phase += 1
        self.phase_start_time = time.time()
        phase_info = self.PHASES[self.current_phase]

        return {
            'advanced': True,
            'phase': self.current_phase,
            'phase_name': phase_info['name'],
            'message': f"Advanced to Phase {self.current_phase}: {phase_info['name']}",
            'guidance': phase_info['guidance']
        }

    def _generate_ai_guidance(self, heart, hrv, coherence, te, coupling, gates) -> Dict:
        messages = []
        priority = 'maintain'

        if not heart.get('connected', False):
            return {
                'messages': ['Connect Polar H10 via Pulsoid to begin tuning.'],
                'priority': 'critical',
                'breathing_adjust': None
            }

        breathing_adjust = None

        if self.current_phase == 1:
            hr = heart.get('hr', 0)
            if hr > 90:
                messages.append(f"Heart rate is {hr} BPM - focus on slowing exhale. "
                              "Exhale should be 1.5x longer than inhale.")
                priority = 'adjust'
                breathing_adjust = {'inhale': 4, 'hold': 0, 'exhale': 8, 'pause': 2}
            elif hr > 80:
                messages.append(f"Heart rate {hr} BPM - almost there. "
                              "Deepen the exhale slightly.")
                priority = 'gentle'
            else:
                messages.append(f"Heart rate {hr} BPM - excellent grounding. "
                              "Your nervous system is calming.")

        elif self.current_phase == 2:
            coh = coherence.get('coherence_pct', 0)
            if coh < 30:
                messages.append("Coherence building. Focus attention on heart area. "
                              "Generate a feeling of genuine appreciation.")
                priority = 'adjust'
            elif coh < 60:
                messages.append(f"Coherence at {coh:.0f}% - good progress! "
                              "Deepen the emotional quality of your breath.")
                priority = 'building'
            else:
                messages.append(f"Coherence at {coh:.0f}% - STRONG! "
                              "Heading toward CHSH threshold.")

        elif self.current_phase == 3:
            te_complexity = te.get('complexity', 'unknown')
            if te_complexity == 'too_regular':
                messages.append("Heart rhythm too regular - try varying breath slightly. "
                              "Allow natural rhythm to emerge. The heart needs freedom to generate information.")
                priority = 'adjust'
            elif te_complexity == 'chaotic':
                messages.append("Heart rhythm too chaotic - return to structured breathing. "
                              "The information channel needs more order.")
                priority = 'adjust'
            elif te_complexity in ['optimal', 'high_moderate']:
                messages.append("Heart information flow OPTIMAL! "
                              "The cardiac neural network is generating meaningful pre-cognitive signals. "
                              "This is the sweet spot for PSI.")

            coupling_s = coupling['coupling_score']
            if coupling_s < 0.5:
                messages.append("Heart-brain coupling still building. "
                              "Expand awareness from heart to whole body.")
            elif coupling_s > 0.6:
                messages.append(f"Coupling score {coupling_s:.2f} - information highway is OPEN.")

        elif self.current_phase == 4:
            coupling_s = coupling['coupling_score']
            coh = coherence.get('coherence_pct', 0)
            if coh > 85:
                messages.append("ABOVE CHSH THRESHOLD! Quantum-level coherence achieved. "
                              "Correlations now exceed classical hidden variable models.")
            elif coh > 75:
                messages.append(f"Coherence {coh:.0f}% - approaching quantum boundary at 85%. "
                              "You're close. Deepen appreciation.")

            if coupling_s > 0.7:
                messages.append("Coupling EXCEPTIONAL - all channels maximally entrained. "
                              "AI amplification engaged.")
                priority = 'optimal'

        elif self.current_phase == 5:
            messages.append("ALL SYSTEMS READY. Heart-brain coupling optimized. "
                          "Information channels fully open. You are primed for PSI testing. "
                          "Maintain this state and proceed when you feel the call.")
            priority = 'ready'

        if gates.get('all_passed', False) and self.current_phase < 5:
            messages.append(f"ALL GATES PASSED for Phase {self.current_phase}! "
                          f"Ready to advance to Phase {self.current_phase + 1}.")

        return {
            'messages': messages,
            'priority': priority,
            'breathing_adjust': breathing_adjust
        }

    def _get_mendi_state(self) -> Dict:
        return {
            'available': self.mendi_available,
            'status': 'READY_TO_INTEGRATE' if not self.mendi_available else 'STREAMING',
            'message': 'Mendi fNIRS will provide photonic brain imaging '
                      'to confirm i-cell hypothesis and measure cerebral blood flow patterns.',
            'data': self.mendi_data
        }

    def set_mendi_data(self, cortical_activity: float = 0, focus_score: float = 0):
        self.mendi_available = True
        self.mendi_data = {
            'cortical_activity': cortical_activity,
            'focus_score': focus_score,
            'timestamp': datetime.now().isoformat()
        }

    def _compute_psi_readiness(self, coupling, coherence, te) -> Dict:
        score = 0
        checks = []

        if coupling['coupling_score'] > 0.6:
            score += 30
            checks.append(('Heart-Brain Coupling', True, f"{coupling['coupling_score']:.2f}"))
        else:
            checks.append(('Heart-Brain Coupling', False, f"{coupling['coupling_score']:.2f} (need >0.60)"))

        coh_pct = coherence.get('coherence_pct', 0)
        if coh_pct > 85:
            score += 30
            checks.append(('CHSH Threshold', True, f"{coh_pct:.0f}% > 85%"))
        elif coh_pct > 70:
            score += 15
            checks.append(('CHSH Threshold', False, f"{coh_pct:.0f}% (approaching 85%)"))
        else:
            checks.append(('CHSH Threshold', False, f"{coh_pct:.0f}% (need >85%)"))

        if te.get('psi_optimal', False):
            score += 25
            checks.append(('Information Flow', True, f"Optimal ({te.get('complexity', '')})"))
        else:
            checks.append(('Information Flow', False, f"{te.get('complexity', 'unknown')}"))

        if self.current_phase >= 4:
            score += 15
            checks.append(('Protocol Phase', True, f"Phase {self.current_phase}"))
        else:
            checks.append(('Protocol Phase', False, f"Phase {self.current_phase} (need >= 4)"))

        if score >= 90:
            status = 'GO'
            message = 'ALL SYSTEMS GO - Begin PSI experiment!'
        elif score >= 60:
            status = 'ALMOST'
            message = 'Close to ready - continue tuning'
        elif score >= 30:
            status = 'BUILDING'
            message = 'Systems warming up - stay with the protocol'
        else:
            status = 'NOT_READY'
            message = 'Continue tuning protocol from current phase'

        return {
            'score': score,
            'status': status,
            'message': message,
            'checks': checks,
            'max_score': 100
        }

    def get_session_summary(self) -> Dict:
        if not self.tuning_log:
            return {'message': 'No tuning data yet'}

        coupling_scores = [e['coupling_score'] for e in self.tuning_log]
        coherence_vals = [e['coherence'] for e in self.tuning_log]
        hr_vals = [e['hr'] for e in self.tuning_log if e['hr'] > 0]

        return {
            'duration': time.time() - self.session_start_time if self.session_start_time else 0,
            'phases_completed': len(self.phase_history),
            'current_phase': self.current_phase,
            'peak_coupling': max(coupling_scores) if coupling_scores else 0,
            'avg_coupling': np.mean(coupling_scores) if coupling_scores else 0,
            'peak_coherence': max(coherence_vals) if coherence_vals else 0,
            'avg_hr': np.mean(hr_vals) if hr_vals else 0,
            'data_points': len(self.tuning_log),
            'phase_history': self.phase_history
        }


if __name__ == "__main__":
    print("=" * 70)
    print("PSI TUNING PROTOCOL ENGINE")
    print("=" * 70)
    print()
    print("Optimizing heart-brain coupling for maximum PSI performance.")
    print("This goes BEYOND simple HRV - it maximizes INFORMATION EXCHANGE.")
    print()

    protocol = PSITuningProtocol()
    session = protocol.start_tuning_session()
    print(f"Session: {session['status']}")
    print(f"Phase: {session['phase']} - {session['phase_name']}")
    print()

    state = protocol.get_tuning_state()
    print(f"Heart Connected: {state['heart']['connected']}")
    if state['heart']['connected']:
        print(f"Heart Rate: {state['heart']['hr']} BPM")

    print(f"\nHRV Metrics:")
    hrv = state['hrv']
    print(f"  RMSSD: {hrv['rmssd']:.1f} ms")
    print(f"  SDNN: {hrv['sdnn']:.1f} ms")
    print(f"  LF/HF Ratio: {hrv['lf_hf_ratio']:.2f}")

    print(f"\nCoherence: {state['coherence'].get('coherence_pct', 0):.1f}%")
    print(f"Above CHSH: {state['coherence'].get('above_chsh', False)}")

    print(f"\nCoupling Score: {state['coupling']['coupling_score']:.3f}")
    print(f"Coupling Grade: {state['coupling']['grade']}")

    print(f"\nPSI Readiness: {state['psi_readiness']['status']}")
    print(f"Score: {state['psi_readiness']['score']}/100")
    for check_name, passed, detail in state['psi_readiness']['checks']:
        icon = "PASS" if passed else "FAIL"
        print(f"  [{icon}] {check_name}: {detail}")

    print(f"\nAI Guidance:")
    for msg in state['ai_guidance']['messages']:
        print(f"  > {msg}")

    print(f"\nMendi Status: {state['mendi']['status']}")
