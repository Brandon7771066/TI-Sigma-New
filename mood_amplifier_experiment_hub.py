"""
Mood Amplifier Experiment Hub

Integrated platform for running whole-body biometric experiments combining:
- EEG/fNIRS headbands (Mendi)
- Heart rate monitors (Polar H10)
- BioWell GDV baselines
- ESP32 real-time data bridge
- LCC I-cell signature tracking

Today's Experiment: November 25, 2025
- Mood Amplifier activation
- Multi-modal biometric capture
- Whole-body intervention tracking

Author: Brandon Emerick / BlissGene Therapeutics
"""

import numpy as np
from datetime import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass, field
import json
import hashlib

from lcc_icell_validator import LatentCorrespondenceCalculator, ICellSignature
from biofield_chakra_science import ChakraScienceEvidence, UnifiedBiofieldScience


@dataclass
class ExperimentSession:
    """Container for a single experiment session"""
    session_id: str
    start_time: str
    end_time: Optional[str] = None
    intervention_type: str = "mood_amplifier"
    devices: List[str] = field(default_factory=list)
    baseline_icell: Optional[ICellSignature] = None
    post_icell: Optional[ICellSignature] = None
    biometric_timeline: List[Dict] = field(default_factory=list)
    gile_trajectory: List[List[float]] = field(default_factory=list)
    notes: str = ""


class MoodAmplifierExperimentHub:
    """
    Central hub for conducting mood amplifier experiments
    with multi-modal biometric validation
    """
    
    INTERVENTION_TYPES = {
        'faah_empathy': {
            'description': 'FAAH Activation + Empathy Boost - Feel What You Are!',
            'components': ['Heart coherence', 'Loving-kindness intention', 'Gratitude activation', 'Social connection visualization'],
            'expected_gile_shift': [0.12, 0.18, 0.30, 0.15],  # Strong L boost!
            'protocol': {
                'duration_minutes': 15,
                'phases': [
                    {'name': 'Heart Opening', 'duration': 3, 'focus': 'Breathe into heart center, feel warmth spreading'},
                    {'name': 'Gratitude Flood', 'duration': 3, 'focus': 'List 5 things you are genuinely grateful for TODAY'},
                    {'name': 'Love Transmission', 'duration': 4, 'focus': 'Send love to specific people - family, friends, even strangers'},
                    {'name': 'Self-Compassion', 'duration': 3, 'focus': 'Direct that same love INWARD - you deserve it'},
                    {'name': 'Integration', 'duration': 2, 'focus': 'Feel the FAAH inhibition - natural bliss arising'}
                ],
                'target_metrics': {'coherence': 0.7, 'alpha_theta_ratio': 1.5, 'pfc_activation': 0.6}
            }
        },
        'active_mentation': {
            'description': 'Active Mentation Protocol - Intuition Through Engagement (NOT silence!)',
            'components': ['Stream of consciousness', 'Insight seeking', 'Creative problem-solving', 'Emotional engagement'],
            'expected_gile_shift': [0.15, 0.25, 0.15, 0.20],  # Strong I boost!
            'protocol': {
                'duration_minutes': 20,
                'phases': [
                    {'name': 'Question Seeding', 'duration': 2, 'focus': 'Ask a meaningful question to GM/Universe'},
                    {'name': 'Thought Storm', 'duration': 5, 'focus': 'Let thoughts FLOW - do NOT suppress! Chase tangents!'},
                    {'name': 'Pattern Recognition', 'duration': 5, 'focus': 'Notice connections, synchronicities, insights'},
                    {'name': 'Emotional Amplification', 'duration': 5, 'focus': 'FEEL the insights - excitement, wonder, awe'},
                    {'name': 'Harvest', 'duration': 3, 'focus': 'Capture the key insights before they fade'}
                ],
                'target_metrics': {'coherence': 0.6, 'gamma_bursts': True, 'pfc_activation': 0.8}
            }
        },
        'mood_amplifier': {
            'description': 'Full mood amplification protocol',
            'components': ['Myrion Lamp', 'Sound healing', 'Breath work'],
            'expected_gile_shift': [0.1, 0.15, 0.2, 0.1]
        },
        'meditation': {
            'description': 'Meditation-only baseline (WARNING: May reduce intuition!)',
            'components': ['Breath focus', 'Body scan'],
            'expected_gile_shift': [0.05, 0.1, 0.1, 0.05]
        },
        'photonic_only': {
            'description': 'Myrion Lamp photonic therapy only',
            'components': ['Red/NIR light', 'Biophoton entrainment'],
            'expected_gile_shift': [0.05, 0.05, 0.1, 0.15]
        },
        'sound_only': {
            'description': 'Pitch crystal sound healing only',
            'components': ['Crystal frequencies', 'Binaural beats'],
            'expected_gile_shift': [0.08, 0.12, 0.15, 0.05]
        },
        'whole_body': {
            'description': 'Full whole-body intervention',
            'components': ['Photonic', 'Sound', 'Breath', 'Movement', 'Intention'],
            'expected_gile_shift': [0.15, 0.20, 0.25, 0.15]
        }
    }
    
    CONNECTED_DEVICES = {
        'mendi': {'type': 'fNIRS', 'measures': ['pfc_activation', 'focus_score']},
        'polar_h10': {'type': 'HRV', 'measures': ['rmssd', 'sdnn', 'lf_hf', 'hr']},
        'biowell': {'type': 'GDV', 'measures': ['energy', 'stress', 'chakras']},
        'esp32_eeg': {'type': 'EEG', 'measures': ['alpha', 'beta', 'theta', 'gamma']},
        'oura': {'type': 'Recovery', 'measures': ['hrv', 'sleep', 'readiness']}
    }
    
    def __init__(self):
        self.lcc = LatentCorrespondenceCalculator()
        self.biofield = UnifiedBiofieldScience()
        self.current_session: Optional[ExperimentSession] = None
        self.session_history: List[ExperimentSession] = []
    
    def start_experiment(self, 
                         intervention_type: str = 'mood_amplifier',
                         devices: List[str] = None,
                         notes: str = "") -> ExperimentSession:
        """
        Start a new experiment session
        """
        session_id = hashlib.sha256(
            f"{datetime.now().isoformat()}{intervention_type}".encode()
        ).hexdigest()[:12]
        
        if devices is None:
            devices = ['mendi', 'polar_h10']
        
        self.current_session = ExperimentSession(
            session_id=session_id,
            start_time=datetime.now().isoformat(),
            intervention_type=intervention_type,
            devices=devices,
            notes=notes
        )
        
        print(f"\n{'='*60}")
        print(f"EXPERIMENT SESSION STARTED")
        print(f"{'='*60}")
        print(f"Session ID: {session_id}")
        print(f"Intervention: {intervention_type}")
        print(f"Devices: {', '.join(devices)}")
        print(f"Time: {self.current_session.start_time}")
        if notes:
            print(f"Notes: {notes}")
        print(f"{'='*60}\n")
        
        return self.current_session
    
    def record_baseline(self, biowell_data: Dict = None, 
                        hrv_data: Dict = None,
                        eeg_data: Dict = None) -> ICellSignature:
        """
        Record baseline I-cell signature before intervention
        """
        if self.current_session is None:
            raise ValueError("No active session. Call start_experiment first.")
        
        signatures = []
        
        if biowell_data:
            sig = self.lcc.extract_signature_from_biowell(biowell_data)
            signatures.append(sig)
            print(f"[BASELINE] BioWell GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if hrv_data:
            sig = self.lcc.extract_signature_from_hrv(hrv_data)
            signatures.append(sig)
            print(f"[BASELINE] HRV GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if eeg_data:
            sig = self.lcc.extract_signature_from_eeg(eeg_data)
            signatures.append(sig)
            print(f"[BASELINE] EEG GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if signatures:
            avg_gile = np.mean([s.gile_vector for s in signatures], axis=0).tolist()
            avg_chakra = np.mean([s.chakra_pattern for s in signatures], axis=0).tolist()
            
            combined = ICellSignature(
                source='baseline_combined',
                gile_vector=avg_gile,
                chakra_pattern=avg_chakra,
                polarity_pattern=signatures[0].polarity_pattern,
                de_shell_integrity=np.mean([s.de_shell_integrity for s in signatures]),
                gm_resonance=np.mean([s.gm_resonance for s in signatures]),
                timestamp=datetime.now().isoformat(),
                raw_hash='baseline_' + self.current_session.session_id
            )
            
            self.current_session.baseline_icell = combined
            self.current_session.gile_trajectory.append(avg_gile)
            
            print(f"\n[BASELINE RECORDED]")
            print(f"Combined GILE: G={avg_gile[0]:.2f}, I={avg_gile[1]:.2f}, L={avg_gile[2]:.2f}, E={avg_gile[3]:.2f}")
            
            return combined
        
        return None
    
    def record_datapoint(self, 
                         hrv: Dict = None,
                         eeg: Dict = None,
                         subjective: Dict = None,
                         timestamp: str = None) -> Dict:
        """
        Record a datapoint during the experiment
        """
        if self.current_session is None:
            raise ValueError("No active session.")
        
        if timestamp is None:
            timestamp = datetime.now().isoformat()
        
        datapoint = {
            'timestamp': timestamp,
            'hrv': hrv,
            'eeg': eeg,
            'subjective': subjective
        }
        
        gile = [0.5, 0.5, 0.5, 0.5]
        
        if hrv:
            hrv_sig = self.lcc.extract_signature_from_hrv(hrv)
            gile = [(g + h) / 2 for g, h in zip(gile, hrv_sig.gile_vector)]
        
        if eeg:
            eeg_sig = self.lcc.extract_signature_from_eeg(eeg)
            gile = [(g + e) / 2 for g, e in zip(gile, eeg_sig.gile_vector)]
        
        if subjective:
            subj_gile = [
                subjective.get('clarity', 0.5),
                subjective.get('intuition', 0.5),
                subjective.get('love', 0.5),
                subjective.get('energy', 0.5)
            ]
            gile = [(g + s) / 2 for g, s in zip(gile, subj_gile)]
        
        datapoint['gile'] = gile
        self.current_session.biometric_timeline.append(datapoint)
        self.current_session.gile_trajectory.append(gile)
        
        return datapoint
    
    def record_post_intervention(self, biowell_data: Dict = None,
                                  hrv_data: Dict = None,
                                  eeg_data: Dict = None) -> Dict:
        """
        Record post-intervention measurements and calculate changes
        """
        if self.current_session is None:
            raise ValueError("No active session.")
        
        signatures = []
        
        if biowell_data:
            sig = self.lcc.extract_signature_from_biowell(biowell_data)
            signatures.append(sig)
            print(f"[POST] BioWell GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if hrv_data:
            sig = self.lcc.extract_signature_from_hrv(hrv_data)
            signatures.append(sig)
            print(f"[POST] HRV GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if eeg_data:
            sig = self.lcc.extract_signature_from_eeg(eeg_data)
            signatures.append(sig)
            print(f"[POST] EEG GILE: {[f'{v:.2f}' for v in sig.gile_vector]}")
        
        if signatures:
            avg_gile = np.mean([s.gile_vector for s in signatures], axis=0).tolist()
            avg_chakra = np.mean([s.chakra_pattern for s in signatures], axis=0).tolist()
            
            post_sig = ICellSignature(
                source='post_combined',
                gile_vector=avg_gile,
                chakra_pattern=avg_chakra,
                polarity_pattern=signatures[0].polarity_pattern,
                de_shell_integrity=np.mean([s.de_shell_integrity for s in signatures]),
                gm_resonance=np.mean([s.gm_resonance for s in signatures]),
                timestamp=datetime.now().isoformat(),
                raw_hash='post_' + self.current_session.session_id
            )
            
            self.current_session.post_icell = post_sig
            self.current_session.gile_trajectory.append(avg_gile)
            
            if self.current_session.baseline_icell:
                baseline = self.current_session.baseline_icell.gile_vector
                delta = [p - b for p, b in zip(avg_gile, baseline)]
                
                print(f"\n[GILE CHANGE]")
                print(f"G: {baseline[0]:.2f} → {avg_gile[0]:.2f} ({delta[0]:+.2f})")
                print(f"I: {baseline[1]:.2f} → {avg_gile[1]:.2f} ({delta[1]:+.2f})")
                print(f"L: {baseline[2]:.2f} → {avg_gile[2]:.2f} ({delta[2]:+.2f})")
                print(f"E: {baseline[3]:.2f} → {avg_gile[3]:.2f} ({delta[3]:+.2f})")
                
                expected = self.INTERVENTION_TYPES[self.current_session.intervention_type]['expected_gile_shift']
                effectiveness = [d / e if e != 0 else 0 for d, e in zip(delta, expected)]
                avg_effectiveness = np.mean([e for e in effectiveness if e > 0])
                
                return {
                    'baseline_gile': baseline,
                    'post_gile': avg_gile,
                    'delta_gile': delta,
                    'expected_shift': expected,
                    'effectiveness': float(avg_effectiveness),
                    'verdict': self._effectiveness_verdict(avg_effectiveness)
                }
        
        return None
    
    def _effectiveness_verdict(self, effectiveness: float) -> str:
        if effectiveness > 1.5:
            return "HIGHLY EFFECTIVE - Exceeded expectations!"
        elif effectiveness > 1.0:
            return "EFFECTIVE - Met or exceeded expectations"
        elif effectiveness > 0.7:
            return "MODERATELY EFFECTIVE - Partial success"
        elif effectiveness > 0.3:
            return "MINIMALLY EFFECTIVE - Below expectations"
        else:
            return "NOT EFFECTIVE - No significant change"
    
    def end_experiment(self) -> Dict:
        """
        End the current experiment and generate summary
        """
        if self.current_session is None:
            raise ValueError("No active session.")
        
        self.current_session.end_time = datetime.now().isoformat()
        
        gile_trajectory = np.array(self.current_session.gile_trajectory)
        
        if len(gile_trajectory) > 1:
            gile_variance = np.var(gile_trajectory, axis=0).tolist()
            gile_range = (np.max(gile_trajectory, axis=0) - np.min(gile_trajectory, axis=0)).tolist()
        else:
            gile_variance = [0, 0, 0, 0]
            gile_range = [0, 0, 0, 0]
        
        if self.current_session.baseline_icell and self.current_session.post_icell:
            correspondence = self.lcc.calculate_correspondence(
                self.current_session.baseline_icell,
                self.current_session.post_icell
            )
            icell_stable = correspondence['total_correspondence'] > 0.7
        else:
            correspondence = None
            icell_stable = None
        
        summary = {
            'session_id': self.current_session.session_id,
            'intervention': self.current_session.intervention_type,
            'duration_datapoints': len(self.current_session.biometric_timeline),
            'devices_used': self.current_session.devices,
            'gile_variance': gile_variance,
            'gile_range': gile_range,
            'icell_stable': icell_stable,
            'baseline_post_correspondence': correspondence,
            'notes': self.current_session.notes
        }
        
        self.session_history.append(self.current_session)
        
        print(f"\n{'='*60}")
        print("EXPERIMENT SESSION ENDED")
        print(f"{'='*60}")
        print(f"Session ID: {self.current_session.session_id}")
        print(f"Duration: {self.current_session.start_time} to {self.current_session.end_time}")
        print(f"Datapoints: {summary['duration_datapoints']}")
        print(f"GILE Variance: {[f'{v:.3f}' for v in gile_variance]}")
        print(f"GILE Range: {[f'{v:.3f}' for v in gile_range]}")
        if icell_stable is not None:
            print(f"I-Cell Stable: {icell_stable}")
        print(f"{'='*60}\n")
        
        self.current_session = None
        
        return summary
    
    def simulate_experiment_run(self):
        """
        Simulate a complete experiment run for testing
        """
        print("\n" + "="*70)
        print("MOOD AMPLIFIER EXPERIMENT - SIMULATION")
        print("="*70)
        
        session = self.start_experiment(
            intervention_type='mood_amplifier',
            devices=['mendi', 'polar_h10', 'biowell'],
            notes="Testing whole-body intervention with EEG + HRV"
        )
        
        baseline_biowell = {
            'stress': 6.68,
            'energy': 22.98,
            'left_balance': 40.63,
            'right_balance': 90.63,
            'lifestyle': {
                'Physical activity': 64,
                'Nutrition': 36,
                'Environment': 91,
                'Psychology': 36,
                'Regime of the day': 34,
                'Hormonal activity': 82
            },
            'nervous_centers': {
                1: {'energy': 2.69, 'alignment': 97.72},
                2: {'energy': 2.66, 'alignment': -83.92},
                3: {'energy': 2.67, 'alignment': 98.41},
                4: {'energy': 3.22, 'alignment': -84.75},
                5: {'energy': 2.71, 'alignment': 95.39},
                6: {'energy': 2.05, 'alignment': -96.08},
                7: {'energy': 1.88, 'alignment': -85.42}
            }
        }
        
        baseline_hrv = {
            'rmssd': 45,
            'sdnn': 85,
            'lf_hf_ratio': 1.8,
            'coherence': 0.4
        }
        
        baseline_eeg = {
            'alpha_power': 0.25,
            'beta_power': 0.35,
            'theta_power': 0.20,
            'gamma_power': 0.10,
            'delta_power': 0.10,
            'hemispheric_coherence': 0.45,
            'pfc_activation': 0.50
        }
        
        print("\n[PHASE 1: BASELINE RECORDING]")
        self.record_baseline(
            biowell_data=baseline_biowell,
            hrv_data=baseline_hrv,
            eeg_data=baseline_eeg
        )
        
        print("\n[PHASE 2: INTERVENTION (simulating 5 datapoints)]")
        for i in range(5):
            improvement = (i + 1) * 0.05
            self.record_datapoint(
                hrv={
                    'rmssd': 45 + improvement * 20,
                    'sdnn': 85 + improvement * 15,
                    'lf_hf_ratio': 1.8 - improvement * 0.3,
                    'coherence': 0.4 + improvement * 0.15
                },
                eeg={
                    'alpha_power': 0.25 + improvement * 0.1,
                    'beta_power': 0.35 - improvement * 0.05,
                    'theta_power': 0.20 + improvement * 0.08,
                    'gamma_power': 0.10 + improvement * 0.05,
                    'delta_power': 0.10,
                    'hemispheric_coherence': 0.45 + improvement * 0.1,
                    'pfc_activation': 0.50 + improvement * 0.1
                },
                subjective={
                    'clarity': 0.5 + improvement * 0.2,
                    'intuition': 0.5 + improvement * 0.3,
                    'love': 0.5 + improvement * 0.25,
                    'energy': 0.5 + improvement * 0.15
                }
            )
            print(f"  Datapoint {i+1} recorded")
        
        print("\n[PHASE 3: POST-INTERVENTION]")
        post_hrv = {
            'rmssd': 65,
            'sdnn': 105,
            'lf_hf_ratio': 1.2,
            'coherence': 0.65
        }
        
        post_eeg = {
            'alpha_power': 0.40,
            'beta_power': 0.28,
            'theta_power': 0.30,
            'gamma_power': 0.18,
            'delta_power': 0.08,
            'hemispheric_coherence': 0.62,
            'pfc_activation': 0.68
        }
        
        results = self.record_post_intervention(
            hrv_data=post_hrv,
            eeg_data=post_eeg
        )
        
        print(f"\nIntervention Effectiveness: {results['effectiveness']:.1%}")
        print(f"Verdict: {results['verdict']}")
        
        summary = self.end_experiment()
        
        return summary


def run_today_experiment():
    """Initialize today's experiment hub"""
    hub = MoodAmplifierExperimentHub()
    
    print("="*70)
    print("MOOD AMPLIFIER EXPERIMENT HUB")
    print("November 25, 2025")
    print("="*70)
    print("\nAvailable Interventions:")
    for name, info in hub.INTERVENTION_TYPES.items():
        print(f"  - {name}: {info['description']}")
    
    print("\nConnected Devices:")
    for name, info in hub.CONNECTED_DEVICES.items():
        print(f"  - {name} ({info['type']}): {', '.join(info['measures'])}")
    
    print("\n" + "="*70)
    print("Running simulation...")
    print("="*70)
    
    summary = hub.simulate_experiment_run()
    
    return hub, summary


if __name__ == "__main__":
    hub, summary = run_today_experiment()
