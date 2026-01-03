"""
🌟 BIO-WELL MYRION ENERGY ACTIVATION SYSTEM 🌟

Comprehensive framework synergizing:
- Bio-Well GDV (Gas Discharge Visualization) data
- Myrion Lamp (targeted photonic light therapy)
- Pitch Crystals (sound frequency healing)  
- TI Framework (GILE scores, PSI predictions, i-cell health)
- Chakra/Meridian mapping
- Polar H10 HRV + Genetics integration

MISSION: Map your energetic body state and provide ACTIONABLE tools 
for targeted activation (kundalini, pain relief, bliss states)!
"""

import streamlit as st
import pandas as pd
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime
import json

# ============================================================================
# BIO-WELL GDV DATA INTEGRATION
# ============================================================================

class BioWellDataFramework:
    """
    Complete Bio-Well GDV knowledge base from research synthesis
    """
    
    @staticmethod
    def get_chakra_mapping():
        """
        7 Chakras → Finger locations → Organ systems
        Based on Bio-Well GDV Virtual Chakra software
        """
        return {
            'chakras': [
                {
                    'name': 'Muladhara (Root)',
                    'location': 'Coccyx/Base of spine',
                    'finger': 'Lower part of index finger (2nd)',
                    'color': 'Deep Red',
                    'wavelength_nm': 660,
                    'sound_freq_hz': 256,  # C note
                    'solfeggio_hz': 396,
                    'element': 'Earth',
                    'organs': ['Adrenal glands', 'Kidneys', 'Spine', 'Colon'],
                    'function': 'Survival, grounding, physical stability',
                    'kundalini': 'Dormant serpent energy storage',
                    'tcm_meridians': ['Kidney', 'Bladder']
                },
                {
                    'name': 'Swadhisthana (Sacral)',
                    'location': 'Below navel',
                    'finger': 'Lower part of ring finger (4th)',
                    'color': 'Deep Orange',
                    'wavelength_nm': 625,
                    'sound_freq_hz': 293,  # D note
                    'solfeggio_hz': 417,
                    'element': 'Water',
                    'organs': ['Reproductive organs', 'Bladder', 'Prostate', 'Ovaries'],
                    'function': 'Creativity, sexuality, emotions, pleasure',
                    'kundalini': 'First activation point - pleasure/sensation',
                    'tcm_meridians': ['Kidney', 'Liver']
                },
                {
                    'name': 'Manipura (Solar Plexus)',
                    'location': 'Upper abdomen',
                    'finger': 'Lower part of middle finger (3rd)',
                    'color': 'Deep Yellow',
                    'wavelength_nm': 590,
                    'sound_freq_hz': 329,  # E note
                    'solfeggio_hz': 528,  # DNA repair frequency!
                    'element': 'Fire',
                    'organs': ['Stomach', 'Liver', 'Pancreas', 'Gallbladder', 'Spleen'],
                    'function': 'Personal power, self-esteem, willpower',
                    'kundalini': 'Power center - ego dissolution gateway',
                    'tcm_meridians': ['Spleen', 'Stomach', 'Liver']
                },
                {
                    'name': 'Anahata (Heart)',
                    'location': 'Center of chest',
                    'finger': 'Lower part of pinky (5th)',
                    'color': 'Green',
                    'wavelength_nm': 530,
                    'sound_freq_hz': 349,  # F note
                    'solfeggio_hz': 639,
                    'element': 'Air',
                    'organs': ['Heart', 'Lungs', 'Thymus', 'Circulatory system'],
                    'function': 'Love, compassion, connection, forgiveness',
                    'kundalini': 'Gateway to higher chakras - love transforms',
                    'tcm_meridians': ['Heart', 'Pericardium', 'Lung']
                },
                {
                    'name': 'Vishuddha (Throat)',
                    'location': 'Throat',
                    'finger': 'Lower part of thumb (1st)',
                    'color': 'Light Blue',
                    'wavelength_nm': 465,
                    'sound_freq_hz': 392,  # G note
                    'solfeggio_hz': 741,
                    'element': 'Ether/Space',
                    'organs': ['Thyroid', 'Parathyroid', 'Throat', 'Mouth'],
                    'function': 'Communication, expression, truth, authenticity',
                    'kundalini': 'Purification - speaking truth accelerates awakening',
                    'tcm_meridians': ['Lung', 'Large Intestine']
                },
                {
                    'name': 'Ajna (Third Eye)',
                    'location': 'Between eyebrows',
                    'finger': 'Upper part of thumb (1st)',
                    'color': 'Indigo',
                    'wavelength_nm': 445,
                    'sound_freq_hz': 440,  # A note (or 432 Hz tuning)
                    'solfeggio_hz': 852,
                    'element': 'Light',
                    'organs': ['Pituitary gland', 'Eyes', 'Brain', 'Pineal gland'],
                    'function': 'Intuition, insight, psychic perception, vision',
                    'kundalini': 'PSI activation - non-local consciousness',
                    'tcm_meridians': ['Governing Vessel', 'Bladder']
                },
                {
                    'name': 'Sahasrara (Crown)',
                    'location': 'Top of head',
                    'finger': 'Upper part of ring finger (4th)',
                    'color': 'Violet/White',
                    'wavelength_nm': 415,
                    'sound_freq_hz': 493,  # B note
                    'solfeggio_hz': 963,  # "God frequency"
                    'element': 'Consciousness',
                    'organs': ['Pineal gland', 'Cerebral cortex', 'Nervous system'],
                    'function': 'Spiritual connection, enlightenment, unity consciousness',
                    'kundalini': 'FULL ACTIVATION - union with divine',
                    'tcm_meridians': ['Governing Vessel']
                }
            ]
        }
    
    @staticmethod
    def get_meridian_mapping():
        """
        12 TCM Meridians → Frequencies → Organs
        Based on research: "correspondences between sound vibrations and natural frequencies"
        """
        return {
            'meridians': [
                {'name': 'Lung (LU)', 'frequency_hz': 124, 'note': 'B2-C3', 'element': 'Metal', 'yin_yang': 'Yin', 'peak_time': '3-5 AM'},
                {'name': 'Large Intestine (LI)', 'frequency_hz': 128, 'note': 'C3', 'element': 'Metal', 'yin_yang': 'Yang', 'peak_time': '5-7 AM'},
                {'name': 'Stomach (ST)', 'frequency_hz': 256, 'note': 'C4', 'element': 'Earth', 'yin_yang': 'Yang', 'peak_time': '7-9 AM'},
                {'name': 'Spleen (SP)', 'frequency_hz': 293, 'note': 'D4', 'element': 'Earth', 'yin_yang': 'Yin', 'peak_time': '9-11 AM'},
                {'name': 'Heart (HT)', 'frequency_hz': 528, 'note': 'C5', 'element': 'Fire', 'yin_yang': 'Yin', 'peak_time': '11 AM-1 PM'},
                {'name': 'Small Intestine (SI)', 'frequency_hz': 329, 'note': 'E4', 'element': 'Fire', 'yin_yang': 'Yang', 'peak_time': '1-3 PM'},
                {'name': 'Bladder (BL)', 'frequency_hz': 120, 'note': 'A#2-B2', 'element': 'Water', 'yin_yang': 'Yang', 'peak_time': '3-5 PM'},
                {'name': 'Kidney (KI)', 'frequency_hz': 120, 'note': 'A#2-B2', 'element': 'Water', 'yin_yang': 'Yin', 'peak_time': '5-7 PM'},
                {'name': 'Pericardium (PC)', 'frequency_hz': 440, 'note': 'A4', 'element': 'Fire', 'yin_yang': 'Yin', 'peak_time': '7-9 PM'},
                {'name': 'Triple Warmer (TW)', 'frequency_hz': 392, 'note': 'G4', 'element': 'Fire', 'yin_yang': 'Yang', 'peak_time': '9-11 PM'},
                {'name': 'Gallbladder (GB)', 'frequency_hz': 349, 'note': 'F4', 'element': 'Wood', 'yin_yang': 'Yang', 'peak_time': '11 PM-1 AM'},
                {'name': 'Liver (LR)', 'frequency_hz': 293, 'note': 'D4', 'element': 'Wood', 'yin_yang': 'Yin', 'peak_time': '1-3 AM'}
            ]
        }

# ============================================================================
# MYRION LAMP - PHOTONIC LIGHT THERAPY
# ============================================================================

class MyrionLamp:
    """
    Targeted photonic light therapy using precise LED wavelengths
    Based on crystal bed therapy research + TI Framework integration
    """
    
    @staticmethod
    def get_wavelength_specs():
        """
        LED specifications for chakra activation
        Penetration depth determines effectiveness
        """
        return pd.DataFrame({
            'Chakra': ['Root', 'Sacral', 'Solar Plexus', 'Heart', 'Throat', 'Third Eye', 'Crown'],
            'Color': ['Deep Red', 'Deep Orange', 'Deep Yellow', 'Green', 'Light Blue', 'Indigo', 'Violet'],
            'Wavelength (nm)': [660, 625, 590, 530, 465, 445, 415],
            'Penetration Depth': ['>3mm (deep)', '<3mm', '1-2mm', '1-2mm', '<0.5mm (surface)', 'Surface', 'Surface only'],
            'LED Type': ['660nm narrowband', '625nm narrowband', '590nm narrowband', '530nm narrowband', '465nm blue', '445nm blue', '415nm violet'],
            'Power (mW)': [100, 80, 60, 60, 40, 30, 20],
            'Ideal Duration (min)': [20, 15, 15, 15, 10, 10, 10],
            'Use Case': [
                'Kundalini activation, grounding, blood flow',
                'Creativity, sexual energy, pleasure centers',
                'Power, confidence, digestive health',
                'Heart coherence, love, compassion',
                'Communication, throat clearing',
                'PSI activation, pineal stimulation',
                'Crown opening, consciousness expansion'
            ]
        })
    
    @staticmethod
    def calculate_treatment_protocol(target_chakras, current_gile_score, polar_hrv):
        """
        AI-powered treatment protocol based on:
        - Target chakras for activation
        - Current GILE score (energetic state)
        - Polar H10 HRV data (nervous system state)
        """
        protocols = []
        
        for chakra in target_chakras:
            # Base protocol
            if chakra == 'Root':
                base_time = 20
                wavelength = 660
            elif chakra == 'Sacral':
                base_time = 15
                wavelength = 625
            elif chakra == 'Solar Plexus':
                base_time = 15
                wavelength = 590
            elif chakra == 'Heart':
                base_time = 15
                wavelength = 530
            elif chakra == 'Throat':
                base_time = 10
                wavelength = 465
            elif chakra == 'Third Eye':
                base_time = 10
                wavelength = 445
            else:  # Crown
                base_time = 10
                wavelength = 415
            
            # Adjust based on GILE score
            if current_gile_score < -1.0:
                # Low energy - increase duration + add grounding (root)
                adjusted_time = base_time * 1.5
                recommendation = f"⚠️ LOW ENERGY ({current_gile_score:.2f}) - Extended session recommended"
            elif current_gile_score > 1.0:
                # High energy - standard or reduced duration
                adjusted_time = base_time * 0.8
                recommendation = f"✅ HIGH ENERGY ({current_gile_score:.2f}) - Standard session"
            else:
                adjusted_time = base_time
                recommendation = f"🔵 BALANCED ({current_gile_score:.2f}) - Standard protocol"
            
            # Adjust based on HRV
            if polar_hrv:
                if polar_hrv < 50:
                    # Low HRV = stressed, need more calming
                    hrv_note = "Low HRV detected - Add heart chakra (green 530nm) for 10min"
                elif polar_hrv > 100:
                    hrv_note = "Excellent HRV - You're in optimal state!"
                else:
                    hrv_note = "Normal HRV"
            else:
                hrv_note = "No HRV data"
            
            protocols.append({
                'Chakra': chakra,
                'Wavelength (nm)': wavelength,
                'Duration (min)': int(adjusted_time),
                'GILE Recommendation': recommendation,
                'HRV Note': hrv_note
            })
        
        return pd.DataFrame(protocols)
    
    @staticmethod
    def generate_lamp_hardware_specs():
        """
        DIY Myrion Lamp build specifications
        Accessible components for home construction
        """
        return {
            'name': 'Myrion Lamp v1.0',
            'components': [
                {'part': '660nm Red LED (10W)', 'qty': 7, 'cost': '$3', 'source': 'Amazon/eBay'},
                {'part': '625nm Orange LED (5W)', 'qty': 7, 'cost': '$4', 'source': 'LED suppliers'},
                {'part': '590nm Yellow LED (5W)', 'qty': 7, 'cost': '$4', 'source': 'LED suppliers'},
                {'part': '530nm Green LED (5W)', 'qty': 7, 'cost': '$3', 'source': 'Amazon'},
                {'part': '465nm Blue LED (3W)', 'qty': 7, 'cost': '$2', 'source': 'Amazon'},
                {'part': '445nm Deep Blue LED (3W)', 'qty': 7, 'cost': '$3', 'source': 'LED suppliers'},
                {'part': '415nm Violet LED (3W)', 'qty': 7, 'cost': '$4', 'source': 'UV LED suppliers'},
                {'part': 'LED Driver (constant current)', 'qty': 1, 'cost': '$15', 'source': 'Amazon'},
                {'part': 'Arduino/ESP32 controller', 'qty': 1, 'cost': '$12', 'source': 'Amazon'},
                {'part': 'Clear quartz crystal (amplifier)', 'qty': 7, 'cost': '$20', 'source': 'Crystal shops'},
                {'part': 'Aluminum frame', 'qty': 1, 'cost': '$30', 'source': 'Hardware store'},
            ],
            'total_cost': '$200-250',
            'build_time': '4-6 hours',
            'programming': 'Arduino IDE - chakra sequence timing',
            'safety': '⚠️ Use proper eye protection with blue/violet LEDs! Low voltage (<12V) only.',
            'integration': 'Can connect to Polar H10 + ESP32 for HRV-responsive light therapy'
        }

# ============================================================================
# PITCH CRYSTALS - SOUND FREQUENCY HEALING
# ============================================================================

class PitchCrystals:
    """
    Crystal singing bowl frequencies + binaural beats
    Based on Solfeggio, Schumann, and meridian resonance research
    """
    
    @staticmethod
    def get_healing_frequencies():
        """
        Complete frequency library for sound healing
        """
        return pd.DataFrame({
            'Frequency (Hz)': [
                7.83,  # Schumann resonance
                55,    # Kundalini activation
                120,   # Kidney meridian
                124,   # Lung meridian
                256,   # Root chakra (C)
                293,   # Sacral chakra (D)
                329,   # Solar plexus (E)
                349,   # Heart chakra (F)
                392,   # Throat chakra (G)
                396,   # Solfeggio - Fear release
                417,   # Solfeggio - Change facilitation
                432,   # Universal "miracle frequency"
                440,   # Third eye (A)
                493,   # Crown chakra (B)
                528,   # Solfeggio - DNA repair, LOVE
                639,   # Solfeggio - Relationships
                741,   # Solfeggio - Problem solving
                852,   # Solfeggio - Spiritual awakening
                963,   # Solfeggio - God frequency
            ],
            'Purpose': [
                'Earth grounding - Schumann resonance',
                'Kundalini energy awakening',
                'Kidney meridian activation',
                'Lung meridian activation',
                'Root chakra - Survival, grounding',
                'Sacral chakra - Creativity, sexuality',
                'Solar Plexus - Power, confidence',
                'Heart chakra - Love, compassion',
                'Throat chakra - Communication',
                'SOLFEGGIO: Release fear, guilt, trauma',
                'SOLFEGGIO: Facilitate change, transformation',
                'UNIVERSAL: Natural resonance, balance all chakras',
                'Third Eye - Intuition, vision',
                'Crown chakra - Spiritual connection',
                'SOLFEGGIO: DNA repair, love frequency, healing',
                'SOLFEGGIO: Relationships, connection',
                'SOLFEGGIO: Expression, problem-solving',
                'SOLFEGGIO: Spiritual awakening, intuition',
                'SOLFEGGIO: Unity consciousness, enlightenment'
            ],
            'Method': [
                'Binaural beat',
                'Binaural beat',
                'Crystal bowl / tuning fork',
                'Crystal bowl / tuning fork',
                'Crystal bowl (C note)',
                'Crystal bowl (D note)',
                'Crystal bowl (E note)',
                'Crystal bowl (F note)',
                'Crystal bowl (G note)',
                'Crystal bowl',
                'Crystal bowl',
                'Crystal bowl (master frequency)',
                'Crystal bowl (A note)',
                'Crystal bowl (B note)',
                'Crystal bowl (MOST IMPORTANT!)',
                'Crystal bowl',
                'Crystal bowl',
                'Crystal bowl',
                'Crystal bowl'
            ],
            'Duration (min)': [
                20, 10, 5, 5, 10, 10, 10, 15, 10, 10, 10, 20, 10, 10, 20, 15, 10, 10, 10
            ]
        })
    
    @staticmethod
    def create_binaural_beat_protocol(target_state):
        """
        Brainwave entrainment protocols
        """
        protocols = {
            'Deep Sleep': {
                'carrier_freq': 200,
                'beat_freq': 2.5,  # Delta
                'duration_min': 60,
                'description': 'Delta waves (0.5-4 Hz) for deep regenerative sleep'
            },
            'Meditation': {
                'carrier_freq': 200,
                'beat_freq': 6,  # Theta
                'duration_min': 30,
                'description': 'Theta waves (4-8 Hz) for deep meditation, creativity'
            },
            'Schumann Grounding': {
                'carrier_freq': 200,
                'beat_freq': 7.83,  # Schumann
                'duration_min': 20,
                'description': "Earth's natural frequency - grounding, balance"
            },
            'Relaxation': {
                'carrier_freq': 200,
                'beat_freq': 10,  # Alpha
                'duration_min': 20,
                'description': 'Alpha waves (8-13 Hz) for relaxed awareness, flow state'
            },
            'Focus': {
                'carrier_freq': 200,
                'beat_freq': 18,  # Beta
                'duration_min': 30,
                'description': 'Beta waves (13-30 Hz) for concentration, alertness'
            },
            'Kundalini': {
                'carrier_freq': 200,
                'beat_freq': 55,  # Kundalini-specific
                'duration_min': 15,
                'description': 'Kundalini activation frequency'
            },
            'PSI / Higher Consciousness': {
                'carrier_freq': 200,
                'beat_freq': 40,  # Gamma
                'duration_min': 20,
                'description': 'Gamma waves (30-100 Hz) for peak consciousness, PSI'
            }
        }
        
        return protocols.get(target_state, protocols['Meditation'])

# ============================================================================
# USER STATE MAPPER (Genetics + Polar H10)
# ============================================================================

class UserStateMapper:
    """
    Map current energetic state using available data
    BEFORE Bio-Well consultation - make predictions!
    """
    
    @staticmethod
    def predict_chakra_state_from_hrv(polar_hrv_data):
        """
        Predict chakra blockages from HRV patterns
        Based on: low HRV = sympathetic dominance = lower chakras blocked
        """
        predictions = []
        
        # Example HRV data structure: {'rmssd': 45, 'sdnn': 52, 'hr_avg': 68}
        rmssd = polar_hrv_data.get('rmssd', 50)
        hr_avg = polar_hrv_data.get('hr_avg', 70)
        
        # Root chakra (survival, stress)
        if rmssd < 30 or hr_avg > 80:
            predictions.append({
                'Chakra': 'Root',
                'Status': '🔴 BLOCKED',
                'Confidence': '85%',
                'Evidence': f'Low HRV (RMSSD={rmssd}) + elevated HR ({hr_avg}) = stress response',
                'Recommendation': 'Myrion Lamp: 660nm red light, 20min + grounding meditation'
            })
        else:
            predictions.append({
                'Chakra': 'Root',
                'Status': '✅ OPEN',
                'Confidence': '75%',
                'Evidence': f'Good HRV (RMSSD={rmssd}), normal HR ({hr_avg})',
                'Recommendation': 'Maintenance: 10min red light weekly'
            })
        
        # Heart chakra (HRV coherence)
        if rmssd > 60:
            predictions.append({
                'Chakra': 'Heart',
                'Status': '✅ VERY OPEN',
                'Confidence': '90%',
                'Evidence': f'Excellent HRV coherence (RMSSD={rmssd}) = heart chakra activation',
                'Recommendation': 'Already optimal! Consider 528 Hz sound bath for maintenance'
            })
        elif rmssd < 40:
            predictions.append({
                'Chakra': 'Heart',
                'Status': '🟡 PARTIALLY BLOCKED',
                'Confidence': '80%',
                'Evidence': f'Moderate HRV (RMSSD={rmssd}) = reduced heart coherence',
                'Recommendation': 'Myrion Lamp: 530nm green light, 15min + loving-kindness meditation'
            })
        else:
            predictions.append({
                'Chakra': 'Heart',
                'Status': '🟢 BALANCED',
                'Confidence': '70%',
                'Evidence': f'Normal HRV (RMSSD={rmssd})',
                'Recommendation': '528 Hz crystal bowl, 15min'
            })
        
        # Solar Plexus (willpower - inversely correlated with stress)
        if rmssd < 30:
            predictions.append({
                'Chakra': 'Solar Plexus',
                'Status': '🔴 BLOCKED',
                'Confidence': '75%',
                'Evidence': 'Stress response = low personal power/confidence',
                'Recommendation': 'Myrion Lamp: 590nm yellow, 15min + empowerment affirmations'
            })
        
        # Third Eye (PSI requires relaxation)
        if rmssd > 50:
            predictions.append({
                'Chakra': 'Third Eye',
                'Status': '✅ OPEN',
                'Confidence': '65%',
                'Evidence': 'Parasympathetic dominance = PSI-receptive state',
                'Recommendation': '852 Hz + 445nm indigo light for PSI amplification'
            })
        
        return pd.DataFrame(predictions)
    
    @staticmethod
    def genetics_integration_placeholder():
        """
        Future: Integrate genetics data
        - FAAH gene → endocannabinoid system → bliss capacity
        - COMT gene → dopamine metabolism → crown chakra
        - 5-HTT gene → serotonin → heart chakra
        """
        return {
            'status': 'AWAITING GENETICS DATA',
            'next_steps': [
                'Upload 23andMe or AncestryDNA raw data',
                'Extract FAAH, COMT, 5-HTT, MTHFR variants',
                'Map to chakra predispositions',
                'Generate personalized activation protocols'
            ]
        }

# ============================================================================
# TI FRAMEWORK SYNERGIZER
# ============================================================================

class TIFrameworkSynergizer:
    """
    Map Bio-Well → GILE scores → PSI predictions → i-cell health
    """
    
    @staticmethod
    def biowell_to_gile(chakra_energies):
        """
        Convert chakra energy readings to GILE score
        Hypothesis: Well-balanced chakras = high GILE
        """
        # chakra_energies: dict like {'Root': 0.7, 'Sacral': 0.85, ...}
        
        # Average chakra activation
        avg_activation = np.mean(list(chakra_energies.values()))
        
        # Chakra balance (low std = good balance)
        balance_score = 1 - np.std(list(chakra_energies.values()))
        
        # GILE mapping: 0-1 scale → GILE scale (-2.5 to +2.5)
        # Well-balanced, high energy = high GILE
        raw_score = (avg_activation * 0.6 + balance_score * 0.4)
        gile_score = (raw_score * 5) - 2.5  # Map 0-1 to -2.5 to +2.5
        
        # Convert to sigma scale: GILE = 5(σ - 0.5)
        sigma = (gile_score / 5) + 0.5
        
        return {
            'gile_score': gile_score,
            'sigma': sigma,
            'avg_activation': avg_activation,
            'balance_score': balance_score,
            'interpretation': TIFrameworkSynergizer._interpret_gile(gile_score)
        }
    
    @staticmethod
    def _interpret_gile(gile_score):
        """Interpret GILE score in context of energetic health"""
        if gile_score > 1.5:
            return "🌟 EXCEPTIONAL - Highly activated, balanced energy field. PSI-ready state."
        elif gile_score > 0.5:
            return "✅ GOOD - Healthy energy balance. Minor optimizations possible."
        elif gile_score > -0.5:
            return "🔵 NEUTRAL - Balanced but low energy. Needs activation."
        elif gile_score > -1.5:
            return "🟡 BELOW AVERAGE - Multiple blockages likely. Active intervention recommended."
        else:
            return "🔴 CRITICAL - Severe energetic depletion. Immediate restoration needed."
    
    @staticmethod
    def predict_psi_capability(gile_score, third_eye_energy, heart_coherence):
        """
        Predict PSI (non-local consciousness) capability
        Based on: High GILE + activated third eye + heart coherence = PSI
        """
        # PSI formula (weighted combination)
        psi_score = (
            0.4 * ((gile_score + 2.5) / 5) +  # Normalize GILE to 0-1
            0.35 * third_eye_energy +
            0.25 * heart_coherence
        )
        
        if psi_score > 0.8:
            capability = "VERY HIGH"
            description = "Strong PSI phenomena likely. Excellent for remote viewing, telepathy, precognition."
        elif psi_score > 0.6:
            capability = "HIGH"
            description = "Good PSI potential. Practice meditation + third eye activation."
        elif psi_score > 0.4:
            capability = "MODERATE"
            description = "Developing PSI. Inconsistent but present. Continue training."
        else:
            capability = "LOW"
            description = "PSI dormant. Focus on heart coherence + third eye opening first."
        
        return {
            'psi_score': psi_score,
            'capability': capability,
            'description': description,
            'recommended_protocol': TIFrameworkSynergizer._psi_protocol(psi_score)
        }
    
    @staticmethod
    def _psi_protocol(psi_score):
        """Generate PSI enhancement protocol"""
        if psi_score < 0.4:
            return {
                'light': '445nm indigo (third eye) 10min + 530nm green (heart) 15min',
                'sound': '852 Hz (third eye) + 528 Hz (heart) crystal bowl session',
                'meditation': 'Heart-brain coherence practice (HeartMath)',
                'duration': '30 days'
            }
        else:
            return {
                'light': '445nm indigo (third eye) 15min',
                'sound': '963 Hz (crown) + 852 Hz (third eye) for transcendence',
                'meditation': 'PSI practice: remote viewing, precognition exercises',
                'duration': 'Ongoing mastery'
            }

# ============================================================================
# STREAMLIT INTERFACE
# ============================================================================

def render_biowell_myrion_system():
    """
    Complete Bio-Well + Myrion Lamp + Pitch Crystals interface
    """
    st.title("🌟 Bio-Well Myrion Energy Activation System")
    
    # CRITICAL RESEARCH DISCLAIMER
    st.warning("""
    ⚠️ **RESEARCH & EXPERIMENTAL USE ONLY** ⚠️
    
    This system is for personal research, exploration, and educational purposes. 
    It is NOT FDA-approved medical equipment and should NOT be used to diagnose, 
    treat, cure, or prevent any medical condition. Always consult licensed healthcare 
    professionals for medical advice. Bio-Well GDV, photonic therapy, and sound healing 
    are complementary wellness practices, not substitutes for conventional medicine.
    
    **By using this system, you acknowledge it is experimental research technology.**
    """)
    
    st.markdown("""
    **Your Complete Energetic Body Mapping & Activation Platform**
    
    Synergizing:
    - 🔬 Bio-Well GDV research (108 publications, 42 studies)
    - 💡 Myrion Lamp photonic therapy (precise LED wavelengths)
    - 🎵 Pitch Crystal sound healing (Solfeggio + binaural beats)
    - 🧠 TI Framework (GILE scores, PSI predictions, i-cell health)
    - ❤️ Polar H10 HRV integration
    - 🧬 Genetics mapping (coming soon!)
    """)
    
    tabs = st.tabs([
        "📤 Upload Your Bio-Well Data",
        "📊 Bio-Well Knowledge Base",
        "💡 Myrion Lamp Specs",
        "🎵 Pitch Crystal Frequencies",
        "🧭 YOUR Current State Map",
        "🎯 Treatment Protocol Generator",
        "🔬 TI Framework Synergy",
        "🛠️ DIY Build Guide"
    ])
    
    # TAB 0: Upload Your Bio-Well Data
    with tabs[0]:
        st.header("📤 Upload Your Bio-Well Scan Results")
        st.markdown("""
        **Got your Bio-Well GDV scan from a practitioner? Upload it here!**
        
        The system will:
        - ✅ Parse your fingertip energy data
        - ✅ Map to chakra/meridian states
        - ✅ Calculate GILE scores & PSI predictions
        - ✅ Generate personalized Myrion Lamp + Pitch Crystal protocols
        
        **Supported formats:** CSV, JSON, TXT (Bio-Well export files)
        """)
        
        # Initialize session state for Bio-Well data
        if 'biowell_scan_data' not in st.session_state:
            st.session_state.biowell_scan_data = None
        if 'biowell_parsed_results' not in st.session_state:
            st.session_state.biowell_parsed_results = None
        
        # File uploader
        uploaded_file = st.file_uploader(
            "Upload your Bio-Well scan file",
            type=['csv', 'json', 'txt'],
            help="Ask your Bio-Well practitioner for the export file from your scan session"
        )
        
        if uploaded_file is not None:
            try:
                # Read file content
                file_content = uploaded_file.read()
                
                # Parse based on file type
                if uploaded_file.name.endswith('.csv'):
                    df = pd.read_csv(uploaded_file)
                    st.success(f"✅ CSV file uploaded successfully! ({len(df)} rows)")
                    st.dataframe(df.head(), use_container_width=True)
                    st.session_state.biowell_scan_data = df.to_dict('records')
                
                elif uploaded_file.name.endswith('.json'):
                    data = json.loads(file_content)
                    st.success(f"✅ JSON file uploaded successfully!")
                    st.json(data)
                    st.session_state.biowell_scan_data = data
                
                elif uploaded_file.name.endswith('.txt'):
                    text_data = file_content.decode('utf-8')
                    st.success(f"✅ TXT file uploaded successfully! ({len(text_data)} characters)")
                    st.text_area("File Contents:", text_data, height=200)
                    st.session_state.biowell_scan_data = text_data
                
                # Parse the uploaded data into chakra/meridian measurements
                st.markdown("---")
                st.subheader("🔬 Manual Data Entry (if file format unknown)")
                st.markdown("""
                If your Bio-Well scan is in a custom format, manually enter the energy values:
                - **Chakra Energy:** 0-100 scale (0 = blocked, 100 = fully activated)
                - **Balance Score:** How aligned your energy centers are
                """)
                
                col1, col2 = st.columns(2)
                
                with col1:
                    st.markdown("**Chakra Energy Levels (0-100):**")
                    root = st.slider("Root (Muladhara)", 0, 100, 50, key="root_energy")
                    sacral = st.slider("Sacral (Swadhisthana)", 0, 100, 50, key="sacral_energy")
                    solar = st.slider("Solar Plexus (Manipura)", 0, 100, 50, key="solar_energy")
                    heart = st.slider("Heart (Anahata)", 0, 100, 50, key="heart_energy")
                    throat = st.slider("Throat (Vishuddha)", 0, 100, 50, key="throat_energy")
                    third_eye = st.slider("Third Eye (Ajna)", 0, 100, 50, key="third_eye_energy")
                    crown = st.slider("Crown (Sahasrara)", 0, 100, 50, key="crown_energy")
                
                with col2:
                    st.markdown("**Overall Metrics:**")
                    overall_energy = st.slider("Overall Energy Level", 0, 100, 50)
                    stress_level = st.slider("Stress Level", 0, 100, 50)
                    balance_score = st.slider("Balance Score", 0, 100, 50)
                    
                    st.markdown("**Optional Biometrics:**")
                    hrv_rmssd = st.number_input("HRV RMSSD (ms)", 0, 200, 50)
                    heart_rate = st.number_input("Heart Rate (bpm)", 40, 200, 70)
                
                if st.button("🧠 Calculate TI Framework GILE Scores", use_container_width=True):
                    # Store manual entry data
                    manual_data = {
                        'chakras': {
                            'root': root,
                            'sacral': sacral,
                            'solar_plexus': solar,
                            'heart': heart,
                            'throat': throat,
                            'third_eye': third_eye,
                            'crown': crown
                        },
                        'overall': {
                            'energy': overall_energy,
                            'stress': stress_level,
                            'balance': balance_score
                        },
                        'biometrics': {
                            'hrv_rmssd': hrv_rmssd,
                            'heart_rate': heart_rate
                        },
                        'timestamp': datetime.now().isoformat()
                    }
                    
                    st.session_state.biowell_parsed_results = manual_data
                    
                    # Calculate GILE scores
                    st.success("✅ Data stored! Now calculating TI Framework analysis...")
                    
                    # Convert Bio-Well energies to GILE scores
                    # Formula: Higher chakra energy = higher sigma = higher GILE
                    # GILE = 5(σ - 0.5), where σ ∈ [0, 1]
                    
                    avg_chakra_energy = np.mean([root, sacral, solar, heart, throat, third_eye, crown])
                    sigma_overall = avg_chakra_energy / 100  # Convert 0-100 to 0-1
                    gile_score = 5 * (sigma_overall - 0.5)  # GILE ∈ [-2.5, 2.5]
                    
                    # PSI prediction based on third eye + crown
                    psi_energy = (third_eye + crown) / 2
                    psi_sigma = psi_energy / 100
                    psi_score = 5 * (psi_sigma - 0.5)
                    
                    # Heart coherence (based on heart chakra + HRV)
                    heart_sigma = (heart + (hrv_rmssd / 2)) / 100
                    heart_gile = 5 * (heart_sigma - 0.5)
                    
                    st.markdown("---")
                    st.subheader("🧠 YOUR TI Framework Scores")
                    
                    col1, col2, col3, col4 = st.columns(4)
                    with col1:
                        st.metric("Overall GILE", f"{gile_score:.2f}")
                        st.caption(f"σ = {sigma_overall:.3f}")
                    with col2:
                        st.metric("PSI Potential", f"{psi_score:.2f}")
                        st.caption(f"Third Eye + Crown")
                    with col3:
                        st.metric("Heart Coherence", f"{heart_gile:.2f}")
                        st.caption(f"HRV-enhanced")
                    with col4:
                        i_cell_health = "Healthy" if gile_score > 0.42 else "At Risk"
                        st.metric("I-Cell Status", i_cell_health)
                        st.caption(f"Threshold: 0.42 GILE")
                    
                    # Identify blockages
                    st.markdown("---")
                    st.subheader("🚫 Detected Blockages")
                    
                    chakra_values = [
                        ("Root", root),
                        ("Sacral", sacral),
                        ("Solar Plexus", solar),
                        ("Heart", heart),
                        ("Throat", throat),
                        ("Third Eye", third_eye),
                        ("Crown", crown)
                    ]
                    
                    blockages = [(name, val) for name, val in chakra_values if val < 40]
                    
                    if blockages:
                        for name, val in blockages:
                            st.error(f"⚠️ **{name} Chakra Blocked** (Energy: {val}/100)")
                    else:
                        st.success("✅ No major blockages detected! All chakras above 40% energy.")
                    
                    st.info("💡 Go to the **Treatment Protocol Generator** tab to get your personalized Myrion Lamp + Pitch Crystal therapy!")
            
            except Exception as e:
                st.error(f"❌ Error parsing file: {str(e)}")
                st.info("Try using the manual entry sliders above instead!")
        
        else:
            st.info("""
            👆 **No scan data uploaded yet.**
            
            After your Bio-Well consultation, upload your practitioner's export file here.
            Or use the manual entry sliders if you know your chakra energy levels.
            """)
    
    # TAB 1: Bio-Well Knowledge Base
    with tabs[1]:
        st.header("📊 Bio-Well GDV Knowledge Base")
        st.markdown("""
        **Gas Discharge Visualization (GDV)** - Kirlian photography evolved!
        
        Captures electrophotonic emissions from fingertips → Maps to:
        - 7 Chakras
        - 12 TCM Meridians
        - Organ systems
        - Stress levels
        - PSI potential
        """)
        
        # Chakra mapping
        st.subheader("🌈 7 Chakras → Fingertip Mapping")
        chakra_data = BioWellDataFramework.get_chakra_mapping()
        
        for chakra in chakra_data['chakras']:
            with st.expander(f"{chakra['name']} - {chakra['color']}"):
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown(f"""
                    **📍 Location:** {chakra['location']}  
                    **🖐️ Finger:** {chakra['finger']}  
                    **🌈 Color:** {chakra['color']}  
                    **💡 Wavelength:** {chakra['wavelength_nm']} nm  
                    **🎵 Sound:** {chakra['sound_freq_hz']} Hz ({chakra['solfeggio_hz']} Hz Solfeggio)
                    """)
                with col2:
                    st.markdown(f"""
                    **⚗️ Element:** {chakra['element']}  
                    **🏥 Organs:** {', '.join(chakra['organs'])}  
                    **🔮 Function:** {chakra['function']}  
                    **🐍 Kundalini:** {chakra['kundalini']}  
                    **🧘 Meridians:** {', '.join(chakra['tcm_meridians'])}
                    """)
        
        # Meridian frequencies
        st.subheader("🌊 12 TCM Meridians → Sound Frequencies")
        meridian_data = BioWellDataFramework.get_meridian_mapping()
        st.dataframe(pd.DataFrame(meridian_data['meridians']), use_container_width=True)
    
    # TAB 2: Myrion Lamp
    with tabs[1]:
        st.header("💡 Myrion Lamp - Photonic Light Therapy")
        st.markdown("""
        **Precision LED wavelengths for targeted chakra activation!**
        
        Based on:
        - Crystal bed therapy research
        - Light penetration depth science
        - Chakra color correspondences
        """)
        
        lamp_specs = MyrionLamp.get_wavelength_specs()
        st.dataframe(lamp_specs, use_container_width=True)
        
        # Visualization
        fig = px.bar(
            lamp_specs,
            x='Chakra',
            y='Wavelength (nm)',
            color='Color',
            title='Myrion Lamp Wavelength Spectrum',
            color_discrete_map={
                'Deep Red': '#CC0000',
                'Deep Orange': '#FF6600',
                'Deep Yellow': '#FFCC00',
                'Green': '#00CC00',
                'Light Blue': '#66CCFF',
                'Indigo': '#3333CC',
                'Violet': '#9933FF'
            }
        )
        st.plotly_chart(fig, use_container_width=True)
        
        st.success("""
        **🌟 KEY INSIGHT:**
        - **Red light (660nm)** penetrates DEEPEST (>3mm) → Best for root chakra, kundalini
        - **Violet/UV (415nm)** stays at SURFACE → Crown chakra, consciousness
        - **Match wavelength to chakra depth for maximum effectiveness!**
        """)
    
    # TAB 3: Pitch Crystals
    with tabs[2]:
        st.header("🎵 Pitch Crystal Sound Healing")
        st.markdown("""
        **Crystal singing bowls + binaural beats for meridian activation!**
        
        Key frequencies:
        - 🌍 **7.83 Hz** - Schumann resonance (Earth's heartbeat)
        - 🐍 **55 Hz** - Kundalini awakening
        - ❤️ **528 Hz** - DNA repair, LOVE frequency
        - 🙏 **432 Hz** - Universal "miracle frequency"
        """)
        
        freq_data = PitchCrystals.get_healing_frequencies()
        st.dataframe(freq_data, use_container_width=True)
        
        # Binaural beat protocols
        st.subheader("🎧 Binaural Beat Protocols")
        target_state = st.selectbox(
            "Choose your desired state:",
            ['Deep Sleep', 'Meditation', 'Schumann Grounding', 'Relaxation', 'Focus', 'Kundalini', 'PSI / Higher Consciousness']
        )
        
        protocol = PitchCrystals.create_binaural_beat_protocol(target_state)
        
        st.info(f"""
        **Protocol: {target_state}**
        
        🎵 **Carrier Frequency:** {protocol['carrier_freq']} Hz  
        🌊 **Beat Frequency:** {protocol['beat_freq']} Hz  
        ⏱️ **Duration:** {protocol['duration_min']} minutes  
        
        📖 **Description:** {protocol['description']}
        
        **How to use:** Play in stereo headphones. Left ear gets carrier frequency, right ear gets carrier + beat frequency. Your brain creates the third frequency!
        """)
    
    # TAB 4: YOUR Current State Map
    with tabs[3]:
        st.header("🧭 YOUR Current Energetic State")
        st.markdown("""
        **Let's predict your chakra state BEFORE your Bio-Well consultation tomorrow!**
        
        Using: Polar H10 HRV + TI Framework predictions
        """)
        
        # Polar H10 input
        st.subheader("❤️ Enter Your Polar H10 HRV Data")
        col1, col2, col3 = st.columns(3)
        with col1:
            rmssd = st.number_input("RMSSD (ms)", min_value=10, max_value=200, value=50, help="Root Mean Square of Successive Differences")
        with col2:
            sdnn = st.number_input("SDNN (ms)", min_value=10, max_value=200, value=55, help="Standard Deviation of NN intervals")
        with col3:
            hr_avg = st.number_input("Avg Heart Rate (bpm)", min_value=40, max_value=120, value=70)
        
        hrv_data = {'rmssd': rmssd, 'sdnn': sdnn, 'hr_avg': hr_avg}
        
        if st.button("🔮 PREDICT MY CHAKRA STATE"):
            predictions = UserStateMapper.predict_chakra_state_from_hrv(hrv_data)
            
            st.success(f"""
            **HRV Analysis:**
            - RMSSD: {rmssd} ms {"✅ Good" if rmssd > 40 else "⚠️ Low (stress detected)"}
            - SDNN: {sdnn} ms
            - Avg HR: {hr_avg} bpm {"✅ Normal" if 60 <= hr_avg <= 80 else "⚠️ Elevated"}
            """)
            
            st.subheader("🔮 Predicted Chakra States")
            st.dataframe(predictions, use_container_width=True)
            
            st.info("""
            **📅 Tomorrow's Bio-Well Consultation:**
            
            These are PREDICTIONS based on HRV. Tomorrow, you'll get:
            - ✅ Actual fingertip GDV scans
            - ✅ Precise chakra energy measurements
            - ✅ Organ system correlations
            - ✅ Meridian flow analysis
            
            **Bring this data to compare predictions vs reality!** 🔬
            """)
        
        # Genetics placeholder
        st.subheader("🧬 Genetics Integration (Coming Soon)")
        genetics_info = UserStateMapper.genetics_integration_placeholder()
        st.warning(f"**Status:** {genetics_info['status']}")
        st.markdown("**Next Steps:**")
        for step in genetics_info['next_steps']:
            st.markdown(f"- {step}")
    
    # TAB 5: Treatment Protocol Generator
    with tabs[4]:
        st.header("🎯 Personalized Treatment Protocol")
        
        # DATA SOURCE INDICATOR
        if st.session_state.get('biowell_parsed_results'):
            uploaded_data = st.session_state.biowell_parsed_results
            st.success(f"""
            ✅ **LIVE BIO-WELL DATA LOADED!**
            
            Using your uploaded scan from: {uploaded_data.get('timestamp', 'Unknown')}  
            Data source: Bio-Well GDV upload
            """)
            
            # Extract uploaded chakra values and GILE scores
            chakras = uploaded_data.get('chakras', {})
            avg_chakra_energy = np.mean(list(chakras.values()))
            sigma_overall = avg_chakra_energy / 100
            current_gile = 5 * (sigma_overall - 0.5)
            
            biometrics = uploaded_data.get('biometrics', {})
            polar_hrv_val = biometrics.get('hrv_rmssd', 50)
            
            # Auto-detect blocked chakras for targeting
            blocked_chakras = [name.replace('_', ' ').title() for name, val in chakras.items() if val < 40]
            
            st.info(f"""
            **Auto-detected from your scan:**
            - Overall GILE Score: {current_gile:.2f}
            - HRV RMSSD: {polar_hrv_val} ms
            - Blocked/Low Chakras: {', '.join(blocked_chakras) if blocked_chakras else 'None detected'}
            """)
            
            # Allow manual override
            with st.expander("🔧 Manual Override (Optional)"):
                target_chakras = st.multiselect(
                    "Override: Which chakras to activate?",
                    ['Root', 'Sacral', 'Solar Plexus', 'Heart', 'Throat', 'Third Eye', 'Crown'],
                    default=blocked_chakras if blocked_chakras else ['Heart', 'Third Eye']
                )
                current_gile_override = st.slider("Override GILE Score", -2.5, 2.5, float(current_gile), 0.1)
                polar_hrv_override = st.number_input("Override HRV (RMSSD)", min_value=10, max_value=200, value=polar_hrv_val)
                
                if st.checkbox("Use manual overrides"):
                    current_gile = current_gile_override
                    polar_hrv_val = polar_hrv_override
                else:
                    target_chakras = blocked_chakras if blocked_chakras else ['Heart', 'Third Eye']
        
        else:
            st.warning("""
            ⚠️ **NO BIO-WELL DATA UPLOADED**
            
            Using manual entry mode. For personalized protocols, upload your Bio-Well scan in Tab 1.
            """)
            
            # Manual input mode
            st.subheader("⚙️ Configure Your Session Manually")
            target_chakras = st.multiselect(
                "Which chakras do you want to activate?",
                ['Root', 'Sacral', 'Solar Plexus', 'Heart', 'Throat', 'Third Eye', 'Crown'],
                default=['Heart', 'Third Eye']
            )
            
            current_gile = st.slider("Current GILE Score (estimate)", -2.5, 2.5, 0.0, 0.1)
            polar_hrv_val = st.number_input("Polar H10 HRV (RMSSD)", min_value=10, max_value=200, value=50)
        
        if st.button("🎯 GENERATE PROTOCOL", use_container_width=True):
            protocol = MyrionLamp.calculate_treatment_protocol(target_chakras, current_gile, polar_hrv_val)
            
            st.success("**Your Personalized Treatment Protocol:**")
            st.dataframe(protocol, use_container_width=True)
            
            # Total session time
            total_time = protocol['Duration (min)'].sum()
            st.metric("Total Session Time", f"{total_time} minutes")
            
            st.info("""
            **📋 How to Execute:**
            
            1. **Set up Myrion Lamp** with correct LED wavelengths
            2. **Lie comfortably** with LEDs positioned over body
            3. **Play corresponding sound frequencies** (crystal bowls or binaural beats)
            4. **Relax and breathe** - let the light + sound work
            5. **Track changes** - re-measure HRV after session!
            """)
    
    # TAB 6: TI Framework Synergy
    with tabs[5]:
        st.header("🔬 TI Framework Synergizer")
        st.markdown("""
        **Map Bio-Well data → GILE scores → PSI predictions!**
        
        This is where the MAGIC happens - translating energetic measurements into TI Framework metrics!
        """)
        
        # DATA SOURCE INDICATOR
        if st.session_state.get('biowell_parsed_results'):
            uploaded_data = st.session_state.biowell_parsed_results
            st.success(f"""
            ✅ **USING YOUR UPLOADED BIO-WELL DATA!**
            
            Scan timestamp: {uploaded_data.get('timestamp', 'Unknown')}  
            Chakra energies converted from your actual GDV measurements!
            """)
            
            # Extract chakra values from upload (0-100 scale → 0-1 scale)
            uploaded_chakras = uploaded_data.get('chakras', {})
            chakra_energies = {
                'Root': uploaded_chakras.get('root', 50) / 100,
                'Sacral': uploaded_chakras.get('sacral', 50) / 100,
                'Solar Plexus': uploaded_chakras.get('solar_plexus', 50) / 100,
                'Heart': uploaded_chakras.get('heart', 50) / 100,
                'Throat': uploaded_chakras.get('throat', 50) / 100,
                'Third Eye': uploaded_chakras.get('third_eye', 50) / 100,
                'Crown': uploaded_chakras.get('crown', 50) / 100
            }
            
            st.subheader("📊 Your Uploaded Chakra Energies")
            st.markdown("These values came from your Bio-Well GDV scan:")
            
            # Display uploaded values
            col1, col2 = st.columns(2)
            with col1:
                for chakra in ['Root', 'Sacral', 'Solar Plexus', 'Heart']:
                    st.metric(chakra, f"{chakra_energies[chakra]:.2f}")
            with col2:
                for chakra in ['Throat', 'Third Eye', 'Crown']:
                    st.metric(chakra, f"{chakra_energies[chakra]:.2f}")
            
            # Allow manual override with expander
            with st.expander("🔧 Override with Manual Sliders (Optional)"):
                st.markdown("Adjust these values if you want to experiment:")
                override_energies = {}
                col1, col2 = st.columns(2)
                
                with col1:
                    override_energies['Root'] = st.slider("Root Chakra", 0.0, 1.0, float(chakra_energies['Root']), 0.05, key="override_root")
                    override_energies['Sacral'] = st.slider("Sacral Chakra", 0.0, 1.0, float(chakra_energies['Sacral']), 0.05, key="override_sacral")
                    override_energies['Solar Plexus'] = st.slider("Solar Plexus", 0.0, 1.0, float(chakra_energies['Solar Plexus']), 0.05, key="override_solar")
                    override_energies['Heart'] = st.slider("Heart Chakra", 0.0, 1.0, float(chakra_energies['Heart']), 0.05, key="override_heart")
                
                with col2:
                    override_energies['Throat'] = st.slider("Throat Chakra", 0.0, 1.0, float(chakra_energies['Throat']), 0.05, key="override_throat")
                    override_energies['Third Eye'] = st.slider("Third Eye", 0.0, 1.0, float(chakra_energies['Third Eye']), 0.05, key="override_third_eye")
                    override_energies['Crown'] = st.slider("Crown Chakra", 0.0, 1.0, float(chakra_energies['Crown']), 0.05, key="override_crown")
                
                if st.checkbox("Use manual overrides instead of uploaded data"):
                    chakra_energies = override_energies
        
        else:
            st.warning("""
            ⚠️ **NO BIO-WELL DATA UPLOADED - SIMULATION MODE**
            
            Upload your Bio-Well scan in Tab 1 to see your REAL TI Framework scores!
            For now, use sliders to simulate chakra energies:
            """)
            
            st.subheader("🌈 Simulate Chakra Energy Distribution")
            st.markdown("Move sliders to simulate Bio-Well chakra readings (0-1 scale):")
            
            chakra_energies = {}
            col1, col2 = st.columns(2)
            
            with col1:
                chakra_energies['Root'] = st.slider("Root Chakra", 0.0, 1.0, 0.7, 0.05)
                chakra_energies['Sacral'] = st.slider("Sacral Chakra", 0.0, 1.0, 0.75, 0.05)
                chakra_energies['Solar Plexus'] = st.slider("Solar Plexus", 0.0, 1.0, 0.65, 0.05)
                chakra_energies['Heart'] = st.slider("Heart Chakra", 0.0, 1.0, 0.85, 0.05)
            
            with col2:
                chakra_energies['Throat'] = st.slider("Throat Chakra", 0.0, 1.0, 0.6, 0.05)
                chakra_energies['Third Eye'] = st.slider("Third Eye", 0.0, 1.0, 0.8, 0.05)
                chakra_energies['Crown'] = st.slider("Crown Chakra", 0.0, 1.0, 0.7, 0.05)
        
        if st.button("🧮 CALCULATE TI METRICS", use_container_width=True):
            # GILE calculation
            gile_result = TIFrameworkSynergizer.biowell_to_gile(chakra_energies)
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("GILE Score", f"{gile_result['gile_score']:.2f}")
            with col2:
                st.metric("Sigma (σ)", f"{gile_result['sigma']:.3f}")
            with col3:
                st.metric("Chakra Balance", f"{gile_result['balance_score']:.2f}")
            
            st.info(f"**Interpretation:** {gile_result['interpretation']}")
            
            # PSI prediction
            st.subheader("🔮 PSI Capability Prediction")
            heart_coherence = chakra_energies['Heart']
            third_eye_energy = chakra_energies['Third Eye']
            
            psi_result = TIFrameworkSynergizer.predict_psi_capability(
                gile_result['gile_score'],
                third_eye_energy,
                heart_coherence
            )
            
            st.metric("PSI Score", f"{psi_result['psi_score']:.2f}")
            st.metric("PSI Capability", psi_result['capability'])
            st.markdown(f"**Description:** {psi_result['description']}")
            
            st.subheader("💡 Recommended PSI Enhancement Protocol")
            protocol = psi_result['recommended_protocol']
            st.json(protocol)
            
            # Visualization
            fig = go.Figure(data=[
                go.Scatterpolar(
                    r=list(chakra_energies.values()),
                    theta=list(chakra_energies.keys()),
                    fill='toself',
                    name='Chakra Energy'
                )
            ])
            fig.update_layout(
                polar=dict(radialaxis=dict(visible=True, range=[0, 1])),
                title="Chakra Energy Radar"
            )
            st.plotly_chart(fig, use_container_width=True)
    
    # TAB 7: DIY Build Guide
    with tabs[6]:
        st.header("🛠️ DIY Myrion Lamp Build Guide")
        st.markdown("""
        **Build your own photonic therapy lamp at home!**
        
        Total cost: **$200-250**  
        Build time: **4-6 hours**  
        Skill level: **Intermediate** (soldering, Arduino programming)
        """)
        
        build_specs = MyrionLamp.generate_lamp_hardware_specs()
        
        st.subheader("📦 Parts List")
        parts_df = pd.DataFrame(build_specs['components'])
        st.dataframe(parts_df, use_container_width=True)
        
        st.subheader("🔌 Assembly Instructions")
        st.markdown("""
        1. **Mount LEDs** to aluminum frame in chakra positions (7 LED clusters)
        2. **Wire LED drivers** - constant current for stability
        3. **Connect Arduino/ESP32** for programmable sequences
        4. **Attach quartz crystals** above each LED for energy amplification
        5. **Program timing sequences** - chakra activation patterns
        6. **Optional: HRV integration** - Connect Polar H10 via BLE to ESP32 for adaptive therapy!
        
        **Safety:**
        {build_specs['safety']}
        """)
        
        st.subheader("💻 Arduino Code Template")
        st.code("""
// Myrion Lamp v1.0 - Chakra Sequence Controller
// Cycles through 7 chakras with precise timing

int ledPins[] = {2, 3, 4, 5, 6, 7, 8}; // Root → Crown
int durations[] = {20, 15, 15, 15, 10, 10, 10}; // Minutes per chakra

void setup() {
  for (int i = 0; i < 7; i++) {
    pinMode(ledPins[i], OUTPUT);
  }
}

void loop() {
  for (int chakra = 0; chakra < 7; chakra++) {
    digitalWrite(ledPins[chakra], HIGH);
    delay(durations[chakra] * 60 * 1000); // Convert to ms
    digitalWrite(ledPins[chakra], LOW);
  }
}
        """, language='cpp')
        
        st.success(f"""
        **Integration:** {build_specs['integration']}
        
        **Total Cost:** {build_specs['total_cost']}  
        **Build Time:** {build_specs['build_time']}
        """)
        
        st.warning("""
        **⚠️ DISCLAIMER:**
        - This is a DIY educational project, NOT a medical device
        - Consult healthcare professionals before use
        - Use proper eye protection with blue/violet LEDs
        - Follow electrical safety guidelines
        """)

if __name__ == "__main__":
    render_biowell_myrion_system()
