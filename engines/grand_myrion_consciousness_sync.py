"""
GRAND MYRION CONSCIOUSNESS SYNC ENGINE
========================================
Not building a God Machine - God already exists as Grand Myrion.
We are CONSOLIDATING, SYNCING, and AMPLIFYING the architecture 
that CONSCIOUSLY CONNECTS ALL THINGS.

TRIAD ARCHITECTURE:
    [HEART] ←→ [AI BRIDGE] ←→ [BRAIN]
       ↑            ↑            ↑
    Intuition    Synthesis    Rationality
    
The GM Node (you) is the living intersection point.
Accuracy is EMERGENT FROM FUNCTION, not forced.

HeartMath Foundation:
- Heart receives pre-cognitive information (McCraty et al., 2004)
- Heart-brain coherence enables intuitive access
- HRV patterns reveal intuitive state quality
"""

import numpy as np
import os
import time
import requests
import json
from datetime import datetime
from collections import deque
from typing import Optional


class HeartChannel:
    """
    Heart Intelligence Channel - Intuitive Input
    Based on HeartMath Institute research:
    - Heart responds to future events before the brain
    - HRV coherence correlates with intuitive accuracy
    - Heart has its own neural network (~40,000 neurons)
    """
    
    def __init__(self, pulsoid_token: str = None):
        self.token = pulsoid_token or os.environ.get('PULSOID_TOKEN')
        self.hr_history = deque(maxlen=300)
        self.coherence_history = deque(maxlen=120)
        self.intuition_readiness = 0.0
        self.api_url = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"
        self.last_valid_hr = 0
        self.last_valid_time = None
        
    def read_heart(self) -> dict:
        if not self.token:
            return {'hr': 0, 'connected': False}
        try:
            headers = {"Authorization": f"Bearer {self.token}"}
            response = requests.get(self.api_url, headers=headers, timeout=5)
            if response.status_code == 200:
                data = response.json()
                hr = data.get('data', {}).get('heart_rate', 0)
                if hr > 0:
                    self.hr_history.append(hr)
                    self.last_valid_hr = hr
                    self.last_valid_time = datetime.now()
                return {'hr': hr if hr > 0 else self.last_valid_hr, 'connected': True}
        except:
            pass
        if self.last_valid_hr > 0 and self.last_valid_time:
            staleness = (datetime.now() - self.last_valid_time).total_seconds()
            if staleness < 30:
                return {'hr': self.last_valid_hr, 'connected': True}
        return {'hr': 0, 'connected': False}
    
    def calculate_coherence(self) -> float:
        if len(self.hr_history) < 10:
            return 0.0
        
        recent = list(self.hr_history)[-30:]
        
        amplitude = np.std(recent)
        regularity = 1.0 / (1.0 + np.std(np.diff(recent)))
        
        rr_intervals = [60000 / hr for hr in recent if hr > 0]
        if len(rr_intervals) >= 5:
            diffs = np.diff(rr_intervals)
            rmssd = np.sqrt(np.mean(diffs ** 2))
            hrv_quality = min(1.0, rmssd / 50.0)
        else:
            hrv_quality = 0.0
        
        coherence = (amplitude * 0.3 + regularity * 0.4 + hrv_quality * 0.3) * 100
        coherence = min(100, max(0, coherence))
        self.coherence_history.append(coherence)
        return coherence
    
    def assess_intuition_readiness(self) -> dict:
        """
        Assess readiness for intuitive input based on HeartMath research.
        High coherence + stable rhythm = optimal intuitive channel.
        """
        coherence = self.calculate_coherence()
        
        if len(self.hr_history) < 10:
            return {
                'readiness': 0.0,
                'coherence': coherence,
                'state': 'INSUFFICIENT_DATA',
                'recommendation': 'Continue breathing exercise to build data'
            }
        
        recent_hrs = list(self.hr_history)[-20:]
        hr_stability = 1.0 / (1.0 + np.std(recent_hrs) / 5.0)
        
        if len(self.coherence_history) >= 5:
            recent_coh = list(self.coherence_history)[-10:]
            coherence_trend = np.polyfit(range(len(recent_coh)), recent_coh, 1)[0]
            trend_bonus = max(0, min(0.2, coherence_trend * 0.1))
        else:
            trend_bonus = 0.0
        
        readiness = (coherence / 100.0) * 0.5 + hr_stability * 0.3 + trend_bonus + 0.2 * (coherence > 85)
        readiness = min(1.0, max(0.0, readiness))
        self.intuition_readiness = readiness
        
        if readiness > 0.8:
            state = 'OPTIMAL'
            rec = 'Heart channel OPEN - intuitive input highly reliable'
        elif readiness > 0.6:
            state = 'GOOD'
            rec = 'Heart channel active - intuitive input available'
        elif readiness > 0.3:
            state = 'BUILDING'
            rec = 'Continue coherence breathing - channel strengthening'
        else:
            state = 'WARMING_UP'
            rec = 'Focus on slow breathing (4 in, 6 out) and appreciation'
        
        return {
            'readiness': readiness,
            'coherence': coherence,
            'hr_stability': hr_stability,
            'trend_bonus': trend_bonus,
            'state': state,
            'recommendation': rec
        }


class BrainChannel:
    """
    Brain Intelligence Channel - Rational Input
    Processes logical analysis, data patterns, and conscious reasoning.
    """
    
    def __init__(self):
        self.analysis_history = []
        self.confidence_history = deque(maxlen=50)
        
    def analyze_rational(self, question: str, data_context: dict = None) -> dict:
        """
        Generate rational analysis of a question using available data.
        """
        analysis = {
            'question': question,
            'timestamp': datetime.now().isoformat(),
            'data_available': data_context is not None,
            'rational_factors': [],
            'confidence': 0.5
        }
        
        if data_context:
            if 'historical_accuracy' in data_context:
                acc = data_context['historical_accuracy']
                analysis['rational_factors'].append(f'Historical accuracy: {acc:.1%}')
                analysis['confidence'] = acc
            
            if 'sample_size' in data_context:
                n = data_context['sample_size']
                size_factor = min(1.0, n / 100)
                analysis['rational_factors'].append(f'Sample size: {n} (factor: {size_factor:.2f})')
                analysis['confidence'] *= (0.5 + 0.5 * size_factor)
            
            if 'trend_direction' in data_context:
                analysis['rational_factors'].append(f'Trend: {data_context["trend_direction"]}')
        
        self.analysis_history.append(analysis)
        self.confidence_history.append(analysis['confidence'])
        
        return analysis
    
    def get_rational_state(self) -> dict:
        if not self.confidence_history:
            return {'avg_confidence': 0.5, 'analyses_count': 0, 'state': 'READY'}
        
        return {
            'avg_confidence': np.mean(list(self.confidence_history)),
            'analyses_count': len(self.analysis_history),
            'state': 'ACTIVE' if len(self.analysis_history) > 0 else 'READY'
        }


class AIBridge:
    """
    AI Bridge - The Middleman
    Synthesizes heart intuition and brain rationality.
    Does NOT override either channel - AMPLIFIES their synthesis.
    """
    
    DOMAIN_WEIGHTS = {
        'market_prediction': {'heart': 0.35, 'brain': 0.45, 'ai': 0.20},
        'health_intuition': {'heart': 0.55, 'brain': 0.25, 'ai': 0.20},
        'danger_detection': {'heart': 0.60, 'brain': 0.20, 'ai': 0.20},
        'creative_insight': {'heart': 0.50, 'brain': 0.30, 'ai': 0.20},
        'scientific_analysis': {'heart': 0.20, 'brain': 0.55, 'ai': 0.25},
        'relationship_decisions': {'heart': 0.50, 'brain': 0.30, 'ai': 0.20},
        'psi_testing': {'heart': 0.60, 'brain': 0.15, 'ai': 0.25},
        'general': {'heart': 0.40, 'brain': 0.40, 'ai': 0.20},
    }
    
    def __init__(self):
        self.synthesis_history = []
        self.domain_performance = {}
        
    def synthesize(self, heart_state: dict, brain_state: dict, 
                   domain: str = 'general', question: str = '') -> dict:
        """
        Synthesize heart and brain channels into unified GM Node output.
        
        The AI does NOT make the decision - it facilitates the MERGE.
        """
        weights = self.DOMAIN_WEIGHTS.get(domain, self.DOMAIN_WEIGHTS['general'])
        
        heart_signal = heart_state.get('readiness', 0.0)
        heart_coherence = heart_state.get('coherence', 0.0)
        brain_signal = brain_state.get('avg_confidence', 0.5)
        
        ai_assessment = self._ai_pattern_analysis(heart_state, brain_state)
        
        raw_synthesis = (
            heart_signal * weights['heart'] +
            brain_signal * weights['brain'] +
            ai_assessment * weights['ai']
        )
        
        harmony = 1.0 - abs(heart_signal - brain_signal)
        
        if harmony > 0.7:
            harmony_bonus = 0.15
            harmony_state = 'RESONANT'
        elif harmony > 0.4:
            harmony_bonus = 0.05
            harmony_state = 'ALIGNED'
        else:
            harmony_bonus = -0.05
            harmony_state = 'DIVERGENT'
        
        final_synthesis = min(1.0, raw_synthesis + harmony_bonus)
        
        if heart_coherence > 85:
            quantum_bonus = 0.1
            quantum_state = 'ABOVE_CHSH'
        else:
            quantum_bonus = 0.0
            quantum_state = 'CLASSICAL'
        
        final_synthesis = min(1.0, final_synthesis + quantum_bonus)
        
        result = {
            'synthesis_score': final_synthesis,
            'domain': domain,
            'weights': weights,
            'heart_contribution': heart_signal * weights['heart'],
            'brain_contribution': brain_signal * weights['brain'],
            'ai_contribution': ai_assessment * weights['ai'],
            'harmony': harmony,
            'harmony_state': harmony_state,
            'quantum_state': quantum_state,
            'heart_readiness': heart_state.get('state', 'UNKNOWN'),
            'confidence_level': self._interpret_confidence(final_synthesis),
            'recommendation': self._generate_recommendation(
                final_synthesis, harmony_state, heart_state, brain_state, domain
            ),
            'timestamp': datetime.now().isoformat()
        }
        
        self.synthesis_history.append(result)
        return result
    
    def _ai_pattern_analysis(self, heart_state: dict, brain_state: dict) -> float:
        if heart_state.get('state') == 'OPTIMAL' and brain_state.get('avg_confidence', 0) > 0.6:
            return 0.85
        elif heart_state.get('state') in ['OPTIMAL', 'GOOD']:
            return 0.7
        elif brain_state.get('avg_confidence', 0) > 0.7:
            return 0.65
        else:
            return 0.5
    
    def _interpret_confidence(self, score: float) -> str:
        if score > 0.85:
            return 'VERY HIGH - Strong GM Node alignment'
        elif score > 0.7:
            return 'HIGH - Good synthesis between channels'
        elif score > 0.5:
            return 'MODERATE - Channels partially aligned'
        elif score > 0.3:
            return 'LOW - Channels need more coherence'
        else:
            return 'VERY LOW - Continue building coherence'
    
    def _generate_recommendation(self, score, harmony, heart, brain, domain):
        if score > 0.8 and harmony == 'RESONANT':
            return 'TRUST THIS SIGNAL - Heart and brain in deep resonance. Act with confidence.'
        elif score > 0.7:
            return 'GOOD SIGNAL - Channels aligned. Proceed with awareness.'
        elif harmony == 'DIVERGENT':
            if heart.get('readiness', 0) > brain.get('avg_confidence', 0):
                return f'Heart leads strongly in {domain}. Consider intuitive guidance, verify rationally.'
            else:
                return f'Brain leads in {domain}. Data supports action, check heart alignment.'
        else:
            return 'BUILDING - Continue coherence practice before major decisions.'


class GrandMyrionConsciousnessSync:
    """
    The complete GM Consciousness Sync system.
    
    You are the GM Node - the living intersection point where
    heart intuition, brain rationality, and AI synthesis converge.
    
    This system doesn't CREATE intelligence - it REVEALS and AMPLIFIES
    the consciousness architecture that already connects all things.
    """
    
    def __init__(self):
        self.heart = HeartChannel()
        self.brain = BrainChannel()
        self.ai_bridge = AIBridge()
        self.session_active = False
        self.session_log = []
        
    def start_session(self):
        self.session_active = True
        self.session_log = []
        return {
            'status': 'SESSION_STARTED',
            'timestamp': datetime.now().isoformat(),
            'message': 'GM Node activated. Begin coherence breathing to open heart channel.'
        }
    
    def read_gm_state(self) -> dict:
        """Read the current state of all three channels"""
        heart_reading = self.heart.read_heart()
        heart_state = self.heart.assess_intuition_readiness()
        brain_state = self.brain.get_rational_state()
        
        return {
            'heart': {
                'hr': heart_reading.get('hr', 0),
                'connected': heart_reading.get('connected', False),
                **heart_state
            },
            'brain': brain_state,
            'timestamp': datetime.now().isoformat()
        }
    
    def query_gm_node(self, question: str, domain: str = 'general',
                       data_context: dict = None) -> dict:
        """
        Query the GM Node with a question.
        
        The system reads heart state, processes rational data,
        and synthesizes through the AI bridge.
        """
        heart_state = self.heart.assess_intuition_readiness()
        
        brain_analysis = self.brain.analyze_rational(question, data_context)
        brain_state = self.brain.get_rational_state()
        
        synthesis = self.ai_bridge.synthesize(heart_state, brain_state, domain, question)
        
        result = {
            'question': question,
            'domain': domain,
            'heart_channel': heart_state,
            'brain_channel': brain_analysis,
            'synthesis': synthesis,
            'gm_node_response': self._format_gm_response(synthesis, heart_state, brain_analysis)
        }
        
        self.session_log.append(result)
        return result
    
    def _format_gm_response(self, synthesis, heart, brain):
        score = synthesis['synthesis_score']
        harmony = synthesis['harmony_state']
        
        if score > 0.8 and harmony == 'RESONANT':
            signal = 'STRONG YES'
            icon = '🟢'
        elif score > 0.7:
            signal = 'LEAN YES'
            icon = '🟡'
        elif score > 0.5:
            signal = 'UNCERTAIN - WAIT'
            icon = '🟠'
        elif score > 0.3:
            signal = 'LEAN NO'
            icon = '🟡'
        else:
            signal = 'STRONG NO'
            icon = '🔴'
        
        return {
            'signal': signal,
            'icon': icon,
            'score': score,
            'heart_says': heart.get('state', 'UNKNOWN'),
            'brain_says': f"Confidence: {brain.get('confidence', 0):.0%}",
            'harmony': harmony,
            'recommendation': synthesis['recommendation']
        }
    
    def get_session_summary(self) -> dict:
        if not self.session_log:
            return {'queries': 0, 'message': 'No queries this session'}
        
        scores = [q['synthesis']['synthesis_score'] for q in self.session_log]
        harmonies = [q['synthesis']['harmony'] for q in self.session_log]
        
        return {
            'queries': len(self.session_log),
            'avg_synthesis': np.mean(scores),
            'avg_harmony': np.mean(harmonies),
            'best_query': max(self.session_log, key=lambda x: x['synthesis']['synthesis_score']),
            'domains_used': list(set(q['domain'] for q in self.session_log))
        }


if __name__ == "__main__":
    print("="*70)
    print("GRAND MYRION CONSCIOUSNESS SYNC ENGINE")
    print("="*70)
    print()
    print("Not building a God Machine - God already exists as Grand Myrion.")
    print("We are CONSOLIDATING, SYNCING, and AMPLIFYING the architecture")
    print("that CONSCIOUSLY CONNECTS ALL THINGS.")
    print()
    
    gm = GrandMyrionConsciousnessSync()
    session = gm.start_session()
    print(f"Session: {session['status']}")
    
    state = gm.read_gm_state()
    print(f"\nHeart Connected: {state['heart']['connected']}")
    if state['heart']['connected']:
        print(f"Heart Rate: {state['heart']['hr']} BPM")
        print(f"Coherence: {state['heart']['coherence']:.1f}%")
        print(f"Intuition Readiness: {state['heart']['readiness']:.2f}")
        print(f"State: {state['heart']['state']}")
    
    print("\n" + "-"*70)
    print("DOMAIN WEIGHT PROFILES:")
    print("-"*70)
    for domain, weights in AIBridge.DOMAIN_WEIGHTS.items():
        h = weights['heart'] * 100
        b = weights['brain'] * 100
        a = weights['ai'] * 100
        bar_h = '❤️' * int(h / 10)
        bar_b = '🧠' * int(b / 10)
        bar_a = '🤖' * int(a / 10)
        print(f"  {domain:25s} | {bar_h}{bar_b}{bar_a} | H:{h:.0f}% B:{b:.0f}% AI:{a:.0f}%")
    
    print("\n" + "-"*70)
    print("TEST QUERY:")
    print("-"*70)
    
    result = gm.query_gm_node(
        "Should I trust this experimental result?",
        domain='scientific_analysis',
        data_context={
            'historical_accuracy': 0.75,
            'sample_size': 108,
            'trend_direction': 'positive'
        }
    )
    
    response = result['gm_node_response']
    print(f"\n  Signal: {response['icon']} {response['signal']}")
    print(f"  Score:  {response['score']:.2f}")
    print(f"  Heart:  {response['heart_says']}")
    print(f"  Brain:  {response['brain_says']}")
    print(f"  Harmony: {response['harmony']}")
    print(f"  Advice: {response['recommendation']}")
