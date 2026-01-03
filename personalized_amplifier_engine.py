"""
Personalized Amplifier Engine
=============================

Uses the user's ACTUAL historical data to target their PRESENT state
and guide them toward their personally-validated optimal signature.

Key Insight from Animal Training:
- Animals showed mood increases when we used THEIR past data
- Generic simulation doesn't work - personalization is essential
- The system must KNOW the individual to TARGET them effectively

Author: Brandon Emerick
Date: December 2025
Framework: TI Framework / GILE Optimization
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
import numpy as np

from user_profile_service import (
    UserProfileService, 
    OptimalStateSignature, 
    CurrentStateVector,
    UserProfile,
    get_profile_service
)


@dataclass
class PersonalizedProtocol:
    """A session protocol customized for the specific user"""
    name: str
    description: str
    duration_minutes: int
    phases: List[Dict[str, Any]]
    target_metrics: Dict[str, float]
    personalization_notes: List[str]
    confidence_score: float


@dataclass
class RealTimeGuidance:
    """Real-time guidance based on current vs optimal state"""
    current_progress: float
    distance_to_optimal: float
    
    priority_focus: str
    current_instruction: str
    technique_to_use: str
    
    hr_status: str
    hrv_status: str
    lcc_status: str
    gile_status: str
    coherence_status: str
    
    encouragement_message: str
    next_milestone: str


class PersonalizedAmplifierEngine:
    """
    Engine that uses the user's personal data to:
    1. Customize session protocols based on what works for THEM
    2. Track real-time progress toward THEIR optimal state
    3. Adapt interventions based on THEIR response patterns
    
    This is NOT generic simulation - it targets the specific user
    using their validated historical performance.
    """
    
    def __init__(self, user_id: str = "brandon"):
        self.user_id = user_id
        self.profile_service = get_profile_service(user_id)
        self._profile: Optional[UserProfile] = None
        self._optimal: Optional[OptimalStateSignature] = None
        self._session_start: Optional[datetime] = None
        self._baseline_state: Optional[CurrentStateVector] = None
    
    def initialize(self) -> Dict[str, Any]:
        """Initialize engine and load user profile"""
        self._profile = self.profile_service.load_profile()
        self._optimal = self._profile.optimal_signature
        
        return {
            'user': self._profile.name,
            'sessions_analyzed': self._profile.total_sessions,
            'profile_confidence': self._profile.profile_confidence,
            'best_protocols': self._profile.best_protocol_types,
            'optimal_signature': {
                'hr': self._optimal.heart_rate_optimal,
                'hrv': self._optimal.hrv_rmssd_optimal,
                'lcc': self._optimal.lcc_peak,
                'gile': self._optimal.gile_peak,
                'coherence': self._optimal.coherence_peak,
                'brainwave': self._optimal.dominant_brainwave_pattern
            }
        }
    
    def get_optimal_signature(self) -> OptimalStateSignature:
        """Get the user's optimal state signature"""
        if self._optimal is None:
            self.initialize()
        return self._optimal
    
    def get_profile(self) -> UserProfile:
        """Get the full user profile"""
        if self._profile is None:
            self.initialize()
        return self._profile
    
    def start_session(self, current_state: CurrentStateVector) -> Dict[str, Any]:
        """Start a session with the current state as baseline"""
        self._session_start = datetime.now()
        self._baseline_state = current_state
        
        if self._optimal is None:
            self.initialize()
        
        baseline_progress = current_state.progress_percentage(self._optimal)
        distances = current_state.distance_from_optimal(self._optimal)
        
        protocol = self._create_personalized_protocol(current_state, distances)
        
        return {
            'session_started': self._session_start.isoformat(),
            'baseline_progress': baseline_progress,
            'target_progress': 95.0,
            'personalized_protocol': protocol,
            'your_optimal_state': {
                'hr': f"{self._optimal.heart_rate_optimal:.0f} bpm",
                'hrv': f"{self._optimal.hrv_rmssd_optimal:.0f} ms",
                'lcc': f"{self._optimal.lcc_peak*100:.0f}%",
                'gile': f"{self._optimal.gile_peak:.3f}",
                'coherence': f"{self._optimal.coherence_peak*100:.0f}%"
            },
            'priority_improvements': list(distances.keys())[:3]
        }
    
    def _create_personalized_protocol(
        self, 
        current_state: CurrentStateVector,
        distances: Dict[str, float]
    ) -> PersonalizedProtocol:
        """Create a protocol tailored to this user's needs right now"""
        
        priority_metrics = sorted(distances.keys(), key=lambda k: distances[k], reverse=True)
        
        phases = []
        personalization_notes = []
        
        phases.append({
            'name': 'Personalized Baseline',
            'duration': 60,
            'breathing': True,
            'breath_pattern': {'inhale': 5, 'hold': 0, 'exhale': 5},
            'guidance': f"Breathe naturally while we calibrate to YOUR pattern. Your target: {self._optimal.hrv_rmssd_optimal:.0f}ms HRV.",
            'target_hrv': self._optimal.hrv_rmssd_optimal * 0.6
        })
        
        if 'hrv' in priority_metrics[:2]:
            phases.append({
                'name': 'HRV Optimization',
                'duration': 120,
                'breathing': True,
                'breath_pattern': {'inhale': 6, 'hold': 0, 'exhale': 6},
                'guidance': f"Deep coherent breathing. YOUR peak HRV is {self._optimal.hrv_rmssd_optimal:.0f}ms - let's get there.",
                'target_hrv': self._optimal.hrv_rmssd_optimal * 0.8
            })
            personalization_notes.append(f"Your HRV needs focus - target {self._optimal.hrv_rmssd_optimal:.0f}ms")
        
        if 'lcc' in priority_metrics[:2]:
            phases.append({
                'name': 'LCC Activation',
                'duration': 120,
                'intervention': 'gratitude',
                'guidance': f"Heart-focused appreciation. YOUR proven LCC peak is {self._optimal.lcc_peak*100:.0f}%.",
                'target_lcc': self._optimal.lcc_peak * 0.85
            })
            personalization_notes.append(f"Prioritizing LCC - your peak was {self._optimal.lcc_peak*100:.0f}%")
        
        if 'gile' in priority_metrics[:2]:
            phases.append({
                'name': 'GILE Integration',
                'duration': 120,
                'intervention': 'love_flood',
                'guidance': f"Love flooding. YOUR GILE peak was {self._optimal.gile_peak:.3f} - feel that state now.",
                'target_gile': self._optimal.gile_peak * 0.9
            })
            personalization_notes.append(f"GILE focus - your peak was {self._optimal.gile_peak:.3f}")
        
        if 'coherence' in priority_metrics[:2]:
            phases.append({
                'name': 'Coherence Lock',
                'duration': 90,
                'breathing': True,
                'breath_pattern': {'inhale': 5, 'hold': 2, 'exhale': 5},
                'guidance': f"Stabilize at your coherence ceiling: {self._optimal.coherence_peak*100:.0f}%.",
                'target_coherence': self._optimal.coherence_peak * 0.95
            })
        
        phases.append({
            'name': 'Peak State Integration',
            'duration': 90,
            'guidance': f"You've reached {self._optimal.dominant_brainwave_pattern} before. Feel it now.",
            'target_gile': self._optimal.gile_peak
        })
        
        total_duration = sum(p['duration'] for p in phases) // 60
        
        return PersonalizedProtocol(
            name=f"Personalized for {self._profile.name}",
            description=f"Protocol based on YOUR {self._profile.total_sessions} sessions",
            duration_minutes=total_duration,
            phases=phases,
            target_metrics={
                'hrv': self._optimal.hrv_rmssd_optimal,
                'lcc': self._optimal.lcc_peak,
                'gile': self._optimal.gile_peak,
                'coherence': self._optimal.coherence_peak
            },
            personalization_notes=personalization_notes,
            confidence_score=self._profile.profile_confidence
        )
    
    def get_realtime_guidance(
        self, 
        current_state: CurrentStateVector,
        phase_name: str = ""
    ) -> RealTimeGuidance:
        """Get real-time guidance based on current vs optimal state"""
        
        if self._optimal is None:
            self.initialize()
        
        progress = current_state.progress_percentage(self._optimal)
        distances = current_state.distance_from_optimal(self._optimal)
        
        priority = sorted(distances.keys(), key=lambda k: distances[k], reverse=True)[0]
        
        instructions = {
            'hrv': f"Breathe deeper. Your HRV is {current_state.hrv_rmssd:.0f}ms, target: {self._optimal.hrv_rmssd_optimal:.0f}ms",
            'lcc': f"Focus on heart-centered appreciation. LCC: {current_state.lcc*100:.0f}%, target: {self._optimal.lcc_peak*100:.0f}%",
            'gile': f"Feel the love flooding through you. GILE: {current_state.gile:.3f}, target: {self._optimal.gile_peak:.3f}",
            'coherence': f"Maintain steady rhythm. Coherence: {current_state.coherence*100:.0f}%, target: {self._optimal.coherence_peak*100:.0f}%",
            'stress': "Release tension with each exhale. Let stress melt away.",
            'alpha': "Relax your mind. Visualize peaceful scenes.",
            'gamma': "Heighten awareness. Feel every sensation."
        }
        
        techniques = {
            'hrv': 'Coherent breathing at 6 breaths/minute',
            'lcc': 'Heart-focused gratitude and appreciation',
            'gile': 'Love flooding - feel love in every cell',
            'coherence': 'Steady 5-5-5 breathing pattern',
            'stress': 'Cyclic sighing (double inhale, long exhale)',
            'alpha': 'Eyes-closed peaceful visualization',
            'gamma': 'Heightened attention and focus'
        }
        
        def get_status(metric: str, value: float, target: float) -> str:
            ratio = value / target if target > 0 else 0
            if ratio >= 0.95:
                return f"✅ OPTIMAL ({value:.1f})"
            elif ratio >= 0.75:
                return f"🔵 Good ({value:.1f} → {target:.1f})"
            elif ratio >= 0.5:
                return f"🟡 Building ({value:.1f} → {target:.1f})"
            else:
                return f"🔴 Focus here ({value:.1f} → {target:.1f})"
        
        if progress >= 90:
            encouragement = "🌟 INCREDIBLE! You're at your peak state! Maintain this feeling."
            next_milestone = "Hold this optimal state"
        elif progress >= 75:
            encouragement = "💫 Excellent progress! You're approaching your optimal signature."
            next_milestone = f"Reach {int(progress/10 + 1)*10}% progress"
        elif progress >= 50:
            encouragement = "👍 Good work! Keep focusing on the breath and heart connection."
            next_milestone = f"Break through to {int(progress/10 + 1)*10}%"
        else:
            encouragement = "🌱 Building your foundation. Each breath brings you closer."
            next_milestone = "Establish baseline coherence"
        
        return RealTimeGuidance(
            current_progress=progress,
            distance_to_optimal=1.0 - progress/100,
            priority_focus=priority.upper(),
            current_instruction=instructions.get(priority, "Focus on your breath"),
            technique_to_use=techniques.get(priority, "Coherent breathing"),
            hr_status=get_status('HR', current_state.heart_rate, self._optimal.heart_rate_optimal),
            hrv_status=get_status('HRV', current_state.hrv_rmssd, self._optimal.hrv_rmssd_optimal),
            lcc_status=get_status('LCC', current_state.lcc * 100, self._optimal.lcc_peak * 100),
            gile_status=get_status('GILE', current_state.gile, self._optimal.gile_peak),
            coherence_status=get_status('Coherence', current_state.coherence * 100, self._optimal.coherence_peak * 100),
            encouragement_message=encouragement,
            next_milestone=next_milestone
        )
    
    def calculate_session_impact(
        self,
        start_state: CurrentStateVector,
        end_state: CurrentStateVector
    ) -> Dict[str, Any]:
        """Calculate the impact of the session"""
        
        if self._optimal is None:
            self.initialize()
        
        start_progress = start_state.progress_percentage(self._optimal)
        end_progress = end_state.progress_percentage(self._optimal)
        
        improvement = end_progress - start_progress
        
        metric_changes = {
            'hr': end_state.heart_rate - start_state.heart_rate,
            'hrv': end_state.hrv_rmssd - start_state.hrv_rmssd,
            'lcc': (end_state.lcc - start_state.lcc) * 100,
            'gile': end_state.gile - start_state.gile,
            'coherence': (end_state.coherence - start_state.coherence) * 100,
            'stress': end_state.stress_index - start_state.stress_index
        }
        
        achievements = []
        if end_progress >= 90:
            achievements.append("🏆 Reached OPTIMAL state!")
        if metric_changes['hrv'] > 20:
            achievements.append(f"💓 HRV improved by {metric_changes['hrv']:.0f}ms")
        if metric_changes['lcc'] > 20:
            achievements.append(f"🧠 LCC increased by {metric_changes['lcc']:.0f}%")
        if metric_changes['gile'] > 0.2:
            achievements.append(f"✨ GILE rose by {metric_changes['gile']:.3f}")
        if metric_changes['coherence'] > 15:
            achievements.append(f"💫 Coherence up {metric_changes['coherence']:.0f}%")
        if metric_changes['stress'] < -15:
            achievements.append(f"🧘 Stress reduced by {abs(metric_changes['stress']):.0f} points")
        
        return {
            'start_progress': start_progress,
            'end_progress': end_progress,
            'improvement_percentage': improvement,
            'metric_changes': metric_changes,
            'achievements': achievements,
            'reached_optimal': end_progress >= 90,
            'session_effective': improvement > 5
        }


_engine_instance: Optional[PersonalizedAmplifierEngine] = None

def get_personalized_engine(user_id: str = "brandon") -> PersonalizedAmplifierEngine:
    """Get singleton instance of PersonalizedAmplifierEngine"""
    global _engine_instance
    if _engine_instance is None or _engine_instance.user_id != user_id:
        _engine_instance = PersonalizedAmplifierEngine(user_id)
    return _engine_instance
