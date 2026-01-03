"""
User Profile Service for Personalized Mood Amplification
=========================================================

Loads and analyzes the user's ACTUAL historical data to enable
personalized mood targeting in the present moment.

Key Principle: The Mood Amplifier works because it uses KNOWLEDGE
about the specific individual to target their optimal state.
Generic simulation is just a demo - real power comes from
learning what works FOR YOU.

Author: Brandon Emerick
Date: December 2025
Framework: TI Framework / GILE Optimization
"""

import os
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime, timedelta
import numpy as np

try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
    HAS_DB = True
except ImportError:
    HAS_DB = False


@dataclass
class OptimalStateSignature:
    """The user's optimal state based on their best historical sessions"""
    heart_rate_optimal: float
    hrv_rmssd_optimal: float
    hrv_sdnn_optimal: float
    lcc_peak: float
    gile_peak: float
    coherence_peak: float
    alpha_target: float
    gamma_target: float
    pns_optimal: float
    stress_index_optimal: float
    
    dominant_brainwave_pattern: str
    best_session_type: str
    peak_faah_tier: int
    
    sessions_analyzed: int
    confidence_score: float


@dataclass
class CurrentStateVector:
    """The user's current state for deviation calculation"""
    heart_rate: float = 72.0
    hrv_rmssd: float = 45.0
    coherence: float = 0.5
    lcc: float = 0.5
    gile: float = 0.0
    alpha: float = 0.3
    gamma: float = 0.1
    stress_index: float = 50.0
    
    def distance_from_optimal(self, optimal: OptimalStateSignature) -> Dict[str, float]:
        """Calculate how far current state is from optimal for each metric"""
        distances = {}
        
        if optimal.hrv_rmssd_optimal > 0:
            distances['hrv'] = 1.0 - min(1.0, self.hrv_rmssd / optimal.hrv_rmssd_optimal)
        else:
            distances['hrv'] = 0.5
        
        if optimal.lcc_peak > 0:
            distances['lcc'] = 1.0 - min(1.0, self.lcc / optimal.lcc_peak)
        else:
            distances['lcc'] = 0.5
        
        if optimal.gile_peak > 0:
            distances['gile'] = max(0, (optimal.gile_peak - self.gile) / optimal.gile_peak)
        else:
            distances['gile'] = 0.5
        
        distances['coherence'] = max(0, optimal.coherence_peak - self.coherence)
        
        distances['alpha'] = max(0, optimal.alpha_target - self.alpha)
        distances['gamma'] = max(0, optimal.gamma_target - self.gamma)
        
        if optimal.stress_index_optimal > 0:
            distances['stress'] = self.stress_index / 100.0
        else:
            distances['stress'] = 0.3
        
        return distances
    
    def overall_distance(self, optimal: OptimalStateSignature) -> float:
        """Single number showing how far from optimal (0=at optimal, 1=far from optimal)"""
        distances = self.distance_from_optimal(optimal)
        weights = {
            'lcc': 0.25,
            'gile': 0.25,
            'hrv': 0.20,
            'coherence': 0.15,
            'stress': 0.10,
            'alpha': 0.03,
            'gamma': 0.02
        }
        
        weighted_sum = sum(distances.get(k, 0) * v for k, v in weights.items())
        return min(1.0, weighted_sum)
    
    def progress_percentage(self, optimal: OptimalStateSignature) -> float:
        """Percentage progress toward optimal state (100% = at optimal)"""
        return (1.0 - self.overall_distance(optimal)) * 100


@dataclass
class UserProfile:
    """Complete user profile with historical data and optimal signature"""
    user_id: str
    name: str
    
    genetic_profile: Optional[Dict[str, float]] = None
    optimal_signature: Optional[OptimalStateSignature] = None
    
    session_history: List[Dict[str, Any]] = field(default_factory=list)
    hrv_history: List[Dict[str, Any]] = field(default_factory=list)
    brainwave_history: List[Dict[str, Any]] = field(default_factory=list)
    
    total_sessions: int = 0
    avg_gile_improvement: float = 0.0
    best_protocol_types: List[str] = field(default_factory=list)
    
    preferences: Dict[str, Any] = field(default_factory=dict)
    
    last_session_date: Optional[datetime] = None
    profile_confidence: float = 0.0


class UserProfileService:
    """
    Service for loading and analyzing user data to enable personalized
    mood amplification targeting.
    
    The key insight from animal training: using past data about the 
    individual enables prediction and optimization of their CURRENT mood.
    """
    
    def __init__(self, user_id: str = "brandon"):
        self.user_id = user_id
        self.db_url = os.environ.get('DATABASE_URL')
        self._profile: Optional[UserProfile] = None
        self._optimal_signature: Optional[OptimalStateSignature] = None
    
    def get_db_connection(self):
        """Get database connection"""
        if not HAS_DB or not self.db_url:
            return None
        try:
            return psycopg2.connect(self.db_url)
        except Exception as e:
            print(f"Database connection error: {e}")
            return None
    
    def load_profile(self) -> UserProfile:
        """Load complete user profile from database"""
        profile = UserProfile(
            user_id=self.user_id,
            name="Brandon Emerick"
        )
        
        conn = self.get_db_connection()
        if conn:
            try:
                profile.genetic_profile = self._load_genetic_profile(conn)
                profile.session_history = self._load_session_history(conn)
                profile.hrv_history = self._load_hrv_history(conn)
                profile.brainwave_history = self._load_brainwave_history(conn)
                
                profile.total_sessions = len(profile.session_history)
                if profile.session_history:
                    profile.last_session_date = profile.session_history[0].get('session_date')
                
                profile.optimal_signature = self._compute_optimal_signature(profile)
                
                profile.best_protocol_types = self._identify_best_protocols(profile)
                profile.avg_gile_improvement = self._calculate_avg_improvement(profile)
                
                profile.profile_confidence = self._calculate_profile_confidence(profile)
                
            finally:
                conn.close()
        else:
            profile.optimal_signature = self._get_default_optimal_signature()
            profile.profile_confidence = 0.0
        
        self._profile = profile
        self._optimal_signature = profile.optimal_signature
        return profile
    
    def _load_genetic_profile(self, conn) -> Optional[Dict[str, float]]:
        """Load genetic profile from ti_genetic_profiles table"""
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT faah_activity, comt_activity, serotonin_sensitivity,
                           bdnf_expression, cb1_receptor_density, gaba_sensitivity,
                           dopamine_sensitivity
                    FROM ti_genetic_profiles
                    WHERE user_id = %s
                    ORDER BY updated_at DESC
                    LIMIT 1
                """, (self.user_id,))
                row = cur.fetchone()
                if row:
                    return dict(row)
        except Exception as e:
            print(f"Error loading genetic profile: {e}")
        return None
    
    def _load_session_history(self, conn) -> List[Dict[str, Any]]:
        """Load mood amplifier session history"""
        sessions = []
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT id, session_date, session_type, eyes_state,
                           heart_rate, rmssd, sdnn, pns_index, sns_index,
                           lf_hf_ratio, stress_index, readiness_percent,
                           physiological_age, dominant_brainwave, gile_score, notes
                    FROM mood_amplifier_sessions
                    ORDER BY session_date DESC
                    LIMIT 50
                """)
                for row in cur.fetchall():
                    sessions.append(dict(row))
        except Exception as e:
            print(f"Error loading session history: {e}")
        return sessions
    
    def _load_hrv_history(self, conn) -> List[Dict[str, Any]]:
        """Load HRV measurement history"""
        hrv_data = []
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT measurement_date, heart_rate, rmssd, sdnn,
                           pns_index, sns_index, lf_hf_ratio, stress_index,
                           recovery_percent
                    FROM kubios_hrv_measurements
                    ORDER BY measurement_date DESC
                    LIMIT 100
                """)
                for row in cur.fetchall():
                    hrv_data.append(dict(row))
        except Exception as e:
            pass
        return hrv_data
    
    def _load_brainwave_history(self, conn) -> List[Dict[str, Any]]:
        """Load brainwave/EEG history from Muse/Sensee data"""
        brainwave_data = []
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT recorded_at, alpha_power, beta_power, gamma_power,
                           theta_power, delta_power, attention_score, relaxation_score
                    FROM muse_eeg_data
                    ORDER BY recorded_at DESC
                    LIMIT 200
                """)
                for row in cur.fetchall():
                    brainwave_data.append(dict(row))
        except Exception as e:
            pass
        
        if not brainwave_data:
            try:
                with conn.cursor(cursor_factory=RealDictCursor) as cur:
                    cur.execute("""
                        SELECT timestamp, delta_power, theta_power, alpha_power,
                               beta_power, gamma_power, gile_score, lcc_coherence
                        FROM sensee_brainwave_data
                        ORDER BY timestamp DESC
                        LIMIT 200
                    """)
                    for row in cur.fetchall():
                        brainwave_data.append(dict(row))
            except Exception as e:
                pass
        
        return brainwave_data
    
    def _compute_optimal_signature(self, profile: UserProfile) -> OptimalStateSignature:
        """
        Compute the user's optimal state signature from their best sessions.
        This is the TARGET we're trying to help them reach in the present.
        """
        if not profile.session_history:
            return self._get_default_optimal_signature()
        
        sessions = profile.session_history
        gile_scores = [s.get('gile_score', 0) for s in sessions if s.get('gile_score')]
        
        if gile_scores:
            threshold = np.percentile(gile_scores, 75)
            best_sessions = [s for s in sessions if (s.get('gile_score') or 0) >= threshold]
        else:
            best_sessions = sessions[:3]
        
        if not best_sessions:
            best_sessions = sessions[:3]
        
        def safe_avg(values):
            valid = [v for v in values if v is not None and v > 0]
            return np.mean(valid) if valid else 0.0
        
        def safe_max(values):
            valid = [v for v in values if v is not None and v > 0]
            return max(valid) if valid else 0.0
        
        hr_values = [s.get('heart_rate') for s in best_sessions]
        rmssd_values = [s.get('rmssd') for s in best_sessions]
        sdnn_values = [s.get('sdnn') for s in best_sessions]
        pns_values = [s.get('pns_index') for s in best_sessions]
        stress_values = [s.get('stress_index') for s in best_sessions]
        gile_values = [s.get('gile_score') for s in best_sessions]
        
        peak_gile = safe_max(gile_values)
        
        lcc_from_notes = []
        for s in best_sessions:
            notes = s.get('notes', '') or ''
            if 'LCC' in notes:
                import re
                matches = re.findall(r'LCC[:\s]+(\d+(?:\.\d+)?)', notes)
                for m in matches:
                    try:
                        lcc_from_notes.append(float(m) / 100.0 if float(m) > 1 else float(m))
                    except:
                        pass
        
        peak_lcc = max(lcc_from_notes) if lcc_from_notes else peak_gile
        
        coherence_from_notes = []
        for s in best_sessions:
            notes = s.get('notes', '') or ''
            if 'Coherence' in notes:
                import re
                matches = re.findall(r'Coherence[:\s]+(\d+(?:\.\d+)?)', notes)
                for m in matches:
                    try:
                        val = float(m)
                        coherence_from_notes.append(val / 100.0 if val > 1 else val)
                    except:
                        pass
        
        peak_coherence = max(coherence_from_notes) if coherence_from_notes else 0.95
        
        alpha_target = 0.85
        gamma_target = 0.35
        for s in best_sessions:
            dominant = s.get('dominant_brainwave', '') or ''
            if 'Alpha' in dominant and 'Gamma' in dominant:
                alpha_target = 0.90
                gamma_target = 0.45
                break
            elif 'Alpha' in dominant:
                alpha_target = 0.85
        
        dominant_patterns = [s.get('dominant_brainwave') for s in best_sessions if s.get('dominant_brainwave')]
        most_common_pattern = max(set(dominant_patterns), key=dominant_patterns.count) if dominant_patterns else "Alpha"
        
        session_types = [s.get('session_type') for s in best_sessions if s.get('session_type')]
        best_type = max(set(session_types), key=session_types.count) if session_types else "Unknown"
        
        return OptimalStateSignature(
            heart_rate_optimal=safe_avg(hr_values) or 55.0,
            hrv_rmssd_optimal=safe_max(rmssd_values) or 90.0,
            hrv_sdnn_optimal=safe_max(sdnn_values) or 60.0,
            lcc_peak=min(1.0, peak_lcc),
            gile_peak=peak_gile,
            coherence_peak=min(1.0, peak_coherence),
            alpha_target=alpha_target,
            gamma_target=gamma_target,
            pns_optimal=safe_max(pns_values) or 2.0,
            stress_index_optimal=min([v for v in stress_values if v and v > 0] or [5.0]),
            dominant_brainwave_pattern=most_common_pattern,
            best_session_type=best_type,
            peak_faah_tier=4,
            sessions_analyzed=len(best_sessions),
            confidence_score=min(1.0, len(best_sessions) / 5.0)
        )
    
    def _get_default_optimal_signature(self) -> OptimalStateSignature:
        """Default optimal signature based on Brandon's known peak states"""
        return OptimalStateSignature(
            heart_rate_optimal=53.0,
            hrv_rmssd_optimal=90.0,
            hrv_sdnn_optimal=58.0,
            lcc_peak=1.0,
            gile_peak=0.973,
            coherence_peak=0.999,
            alpha_target=0.90,
            gamma_target=0.45,
            pns_optimal=2.05,
            stress_index_optimal=2.1,
            dominant_brainwave_pattern="Alpha-Theta-Gamma",
            best_session_type="POSITIVE_ENERGY_FAAH_ENHANCED",
            peak_faah_tier=4,
            sessions_analyzed=4,
            confidence_score=0.8
        )
    
    def _identify_best_protocols(self, profile: UserProfile) -> List[str]:
        """Identify which protocol types work best for this user"""
        if not profile.session_history:
            return ["FAAH_ENHANCED", "POSITIVE_ENERGY"]
        
        type_scores = {}
        for session in profile.session_history:
            stype = session.get('session_type', 'unknown')
            gile = session.get('gile_score', 0) or 0
            if stype not in type_scores:
                type_scores[stype] = []
            type_scores[stype].append(gile)
        
        avg_scores = {k: np.mean(v) for k, v in type_scores.items()}
        sorted_types = sorted(avg_scores.keys(), key=lambda x: avg_scores[x], reverse=True)
        return sorted_types[:3]
    
    def _calculate_avg_improvement(self, profile: UserProfile) -> float:
        """Calculate average GILE improvement across sessions"""
        if len(profile.session_history) < 2:
            return 0.0
        
        gile_scores = [s.get('gile_score', 0) for s in profile.session_history if s.get('gile_score')]
        if len(gile_scores) < 2:
            return 0.0
        
        improvements = []
        for i in range(len(gile_scores) - 1):
            if gile_scores[i] > 0:
                improvement = (gile_scores[i] - gile_scores[i+1]) / gile_scores[i+1] if gile_scores[i+1] > 0 else 0
                improvements.append(improvement)
        
        return np.mean(improvements) if improvements else 0.0
    
    def _calculate_profile_confidence(self, profile: UserProfile) -> float:
        """Calculate confidence in profile accuracy"""
        confidence = 0.0
        
        if profile.session_history:
            confidence += min(0.3, len(profile.session_history) * 0.05)
        
        if profile.hrv_history:
            confidence += min(0.2, len(profile.hrv_history) * 0.01)
        
        if profile.brainwave_history:
            confidence += min(0.2, len(profile.brainwave_history) * 0.01)
        
        if profile.genetic_profile:
            confidence += 0.15
        
        if profile.optimal_signature:
            confidence += profile.optimal_signature.confidence_score * 0.15
        
        return min(1.0, confidence)
    
    def get_optimal_signature(self) -> OptimalStateSignature:
        """Get the user's optimal state signature (loads if needed)"""
        if self._optimal_signature is None:
            self.load_profile()
        return self._optimal_signature or self._get_default_optimal_signature()
    
    def get_profile(self) -> UserProfile:
        """Get the full user profile (loads if needed)"""
        if self._profile is None:
            self.load_profile()
        return self._profile
    
    def create_current_state(
        self,
        heart_rate: float = 72.0,
        hrv_rmssd: float = 45.0,
        coherence: float = 0.5,
        lcc: float = 0.5,
        gile: float = 0.0,
        alpha: float = 0.3,
        gamma: float = 0.1,
        stress_index: float = 50.0
    ) -> CurrentStateVector:
        """Create a current state vector for comparison"""
        return CurrentStateVector(
            heart_rate=heart_rate,
            hrv_rmssd=hrv_rmssd,
            coherence=coherence,
            lcc=lcc,
            gile=gile,
            alpha=alpha,
            gamma=gamma,
            stress_index=stress_index
        )
    
    def get_targeting_recommendations(
        self,
        current_state: CurrentStateVector
    ) -> Dict[str, Any]:
        """
        Get personalized recommendations for reaching optimal state.
        This is the core of "targeting YOU in the PRESENT."
        """
        optimal = self.get_optimal_signature()
        profile = self.get_profile()
        
        distances = current_state.distance_from_optimal(optimal)
        progress = current_state.progress_percentage(optimal)
        
        priority_metrics = sorted(distances.keys(), key=lambda k: distances[k], reverse=True)[:3]
        
        recommendations = []
        
        if distances.get('hrv', 0) > 0.3:
            recommendations.append({
                'focus': 'HRV Improvement',
                'technique': 'Coherent breathing at 6 breaths/min',
                'target': f'Raise RMSSD from {current_state.hrv_rmssd:.0f}ms toward {optimal.hrv_rmssd_optimal:.0f}ms',
                'priority': 1 if 'hrv' in priority_metrics[:2] else 2
            })
        
        if distances.get('lcc', 0) > 0.2:
            recommendations.append({
                'focus': 'LCC Enhancement',
                'technique': 'Heart-focused appreciation with sustained attention',
                'target': f'Increase LCC from {current_state.lcc*100:.0f}% toward {optimal.lcc_peak*100:.0f}%',
                'priority': 1 if 'lcc' in priority_metrics[:2] else 2
            })
        
        if distances.get('gile', 0) > 0.2:
            recommendations.append({
                'focus': 'GILE Activation',
                'technique': 'Gratitude flooding + love intention',
                'target': f'Raise GILE from {current_state.gile:.3f} toward {optimal.gile_peak:.3f}',
                'priority': 1 if 'gile' in priority_metrics[:2] else 2
            })
        
        if distances.get('stress', 0) > 0.3:
            recommendations.append({
                'focus': 'Stress Reduction',
                'technique': 'Cyclic sighing (double inhale, long exhale)',
                'target': f'Reduce stress from {current_state.stress_index:.0f} toward {optimal.stress_index_optimal:.0f}',
                'priority': 1 if 'stress' in priority_metrics[:2] else 2
            })
        
        if profile.best_protocol_types:
            best_protocol = profile.best_protocol_types[0]
        else:
            best_protocol = optimal.best_session_type
        
        return {
            'current_progress': progress,
            'distance_to_optimal': 1.0 - progress/100,
            'priority_metrics': priority_metrics,
            'distances': distances,
            'recommendations': sorted(recommendations, key=lambda x: x['priority']),
            'recommended_protocol': best_protocol,
            'optimal_signature': {
                'hr': optimal.heart_rate_optimal,
                'hrv': optimal.hrv_rmssd_optimal,
                'lcc': optimal.lcc_peak,
                'gile': optimal.gile_peak,
                'coherence': optimal.coherence_peak,
                'brainwave_pattern': optimal.dominant_brainwave_pattern
            },
            'profile_confidence': profile.profile_confidence,
            'sessions_analyzed': optimal.sessions_analyzed
        }


_profile_service_instance: Optional[UserProfileService] = None

def get_profile_service(user_id: str = "brandon") -> UserProfileService:
    """Get singleton instance of UserProfileService"""
    global _profile_service_instance
    if _profile_service_instance is None or _profile_service_instance.user_id != user_id:
        _profile_service_instance = UserProfileService(user_id)
    return _profile_service_instance
