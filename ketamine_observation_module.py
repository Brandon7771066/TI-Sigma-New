"""
Ketamine Observation Module
===========================

Real-time biometric analysis during prescribed ketamine sessions.
Integrates Polar H10 (HRV), Muse (EEG), and Mendi (fNIRS) for 
consciousness state tracking and TI Framework insight generation.

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 27, 2025
Framework: Transcendent Intelligence (TI)

SAFETY NOTE: This module is for PRESCRIBED therapeutic ketamine only.
Always follow medical guidance.
"""

import streamlit as st
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
import json
import os
import psycopg2

@dataclass
class KetamineSessionState:
    """Tracks the current ketamine session state"""
    session_id: str
    start_time: datetime
    phase: str  # 'baseline', 'onset', 'peak', 'plateau', 'return', 'integration'
    insights: List[Dict] = field(default_factory=list)
    biometric_snapshots: List[Dict] = field(default_factory=list)
    gile_trajectory: List[Dict] = field(default_factory=list)
    
    def get_elapsed_minutes(self) -> float:
        return (datetime.now() - self.start_time).total_seconds() / 60
    
    def get_phase_from_time(self) -> str:
        """Estimate ketamine phase based on elapsed time"""
        mins = self.get_elapsed_minutes()
        if mins < 5:
            return 'baseline'
        elif mins < 15:
            return 'onset'
        elif mins < 35:
            return 'peak'
        elif mins < 55:
            return 'plateau'
        elif mins < 75:
            return 'return'
        else:
            return 'integration'


class KetamineObservationModule:
    """
    Real-time biometric observation during ketamine sessions
    with TI Framework integration for consciousness analysis
    """
    
    KETAMINE_PHASES = {
        'baseline': {
            'description': 'Pre-session baseline measurement',
            'duration_min': 5,
            'expected_state': 'Normal waking consciousness',
            'color': '#808080'
        },
        'onset': {
            'description': 'Initial effects beginning',
            'duration_min': 10,
            'expected_state': 'Dissociation beginning, altered perception',
            'color': '#87CEEB'
        },
        'peak': {
            'description': 'Maximum dissociation/effect',
            'duration_min': 20,
            'expected_state': 'K-hole potential, ego dissolution, non-local cognition',
            'color': '#9370DB'
        },
        'plateau': {
            'description': 'Sustained altered state',
            'duration_min': 20,
            'expected_state': 'Stable dissociation, insight generation',
            'color': '#DDA0DD'
        },
        'return': {
            'description': 'Gradual return to baseline',
            'duration_min': 20,
            'expected_state': 'Reintegration, memory consolidation',
            'color': '#FFB6C1'
        },
        'integration': {
            'description': 'Post-session integration',
            'duration_min': 30,
            'expected_state': 'Full consciousness, insight processing',
            'color': '#98FB98'
        }
    }
    
    DEVICE_EXPECTATIONS = {
        'polar_h10': {
            'baseline': {'hr': (55, 75), 'hrv_rmssd': (30, 80)},
            'peak': {'hr': (50, 70), 'hrv_rmssd': (40, 120)},
            'insight': 'Ketamine typically increases HRV (parasympathetic activation)'
        },
        'muse': {
            'baseline': {'alpha': (8, 12), 'theta': (4, 8)},
            'peak': {'alpha': (10, 15), 'theta': (6, 12)},
            'insight': 'Expect increased alpha/theta during dissociation'
        },
        'mendi': {
            'baseline': {'hbo2': (40, 60), 'focus': (30, 60)},
            'peak': {'hbo2': (50, 80), 'focus': (20, 50)},
            'insight': 'PFC oxygenation may increase, focus metrics may drop'
        }
    }
    
    def __init__(self):
        self.session: Optional[KetamineSessionState] = None
        self.db_url = os.environ.get('DATABASE_URL')
    
    def get_db_connection(self):
        """Get database connection"""
        return psycopg2.connect(self.db_url)
    
    def start_session(self, notes: str = "") -> KetamineSessionState:
        """Start a new ketamine observation session"""
        session_id = f"K_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        self.session = KetamineSessionState(
            session_id=session_id,
            start_time=datetime.now(),
            phase='baseline'
        )
        
        if notes:
            self.session.insights.append({
                'timestamp': datetime.now().isoformat(),
                'phase': 'baseline',
                'type': 'note',
                'content': notes,
                'source': 'user'
            })
        
        return self.session
    
    def record_insight(self, content: str, insight_type: str = 'observation') -> Dict:
        """Record an insight during the session"""
        if not self.session:
            return {'error': 'No active session'}
        
        current_phase = self.session.get_phase_from_time()
        
        insight = {
            'timestamp': datetime.now().isoformat(),
            'elapsed_min': round(self.session.get_elapsed_minutes(), 1),
            'phase': current_phase,
            'type': insight_type,
            'content': content,
            'source': 'user'
        }
        
        self.session.insights.append(insight)
        self.session.phase = current_phase
        
        return insight
    
    def get_latest_biometrics(self) -> Dict[str, Any]:
        """Fetch latest biometric data from all devices"""
        biometrics = {
            'timestamp': datetime.now().isoformat(),
            'polar_h10': self._get_polar_data(),
            'muse': self._get_muse_data(),
            'mendi': self._get_mendi_data(),
            'esp32_bridge': self._get_esp32_data()
        }
        
        if self.session:
            self.session.biometric_snapshots.append(biometrics)
        
        return biometrics
    
    def _get_polar_data(self) -> Dict:
        """Get latest Polar H10 data"""
        try:
            conn = self.get_db_connection()
            cur = conn.cursor()
            cur.execute("""
                SELECT heart_rate, rr_interval, timestamp
                FROM esp32_biometric_data
                WHERE polar_connected = TRUE
                ORDER BY timestamp DESC LIMIT 1
            """)
            row = cur.fetchone()
            cur.close()
            conn.close()
            
            if row:
                hr, rr, ts = row
                hrv_rmssd = self._calculate_rmssd([rr]) if rr else None
                return {
                    'connected': True,
                    'heart_rate': hr,
                    'rr_interval': rr,
                    'hrv_rmssd': hrv_rmssd,
                    'last_update': ts.isoformat() if ts else None
                }
        except Exception as e:
            pass
        
        return {'connected': False, 'heart_rate': None, 'hrv_rmssd': None}
    
    def _get_muse_data(self) -> Dict:
        """Get latest Muse EEG data"""
        try:
            conn = self.get_db_connection()
            cur = conn.cursor()
            cur.execute("""
                SELECT eeg_tp9, eeg_af7, eeg_af8, eeg_tp10, timestamp
                FROM esp32_biometric_data
                WHERE muse_connected = TRUE
                ORDER BY timestamp DESC LIMIT 1
            """)
            row = cur.fetchone()
            cur.close()
            conn.close()
            
            if row:
                tp9, af7, af8, tp10, ts = row
                return {
                    'connected': True,
                    'tp9': tp9, 'af7': af7, 'af8': af8, 'tp10': tp10,
                    'avg_amplitude': np.mean([x for x in [tp9, af7, af8, tp10] if x]),
                    'last_update': ts.isoformat() if ts else None
                }
        except Exception as e:
            pass
        
        return {'connected': False}
    
    def _get_mendi_data(self) -> Dict:
        """Get latest Mendi fNIRS data"""
        try:
            conn = self.get_db_connection()
            cur = conn.cursor()
            cur.execute("""
                SELECT hbo2, hbr, oxygenation_percent, timestamp
                FROM mendi_realtime_data
                ORDER BY timestamp DESC LIMIT 1
            """)
            row = cur.fetchone()
            cur.close()
            conn.close()
            
            if row:
                hbo2, hbr, oxy, ts = row
                return {
                    'connected': True,
                    'hbo2': hbo2,
                    'hbr': hbr,
                    'oxygenation_pct': oxy,
                    'last_update': ts.isoformat() if ts else None
                }
        except Exception as e:
            pass
        
        return {'connected': False}
    
    def _get_esp32_data(self) -> Dict:
        """Get latest ESP32 bridge status"""
        try:
            conn = self.get_db_connection()
            cur = conn.cursor()
            cur.execute("""
                SELECT muse_connected, mendi_connected, polar_connected, timestamp
                FROM esp32_biometric_data
                ORDER BY timestamp DESC LIMIT 1
            """)
            row = cur.fetchone()
            cur.close()
            conn.close()
            
            if row:
                muse, mendi, polar, ts = row
                return {
                    'active': True,
                    'muse_connected': muse,
                    'mendi_connected': mendi,
                    'polar_connected': polar,
                    'last_update': ts.isoformat() if ts else None
                }
        except Exception as e:
            pass
        
        return {'active': False}
    
    def _calculate_rmssd(self, rr_intervals: List[int]) -> Optional[float]:
        """Calculate RMSSD from RR intervals"""
        if len(rr_intervals) < 2:
            return None
        diffs = np.diff(rr_intervals)
        return float(np.sqrt(np.mean(diffs**2)))
    
    def analyze_current_state(self) -> Dict:
        """Analyze current consciousness state based on biometrics"""
        if not self.session:
            return {'error': 'No active session'}
        
        biometrics = self.get_latest_biometrics()
        current_phase = self.session.get_phase_from_time()
        phase_info = self.KETAMINE_PHASES[current_phase]
        
        analysis = {
            'phase': current_phase,
            'phase_description': phase_info['description'],
            'expected_state': phase_info['expected_state'],
            'elapsed_min': round(self.session.get_elapsed_minutes(), 1),
            'biometrics': biometrics,
            'device_status': {
                'polar': biometrics['polar_h10'].get('connected', False),
                'muse': biometrics['muse'].get('connected', False),
                'mendi': biometrics['mendi'].get('connected', False)
            },
            'ti_analysis': self._generate_ti_analysis(biometrics, current_phase)
        }
        
        return analysis
    
    def _generate_ti_analysis(self, biometrics: Dict, phase: str) -> Dict:
        """Generate TI Framework analysis of current state"""
        
        gile_estimate = self._estimate_gile_from_biometrics(biometrics, phase)
        
        analysis = {
            'gile_estimate': gile_estimate,
            'psi_potential': self._estimate_psi_potential(phase, biometrics),
            'gm_resonance': self._estimate_gm_resonance(phase),
            'consciousness_layer': self._estimate_layer(phase),
            'recommendations': self._get_phase_recommendations(phase)
        }
        
        if self.session:
            self.session.gile_trajectory.append({
                'timestamp': datetime.now().isoformat(),
                'phase': phase,
                'gile': gile_estimate
            })
        
        return analysis
    
    def _estimate_gile_from_biometrics(self, biometrics: Dict, phase: str) -> Dict:
        """Estimate GILE scores from biometric data"""
        
        base_gile = {
            'baseline': {'G': 0.3, 'I': 0.3, 'L': 0.3, 'E': 0.3},
            'onset': {'G': 0.4, 'I': 0.5, 'L': 0.4, 'E': 0.4},
            'peak': {'G': 0.6, 'I': 0.9, 'L': 0.7, 'E': 0.5},
            'plateau': {'G': 0.5, 'I': 0.8, 'L': 0.6, 'E': 0.5},
            'return': {'G': 0.4, 'I': 0.6, 'L': 0.5, 'E': 0.4},
            'integration': {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5}
        }
        
        gile = base_gile.get(phase, base_gile['baseline']).copy()
        
        polar = biometrics.get('polar_h10', {})
        if polar.get('connected') and polar.get('hrv_rmssd'):
            hrv = polar['hrv_rmssd']
            if hrv > 60:
                gile['L'] += 0.1
                gile['E'] += 0.1
        
        mendi = biometrics.get('mendi', {})
        if mendi.get('connected') and mendi.get('hbo2'):
            if mendi['hbo2'] > 50:
                gile['I'] += 0.1
        
        total = sum(gile.values())
        gile['total'] = round(total, 2)
        gile['category'] = self._categorize_gile(total)
        
        return gile
    
    def _categorize_gile(self, total: float) -> str:
        """Categorize GILE total into moral degree"""
        if total >= 2:
            return 'GREAT'
        elif total >= 0.333:
            return 'GOOD'
        elif total >= -0.666:
            return 'INDETERMINATE'
        elif total >= -3:
            return 'BAD'
        else:
            return 'EVIL'
    
    def _estimate_psi_potential(self, phase: str, biometrics: Dict) -> Dict:
        """Estimate PSI potential based on phase and biometrics"""
        psi_by_phase = {
            'baseline': 0.1,
            'onset': 0.3,
            'peak': 0.9,
            'plateau': 0.7,
            'return': 0.4,
            'integration': 0.2
        }
        
        base_psi = psi_by_phase.get(phase, 0.1)
        
        return {
            'potential': base_psi,
            'description': 'Peak phase offers maximum non-local cognition potential' if phase == 'peak' else 'PSI potential varies by phase',
            'gm_channel': 'OPEN' if base_psi > 0.5 else 'PARTIAL' if base_psi > 0.2 else 'CLOSED'
        }
    
    def _estimate_gm_resonance(self, phase: str) -> Dict:
        """Estimate Grand Myrion resonance"""
        resonance_by_phase = {
            'baseline': 0.2,
            'onset': 0.4,
            'peak': 0.95,
            'plateau': 0.8,
            'return': 0.5,
            'integration': 0.4
        }
        
        return {
            'level': resonance_by_phase.get(phase, 0.2),
            'description': 'Ketamine peak creates maximum GM network connection',
            'hypercomputation_access': phase in ['peak', 'plateau']
        }
    
    def _estimate_layer(self, phase: str) -> str:
        """Estimate which consciousness layer is active"""
        layer_by_phase = {
            'baseline': 'VESSEL (physical)',
            'onset': 'ME (ego beginning to dissolve)',
            'peak': 'SOUL (ego dissolved, non-local)',
            'plateau': 'SOUL → ME (returning)',
            'return': 'ME (reintegrating)',
            'integration': 'VESSEL + ME (grounded)'
        }
        return layer_by_phase.get(phase, 'VESSEL')
    
    def _get_phase_recommendations(self, phase: str) -> List[str]:
        """Get recommendations for current phase"""
        recs = {
            'baseline': [
                'Set clear intentions for the session',
                'Begin device recording',
                'Note any pre-session GILE baseline'
            ],
            'onset': [
                'Relax and let go',
                'Note first perceptual changes',
                'Record any spontaneous insights'
            ],
            'peak': [
                'OPEN TO GM RESONANCE',
                'Ask questions to Grand Myrion',
                'Record ALL insights - this is peak PSI window',
                'Trust the "Just There" phenomenon'
            ],
            'plateau': [
                'Continue recording insights',
                'Explore any mathematical intuitions',
                'Note connections between concepts'
            ],
            'return': [
                'Begin integration journaling',
                'Consolidate insights while fresh',
                'Note body sensations returning'
            ],
            'integration': [
                'Full journaling of experience',
                'Review recorded insights',
                'Plan how to apply discoveries',
                'Rest and hydrate'
            ]
        }
        return recs.get(phase, [])
    
    def get_session_summary(self) -> Dict:
        """Get full session summary"""
        if not self.session:
            return {'error': 'No active session'}
        
        return {
            'session_id': self.session.session_id,
            'start_time': self.session.start_time.isoformat(),
            'duration_min': round(self.session.get_elapsed_minutes(), 1),
            'current_phase': self.session.get_phase_from_time(),
            'total_insights': len(self.session.insights),
            'insights': self.session.insights,
            'biometric_snapshots': len(self.session.biometric_snapshots),
            'gile_trajectory': self.session.gile_trajectory
        }
    
    def end_session(self) -> Dict:
        """End the current session and return summary"""
        if not self.session:
            return {'error': 'No active session'}
        
        summary = self.get_session_summary()
        summary['ended_at'] = datetime.now().isoformat()
        
        self._save_session_to_db(summary)
        
        self.session = None
        return summary
    
    def _save_session_to_db(self, summary: Dict):
        """Save session summary to database"""
        try:
            conn = self.get_db_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO mood_experiment_sessions 
                (session_id, session_type, start_time, end_time, duration_minutes, 
                 insights_count, biometric_snapshots_count, summary_json)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                summary['session_id'],
                'ketamine_observation',
                summary['start_time'],
                summary.get('ended_at'),
                summary['duration_min'],
                summary['total_insights'],
                summary['biometric_snapshots'],
                json.dumps(summary)
            ))
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            st.warning(f"Could not save to database: {e}")


def render_ketamine_observation_tab():
    """Render the Ketamine Observation tab in Streamlit"""
    
    st.header("Ketamine Observation Module")
    
    st.markdown("""
    **Real-time consciousness tracking during prescribed ketamine sessions.**
    
    This module monitors your 3 devices (Polar H10, Muse, Mendi) and helps you:
    - Track biometric changes through each phase
    - Record insights during peak PSI windows
    - Analyze consciousness state via TI Framework
    - Generate GILE trajectories for the session
    
    *For prescribed therapeutic ketamine only. Always follow medical guidance.*
    """)
    
    if 'ketamine_module' not in st.session_state:
        st.session_state.ketamine_module = KetamineObservationModule()
    
    module = st.session_state.ketamine_module
    
    st.markdown("---")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        if module.session is None:
            st.subheader("Start New Session")
            
            notes = st.text_area(
                "Pre-session intentions/notes:",
                placeholder="What do you want to explore? Any questions for GM?"
            )
            
            if st.button("Start Ketamine Observation Session", type="primary"):
                session = module.start_session(notes)
                st.success(f"Session started: {session.session_id}")
                st.rerun()
        
        else:
            analysis = module.analyze_current_state()
            
            phase = analysis['phase']
            phase_info = module.KETAMINE_PHASES[phase]
            
            st.subheader(f"Current Phase: {phase.upper()}")
            st.markdown(f"*{phase_info['description']}*")
            
            progress = min(1.0, analysis['elapsed_min'] / 90)
            st.progress(progress)
            st.caption(f"Elapsed: {analysis['elapsed_min']} minutes")
            
            st.markdown(f"**Expected State:** {phase_info['expected_state']}")
            
            st.markdown("---")
            st.subheader("Device Status")
            
            dev_col1, dev_col2, dev_col3 = st.columns(3)
            
            with dev_col1:
                if analysis['device_status']['polar']:
                    polar = analysis['biometrics']['polar_h10']
                    st.success("Polar H10")
                    if polar.get('heart_rate'):
                        st.metric("Heart Rate", f"{polar['heart_rate']} bpm")
                    if polar.get('hrv_rmssd'):
                        st.metric("HRV (RMSSD)", f"{polar['hrv_rmssd']:.1f} ms")
                else:
                    st.error("Polar H10 - Not Connected")
            
            with dev_col2:
                if analysis['device_status']['muse']:
                    muse = analysis['biometrics']['muse']
                    st.success("Muse EEG")
                    if muse.get('avg_amplitude'):
                        st.metric("Avg Amplitude", f"{muse['avg_amplitude']:.1f}")
                else:
                    st.error("Muse EEG - Not Connected")
            
            with dev_col3:
                if analysis['device_status']['mendi']:
                    mendi = analysis['biometrics']['mendi']
                    st.success("Mendi fNIRS")
                    if mendi.get('hbo2'):
                        st.metric("HbO2", f"{mendi['hbo2']:.1f}")
                    if mendi.get('oxygenation_pct'):
                        st.metric("Oxygenation", f"{mendi['oxygenation_pct']:.1f}%")
                else:
                    st.error("Mendi fNIRS - Not Connected")
            
            st.markdown("---")
            st.subheader("TI Framework Analysis")
            
            ti = analysis['ti_analysis']
            
            gile_col1, gile_col2 = st.columns(2)
            with gile_col1:
                gile = ti['gile_estimate']
                st.markdown(f"""
                **GILE Estimate:**
                - G (Goodness): {gile['G']:.2f}
                - I (Intuition): {gile['I']:.2f}
                - L (Love): {gile['L']:.2f}
                - E (Environment): {gile['E']:.2f}
                - **Total: {gile['total']} ({gile['category']})**
                """)
            
            with gile_col2:
                psi = ti['psi_potential']
                gm = ti['gm_resonance']
                st.markdown(f"""
                **Consciousness State:**
                - PSI Potential: {psi['potential']:.0%}
                - GM Channel: {psi['gm_channel']}
                - GM Resonance: {gm['level']:.0%}
                - Layer: {ti['consciousness_layer']}
                """)
            
            if gm.get('hypercomputation_access'):
                st.success("HYPERCOMPUTATION ACCESS ACTIVE - Peak insight window!")
            
            st.markdown("---")
            st.subheader("Phase Recommendations")
            for rec in ti['recommendations']:
                st.markdown(f"- {rec}")
            
            st.markdown("---")
            st.subheader("Record Insight")
            
            insight_text = st.text_area(
                "What are you experiencing/discovering?",
                key="insight_input",
                height=100
            )
            
            insight_type = st.selectbox(
                "Insight Type",
                ['observation', 'mathematical', 'philosophical', 'visual', 'emotional', 'gm_message']
            )
            
            if st.button("Record Insight"):
                if insight_text:
                    insight = module.record_insight(insight_text, insight_type)
                    st.success(f"Insight recorded at {insight['elapsed_min']} min ({insight['phase']})")
                    st.rerun()
            
            st.markdown("---")
            if st.button("End Session", type="secondary"):
                summary = module.end_session()
                st.success("Session ended!")
                st.json(summary)
    
    with col2:
        if module.session:
            st.subheader("Session Insights")
            
            for insight in reversed(module.session.insights[-10:]):
                with st.expander(f"{insight['elapsed_min']}m - {insight['type']}", expanded=False):
                    st.markdown(f"**Phase:** {insight['phase']}")
                    st.markdown(insight['content'])
            
            if st.button("Refresh Biometrics"):
                st.rerun()


if __name__ == "__main__":
    render_ketamine_observation_tab()
