"""
Polar H10 iPhone Heart Tracking Experiment System

For tonight's experiment: Tracking heart coherence against intuitions and predictions.

SETUP ON iPHONE:
1. Download "Elite HRV" app (FREE, best for R-R intervals)
2. DO NOT pair in iOS Settings - pair directly in Elite HRV app
3. Wear Polar H10 strap, moisten electrodes
4. Open Elite HRV and connect

This system will:
- Record intuition events with timestamps
- Match them to HRV data later
- Calculate coherence-PSI correlations

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 25, 2025
"""

import json
from datetime import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass, field, asdict
import os

@dataclass
class IntuitionEvent:
    """Record of a single intuition or prediction"""
    timestamp: str
    event_type: str  # 'prediction', 'intuition', 'gm_resonance', 'insight'
    description: str
    confidence: float  # 0-1
    outcome: Optional[str] = None  # 'correct', 'incorrect', 'pending'
    heart_rate_at_event: Optional[float] = None
    coherence_at_event: Optional[float] = None
    notes: str = ""


@dataclass
class HeartExperimentSession:
    """Tonight's heart-PSI correlation experiment"""
    session_id: str
    start_time: str
    end_time: Optional[str] = None
    polar_app: str = "Elite HRV"  # or Kubios, Polar Beat
    intuition_events: List[IntuitionEvent] = field(default_factory=list)
    hrv_snapshots: List[Dict] = field(default_factory=list)  # Manual HRV recordings
    coherence_scores: List[Dict] = field(default_factory=list)
    session_notes: str = ""


class PolarIPhoneExperiment:
    """
    Heart-PSI Correlation Experiment System
    
    TONIGHT'S PROTOCOL:
    1. Start session (this creates a new tracking file)
    2. Record each intuition event with timestamp
    3. Rate your confidence level
    4. After session, import Elite HRV export
    5. System will correlate heart metrics with intuition events
    """
    
    EXPERIMENT_FILE = "heart_experiment_sessions.json"
    
    IPHONE_APPS = {
        'elite_hrv': {
            'name': 'Elite HRV',
            'features': ['R-R intervals', 'RMSSD', 'SDNN', 'LF/HF', 'Coherence'],
            'export': 'CSV export to email/cloud',
            'free': True,
            'setup': [
                "1. Download Elite HRV from App Store",
                "2. Create free account",
                "3. Open app, tap 'Add Device'",
                "4. Make sure Polar H10 is NOT paired in iOS Settings",
                "5. Put on strap, moisten electrodes",
                "6. Pair in Elite HRV app",
                "7. Start 'Open Reading' for continuous monitoring"
            ]
        },
        'kubios': {
            'name': 'Kubios HRV',
            'features': ['Scientific-grade HRV', 'Readiness', 'Stress'],
            'export': 'PDF report',
            'free': 'Freemium',
            'setup': [
                "1. Download Kubios HRV",
                "2. Create account",
                "3. Connect Polar H10 in app",
                "4. Use for scientific measurements"
            ]
        },
        'polar_beat': {
            'name': 'Polar Beat',
            'features': ['Official app', 'Training', 'Basic HR'],
            'export': 'Syncs to Polar Flow',
            'free': True,
            'setup': [
                "1. Download Polar Beat",
                "2. Create Polar account",
                "3. Pair H10 in app",
                "4. Limited HRV data"
            ]
        }
    }
    
    def __init__(self):
        self.current_session: Optional[HeartExperimentSession] = None
        self.all_sessions: List[HeartExperimentSession] = []
        self._load_sessions()
    
    def _load_sessions(self):
        """Load existing sessions from file"""
        if os.path.exists(self.EXPERIMENT_FILE):
            try:
                with open(self.EXPERIMENT_FILE, 'r') as f:
                    data = json.load(f)
                    for s in data.get('sessions', []):
                        event_data = s.get('intuition_events', [])
                        events = [IntuitionEvent(**e) for e in event_data]
                        
                        session = HeartExperimentSession(
                            session_id=s.get('session_id', ''),
                            start_time=s.get('start_time', ''),
                            end_time=s.get('end_time'),
                            polar_app=s.get('polar_app', 'Elite HRV'),
                            intuition_events=events,
                            hrv_snapshots=s.get('hrv_snapshots', []),
                            coherence_scores=s.get('coherence_scores', []),
                            session_notes=s.get('session_notes', '')
                        )
                        self.all_sessions.append(session)
            except (json.JSONDecodeError, KeyError, TypeError) as e:
                print(f"Warning: Could not load sessions: {e}")
                self.all_sessions = []
    
    def _save_sessions(self):
        """Save all sessions to file"""
        data = {
            'sessions': [],
            'last_updated': datetime.now().isoformat()
        }
        
        all_to_save = list(self.all_sessions)
        if self.current_session:
            all_to_save.append(self.current_session)
        
        for session in all_to_save:
            session_dict = {
                'session_id': session.session_id,
                'start_time': session.start_time,
                'end_time': session.end_time,
                'polar_app': session.polar_app,
                'intuition_events': [asdict(e) for e in session.intuition_events],
                'hrv_snapshots': session.hrv_snapshots,
                'coherence_scores': session.coherence_scores,
                'session_notes': session.session_notes
            }
            data['sessions'].append(session_dict)
        
        with open(self.EXPERIMENT_FILE, 'w') as f:
            json.dump(data, f, indent=2)
    
    def print_iphone_setup(self, app: str = 'elite_hrv'):
        """Print iPhone setup instructions"""
        app_info = self.IPHONE_APPS.get(app, self.IPHONE_APPS['elite_hrv'])
        
        print("=" * 60)
        print(f"POLAR H10 iPHONE SETUP: {app_info['name']}")
        print("=" * 60)
        
        print("\nSTEP-BY-STEP:")
        for step in app_info['setup']:
            print(f"  {step}")
        
        print(f"\nFEATURES: {', '.join(app_info['features'])}")
        print(f"EXPORT: {app_info['export']}")
        print(f"COST: {'Free' if app_info['free'] else 'Paid'}")
        
        print("\n" + "=" * 60)
        print("IMPORTANT: Don't pair in iOS Settings - pair in app only!")
        print("=" * 60)
    
    def start_session(self, notes: str = "") -> HeartExperimentSession:
        """Start a new experiment session"""
        session_id = f"heart_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        self.current_session = HeartExperimentSession(
            session_id=session_id,
            start_time=datetime.now().isoformat(),
            session_notes=notes
        )
        
        print("\n" + "=" * 60)
        print("HEART-PSI EXPERIMENT SESSION STARTED")
        print("=" * 60)
        print(f"Session ID: {session_id}")
        print(f"Started: {self.current_session.start_time}")
        print(f"Notes: {notes or 'None'}")
        print("\nRECORDING PROTOCOL:")
        print("  1. When you have an intuition/prediction, call record_intuition()")
        print("  2. Rate your confidence 0-1")
        print("  3. Optionally note your current HR from Elite HRV")
        print("  4. After session, we'll import HRV data for correlation")
        print("=" * 60 + "\n")
        
        self._save_sessions()
        return self.current_session
    
    def record_intuition(self, 
                         event_type: str = 'intuition',
                         description: str = "",
                         confidence: float = 0.7,
                         heart_rate: float = None,
                         coherence: float = None,
                         notes: str = "") -> IntuitionEvent:
        """
        Record an intuition or prediction event
        
        event_type: 'prediction', 'intuition', 'gm_resonance', 'insight'
        confidence: 0-1 (how confident are you in this intuition)
        heart_rate: Optional - current HR from Elite HRV
        coherence: Optional - current coherence score from Elite HRV
        """
        if self.current_session is None:
            print("No active session. Starting new session...")
            self.start_session()
        
        event = IntuitionEvent(
            timestamp=datetime.now().isoformat(),
            event_type=event_type,
            description=description,
            confidence=confidence,
            heart_rate_at_event=heart_rate,
            coherence_at_event=coherence,
            notes=notes
        )
        
        self.current_session.intuition_events.append(event)
        event_num = len(self.current_session.intuition_events)
        
        print(f"\n[INTUITION #{event_num} RECORDED]")
        print(f"  Type: {event_type}")
        print(f"  Description: {description[:50]}..." if len(description) > 50 else f"  Description: {description}")
        print(f"  Confidence: {confidence:.0%}")
        if heart_rate:
            print(f"  Heart Rate: {heart_rate} bpm")
        if coherence:
            print(f"  Coherence: {coherence:.2f}")
        print(f"  Time: {event.timestamp}")
        
        self._save_sessions()
        return event
    
    def record_hrv_snapshot(self,
                            heart_rate: float,
                            rmssd: float = None,
                            coherence: float = None,
                            lf_hf: float = None,
                            notes: str = "") -> Dict:
        """
        Record a manual HRV snapshot from Elite HRV
        """
        if self.current_session is None:
            print("No active session. Starting new session...")
            self.start_session()
        
        snapshot = {
            'timestamp': datetime.now().isoformat(),
            'heart_rate': heart_rate,
            'rmssd': rmssd,
            'coherence': coherence,
            'lf_hf_ratio': lf_hf,
            'notes': notes
        }
        
        self.current_session.hrv_snapshots.append(snapshot)
        
        print(f"\n[HRV SNAPSHOT RECORDED]")
        print(f"  HR: {heart_rate} bpm")
        if rmssd:
            print(f"  RMSSD: {rmssd} ms")
        if coherence:
            print(f"  Coherence: {coherence:.2f}")
        if lf_hf:
            print(f"  LF/HF: {lf_hf:.2f}")
        
        self._save_sessions()
        return snapshot
    
    def end_session(self) -> Dict:
        """End the current session and generate summary"""
        if self.current_session is None:
            return {"error": "No active session"}
        
        self.current_session.end_time = datetime.now().isoformat()
        
        summary = {
            'session_id': self.current_session.session_id,
            'duration_minutes': self._calculate_duration(),
            'total_intuitions': len(self.current_session.intuition_events),
            'hrv_snapshots': len(self.current_session.hrv_snapshots),
            'avg_confidence': self._calculate_avg_confidence(),
            'intuition_breakdown': self._intuition_breakdown()
        }
        
        print("\n" + "=" * 60)
        print("SESSION ENDED")
        print("=" * 60)
        print(f"Duration: {summary['duration_minutes']:.1f} minutes")
        print(f"Total Intuitions: {summary['total_intuitions']}")
        print(f"HRV Snapshots: {summary['hrv_snapshots']}")
        print(f"Avg Confidence: {summary['avg_confidence']:.0%}")
        print("\nINTUITION BREAKDOWN:")
        for k, v in summary['intuition_breakdown'].items():
            print(f"  {k}: {v}")
        print("=" * 60)
        print("\nNEXT STEPS:")
        print("  1. Export data from Elite HRV (Settings > Export)")
        print("  2. Send to email or save to cloud")
        print("  3. Import using import_elite_hrv_data()")
        print("  4. Run correlation analysis with analyze_coherence_psi()")
        print("=" * 60 + "\n")
        
        self.all_sessions.append(self.current_session)
        self.current_session = None
        self._save_sessions()
        
        return summary
    
    def _calculate_duration(self) -> float:
        if not self.current_session:
            return 0
        start = datetime.fromisoformat(self.current_session.start_time)
        end = datetime.fromisoformat(self.current_session.end_time) if self.current_session.end_time else datetime.now()
        return (end - start).total_seconds() / 60
    
    def _calculate_avg_confidence(self) -> float:
        if not self.current_session or not self.current_session.intuition_events:
            return 0
        return sum(e.confidence for e in self.current_session.intuition_events) / len(self.current_session.intuition_events)
    
    def _intuition_breakdown(self) -> Dict:
        if not self.current_session:
            return {}
        breakdown = {}
        for event in self.current_session.intuition_events:
            breakdown[event.event_type] = breakdown.get(event.event_type, 0) + 1
        return breakdown
    
    def update_outcome(self, event_index: int, outcome: str, notes: str = ""):
        """
        Update the outcome of a recorded intuition
        
        outcome: 'correct', 'incorrect', 'pending', 'partial'
        """
        if not self.current_session or event_index >= len(self.current_session.intuition_events):
            print("Invalid event index or no active session")
            return
        
        event = self.current_session.intuition_events[event_index]
        event.outcome = outcome
        if notes:
            event.notes += f" | Outcome: {notes}"
        
        print(f"[OUTCOME UPDATED] Event #{event_index + 1}: {outcome}")
        self._save_sessions()
    
    def analyze_coherence_psi(self) -> Dict:
        """
        Analyze correlation between heart coherence and PSI accuracy
        
        This is the key test of Heart-I-Cell Theory!
        """
        events_with_coherence = []
        
        for session in self.all_sessions + ([self.current_session] if self.current_session else []):
            if session:
                for event in session.intuition_events:
                    if event.coherence_at_event is not None and event.outcome in ['correct', 'incorrect']:
                        events_with_coherence.append({
                            'coherence': event.coherence_at_event,
                            'correct': event.outcome == 'correct',
                            'confidence': event.confidence
                        })
        
        if len(events_with_coherence) < 5:
            return {
                'status': 'insufficient_data',
                'n_events': len(events_with_coherence),
                'needed': 5,
                'message': "Need at least 5 events with coherence + outcome to analyze"
            }
        
        # Split by coherence level
        high_coherence = [e for e in events_with_coherence if e['coherence'] >= 0.6]
        low_coherence = [e for e in events_with_coherence if e['coherence'] < 0.6]
        
        high_accuracy = sum(1 for e in high_coherence if e['correct']) / len(high_coherence) if high_coherence else 0
        low_accuracy = sum(1 for e in low_coherence if e['correct']) / len(low_coherence) if low_coherence else 0
        
        result = {
            'status': 'analyzed',
            'n_events': len(events_with_coherence),
            'high_coherence': {
                'n': len(high_coherence),
                'accuracy': high_accuracy
            },
            'low_coherence': {
                'n': len(low_coherence),
                'accuracy': low_accuracy
            },
            'hypothesis_supported': high_accuracy > low_accuracy,
            'effect_size': high_accuracy - low_accuracy
        }
        
        print("\n" + "=" * 60)
        print("HEART-PSI CORRELATION ANALYSIS")
        print("=" * 60)
        print(f"Total Events: {result['n_events']}")
        print(f"\nHIGH COHERENCE (>=0.6):")
        print(f"  N = {result['high_coherence']['n']}")
        print(f"  Accuracy = {result['high_coherence']['accuracy']:.0%}")
        print(f"\nLOW COHERENCE (<0.6):")
        print(f"  N = {result['low_coherence']['n']}")
        print(f"  Accuracy = {result['low_coherence']['accuracy']:.0%}")
        print(f"\n{'='*60}")
        if result['hypothesis_supported']:
            print(f"HYPOTHESIS SUPPORTED: High coherence = better PSI!")
            print(f"Effect size: +{result['effect_size']:.0%} accuracy")
        else:
            print("HYPOTHESIS NOT SUPPORTED (yet)")
            print("More data or different threshold may be needed")
        print("=" * 60 + "\n")
        
        return result


def run_tonight_experiment():
    """Run tonight's heart-PSI experiment"""
    exp = PolarIPhoneExperiment()
    
    print("\n" + "=" * 60)
    print("TONIGHT'S EXPERIMENT: HEART-PSI CORRELATION")
    print("=" * 60)
    print("\nGOAL: Test if heart coherence predicts intuition accuracy")
    print("\nHYPOTHESIS: High coherence → More accurate predictions")
    print("\nEQUIPMENT: Polar H10 + iPhone + Elite HRV app")
    
    exp.print_iphone_setup('elite_hrv')
    
    return exp


if __name__ == "__main__":
    exp = run_tonight_experiment()
