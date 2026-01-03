"""
Synchronization Detection System
Detects when user crosses key coherence thresholds (0.85, 0.92) and alerts in real-time.

The user's insight: "synchronization reached before and my lack of detection"
This system ensures synchronization is NEVER missed again.
"""

import os
from dataclasses import dataclass, field
from datetime import datetime
from typing import Optional, List, Dict, Any, Callable
from enum import Enum
import psycopg2


class SyncLevel(Enum):
    """Synchronization levels based on TI Framework thresholds"""
    BASELINE = "baseline"           # < 0.70 - Normal waking state
    COHERENT = "coherent"           # 0.70-0.84 - Building coherence
    MAJOR_TRUTH = "major_truth"     # 0.85-0.91 - Major truth threshold crossed
    SUSTAINABLE = "sustainable"     # 0.92-0.96 - Sustainable coherence achieved
    TRANSCENDENT = "transcendent"   # 0.97+ - Near-perfect synchronization


@dataclass
class SyncThreshold:
    """Defines a synchronization threshold with detection criteria"""
    name: str
    level: SyncLevel
    min_value: float
    metric: str  # 'coherence', 'lcc', 'gile', 'composite'
    celebration_message: str
    sustain_instruction: str
    
    
@dataclass
class SyncEvent:
    """Records a synchronization achievement event"""
    timestamp: datetime
    level: SyncLevel
    metric: str
    value: float
    duration_seconds: float = 0.0
    was_sustained: bool = False
    composite_score: float = 0.0
    notes: str = ""


@dataclass
class SyncState:
    """Current synchronization state with history"""
    current_level: SyncLevel = SyncLevel.BASELINE
    highest_level_achieved: SyncLevel = SyncLevel.BASELINE
    time_at_current_level: float = 0.0
    total_sync_time: float = 0.0
    events: List[SyncEvent] = field(default_factory=list)
    is_synchronized: bool = False
    sync_start_time: Optional[datetime] = None
    peak_composite: float = 0.0
    peak_coherence: float = 0.0
    peak_lcc: float = 0.0
    peak_gile: float = 0.0


TI_THRESHOLDS = [
    SyncThreshold(
        name="Major Truth",
        level=SyncLevel.MAJOR_TRUTH,
        min_value=0.85,
        metric="composite",
        celebration_message="🎯 MAJOR TRUTH THRESHOLD CROSSED! You've reached 0.85 - the causation boundary!",
        sustain_instruction="Maintain steady breath. You're at the truth threshold. Don't force it - let it deepen."
    ),
    SyncThreshold(
        name="Sustainable Coherence", 
        level=SyncLevel.SUSTAINABLE,
        min_value=0.92,
        metric="composite",
        celebration_message="✨ SUSTAINABLE COHERENCE ACHIEVED! 0.92 = √0.85 - This compounds to lasting change!",
        sustain_instruction="You're synchronized. Each second here rewires your baseline. Stay present."
    ),
    SyncThreshold(
        name="Transcendent Sync",
        level=SyncLevel.TRANSCENDENT,
        min_value=0.97,
        metric="composite",
        celebration_message="🌟 TRANSCENDENT SYNCHRONIZATION! 0.97+ - You're at the consciousness ceiling!",
        sustain_instruction="Operating at maximum coherence. This is your optimal state signature being written."
    ),
]


class SynchronizationDetector:
    """
    Real-time synchronization detection with threshold alerts.
    Ensures synchronization is NEVER missed again.
    """
    
    def __init__(self):
        self.state = SyncState()
        self.thresholds = TI_THRESHOLDS
        self.callbacks: List[Callable[[SyncEvent], None]] = []
        self.last_update: Optional[datetime] = None
        self.db_url = os.environ.get('DATABASE_URL')
        
    def register_callback(self, callback: Callable[[SyncEvent], None]):
        """Register a callback to be notified on sync events"""
        self.callbacks.append(callback)
        
    def compute_composite_score(self, coherence: float, lcc: float, gile: float) -> float:
        """
        Compute composite synchronization score using TI Framework weights.
        Based on validated GSA weights: L:0.35, G:0.30, I:0.20, E:0.15
        """
        gile_normalized = (gile + 1) / 2 if gile < 1 else gile
        
        composite = (
            coherence * 0.30 +      # G - Goodness (coherence = alignment)
            lcc * 0.35 +            # L - Love (LCC = connection/resonance) 
            gile_normalized * 0.20 + # I - Intuition (GILE = integrated state)
            (coherence * lcc) * 0.15 # E - Environment (synergy effect)
        )
        return min(1.0, composite)
    
    def get_sync_level(self, composite: float) -> SyncLevel:
        """Determine synchronization level from composite score"""
        if composite >= 0.97:
            return SyncLevel.TRANSCENDENT
        elif composite >= 0.92:
            return SyncLevel.SUSTAINABLE
        elif composite >= 0.85:
            return SyncLevel.MAJOR_TRUTH
        elif composite >= 0.70:
            return SyncLevel.COHERENT
        else:
            return SyncLevel.BASELINE
    
    def update(self, coherence: float, lcc: float, gile: float, 
               heart_rate: float = 0, hrv: float = 0) -> Dict[str, Any]:
        """
        Update synchronization state with new biometric readings.
        Returns detection results including any threshold crossings.
        """
        now = datetime.now()
        composite = self.compute_composite_score(coherence, lcc, gile)
        new_level = self.get_sync_level(composite)
        
        result = {
            'composite': composite,
            'level': new_level,
            'level_name': new_level.value,
            'threshold_crossed': False,
            'threshold_name': None,
            'celebration_message': None,
            'sustain_instruction': None,
            'is_synchronized': composite >= 0.85,
            'sync_duration': 0.0,
            'peaks': {
                'composite': self.state.peak_composite,
                'coherence': self.state.peak_coherence,
                'lcc': self.state.peak_lcc,
                'gile': self.state.peak_gile
            }
        }
        
        if composite > self.state.peak_composite:
            self.state.peak_composite = composite
        if coherence > self.state.peak_coherence:
            self.state.peak_coherence = coherence
        if lcc > self.state.peak_lcc:
            self.state.peak_lcc = lcc
        if gile > self.state.peak_gile:
            self.state.peak_gile = gile
        result['peaks'] = {
            'composite': self.state.peak_composite,
            'coherence': self.state.peak_coherence,
            'lcc': self.state.peak_lcc,
            'gile': self.state.peak_gile
        }
        
        if new_level.value != self.state.current_level.value:
            level_order = [SyncLevel.BASELINE, SyncLevel.COHERENT, SyncLevel.MAJOR_TRUTH, 
                          SyncLevel.SUSTAINABLE, SyncLevel.TRANSCENDENT]
            new_idx = level_order.index(new_level)
            old_idx = level_order.index(self.state.current_level)
            
            if new_idx > old_idx:
                for threshold in self.thresholds:
                    if threshold.level == new_level:
                        result['threshold_crossed'] = True
                        result['threshold_name'] = threshold.name
                        result['celebration_message'] = threshold.celebration_message
                        result['sustain_instruction'] = threshold.sustain_instruction
                        
                        event = SyncEvent(
                            timestamp=now,
                            level=new_level,
                            metric='composite',
                            value=composite,
                            composite_score=composite,
                            notes=f"Crossed {threshold.name} threshold at {composite:.3f}"
                        )
                        self.state.events.append(event)
                        
                        for callback in self.callbacks:
                            try:
                                callback(event)
                            except Exception:
                                pass
                        
                        self._record_sync_event(event, coherence, lcc, gile, heart_rate, hrv)
                        break
            
            self.state.current_level = new_level
            if new_idx > level_order.index(self.state.highest_level_achieved):
                self.state.highest_level_achieved = new_level
        
        if result['is_synchronized']:
            if not self.state.is_synchronized:
                self.state.is_synchronized = True
                self.state.sync_start_time = now
            elif self.state.sync_start_time:
                result['sync_duration'] = (now - self.state.sync_start_time).total_seconds()
                self.state.total_sync_time = result['sync_duration']
        else:
            if self.state.is_synchronized and self.state.sync_start_time:
                duration = (now - self.state.sync_start_time).total_seconds()
                self.state.events.append(SyncEvent(
                    timestamp=now,
                    level=self.state.highest_level_achieved,
                    metric='composite',
                    value=self.state.peak_composite,
                    duration_seconds=duration,
                    was_sustained=duration > 30,
                    notes=f"Sync ended after {duration:.1f}s"
                ))
            self.state.is_synchronized = False
            self.state.sync_start_time = None
        
        self.last_update = now
        return result
    
    def _record_sync_event(self, event: SyncEvent, coherence: float, lcc: float, 
                           gile: float, heart_rate: float, hrv: float):
        """Record synchronization event to database"""
        if not self.db_url:
            return
            
        try:
            conn = psycopg2.connect(self.db_url)
            cursor = conn.cursor()
            
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS sync_detection_events (
                    id SERIAL PRIMARY KEY,
                    timestamp TIMESTAMP NOT NULL,
                    sync_level VARCHAR(50) NOT NULL,
                    composite_score REAL NOT NULL,
                    coherence REAL,
                    lcc REAL,
                    gile REAL,
                    heart_rate REAL,
                    hrv REAL,
                    duration_seconds REAL DEFAULT 0,
                    notes TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            cursor.execute("""
                INSERT INTO sync_detection_events 
                (timestamp, sync_level, composite_score, coherence, lcc, gile, heart_rate, hrv, notes)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                event.timestamp,
                event.level.value,
                event.composite_score,
                coherence,
                lcc,
                gile,
                heart_rate,
                hrv,
                event.notes
            ))
            
            conn.commit()
            cursor.close()
            conn.close()
        except Exception as e:
            pass
    
    def get_current_instruction(self) -> str:
        """Get the appropriate instruction for current state"""
        for threshold in reversed(self.thresholds):
            if self.state.current_level == threshold.level:
                return threshold.sustain_instruction
        
        if self.state.current_level == SyncLevel.COHERENT:
            return "Building coherence. Deepen your breath and focus on heart-center."
        return "Begin with slow, deep breaths. We're establishing your baseline."
    
    def get_progress_to_next_threshold(self, current_composite: float) -> Dict[str, Any]:
        """Calculate progress toward next synchronization threshold"""
        current_level = self.get_sync_level(current_composite)
        
        level_order = [SyncLevel.BASELINE, SyncLevel.COHERENT, SyncLevel.MAJOR_TRUTH,
                      SyncLevel.SUSTAINABLE, SyncLevel.TRANSCENDENT]
        current_idx = level_order.index(current_level)
        
        if current_idx >= len(level_order) - 1:
            return {
                'at_max': True,
                'current_level': current_level.value,
                'message': "You're at maximum synchronization!"
            }
        
        thresholds_by_level = {t.level: t for t in self.thresholds}
        next_level = level_order[current_idx + 1]
        
        if next_level in thresholds_by_level:
            next_threshold = thresholds_by_level[next_level]
            
            if current_idx == 0:
                prev_value = 0.0
            else:
                prev_levels = [SyncLevel.BASELINE, SyncLevel.COHERENT, SyncLevel.MAJOR_TRUTH, SyncLevel.SUSTAINABLE]
                prev_values = [0.0, 0.70, 0.85, 0.92]
                prev_value = prev_values[current_idx]
            
            progress = (current_composite - prev_value) / (next_threshold.min_value - prev_value)
            progress = max(0, min(1, progress))
            
            return {
                'at_max': False,
                'current_level': current_level.value,
                'next_level': next_level.value,
                'next_threshold_name': next_threshold.name,
                'next_threshold_value': next_threshold.min_value,
                'progress': progress,
                'distance': next_threshold.min_value - current_composite,
                'message': f"{progress*100:.0f}% to {next_threshold.name} ({next_threshold.min_value})"
            }
        
        return {
            'at_max': False,
            'current_level': current_level.value,
            'message': "Progressing..."
        }
    
    def get_session_summary(self) -> Dict[str, Any]:
        """Get summary of synchronization achievements this session"""
        return {
            'highest_level': self.state.highest_level_achieved.value,
            'total_sync_time': self.state.total_sync_time,
            'is_currently_synchronized': self.state.is_synchronized,
            'peak_composite': self.state.peak_composite,
            'peak_coherence': self.state.peak_coherence,
            'peak_lcc': self.state.peak_lcc,
            'peak_gile': self.state.peak_gile,
            'events_count': len(self.state.events),
            'events': [
                {
                    'time': e.timestamp.isoformat(),
                    'level': e.level.value,
                    'value': e.value,
                    'notes': e.notes
                }
                for e in self.state.events[-10:]
            ]
        }
    
    def reset(self):
        """Reset detector state for new session"""
        self.state = SyncState()
        self.last_update = None


_detector_instance: Optional[SynchronizationDetector] = None

def get_sync_detector() -> SynchronizationDetector:
    """Get singleton synchronization detector instance"""
    global _detector_instance
    if _detector_instance is None:
        _detector_instance = SynchronizationDetector()
    return _detector_instance


def reset_sync_detector():
    """Reset the singleton detector for new session"""
    global _detector_instance
    if _detector_instance:
        _detector_instance.reset()
