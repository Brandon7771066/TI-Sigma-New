"""
Automated Animal Synchrony Study System

This system enables large-scale monitoring of animal behavior across
multiple zoo webcams, correlating with GCP readings to test LCC predictions.

Features:
- Multi-webcam capture (parallel processing with scheduled snapshots)
- Behavior annotation interface
- Automated GCP data ingestion
- Synchrony scoring with proper time-window alignment
- SQLite database for scalable storage
"""

import os
import json
import time
import sqlite3
import threading
import requests
from datetime import datetime, timedelta
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed
import re

# Database and storage paths
STUDY_DB_PATH = Path("experiments/study_data")
STUDY_DB_PATH.mkdir(parents=True, exist_ok=True)
DB_FILE = STUDY_DB_PATH / "animal_study.db"


@dataclass
class WebcamSource:
    """Definition of a webcam source"""
    name: str
    species: str
    location: str
    url: str
    timezone: str
    estimated_r: float
    active: bool = True
    notes: str = ""
    latitude: float = 0.0
    longitude: float = 0.0


@dataclass
class BehaviorObservation:
    """Single behavior observation"""
    id: Optional[int] = None
    timestamp_utc: str = ""
    webcam_name: str = ""
    species: str = ""
    location: str = ""
    behavior_code: str = ""
    activity_level: int = 0
    mood_score: int = 0
    gcp_z_score: Optional[float] = None
    notes: str = ""
    observer: str = "automated"
    session_id: str = ""


@dataclass
class SynchronyScore:
    """Synchrony calculation between two webcams"""
    timestamp: str
    webcam_a: str
    webcam_b: str
    species_a: str
    species_b: str
    behavior_match: bool
    category_match: bool
    activity_diff: int
    mood_diff: int
    synchrony_score: float
    distance_km: float
    time_diff_seconds: float


class Database:
    """SQLite database for scalable storage"""
    
    def __init__(self, db_path: Path = DB_FILE):
        self.db_path = db_path
        self._init_db()
    
    def _init_db(self):
        """Initialize database schema"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS webcams (
                    name TEXT PRIMARY KEY,
                    species TEXT,
                    location TEXT,
                    url TEXT,
                    timezone TEXT,
                    estimated_r REAL,
                    active INTEGER DEFAULT 1,
                    notes TEXT,
                    latitude REAL DEFAULT 0,
                    longitude REAL DEFAULT 0
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS observations (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp_utc TEXT NOT NULL,
                    webcam_name TEXT NOT NULL,
                    species TEXT,
                    location TEXT,
                    behavior_code TEXT,
                    activity_level INTEGER,
                    mood_score INTEGER,
                    gcp_z_score REAL,
                    notes TEXT,
                    observer TEXT,
                    session_id TEXT,
                    FOREIGN KEY (webcam_name) REFERENCES webcams(name)
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS gcp_readings (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp_utc TEXT NOT NULL,
                    z_score REAL,
                    variance REAL,
                    is_significant INTEGER,
                    source TEXT
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS sessions (
                    id TEXT PRIMARY KEY,
                    name TEXT,
                    start_time TEXT,
                    end_time TEXT,
                    webcams TEXT,
                    notes TEXT
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS synchrony_scores (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp TEXT,
                    webcam_a TEXT,
                    webcam_b TEXT,
                    synchrony_score REAL,
                    distance_km REAL,
                    gcp_z_score REAL,
                    session_id TEXT
                )
            """)
            
            # Create indexes for efficient queries
            conn.execute("CREATE INDEX IF NOT EXISTS idx_obs_timestamp ON observations(timestamp_utc)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_obs_session ON observations(session_id)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_gcp_timestamp ON gcp_readings(timestamp_utc)")
            
            conn.commit()
    
    def add_observation(self, obs: BehaviorObservation) -> int:
        """Add observation and return ID"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("""
                INSERT INTO observations 
                (timestamp_utc, webcam_name, species, location, behavior_code,
                 activity_level, mood_score, gcp_z_score, notes, observer, session_id)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (obs.timestamp_utc, obs.webcam_name, obs.species, obs.location,
                  obs.behavior_code, obs.activity_level, obs.mood_score,
                  obs.gcp_z_score, obs.notes, obs.observer, obs.session_id))
            return cursor.lastrowid or 0
    
    def add_gcp_reading(self, timestamp: str, z_score: float, 
                        variance: float = 1.0, source: str = "manual"):
        """Add GCP reading"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO gcp_readings (timestamp_utc, z_score, variance, is_significant, source)
                VALUES (?, ?, ?, ?, ?)
            """, (timestamp, z_score, variance, 1 if abs(z_score) >= 2 else 0, source))
    
    def get_observations_in_window(self, center_time: datetime, 
                                    window_seconds: float = 30) -> List[BehaviorObservation]:
        """Get observations within time window"""
        start = (center_time - timedelta(seconds=window_seconds)).isoformat()
        end = (center_time + timedelta(seconds=window_seconds)).isoformat()
        
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            rows = conn.execute("""
                SELECT * FROM observations
                WHERE timestamp_utc >= ? AND timestamp_utc <= ?
                ORDER BY timestamp_utc
            """, (start, end)).fetchall()
            
            return [BehaviorObservation(**dict(row)) for row in rows]
    
    def get_gcp_reading_at(self, timestamp: datetime, 
                           tolerance_seconds: float = 60) -> Optional[float]:
        """Get nearest GCP reading to timestamp"""
        start = (timestamp - timedelta(seconds=tolerance_seconds)).isoformat()
        end = (timestamp + timedelta(seconds=tolerance_seconds)).isoformat()
        
        with sqlite3.connect(self.db_path) as conn:
            row = conn.execute("""
                SELECT z_score FROM gcp_readings
                WHERE timestamp_utc >= ? AND timestamp_utc <= ?
                ORDER BY ABS(julianday(timestamp_utc) - julianday(?))
                LIMIT 1
            """, (start, end, timestamp.isoformat())).fetchone()
            
            return row[0] if row else None
    
    def get_observation_count(self) -> int:
        """Get total observation count"""
        with sqlite3.connect(self.db_path) as conn:
            return conn.execute("SELECT COUNT(*) FROM observations").fetchone()[0]
    
    def get_all_observations(self, limit: int = 10000) -> List[BehaviorObservation]:
        """Get all observations"""
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            rows = conn.execute(
                "SELECT * FROM observations ORDER BY timestamp_utc DESC LIMIT ?",
                (limit,)
            ).fetchall()
            return [BehaviorObservation(**dict(row)) for row in rows]


class WebcamRegistry:
    """Registry of available zoo webcams with database persistence"""
    
    def __init__(self, db: Database):
        self.db = db
        self.webcams: Dict[str, WebcamSource] = {}
        self._load_defaults()
    
    def _load_defaults(self):
        """Load default webcams"""
        defaults = [
            WebcamSource(
                name="smithsonian_lions",
                species="lion",
                location="Washington DC",
                url="https://nationalzoo.si.edu/webcams/lion-cam",
                timezone="America/New_York",
                estimated_r=4.5,
                latitude=38.93, longitude=-77.05
            ),
            WebcamSource(
                name="sandiego_tigers",
                species="tiger",
                location="San Diego",
                url="https://zoo.sandiegozoo.org/live-cameras",
                timezone="America/Los_Angeles",
                estimated_r=4.5,
                latitude=32.73, longitude=-117.15
            ),
            WebcamSource(
                name="smithsonian_pandas",
                species="panda",
                location="Washington DC",
                url="https://nationalzoo.si.edu/webcams/panda-cam",
                timezone="America/New_York",
                estimated_r=4.0,
                latitude=38.93, longitude=-77.05
            ),
            WebcamSource(
                name="houston_gorillas",
                species="gorilla",
                location="Houston",
                url="https://www.houstonzoo.org/explore/webcams/",
                timezone="America/Chicago",
                estimated_r=6.5,
                latitude=29.71, longitude=-95.39
            ),
            WebcamSource(
                name="mpala_wildlife",
                species="mixed_african",
                location="Kenya",
                url="https://explore.org/livecams/african-wildlife/african-animal-camera",
                timezone="Africa/Nairobi",
                estimated_r=4.0,
                latitude=-0.29, longitude=36.90
            ),
            WebcamSource(
                name="katmai_bears",
                species="brown_bear",
                location="Alaska",
                url="https://explore.org/livecams/brown-bears/brown-bear-salmon-cam-brooks-falls",
                timezone="America/Anchorage",
                estimated_r=4.0,
                latitude=58.55, longitude=-155.78
            ),
            WebcamSource(
                name="monterey_kelp",
                species="mixed_marine",
                location="Monterey",
                url="https://www.montereybayaquarium.org/animals/live-cams/kelp-forest-cam",
                timezone="America/Los_Angeles",
                estimated_r=3.0,
                latitude=36.62, longitude=-121.90
            ),
            WebcamSource(
                name="decorah_eagles",
                species="bald_eagle",
                location="Iowa",
                url="https://explore.org/livecams/bald-eagles/decorah-eagles",
                timezone="America/Chicago",
                estimated_r=3.5,
                latitude=43.30, longitude=-91.78
            ),
        ]
        
        for webcam in defaults:
            self.webcams[webcam.name] = webcam
            self._save_webcam(webcam)
    
    def _save_webcam(self, webcam: WebcamSource):
        """Save webcam to database"""
        with sqlite3.connect(self.db.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO webcams 
                (name, species, location, url, timezone, estimated_r, active, notes, latitude, longitude)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (webcam.name, webcam.species, webcam.location, webcam.url,
                  webcam.timezone, webcam.estimated_r, 1 if webcam.active else 0,
                  webcam.notes, webcam.latitude, webcam.longitude))
    
    def get_active_webcams(self) -> List[WebcamSource]:
        """Return all active webcams"""
        return [w for w in self.webcams.values() if w.active]
    
    def calculate_distance(self, loc_a: str, loc_b: str) -> float:
        """Calculate distance between two locations using Haversine formula"""
        import math
        
        cam_a = next((w for w in self.webcams.values() if w.location == loc_a), None)
        cam_b = next((w for w in self.webcams.values() if w.location == loc_b), None)
        
        if not cam_a or not cam_b:
            return 0.0
        
        R = 6371  # Earth's radius in km
        lat1, lon1 = math.radians(cam_a.latitude), math.radians(cam_a.longitude)
        lat2, lon2 = math.radians(cam_b.latitude), math.radians(cam_b.longitude)
        
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        
        a = math.sin(dlat/2)**2 + math.cos(lat1) * math.cos(lat2) * math.sin(dlon/2)**2
        c = 2 * math.asin(math.sqrt(a))
        
        return R * c


class GCPMonitor:
    """Monitor GCP readings with database persistence"""
    
    def __init__(self, db: Database):
        self.db = db
        self.current_z = 0.0
        self.significant_threshold = 2.0
        self.lock = threading.Lock()
    
    def update_reading(self, z_score: float, source: str = "manual"):
        """Update and persist GCP reading"""
        with self.lock:
            self.current_z = z_score
            timestamp = datetime.utcnow().isoformat()
            self.db.add_gcp_reading(timestamp, z_score, source=source)
    
    def get_current_reading(self) -> dict:
        """Get current GCP state"""
        return {
            "timestamp_utc": datetime.utcnow().isoformat(),
            "z_score": self.current_z,
            "is_significant": abs(self.current_z) >= self.significant_threshold
        }
    
    def is_significant_event(self) -> bool:
        """Check if current reading is significant"""
        return abs(self.current_z) >= self.significant_threshold


class SynchronyCalculator:
    """Calculate synchrony with proper time-window alignment"""
    
    ACTIVE_BEHAVIORS = {'W', 'So', 'V', 'P', 'A'}
    INACTIVE_BEHAVIORS = {'S', 'R', 'E'}
    
    def __init__(self, db: Database, registry: WebcamRegistry):
        self.db = db
        self.registry = registry
        self.time_window_seconds = 30  # Configurable alignment window
    
    def calculate_pair_synchrony(self, obs_a: BehaviorObservation, 
                                  obs_b: BehaviorObservation) -> SynchronyScore:
        """Calculate synchrony between two observations with time alignment"""
        
        # Parse timestamps
        time_a = datetime.fromisoformat(obs_a.timestamp_utc.replace('Z', '+00:00').replace('+00:00', ''))
        time_b = datetime.fromisoformat(obs_b.timestamp_utc.replace('Z', '+00:00').replace('+00:00', ''))
        time_diff = abs((time_a - time_b).total_seconds())
        
        # Behavior matching
        behavior_match = obs_a.behavior_code == obs_b.behavior_code
        
        category_match = (
            (obs_a.behavior_code in self.ACTIVE_BEHAVIORS and 
             obs_b.behavior_code in self.ACTIVE_BEHAVIORS) or
            (obs_a.behavior_code in self.INACTIVE_BEHAVIORS and 
             obs_b.behavior_code in self.INACTIVE_BEHAVIORS)
        )
        
        activity_diff = abs(obs_a.activity_level - obs_b.activity_level)
        mood_diff = abs(obs_a.mood_score - obs_b.mood_score)
        
        # Calculate synchrony score (0-1)
        # Weight decreases with time difference
        time_weight = max(0, 1 - (time_diff / self.time_window_seconds))
        
        score = 0.0
        if behavior_match:
            score += 0.5 * time_weight
        elif category_match:
            score += 0.25 * time_weight
        
        score += max(0, 0.25 - (activity_diff * 0.05)) * time_weight
        score += max(0, 0.25 - (mood_diff * 0.05)) * time_weight
        
        # Get distance
        distance = self.registry.calculate_distance(obs_a.location, obs_b.location)
        
        return SynchronyScore(
            timestamp=obs_a.timestamp_utc,
            webcam_a=obs_a.webcam_name,
            webcam_b=obs_b.webcam_name,
            species_a=obs_a.species,
            species_b=obs_b.species,
            behavior_match=behavior_match,
            category_match=category_match,
            activity_diff=activity_diff,
            mood_diff=mood_diff,
            synchrony_score=score,
            distance_km=distance,
            time_diff_seconds=time_diff
        )
    
    def calculate_baseline_chance(self, observations: List[BehaviorObservation]) -> float:
        """Calculate expected synchrony by chance based on behavior distribution"""
        if not observations:
            return 0.33  # Default if no data
        
        # Count behavior frequencies
        behavior_counts: Dict[str, int] = {}
        for obs in observations:
            behavior_counts[obs.behavior_code] = behavior_counts.get(obs.behavior_code, 0) + 1
        
        total = len(observations)
        
        # Probability of exact match by chance
        exact_match_prob = sum((count/total)**2 for count in behavior_counts.values())
        
        # Probability of category match
        active_prob = sum(behavior_counts.get(b, 0)/total for b in self.ACTIVE_BEHAVIORS)
        inactive_prob = sum(behavior_counts.get(b, 0)/total for b in self.INACTIVE_BEHAVIORS)
        category_match_prob = active_prob**2 + inactive_prob**2
        
        # Expected synchrony score by chance
        baseline = exact_match_prob * 0.5 + (category_match_prob - exact_match_prob) * 0.25 + 0.25
        
        return baseline
    
    def calculate_all_pairs_in_window(self, center_time: datetime) -> List[SynchronyScore]:
        """Calculate synchrony for all pairs within time window"""
        observations = self.db.get_observations_in_window(
            center_time, self.time_window_seconds
        )
        
        if len(observations) < 2:
            return []
        
        scores = []
        for i in range(len(observations)):
            for j in range(i + 1, len(observations)):
                # Only compare different webcams
                if observations[i].webcam_name != observations[j].webcam_name:
                    score = self.calculate_pair_synchrony(observations[i], observations[j])
                    scores.append(score)
        
        return scores


class ExperimentSession:
    """Manage experiment session with database persistence"""
    
    def __init__(self, name: str, webcam_names: List[str], db: Optional[Database] = None):
        self.db = db or Database()
        self.registry = WebcamRegistry(self.db)
        self.gcp_monitor = GCPMonitor(self.db)
        self.synchrony_calc = SynchronyCalculator(self.db, self.registry)
        
        self.name = name
        self.session_id = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        self.webcam_names = webcam_names
        self.start_time: Optional[datetime] = None
        self.end_time: Optional[datetime] = None
        self.is_running = False
    
    def start(self):
        """Start experiment session"""
        self.start_time = datetime.utcnow()
        self.is_running = True
        
        # Save session to database
        with sqlite3.connect(self.db.db_path) as conn:
            conn.execute("""
                INSERT INTO sessions (id, name, start_time, webcams)
                VALUES (?, ?, ?, ?)
            """, (self.session_id, self.name, self.start_time.isoformat(),
                  json.dumps(self.webcam_names)))
        
        print(f"\n{'='*60}")
        print(f"EXPERIMENT SESSION STARTED: {self.name}")
        print(f"Session ID: {self.session_id}")
        print(f"Start time: {self.start_time.isoformat()}")
        print(f"Webcams: {', '.join(self.webcam_names)}")
        print(f"{'='*60}\n")
    
    def stop(self):
        """Stop experiment session"""
        self.end_time = datetime.utcnow()
        self.is_running = False
        
        # Update session in database
        with sqlite3.connect(self.db.db_path) as conn:
            conn.execute("""
                UPDATE sessions SET end_time = ? WHERE id = ?
            """, (self.end_time.isoformat(), self.session_id))
        
        duration = self.end_time - self.start_time if self.start_time else timedelta(0)
        obs_count = self.db.get_observation_count()
        
        print(f"\n{'='*60}")
        print(f"EXPERIMENT SESSION ENDED")
        print(f"Duration: {duration}")
        print(f"Total observations in database: {obs_count}")
        print(f"{'='*60}\n")
    
    def record_observation(self, webcam_name: str, behavior_code: str,
                          activity_level: int, mood_score: int, 
                          notes: str = "", observer: str = "manual"):
        """Record behavior observation"""
        webcam = self.registry.webcams.get(webcam_name)
        if not webcam:
            print(f"Warning: Unknown webcam {webcam_name}")
            return
        
        gcp = self.gcp_monitor.get_current_reading()
        
        obs = BehaviorObservation(
            timestamp_utc=datetime.utcnow().isoformat(),
            webcam_name=webcam_name,
            species=webcam.species,
            location=webcam.location,
            behavior_code=behavior_code,
            activity_level=activity_level,
            mood_score=mood_score,
            gcp_z_score=gcp['z_score'],
            notes=notes,
            observer=observer,
            session_id=self.session_id
        )
        
        obs_id = self.db.add_observation(obs)
        
        print(f"[{obs.timestamp_utc}] #{obs_id} {webcam_name}: {behavior_code} "
              f"(activity={activity_level}, mood={mood_score}, GCP={gcp['z_score']:.2f})")
    
    def get_current_synchrony(self) -> Dict:
        """Calculate current synchrony"""
        now = datetime.utcnow()
        scores = self.synchrony_calc.calculate_all_pairs_in_window(now)
        
        if not scores:
            return {"error": "Not enough paired observations"}
        
        avg_sync = sum(s.synchrony_score for s in scores) / len(scores)
        baseline = self.synchrony_calc.calculate_baseline_chance(
            self.db.get_all_observations(limit=1000)
        )
        
        return {
            "timestamp": now.isoformat(),
            "n_pairs": len(scores),
            "average_synchrony": avg_sync,
            "baseline_chance": baseline,
            "above_chance": avg_sync > baseline,
            "deviation": avg_sync - baseline,
            "max_synchrony": max(s.synchrony_score for s in scores),
            "min_synchrony": min(s.synchrony_score for s in scores),
            "gcp_z_score": self.gcp_monitor.current_z
        }
    
    def get_summary(self) -> Dict:
        """Get session summary"""
        with sqlite3.connect(self.db.db_path) as conn:
            obs_count = conn.execute(
                "SELECT COUNT(*) FROM observations WHERE session_id = ?",
                (self.session_id,)
            ).fetchone()[0]
            
            species = conn.execute(
                "SELECT DISTINCT species FROM observations WHERE session_id = ?",
                (self.session_id,)
            ).fetchall()
            
            webcams = conn.execute(
                "SELECT DISTINCT webcam_name FROM observations WHERE session_id = ?",
                (self.session_id,)
            ).fetchall()
        
        return {
            "session_id": self.session_id,
            "name": self.name,
            "start_time": self.start_time.isoformat() if self.start_time else None,
            "end_time": self.end_time.isoformat() if self.end_time else None,
            "observations": obs_count,
            "species": [s[0] for s in species],
            "webcams": [w[0] for w in webcams]
        }


def demo_experiment():
    """Demonstrate the experiment system"""
    print("\n" + "="*70)
    print("AUTOMATED ANIMAL SYNCHRONY STUDY SYSTEM")
    print("Using SQLite database for scalable storage")
    print("="*70)
    
    db = Database()
    registry = WebcamRegistry(db)
    
    print("\n--- Available Webcams ---")
    for name, webcam in registry.webcams.items():
        print(f"  [{name}] {webcam.species} @ {webcam.location} (R≈{webcam.estimated_r})")
    
    webcams = ["smithsonian_lions", "mpala_wildlife", "katmai_bears"]
    session = ExperimentSession("Demo Study", webcams, db)
    session.start()
    
    print("\n--- Recording Observations ---")
    behaviors = [
        ("smithsonian_lions", "R", 1, 1, "Lion resting"),
        ("mpala_wildlife", "W", 3, 2, "Zebras walking"),
        ("katmai_bears", "E", 2, 2, "Bear fishing"),
    ]
    
    for webcam, behavior, activity, mood, note in behaviors:
        session.record_observation(webcam, behavior, activity, mood, note)
        time.sleep(0.3)
    
    print("\n--- Synchrony Analysis ---")
    sync = session.get_current_synchrony()
    for key, value in sync.items():
        if isinstance(value, float):
            print(f"  {key}: {value:.4f}")
        else:
            print(f"  {key}: {value}")
    
    session.stop()
    
    print(f"\n--- Database Stats ---")
    print(f"  Total observations: {db.get_observation_count()}")
    print(f"  Database location: {DB_FILE}")
    
    print("\n" + "="*70)
    print("System ready for full experiment!")
    print("="*70)


if __name__ == "__main__":
    demo_experiment()
