"""
Oura Ring Gen 3 — Full API v2 Integration
==========================================
Covers all ~50+ metrics the Gen 3 provides:
  Sleep (stages, HRV, HR, breath, SpO2)
  Readiness (score + 8 contributors)
  Activity (score + 6 contributors, MET, steps)
  Heart Rate  — PPG, 5-min resolution while awake; 30-sec during sleep
  SpO2        — overnight average + breathing disturbance
  Stress      — daytime stress & recovery load
  Resilience  — sleep + daytime composite
  VO2 Max     — aerobic capacity estimate
  Workouts    — type, HR, distance, intensity
  Sessions    — meditation/focus/napping
  Personal Info

Authentication: Personal Access Token
  1. Go to https://cloud.ouraring.com/personal-access-tokens
  2. Create a new token → copy it
  3. Add it as OURA_PERSONAL_ACCESS_TOKEN in Replit Secrets

Author: Brandon Emerick (TI Sigma / BlissGene Therapeutics)
Updated: April 6, 2026
"""

import os
import json
import requests
from datetime import datetime, timedelta, date
from typing import Dict, Any, List, Optional
from dataclasses import dataclass, asdict, field
import statistics


BASE_URL = "https://api.ouraring.com/v2"


# ── Data Models ────────────────────────────────────────────────────────────────

@dataclass
class OuraHeartRatePoint:
    """Single PPG heart rate sample (5-min resolution awake; 30-sec sleep)."""
    timestamp: str
    bpm: int
    source: str  # 'ppg' | 'pedometer' | 'automatic'


@dataclass
class OuraSleepSession:
    """One full sleep session (may be multiple per night: sleep + naps)."""
    id: str
    day: str
    bedtime_start: str
    bedtime_end: str
    type: str                        # 'long_sleep' | 'rest' | 'sleep' | 'late_nap'
    # Durations in seconds
    total_sleep_duration: Optional[int] = None
    time_in_bed: Optional[int] = None
    deep_sleep_duration: Optional[int] = None
    rem_sleep_duration: Optional[int] = None
    light_sleep_duration: Optional[int] = None
    awake_time: Optional[int] = None
    # Quality
    efficiency: Optional[int] = None      # %
    latency: Optional[int] = None         # seconds to fall asleep
    restless_periods: Optional[int] = None
    # Biometrics
    average_hrv: Optional[float] = None   # ms
    lowest_heart_rate: Optional[int] = None
    average_heart_rate: Optional[float] = None
    average_breath: Optional[float] = None  # breaths/min
    # Stage map: list of (phase, duration_sec) in 5-min buckets
    sleep_phase_5_min: Optional[str] = None


@dataclass
class OuraDailyData:
    """All-up daily snapshot combining every endpoint."""
    date: str

    # ── Sleep summary
    sleep_score: Optional[int] = None
    sleep_efficiency: Optional[int] = None
    sleep_latency: Optional[int] = None          # seconds
    deep_sleep_duration: Optional[int] = None    # seconds
    rem_sleep_duration: Optional[int] = None     # seconds
    light_sleep_duration: Optional[int] = None   # seconds
    total_sleep_duration: Optional[int] = None   # seconds
    time_in_bed: Optional[int] = None            # seconds
    awake_time: Optional[int] = None             # seconds
    sleep_hrv: Optional[float] = None            # ms (nightly average)
    sleep_lowest_hr: Optional[int] = None
    sleep_avg_hr: Optional[float] = None
    sleep_avg_breath: Optional[float] = None     # breaths/min
    restless_periods: Optional[int] = None

    # ── Readiness (score + 8 contributors, all 0-100)
    readiness_score: Optional[int] = None
    temperature_deviation: Optional[float] = None  # °C
    temperature_trend_deviation: Optional[float] = None
    hrv_balance: Optional[int] = None
    resting_heart_rate: Optional[int] = None
    recovery_index: Optional[int] = None
    activity_balance: Optional[int] = None
    sleep_balance: Optional[int] = None
    body_temperature: Optional[int] = None
    previous_night: Optional[int] = None
    previous_day_activity: Optional[int] = None

    # ── Activity (score + 6 contributors)
    activity_score: Optional[int] = None
    steps: Optional[int] = None
    active_calories: Optional[int] = None
    total_calories: Optional[int] = None
    equivalent_walking_distance: Optional[int] = None  # meters
    high_activity_time: Optional[int] = None    # seconds
    medium_activity_time: Optional[int] = None  # seconds
    low_activity_time: Optional[int] = None     # seconds
    sedentary_time: Optional[int] = None        # seconds
    rest_time: Optional[int] = None             # seconds
    average_met: Optional[float] = None
    inactivity_alerts: Optional[int] = None
    target_calories: Optional[int] = None
    target_meters: Optional[int] = None
    # Activity contributors
    meet_daily_targets: Optional[int] = None
    move_every_hour: Optional[int] = None
    recovery_time: Optional[int] = None
    stay_active: Optional[int] = None
    training_frequency: Optional[int] = None
    training_volume: Optional[int] = None

    # ── SpO2
    spo2_average: Optional[float] = None          # %
    spo2_breathing_disturbance: Optional[float] = None

    # ── Stress
    stress_high: Optional[int] = None            # minutes of high stress
    recovery_high: Optional[int] = None          # minutes of high recovery
    day_summary: Optional[str] = None            # 'restored' | 'normal' | 'stressful'

    # ── Resilience
    resilience_sleep_recovery: Optional[int] = None
    resilience_daytime_recovery: Optional[int] = None
    resilience_level: Optional[str] = None       # 'poor' | 'adequate' | 'solid' | 'strong' | 'exceptional'

    # ── VO2 Max
    vo2_max: Optional[float] = None

    # ── Computed
    recovery_quality: Optional[float] = None     # 0-1 composite


# ── Main Client ───────────────────────────────────────────────────────────────

class OuraRingIntegration:
    """
    Full Oura Cloud API v2 client for Oura Ring Gen 3.

    Usage:
        oura = OuraRingIntegration()          # reads OURA_PERSONAL_ACCESS_TOKEN
        today = oura.get_today_snapshot()
        hr    = oura.get_recent_heart_rate(hours=6)
    """

    def __init__(self, personal_access_token: Optional[str] = None):
        self.token = personal_access_token or os.getenv('OURA_PERSONAL_ACCESS_TOKEN')
        self.headers = {"Authorization": f"Bearer {self.token}"} if self.token else {}
        self._cache: Dict[str, Any] = {}

    @property
    def is_connected(self) -> bool:
        return bool(self.token)

    def _get(self, path: str, params: Dict = None) -> Any:
        """Raw GET with error handling."""
        if not self.token:
            raise ValueError(
                "Oura token not found. Add OURA_PERSONAL_ACCESS_TOKEN to Replit Secrets.\n"
                "Get your token at: https://cloud.ouraring.com/personal-access-tokens"
            )
        resp = requests.get(f"{BASE_URL}/{path}", headers=self.headers,
                            params=params or {}, timeout=10)
        resp.raise_for_status()
        return resp.json()

    # ── Personal Info ──────────────────────────────────────────────────────────

    def get_personal_info(self) -> Dict[str, Any]:
        """Age, weight, height, biological sex, email."""
        return self._get("usercollection/personal_info")

    # ── Heart Rate (PPG) ───────────────────────────────────────────────────────

    def get_heart_rate(
        self,
        start_datetime: Optional[str] = None,
        end_datetime: Optional[str] = None,
        hours_back: int = 24
    ) -> List[OuraHeartRatePoint]:
        """
        Continuous PPG heart rate — 5-min resolution while awake,
        ~30-sec resolution during sleep.

        Args:
            start_datetime: ISO datetime, defaults to hours_back ago
            end_datetime:   ISO datetime, defaults to now
            hours_back:     convenience shorthand (ignored if start_datetime provided)

        Returns:
            List of OuraHeartRatePoint sorted oldest-first
        """
        if not end_datetime:
            end_dt = datetime.utcnow()
        else:
            end_dt = datetime.fromisoformat(end_datetime.replace('Z', ''))
        if not start_datetime:
            start_dt = end_dt - timedelta(hours=hours_back)
        else:
            start_dt = datetime.fromisoformat(start_datetime.replace('Z', ''))

        data = self._get("usercollection/heartrate", {
            "start_datetime": start_dt.strftime("%Y-%m-%dT%H:%M:%S"),
            "end_datetime":   end_dt.strftime("%Y-%m-%dT%H:%M:%S"),
        })
        return [
            OuraHeartRatePoint(
                timestamp=p["timestamp"],
                bpm=p["bpm"],
                source=p.get("source", "ppg")
            )
            for p in data.get("data", [])
        ]

    def get_latest_heart_rate(self) -> Optional[OuraHeartRatePoint]:
        """Most recent PPG reading (last 2 hours)."""
        points = self.get_heart_rate(hours_back=2)
        return points[-1] if points else None

    # ── Daily Sleep ────────────────────────────────────────────────────────────

    def get_daily_sleep(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        return self._get("usercollection/daily_sleep",
                         {"start_date": start_date, "end_date": end_date}).get("data", [])

    def get_sleep_sessions(self, start_date: str = None, end_date: str = None) -> List[OuraSleepSession]:
        """Individual sleep sessions (more detail than daily_sleep)."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        raw = self._get("usercollection/sleep",
                        {"start_date": start_date, "end_date": end_date}).get("data", [])
        sessions = []
        for s in raw:
            sessions.append(OuraSleepSession(
                id=s.get("id", ""),
                day=s.get("day", ""),
                bedtime_start=s.get("bedtime_start", ""),
                bedtime_end=s.get("bedtime_end", ""),
                type=s.get("type", "sleep"),
                total_sleep_duration=s.get("total_sleep_duration"),
                time_in_bed=s.get("time_in_bed"),
                deep_sleep_duration=s.get("deep_sleep_duration"),
                rem_sleep_duration=s.get("rem_sleep_duration"),
                light_sleep_duration=s.get("light_sleep_duration"),
                awake_time=s.get("awake_time"),
                efficiency=s.get("efficiency"),
                latency=s.get("latency"),
                restless_periods=s.get("restless_periods"),
                average_hrv=s.get("average_hrv"),
                lowest_heart_rate=s.get("lowest_heart_rate"),
                average_heart_rate=s.get("average_heart_rate"),
                average_breath=s.get("average_breath"),
                sleep_phase_5_min=str(s.get("sleep_phase_5_min", "")),
            ))
        return sessions

    # ── Readiness ──────────────────────────────────────────────────────────────

    def get_daily_readiness(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        return self._get("usercollection/daily_readiness",
                         {"start_date": start_date, "end_date": end_date}).get("data", [])

    # ── Activity ───────────────────────────────────────────────────────────────

    def get_daily_activity(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        return self._get("usercollection/daily_activity",
                         {"start_date": start_date, "end_date": end_date}).get("data", [])

    # ── SpO2 ───────────────────────────────────────────────────────────────────

    def get_daily_spo2(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Overnight SpO2 average + breathing disturbance index."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        try:
            return self._get("usercollection/daily_spo2",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── Stress ─────────────────────────────────────────────────────────────────

    def get_daily_stress(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Daytime stress & recovery minutes + day summary label."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        try:
            return self._get("usercollection/daily_stress",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── Resilience ─────────────────────────────────────────────────────────────

    def get_daily_resilience(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Sleep recovery + daytime recovery + resilience level label."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        try:
            return self._get("usercollection/daily_resilience",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── VO2 Max ────────────────────────────────────────────────────────────────

    def get_vo2_max(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Aerobic capacity estimate from daily ring data."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=30)).isoformat()
        try:
            return self._get("usercollection/vo2_max",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── Workouts ───────────────────────────────────────────────────────────────

    def get_workouts(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Detected workout sessions with HR, calories, distance."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        try:
            return self._get("usercollection/workout",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── Sessions (meditation / focus / nap) ───────────────────────────────────

    def get_sessions(self, start_date: str = None, end_date: str = None) -> List[Dict]:
        """Guided sessions (meditation, focus, etc.) tracked in the app."""
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()
        try:
            return self._get("usercollection/session",
                             {"start_date": start_date, "end_date": end_date}).get("data", [])
        except Exception:
            return []

    # ── Combined Daily Snapshot ────────────────────────────────────────────────

    def get_combined_daily_data(
        self, start_date: str = None, end_date: str = None
    ) -> List[OuraDailyData]:
        """
        Merge all endpoints into one OuraDailyData per day.
        Covers all ~50+ Gen 3 metrics.
        """
        end_date = end_date or date.today().isoformat()
        start_date = start_date or (date.today() - timedelta(days=7)).isoformat()

        sleep_map     = {d["day"]: d for d in self.get_daily_sleep(start_date, end_date)}
        readiness_map = {d["day"]: d for d in self.get_daily_readiness(start_date, end_date)}
        activity_map  = {d["day"]: d for d in self.get_daily_activity(start_date, end_date)}
        spo2_map      = {d["day"]: d for d in self.get_daily_spo2(start_date, end_date)}
        stress_map    = {d["day"]: d for d in self.get_daily_stress(start_date, end_date)}
        resil_map     = {d["day"]: d for d in self.get_daily_resilience(start_date, end_date)}
        vo2_map       = {d["day"]: d for d in self.get_vo2_max(start_date, end_date)}

        all_days = sorted(set(
            list(sleep_map) + list(readiness_map) + list(activity_map)
        ))

        result = []
        for day in all_days:
            s  = sleep_map.get(day, {})
            r  = readiness_map.get(day, {})
            a  = activity_map.get(day, {})
            sp = spo2_map.get(day, {})
            st = stress_map.get(day, {})
            re = resil_map.get(day, {})
            vo = vo2_map.get(day, {})

            rc  = r.get("contributors", {})
            ac  = a.get("contributors", {})
            sp2 = sp.get("spo2_percentage", {})

            daily = OuraDailyData(
                date=day,
                # Sleep
                sleep_score=s.get("score"),
                sleep_efficiency=s.get("efficiency"),
                sleep_latency=s.get("latency"),
                deep_sleep_duration=s.get("deep_sleep_duration"),
                rem_sleep_duration=s.get("rem_sleep_duration"),
                light_sleep_duration=s.get("light_sleep_duration"),
                total_sleep_duration=s.get("total_sleep_duration"),
                time_in_bed=s.get("time_in_bed"),
                awake_time=s.get("awake_time"),
                sleep_hrv=s.get("average_hrv"),
                sleep_lowest_hr=s.get("lowest_heart_rate"),
                sleep_avg_hr=s.get("average_heart_rate"),
                sleep_avg_breath=s.get("average_breath"),
                restless_periods=s.get("restless_periods"),
                # Readiness
                readiness_score=r.get("score"),
                temperature_deviation=r.get("temperature_deviation"),
                temperature_trend_deviation=r.get("temperature_trend_deviation"),
                hrv_balance=rc.get("hrv_balance"),
                resting_heart_rate=rc.get("resting_heart_rate"),
                recovery_index=rc.get("recovery_index"),
                activity_balance=rc.get("activity_balance"),
                sleep_balance=rc.get("sleep_balance"),
                body_temperature=rc.get("body_temperature"),
                previous_night=rc.get("previous_night"),
                previous_day_activity=rc.get("previous_day_activity"),
                # Activity
                activity_score=a.get("score"),
                steps=a.get("steps"),
                active_calories=a.get("active_calories"),
                total_calories=a.get("total_calories"),
                equivalent_walking_distance=a.get("equivalent_walking_distance"),
                high_activity_time=a.get("high_activity_time"),
                medium_activity_time=a.get("medium_activity_time"),
                low_activity_time=a.get("low_activity_time"),
                sedentary_time=a.get("sedentary_time"),
                rest_time=a.get("rest_time"),
                average_met=a.get("average_met_minutes"),
                inactivity_alerts=a.get("inactivity_alerts"),
                target_calories=a.get("target_calories"),
                target_meters=a.get("target_meters"),
                meet_daily_targets=ac.get("meet_daily_targets"),
                move_every_hour=ac.get("move_every_hour"),
                recovery_time=ac.get("recovery_time"),
                stay_active=ac.get("stay_active"),
                training_frequency=ac.get("training_frequency"),
                training_volume=ac.get("training_volume"),
                # SpO2
                spo2_average=sp2.get("average"),
                spo2_breathing_disturbance=sp.get("breathing_disturbance_index"),
                # Stress
                stress_high=st.get("stress_high"),
                recovery_high=st.get("recovery_high"),
                day_summary=st.get("day_summary"),
                # Resilience
                resilience_sleep_recovery=re.get("sleep_recovery"),
                resilience_daytime_recovery=re.get("daytime_recovery"),
                resilience_level=re.get("level"),
                # VO2 Max
                vo2_max=vo.get("vo2_max"),
            )
            daily.recovery_quality = self.calculate_recovery_quality(daily)
            result.append(daily)

        return result

    def get_today_snapshot(self) -> OuraDailyData:
        """
        Pull all today's metrics in one call.
        Returns the most recent OuraDailyData (today or yesterday if today hasn't synced).
        """
        today = date.today().isoformat()
        yesterday = (date.today() - timedelta(days=1)).isoformat()
        data = self.get_combined_daily_data(start_date=yesterday, end_date=today)
        if data:
            return data[-1]
        return OuraDailyData(date=today)

    # ── Scoring Helpers ────────────────────────────────────────────────────────

    def calculate_recovery_quality(self, d: OuraDailyData) -> float:
        """
        Composite recovery quality 0.0–1.0.
        Weights: readiness 40%, sleep 35%, HRV balance 25%.
        """
        parts = []
        if d.readiness_score is not None:
            parts.append((d.readiness_score / 100.0, 0.40))
        if d.sleep_score is not None:
            parts.append((d.sleep_score / 100.0, 0.35))
        if d.hrv_balance is not None:
            parts.append((d.hrv_balance / 100.0, 0.25))
        if not parts:
            return 0.0
        total_w = sum(w for _, w in parts)
        return sum(v * w for v, w in parts) / total_w

    def oura_gile_score(self, d: OuraDailyData) -> float:
        """
        Map Oura data → GILE score (-2.5 to +2.5).
        GILE = 5(sigma - 0.5) where sigma = recovery_quality.
        """
        q = d.recovery_quality if d.recovery_quality is not None else 0.5
        return round(5.0 * (q - 0.5), 3)

    def seconds_to_hm(self, secs: Optional[int]) -> str:
        if secs is None:
            return "—"
        h, m = divmod(secs // 60, 60)
        return f"{h}h {m:02d}m"

    def score_color(self, score: Optional[int]) -> str:
        if score is None:
            return "#888"
        if score >= 85:
            return "#00cc44"
        if score >= 70:
            return "#88dd00"
        if score >= 55:
            return "#ffcc00"
        return "#ff4444"

    def get_optimal_windows(self, days: int = 30) -> List[Dict]:
        """Days with recovery_quality >= 0.70 — optimal for PSI / high-stakes decisions."""
        end_date = date.today().isoformat()
        start_date = (date.today() - timedelta(days=days)).isoformat()
        data = self.get_combined_daily_data(start_date, end_date)
        return sorted(
            [
                {
                    "date": d.date,
                    "recovery_quality": d.recovery_quality,
                    "readiness_score": d.readiness_score,
                    "sleep_score": d.sleep_score,
                    "gile_score": self.oura_gile_score(d),
                    "recommendation": "EXCELLENT — high PSI window",
                }
                for d in data
                if d.recovery_quality and d.recovery_quality >= 0.70
            ],
            key=lambda x: x["recovery_quality"],
            reverse=True,
        )

    def save_data(self, filename: str = "oura_data.json"):
        end_date = date.today().isoformat()
        start_date = (date.today() - timedelta(days=30)).isoformat()
        data = [asdict(d) for d in self.get_combined_daily_data(start_date, end_date)]
        with open(filename, "w") as f:
            json.dump(data, f, indent=2, default=str)
        return filename
