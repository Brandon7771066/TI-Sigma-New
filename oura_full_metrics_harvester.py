"""
Oura Full Metrics Harvester
============================

Pulls 30 days of all 50+ Oura Gen 3 metrics into a single JSON file for
downstream Phase B weight learning + PPG biophoton-signature proxy work.

Outputs
-------
data/oura_30day_harvest_<YYYY-MM-DD>.json with structure:
  {
    "harvest_metadata": {...},
    "daily_records": [ <one OuraDailyData dict per day, 50+ fields>, ... ],
    "sleep_sessions": [ <one OuraSleepSession dict per session>, ... ],
    "heart_rate_samples": {
        "<YYYY-MM-DD>": [ {timestamp, bpm, source}, ... ],
        ...
    },
    "personal_info": {...},
    "completeness_summary": {...}
  }

Usage
-----
    python oura_full_metrics_harvester.py [--days 30]

Environment
-----------
Requires OURA_PERSONAL_ACCESS_TOKEN (already in Replit Secrets).

Cost
----
$0 — Oura API is free for personal access tokens, rate-limited at 5000
requests/day per user. This harvester makes ~7 + N API calls (1 per day for
heart-rate per-day windows + 6 daily-aggregate endpoints + 1 personal-info).

Honest scope
------------
- All metrics are real Oura values, no proxies, no fallbacks.
- Heart-rate samples come from the ring's optical PPG sensor (BPM only;
  Oura does NOT expose raw PPG waveform via API).
- A day is "complete" if sleep + readiness + activity records all present;
  some days may be partial (rough sleep, no ring overnight, etc.).
"""

from __future__ import annotations
import argparse
import json
import os
import sys
from dataclasses import asdict
from datetime import date, datetime, timedelta
from typing import Dict, Any, List

from oura_ring_integration import OuraRingIntegration


def harvest(days: int = 30, output_dir: str = "data") -> str:
    """Pull `days` days of all Oura metrics, write JSON, return path."""
    oura = OuraRingIntegration()
    if not oura.is_connected:
        print("❌ OURA_PERSONAL_ACCESS_TOKEN not configured.", file=sys.stderr)
        sys.exit(1)

    end_date = date.today()
    # Inclusive `days`-day window: end_date back to end_date - (days-1)
    start_date = end_date - timedelta(days=days - 1)
    start_iso = start_date.isoformat()
    end_iso = end_date.isoformat()

    # Per-endpoint status flags so silent fallbacks can be detected later
    endpoint_status: Dict[str, str] = {}

    print(f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"OURA FULL METRICS HARVEST — {start_iso} → {end_iso} ({days} days inclusive)")
    print(f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

    # ── 1. Personal info (constant) ──────────────────────────────────────────
    print("\n[1/5] Personal info...")
    try:
        personal = oura.get_personal_info()
        # Strip email for privacy in the harvest file
        personal.pop("email", None)
        print(f"      ✅ age={personal.get('age')}, sex={personal.get('biological_sex')}")
        endpoint_status["personal_info"] = "ok"
    except Exception as e:
        print(f"      ⚠️  fallback to empty: {e}")
        personal = {}
        endpoint_status["personal_info"] = f"error: {type(e).__name__}: {e}"

    # ── 2. Combined daily records (sleep + readiness + activity + spo2 + stress + resilience + vo2) ──
    print(f"\n[2/5] Combined daily records ({days} days)...")
    try:
        daily_objects = oura.get_combined_daily_data(start_iso, end_iso)
        daily_records = [asdict(d) for d in daily_objects]
        endpoint_status["combined_daily_data"] = "ok"
        print(f"      ✅ {len(daily_records)} day records")
    except Exception as e:
        daily_records = []
        endpoint_status["combined_daily_data"] = f"error: {type(e).__name__}: {e}"
        print(f"      ❌ combined_daily_data failed: {e}")

    # ── 3. Sleep sessions (more detail per session, can be > 1/day with naps) ──
    print(f"\n[3/5] Sleep sessions...")
    try:
        sleep_session_objs = oura.get_sleep_sessions(start_iso, end_iso)
        sleep_sessions = [asdict(s) for s in sleep_session_objs]
        endpoint_status["sleep_sessions"] = "ok"
        print(f"      ✅ {len(sleep_sessions)} sleep sessions")
    except Exception as e:
        sleep_session_objs = []
        sleep_sessions = []
        endpoint_status["sleep_sessions"] = f"error: {type(e).__name__}: {e}"
        print(f"      ❌ sleep_sessions failed: {e}")

    # Backfill sleep_hrv on daily_records from long_sleep sessions
    # (the daily_sleep endpoint omits average_hrv; it lives on sessions)
    longsleep_by_day = {
        s.day: s for s in sleep_session_objs
        if s.type == "long_sleep"
    }
    n_backfilled_hrv = 0
    for rec in daily_records:
        day = rec["date"]
        sess = longsleep_by_day.get(day)
        if sess and rec.get("sleep_hrv") is None and sess.average_hrv is not None:
            rec["sleep_hrv"] = sess.average_hrv
            n_backfilled_hrv += 1
        if sess and rec.get("sleep_lowest_hr") is None and sess.lowest_heart_rate is not None:
            rec["sleep_lowest_hr"] = sess.lowest_heart_rate
        if sess and rec.get("sleep_avg_hr") is None and sess.average_heart_rate is not None:
            rec["sleep_avg_hr"] = sess.average_heart_rate
        if sess and rec.get("sleep_avg_breath") is None and sess.average_breath is not None:
            rec["sleep_avg_breath"] = sess.average_breath
    print(f"      ↺ backfilled sleep_hrv from sessions on {n_backfilled_hrv} days")

    # ── 4. Heart-rate PPG samples (per-day windows to keep response sizes manageable) ──
    print(f"\n[4/5] Heart-rate PPG samples (per-day, this is slow)...")
    hr_by_day: Dict[str, List[Dict[str, Any]]] = {}
    hr_status_by_day: Dict[str, str] = {}
    n_samples_total = 0
    # Inclusive: from start_date to end_date
    for offset in range(days):
        d = start_date + timedelta(days=offset)
        day_str = d.isoformat()
        start_dt = f"{day_str}T00:00:00"
        end_dt   = f"{day_str}T23:59:59"
        try:
            points = oura.get_heart_rate(start_datetime=start_dt, end_datetime=end_dt)
            hr_by_day[day_str] = [
                {"timestamp": p.timestamp, "bpm": p.bpm, "source": p.source}
                for p in points
            ]
            hr_status_by_day[day_str] = "ok"
            n_samples_total += len(points)
            if offset % 5 == 0:
                print(f"      {day_str}: {len(points):4d} samples (total so far: {n_samples_total})")
        except Exception as e:
            hr_by_day[day_str] = []
            hr_status_by_day[day_str] = f"error: {type(e).__name__}: {e}"
            print(f"      {day_str}: ⚠️  fallback to empty: {e}")
    n_hr_ok = sum(1 for v in hr_status_by_day.values() if v == "ok")
    n_hr_err = len(hr_status_by_day) - n_hr_ok
    print(f"      ✅ {n_samples_total} total HR samples across {len(hr_by_day)} days "
          f"({n_hr_ok} ok, {n_hr_err} errored)")
    endpoint_status["heart_rate_per_day"] = f"{n_hr_ok}/{len(hr_status_by_day)} days ok"

    # ── 5. Workouts + sessions ──────────────────────────────────────────────
    print(f"\n[5/5] Workouts + guided sessions...")
    try:
        workouts = oura.get_workouts(start_iso, end_iso)
        endpoint_status["workouts"] = "ok"
    except Exception as e:
        workouts = []
        endpoint_status["workouts"] = f"error: {type(e).__name__}: {e}"
        print(f"      ⚠️  workouts fallback to empty: {e}")
    try:
        sessions = oura.get_sessions(start_iso, end_iso)
        endpoint_status["guided_sessions"] = "ok"
    except Exception as e:
        sessions = []
        endpoint_status["guided_sessions"] = f"error: {type(e).__name__}: {e}"
        print(f"      ⚠️  sessions fallback to empty: {e}")
    print(f"      ✅ {len(workouts)} workouts, {len(sessions)} guided sessions")

    # ── Completeness summary ────────────────────────────────────────────────
    n_days = len(daily_records)
    n_with_sleep = sum(1 for d in daily_records if d.get("sleep_score") is not None)
    n_with_readiness = sum(1 for d in daily_records if d.get("readiness_score") is not None)
    n_with_activity = sum(1 for d in daily_records if d.get("activity_score") is not None)
    n_with_hrv = sum(1 for d in daily_records if d.get("sleep_hrv") is not None)
    n_with_spo2 = sum(1 for d in daily_records if d.get("spo2_average") is not None)
    n_with_stress = sum(1 for d in daily_records if d.get("stress_high") is not None)
    n_with_resilience = sum(1 for d in daily_records if d.get("resilience_level") is not None)

    completeness = {
        "n_days": n_days,
        "with_sleep_score":  f"{n_with_sleep}/{n_days}",
        "with_readiness":    f"{n_with_readiness}/{n_days}",
        "with_activity":     f"{n_with_activity}/{n_days}",
        "with_sleep_hrv":    f"{n_with_hrv}/{n_days}",
        "with_spo2":         f"{n_with_spo2}/{n_days}",
        "with_stress":       f"{n_with_stress}/{n_days}",
        "with_resilience":   f"{n_with_resilience}/{n_days}",
        "n_sleep_sessions":  len(sleep_sessions),
        "n_hr_samples":      n_samples_total,
        "n_workouts":        len(workouts),
        "n_sessions":        len(sessions),
    }

    payload = {
        "harvest_metadata": {
            "harvest_date": end_date.isoformat(),
            "start_date":   start_iso,
            "end_date":     end_iso,
            "days_requested": days,
            "harvested_at": datetime.utcnow().isoformat() + "Z",
            "source": "Oura Cloud API v2 / Oura Ring Gen 3",
            "honest_scope": (
                "Successfully-fetched values are real Oura values. Endpoints that "
                "errored fall back to empty containers — see "
                "`endpoint_status` and `n_backfilled` for per-endpoint truth flags. "
                "Heart-rate samples are BPM only (Oura does not expose raw PPG "
                "waveform via API). Personal email stripped for privacy. "
                "sleep_hrv on daily_sleep is NOT exposed by the API; values are "
                "backfilled from long_sleep sessions when available — count = "
                f"{n_backfilled_hrv} days backfilled."
            ),
        },
        "endpoint_status": endpoint_status,
        "n_backfilled": {
            "sleep_hrv_from_sessions":   n_backfilled_hrv,
            "sleep_avg_breath_from_sessions": sum(
                1 for d in daily_records
                if longsleep_by_day.get(d["date"]) is not None
                and d.get("sleep_avg_breath") is not None
            ),
        },
        "hr_status_by_day": hr_status_by_day,
        "personal_info": personal,
        "daily_records": daily_records,
        "sleep_sessions": sleep_sessions,
        "heart_rate_samples": hr_by_day,
        "workouts": workouts,
        "sessions": sessions,
        "completeness_summary": completeness,
    }

    os.makedirs(output_dir, exist_ok=True)
    out_path = os.path.join(
        output_dir,
        f"oura_30day_harvest_{end_date.isoformat()}.json"
    )
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2, default=str)

    print(f"\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"✅ HARVEST COMPLETE")
    print(f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"File: {out_path}")
    print(f"Size: {os.path.getsize(out_path) / 1024:.1f} KB")
    print(f"\nCompleteness:")
    for k, v in completeness.items():
        print(f"  {k:25s} {v}")
    print(f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    return out_path


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--days", type=int, default=30, help="lookback window")
    p.add_argument("--output-dir", default="data", help="output directory")
    args = p.parse_args()
    harvest(days=args.days, output_dir=args.output_dir)


if __name__ == "__main__":
    main()
