"""
GSA Daily Scheduler
===================
Runs gsa_live_trader.py (LIVE orders) at 9:35 AM ET on weekdays.
Uses zoneinfo for correct EST/EDT detection — no hardcoded UTC offset.

To see signals without placing orders: python gsa_live_trader.py --dry
To execute orders manually right now:  python gsa_live_trader.py
"""

import time
import datetime
import subprocess
import sys
from zoneinfo import ZoneInfo

ET = ZoneInfo("America/New_York")


def now_et() -> datetime.datetime:
    return datetime.datetime.now(tz=ET)


def is_weekday() -> bool:
    return now_et().weekday() < 5   # Mon=0 … Fri=4


def run_daily_cycle():
    ts = now_et().strftime("%Y-%m-%d %H:%M:%S ET")
    print(f"\n{'='*60}")
    print(f"  GSA DAILY LIVE CYCLE — {ts}")
    print(f"{'='*60}")
    try:
        result = subprocess.run(
            [sys.executable, "gsa_live_trader.py"],   # LIVE — no --dry
            capture_output=False,
            timeout=300
        )
        if result.returncode == 0:
            print("  ✅ Daily live cycle complete")
        else:
            print(f"  ❌ Live cycle exited with code {result.returncode}")
    except Exception as e:
        print(f"  ❌ Error running live cycle: {e}")


def already_ran_today_per_db() -> bool:
    """Pass-44 catch-up: query gsa_performance_log to see if a live cycle
    already ran today (US/Eastern). Returns False on any DB error so we
    don't suppress a retry on transient connectivity issues."""
    try:
        import os, psycopg2
        conn = psycopg2.connect(os.environ["DATABASE_URL"])
        cur = conn.cursor()
        today_et = now_et().date()
        cur.execute(
            "SELECT COUNT(*) FROM gsa_performance_log "
            "WHERE (recorded_at AT TIME ZONE 'America/New_York')::date = %s",
            (today_et,))
        n = cur.fetchone()[0]
        cur.close(); conn.close()
        return n > 0
    except Exception as e:
        print(f"  ⚠ DB catch-up check failed (will allow retry): {e}")
        return False


def main():
    print(f"GSA Daily Scheduler started — {now_et().strftime('%Y-%m-%d %H:%M %Z')}")
    print("Will run LIVE orders at 9:35 AM ET each trading weekday.")
    print("Pass-44 catch-up: also runs immediately if it's after 9:35 ET")
    print("on a weekday and DB shows no run for today yet.")
    print("Timezone: America/New_York (auto EST/EDT)")
    print("Manual override: python gsa_live_trader.py")

    ran_today: datetime.date = None

    while True:
        today = now_et().date()
        et    = now_et()
        h, m  = et.hour, et.minute

        # Reset in-memory flag at midnight ET so a new day allows a fresh run
        if ran_today != today:
            # Pass-44 catch-up: if the workflow restarted mid-day after the
            # 9:35 ET window, run immediately rather than waiting until
            # tomorrow morning. Guard with DB check so we don't double-fire.
            past_open = (h > 9) or (h == 9 and m >= 35)
            before_close = h < 16  # don't fire after 4pm ET (market closed)
            if (is_weekday() and past_open and before_close
                    and not already_ran_today_per_db()):
                print(f"  ↪ Catch-up trigger: {et.strftime('%H:%M %Z')} "
                      f"is past 9:35 ET on a weekday and DB has no run today")
                run_daily_cycle()
                ran_today = today
                time.sleep(60); continue

        if is_weekday() and h == 9 and m >= 35 and ran_today != today:
            run_daily_cycle()
            ran_today = today

        time.sleep(60)


if __name__ == "__main__":
    main()
