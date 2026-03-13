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


def main():
    print(f"GSA Daily Scheduler started — {now_et().strftime('%Y-%m-%d %H:%M %Z')}")
    print("Will run LIVE orders at 9:35 AM ET each trading weekday.")
    print("Timezone: America/New_York (auto EST/EDT)")
    print("Manual override: python gsa_live_trader.py")

    ran_today: datetime.date = None

    while True:
        today = now_et().date()
        et    = now_et()
        h, m  = et.hour, et.minute

        if is_weekday() and h == 9 and m >= 35 and ran_today != today:
            run_daily_cycle()
            ran_today = today

        time.sleep(60)


if __name__ == "__main__":
    main()
