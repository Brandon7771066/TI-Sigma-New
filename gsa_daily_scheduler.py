"""
GSA Daily Scheduler
===================
Runs gsa_live_trader.py --dry at 9:35 AM ET each trading weekday.
Provides a daily signal log without executing orders.
To execute live orders: run `python gsa_live_trader.py` manually.

Runs as a persistent background workflow.
"""

import time
import datetime
import subprocess
import sys

def is_weekday():
    return datetime.datetime.now().weekday() < 5  # Mon=0, Fri=4

def eastern_hour_minute():
    now = datetime.datetime.utcnow()
    # ET = UTC-5 (EST) or UTC-4 (EDT); approximate as UTC-5 for simplicity
    et = now - datetime.timedelta(hours=5)
    return et.hour, et.minute

def run_daily_signals():
    print(f"\n{'='*60}")
    print(f"  GSA DAILY SIGNAL RUN — {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*60}")
    try:
        result = subprocess.run(
            [sys.executable, "gsa_live_trader.py", "--dry"],
            capture_output=False,
            timeout=300
        )
        if result.returncode == 0:
            print("  ✅ Daily signal run complete")
        else:
            print(f"  ❌ Signal run exited with code {result.returncode}")
    except Exception as e:
        print(f"  ❌ Error: {e}")

def main():
    print(f"GSA Daily Scheduler started — {datetime.datetime.now()}")
    print("Will run signals at 9:35 AM ET on weekdays.")
    print("Use `python gsa_live_trader.py` to execute live orders manually.")

    ran_today = None

    while True:
        today = datetime.date.today()
        h, m  = eastern_hour_minute()

        if is_weekday() and h == 9 and m >= 35 and ran_today != today:
            run_daily_signals()
            ran_today = today

        time.sleep(60)

if __name__ == "__main__":
    main()
