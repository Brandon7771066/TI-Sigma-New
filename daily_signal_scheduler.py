"""
Daily GSA Signal Scheduler
Runs the algorithm daily and logs signals for Collective2 entry
"""

import os
import json
import time
from datetime import datetime, timedelta
from apscheduler.schedulers.blocking import BlockingScheduler
from apscheduler.triggers.cron import CronTrigger
import numpy as np
import yfinance as yf

from gsa_core import GSACore, MarketRegime

SIGNAL_LOG_FILE = "data/daily_signals.json"
os.makedirs("data", exist_ok=True)


def load_signal_history():
    """Load historical signals"""
    if os.path.exists(SIGNAL_LOG_FILE):
        with open(SIGNAL_LOG_FILE, 'r') as f:
            return json.load(f)
    return {"signals": [], "performance": []}


def save_signal_history(history):
    """Save signal history"""
    with open(SIGNAL_LOG_FILE, 'w') as f:
        json.dump(history, f, indent=2, default=str)


def generate_daily_signals():
    """Generate and log daily trading signals"""
    print(f"\n{'='*60}")
    print(f"DAILY SIGNAL GENERATION - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*60}")
    
    gsa = GSACore(lookback_short=7, lookback_long=60)
    
    GREEN_LIGHT_STOCKS = [
        'GOOGL', 'NVDA', 'MSFT', 'META',
        'CAT', 'GE',
        'GS', 'MS',
        'XOM', 'CVX', 'COP',
        'WMT', 'TJX'
    ]
    
    signals = []
    
    for ticker in GREEN_LIGHT_STOCKS:
        try:
            data = yf.download(ticker, period="3mo", progress=False)
            if data.empty or len(data) < 60:
                continue
            
            close_values = data['Close'].values
            closes = np.array(close_values.flatten() if hasattr(close_values, 'flatten') 
                            else close_values, dtype=float)
            
            price_diff = np.diff(closes)
            returns = (price_diff / closes[:-1]) * 100
            
            xi = gsa.compute_xi_metrics(returns[-60:], closes[-60:])
            gile = gsa.compute_gile(returns[-60:], closes[-60:])
            regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, 1.0)
            signal = gsa.generate_signal(xi, gile, regime, conf)
            
            signal_data = {
                'ticker': ticker,
                'action': signal.action,
                'confidence': round(signal.confidence, 3),
                'gile': round(gile.composite, 3),
                'price': round(float(closes[-1]), 2),
                'regime': regime.value,
                'timestamp': datetime.now().isoformat()
            }
            signals.append(signal_data)
            
            print(f"  {ticker:6s}: {signal.action:12s} | GILE {gile.composite:.3f} | "
                  f"Conf {signal.confidence:.2f} | ${closes[-1]:.2f}")
            
        except Exception as e:
            print(f"  Error processing {ticker}: {str(e)[:40]}")
    
    buy_signals = [s for s in signals if s['action'] in ['buy', 'strong_buy']]
    sell_signals = [s for s in signals if s['action'] in ['sell', 'strong_sell']]
    
    history = load_signal_history()
    
    daily_summary = {
        'date': datetime.now().strftime('%Y-%m-%d'),
        'time': datetime.now().strftime('%H:%M:%S'),
        'total_signals': len(signals),
        'buy_count': len(buy_signals),
        'sell_count': len(sell_signals),
        'signals': signals,
        'top_buys': sorted(buy_signals, key=lambda x: x['gile'], reverse=True)[:5]
    }
    
    history['signals'].append(daily_summary)
    
    if len(history['signals']) > 90:
        history['signals'] = history['signals'][-90:]
    
    save_signal_history(history)
    
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Total signals: {len(signals)}")
    print(f"Buy signals: {len(buy_signals)}")
    print(f"Sell signals: {len(sell_signals)}")
    
    if buy_signals:
        print(f"\nTOP 5 BUYS FOR COLLECTIVE2:")
        for i, sig in enumerate(sorted(buy_signals, key=lambda x: x['gile'], reverse=True)[:5], 1):
            print(f"  {i}. {sig['ticker']:6s} @ ${sig['price']:8.2f} | GILE {sig['gile']:.3f}")
    
    print(f"\nSignals saved to: {SIGNAL_LOG_FILE}")
    print(f"{'='*60}\n")
    
    return daily_summary


def run_scheduler():
    """Run the daily scheduler"""
    print("Starting GSA Daily Signal Scheduler")
    print("Signals will be generated at 9:35 AM ET (market open + 5 min)")
    
    generate_daily_signals()
    
    scheduler = BlockingScheduler()
    
    scheduler.add_job(
        generate_daily_signals,
        CronTrigger(hour=9, minute=35, timezone='America/New_York'),
        id='daily_signals',
        name='Generate daily GSA signals',
        replace_existing=True
    )
    
    scheduler.add_job(
        generate_daily_signals,
        CronTrigger(hour=15, minute=30, timezone='America/New_York'),
        id='afternoon_signals',
        name='Generate afternoon GSA signals',
        replace_existing=True
    )
    
    print("Scheduler started. Press Ctrl+C to stop.")
    
    try:
        scheduler.start()
    except KeyboardInterrupt:
        print("Scheduler stopped.")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--once":
        generate_daily_signals()
    else:
        run_scheduler()
