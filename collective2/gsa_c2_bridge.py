"""
GSA to Collective2 Bridge
Reads daily GSA signals and submits to C2 for live trading

Usage:
    python collective2/gsa_c2_bridge.py --mode test     # Test connection
    python collective2/gsa_c2_bridge.py --mode signals  # Show today's signals
    python collective2/gsa_c2_bridge.py --mode submit   # Submit to C2
"""

import os
import sys
import json
import argparse
from datetime import datetime, timedelta
from typing import Dict, List, Optional
from dataclasses import dataclass

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from collective2.collective2_integration import (
    Collective2Client, ARTASignalGenerator, C2Signal, 
    SignalAction, C2Response
)

SIGNALS_FILE = "data/daily_signals.json"

# Position sizing based on account size
# Adjust these for your risk tolerance
DEFAULT_POSITION_SIZE = 100  # shares per position
MAX_POSITIONS = 5  # max concurrent positions
CAPITAL_PER_POSITION = 10000  # $ per position (for dollar-based sizing)

@dataclass
class GSASignal:
    ticker: str
    action: str  # strong_buy, buy, hold, sell, strong_sell
    confidence: float
    gile: float
    price: float
    regime: str
    timestamp: str

def load_latest_signals() -> List[GSASignal]:
    """Load the most recent GSA signals from daily_signals.json"""
    
    if not os.path.exists(SIGNALS_FILE):
        print(f"Error: {SIGNALS_FILE} not found")
        print("Run the daily signal generator first")
        return []
    
    with open(SIGNALS_FILE, 'r') as f:
        data = json.load(f)
    
    if not data.get('signals'):
        print("No signals found in file")
        return []
    
    # Get the most recent signal batch
    latest = data['signals'][-1]
    signal_date = latest.get('date', 'unknown')
    
    print(f"Loading signals from: {signal_date}")
    print(f"Total signals: {latest.get('total_signals', 0)}")
    print(f"Buy signals: {latest.get('buy_count', 0)}")
    print()
    
    signals = []
    for s in latest.get('signals', []):
        signals.append(GSASignal(
            ticker=s['ticker'],
            action=s['action'],
            confidence=s['confidence'],
            gile=s['gile'],
            price=s['price'],
            regime=s['regime'],
            timestamp=s['timestamp']
        ))
    
    return signals

def get_actionable_signals(signals: List[GSASignal]) -> List[GSASignal]:
    """Filter to only actionable signals (buys and sells, not holds)"""
    return [s for s in signals if s.action in ('strong_buy', 'buy', 'sell', 'strong_sell')]

def calculate_position_size(signal: GSASignal, method: str = 'fixed') -> int:
    """
    Calculate position size based on signal and method
    
    Methods:
        'fixed': Fixed number of shares
        'dollar': Fixed dollar amount per position
        'confidence': Scale by signal confidence
    """
    
    if method == 'fixed':
        return DEFAULT_POSITION_SIZE
    
    elif method == 'dollar':
        if signal.price > 0:
            shares = int(CAPITAL_PER_POSITION / signal.price)
            return max(shares, 1)
        return DEFAULT_POSITION_SIZE
    
    elif method == 'confidence':
        base = DEFAULT_POSITION_SIZE
        # Scale 0.5x to 1.5x based on confidence
        multiplier = 0.5 + signal.confidence
        return int(base * multiplier)
    
    return DEFAULT_POSITION_SIZE

def display_signals(signals: List[GSASignal]):
    """Display signals in a nice format"""
    
    print("=" * 70)
    print("GSA DAILY SIGNALS")
    print("=" * 70)
    print()
    
    # Group by action
    strong_buys = [s for s in signals if s.action == 'strong_buy']
    buys = [s for s in signals if s.action == 'buy']
    holds = [s for s in signals if s.action == 'hold']
    sells = [s for s in signals if s.action in ('sell', 'strong_sell')]
    
    if strong_buys:
        print("🚀 STRONG BUY:")
        for s in strong_buys:
            print(f"   {s.ticker:6} @ ${s.price:>8.2f}  GILE={s.gile:.3f}  regime={s.regime}")
    
    if buys:
        print("\n✅ BUY:")
        for s in buys:
            print(f"   {s.ticker:6} @ ${s.price:>8.2f}  GILE={s.gile:.3f}  regime={s.regime}")
    
    if holds:
        print("\n⏸️  HOLD:")
        for s in holds:
            print(f"   {s.ticker:6} @ ${s.price:>8.2f}  GILE={s.gile:.3f}  regime={s.regime}")
    
    if sells:
        print("\n🔴 SELL:")
        for s in sells:
            print(f"   {s.ticker:6} @ ${s.price:>8.2f}  GILE={s.gile:.3f}  regime={s.regime}")
    
    print()
    print("=" * 70)

def test_c2_connection() -> bool:
    """Test connection to Collective2"""
    
    print("Testing Collective2 Connection...")
    print()
    
    # Check environment variables
    api_key = os.environ.get('COLLECTIVE2_API_KEY', '')
    system_id = os.environ.get('COLLECTIVE2_SYSTEM_ID', '')
    
    print(f"API Key: {'✅ Set' if api_key else '❌ Missing'}")
    print(f"System ID: {system_id if system_id else '❌ Missing'}")
    print()
    
    if not api_key or not system_id:
        print("Configuration incomplete!")
        print()
        print("To set up Collective2:")
        print("1. Go to https://collective2.com/sell-trading-system")
        print("2. Create a new strategy (or use existing)")
        print("3. Note your System ID from the strategy page")
        print("4. Get your API key from https://collective2.com/platform-transmit/manage/")
        print("5. Add secrets in Replit:")
        print("   - COLLECTIVE2_API_KEY = your_api_key")
        print("   - COLLECTIVE2_SYSTEM_ID = your_system_id")
        return False
    
    try:
        client = Collective2Client()
        
        # Try to get system stats
        stats = client.get_system_stats()
        
        if stats.get('ok') == 1:
            print("✅ Connection successful!")
            print()
            response = stats.get('response', {})
            print(f"System Name: {response.get('systemname', 'N/A')}")
            print(f"Age (days): {response.get('agedays', 'N/A')}")
            print(f"Trades: {response.get('numtrades', 'N/A')}")
            return True
        else:
            error = stats.get('title', stats.get('message', stats.get('error', 'Unknown error')))
            print(f"❌ Connection failed: {error}")
            
            if 'systemid' in str(error).lower():
                print()
                print("The System ID appears to be incorrect.")
                print("Please verify your COLLECTIVE2_SYSTEM_ID is correct.")
                print("You can find it on your strategy page at Collective2.")
            
            return False
            
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def submit_signals_to_c2(signals: List[GSASignal], dry_run: bool = True) -> Dict:
    """
    Submit GSA signals to Collective2
    
    Args:
        signals: List of GSA signals to submit
        dry_run: If True, only show what would be submitted
    
    Returns:
        Summary of submission results
    """
    
    actionable = get_actionable_signals(signals)
    
    if not actionable:
        print("No actionable signals to submit")
        return {'submitted': 0, 'skipped': 0, 'errors': []}
    
    # Limit to top signals
    buys = [s for s in actionable if s.action in ('strong_buy', 'buy')]
    sells = [s for s in actionable if s.action in ('sell', 'strong_sell')]
    
    # Sort buys by GILE score (highest first)
    buys.sort(key=lambda x: x.gile, reverse=True)
    
    # Take top N positions
    top_buys = buys[:MAX_POSITIONS]
    
    print(f"Signals to submit: {len(top_buys)} buys, {len(sells)} sells")
    print()
    
    if dry_run:
        print("=" * 50)
        print("DRY RUN - No orders will be placed")
        print("=" * 50)
        print()
        
        for s in top_buys:
            qty = calculate_position_size(s, method='dollar')
            print(f"  BUY  {s.ticker:6} x {qty:4} shares @ ${s.price:.2f}")
            print(f"        GILE={s.gile:.3f}, confidence={s.confidence:.1f}")
        
        for s in sells:
            print(f"  SELL {s.ticker:6} (close position)")
            print(f"        GILE={s.gile:.3f}, confidence={s.confidence:.1f}")
        
        print()
        print("To actually submit, run with --submit flag")
        return {'submitted': 0, 'dry_run': True}
    
    # Live submission
    try:
        client = Collective2Client()
        generator = ARTASignalGenerator(client)
        generator.position_size = DEFAULT_POSITION_SIZE
        
        # Refresh current positions
        print("Refreshing current positions...")
        try:
            generator.refresh_positions()
            if generator.current_positions:
                print(f"  Current positions: {generator.current_positions}")
            else:
                print("  No current positions")
        except Exception as e:
            print(f"  Warning: Could not refresh positions ({e})")
        
        print()
        
        results = {
            'submitted': 0,
            'skipped': 0,
            'errors': []
        }
        
        # Submit buy signals
        for s in top_buys:
            qty = calculate_position_size(s, method='dollar')
            print(f"Submitting BUY {s.ticker} x {qty}...")
            
            result = generator.submit_arta_signal(s.ticker, s.action, s.confidence)
            
            if result.success:
                print(f"  ✅ Success: {result.message}")
                results['submitted'] += 1
            else:
                print(f"  ⚠️ Skipped: {result.message}")
                if 'error' in result.message.lower():
                    results['errors'].append(f"{s.ticker}: {result.message}")
                else:
                    results['skipped'] += 1
        
        # Submit sell signals
        for s in sells:
            print(f"Submitting SELL {s.ticker}...")
            
            result = generator.submit_arta_signal(s.ticker, s.action, s.confidence)
            
            if result.success:
                print(f"  ✅ Success: {result.message}")
                results['submitted'] += 1
            else:
                print(f"  ⚠️ Skipped: {result.message}")
                results['skipped'] += 1
        
        print()
        print("=" * 50)
        print("SUBMISSION COMPLETE")
        print(f"  Submitted: {results['submitted']}")
        print(f"  Skipped: {results['skipped']}")
        if results['errors']:
            print(f"  Errors: {len(results['errors'])}")
            for e in results['errors']:
                print(f"    - {e}")
        print("=" * 50)
        
        return results
        
    except Exception as e:
        print(f"Error: {e}")
        return {'submitted': 0, 'errors': [str(e)]}

def main():
    parser = argparse.ArgumentParser(description="GSA to Collective2 Bridge")
    parser.add_argument('--mode', choices=['test', 'signals', 'submit', 'dry-run'], 
                        default='signals',
                        help='Operation mode')
    parser.add_argument('--submit', action='store_true',
                        help='Actually submit orders (not dry run)')
    
    args = parser.parse_args()
    
    print()
    print("=" * 50)
    print("GSA → COLLECTIVE2 BRIDGE")
    print("=" * 50)
    print()
    
    if args.mode == 'test':
        test_c2_connection()
    
    elif args.mode == 'signals':
        signals = load_latest_signals()
        if signals:
            display_signals(signals)
    
    elif args.mode == 'submit' or args.mode == 'dry-run':
        # First test connection
        if not test_c2_connection():
            print("\nFix connection issues before submitting signals.")
            return
        
        print()
        
        # Load signals
        signals = load_latest_signals()
        if not signals:
            return
        
        display_signals(signals)
        
        # Submit (or dry run)
        dry_run = not args.submit and args.mode != 'submit'
        submit_signals_to_c2(signals, dry_run=dry_run)

if __name__ == "__main__":
    main()
