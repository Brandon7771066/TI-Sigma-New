"""
Collective2 Trading Manager
Submit GSA signals to Collective2 for live trading
"""

import streamlit as st
import sys
import os
import json

sys.path.append('..')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

st.set_page_config(page_title="Collective2 Manager", page_icon="📊", layout="wide")

st.title("📊 Collective2 Trading Manager")
st.markdown("**Connect GSA algorithm to Collective2 for live trading signals**")

# Check configuration status
api_key = os.environ.get('COLLECTIVE2_API_KEY', '')
system_id = os.environ.get('COLLECTIVE2_SYSTEM_ID', '')

st.divider()

# Configuration Status
col1, col2 = st.columns(2)
with col1:
    st.markdown("### Configuration Status")
    if api_key:
        st.success(f"✅ API Key: Configured ({len(api_key)} chars)")
    else:
        st.error("❌ API Key: Missing")
    
    if system_id:
        st.success(f"✅ System ID: {system_id}")
    else:
        st.error("❌ System ID: Missing")

with col2:
    st.markdown("### Connection Test")
    if st.button("🔌 Test Connection", type="primary"):
        if not api_key or not system_id:
            st.error("Configure API Key and System ID first!")
        else:
            try:
                from collective2.collective2_integration import Collective2Client
                client = Collective2Client()
                stats = client.get_system_stats()
                
                if stats.get('ok') == 1:
                    st.success("✅ Connected to Collective2!")
                    response = stats.get('response', {})
                    st.json({
                        'System Name': response.get('systemname', 'N/A'),
                        'Age (days)': response.get('agedays', 'N/A'),
                        'Trades': response.get('numtrades', 'N/A')
                    })
                else:
                    error = stats.get('title', stats.get('message', stats.get('error', 'Unknown')))
                    st.error(f"Connection failed: {error}")
                    
                    if 'systemid' in str(error).lower():
                        st.warning("""
                        **System ID Issue Detected**
                        
                        This usually means:
                        1. The API key was created for a different strategy
                        2. The System ID is incorrect
                        
                        To fix:
                        1. Go to your C2 strategy page
                        2. Note the System ID from the URL or settings
                        3. Generate a NEW API key for that specific strategy
                        4. Update both secrets in Replit
                        """)
            except Exception as e:
                st.error(f"Error: {e}")

st.divider()

# Setup Instructions
with st.expander("📋 Setup Instructions"):
    st.markdown("""
    ### How to Connect GSA to Collective2
    
    **Step 1: Create a Strategy on Collective2**
    1. Go to [collective2.com/sell-trading-system](https://collective2.com/sell-trading-system)
    2. Create a new trading strategy (free to start)
    3. Note your **System ID** from the strategy URL or settings
    
    **Step 2: Get Your API Key**
    1. Go to [Platform Transmit Manager](https://collective2.com/platform-transmit/manage/)
    2. Create a new API key FOR YOUR SPECIFIC STRATEGY
    3. Copy the API key
    
    **Step 3: Add Secrets in Replit**
    1. Go to Replit's Secrets tab (🔒)
    2. Add: `COLLECTIVE2_API_KEY` = your_api_key
    3. Add: `COLLECTIVE2_SYSTEM_ID` = your_system_id
    
    **Step 4: Test Connection**
    - Click the "Test Connection" button above
    - If successful, you can start submitting signals!
    
    ---
    
    **Important Notes:**
    - The API key must be created for the SAME strategy as your System ID
    - Generate a fresh API key if you're having permission issues
    - Your strategy must be "active" on C2 to receive signals
    """)

st.divider()

# Load and Display Signals
st.markdown("### 📈 Today's GSA Signals")

SIGNALS_FILE = "data/daily_signals.json"

if os.path.exists(SIGNALS_FILE):
    with open(SIGNALS_FILE, 'r') as f:
        data = json.load(f)
    
    if data.get('signals'):
        latest = data['signals'][-1]
        signal_date = latest.get('date', 'unknown')
        
        st.info(f"Signals from: **{signal_date}** | Total: {latest.get('total_signals', 0)} | Buy signals: {latest.get('buy_count', 0)}")
        
        signals = latest.get('signals', [])
        
        # Display in columns
        col_buy, col_hold, col_sell = st.columns(3)
        
        strong_buys = [s for s in signals if s.get('action') == 'strong_buy']
        buys = [s for s in signals if s.get('action') == 'buy']
        holds = [s for s in signals if s.get('action') == 'hold']
        sells = [s for s in signals if s.get('action') in ('sell', 'strong_sell')]
        
        with col_buy:
            st.markdown("#### 🚀 Buy Signals")
            if strong_buys:
                for s in strong_buys:
                    st.success(f"**{s['ticker']}** STRONG BUY @ ${s['price']:.2f}")
                    st.caption(f"GILE: {s['gile']:.3f} | {s['regime']}")
            if buys:
                for s in buys:
                    st.info(f"**{s['ticker']}** BUY @ ${s['price']:.2f}")
                    st.caption(f"GILE: {s['gile']:.3f} | {s['regime']}")
            if not strong_buys and not buys:
                st.caption("No buy signals today")
        
        with col_hold:
            st.markdown("#### ⏸️ Hold")
            if holds:
                for s in holds:
                    st.warning(f"**{s['ticker']}** @ ${s['price']:.2f}")
                    st.caption(f"GILE: {s['gile']:.3f}")
            else:
                st.caption("No holds")
        
        with col_sell:
            st.markdown("#### 🔴 Sell Signals")
            if sells:
                for s in sells:
                    st.error(f"**{s['ticker']}** SELL @ ${s['price']:.2f}")
                    st.caption(f"GILE: {s['gile']:.3f} | {s['regime']}")
            else:
                st.caption("No sell signals today")
        
        st.divider()
        
        # Submit to C2
        st.markdown("### 🚀 Submit to Collective2")
        
        actionable = [s for s in signals if s.get('action') in ('strong_buy', 'buy', 'sell', 'strong_sell')]
        
        if not actionable:
            st.info("No actionable signals to submit (only holds)")
        else:
            st.warning(f"Ready to submit {len(actionable)} actionable signals")
            
            # Show what will be submitted
            with st.expander("Preview Submission"):
                for s in actionable:
                    action_emoji = "🟢" if s['action'] in ('strong_buy', 'buy') else "🔴"
                    st.write(f"{action_emoji} {s['action'].upper()}: {s['ticker']} @ ${s['price']:.2f}")
            
            col_dry, col_live = st.columns(2)
            
            with col_dry:
                if st.button("🔍 Dry Run (Preview Only)"):
                    st.info("Would submit the signals above. No actual orders placed.")
            
            with col_live:
                submit_btn = st.button("⚡ SUBMIT LIVE SIGNALS", type="primary", 
                                       disabled=not (api_key and system_id))
                
                if submit_btn:
                    st.warning("Live submission starting...")
                    
                    try:
                        from collective2.collective2_integration import Collective2Client, ARTASignalGenerator
                        
                        client = Collective2Client()
                        generator = ARTASignalGenerator(client)
                        
                        results = []
                        for s in actionable:
                            result = generator.submit_arta_signal(
                                s['ticker'], 
                                s['action'], 
                                s.get('confidence', 0.6)
                            )
                            results.append({
                                'ticker': s['ticker'],
                                'action': s['action'],
                                'success': result.success,
                                'message': result.message
                            })
                        
                        # Show results
                        success_count = sum(1 for r in results if r['success'])
                        st.success(f"Submitted {success_count}/{len(results)} signals")
                        
                        for r in results:
                            if r['success']:
                                st.success(f"✅ {r['ticker']}: {r['message']}")
                            else:
                                st.warning(f"⚠️ {r['ticker']}: {r['message']}")
                                
                    except Exception as e:
                        st.error(f"Submission failed: {e}")
    else:
        st.warning("No signals found in database")
else:
    st.error(f"Signals file not found: {SIGNALS_FILE}")
    st.info("Run the daily signal generator to create signals")

st.divider()

# Command line reference
with st.expander("🖥️ Command Line Tools"):
    st.markdown("""
    ```bash
    # Test connection
    python collective2/gsa_c2_bridge.py --mode test
    
    # View today's signals
    python collective2/gsa_c2_bridge.py --mode signals
    
    # Dry run (preview submission)
    python collective2/gsa_c2_bridge.py --mode dry-run
    
    # Submit live signals
    python collective2/gsa_c2_bridge.py --mode submit --submit
    ```
    """)
