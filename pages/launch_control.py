"""
Launch Control Dashboard
========================
Unified command center for revenue generation:
- Kalshi prediction market live trading
- Alpaca GSA paper trading
- Revenue strategy overview
"""

import streamlit as st
import os
from datetime import datetime, timedelta

st.header("Launch Control - Revenue Command Center")

tab_kalshi, tab_alpaca, tab_strategy = st.tabs([
    "Kalshi Prediction Markets",
    "Alpaca Paper Trading (GSA)",
    "Revenue Strategy"
])

with tab_kalshi:
    st.subheader("Kalshi Live Market Scanner")

    api_key_id = os.environ.get('KALSHI_API_KEY_ID', '')
    private_key = os.environ.get('KALSHI_PRIVATE_KEY', '')
    has_credentials = bool(api_key_id and private_key)

    if has_credentials:
        st.success("Kalshi API credentials connected")
    else:
        st.warning("Add KALSHI_API_KEY_ID and KALSHI_PRIVATE_KEY to secrets to connect.")

    col_bankroll, col_scan_type = st.columns(2)
    with col_bankroll:
        bankroll = st.number_input("Bankroll ($)", min_value=10.0, max_value=10000.0, value=300.0, step=50.0)
    with col_scan_type:
        scan_type = st.selectbox("Scan Type", [
            "Weather Markets (daily resolution)",
            "All Markets (general scan)",
            "Economics & Financials",
            "Politics & Elections",
            "Science & Technology"
        ])

    col_btn1, col_btn2 = st.columns(2)
    with col_btn1:
        scan_clicked = st.button("Scan Markets", type="primary", use_container_width=True, disabled=not has_credentials)
    with col_btn2:
        check_balance = st.button("Check Balance & Positions", use_container_width=True, disabled=not has_credentials)

    if check_balance and has_credentials:
        with st.spinner("Checking account..."):
            try:
                from kalshi_live_scanner import KalshiLiveScanner
                scanner = KalshiLiveScanner()
                if scanner.connect():
                    balance = scanner.get_balance()
                    positions = scanner.get_positions()
                    c1, c2 = st.columns(2)
                    with c1:
                        st.metric("Account Balance", f"${balance:.2f}")
                    with c2:
                        st.metric("Open Positions", len(positions))
                    if positions:
                        st.markdown("### Current Positions")
                        for pos in positions:
                            ticker = pos.get('ticker', '')
                            qty = pos.get('total_traded', 0)
                            st.markdown(f"- **{ticker}**: {qty} contracts")
                else:
                    st.error("Could not connect to Kalshi")
            except Exception as e:
                st.error(f"Error: {str(e)}")

    if scan_clicked and has_credentials:
        with st.spinner("Connecting to Kalshi and scanning markets..."):
            try:
                from kalshi_live_scanner import KalshiLiveScanner
                scanner = KalshiLiveScanner()
                connected = scanner.connect()

                if connected:
                    balance = scanner.get_balance()
                    st.success(f"Connected! Balance: ${balance:.2f}")

                    markets = []
                    if scan_type == "Weather Markets (daily resolution)":
                        markets = scanner.scan_weather_markets()
                    else:
                        all_markets = scanner.scan_all_markets(limit=500)
                        if scan_type == "Economics & Financials":
                            markets = [m for m in all_markets if any(c in m.get('category', '').lower() for c in ['economics', 'financials', 'financial'])]
                        elif scan_type == "Politics & Elections":
                            markets = [m for m in all_markets if any(c in m.get('category', '').lower() for c in ['politics', 'elections', 'political'])]
                        elif scan_type == "Science & Technology":
                            markets = [m for m in all_markets if any(c in m.get('category', '').lower() for c in ['science', 'technology', 'tech'])]
                        else:
                            markets = all_markets

                    if markets:
                        st.session_state['kalshi_markets'] = markets
                        st.session_state['kalshi_scan_type'] = scan_type
                        st.info(f"Found {len(markets)} markets")
                    else:
                        st.warning("No markets found for this category")
                else:
                    st.error("Could not connect. Check your API credentials.")
            except Exception as e:
                st.error(f"Error scanning: {str(e)}")

    if 'kalshi_markets' in st.session_state and st.session_state['kalshi_markets']:
        markets = st.session_state['kalshi_markets']
        scan_label = st.session_state.get('kalshi_scan_type', 'All')

        high_conf = [m for m in markets if m.get('our_probability', 0) >= 0.85]
        med_conf = [m for m in markets if 0.70 <= m.get('our_probability', 0) < 0.85]
        best_profit = sorted(markets, key=lambda x: x.get('profit_potential', 0), reverse=True)

        c1, c2, c3, c4 = st.columns(4)
        with c1:
            st.metric("Total Markets", len(markets))
        with c2:
            st.metric("High Confidence (85%+)", len(high_conf))
        with c3:
            st.metric("Medium (70-85%)", len(med_conf))
        with c4:
            avg_profit = sum(m.get('profit_potential', 0) for m in markets[:20]) / max(len(markets[:20]), 1)
            st.metric("Avg Profit (top 20)", f"{avg_profit:.1f}%")

        view_mode = st.radio("Sort by", ["Highest Confidence", "Best Profit Potential", "Fastest Resolution"], horizontal=True)

        if view_mode == "Highest Confidence":
            display_markets = sorted(markets, key=lambda x: x.get('our_probability', 0), reverse=True)
        elif view_mode == "Best Profit Potential":
            display_markets = best_profit
        else:
            display_markets = sorted(markets, key=lambda x: x.get('days_to_close', 999))

        for i, market in enumerate(display_markets[:30]):
            prob = market.get('our_probability', 0)
            title = market.get('title', 'Unknown')
            ticker = market.get('ticker', '')
            position = market.get('recommended_position', 'YES')
            entry_price = market.get('entry_price', 50)
            profit_pct = market.get('profit_potential', 0)
            volume = market.get('volume', 0)
            days = market.get('days_to_close', 0)
            category = market.get('category', '')

            kelly_f = 0
            if entry_price > 0 and entry_price < 100:
                odds = 100.0 / entry_price
                kelly_f = max(0, (prob * odds - 1) / (odds - 1))
            recommended_bet = min(bankroll * kelly_f * 0.25, bankroll * 0.10)

            conf_label = "HIGH" if prob >= 0.85 else "MED" if prob >= 0.70 else "LOW"
            days_label = f"{days}d" if days > 0 else "TODAY"

            with st.expander(f"[{conf_label} {prob:.0%}] {title[:80]} | {position} @ ${entry_price/100:.2f} | +{profit_pct:.0f}% | {days_label}"):
                c1, c2, c3, c4 = st.columns(4)
                with c1:
                    st.metric("Market Consensus", f"{prob:.1%}")
                with c2:
                    st.metric("Entry Price", f"${entry_price/100:.2f}")
                with c3:
                    st.metric("Profit if Win", f"+{profit_pct:.1f}%")
                with c4:
                    st.metric("Suggested Bet", f"${recommended_bet:.2f}")

                c5, c6, c7, c8 = st.columns(4)
                with c5:
                    st.metric("Volume", f"{volume:,}")
                with c6:
                    st.metric("Days to Close", days_label)
                with c7:
                    st.metric("Category", category or "N/A")
                with c8:
                    st.metric("Position", position)

                st.caption(f"Ticker: {ticker}")
                if market.get('reasoning'):
                    st.markdown(f"**Analysis:** {market['reasoning']}")

        st.markdown("---")
        st.markdown("### Risk Management Reminders")
        st.markdown("""
        - **Quarter-Kelly sizing**: Never bet more than 1/4 of the Kelly-optimal amount
        - **Max 10% per position**: Never put more than 10% of bankroll on one trade
        - **Start small**: First few trades should be $10-25 to test the system
        - **Daily weather markets** resolve fastest but have narrower profit margins
        - **Track every trade**: Record predictions vs outcomes to calibrate confidence
        """)

with tab_alpaca:
    st.subheader("GSA Paper Trading - Stock Algorithm")

    apca_key = os.environ.get('APCA_API_KEY_ID', '')
    apca_secret = os.environ.get('APCA_API_SECRET_KEY', '')
    has_alpaca = bool(apca_key and apca_secret)

    if has_alpaca:
        st.success("Alpaca API credentials detected")
    else:
        st.warning("Add APCA_API_KEY_ID and APCA_API_SECRET_KEY to secrets.")

    st.markdown("""
    **Grand Stock Algorithm (GSA)** - TI Framework stock trading engine:
    - Xi(E) = A(t) * kappa(t,tau) * C(t) -> PD -> GILE -> Signal
    - 14 validated stocks: GOOGL, NVDA, MSFT, META, CAT, GE, GS, MS, XOM, CVX, COP, WMT, TJX
    - Quarter-Kelly position sizing
    """)

    if st.button("Generate Live GSA Signals", type="primary", use_container_width=True):
        with st.spinner("Downloading 60 days of market data and generating signals..."):
            try:
                from alpaca_paper_trader import AlpacaGSAPaperTrader
                trader = AlpacaGSAPaperTrader(paper_trading=True, initial_cash=3000)
                universe_data = trader.download_universe_data(period="60d")

                if universe_data:
                    signals = trader.generate_signals(universe_data)
                    top_signals = trader.rank_signals(signals, top_n=14)

                    st.session_state['gsa_signals'] = signals
                    st.session_state['gsa_top'] = top_signals
                    st.success(f"Generated signals for {len(signals)} stocks!")
                else:
                    st.error("Could not download market data")
            except Exception as e:
                st.error(f"Error: {str(e)}")

    if 'gsa_signals' in st.session_state:
        signals = st.session_state['gsa_signals']
        top = st.session_state.get('gsa_top', [])

        buys = {t: s for t, s in signals.items() if s['action'] in ['strong_buy', 'buy']}
        sells = {t: s for t, s in signals.items() if s['action'] in ['strong_sell', 'sell']}
        holds = {t: s for t, s in signals.items() if s['action'] == 'hold'}

        c1, c2, c3, c4 = st.columns(4)
        with c1:
            st.metric("BUY Signals", len(buys))
        with c2:
            st.metric("SELL Signals", len(sells))
        with c3:
            st.metric("HOLD Signals", len(holds))
        with c4:
            st.metric("Total Stocks", len(signals))

        if buys:
            st.markdown("### BUY Signals")
            for ticker, sig in sorted(buys.items(), key=lambda x: x[1]['gile'], reverse=True):
                st.markdown(f"**{ticker}** | {sig['action'].upper()} | GILE: {sig['gile']:.2f} | "
                           f"Confidence: {sig['confidence']:.2f} | ${sig['price']:.2f} | {sig['regime']}")

        if sells:
            st.markdown("### SELL Signals")
            for ticker, sig in sorted(sells.items(), key=lambda x: x[1]['gile']):
                st.markdown(f"**{ticker}** | {sig['action'].upper()} | GILE: {sig['gile']:.2f} | "
                           f"Confidence: {sig['confidence']:.2f} | ${sig['price']:.2f} | {sig['regime']}")

        if holds:
            st.markdown("### HOLD Signals")
            for ticker, sig in sorted(holds.items()):
                st.markdown(f"**{ticker}** | HOLD | GILE: {sig['gile']:.2f} | ${sig['price']:.2f}")

    if has_alpaca:
        st.markdown("---")
        st.markdown("### Alpaca Account Status")
        if st.button("Check Alpaca Connection"):
            try:
                from alpaca_trade_api import REST
                client = REST(
                    key_id=apca_key,
                    secret_key=apca_secret,
                    base_url='https://paper-api.alpaca.markets'
                )
                account = client.get_account()
                c1, c2, c3 = st.columns(3)
                with c1:
                    st.metric("Buying Power", f"${float(account.buying_power):,.2f}")
                with c2:
                    st.metric("Portfolio Value", f"${float(account.portfolio_value):,.2f}")
                with c3:
                    st.metric("Status", account.status)
            except Exception as e:
                st.error(f"Alpaca error: {str(e)}")

with tab_strategy:
    st.subheader("Revenue Strategy Overview")

    st.markdown("### Capital Allocation Plan")

    col1, col2 = st.columns(2)
    with col1:
        st.markdown("""
        **Personal Credit ($301 - First Premier)**
        - Kalshi prediction markets: $200
          - Start with highest-confidence daily markets
          - Compound winnings over time
        - Reserve: $101 (emergency buffer)
        """)

    with col2:
        st.markdown("""
        **Business Credit ($3,000 - Rho)**
        - Stock algorithm infrastructure: $500
          - Alpaca live trading (after paper validation)
          - API subscriptions
        - Social media launch: $500
          - Marketing contractor (Upwork, results-based)
          - Content tools (Pictory active)
        - Affiliate marketing setup: $200
        - Reserve: $1,800 (working capital)
        """)

    st.markdown("---")
    st.markdown("### Revenue Streams")

    streams = [
        ("Kalshi Prediction Markets", "Days", "$50-500/week", "Ready", "Medium"),
        ("GSA Paper Trading", "30 days", "Track record", "Ready", "None"),
        ("GSA Live Trading", "60 days", "$200-2000/mo", "After paper", "Medium"),
        ("Affiliate Marketing", "2-4 weeks", "$100-1000/mo", "Need partnerships", "Low"),
        ("Social Media Content", "1-3 months", "$500-5000/mo", "Planning", "Low"),
        ("API Licensing (TI Engine)", "3-6 months", "$1000-10000/mo", "Future", "Low"),
    ]

    for name, timeline, potential, status, risk in streams:
        with st.expander(f"{name} | {potential} | {timeline}"):
            c1, c2, c3 = st.columns(3)
            with c1:
                st.markdown(f"**Timeline:** {timeline}")
            with c2:
                st.markdown(f"**Status:** {status}")
            with c3:
                st.markdown(f"**Risk:** {risk}")

    st.markdown("---")
    st.markdown("### Social Media Plan")
    st.markdown("""
    **Platforms:** X, Instagram, LinkedIn, YouTube

    **Content:** Video via Pictory | Marketing contractor via Upwork (results-based)

    **Affiliate Products:** Katalyst EMS Suit, RedRush, health/biometric products

    **blissgene.org:** Managed externally via GoDaddy/Microsoft Outlook
    """)

    st.markdown("---")
    st.markdown("### Priority Action Items")
    st.markdown("""
    1. Scan Kalshi for first high-confidence trade
    2. Generate GSA paper trading signals, start Alpaca paper trading
    3. Place first Kalshi trades ($10-25 on 90%+ confidence markets)
    4. Set up affiliate accounts (Katalyst, RedRush)
    5. Post first marketing contractor job on Upwork
    6. Review GSA paper trading performance (30 days)
    7. If GSA positive, consider small live trades (60 days)
    """)
