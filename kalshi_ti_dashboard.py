"""
Kalshi TI Framework Dashboard
Interactive Streamlit interface for prediction market analysis using GILE

Features:
- Market discovery and filtering
- GILE-based analysis
- Trading signals with expected value
- Performance tracking
- Risk management
"""

import streamlit as st
from kalshi_ti_connector import KalshiTIConnector
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime

def render_kalshi_ti_dashboard():
    """Main Kalshi TI Framework dashboard"""
    
    st.title("🔮 Kalshi Prediction Markets × TI Framework")
    st.markdown("### GILE-Based Analysis for Exponential Wealth Generation")
    st.markdown("**Apply quantum-classical physics to prediction markets**")
    
    # Initialize connector
    if 'kalshi_connector' not in st.session_state:
        st.session_state.kalshi_connector = KalshiTIConnector()
    
    connector = st.session_state.kalshi_connector
    
    # Sidebar controls
    st.sidebar.header("⚙️ Configuration")
    
    # Authentication
    st.sidebar.markdown("### 🔐 Kalshi Authentication")
    api_key_id = st.sidebar.text_input("API Key ID:", value="", type="password", help="Get from kalshi.com")
    private_key_path = st.sidebar.text_input("Private Key Path:", value="", help="Path to your .pem file")
    
    if st.sidebar.button("🔗 Connect to Kalshi", use_container_width=True):
        if api_key_id and private_key_path:
            connector.api_key_id = api_key_id
            connector.private_key_path = private_key_path
            
            with st.spinner("Connecting to Kalshi..."):
                success = connector.authenticate()
                if success:
                    st.sidebar.success("✅ Connected!")
                else:
                    st.sidebar.error("❌ Connection failed")
        else:
            st.sidebar.warning("⚠️ Running in demo mode without credentials")
    
    # Market filters
    st.sidebar.markdown("---")
    st.sidebar.markdown("### 📊 Market Filters")
    
    num_markets = st.sidebar.slider("Markets to Analyze:", 5, 50, 10, 5)
    category = st.sidebar.selectbox("Category:", ["All", "economics", "politics", "technology", "crypto", "science"])
    category_filter = None if category == "All" else category.lower()
    
    min_ev = st.sidebar.slider("Min Expected Value:", 0.0, 0.5, 0.05, 0.01, 
                                help="Minimum EV threshold for opportunities")
    
    # Main content tabs
    tabs = st.tabs(["📈 Market Analysis", "🎯 Top Opportunities", "💰 Portfolio", "📊 Performance"])
    
    # Tab 1: Market Analysis
    with tabs[0]:
        st.header("📈 Market Analysis")
        
        # Fetch and analyze markets
        if st.button("🔍 Analyze Markets", type="primary", use_container_width=True):
            with st.spinner("Fetching and analyzing markets..."):
                markets = connector.get_markets(limit=num_markets, category=category_filter)
                analyses = connector.batch_analyze_markets(markets)
                
                st.session_state.market_analyses = analyses
                st.success(f"✅ Analyzed {len(analyses)} markets!")
        
        # Display analyses
        if 'market_analyses' in st.session_state:
            analyses = st.session_state.market_analyses
            
            # Summary metrics
            col1, col2, col3, col4 = st.columns(4)
            
            buy_yes_count = sum(1 for a in analyses if a['signal'] == 'BUY_YES')
            buy_no_count = sum(1 for a in analyses if a['signal'] == 'BUY_NO')
            hold_count = sum(1 for a in analyses if a['signal'] == 'HOLD')
            avg_gile = sum(a['adjusted_gile'] for a in analyses) / len(analyses)
            
            with col1:
                st.metric("BUY YES Signals", buy_yes_count)
            
            with col2:
                st.metric("BUY NO Signals", buy_no_count)
            
            with col3:
                st.metric("HOLD Signals", hold_count)
            
            with col4:
                st.metric("Avg GILE", f"{avg_gile:.2f}")
            
            # Market table
            st.markdown("### 📋 Market Analysis Results")
            
            for i, analysis in enumerate(analyses, 1):
                with st.expander(f"{i}. {analysis['market_title']}", expanded=(i <= 3)):
                    col1, col2, col3 = st.columns(3)
                    
                    with col1:
                        st.metric("GILE Score", f"{analysis['adjusted_gile']:.2f}")
                        st.metric("Momentum", f"{analysis['momentum']:.2f}")
                    
                    with col2:
                        signal_color = "🟢" if "BUY" in analysis['signal'] else "🟡"
                        st.metric("Signal", f"{signal_color} {analysis['signal']}")
                        st.metric("Confidence", f"{analysis['confidence']:.1%}")
                    
                    with col3:
                        ev_color = "green" if analysis['expected_value'] > 0 else "red"
                        st.metric("Expected Value", f"{analysis['expected_value']:+.2%}")
                        st.caption(f"YES Price: ${analysis['current_yes_price']:.2f}")
                        st.caption(f"NO Price: ${analysis['current_no_price']:.2f}")
                    
                    st.info(f"💡 **Reasoning:** {analysis['reasoning']}")
            
            # GILE distribution chart
            st.markdown("### 📊 GILE Distribution")
            
            fig = go.Figure()
            
            gile_values = [a['adjusted_gile'] for a in analyses]
            titles = [a['market_title'][:40] + "..." if len(a['market_title']) > 40 else a['market_title'] for a in analyses]
            
            colors = [
                'green' if a['signal'] == 'BUY_YES' else 
                'red' if a['signal'] == 'BUY_NO' else 
                'gray' 
                for a in analyses
            ]
            
            fig.add_trace(go.Bar(
                x=titles,
                y=gile_values,
                marker_color=colors,
                text=[f"{g:.2f}" for g in gile_values],
                textposition='auto',
                hovertemplate='<b>%{x}</b><br>GILE: %{y:.2f}<extra></extra>'
            ))
            
            fig.update_layout(
                title="GILE Scores by Market",
                xaxis_title="Market",
                yaxis_title="GILE Score",
                yaxis_range=[0, 1],
                height=500,
                showlegend=False
            )
            
            fig.update_xaxes(tickangle=-45)
            
            st.plotly_chart(fig, use_container_width=True)
        
        else:
            st.info("👆 Click 'Analyze Markets' to get started!")
    
    # Tab 2: Top Opportunities
    with tabs[1]:
        st.header("🎯 Top Trading Opportunities")
        
        if 'market_analyses' in st.session_state:
            analyses = st.session_state.market_analyses
            
            # Find opportunities
            opportunities = connector.get_top_opportunities(
                [a for a in analyses],  # Convert back to market format
                min_ev=min_ev
            )
            
            if opportunities:
                st.success(f"🎯 Found {len(opportunities)} opportunities with EV > {min_ev:.1%}")
                
                # Top opportunities
                for i, opp in enumerate(opportunities[:5], 1):
                    st.markdown(f"### {i}. {opp['market_title']}")
                    
                    col1, col2, col3, col4 = st.columns(4)
                    
                    with col1:
                        st.metric("Signal", opp['signal'])
                    
                    with col2:
                        st.metric("GILE", f"{opp['adjusted_gile']:.2f}")
                    
                    with col3:
                        st.metric("Confidence", f"{opp['confidence']:.1%}")
                    
                    with col4:
                        st.metric("Expected Value", f"{opp['expected_value']:+.2%}", 
                                 delta=f"+{opp['expected_value']:.2%}")
                    
                    st.info(f"💡 **Reasoning:** {opp['reasoning']}")
                    
                    # Trading action
                    if st.button(f"📊 Simulate Trade #{i}", key=f"trade_{i}"):
                        side = 'yes' if opp['signal'] == 'BUY_YES' else 'no'
                        price = opp['current_yes_price'] if side == 'yes' else opp['current_no_price']
                        
                        result = connector.place_order(
                            market_id=opp['market_id'],
                            side=side,
                            quantity=10,  # Demo quantity
                            price=price
                        )
                        
                        if result['status'] == 'simulated':
                            st.success(f"✅ Simulated: BUY {result['quantity']} {side.upper()} contracts at ${result['price']:.2f}")
                        elif result['status'] == 'placed':
                            st.success(f"✅ Order placed! ID: {result['order_id']}")
                        else:
                            st.error(f"❌ Error: {result.get('error', 'Unknown')}")
                    
                    st.markdown("---")
                
                # Expected value distribution
                st.markdown("### 📊 Expected Value Distribution")
                
                fig = px.scatter(
                    x=[o['adjusted_gile'] for o in opportunities],
                    y=[o['expected_value'] for o in opportunities],
                    size=[o['confidence'] for o in opportunities],
                    color=[o['signal'] for o in opportunities],
                    hover_name=[o['market_title'][:50] for o in opportunities],
                    labels={'x': 'GILE Score', 'y': 'Expected Value', 'color': 'Signal'},
                    title="GILE vs Expected Value"
                )
                
                fig.update_layout(height=500)
                
                st.plotly_chart(fig, use_container_width=True)
            
            else:
                st.warning(f"⚠️ No opportunities found with EV > {min_ev:.1%}. Try lowering the threshold.")
        
        else:
            st.info("👈 Go to 'Market Analysis' tab first to analyze markets!")
    
    # Tab 3: Portfolio
    with tabs[2]:
        st.header("💰 Portfolio Tracking")
        
        st.info("🚧 Coming soon: Track your positions, P&L, and ROI!")
        
        # Placeholder portfolio metrics
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric("Total Value", "$0.00")
        
        with col2:
            st.metric("Total P&L", "$0.00", delta="0%")
        
        with col3:
            st.metric("Win Rate", "0%")
        
        with col4:
            st.metric("ROI", "0%")
        
        st.markdown("### 📋 Positions")
        st.info("No active positions")
    
    # Tab 4: Performance
    with tabs[3]:
        st.header("📊 Performance Analytics")
        
        st.info("🚧 Coming soon: Historical performance, accuracy metrics, and backtesting!")
        
        # Placeholder metrics
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric("Total Predictions", "0")
        
        with col2:
            st.metric("Accuracy", "0%")
        
        with col3:
            st.metric("Sharpe Ratio", "0.00")
    
    # Footer
    st.markdown("---")
    st.markdown("""
    ### 💡 About TI Framework Prediction Markets
    
    This system applies the **GILE (Goodness, Intuition, Love, Environment) Framework** to prediction markets:
    
    - **GILE Analysis**: Convert market data → GILE scores → physics-based predictions
    - **Momentum Detection**: High volume/open interest = strong conviction
    - **Expected Value**: Calculate EV to identify profitable trades
    - **Risk Management**: Only trade when confidence exceeds thresholds
    
    **Disclaimer:** This is experimental technology combining quantum physics with finance. 
    Trade at your own risk. Past performance ≠ future results.
    """)


if __name__ == '__main__':
    render_kalshi_ti_dashboard()
