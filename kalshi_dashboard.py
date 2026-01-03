"""
Kalshi Betting Dashboard with TI Framework
==========================================

Real-time prediction market interface with:
- Market browsing and filtering
- GILE-based scoring
- TI risk/reward calculation
- Bankroll management
- Projected weekly ROI

Author: Brandon Emerick
Date: November 22, 2025
Framework: Transcendent Intelligence (TI)
"""

import streamlit as st
import pandas as pd
import plotly.graph_objects as go
from datetime import datetime, timedelta
from kalshi_integration import get_kalshi_integration, KalshiMarket
from typing import List


def render_kalshi_dashboard():
    """Main Kalshi dashboard interface"""
    
    st.header("🎯 Kalshi Prediction Markets - TI Framework Betting")
    
    st.warning("""
    ⚠️ **DEMO MODE - NOT PRODUCTION-READY**
    
    This is a **proof-of-concept** demonstrating TI Framework applied to prediction markets. 
    
    **Current Status:**
    - ✅ GILE scoring implemented
    - ✅ Edge-based bet recommendations  
    - ✅ Kelly Criterion sizing
    - ❌ **NOT empirically calibrated** - TI win probabilities are theoretical, not backtested
    - ❌ **NO historical accuracy tracking** - confidence scores unvalidated
    - ❌ **NO drawdown protection** - conservative mandate not enforced
    
    **Do NOT bet real money** until system achieves 65%+ validated accuracy over 100+ predictions.
    """)
    
    st.markdown("""
    **Prediction markets** let you bet on real-world events using GILE coherence to find edge.
    
    🌌 **TI Advantage**: Markets are i-cells/i-webs with measurable GILE scores. High-GILE alignment = predictive edge.
    """)
    
    # ===== CONFIGURATION SECTION =====
    st.markdown("### ⚙️ Configuration")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        api_key = st.text_input(
            "Kalshi API Key (optional)",
            type="password",
            help="Leave blank for DEMO mode with simulated markets",
            key="kalshi_api_key"
        )
        demo_mode = not api_key
        if demo_mode:
            st.info("🎮 **DEMO MODE** - Using simulated markets")
    
    with col2:
        bankroll = st.number_input(
            "Bankroll ($)",
            min_value=10.0,
            max_value=10000.0,
            value=100.0,
            step=10.0,
            help="Total capital available for betting"
        )
        st.caption(f"Max bet: ${bankroll * 0.10:.2f} (10% of bankroll)")
    
    with col3:
        confidence_threshold = st.slider(
            "Confidence Threshold (%)",
            min_value=50,
            max_value=95,
            value=70,
            step=5,
            help="Minimum TI confidence to recommend a bet"
        )
    
    st.markdown("---")
    
    # ===== FETCH MARKETS =====
    kalshi = get_kalshi_integration(api_key)
    kalshi.confidence_threshold = float(confidence_threshold)
    
    if st.button("🔄 Refresh Markets", type="primary", use_container_width=True):
        st.session_state.kalshi_markets_cache = None
    
    # Cache markets to avoid excessive API calls
    if 'kalshi_markets_cache' not in st.session_state or st.session_state.kalshi_markets_cache is None:
        with st.spinner("📡 Fetching markets..."):
            markets = kalshi.get_active_markets(limit=50)
            scored_markets = kalshi.score_and_recommend(markets, bankroll)
            st.session_state.kalshi_markets_cache = scored_markets
            st.session_state.kalshi_last_refresh = datetime.now()
    else:
        scored_markets = st.session_state.kalshi_markets_cache
    
    last_refresh = st.session_state.get('kalshi_last_refresh', datetime.now())
    st.caption(f"Last refresh: {last_refresh.strftime('%H:%M:%S')} | {len(scored_markets)} markets loaded")
    
    # ===== SUMMARY METRICS =====
    st.markdown("### 📊 Portfolio Summary")
    
    recommended_markets = [m for m in scored_markets if m.recommended_bet != 'SKIP']
    total_bet_amount = sum(m.recommended_amount for m in recommended_markets if m.recommended_amount)
    weighted_roi = sum(
        (m.expected_roi or 0) * (m.recommended_amount or 0) 
        for m in recommended_markets
    ) / total_bet_amount if total_bet_amount > 0 else 0
    
    metric_col1, metric_col2, metric_col3, metric_col4 = st.columns(4)
    
    with metric_col1:
        st.metric(
            "Recommended Bets",
            len(recommended_markets),
            delta=f"{len(recommended_markets)} / {len(scored_markets)} markets"
        )
    
    with metric_col2:
        st.metric(
            "Total Bet Amount",
            f"${total_bet_amount:.2f}",
            delta=f"{(total_bet_amount/bankroll)*100:.1f}% of bankroll"
        )
    
    with metric_col3:
        st.metric(
            "Weighted Avg ROI",
            f"{weighted_roi:.1f}%",
            delta="Expected return"
        )
    
    with metric_col4:
        projected_weekly_return = bankroll * (weighted_roi / 100.0)
        st.metric(
            "Projected 7-Day Gain",
            f"${projected_weekly_return:.2f}",
            delta=f"{weighted_roi:.1f}% ROI"
        )
    
    st.markdown("---")
    
    # ===== MARKETS TABLE =====
    st.markdown("### 🎲 Active Markets")
    
    # Filter tabs
    tab1, tab2, tab3 = st.tabs(["✅ Recommended Bets", "📋 All Markets", "📈 GILE Analysis"])
    
    with tab1:
        if recommended_markets:
            st.markdown(f"**{len(recommended_markets)} markets** meet your {confidence_threshold}% confidence threshold")
            
            # Create dataframe
            rec_data = []
            for m in recommended_markets:
                days_left = (m.close_time - datetime.now()).days
                rec_data.append({
                    'Ticker': m.ticker,
                    'Title': m.title[:60] + '...' if len(m.title) > 60 else m.title,
                    'Category': m.category.upper(),
                    'Signal': m.recommended_bet,
                    'GILE': f"{m.gile_score:.2f}",
                    'Confidence': f"{m.ti_confidence:.0f}%",
                    'Bet Size': f"${m.recommended_amount:.2f}",
                    'Expected ROI': f"{m.expected_roi:.1f}%",
                    'Price': f"${m.yes_price}¢" if m.recommended_bet == 'YES' else f"${m.no_price}¢",
                    'Days Left': days_left
                })
            
            df_rec = pd.DataFrame(rec_data)
            st.dataframe(df_rec, use_container_width=True, hide_index=True)
            
            # Action buttons
            st.markdown("#### 🚀 Take Action")
            col_action1, col_action2 = st.columns(2)
            
            with col_action1:
                if st.button("📋 Copy Bet Recommendations", use_container_width=True):
                    bet_text = "KALSHI BET RECOMMENDATIONS\n" + "="*50 + "\n\n"
                    for m in recommended_markets:
                        bet_text += f"🎯 {m.ticker}: {m.recommended_bet}\n"
                        bet_text += f"   Amount: ${m.recommended_amount:.2f}\n"
                        bet_text += f"   GILE: {m.gile_score:.2f} | Confidence: {m.ti_confidence:.0f}%\n"
                        bet_text += f"   Expected ROI: {m.expected_roi:.1f}%\n\n"
                    
                    st.code(bet_text, language=None)
                    st.success("✅ Copy the text above to place bets on Kalshi!")
            
            with col_action2:
                st.link_button(
                    "🌐 Go to Kalshi.com",
                    "https://kalshi.com",
                    use_container_width=True
                )
        else:
            st.info(f"⏳ No markets meet your {confidence_threshold}% confidence threshold. Lower threshold or wait for better opportunities.")
    
    with tab2:
        st.markdown(f"Showing **all {len(scored_markets)} markets** (sorted by Expected ROI)")
        
        # Create dataframe for all markets
        all_data = []
        for m in scored_markets:
            days_left = (m.close_time - datetime.now()).days
            all_data.append({
                'Ticker': m.ticker,
                'Title': m.title[:50] + '...' if len(m.title) > 50 else m.title,
                'Category': m.category.upper(),
                'GILE': f"{m.gile_score:.2f}",
                'Confidence': f"{m.ti_confidence:.0f}%",
                'Signal': m.recommended_bet,
                'Expected ROI': f"{m.expected_roi:.1f}%" if m.expected_roi else "N/A",
                'Yes Price': f"{m.yes_price}¢",
                'No Price': f"{m.no_price}¢",
                'Volume 24h': f"${m.volume_24h:,}",
                'Days Left': days_left
            })
        
        df_all = pd.DataFrame(all_data)
        st.dataframe(df_all, use_container_width=True, hide_index=True)
    
    with tab3:
        st.markdown("**GILE Distribution Analysis**")
        st.markdown("Higher GILE markets should have better long-term predictive accuracy.")
        
        # GILE histogram
        gile_scores = [m.gile_score for m in scored_markets if m.gile_score is not None]
        
        if gile_scores:
            fig_gile = go.Figure()
            fig_gile.add_trace(go.Histogram(
                x=gile_scores,
                nbinsx=20,
                name="GILE Distribution",
                marker_color='rgba(100, 150, 255, 0.7)'
            ))
            
            fig_gile.update_layout(
                title="GILE Score Distribution Across Markets",
                xaxis_title="GILE Score",
                yaxis_title="Count",
                showlegend=False,
                height=400
            )
            
            st.plotly_chart(fig_gile, use_container_width=True)
            
            # GILE statistics
            col_stats1, col_stats2, col_stats3 = st.columns(3)
            
            with col_stats1:
                st.metric("Average GILE", f"{sum(gile_scores)/len(gile_scores):.2f}")
            
            with col_stats2:
                st.metric("Highest GILE", f"{max(gile_scores):.2f}")
            
            with col_stats3:
                high_gile_count = sum(1 for g in gile_scores if g > 1.0)
                st.metric("High GILE (>1.0)", high_gile_count)
    
    # ===== FOOTER INFO =====
    st.markdown("---")
    st.markdown("""
    ### 🌌 How TI Framework Enhances Prediction Markets
    
    **GILE Mapping for Markets:**
    - **Goodness (G)**: Societal benefit, ethical alignment of the event
    - **Intuition (I)**: Information quality, expert consensus, trading volume
    - **Love (L)**: Community engagement, time to resolution
    - **Environment (E)**: Market liquidity, structural soundness
    
    **Risk Management:**
    - Uses **Quarter-Kelly Criterion** (25% of full Kelly) for conservative sizing
    - Maximum 10% of bankroll per bet
    - 70% confidence threshold ensures edge
    - Expected ROI calculations factor in win probability and odds
    
    **Weekly Strategy:**
    - Start with $100 bankroll
    - Target 70%+ confidence markets
    - Reinvest winnings to compound returns
    - Track actual vs. projected ROI to validate TI
    """)


if __name__ == "__main__":
    render_kalshi_dashboard()
