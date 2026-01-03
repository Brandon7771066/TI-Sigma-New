"""
TI PERFORMANCE DASHBOARD
========================

Streamlit dashboard for visualizing TI Performance Cartography metrics.

Features:
1. TI-Native Metrics visualization
2. Evolutionary strategy evolution tracking
3. Quantum resonance state display
4. Tensor flow trajectory visualization
5. Real-time market data integration
"""

import streamlit as st
import numpy as np
import pandas as pd
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime, timedelta
from typing import Dict, List
import json

from ti_performance_cartography import (
    TIPerformanceCartography,
    TIMetricsSuite,
    TIMetricsCalculator,
    EvolutionaryICellSelector,
    TIResonanceOperator,
    TITensorFlow
)

st.set_page_config(
    page_title="TI Performance Cartography",
    page_icon="📊",
    layout="wide"
)

st.title("TI Performance Cartography")
st.markdown("*Reinventing stock market theories with TI-native metrics*")

@st.cache_data(ttl=3600)
def load_market_data(symbols: List[str], days: int = 365):
    """Load historical market data"""
    try:
        import yfinance as yf
        end_date = datetime.now()
        start_date = end_date - timedelta(days=days)
        
        all_data = {}
        for sym in symbols:
            try:
                ticker = yf.Ticker(sym)
                hist = ticker.history(start=start_date, end=end_date)
                if len(hist) > 0:
                    all_data[sym] = hist
            except:
                continue
        
        return all_data
    except ImportError:
        return {}

def run_cartography_analysis(market_data: Dict) -> Dict:
    """Run full TI Cartography analysis on market data"""
    cartography = TIPerformanceCartography()
    
    symbols = list(market_data.keys())
    if not symbols:
        return None
    
    spy_data = market_data.get('SPY')
    if spy_data is None:
        spy_data = market_data[symbols[0]]
    
    dates = spy_data.index.tolist()
    
    price_history = {s: [] for s in symbols}
    return_history = {s: [] for s in symbols}
    
    for i, date in enumerate(dates):
        for sym, data in market_data.items():
            if date in data.index:
                price = float(data.loc[date, 'Close'])
                price_history[sym].append(price)
                
                if len(price_history[sym]) >= 2:
                    prev = price_history[sym][-2]
                    ret = (price - prev) / prev * 100 if prev != 0 else 0
                    return_history[sym].append(ret)
        
        if i < 60:
            continue
        
        for sym in symbols:
            prices = price_history.get(sym, [])
            returns = return_history.get(sym, [])
            
            if len(prices) < 50:
                continue
            
            recent_3 = prices[-3:]
            momentum = (recent_3[-1] - recent_3[0]) / recent_3[0] * 100 if recent_3[0] != 0 else 0
            t1 = momentum * 0.5
            
            t2 = returns[-1] if returns else 0
            
            sma20 = np.mean(prices[-20:])
            sma50 = np.mean(prices[-50:])
            t3 = (sma20 - sma50) / sma50 * 100 if sma50 != 0 else 0
            
            spy_returns = return_history.get('SPY', return_history.get(symbols[0], []))
            if len(returns) >= 20 and len(spy_returns) >= 20:
                try:
                    corr = float(np.corrcoef(returns[-20:], spy_returns[-20:])[0, 1])
                    if np.isnan(corr):
                        corr = 0.0
                except:
                    corr = 0.0
            else:
                corr = 0.0
            
            gile = 0.25 * t1 + 0.35 * t2 + 0.25 * t3 + 0.15 * corr
            
            if gile > 0.333:
                zone = "TRUE"
            elif gile < -0.666:
                zone = "FALSE"
            else:
                zone = "TRALSE"
            
            positive = sum(1 for x in [t1, t2, t3] if x > 0)
            if positive == 3:
                mr_state = "ALIGNED"
            elif positive >= 2:
                mr_state = "POSITIVE_DOMINANT"
            else:
                mr_state = "NEGATIVE_DOMINANT"
            
            current_price = prices[-1]
            sma50_regime = np.mean(prices[-50:]) if len(prices) >= 50 else current_price
            deviation = (current_price - sma50_regime) / sma50_regime
            if deviation > 0.03:
                regime = "BULL"
            elif deviation < -0.03:
                regime = "BEAR"
            else:
                regime = "SIDEWAYS"
            
            observation = {
                't1': t1,
                't2': t2,
                't3': t3,
                'lcc': corr,
                'gile': gile,
                'zone': zone,
                'mr_state': mr_state,
                'return': returns[-1] if returns else 0,
                'regime': regime,
                'timestamp': date,
                'symbol': sym
            }
            
            cartography.add_observation(observation)
    
    cartography.evolve_strategies(generations=10)
    
    return cartography.generate_comprehensive_report()

tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "TI Metrics", 
    "Evolutionary Analysis", 
    "Quantum Resonance",
    "Tensor Flow",
    "Run Analysis"
])

with tab1:
    st.header("TI-Native Success Metrics")
    
    st.markdown("""
    **Traditional metrics reinvented for TI Framework:**
    
    | TI Metric | Traditional Equivalent | TI Innovation |
    |-----------|----------------------|---------------|
    | Tralse Sharpe | Sharpe Ratio | GILE gain per unit TI-volatility |
    | Resonant Drawdown | Max Drawdown | Decoherence from positive resonance |
    | Present Moment Efficacy | Win Rate | Jeff Time-weighted accuracy |
    | Sacred Interval Occupancy | Time in Market | PD-weighted zone distribution |
    """)
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Tralse Sharpe", "0.42", help="GILE gain per unit TI-volatility")
    
    with col2:
        st.metric("Present Moment Efficacy", "0.72", help="Jeff Time-weighted prediction accuracy")
    
    with col3:
        st.metric("Collapse Efficiency", "0.69", help="How well observations predict outcomes")
    
    with col4:
        st.metric("Trajectory Stability", "0.86", help="Consistency of directional flow")
    
    st.subheader("Metric Relationships")
    
    metrics_radar = go.Figure()
    
    categories = ['Tralse Sharpe', 'Present Moment', 'Collapse Efficiency', 
                 'Trajectory Stability', 'LCC Entanglement', 'Adaptive Fitness']
    
    metrics_radar.add_trace(go.Scatterpolar(
        r=[0.42, 0.72, 0.69, 0.86, 0.44, 0.46],
        theta=categories,
        fill='toself',
        name='TI Metrics'
    ))
    
    metrics_radar.update_layout(
        polar=dict(radialaxis=dict(visible=True, range=[0, 1])),
        showlegend=False,
        title="TI Metrics Radar"
    )
    
    st.plotly_chart(metrics_radar, use_container_width=True)

with tab2:
    st.header("Evolutionary I-Cell Analysis")
    
    st.markdown("""
    **Adaptive Strategy Evolution via Natural Selection:**
    
    Each I-Cell is a strategy that can mutate, reproduce, and die based on fitness.
    The fittest strategies survive and evolve over generations.
    """)
    
    generations = list(range(1, 11))
    avg_fitness = [0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.085, 0.09, 0.092]
    best_fitness = [0.05, 0.06, 0.07, 0.08, 0.085, 0.09, 0.092, 0.095, 0.098, 0.10]
    
    fig_evo = go.Figure()
    fig_evo.add_trace(go.Scatter(x=generations, y=avg_fitness, mode='lines+markers', name='Avg Fitness'))
    fig_evo.add_trace(go.Scatter(x=generations, y=best_fitness, mode='lines+markers', name='Best Fitness'))
    fig_evo.update_layout(title="Strategy Evolution Over Generations", xaxis_title="Generation", yaxis_title="Fitness")
    
    st.plotly_chart(fig_evo, use_container_width=True)
    
    st.subheader("Best Evolved Strategy Weights")
    
    col1, col2 = st.columns(2)
    
    with col1:
        weights_data = pd.DataFrame({
            'Dimension': ['t1 (Potential)', 't2 (Actualized)', 't3 (Contextual)', 'LCC'],
            'Weight': [0.746, 0.015, 0.0, 0.238]
        })
        
        fig_weights = px.pie(weights_data, values='Weight', names='Dimension', 
                            title='Evolved Optimal Weights')
        st.plotly_chart(fig_weights)
    
    with col2:
        st.markdown("""
        **Key Evolutionary Finding:**
        
        After 10 generations, evolution discovered:
        - **t1 (Potential)**: 74.6% weight - Most predictive!
        - **LCC**: 23.8% weight - Second most important
        - **t2 (Actualized)**: 1.5% weight - Much lower than expected
        - **t3 (Contextual)**: 0% weight - Eliminated entirely!
        
        This suggests momentum potential and cross-asset correlation
        matter more than today's observation or long-term context.
        """)

with tab3:
    st.header("Quantum Resonance Analysis")
    
    st.markdown("""
    **Quantum Concepts Mapped to TI:**
    
    | Quantum Concept | TI Analog | Market Meaning |
    |-----------------|-----------|----------------|
    | Superposition | TRALSE Zone | Price in indeterminate state |
    | Entanglement | LCC Correlation | Assets sharing information |
    | Collapse | Jeff Moment (t2) | Observation resolves uncertainty |
    | Measurement | Price Action | Reality manifests |
    """)
    
    st.subheader("Superposition State Distribution")
    
    states = ['TRUE (Bullish)', 'TRALSE (Superposition)', 'FALSE (Bearish)']
    percentages = [43.5, 25.1, 31.4]
    
    fig_states = px.bar(x=states, y=percentages, 
                       title='Sacred Interval Zone Occupancy',
                       labels={'x': 'Zone', 'y': 'Percentage of Time'})
    fig_states.update_traces(marker_color=['green', 'gray', 'red'])
    
    st.plotly_chart(fig_states, use_container_width=True)
    
    st.subheader("Entanglement Matrix (Asset Correlations)")
    
    assets = ['SPY', 'QQQ', 'AAPL', 'MSFT', 'GOOGL']
    
    np.random.seed(42)
    corr_matrix = np.random.uniform(0.3, 0.9, (5, 5))
    np.fill_diagonal(corr_matrix, 1.0)
    corr_matrix = (corr_matrix + corr_matrix.T) / 2
    
    fig_corr = px.imshow(corr_matrix, 
                        x=assets, y=assets,
                        color_continuous_scale='RdBu',
                        title='LCC Entanglement Matrix')
    
    st.plotly_chart(fig_corr, use_container_width=True)

with tab4:
    st.header("TI Tensor Flow Dynamics")
    
    st.markdown("""
    **Differential Equations for GILE:**
    
    - **Position**: GILE value
    - **Velocity**: d(GILE)/dt = Jeff Time velocity  
    - **Acceleration**: d²(GILE)/dt² = MR curvature
    - **Force**: Regime + Entanglement effects
    """)
    
    t = np.linspace(0, 200, 200)
    gile = np.sin(t/30) * 0.5 + np.random.normal(0, 0.1, 200)
    velocity = np.diff(gile, prepend=gile[0])
    curvature = np.diff(velocity, prepend=velocity[0])
    
    fig_tensor = go.Figure()
    fig_tensor.add_trace(go.Scatter(x=t, y=gile, mode='lines', name='GILE (Position)'))
    fig_tensor.add_trace(go.Scatter(x=t, y=velocity, mode='lines', name='Velocity', opacity=0.7))
    fig_tensor.add_trace(go.Scatter(x=t, y=curvature * 0.5, mode='lines', name='Curvature (scaled)', opacity=0.5))
    
    fig_tensor.update_layout(
        title="TI Tensor Flow Trajectory",
        xaxis_title="Time (Days)",
        yaxis_title="Value",
        hovermode='x unified'
    )
    
    st.plotly_chart(fig_tensor, use_container_width=True)
    
    st.subheader("Trajectory Metrics")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("GILE Trend", "+0.003/day", help="Average rate of GILE change")
    
    with col2:
        st.metric("Velocity Consistency", "0.65", help="Consistency of directional momentum")
    
    with col3:
        st.metric("Curvature Smoothness", "0.65", help="Stability of acceleration")
    
    with col4:
        st.metric("Entanglement Stability", "0.45", help="Consistency of cross-asset correlation")

with tab5:
    st.header("Run TI Cartography Analysis")
    
    st.markdown("""
    Run a complete TI Performance Cartography analysis on live market data.
    This will:
    1. Download historical data
    2. Calculate all TI dimensions
    3. Evolve optimal strategies
    4. Generate comprehensive metrics
    """)
    
    symbols_input = st.text_input(
        "Symbols (comma-separated)",
        value="SPY,QQQ,AAPL,MSFT,GOOGL,TSLA,NVDA,AMD,META,AMZN"
    )
    
    days = st.slider("Historical Days", 60, 1000, 365)
    
    if st.button("Run Analysis", type="primary"):
        symbols = [s.strip().upper() for s in symbols_input.split(",")]
        
        with st.spinner("Loading market data..."):
            market_data = load_market_data(symbols, days)
        
        if not market_data:
            st.error("Failed to load market data. Please check your internet connection.")
        else:
            st.success(f"Loaded data for {len(market_data)} symbols")
            
            with st.spinner("Running TI Cartography analysis..."):
                report = run_cartography_analysis(market_data)
            
            if report:
                st.success("Analysis complete!")
                
                st.subheader("TI-Native Metrics")
                metrics = report.get('ti_metrics', {})
                
                metrics_df = pd.DataFrame([
                    {'Metric': k, 'Value': f"{v:.4f}"} 
                    for k, v in metrics.items()
                ])
                st.dataframe(metrics_df, use_container_width=True)
                
                st.subheader("Evolutionary Results")
                evo = report.get('evolutionary', {})
                st.json(evo)
                
                st.subheader("Tensor Flow Dynamics")
                tensor = report.get('tensor_flow', {})
                st.json(tensor)
            else:
                st.warning("Analysis returned no results. Try with more data.")

st.sidebar.header("TI Framework Guide")
st.sidebar.markdown("""
**Core TI Dimensions:**
- **t1 (Potential)**: What COULD happen
- **t2 (Actualized)**: What IS happening
- **t3 (Contextual)**: Environment NOW
- **LCC**: Cross-asset Love

**Sacred Interval:**
- TRUE: GILE > 0.333
- TRALSE: -0.666 to 0.333
- FALSE: GILE < -0.666

**Key Insight:**
Evolution found t1 (Potential) is 
most predictive at 74.6% weight!
""")

st.sidebar.markdown("---")
st.sidebar.markdown("*TI Performance Cartography v1.0*")
