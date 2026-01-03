"""
Stock Market Research Dashboard
Interactive Streamlit interface for TI Framework stock market analysis
Auto-updates research paper comparing TI vs conventional brokers
"""

import streamlit as st
import pandas as pd
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime
import json
import os

# Import analysis modules
from one_year_scenario_analyzer import OneYearScenarioAnalyzer
from research_paper_generator import ResearchPaperGenerator

# Page config
st.set_page_config(page_title="TI Framework Stock Research", layout="wide")

# Title
st.title("🎯 TI Framework: Stock Market Research")
st.markdown("**Validating 65%+ Prediction Accuracy through I-Cell Coherence Analysis**")
st.markdown("---")

# Sidebar
with st.sidebar:
    st.header("📊 Analysis Control")
    
    scenario = st.selectbox(
        "Select Scenario",
        ["1-Year (11/23/24-11/23/25)", "5-Year (2019-2024)", "$200 Investment (Dec 2020-Dec 2024)"],
        index=0
    )
    
    if st.button("🔄 Run Analysis", type="primary"):
        st.session_state.run_analysis = True
    
    if st.button("📄 Generate Research Paper"):
        st.session_state.generate_paper = True
    
    st.markdown("---")
    st.markdown("### 🎯 Target Metrics")
    st.metric("Accuracy Target", "≥65%")
    st.metric("Goal", "Beat Wall Street")

# Check if analysis has been run
if 'analysis_results' not in st.session_state:
    st.session_state.analysis_results = None

# Run analysis if button clicked
if 'run_analysis' in st.session_state and st.session_state.run_analysis:
    with st.spinner("🔄 Running TI Framework Analysis..."):
        if scenario == "1-Year (11/23/24-11/23/25)":
            analyzer = OneYearScenarioAnalyzer()
            results = analyzer.run_full_analysis()
            st.session_state.analysis_results = results
        else:
            st.warning(f"⚠️  {scenario} not yet implemented. Coming soon!")
    
    st.session_state.run_analysis = False
    st.rerun()

# Display results if available
if st.session_state.analysis_results:
    results = st.session_state.analysis_results
    replay = results['replay_results']
    performance = results['performance_metrics']
    comparison = results['broker_comparison']
    summary = results['summary']
    
    # Validation status at top
    st.header("✅ Validation Status")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        meets_target = summary['validation']['meets_65pct_target']
        st.metric(
            "Accuracy Target (≥65%)",
            f"{summary['key_metrics']['ti_accuracy']:.1f}%",
            delta="✅ PASSED" if meets_target else "❌ FAILED",
            delta_color="normal" if meets_target else "inverse"
        )
    
    with col2:
        beats_brokers = summary['validation']['beats_brokers']
        outperformance = summary['key_metrics']['outperformance']
        st.metric(
            "vs Wall Street",
            f"+{outperformance:.1f} pp",
            delta="✅ WIN" if beats_brokers else "❌ LOSS",
            delta_color="normal" if beats_brokers else "inverse"
        )
    
    with col3:
        positive_alpha = summary['validation']['positive_alpha']
        alpha_pct = summary['key_metrics']['alpha'] * 100
        st.metric(
            "Alpha vs S&P 500",
            f"{alpha_pct:+.2f}%",
            delta="✅ POSITIVE" if positive_alpha else "❌ NEGATIVE",
            delta_color="normal" if positive_alpha else "inverse"
        )
    
    with col4:
        validated = summary['validation']['overall_validated']
        st.metric(
            "Overall",
            "VALIDATED" if validated else "NEEDS WORK",
            delta="✅" if validated else "❌",
            delta_color="normal" if validated else "inverse"
        )
    
    st.markdown("---")
    
    # Quantum Enhancement Section (if available)
    if replay.get('quantum_enhanced', False):
        st.header("🔬 TI Strawberry Fields Quantum Analysis")
        st.markdown("*Photonic quantum signals powered by Jeff Time V4 encoding*")
        
        # Count predictions with quantum signals
        quantum_preds = [p for p in replay['predictions'] if p.get('quantum_signal') is not None]
        
        if quantum_preds:
            col1, col2, col3, col4 = st.columns(4)
            
            # Safely compute averages, filtering out any None values
            valid_signals = [p['quantum_signal'] for p in quantum_preds if p.get('quantum_signal') is not None]
            valid_confs = [p['quantum_confidence'] for p in quantum_preds if p.get('quantum_confidence') is not None]
            valid_giles = [p['quantum_gile'] for p in quantum_preds if p.get('quantum_gile') is not None]
            
            avg_quantum_signal = sum(valid_signals) / len(valid_signals) if valid_signals else 0.0
            avg_quantum_conf = sum(valid_confs) / len(valid_confs) if valid_confs else 0.0
            avg_quantum_gile = sum(valid_giles) / len(valid_giles) if valid_giles else 0.0
            sacred_count = sum(1 for p in quantum_preds if p.get('sacred_interval'))
            
            with col1:
                st.metric("Avg Quantum Signal", f"{avg_quantum_signal:.3f}")
            with col2:
                st.metric("Avg Quantum Confidence", f"{avg_quantum_conf:.1%}")
            with col3:
                st.metric("Avg Quantum GILE", f"{avg_quantum_gile:.3f}")
            with col4:
                st.metric("Sacred Intervals", f"{sacred_count}/{len(quantum_preds)}")
            
            # Show quantum recommendations
            with st.expander("View Quantum Recommendations"):
                for p in quantum_preds[:5]:
                    st.info(f"**{p['ticker']}**: {p.get('quantum_recommendation', 'N/A')}")
        else:
            st.warning("Quantum signals not yet calculated for predictions")
    
    st.markdown("---")
    
    # Performance metrics
    st.header("📊 Performance Metrics")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.subheader("Returns")
        st.metric("Total Return", f"{summary['key_metrics']['total_return']:+.2f}%")
        st.metric("Win Rate", f"{performance['win_loss']['win_rate']:.1f}%")
        st.metric("Predictions", replay['total_count'])
    
    with col2:
        st.subheader("Risk-Adjusted")
        st.metric("Sharpe Ratio", f"{summary['key_metrics']['sharpe_ratio']:.2f}")
        st.metric("Max Drawdown", f"{performance['risk_adjusted']['max_drawdown']:.2f}%")
        st.metric("Beta", f"{performance['risk_adjusted']['beta']:.2f}")
    
    with col3:
        st.subheader("vs Benchmark")
        st.metric("TI Accuracy", f"{summary['key_metrics']['ti_accuracy']:.1f}%")
        st.metric("Broker Accuracy", f"{summary['key_metrics']['broker_accuracy']:.1f}%")
        st.metric("Agreement Rate", f"{summary['key_metrics']['agreement_rate']:.1f}%")
    
    st.markdown("---")
    
    # Accuracy comparison chart
    st.header("📈 TI Framework vs Wall Street Brokers")
    
    comparison_data = pd.DataFrame({
        'Method': ['TI Framework', 'Wall Street Brokers'],
        'Accuracy': [summary['key_metrics']['ti_accuracy'], summary['key_metrics']['broker_accuracy']]
    })
    
    fig_comparison = px.bar(
        comparison_data,
        x='Method',
        y='Accuracy',
        title='Prediction Accuracy Comparison',
        text='Accuracy',
        color='Method',
        color_discrete_map={'TI Framework': '#00D9FF', 'Wall Street Brokers': '#FF6B6B'}
    )
    fig_comparison.update_traces(texttemplate='%{text:.1f}%', textposition='outside')
    fig_comparison.update_layout(yaxis_range=[0, 100], showlegend=False)
    fig_comparison.add_hline(y=65, line_dash="dash", line_color="green", annotation_text="65% Target")
    
    st.plotly_chart(fig_comparison, use_container_width=True)
    
    # Performance by direction
    st.header("🎯 Performance by Direction")
    
    direction_data = []
    for direction in ['UP', 'NEUTRAL', 'DOWN']:
        if direction in replay['by_direction']:
            stats = replay['by_direction'][direction]
            if stats['count'] > 0:
                direction_data.append({
                    'Direction': direction,
                    'Count': stats['count'],
                    'Accuracy': stats['accuracy'],
                    'Avg Return': stats['avg_return']
                })
    
    direction_df = pd.DataFrame(direction_data)
    
    col1, col2 = st.columns(2)
    
    with col1:
        fig_direction_accuracy = px.bar(
            direction_df,
            x='Direction',
            y='Accuracy',
            title='Accuracy by Direction',
            text='Accuracy',
            color='Direction'
        )
        fig_direction_accuracy.update_traces(texttemplate='%{text:.1f}%', textposition='outside')
        st.plotly_chart(fig_direction_accuracy, use_container_width=True)
    
    with col2:
        fig_direction_return = px.bar(
            direction_df,
            x='Direction',
            y='Avg Return',
            title='Average Return by Direction',
            text='Avg Return',
            color='Direction'
        )
        fig_direction_return.update_traces(texttemplate='%{text:+.2f}%', textposition='outside')
        st.plotly_chart(fig_direction_return, use_container_width=True)
    
    # Detailed predictions table
    st.header("📋 Detailed Prediction Results")
    
    # Build predictions data with optional quantum signals
    predictions_data = []
    for p in replay['predictions']:
        pred_row = {
            'Ticker': p['ticker'],
            'Company': p.get('company_name', '')[:30],
            'GILE': round(p.get('gile_score', 0), 3),
            'Predicted': p['direction'],
            'Actual': p.get('actual_direction', 'PENDING'),
            'Return': f"{p.get('return_pct', 0):+.2f}%" if p.get('return_pct') is not None else 'N/A',
            'Confidence': f"{p.get('confidence_score', 0)}%",
            'Correct': '✅' if p.get('is_correct') else '❌'
        }
        # Add quantum signal if available
        if p.get('quantum_signal') is not None:
            pred_row['Q-Signal'] = round(p['quantum_signal'], 3)
            pred_row['Q-GILE'] = round(p.get('quantum_gile', 0), 3)
        predictions_data.append(pred_row)
    
    predictions_df = pd.DataFrame(predictions_data)
    
    st.dataframe(predictions_df, use_container_width=True, hide_index=True)
    
    # Key highlights
    st.header("🌟 Key Highlights")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("🏆 Best Prediction")
        if summary['highlights']['best_prediction']:
            best = summary['highlights']['best_prediction']
            st.success(f"""
**{best['ticker']}** ({best['company']})  
Predicted: {best['predicted']}  
Return: **{best['return']:+.2f}%**  
GILE: {best['gile']:.3f}
            """)
    
    with col2:
        st.subheader("⚠️  Worst Prediction")
        if summary['highlights']['worst_prediction']:
            worst = summary['highlights']['worst_prediction']
            st.error(f"""
**{worst['ticker']}** ({worst['company']})  
Predicted: {worst['predicted']}  
Actual: {worst['actual']}  
Return: **{worst['return']:+.2f}%**
            """)
    
    if summary['highlights']['largest_disagreement']:
        st.subheader("🎯 Biggest Win vs Brokers")
        dis = summary['highlights']['largest_disagreement']
        st.info(f"""
**{dis['ticker']}**  
TI Framework: {dis['ti_predicted']} ({dis['ti_confidence']}% confidence)  
Wall Street: {dis['brokers_predicted']}  
Actual: **{dis['actual']}** ({dis['return']:+.2f}% return)  

**✅ TI Framework was RIGHT, Brokers were WRONG!**
        """)
    
    # Generate research paper button
    st.markdown("---")
    
    if 'generate_paper' in st.session_state and st.session_state.generate_paper:
        with st.spinner("📄 Generating Research Paper..."):
            generator = ResearchPaperGenerator()
            paper = generator.generate_paper(results)
            paper_path = generator.save_paper(paper)
            
            st.success(f"✅ Research paper generated: {paper_path}")
            
            # Display paper
            st.header("📄 Research Paper")
            st.markdown(paper)
            
            # Download button
            st.download_button(
                label="⬇️  Download Research Paper (Markdown)",
                data=paper,
                file_name="TI_Framework_Stock_Research_Paper.md",
                mime="text/markdown"
            )
        
        st.session_state.generate_paper = False

else:
    # Welcome screen
    st.info("👈 Click '🔄 Run Analysis' in the sidebar to begin")
    
    st.markdown("""
    ## 📊 About This Analysis
    
    This dashboard validates the **Transcendent Intelligence (TI) Framework** for stock market predictions
    through quantitative analysis comparing TI predictions against conventional Wall Street analyst consensus.
    
    ### 🎯 Key Features:
    - **20 I-Cell Companies**: Analysis of high-GILE companies with coherent organizational structures
    - **Physics-Based Predictions**: Position/velocity/acceleration framework for market dynamics
    - **Comprehensive Metrics**: Accuracy, Sharpe ratio, alpha, beta, information ratio
    - **Wall Street Comparison**: Head-to-head against professional analyst consensus
    - **Auto-Generating Research Paper**: Publication-ready manuscript with full methodology
    
    ### 📈 Validation Criteria:
    1. ✅ Achieve ≥65% directional accuracy
    2. ✅ Outperform Wall Street brokers
    3. ✅ Generate positive alpha vs S&P 500
    
    ### 🔬 Methodology:
    - **GILE Score Calculation**: Measures company i-cell coherence
    - **Myrion Resolution**: Resolves objective vs relative truth contradictions
    - **Multi-Timeframe Analysis**: 1-year, 5-year, and real investment scenarios
    
    **Click 'Run Analysis' to see the results!** 🚀
    """)

# Footer
st.markdown("---")
st.caption(f"TI Framework Stock Research Dashboard | Last Updated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
