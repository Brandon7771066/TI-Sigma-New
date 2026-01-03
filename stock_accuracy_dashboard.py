"""
Stock Market Accuracy Diagnosis Dashboard
Interactive Streamlit interface for comparing GILE vs baseline strategies

Features:
- Side-by-side accuracy comparison
- Statistical significance testing
- Performance visualizations
- Publication-ready reports
"""

import streamlit as st
import json
from datetime import datetime, timedelta
from stock_accuracy_diagnosis import StockAccuracyDiagnosis
import plotly.graph_objects as go
import plotly.express as px

def render_stock_accuracy_dashboard():
    """Main dashboard for stock accuracy diagnosis"""
    
    st.title("📊 Stock Market Accuracy Diagnosis")
    st.markdown("### GILE Framework vs Traditional Strategies")
    st.markdown("**Rigorous scientific comparison with statistical baselines**")
    
    # Sidebar controls
    st.sidebar.header("🔬 Test Configuration")
    
    ticker = st.sidebar.text_input("Stock Ticker:", value="SPY", help="Use SPY for S&P 500")
    
    # Date range
    end_date = st.sidebar.date_input("End Date:", value=datetime.now())
    start_date = st.sidebar.date_input("Start Date:", value=datetime.now() - timedelta(days=730))
    
    # Company data for GILE
    st.sidebar.markdown("#### Company KPIs (for GILE)")
    revenue_growth = st.sidebar.slider("Revenue Growth:", -0.5, 1.0, 0.15, 0.05)
    profit_margin = st.sidebar.slider("Profit Margin:", -0.3, 0.5, 0.12, 0.01)
    innovation_score = st.sidebar.slider("Innovation Score:", 0.0, 1.0, 0.7, 0.1)
    
    company_data = {
        'name': ticker,
        'revenue_growth': revenue_growth,
        'profit_margin': profit_margin,
        'innovation_score': innovation_score
    }
    
    run_diagnosis = st.sidebar.button("🚀 Run Diagnosis", type="primary", use_container_width=True)
    
    # Main content
    tabs = st.tabs(["📈 Overview", "🏆 Comparison", "📊 Detailed Results", "📄 Report"])
    
    # Initialize session state
    if 'diagnosis_results' not in st.session_state:
        st.session_state.diagnosis_results = None
    
    # Run diagnosis
    if run_diagnosis:
        with st.spinner("🔬 Running comprehensive diagnosis... This may take a few minutes..."):
            try:
                diagnosis = StockAccuracyDiagnosis()
                results = diagnosis.run_comprehensive_diagnosis(
                    ticker=ticker,
                    start_date=datetime.combine(start_date, datetime.min.time()),
                    end_date=datetime.combine(end_date, datetime.min.time()),
                    company_data=company_data
                )
                st.session_state.diagnosis_results = results
                st.success("✅ Diagnosis complete!")
            except Exception as e:
                st.error(f"❌ Error running diagnosis: {e}")
                st.exception(e)
    
    results = st.session_state.diagnosis_results
    
    # Tab 1: Overview
    with tabs[0]:
        st.header("📈 Diagnosis Overview")
        
        if results:
            # Key metrics
            col1, col2, col3, col4 = st.columns(4)
            
            with col1:
                st.metric(
                    "GILE Accuracy",
                    f"{results['gile_framework']['direction_accuracy']:.1f}%",
                    delta=f"{results['gile_framework']['direction_accuracy'] - 50:.1f}% vs random"
                )
            
            with col2:
                sp500_return = results['baselines']['sp500_buyhold']['total_return_pct']
                st.metric(
                    "S&P 500 Return",
                    f"{sp500_return:+.1f}%",
                    delta="Buy & Hold"
                )
            
            with col3:
                ta_accuracy = results['baselines']['technical_analysis']['accuracy']
                st.metric(
                    "Technical Analysis",
                    f"{ta_accuracy:.1f}%",
                    delta=f"{ta_accuracy - 50:.1f}% vs random"
                )
            
            with col4:
                momentum_accuracy = results['baselines']['momentum']['accuracy']
                st.metric(
                    "Momentum Strategy",
                    f"{momentum_accuracy:.1f}%",
                    delta=f"{momentum_accuracy - 50:.1f}% vs random"
                )
            
            # Winner announcement
            st.markdown("---")
            winner = results['ranking'][0]
            st.success(f"🏆 **WINNER: {winner[0]}** with {winner[1]:.1f}% accuracy!")
            
            # Test period info
            st.info(f"📅 Test Period: {results['test_period']['start_date']} to {results['test_period']['end_date']} ({results['test_period']['days']} days)")
            
        else:
            st.info("👈 Configure test parameters in the sidebar and click **Run Diagnosis** to start!")
            
            st.markdown("""
            ### What This Tests:
            
            This comprehensive diagnosis compares **5 strategies**:
            
            1. **GILE Framework** - Your TI Framework predictions using quantum-classical physics
            2. **S&P 500 Buy-and-Hold** - Market benchmark (beats 80% of traders!)
            3. **Random 50%** - Statistical baseline (coin flip)
            4. **Technical Analysis** - Traditional RSI + MACD + Moving Averages
            5. **Momentum Strategy** - "The trend is your friend"
            
            ### Why This Matters:
            
            - If GILE beats random (50%), it has predictive power
            - If GILE beats technical analysis (~55-60%), it's better than Wall Street pros
            - If GILE beats buy-and-hold, it's market-beating alpha
            - **Above 65%** = potential for exponential wealth generation
            
            ### Scientific Rigor:
            
            ✅ **Temporal blinding** - No future data leakage  
            ✅ **Side-by-side comparison** - Same data, same period  
            ✅ **Statistical baselines** - Random chance benchmark  
            ✅ **Traditional methods** - Industry-standard indicators  
            ✅ **Transparency** - Full "show your work" logging  
            """)
    
    # Tab 2: Comparison
    with tabs[1]:
        st.header("🏆 Strategy Comparison")
        
        if results:
            # Create comparison chart
            ranking = results['ranking']
            
            fig = go.Figure()
            
            strategies = [r[0] for r in ranking]
            accuracies = [r[1] for r in ranking]
            
            # Color code: GILE = gold, others = blue/gray
            colors = ['gold' if 'GILE' in s else 'steelblue' for s in strategies]
            
            fig.add_trace(go.Bar(
                x=strategies,
                y=accuracies,
                marker_color=colors,
                text=[f"{acc:.1f}%" for acc in accuracies],
                textposition='auto',
                hovertemplate='<b>%{x}</b><br>Accuracy: %{y:.1f}%<extra></extra>'
            ))
            
            # Add 50% random baseline line
            fig.add_hline(y=50, line_dash="dash", line_color="red", 
                         annotation_text="Random Chance (50%)", annotation_position="right")
            
            # Add 65% target line
            fig.add_hline(y=65, line_dash="dash", line_color="green",
                         annotation_text="Target (65%)", annotation_position="right")
            
            fig.update_layout(
                title="Accuracy Comparison (Higher = Better)",
                xaxis_title="Strategy",
                yaxis_title="Accuracy (%)",
                yaxis_range=[0, 100],
                height=500
            )
            
            st.plotly_chart(fig, use_container_width=True)
            
            # Statistical significance
            st.markdown("### 📊 Statistical Analysis")
            
            gile_acc = results['gile_framework']['direction_accuracy']
            random_acc = results['baselines']['random_50']['avg_accuracy']
            
            # Z-test for proportion
            n = results['gile_framework']['total_predictions']
            p_gile = gile_acc / 100
            p_random = 0.5
            
            if n > 0:
                z_score = (p_gile - p_random) / ((p_random * (1 - p_random) / n) ** 0.5)
                
                # Two-tailed p-value approximation
                from math import erf
                p_value = 2 * (1 - 0.5 * (1 + erf(abs(z_score) / (2 ** 0.5))))
                
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Z-Score", f"{z_score:.2f}")
                
                with col2:
                    st.metric("P-Value", f"{p_value:.4f}")
                
                with col3:
                    significant = "YES ✅" if p_value < 0.05 else "NO ❌"
                    st.metric("Significant (p<0.05)?", significant)
                
                if p_value < 0.05:
                    st.success(f"✅ **STATISTICALLY SIGNIFICANT!** GILE predictions are significantly better than random (p = {p_value:.4f})")
                else:
                    st.warning(f"⚠️ Not statistically significant (p = {p_value:.4f}). Need more data or better accuracy.")
            
            # Comparison table
            st.markdown("### 📋 Detailed Comparison")
            
            comparison_data = []
            for strategy, accuracy in ranking:
                baseline = results['baselines']
                
                if 'GILE' in strategy:
                    data = {
                        'Strategy': strategy,
                        'Accuracy (%)': f"{accuracy:.1f}",
                        'Predictions': results['gile_framework']['total_predictions'],
                        'Beat Random?': '✅' if accuracy > 50 else '❌',
                        'Beat TA?': '✅' if accuracy > baseline['technical_analysis']['accuracy'] else '❌'
                    }
                elif 'Technical' in strategy:
                    data = {
                        'Strategy': strategy,
                        'Accuracy (%)': f"{accuracy:.1f}",
                        'Predictions': baseline['technical_analysis']['total_signals'],
                        'Beat Random?': '✅' if accuracy > 50 else '❌',
                        'Beat TA?': 'N/A'
                    }
                elif 'Momentum' in strategy:
                    data = {
                        'Strategy': strategy,
                        'Accuracy (%)': f"{accuracy:.1f}",
                        'Predictions': baseline['momentum']['total_predictions'],
                        'Beat Random?': '✅' if accuracy > 50 else '❌',
                        'Beat TA?': '✅' if accuracy > baseline['technical_analysis']['accuracy'] else '❌'
                    }
                else:
                    data = {
                        'Strategy': strategy,
                        'Accuracy (%)': f"{accuracy:.1f}",
                        'Predictions': 'N/A',
                        'Beat Random?': 'N/A',
                        'Beat TA?': 'N/A'
                    }
                
                comparison_data.append(data)
            
            st.table(comparison_data)
        
        else:
            st.info("Run diagnosis first to see comparison!")
    
    # Tab 3: Detailed Results
    with tabs[2]:
        st.header("📊 Detailed Results")
        
        if results:
            # GILE Results
            st.subheader("🔮 GILE Framework Results")
            
            gile = results['gile_framework']
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Direction Accuracy", f"{gile['direction_accuracy']:.1f}%")
            with col2:
                st.metric("Magnitude Accuracy", f"{gile['magnitude_accuracy']:.1f}%")
            with col3:
                st.metric("Total Predictions", gile['total_predictions'])
            
            # Sample predictions
            if gile.get('results'):
                st.markdown("#### Sample Predictions")
                
                sample_df = []
                for pred in gile['results'][:10]:
                    sample_df.append({
                        'Date': pred['prediction_date'],
                        'Signal': pred['prediction']['signal'],
                        'Predicted': f"{pred['prediction']['target_change_pct']:+.1f}%",
                        'Actual': f"{pred['actual']['return_pct']:+.1f}%",
                        'Correct': '✅' if pred['accuracy']['direction_correct'] else '❌',
                        'Confidence': f"{pred['prediction']['confidence']:.2f}"
                    })
                
                st.dataframe(sample_df, use_container_width=True)
            
            st.markdown("---")
            
            # Baseline results
            st.subheader("📈 Baseline Strategy Results")
            
            baselines = results['baselines']
            
            # S&P 500
            st.markdown("#### 📊 S&P 500 Buy-and-Hold")
            sp500 = baselines['sp500_buyhold']
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Total Return", f"{sp500['total_return_pct']:+.1f}%")
            with col2:
                st.metric("Annualized Return", f"{sp500['annualized_return_pct']:+.1f}%")
            with col3:
                st.metric("Max Drawdown", f"{sp500['max_drawdown_pct']:.1f}%")
            
            # Random 50%
            st.markdown("#### 🎲 Random 50% Baseline")
            random = baselines['random_50']
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Avg Accuracy", f"{random['avg_accuracy']:.1f}%")
            with col2:
                st.metric("Accuracy Range", f"{random['min_accuracy']:.1f}% - {random['max_accuracy']:.1f}%")
            with col3:
                st.metric("Simulations", random['num_simulations'])
            
            # Technical Analysis
            st.markdown("#### 📉 Technical Analysis (RSI + MACD + MA)")
            ta = baselines['technical_analysis']
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Accuracy", f"{ta['accuracy']:.1f}%")
            with col2:
                st.metric("Total Signals", ta['total_signals'])
            with col3:
                st.metric("Correct Signals", ta['correct_signals'])
            
            # Momentum
            st.markdown("#### 🚀 Momentum Strategy")
            momentum = baselines['momentum']
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Accuracy", f"{momentum['accuracy']:.1f}%")
            with col2:
                st.metric("Total Predictions", momentum['total_predictions'])
            with col3:
                st.metric("Correct Predictions", momentum['correct_predictions'])
        
        else:
            st.info("Run diagnosis first to see detailed results!")
    
    # Tab 4: Report
    with tabs[3]:
        st.header("📄 Publication-Ready Report")
        
        if results:
            # Executive Summary
            st.markdown("## Executive Summary")
            st.markdown(f"""
            **Stock Accuracy Diagnosis Report**  
            Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
            
            **Test Configuration:**
            - Ticker: {results['test_period']['ticker']}
            - Period: {results['test_period']['start_date']} to {results['test_period']['end_date']}
            - Duration: {results['test_period']['days']} days
            
            **Key Findings:**
            
            1. **GILE Framework Performance:** {results['gile_framework']['direction_accuracy']:.1f}% direction accuracy
            2. **Market Benchmark (S&P 500):** {results['baselines']['sp500_buyhold']['total_return_pct']:+.1f}% total return
            3. **Technical Analysis Baseline:** {results['baselines']['technical_analysis']['accuracy']:.1f}% accuracy
            4. **Random Baseline:** {results['baselines']['random_50']['avg_accuracy']:.1f}% accuracy (expected: 50%)
            
            **Winner:** {results['ranking'][0][0]} ({results['ranking'][0][1]:.1f}% accuracy)
            """)
            
            # Download button
            report_json = json.dumps(results, indent=2, default=str)
            st.download_button(
                label="📥 Download JSON Report",
                data=report_json,
                file_name=f"stock_diagnosis_{results['test_period']['ticker']}_{datetime.now().strftime('%Y%m%d')}.json",
                mime="application/json"
            )
            
            # Methodology
            st.markdown("---")
            st.markdown("## Methodology")
            st.markdown("""
            ### Testing Framework
            
            This diagnosis implements rigorous scientific methods to validate prediction accuracy:
            
            #### 1. Temporal Blinding
            - No future data leakage - predictions use only data available at prediction time
            - Strict enforcement of causality in backtests
            
            #### 2. Baseline Comparisons
            - **S&P 500 Buy-and-Hold**: Market benchmark
            - **Random 50%**: Statistical baseline (100 simulations)
            - **Technical Analysis**: RSI + MACD + 50-day MA
            - **Momentum Strategy**: 30-day trend continuation
            
            #### 3. Statistical Validation
            - Z-tests for proportion significance
            - P-value calculation (α = 0.05)
            - Confidence intervals
            
            #### 4. Multiple Metrics
            - Direction accuracy (UP vs DOWN)
            - Magnitude accuracy (within 5%)
            - Risk-adjusted returns (Sharpe ratio)
            - Maximum drawdown
            
            ### GILE Framework Approach
            
            The GILE (Goodness, Intuition, Love, Environment) Framework uses:
            - Company KPI analysis → GILE score
            - Historical GILE trajectory → Position, velocity, acceleration
            - Physics-based prediction engine
            - Myrion Resolution for indeterminate states
            - Market sentiment integration
            
            ### Limitations
            
            - Historical performance ≠ future results
            - Small sample sizes may lack statistical power
            - Market regime changes affect all strategies
            - Transaction costs not included
            """)
        
        else:
            st.info("Run diagnosis first to generate report!")


if __name__ == '__main__':
    render_stock_accuracy_dashboard()
