"""
Historical Stock Market Backtesting Dashboard
Test TI Framework predictions against known outcomes with full transparency
"""

import streamlit as st
from datetime import datetime, timedelta
from historical_stock_backtester import HistoricalStockBacktester
from db_utils import db
import pandas as pd
import json

def render_backtest_dashboard():
    """
    Render the historical backtesting dashboard
    """
    st.title("🔬 Historical Stock Market Backtesting")
    st.markdown("### Test TI Framework Against Known Outcomes")
    
    st.info("""
    **🎯 SCIENTIFIC VALIDATION VIA BACKTESTING**
    
    This system tests our physics-based prediction engine on historical stock data with:
    - **Temporal Blinding**: Bots only see data available at prediction time (no future leakage)
    - **Show Your Work**: Full transparency logging for each prediction step
    - **Parameter Tuning**: Adjust GILE weights based on backtest results
    - **Multiple Time Periods**: Test across different market regimes (2020 pandemic, 2024 bull market, etc.)
    
    **Goal**: Validate 65%+ accuracy to prove TI Framework superiority over classical economics!
    """)
    
    # ========== BACKTEST CONFIGURATION ==========
    st.markdown("---")
    st.subheader("⚙️ Backtest Configuration")
    
    col1, col2 = st.columns(2)
    
    with col1:
        # Time period selector
        st.markdown("**📅 Time Period**")
        
        time_period = st.selectbox(
            "Select Historical Period",
            options=[
                'custom',
                '2025_ytd',
                '2024_recent',
                '2024_full',
                '2020_pandemic',
                '2021_recovery',
                '2022_correction',
                '2023_ai_boom'
            ],
            format_func=lambda x: {
                'custom': '🔧 Custom Date Range',
                '2025_ytd': '📅 2025 Year-to-Date (Jan 1 - Nov 22)',
                '2024_recent': '📊 Recent 2024 (Nov 22 - Dec 31)',
                '2024_full': '📈 Full 2024 Year',
                '2020_pandemic': '😷 2020 Pandemic Crash & Recovery',
                '2021_recovery': '🚀 2021 Post-Pandemic Bull Run',
                '2022_correction': '📉 2022 Market Correction',
                '2023_ai_boom': '🤖 2023 AI Boom (ChatGPT Era)'
            }[x]
        )
        
        # Set date ranges based on selection
        if time_period == 'custom':
            start_date = st.date_input("Start Date", value=datetime(2024, 1, 1))
            end_date = st.date_input("End Date", value=datetime(2024, 11, 22))
        elif time_period == '2025_ytd':
            start_date = datetime(2025, 1, 1)
            end_date = datetime(2025, 11, 22)
        elif time_period == '2024_recent':
            start_date = datetime(2024, 11, 22)
            end_date = datetime(2024, 12, 31)
        elif time_period == '2024_full':
            start_date = datetime(2024, 1, 1)
            end_date = datetime(2024, 12, 31)
        elif time_period == '2020_pandemic':
            start_date = datetime(2020, 1, 1)
            end_date = datetime(2020, 12, 31)
        elif time_period == '2021_recovery':
            start_date = datetime(2021, 1, 1)
            end_date = datetime(2021, 12, 31)
        elif time_period == '2022_correction':
            start_date = datetime(2022, 1, 1)
            end_date = datetime(2022, 12, 31)
        elif time_period == '2023_ai_boom':
            start_date = datetime(2023, 1, 1)
            end_date = datetime(2023, 12, 31)
        else:
            start_date = datetime(2024, 1, 1)
            end_date = datetime(2024, 11, 22)
        
        if time_period != 'custom':
            st.info(f"**Date Range:** {start_date.strftime('%Y-%m-%d')} to {end_date.strftime('%Y-%m-%d')}")
    
    with col2:
        st.markdown("**⚙️ Prediction Settings**")
        
        prediction_window = st.selectbox(
            "Prediction Window",
            options=['weekly_start', 'weekly_end', 'monthly'],
            format_func=lambda x: {
                'weekly_start': '📅 Weekly Start (Monday)',
                'weekly_end': '📅 Weekly End (Friday)',
                'monthly': '📆 Monthly (30 days)'
            }[x]
        )
        
        frequency_days = st.number_input(
            "Prediction Frequency (days)",
            min_value=1,
            max_value=30,
            value=7,
            help="How often to generate new predictions (e.g., 7 for weekly)"
        )
        
        max_tickers = st.slider(
            "Number of Stocks to Test",
            min_value=1,
            max_value=20,
            value=5,
            help="Test top N stocks from i-cell companies"
        )
    
    # ========== TICKER SELECTION ==========
    st.markdown("---")
    st.subheader("📊 Stock Selection")
    
    # Get i-cell companies
    companies = db.get_all_companies(limit=20)
    
    if not companies:
        st.warning("⚠️ No i-cell companies found. Please seed companies first.")
        return
    
    st.success(f"**{len(companies)} i-cell companies available for backtesting**")
    
    # Show top companies
    selected_tickers = [c['ticker'] for c in companies[:max_tickers]]
    
    company_df = pd.DataFrame([
        {
            'Ticker': c['ticker'],
            'Company': c.get('name', c.get('company_name', 'Unknown')),
            'Sector': c.get('sector', 'Unknown'),
            'GILE': c.get('gile_score', 0.5),
            'Coherence': c.get('coherence_score', 0.0)
        }
        for c in companies[:max_tickers]
    ])
    
    st.dataframe(company_df, use_container_width=True)
    
    # ========== RUN BACKTEST ==========
    st.markdown("---")
    
    if st.button("🚀 RUN HISTORICAL BACKTEST", type="primary", use_container_width=True):
        # Initialize backtester
        backtester = HistoricalStockBacktester()
        
        # Prepare company data map
        company_data_map = {}
        for company in companies[:max_tickers]:
            ticker = company['ticker']
            company_data_map[ticker] = {
                'employee_sentiment': company.get('employee_sentiment', 0.7),
                'debt_to_equity': company.get('debt_to_equity', 0.5),
                'esg_score': company.get('esg_score', 0.6),
                'product_launch_rate': company.get('product_launch_rate', 0.5),
                'rd_intensity': company.get('rd_intensity', 0.5),
                'market_beta': company.get('market_beta', 1.0),
                'customer_nps': company.get('customer_nps', 0.7),
                'retention_rate': company.get('retention_rate', 0.75),
                'market_share_trend': company.get('market_share_trend', 0.6),
                'sector_momentum': company.get('sector_momentum', 0.6),
                'revenue_velocity': company.get('revenue_velocity', 0.65)
            }
        
        # Run backtest
        with st.spinner(f"🔬 Running backtest from {start_date.strftime('%Y-%m-%d')} to {end_date.strftime('%Y-%m-%d')}..."):
            results = backtester.run_multi_ticker_backtest(
                tickers=selected_tickers,
                company_data_map=company_data_map,
                start_date=start_date,
                end_date=end_date,
                prediction_window=prediction_window,
                frequency_days=frequency_days
            )
        
        if not results:
            st.error("❌ Backtest failed - no results generated")
            return
        
        # Calculate accuracy metrics
        accuracy_stats = backtester.calculate_backtest_accuracy(results)
        
        # ========== DISPLAY RESULTS ==========
        st.markdown("---")
        st.markdown("## 📊 BACKTEST RESULTS")
        
        # Overall metrics
        st.subheader("🎯 Overall Accuracy")
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            direction_acc = accuracy_stats['direction_accuracy']
            delta_color = "normal" if direction_acc >= 65 else "inverse"
            st.metric(
                "Direction Accuracy",
                f"{direction_acc:.1f}%",
                delta=f"{direction_acc - 65:.1f}% vs target",
                delta_color=delta_color
            )
        
        with col2:
            st.metric(
                "Total Predictions",
                accuracy_stats['total_predictions']
            )
        
        with col3:
            st.metric(
                "Magnitude Accuracy",
                f"{accuracy_stats['magnitude_accuracy']:.1f}%",
                help="% within 5% of predicted magnitude"
            )
        
        with col4:
            st.metric(
                "Avg Error",
                f"{accuracy_stats['avg_magnitude_error']:.1f}%",
                help="Average magnitude error"
            )
        
        # Target achievement
        if accuracy_stats['target_achieved']:
            st.success("🎉 **TARGET ACHIEVED!** Direction accuracy ≥65% - TI Framework validated!")
        else:
            st.warning(f"⚠️ **Target not met** - Need to iterate GILE parameters. Current: {direction_acc:.1f}%, Target: 65%")
        
        # ========== ACCURACY BY RESOLUTION TYPE ==========
        st.markdown("---")
        st.subheader("🔮 Accuracy by Myrion Resolution Type")
        
        resolution_stats = accuracy_stats['by_resolution_type']
        
        resolution_df = pd.DataFrame([
            {
                'Resolution Type': rtype.upper(),
                'Predictions': stats['total'],
                'Accuracy': f"{stats['accuracy']:.1f}%"
            }
            for rtype, stats in resolution_stats.items()
        ])
        
        st.dataframe(resolution_df, use_container_width=True)
        
        st.info("""
        **📝 Interpretation:**
        - **OBJECTIVE**: Fundamentals trump sentiment - best when company is undervalued
        - **RELATIVE**: Market sentiment trump fundamentals - good for momentum plays
        - **INDETERMINATE**: True contradictions - requires deeper analysis
        - **ALIGNED**: No conflict - highest confidence predictions
        """)
        
        # ========== DETAILED RESULTS TABLE ==========
        st.markdown("---")
        st.subheader("📋 All Predictions with Work Logs")
        
        # Create results dataframe
        results_data = []
        for r in results:
            results_data.append({
                'Date': r['prediction_date'],
                'Ticker': r['ticker'],
                'Signal': r['prediction']['signal'],
                'Predicted': f"{r['prediction']['target_change_pct']:+.1f}%",
                'Actual': f"{r['actual']['return_pct']:+.1f}%",
                'Correct': '✅' if r['accuracy']['direction_correct'] else '❌',
                'Error': f"{r['accuracy']['magnitude_error']:.1f}%",
                'MR Type': r['prediction']['mr_resolution'],
                'Confidence': f"{r['prediction']['confidence']*100:.0f}%"
            })
        
        results_df = pd.DataFrame(results_data)
        st.dataframe(results_df, use_container_width=True)
        
        # ========== WORK LOGS (SHOW YOUR WORK) ==========
        st.markdown("---")
        st.subheader("🔍 'Show Your Work' - Detailed Prediction Logs")
        
        st.info("**Full transparency**: See exactly what data was available and how predictions were generated")
        
        # Show work logs for select predictions
        num_to_show = min(5, len(results))
        st.markdown(f"**Showing detailed work logs for first {num_to_show} predictions:**")
        
        for i, result in enumerate(results[:num_to_show]):
            with st.expander(
                f"📝 {result['ticker']} on {result['prediction_date']} - {result['prediction']['signal']}" + 
                (" ✅ CORRECT" if result['accuracy']['direction_correct'] else " ❌ WRONG"),
                expanded=(i == 0)
            ):
                work_log = result.get('work_log')
                
                if not work_log:
                    st.warning("No work log available")
                    continue
                
                # Display each step
                for step_num, step in enumerate(work_log['steps'], 1):
                    st.markdown(f"**Step {step_num}: {step['step'].replace('_', ' ').title()}**")
                    
                    # Show step details
                    step_copy = step.copy()
                    step_copy.pop('step', None)
                    
                    st.json(step_copy)
                    st.markdown("---")
                
                # Summary
                st.markdown("### Prediction vs Actual")
                
                scol1, scol2 = st.columns(2)
                
                with scol1:
                    st.markdown("**Predicted:**")
                    st.markdown(f"- Signal: {result['prediction']['signal']}")
                    st.markdown(f"- Return: {result['prediction']['target_change_pct']:+.1f}%")
                    st.markdown(f"- Position: {result['prediction']['position']:.2f}")
                    st.markdown(f"- Velocity: {result['prediction']['velocity']:.3f}/day")
                    st.markdown(f"- Acceleration: {result['prediction']['acceleration']:.4f}/day²")
                
                with scol2:
                    st.markdown("**Actual:**")
                    st.markdown(f"- Direction: {result['actual']['direction']}")
                    st.markdown(f"- Return: {result['actual']['return_pct']:+.1f}%")
                    st.markdown(f"- Error: {result['accuracy']['magnitude_error']:.1f}%")
                    
                    if result['accuracy']['direction_correct']:
                        st.success("✅ Direction correct!")
                    else:
                        st.error("❌ Direction wrong")
        
        # ========== EXPORT RESULTS ==========
        st.markdown("---")
        st.subheader("💾 Export Backtest Results")
        
        if st.button("📥 Export Full Report to JSON"):
            report_path = backtester.export_backtest_report(results)
            
            with open(report_path, 'r') as f:
                report_json = f.read()
            
            st.download_button(
                label="📥 Download Backtest Report",
                data=report_json,
                file_name=f"ti_backtest_{start_date.strftime('%Y%m%d')}_{end_date.strftime('%Y%m%d')}.json",
                mime="application/json",
                use_container_width=True
            )
            
            st.success(f"✅ Report generated: {report_path}")
        
        # ========== PARAMETER TUNING RECOMMENDATIONS ==========
        st.markdown("---")
        st.subheader("🔧 Parameter Tuning Recommendations")
        
        if accuracy_stats['direction_accuracy'] < 65:
            st.warning("**Accuracy below target - recommended parameter adjustments:**")
            
            # Analyze which resolution types performed best
            best_resolution = max(
                resolution_stats.items(),
                key=lambda x: x[1]['accuracy']
            )
            
            worst_resolution = min(
                resolution_stats.items(),
                key=lambda x: x[1]['accuracy']
            )
            
            st.markdown(f"""
            **Performance Analysis:**
            - Best Resolution Type: **{best_resolution[0].upper()}** ({best_resolution[1]['accuracy']:.1f}% accuracy)
            - Worst Resolution Type: **{worst_resolution[0].upper()}** ({worst_resolution[1]['accuracy']:.1f}% accuracy)
            
            **Suggested Adjustments:**
            1. Increase weight for {best_resolution[0]} signals
            2. Add stricter filtering for {worst_resolution[0]} predictions
            3. Consider adjusting GILE baseline parameters
            4. Tune MR PD thresholds to favor higher-accuracy resolution types
            5. Increase lookback window for velocity/acceleration calculations
            """)
        else:
            st.success("""
            **✅ Accuracy meets target!**
            
            Current parameter configuration is effective. Consider:
            1. Testing on additional time periods to verify robustness
            2. Expanding to more stocks
            3. Publishing results for academic validation
            """)

if __name__ == "__main__":
    render_backtest_dashboard()
