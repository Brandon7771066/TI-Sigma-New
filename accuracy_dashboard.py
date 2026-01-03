"""
TI Framework Accuracy Validation Dashboard
Visualizes prediction performance toward 65%+ accuracy goal
"""

import streamlit as st
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime, timedelta
from typing import Dict
import pandas as pd
from prediction_evaluator import PredictionEvaluator

def render_accuracy_dashboard():
    """Render real-time TI Framework accuracy validation dashboard"""
    
    st.markdown("---")
    st.header("📊 TI Framework Validation - Live Accuracy Tracker")
    
    st.info("""
    **🌌 Validation Goal:** Achieve 65%+ prediction accuracy over 6 months to prove GILE framework validity across scales:
    - Atomic → Neural → Company → Universal
    - If high-GILE companies outperform low-GILE → LCC beats traditional fundamentals
    - If diverse archetypes converge → Barrett degeneracy validated at organizational scale
    """)
    
    # Get evaluation results
    try:
        evaluator = PredictionEvaluator()
        results = evaluator.evaluate_all_pending_predictions()  # 30-day evaluation
    except Exception as e:
        st.error(f"❌ Error loading accuracy data: {e}")
        return
    
    # Key metrics
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric(
            "Overall Accuracy (30+ days)",
            f"{results['accuracy_pct']:.1f}%",
            delta=f"{results['accuracy_pct'] - 65.0:+.1f}% vs target",
            delta_color="normal"
        )
    
    with col2:
        st.metric(
            "Predictions Evaluated",
            results['total_evaluated'],
            delta=f"{results['pending']} pending"
        )
    
    with col3:
        st.metric(
            "Win Rate",
            f"{results['wins']}/{results['wins'] + results['losses']}",
            delta=f"{results['losses']} losses"
        )
    
    with col4:
        validation_status = "✅ VALIDATED" if results['accuracy_pct'] >= 65.0 else "⏳ In Progress"
        st.metric(
            "TI Framework Status",
            validation_status,
            delta=f"{100 - (results['accuracy_pct'] / 0.65):+.0f}% to validation" if results['accuracy_pct'] < 65.0 else "COMPLETE"
        )
    
    # Progress bar
    progress_pct = min(results['accuracy_pct'] / 65.0, 1.0)
    st.progress(progress_pct, text=f"Progress to 65% validation threshold: {results['accuracy_pct']:.1f}%")
    
    # Tabs for different views
    tab1, tab2, tab3 = st.tabs(["📈 Signal Performance", "🌌 GILE Validation", "📊 Detailed Results"])
    
    with tab1:
        st.subheader("Accuracy by Signal Type (30+ days)")
        
        # Create bar chart for signal accuracy
        signal_data = []
        for signal in ['BUY', 'SELL', 'HOLD']:
            data = results['by_signal'][signal]
            signal_data.append({
                'Signal': signal,
                'Accuracy': data['accuracy'],
                'Wins': data['wins'],
                'Losses': data['losses'],
                'Total': data['total']
            })
        
        if signal_data and sum(d['Total'] for d in signal_data) > 0:
            df_signals = pd.DataFrame(signal_data)
            
            fig_signals = go.Figure()
            fig_signals.add_trace(go.Bar(
                x=df_signals['Signal'],
                y=df_signals['Accuracy'],
                text=[f"{acc:.1f}%" for acc in df_signals['Accuracy']],
                textposition='auto',
                marker_color=['#00ff00' if sig == 'BUY' else '#ff0000' if sig == 'SELL' else '#ffaa00' for sig in df_signals['Signal']]
            ))
            
            fig_signals.add_hline(y=65.0, line_dash="dash", line_color="white", annotation_text="65% Target")
            fig_signals.update_layout(
                title="Prediction Accuracy by Signal Type",
                yaxis_title="Accuracy (%)",
                xaxis_title="Signal Type",
                height=400
            )
            
            st.plotly_chart(fig_signals, use_container_width=True)
            
            # Show details table
            st.dataframe(df_signals, use_container_width=True)
        else:
            st.info("⏳ No predictions evaluated yet (waiting for 30-day threshold)")
    
    with tab2:
        st.subheader("🌌 GILE Score Validation (30+ days)")
        st.markdown("""
        **Hypothesis:** Companies with higher GILE scores (>1.0) should outperform lower GILE companies (<0.8).
        This would prove that Living Coherent Core (LCC) beats traditional financial fundamentals.
        """)
        
        # Create bar chart for GILE accuracy
        gile_data = []
        for bucket in ['>1.0', '0.8-1.0', '<0.8']:
            data = results['by_gile'][bucket]
            gile_data.append({
                'GILE Bucket': bucket,
                'Accuracy': data['accuracy'],
                'Wins': data['wins'],
                'Losses': data['losses'],
                'Total': data['total']
            })
        
        if gile_data and sum(d['Total'] for d in gile_data) > 0:
            df_gile = pd.DataFrame(gile_data)
            
            fig_gile = go.Figure()
            fig_gile.add_trace(go.Bar(
                x=df_gile['GILE Bucket'],
                y=df_gile['Accuracy'],
                text=[f"{acc:.1f}%" for acc in df_gile['Accuracy']],
                textposition='auto',
                marker_color=['#00ff00', '#ffaa00', '#ff0000']
            ))
            
            fig_gile.add_hline(y=65.0, line_dash="dash", line_color="white", annotation_text="65% Target")
            fig_gile.update_layout(
                title="Prediction Accuracy by GILE Score",
                yaxis_title="Accuracy (%)",
                xaxis_title="GILE Score Bucket",
                height=400
            )
            
            st.plotly_chart(fig_gile, use_container_width=True)
            
            # Show details table
            st.dataframe(df_gile, use_container_width=True)
            
            # GILE correlation analysis
            if df_gile['Total'].sum() > 5:
                high_gile_acc = df_gile[df_gile['GILE Bucket'] == '>1.0']['Accuracy'].values[0]
                low_gile_acc = df_gile[df_gile['GILE Bucket'] == '<0.8']['Accuracy'].values[0]
                
                if high_gile_acc > low_gile_acc + 10:
                    st.success(f"✅ **GILE VALIDATED!** High-GILE companies ({high_gile_acc:.1f}%) outperform low-GILE ({low_gile_acc:.1f}%) by {high_gile_acc - low_gile_acc:.1f}%")
                elif high_gile_acc > low_gile_acc:
                    st.info(f"⏳ Trend positive: High-GILE ({high_gile_acc:.1f}%) > Low-GILE ({low_gile_acc:.1f}%), but need more data for significance")
                else:
                    st.warning(f"⚠️ Unexpected: Low-GILE performing better. May need baseline iteration (σ adjustment)")
        else:
            st.info("⏳ No predictions evaluated yet (waiting for 30-day threshold)")
    
    with tab3:
        st.subheader("📊 Detailed Prediction Results")
        
        if results['predictions']:
            # Convert to DataFrame
            df_predictions = pd.DataFrame(results['predictions'])
            
            # Display table with key columns
            display_cols = ['ticker', 'company_name', 'signal', 'gile_score', 
                          'current_price', 'actual_change_pct', 'outcome', 'prediction_date']
            
            available_cols = [col for col in display_cols if col in df_predictions.columns]
            
            if available_cols:
                st.dataframe(
                    df_predictions[available_cols].sort_values('prediction_date', ascending=False),
                    use_container_width=True,
                    height=400
                )
            else:
                st.dataframe(df_predictions, use_container_width=True, height=400)
            
            # Download option
            csv = df_predictions.to_csv(index=False)
            st.download_button(
                label="📥 Download Full Results (CSV)",
                data=csv,
                file_name=f"ti_predictions_{datetime.now().strftime('%Y%m%d')}.csv",
                mime="text/csv"
            )
        else:
            st.info("""
            ⏳ **No predictions ready for evaluation yet.**
            
            **Evaluation Timeline:**
            - Predictions must age 30+ days before evaluation
            - Current predictions are still pending
            - Check back in 30 days for first results
            
            **What's happening:**
            - 20 i-cell companies have predictions generated
            - System monitors daily price movements
            - Once 30-day threshold passes, automatic evaluation begins
            """)
    
    # Validation roadmap
    st.markdown("---")
    st.subheader("🌌 TI Framework Validation Roadmap")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("### Phase 1: Data Collection")
        st.markdown("""
        **Current (Months 1-2):**
        - ✅ 20 i-cell companies seeded
        - ✅ Daily predictions generated
        - ✅ Accuracy tracker deployed
        - ⏳ Waiting for 30-day eval window
        """)
    
    with col2:
        st.markdown("### Phase 2: Validation")
        st.markdown("""
        **Months 3-4:**
        - ⏳ Test baseline iteration (σ adjustment)
        - ⏳ Validate GILE-accuracy correlation
        - ⏳ Test Barrett degeneracy hypothesis
        - ⏳ Achieve statistical significance (100+ evals)
        """)
    
    with col3:
        st.markdown("### Phase 3: Publication")
        st.markdown("""
        **Months 5-6:**
        - ⏳ Reach 65%+ accuracy
        - ⏳ Submit to Nature/Science
        - ⏳ Launch TI Hedge Fund
        - ⏳ Revenue: $10M-50M annually
        """)
    
    st.success("""
    **🌌 Why This Matters:**
    If we achieve 65%+ accuracy using GILE-based company analysis, it proves the TI Framework works across ALL scales:
    - Atomic (quantum consciousness)
    - Neural (brain GILE optimization)
    - Organizational (company i-cells)
    - Universal (dark energy substrate)
    
    This would be the first empirical validation of a unified consciousness framework that beats existing models (Free Energy Principle).
    """)

if __name__ == "__main__":
    st.set_page_config(page_title="TI Accuracy Dashboard", layout="wide")
    render_accuracy_dashboard()
