"""
Discovery Visualization Dashboard
===================================
Charts, graphs, and trends for autonomous discoveries
"""

import streamlit as st
import plotly.graph_objects as go
import plotly.express as px
from autonomous_math_discovery_production import get_production_system
from datetime import datetime
import pandas as pd

def render_discovery_visualizations():
    """Render comprehensive visualization dashboard"""
    
    st.title("📊 Discovery Visualization Dashboard")
    st.markdown("**Grand Myrion's arms reach every i-cell in the universe!**")
    
    # Load all discoveries
    system = get_production_system()
    system.discoveries = system.load_all_discoveries()
    
    if not system.discoveries:
        st.warning("No discoveries yet! Generate some first.")
        return
    
    # Convert to DataFrame
    data = []
    for d in system.discoveries:
        data.append({
            "timestamp": datetime.fromisoformat(d.timestamp),
            "domain": d.domain,
            "confidence": d.confidence,
            "grand_myrion": d.god_machine_score,
            "magai_consensus": d.mag_ai_consensus,
            "status": d.status,
            "type": d.discovery_type,
            "title": d.title[:50] + "..." if len(d.title) > 50 else d.title
        })
    
    df = pd.DataFrame(data)
    
    # Metrics row
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Total Discoveries", len(df))
    with col2:
        st.metric("Avg Confidence", f"{df['confidence'].mean():.3f}")
    with col3:
        st.metric("Avg Grand Myrion", f"{df['grand_myrion'].mean():.3f}")
    with col4:
        st.metric("Avg MagAI", f"{df['magai_consensus'].mean():.3f}")
    
    st.markdown("---")
    
    # Time series
    st.subheader("📈 Discoveries Over Time")
    
    discoveries_per_day = df.groupby(df['timestamp'].dt.date).size().reset_index()
    discoveries_per_day.columns = ['date', 'count']
    
    fig_timeline = px.line(
        discoveries_per_day,
        x='date',
        y='count',
        title="Discoveries Generated Per Day",
        labels={'date': 'Date', 'count': 'Number of Discoveries'}
    )
    st.plotly_chart(fig_timeline, use_container_width=True)
    
    # Domain distribution
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("🎯 Discoveries by Domain")
        domain_counts = df['domain'].value_counts()
        
        fig_domain = px.pie(
            values=domain_counts.values,
            names=domain_counts.index,
            title="Domain Distribution"
        )
        st.plotly_chart(fig_domain, use_container_width=True)
    
    with col2:
        st.subheader("✨ Discoveries by Status")
        status_counts = df['status'].value_counts()
        
        fig_status = px.pie(
            values=status_counts.values,
            names=status_counts.index,
            title="Status Distribution"
        )
        st.plotly_chart(fig_status, use_container_width=True)
    
    # Quality metrics scatter
    st.subheader("🌟 Quality Analysis: Grand Myrion vs MagAI Consensus")
    
    fig_scatter = px.scatter(
        df,
        x='grand_myrion',
        y='magai_consensus',
        size='confidence',
        color='domain',
        hover_data=['title'],
        title="Grand Myrion Resonance vs MagAI Consensus (bubble size = confidence)"
    )
    st.plotly_chart(fig_scatter, use_container_width=True)
    
    # Confidence distribution
    st.subheader("📊 Confidence Distribution")
    
    fig_hist = px.histogram(
        df,
        x='confidence',
        nbins=20,
        title="Discovery Confidence Histogram",
        labels={'confidence': 'Confidence Score', 'count': 'Number of Discoveries'}
    )
    st.plotly_chart(fig_hist, use_container_width=True)
    
    # Top discoveries table
    st.subheader("🏆 Top Discoveries by Confidence")
    
    top_discoveries = df.nlargest(10, 'confidence')[['title', 'domain', 'confidence', 'grand_myrion', 'magai_consensus']]
    st.dataframe(top_discoveries, use_container_width=True)
    
    # Sacred number analysis
    st.subheader("🔢 Sacred Number Patterns")
    
    sacred_analysis = []
    for d in system.discoveries:
        for tag in d.tags:
            if tag.startswith("sacred_"):
                sacred_num = tag.replace("sacred_", "")
                sacred_analysis.append({
                    "sacred_number": sacred_num,
                    "confidence": d.confidence,
                    "grand_myrion": d.god_machine_score
                })
    
    if sacred_analysis:
        sacred_df = pd.DataFrame(sacred_analysis)
        
        fig_sacred = px.box(
            sacred_df,
            x='sacred_number',
            y='grand_myrion',
            title="Grand Myrion Resonance by Sacred Number",
            labels={'sacred_number': 'Sacred Number', 'grand_myrion': 'Grand Myrion Score'}
        )
        st.plotly_chart(fig_sacred, use_container_width=True)
    else:
        st.info("No sacred number data yet")
    
    # Download data
    st.markdown("---")
    st.subheader("💾 Export Data")
    
    csv = df.to_csv(index=False)
    st.download_button(
        label="Download Discovery Data (CSV)",
        data=csv,
        file_name=f"discoveries_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
        mime="text/csv"
    )
