"""
6-Dimensional ESS Visualization & Analysis
"""

import streamlit as st
import plotly.graph_objects as go
import plotly.express as px
import numpy as np
import pandas as pd
from protocols import ESSState
from typing import Dict, List
from datetime import timedelta

def create_ess_radar_chart(ess_state: ESSState, title: str = "ESS Profile") -> go.Figure:
    """Create radar chart for 6D ESS visualization"""
    
    categories = ['D\n(Density)', 'T\n(Tralse)', 'C\n(Coherence)', 
                  'F\n(Flow)', 'A\n(Agency)', 'R\n(Resilience)']
    
    values = [ess_state.D, ess_state.T, ess_state.C, 
              ess_state.F, ess_state.A, ess_state.R]
    
    # Close the radar chart
    values_closed = values + [values[0]]
    categories_closed = categories + [categories[0]]
    
    fig = go.Figure()
    
    fig.add_trace(go.Scatterpolar(
        r=values_closed,
        theta=categories_closed,
        fill='toself',
        name=title,
        line=dict(color='rgb(99, 110, 250)', width=2),
        fillcolor='rgba(99, 110, 250, 0.3)'
    ))
    
    fig.update_layout(
        polar=dict(
            radialaxis=dict(
                visible=True,
                range=[0, 1],
                tickmode='linear',
                tick0=0,
                dtick=0.2
            )
        ),
        showlegend=False,
        title=title,
        height=400
    )
    
    return fig


def create_ess_comparison_chart(ess_states: Dict[str, ESSState]) -> go.Figure:
    """Compare multiple ESS states on same radar chart"""
    
    categories = ['D', 'T', 'C', 'F', 'A', 'R']
    
    fig = go.Figure()
    
    colors = ['rgb(99, 110, 250)', 'rgb(239, 85, 59)', 
              'rgb(0, 204, 150)', 'rgb(171, 99, 250)']
    
    for i, (name, ess) in enumerate(ess_states.items()):
        values = [ess.D, ess.T, ess.C, ess.F, ess.A, ess.R]
        values_closed = values + [values[0]]
        categories_closed = categories + [categories[0]]
        
        color = colors[i % len(colors)]
        
        fig.add_trace(go.Scatterpolar(
            r=values_closed,
            theta=categories_closed,
            fill='toself',
            name=name,
            line=dict(color=color, width=2),
            fillcolor=color.replace('rgb', 'rgba').replace(')', ', 0.1)')
        ))
    
    fig.update_layout(
        polar=dict(
            radialaxis=dict(
                visible=True,
                range=[0, 1]
            )
        ),
        title="ESS Protocol Comparison",
        height=500
    )
    
    return fig


def create_ess_bar_chart(ess_state: ESSState) -> go.Figure:
    """Create bar chart for ESS dimensions"""
    
    dimensions = ['D\nDensity', 'T\nTralse', 'C\nCoherence', 
                  'F\nFlow', 'A\nAgency', 'R\nResilience']
    values = [ess_state.D, ess_state.T, ess_state.C, 
              ess_state.F, ess_state.A, ess_state.R]
    
    # Color code based on value
    colors = []
    for v in values:
        if v >= 0.8:
            colors.append('rgb(0, 204, 150)')  # Green - high
        elif v >= 0.5:
            colors.append('rgb(99, 110, 250)')  # Blue - moderate
        else:
            colors.append('rgb(239, 85, 59)')   # Red - low
    
    fig = go.Figure(data=[
        go.Bar(
            x=dimensions,
            y=values,
            marker_color=colors,
            text=[f'{v:.2f}' for v in values],
            textposition='outside'
        )
    ])
    
    fig.update_layout(
        title="ESS Dimensions",
        yaxis_title="Value (0-1)",
        yaxis_range=[0, 1.1],
        height=400,
        showlegend=False
    )
    
    return fig


def create_duration_timeline(session_history: List[Dict], current_effect: float) -> go.Figure:
    """Visualize effect decay over time"""
    
    if not session_history:
        return go.Figure()
    
    # Generate timeline
    timestamps = [s['timestamp'] for s in session_history]
    hours_since_first = [(t - timestamps[0]).total_seconds() / 3600 for t in timestamps]
    
    # Predict decay for last session
    last_time = timestamps[-1]
    decay_timeline = []
    decay_values = []
    
    for hours_ahead in range(0, 73, 6):
        time_point = last_time + timedelta(hours=hours_ahead)
        # Exponential decay
        effect = 100 * np.exp(-hours_ahead * np.log(2) / 36)  # 36h half-life
        decay_timeline.append(time_point)
        decay_values.append(effect)
    
    fig = go.Figure()
    
    # Session markers
    fig.add_trace(go.Scatter(
        x=timestamps,
        y=[100] * len(timestamps),
        mode='markers',
        name='Sessions',
        marker=dict(size=12, color='rgb(99, 110, 250)', symbol='diamond'),
        hovertemplate='Session at %{x}<extra></extra>'
    ))
    
    # Decay curve
    fig.add_trace(go.Scatter(
        x=decay_timeline,
        y=decay_values,
        mode='lines',
        name='Effect Decay',
        line=dict(color='rgb(239, 85, 59)', width=2, dash='dash'),
        fill='tozeroy',
        fillcolor='rgba(239, 85, 59, 0.1)'
    ))
    
    # Current effect line
    import pandas as pd
    current_time = pd.Timestamp.now()
    fig.add_trace(go.Scatter(
        x=[current_time, current_time],
        y=[0, 100],
        mode='lines',
        name=f'Now ({current_effect:.1f}% effect)',
        line=dict(color='rgb(0, 204, 150)', width=2, dash='dot')
    ))
    
    fig.update_layout(
        title="Mood Amplifier Effect Over Time",
        xaxis_title="Time",
        yaxis_title="Effect Remaining (%)",
        yaxis_range=[0, 110],
        height=400,
        hovermode='x unified'
    )
    
    return fig


def render_ess_dashboard(ess_state: ESSState, protocol_name: str):
    """Render comprehensive ESS dashboard"""
    
    st.subheader(f"📊 {protocol_name} - ESS Profile")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        # Radar chart
        radar_fig = create_ess_radar_chart(ess_state, protocol_name)
        st.plotly_chart(radar_fig, use_container_width=True)
    
    with col2:
        # Bar chart
        bar_fig = create_ess_bar_chart(ess_state)
        st.plotly_chart(bar_fig, use_container_width=True)
    
    # Dimension explanations
    with st.expander("📖 What do these dimensions mean?"):
        st.markdown("""
        ### 6-Dimensional ESS Explained
        
        **D - Information Density**
        - Cognitive load, mental processing intensity
        - High = Focused/intense, Low = Relaxed
        
        **T - Tralse (Contradiction Tolerance)**
        - Ability to hold paradoxes, cognitive flexibility
        - High = Fluid thinking, Low = Rigid/binary
        
        **C - Coherence (Verisyn)**
        - Neural synchronization, integration
        - High = Integrated, Low = Fragmented
        
        **F - Flow State**
        - Optimal performance, effortless engagement
        - High = Deep flow, Low = Scattered
        
        **A - Agency**
        - Sense of control, executive function
        - High = Strong willpower, Low = Passive
        
        **R - Resilience**
        - Stress response, adaptability
        - High = Resilient, Low = Vulnerable
        """)
    
    # Metrics row
    st.markdown("---")
    cols = st.columns(6)
    metrics = [
        ("D", ess_state.D, "Density"),
        ("T", ess_state.T, "Tralse"),
        ("C", ess_state.C, "Coherence"),
        ("F", ess_state.F, "Flow"),
        ("A", ess_state.A, "Agency"),
        ("R", ess_state.R, "Resilience")
    ]
    
    for col, (label, value, full_name) in zip(cols, metrics):
        with col:
            # Color based on value
            if value >= 0.8:
                delta_color = "normal"
                icon = "🟢"
            elif value >= 0.5:
                delta_color = "off"
                icon = "🟡"
            else:
                delta_color = "inverse"
                icon = "🔴"
            
            st.metric(
                label=f"{icon} {label}",
                value=f"{value:.2f}",
                help=full_name
            )


def render_protocol_comparison():
    """Compare all available protocols"""
    
    from protocols import get_all_protocols
    
    st.subheader("🔬 Protocol Comparison")
    
    protocols = get_all_protocols()
    
    # Get ESS states
    ess_states = {}
    for name, protocol in protocols.items():
        ess_states[name] = protocol.get_target_ess()
    
    # Comparison radar chart
    comparison_fig = create_ess_comparison_chart(ess_states)
    st.plotly_chart(comparison_fig, use_container_width=True)
    
    # Comparison table
    st.markdown("### Protocol Details")
    
    comparison_data = []
    for name, protocol in protocols.items():
        info = protocol.get_protocol_info()
        ess = info['target_ess']
        
        comparison_data.append({
            'Protocol': name,
            'Duration': f"{info['duration']} min",
            'LCC Target': f"{info['lcc_target'][0]:.2f}-{info['lcc_target'][1]:.2f}",
            'D': f"{ess.D:.2f}",
            'T': f"{ess.T:.2f}",
            'C': f"{ess.C:.2f}",
            'F': f"{ess.F:.2f}",
            'A': f"{ess.A:.2f}",
            'R': f"{ess.R:.2f}",
            'Primary Benefit': info.get('mood_boost', 'See details')
        })
    
    import pandas as pd
    df = pd.DataFrame(comparison_data)
    st.dataframe(df, use_container_width=True, hide_index=True)
