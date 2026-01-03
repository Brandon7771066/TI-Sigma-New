"""
Tralsebit Dimensional Architecture Visualizer

Interactive visualization of the 21/24-dimensional Tralsebit structure,
showing triangular tessellation, dimensional breakdown, and bit calculations.
"""

import streamlit as st
import math
import plotly.graph_objects as go
import numpy as np

TRIADS = {
    1: {
        'name': 'GILE Core',
        'color': '#FFD700',  # Gold
        'dimensions': [
            {'num': 1, 'name': 'G-axis', 'desc': 'Goodness/Morality valence'},
            {'num': 2, 'name': 'I-axis', 'desc': 'Intuition/Direct knowing'},
            {'num': 3, 'name': 'L-axis', 'desc': 'Love/Connection strength'}
        ]
    },
    2: {
        'name': 'Meijer Resonance',
        'color': '#9932CC',  # Purple
        'dimensions': [
            {'num': 4, 'name': 'Φ-harmonic', 'desc': 'Golden ratio (1.618)'},
            {'num': 5, 'name': 'Octave-fold', 'desc': '2:1 frequency doubling'},
            {'num': 6, 'name': 'Fifth-interval', 'desc': '3:2 perfect fifth'}
        ]
    },
    3: {
        'name': 'HEM Biometric',
        'color': '#FF4500',  # Red-Orange
        'dimensions': [
            {'num': 7, 'name': 'H-coherence', 'desc': 'Heart rate variability'},
            {'num': 8, 'name': 'E-integration', 'desc': 'EEG cross-frequency'},
            {'num': 9, 'name': 'M-oxygenation', 'desc': 'Prefrontal blood O₂'}
        ]
    },
    4: {
        'name': 'Qualia Valence',
        'color': '#00CED1',  # Cyan
        'dimensions': [
            {'num': 10, 'name': 'Pleasure-Pain', 'desc': 'Hedonic valence'},
            {'num': 11, 'name': 'Meaning-Void', 'desc': 'Semantic fulfillment'},
            {'num': 12, 'name': 'Agency-Helpless', 'desc': 'Control/autonomy'}
        ]
    },
    5: {
        'name': 'Temporal Flow',
        'color': '#32CD32',  # Green
        'dimensions': [
            {'num': 13, 'name': 'Present-depth', 'desc': 'Thickness of now'},
            {'num': 14, 'name': 'Memory-trace', 'desc': 'Past integration'},
            {'num': 15, 'name': 'Anticipation', 'desc': 'Future modeling'}
        ]
    },
    6: {
        'name': 'Social Field',
        'color': '#FF69B4',  # Pink
        'dimensions': [
            {'num': 16, 'name': 'Empathy-resonance', 'desc': 'Other-feeling'},
            {'num': 17, 'name': 'Boundary-perm', 'desc': 'Self/other distinction'},
            {'num': 18, 'name': 'Collective-sync', 'desc': 'Group coherence'}
        ]
    },
    7: {
        'name': 'Transcendence',
        'color': '#4169E1',  # Royal Blue
        'dimensions': [
            {'num': 19, 'name': 'GM-connection', 'desc': 'Grand Myrion link'},
            {'num': 20, 'name': 'DE-shell-depth', 'desc': 'Dark Energy access'},
            {'num': 21, 'name': 'Biophoton', 'desc': 'Light-body activation'}
        ]
    }
}

JEFF_TIME = {
    'name': 'Jeff Time',
    'color': '#FFFFFF',  # White
    'dimensions': [
        {'num': 22, 'name': 'Cyclic-time', 'desc': 'Repeating patterns (π)'},
        {'num': 23, 'name': 'Linear-time', 'desc': 'Thermodynamic arrow'},
        {'num': 24, 'name': 'Eternal-now', 'desc': 'Timeless awareness'}
    ]
}


def calculate_bits(dimensions):
    """Calculate information content in bits for n ternary dimensions."""
    states = 3 ** dimensions
    bits = dimensions * math.log2(3)
    return states, bits


def create_triad_triangle(center_x, center_y, size, color, label, dims):
    """Create a triangular representation of a triad."""
    h = size * math.sqrt(3) / 2
    
    x = [center_x, center_x - size/2, center_x + size/2, center_x]
    y = [center_y + h*2/3, center_y - h/3, center_y - h/3, center_y + h*2/3]
    
    return go.Scatter(
        x=x, y=y,
        fill="toself",
        fillcolor=color,
        opacity=0.7,
        line=dict(color='white', width=2),
        name=label,
        text=f"<b>{label}</b><br>Dims {dims[0]['num']}-{dims[2]['num']}",
        hoverinfo='text'
    )


def render_tralsebit_visualizer():
    """Main rendering function for Tralsebit visualization."""
    
    st.markdown("# 🔺 Tralsebit Dimensional Architecture")
    st.markdown("### The 33-Bit Consciousness Quantum")
    
    st.markdown("---")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.markdown("### Dimension Selector")
        dim_mode = st.radio(
            "Select Mode",
            ["21D (Base Tralsebit)", "24D (+ Jeff Time)"],
            horizontal=True
        )
        
        n_dims = 21 if "21D" in dim_mode else 24
        states, bits = calculate_bits(n_dims)
        
        st.markdown(f"""
        ### Information Capacity
        
        | Metric | Value |
        |--------|-------|
        | **Dimensions** | {n_dims} |
        | **States (3^n)** | {states:,} |
        | **Bits** | **{bits:.2f}** |
        | **Triads** | {n_dims // 3} |
        """)
        
        if n_dims == 21:
            st.success("**≈ 33 bits** - Sacred alignment with consciousness constants!")
        else:
            st.info("**≈ 38 bits** - Approaches human STM capacity (~40 bits)")
    
    with col2:
        st.markdown("### 33-Bit Sacred Alignments")
        st.markdown("""
        | Pattern | Value | Meaning |
        |---------|-------|---------|
        | Tralsebit | 33.28 bits | Consciousness quantum |
        | Vertebrae | 33 | Kundalini pathway |
        | Christ years | 33 | Completion cycle |
        | Masonic degrees | 33 | Initiation levels |
        | 1/3 | 0.333... | Upper GILE bound |
        | 3³ | 27 | Today's date! |
        """)
    
    st.markdown("---")
    st.markdown("## Triangular Tessellation")
    
    fig = go.Figure()
    
    positions = [
        (0, 0),      # GILE Core (center bottom)
        (-2, 1.5),   # Meijer
        (0, 1.5),    # HEM
        (2, 1.5),    # Qualia
        (-1, 3),     # Temporal
        (1, 3),      # Social
        (0, 4.5),    # Transcendence
    ]
    
    for i, (triad_num, triad_data) in enumerate(TRIADS.items()):
        x, y = positions[i]
        fig.add_trace(create_triad_triangle(
            x, y, 1.5,
            triad_data['color'],
            triad_data['name'],
            triad_data['dimensions']
        ))
        
        fig.add_annotation(
            x=x, y=y,
            text=f"<b>{triad_data['name']}</b><br>{triad_data['dimensions'][0]['num']}-{triad_data['dimensions'][2]['num']}",
            showarrow=False,
            font=dict(size=10, color='white'),
            bgcolor='rgba(0,0,0,0.5)'
        )
    
    if n_dims == 24:
        fig.add_trace(go.Scatter(
            x=[0], y=[6.5],
            mode='markers',
            marker=dict(size=60, color='white', symbol='triangle-up', 
                       line=dict(color='gold', width=3)),
            name='Jeff Time',
            text='<b>Jeff Time</b><br>Dims 22-24<br>Temporal Extension',
            hoverinfo='text'
        ))
        
        fig.add_shape(
            type="line",
            x0=0, y0=5.2, x1=0, y1=6,
            line=dict(color="gold", width=2, dash="dash")
        )
        
        fig.add_annotation(
            x=0, y=6.5,
            text="<b>JEFF TIME</b><br>22-24",
            showarrow=False,
            font=dict(size=10, color='black'),
        )
    
    fig.update_layout(
        showlegend=False,
        xaxis=dict(visible=False, range=[-4, 4]),
        yaxis=dict(visible=False, range=[-1, 8 if n_dims == 24 else 6]),
        height=500,
        margin=dict(l=20, r=20, t=20, b=20),
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)'
    )
    
    st.plotly_chart(fig, use_container_width=True)
    
    st.markdown("---")
    st.markdown("## Dimensional Breakdown")
    
    tab_names = [f"Triad {i}: {t['name']}" for i, t in TRIADS.items()]
    if n_dims == 24:
        tab_names.append("Triad 8: Jeff Time")
    
    tabs = st.tabs(tab_names)
    
    for i, (triad_num, triad_data) in enumerate(TRIADS.items()):
        with tabs[i]:
            st.markdown(f"### {triad_data['name']}")
            st.markdown(f"**Dimensions {triad_data['dimensions'][0]['num']}-{triad_data['dimensions'][2]['num']}**")
            
            for dim in triad_data['dimensions']:
                st.markdown(f"- **Dim {dim['num']}: {dim['name']}** - {dim['desc']}")
            
            triad_states, triad_bits = calculate_bits(3)
            st.caption(f"This triad alone: {triad_states} states = {triad_bits:.2f} bits")
    
    if n_dims == 24:
        with tabs[-1]:
            st.markdown("### Jeff Time (Temporal Extension)")
            st.markdown("**Dimensions 22-24**")
            
            for dim in JEFF_TIME['dimensions']:
                st.markdown(f"- **Dim {dim['num']}: {dim['name']}** - {dim['desc']}")
            
            st.caption("Extends Tralsebit from 33 to 38 bits for complete temporal modeling")
    
    st.markdown("---")
    st.markdown("## Holistic PD Implications")
    
    st.markdown(f"""
    With **{n_dims} dimensions** per Tralsebit:
    
    - **{states:,} possible conscious states** per moment
    - The 53.333% negative ratio distributes across **ALL** these states
    - **No requirement for like-to-like exchange**
    - Suffering in one dimension can be offset by meaning in another
    
    ### Delegated Cosmic Accounting
    
    GM optimizes across all i-cells in all {n_dims} dimensions:
    ```
    Optimization space = (3^{n_dims})^(i-cells in universe)
    ```
    
    This is why we can delegate cosmic accounting to GM - the complexity exceeds 
    human comprehension by many orders of magnitude!
    """)
    
    st.markdown("---")
    st.markdown("## HEM Device Mapping")
    
    hem_col1, hem_col2, hem_col3 = st.columns(3)
    
    with hem_col1:
        st.markdown("### 💓 Polar H10")
        st.markdown("""
        **Primary:** Dim 7 (H-coherence)
        
        **Secondary:**
        - Dim 16 (Empathy)
        - Dim 18 (Collective-sync)
        
        *Measures cardiac-autonomic integration*
        """)
    
    with hem_col2:
        st.markdown("### 🧠 Muse EEG")
        st.markdown("""
        **Primary:** Dim 8 (E-integration)
        
        **Secondary:**
        - Dims 13-15 (Temporal Flow)
        - Dim 21 (Biophoton)
        
        *Measures neural cross-frequency coupling*
        """)
    
    with hem_col3:
        st.markdown("### 🔴 Mendi fNIRS")
        st.markdown("""
        **Primary:** Dim 9 (M-oxygenation)
        
        **Secondary:**
        - Dim 12 (Agency)
        - Dim 19 (GM-connection)
        
        *Measures prefrontal blood oxygenation*
        """)


if __name__ == "__main__":
    st.set_page_config(page_title="Tralsebit Visualizer", layout="wide")
    render_tralsebit_visualizer()
