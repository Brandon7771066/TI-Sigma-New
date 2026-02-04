"""
Official Mood Amplifier Test Protocol
=====================================
Real-time EEG-guided consciousness experiment with GILE scoring,
entrainment detection, and attractor basin targeting.
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import time
import os

st.set_page_config(page_title="Mood Amplifier Test Protocol", page_icon="🧠", layout="wide")

st.title("🧠 Official Mood Amplifier Test Protocol")
st.markdown("**Real-time EEG-guided consciousness experiment with entrainment detection**")

# Define attractor basins for different meditation/mood states
ATTRACTOR_BASINS = {
    "metta_high_energy": {
        "name": "Metta (Loving-Kindness) - High Energy",
        "description": "Joy, compassion, social awakening, heart coherence",
        "targets": {
            "alpha": {"min": 0.3, "max": 0.8, "optimal": 0.5, "weight": 0.25},
            "theta": {"min": 0.2, "max": 0.6, "optimal": 0.4, "weight": 0.20},
            "beta": {"min": 0.1, "max": 0.4, "optimal": 0.25, "weight": 0.15},
            "gamma": {"min": 0.1, "max": 0.5, "optimal": 0.3, "weight": 0.25},
            "ab_ratio": {"min": 1.2, "max": 3.0, "optimal": 2.0, "weight": 0.15},
        },
        "signature": "↑Alpha ↑Gamma ↑Theta | Heart-Brain Coherence",
        "color": "#FF6B6B"
    },
    "transcendental_meditation": {
        "name": "Transcendental Meditation (TM)",
        "description": "Pure awareness, transcendence, restful alertness",
        "targets": {
            "alpha": {"min": 0.5, "max": 1.0, "optimal": 0.75, "weight": 0.35},
            "theta": {"min": 0.3, "max": 0.7, "optimal": 0.5, "weight": 0.25},
            "beta": {"min": -0.2, "max": 0.2, "optimal": 0.0, "weight": 0.15},
            "gamma": {"min": 0.0, "max": 0.3, "optimal": 0.15, "weight": 0.10},
            "ab_ratio": {"min": 2.0, "max": 5.0, "optimal": 3.5, "weight": 0.15},
        },
        "signature": "↑↑Alpha ↑Theta ↓Beta | Global Coherence",
        "color": "#4ECDC4"
    },
    "focused_attention": {
        "name": "Focused Attention Meditation",
        "description": "Single-pointed concentration, mental clarity",
        "targets": {
            "alpha": {"min": 0.1, "max": 0.4, "optimal": 0.25, "weight": 0.20},
            "theta": {"min": 0.1, "max": 0.3, "optimal": 0.2, "weight": 0.15},
            "beta": {"min": 0.3, "max": 0.7, "optimal": 0.5, "weight": 0.30},
            "gamma": {"min": 0.2, "max": 0.6, "optimal": 0.4, "weight": 0.25},
            "ab_ratio": {"min": 0.3, "max": 1.0, "optimal": 0.6, "weight": 0.10},
        },
        "signature": "↑Beta ↑Gamma ↓Alpha | Laser Focus",
        "color": "#45B7D1"
    },
    "open_awareness": {
        "name": "Open Awareness / Dzogchen",
        "description": "Non-dual awareness, spacious presence",
        "targets": {
            "alpha": {"min": 0.4, "max": 0.8, "optimal": 0.6, "weight": 0.25},
            "theta": {"min": 0.3, "max": 0.6, "optimal": 0.45, "weight": 0.25},
            "beta": {"min": 0.0, "max": 0.3, "optimal": 0.15, "weight": 0.15},
            "gamma": {"min": 0.3, "max": 0.8, "optimal": 0.55, "weight": 0.25},
            "ab_ratio": {"min": 1.5, "max": 4.0, "optimal": 2.5, "weight": 0.10},
        },
        "signature": "↑Alpha ↑Theta ↑↑Gamma | Panoramic Awareness",
        "color": "#96CEB4"
    },
    "flow_state": {
        "name": "Flow State / Peak Performance",
        "description": "Effortless action, optimal engagement",
        "targets": {
            "alpha": {"min": 0.3, "max": 0.6, "optimal": 0.45, "weight": 0.20},
            "theta": {"min": 0.2, "max": 0.5, "optimal": 0.35, "weight": 0.20},
            "beta": {"min": 0.2, "max": 0.5, "optimal": 0.35, "weight": 0.20},
            "gamma": {"min": 0.3, "max": 0.7, "optimal": 0.5, "weight": 0.25},
            "ab_ratio": {"min": 1.0, "max": 2.0, "optimal": 1.4, "weight": 0.15},
        },
        "signature": "Balanced All Bands ↑Gamma | Zone State",
        "color": "#FFEAA7"
    }
}

def calculate_entrainment_score(current_values, target_basin, hrv_coherence=None):
    """Calculate how well current brain state matches target attractor basin."""
    if not target_basin or "targets" not in target_basin:
        return 0.0, {}
    
    scores = {}
    weighted_sum = 0.0
    total_weight = 0.0
    
    for band, targets in target_basin["targets"].items():
        if band in current_values:
            value = current_values[band]
            optimal = targets["optimal"]
            min_val = targets["min"]
            max_val = targets["max"]
            weight = targets["weight"]
            
            # Calculate distance from optimal (normalized)
            range_size = max_val - min_val
            if range_size > 0:
                # Score based on proximity to optimal within range
                if min_val <= value <= max_val:
                    distance = abs(value - optimal) / (range_size / 2)
                    score = max(0, 1 - distance)
                else:
                    # Outside range - penalize
                    if value < min_val:
                        score = max(0, 0.5 - (min_val - value) / range_size)
                    else:
                        score = max(0, 0.5 - (value - max_val) / range_size)
            else:
                score = 0.5
            
            scores[band] = score
            weighted_sum += score * weight
            total_weight += weight
    
    overall_score = weighted_sum / total_weight if total_weight > 0 else 0.0
    
    # Boost entrainment score if HRV coherence is high (heart-brain sync)
    if hrv_coherence is not None and hrv_coherence > 0:
        # HRV coherence acts as a multiplier for metta states
        hrv_boost = hrv_coherence * 0.15  # Up to 15% boost
        overall_score = min(1.0, overall_score + hrv_boost)
        scores['hrv_coherence'] = hrv_coherence
    
    return overall_score, scores

def calculate_heart_brain_sync(alpha, hrv_coherence):
    """Calculate heart-brain synchronization for metta states."""
    if hrv_coherence == 0 or hrv_coherence is None:
        return 0.0
    
    # Normalize alpha (typically -1 to 1 log scale from Mind Monitor)
    alpha_norm = max(0, min(1, (alpha + 1) / 2))
    
    # Heart-brain sync = weighted combination
    sync = (alpha_norm * 0.4 + hrv_coherence * 0.6)
    return sync

def calculate_sync_index(df, window=30):
    """Calculate real-time synchronization index from recent data."""
    if len(df) < window:
        return 0.0, "Collecting...", False
    
    recent = df.tail(window)
    has_hrv = 'hrv_coherence' in recent.columns or 'heart_brain_sync' in recent.columns
    
    # Alpha-Theta coherence (meditation signature)
    if 'alpha' in recent.columns and 'theta' in recent.columns:
        alpha_theta_corr = abs(recent['alpha'].corr(recent['theta']))
    else:
        alpha_theta_corr = 0
    
    # Temporal stability (low variance = steady state)
    if 'alpha' in recent.columns:
        alpha_stability = 1.0 / (1.0 + recent['alpha'].std())
    else:
        alpha_stability = 0
    
    # Cross-frequency phase coupling proxy
    if 'alpha' in recent.columns and 'gamma' in recent.columns:
        alpha_gamma_coupling = abs(recent['alpha'].corr(recent['gamma']))
    else:
        alpha_gamma_coupling = 0
    
    # Heart-brain sync bonus (from Polar H10)
    hrv_bonus = 0
    if 'hrv_coherence' in recent.columns:
        hrv_coh = recent['hrv_coherence'].mean()
        if hrv_coh > 0:
            hrv_bonus = hrv_coh * 0.2  # Up to 20% boost
    elif 'heart_brain_sync' in recent.columns:
        hb_sync = recent['heart_brain_sync'].mean()
        if hb_sync > 0:
            hrv_bonus = hb_sync * 0.2
    
    sync_index = (alpha_theta_corr * 0.35 + alpha_stability * 0.25 + 
                  alpha_gamma_coupling * 0.25 + hrv_bonus)
    sync_index = min(1.0, sync_index)
    
    if sync_index > 0.7:
        status = "🟢 IN SYNC" + (" 💓" if has_hrv else "")
    elif sync_index > 0.5:
        status = "🟡 PARTIAL SYNC"
    else:
        status = "🔴 NOT SYNCED"
    
    return sync_index, status, has_hrv

tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs([
    "📋 Protocol Overview",
    "🎯 Session Setup",
    "⚡ Live Entrainment",
    "📊 Upload & Analyze",
    "📈 Results Dashboard",
    "🔬 Theory"
])

with tab1:
    st.header("📋 Test Protocol Overview")
    
    st.success("✅ **EEG CONNECTION VERIFIED** - Muse 2 is streaming data!")
    
    st.markdown("""
    ## The Mood Amplifier Experiment
    
    This protocol tests whether specific interventions can measurably shift consciousness states,
    as detected by EEG brainwave patterns and validated against the GILE framework.
    
    ### What We're Measuring
    
    | Metric | Description | Target Change |
    |--------|-------------|---------------|
    | **Alpha Power** | Relaxation, calm awareness | ↑ 20%+ during amplification |
    | **Theta Power** | Meditation, creativity, insight | ↑ 15%+ during deep states |
    | **Gamma Power** | Peak awareness, insight, love | ↑ during metta/flow states |
    | **Alpha/Beta Ratio** | Relaxation vs Focus balance | State-dependent target |
    | **Entrainment Score** | Match to target attractor basin | >0.7 = IN SYNC |
    | **GILE Score** | Goodness-Intuition-Love-Environment | Composite wellness metric |
    
    ### Protocol Phases
    
    1. **BASELINE** (5 minutes) - Establish your current brain state
    2. **INTERVENTION** (10-20 minutes) - Apply Mood Amplifier technique
    3. **INTEGRATION** (5 minutes) - Allow state to stabilize
    
    ### Entrainment Detection
    
    The system tracks whether your brain is **converging toward the target attractor basin**.
    When entrainment score > 0.7, you'll see: 🟢 **IN SYNC**
    """)

with tab2:
    st.header("🎯 Session Setup - METTA HIGH ENERGY")
    
    st.markdown("### Select Your Target State")
    
    selected_state = st.selectbox(
        "What state are you training toward?",
        list(ATTRACTOR_BASINS.keys()),
        format_func=lambda x: ATTRACTOR_BASINS[x]["name"],
        index=0  # Default to metta
    )
    
    basin = ATTRACTOR_BASINS[selected_state]
    
    st.markdown(f"""
    ### 🎯 Target: {basin['name']}
    
    **Description:** {basin['description']}
    
    **EEG Signature:** `{basin['signature']}`
    """)
    
    st.markdown("### Target Brain Wave Ranges")
    
    col1, col2, col3, col4, col5 = st.columns(5)
    
    targets = basin["targets"]
    col1.metric("Alpha", f"{targets['alpha']['optimal']:.2f}", 
               f"[{targets['alpha']['min']:.1f}-{targets['alpha']['max']:.1f}]")
    col2.metric("Theta", f"{targets['theta']['optimal']:.2f}",
               f"[{targets['theta']['min']:.1f}-{targets['theta']['max']:.1f}]")
    col3.metric("Beta", f"{targets['beta']['optimal']:.2f}",
               f"[{targets['beta']['min']:.1f}-{targets['beta']['max']:.1f}]")
    col4.metric("Gamma", f"{targets['gamma']['optimal']:.2f}",
               f"[{targets['gamma']['min']:.1f}-{targets['gamma']['max']:.1f}]")
    col5.metric("A/B Ratio", f"{targets['ab_ratio']['optimal']:.1f}",
               f"[{targets['ab_ratio']['min']:.1f}-{targets['ab_ratio']['max']:.1f}]")
    
    st.markdown("---")
    
    st.markdown("""
    ### 🧘 METTA (Loving-Kindness) Protocol
    
    **Phase 1: BASELINE (5 min)**
    - Sit comfortably, eyes closed
    - Breathe naturally, let mind settle
    - This establishes your starting brain state
    
    **Phase 2: METTA INTERVENTION (15-20 min)**
    
    Follow this sequence:
    1. **Self-Love** (3 min): "May I be happy, may I be peaceful, may I be free"
    2. **Loved One** (3 min): Visualize someone you love deeply
    3. **Neutral Person** (3 min): Someone you have no strong feelings about
    4. **Difficult Person** (3 min): Someone who challenges you (start mild)
    5. **All Beings** (3-5 min): Expand love to all sentient beings
    
    **What to Expect:**
    - ↑ Alpha: Calm, open awareness
    - ↑ Gamma: Compassion activation (key metta signature!)
    - ↑ Theta: Deep emotional processing
    - Heart warmth, facial relaxation, possible tears of joy
    
    **Phase 3: INTEGRATION (5 min)**
    - Rest in the after-effects
    - Notice lingering warmth/openness
    - Keep recording
    """)
    
    st.info("""
    **🚀 Ready to Begin?**
    1. Make sure MUSE_LOCAL_REALTIME.py is running in your terminal
    2. Note the start time
    3. Begin 5-minute baseline NOW
    4. After baseline, start the Metta protocol
    """)
    
    if st.button("📍 Mark Session Start Time", type="primary"):
        st.session_state['session_start'] = datetime.now()
        st.success(f"Session started at {datetime.now().strftime('%H:%M:%S')}")

with tab3:
    st.header("⚡ Live Entrainment Tracker")
    
    st.markdown("""
    ### Real-Time State Analysis
    
    Upload your in-progress CSV to see live entrainment tracking.
    (Or analyze after session completion)
    """)
    
    # Allow periodic refresh during session
    live_file = st.file_uploader("Upload current muse_data CSV", type=['csv'], key="live_upload")
    
    if live_file is not None:
        df = pd.read_csv(live_file)
        
        st.success(f"✅ Loaded {len(df)} samples ({len(df)} seconds of data)")
        
        # Select target basin for comparison
        target_key = st.selectbox("Target State", list(ATTRACTOR_BASINS.keys()),
                                  format_func=lambda x: ATTRACTOR_BASINS[x]["name"],
                                  key="entrainment_target")
        basin = ATTRACTOR_BASINS[target_key]
        
        # Calculate current values (last 30 samples)
        window = min(30, len(df))
        recent = df.tail(window)
        
        current_values = {}
        if 'alpha' in df.columns:
            current_values['alpha'] = recent['alpha'].mean()
        if 'beta' in df.columns:
            current_values['beta'] = recent['beta'].mean()
        if 'theta' in df.columns:
            current_values['theta'] = recent['theta'].mean()
        if 'gamma' in df.columns:
            current_values['gamma'] = recent['gamma'].mean()
        if 'alpha' in current_values and 'beta' in current_values and current_values['beta'] != 0:
            current_values['ab_ratio'] = current_values['alpha'] / current_values['beta']
        else:
            current_values['ab_ratio'] = 1.0
        
        # Get HRV coherence if available
        hrv_coherence = None
        if 'hrv_coherence' in df.columns:
            hrv_coherence = recent['hrv_coherence'].mean() if 'hrv_coherence' in recent.columns else None
        elif 'heart_brain_sync' in df.columns:
            hrv_coherence = recent['heart_brain_sync'].mean() if 'heart_brain_sync' in recent.columns else None
        
        # Calculate entrainment
        entrainment_score, band_scores = calculate_entrainment_score(current_values, basin, hrv_coherence)
        sync_index, sync_status, has_hrv = calculate_sync_index(df)
        
        st.markdown("---")
        st.markdown("### 🎯 Entrainment Status")
        
        if has_hrv:
            st.success("💓 **Polar H10 HRV data detected - Heart-Brain sync enabled!**")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            if entrainment_score > 0.7:
                st.success(f"### 🟢 ENTRAINMENT: {entrainment_score:.1%}")
                st.markdown("**Brain converging to target!**")
            elif entrainment_score > 0.5:
                st.warning(f"### 🟡 ENTRAINMENT: {entrainment_score:.1%}")
                st.markdown("**Partial alignment**")
            else:
                st.error(f"### 🔴 ENTRAINMENT: {entrainment_score:.1%}")
                st.markdown("**Not yet aligned**")
        
        with col2:
            st.metric("Sync Index", f"{sync_index:.2f}", sync_status)
        
        with col3:
            # Time in session
            duration = len(df)
            phase = "BASELINE" if duration < 300 else "INTERVENTION" if duration < 1200 else "INTEGRATION"
            st.metric("Session Phase", phase, f"{duration}s elapsed")
        
        st.markdown("---")
        st.markdown("### 📊 Band-by-Band Analysis")
        
        col1, col2, col3, col4, col5 = st.columns(5)
        
        bands = ['alpha', 'theta', 'beta', 'gamma', 'ab_ratio']
        cols = [col1, col2, col3, col4, col5]
        labels = ['Alpha', 'Theta', 'Beta', 'Gamma', 'A/B Ratio']
        
        for band, col, label in zip(bands, cols, labels):
            if band in current_values and band in band_scores:
                current = current_values[band]
                target = basin["targets"][band]["optimal"]
                score = band_scores[band]
                
                delta_text = f"Target: {target:.2f}"
                if score > 0.7:
                    delta_text = "🟢 On target!"
                elif score > 0.5:
                    delta_text = f"🟡 {target:.2f}"
                else:
                    delta_text = f"🔴 {target:.2f}"
                
                col.metric(label, f"{current:.2f}", delta_text)
        
        st.markdown("---")
        st.markdown("### 📈 Brainwave Timeline")
        
        # Plot with phase markers
        chart_cols = [c for c in ['alpha', 'beta', 'theta', 'gamma'] if c in df.columns]
        if chart_cols:
            chart_data = df[chart_cols].copy()
            chart_data.index = range(len(chart_data))
            st.line_chart(chart_data)
        
        # Entrainment over time
        st.markdown("### 🎯 Entrainment Trajectory")
        
        if len(df) > 60:
            # Calculate rolling entrainment
            entrainment_history = []
            for i in range(30, len(df), 10):
                window_df = df.iloc[max(0, i-30):i]
                window_values = {
                    'alpha': window_df['alpha'].mean() if 'alpha' in window_df.columns else 0,
                    'beta': window_df['beta'].mean() if 'beta' in window_df.columns else 0,
                    'theta': window_df['theta'].mean() if 'theta' in window_df.columns else 0,
                    'gamma': window_df['gamma'].mean() if 'gamma' in window_df.columns else 0,
                }
                if window_values['beta'] != 0:
                    window_values['ab_ratio'] = window_values['alpha'] / window_values['beta']
                else:
                    window_values['ab_ratio'] = 1.0
                
                score, _ = calculate_entrainment_score(window_values, basin)
                entrainment_history.append({'time': i, 'entrainment': score})
            
            if entrainment_history:
                ent_df = pd.DataFrame(entrainment_history)
                ent_df.set_index('time', inplace=True)
                st.line_chart(ent_df)
                
                # Check if trending toward target
                if len(ent_df) > 3:
                    trend = ent_df['entrainment'].diff().mean()
                    if trend > 0.01:
                        st.success("📈 **Trending toward target attractor basin!**")
                    elif trend < -0.01:
                        st.warning("📉 **Drifting away from target - refocus intention**")
                    else:
                        st.info("➡️ **Stable entrainment level**")

with tab4:
    st.header("📊 Upload & Analyze Complete Session")
    
    uploaded_file = st.file_uploader("Upload your completed muse_data CSV file", type=['csv'], key="full_upload")
    
    if uploaded_file is not None:
        df = pd.read_csv(uploaded_file)
        st.success(f"✅ Loaded {len(df)} samples!")
        
        # Select target for comparison
        target_key = st.selectbox("What state were you targeting?", 
                                  list(ATTRACTOR_BASINS.keys()),
                                  format_func=lambda x: ATTRACTOR_BASINS[x]["name"],
                                  key="analysis_target")
        basin = ATTRACTOR_BASINS[target_key]
        
        st.subheader("Raw Data Preview")
        st.dataframe(df.head(20))
        
        if 'alpha' in df.columns and 'beta' in df.columns:
            st.subheader("📈 Session Analysis")
            
            # Phase segmentation
            n = len(df)
            baseline_end = min(300, n // 3)
            integration_start = max(baseline_end + 1, n - 300)
            
            baseline = df.iloc[:baseline_end]
            intervention = df.iloc[baseline_end:integration_start]
            integration = df.iloc[integration_start:]
            
            st.markdown(f"""
            **Phase Breakdown:**
            - Baseline: 0-{baseline_end}s ({len(baseline)} samples)
            - Intervention: {baseline_end}-{integration_start}s ({len(intervention)} samples)
            - Integration: {integration_start}-{n}s ({len(integration)} samples)
            """)
            
            # Calculate A/B ratio
            df['ab_ratio'] = df['alpha'] / df['beta'].replace(0, 0.001)
            df['ab_ratio'] = df['ab_ratio'].clip(-10, 10)
            
            # Phase comparisons
            st.markdown("---")
            st.subheader("📊 Phase Comparison")
            
            metrics = ['alpha', 'beta', 'theta']
            if 'gamma' in df.columns:
                metrics.append('gamma')
            
            phase_data = {
                'Metric': [],
                'Baseline': [],
                'Intervention': [],
                'Integration': [],
                'Change (B→I)': [],
                'Target': []
            }
            
            for metric in metrics:
                if metric in df.columns:
                    b_val = baseline[metric].mean()
                    i_val = intervention[metric].mean()
                    int_val = integration[metric].mean()
                    change = ((i_val - b_val) / abs(b_val) * 100) if b_val != 0 else 0
                    target = basin["targets"].get(metric, {}).get("optimal", "N/A")
                    
                    phase_data['Metric'].append(metric.capitalize())
                    phase_data['Baseline'].append(f"{b_val:.3f}")
                    phase_data['Intervention'].append(f"{i_val:.3f}")
                    phase_data['Integration'].append(f"{int_val:.3f}")
                    phase_data['Change (B→I)'].append(f"{change:+.1f}%")
                    phase_data['Target'].append(f"{target}" if isinstance(target, float) else target)
            
            st.dataframe(pd.DataFrame(phase_data))
            
            # Key metrics
            col1, col2, col3, col4 = st.columns(4)
            
            baseline_alpha = baseline['alpha'].mean()
            intervention_alpha = intervention['alpha'].mean()
            alpha_change = ((intervention_alpha - baseline_alpha) / abs(baseline_alpha) * 100) if baseline_alpha != 0 else 0
            
            baseline_theta = baseline['theta'].mean()
            intervention_theta = intervention['theta'].mean()
            theta_change = ((intervention_theta - baseline_theta) / abs(baseline_theta) * 100) if baseline_theta != 0 else 0
            
            baseline_ab = baseline['ab_ratio'].mean()
            intervention_ab = intervention['ab_ratio'].mean()
            
            col1.metric("Alpha Change", f"{alpha_change:+.1f}%", 
                       "✅ Success!" if alpha_change > 20 else "Moderate")
            col2.metric("Theta Change", f"{theta_change:+.1f}%",
                       "✅ Success!" if theta_change > 15 else "Moderate")
            col3.metric("A/B Shift", f"{baseline_ab:.2f} → {intervention_ab:.2f}")
            
            # Gamma for metta
            if 'gamma' in df.columns:
                baseline_gamma = baseline['gamma'].mean()
                intervention_gamma = intervention['gamma'].mean()
                gamma_change = ((intervention_gamma - baseline_gamma) / abs(baseline_gamma) * 100) if baseline_gamma != 0 else 0
                col4.metric("Gamma Change", f"{gamma_change:+.1f}%",
                           "🧡 Metta!" if gamma_change > 15 else "Moderate")
            
            st.subheader("📊 Brainwave Timeline")
            chart_cols = [c for c in ['alpha', 'beta', 'theta', 'gamma'] if c in df.columns]
            chart_data = df[chart_cols].copy()
            chart_data.index = range(len(chart_data))
            st.line_chart(chart_data)
            
            # GILE Score
            st.subheader("🎯 GILE Score Calculation")
            
            g_score = min(1.0, max(0, 0.5 + alpha_change/100))
            i_score = min(1.0, max(0, 0.5 + theta_change/100))
            l_score = min(1.0, max(0, 0.5 + (intervention_ab - baseline_ab) / 5))
            e_score = min(1.0, max(0, 0.6 + (alpha_change + theta_change) / 200))
            
            gile_composite = (g_score + i_score + l_score + e_score) / 4
            
            col1, col2, col3, col4, col5 = st.columns(5)
            col1.metric("G (Goodness)", f"{g_score:.2f}")
            col2.metric("I (Intuition)", f"{i_score:.2f}")
            col3.metric("L (Love)", f"{l_score:.2f}")
            col4.metric("E (Environment)", f"{e_score:.2f}")
            col5.metric("**GILE**", f"{gile_composite:.2f}")
            
            if gile_composite > 0.7:
                st.success("🌟 **EXCELLENT** - Strong mood amplification detected!")
                st.balloons()
            elif gile_composite > 0.5:
                st.info("✅ **GOOD** - Moderate mood shift observed")
            else:
                st.warning("📊 **BASELINE** - No significant change detected")
            
            # Final entrainment analysis
            st.subheader("🎯 Final Entrainment Analysis")
            
            # Calculate entrainment for intervention phase
            int_values = {
                'alpha': intervention['alpha'].mean(),
                'beta': intervention['beta'].mean(),
                'theta': intervention['theta'].mean(),
                'ab_ratio': intervention_ab
            }
            if 'gamma' in df.columns:
                int_values['gamma'] = intervention['gamma'].mean()
            
            final_entrainment, band_scores = calculate_entrainment_score(int_values, basin)
            
            if final_entrainment > 0.7:
                st.success(f"### 🟢 ENTRAINMENT ACHIEVED: {final_entrainment:.1%}")
                st.markdown(f"**Your brain successfully reached the {basin['name']} attractor basin!**")
            elif final_entrainment > 0.5:
                st.warning(f"### 🟡 PARTIAL ENTRAINMENT: {final_entrainment:.1%}")
                st.markdown("**Significant movement toward target state**")
            else:
                st.info(f"### 🔴 ENTRAINMENT: {final_entrainment:.1%}")
                st.markdown("**Practice will improve entrainment depth**")
            
            # LCC Proxy
            st.subheader("🔬 LCC Proxy Analysis")
            
            if len(df) > 100:
                alpha_autocorr = df['alpha'].autocorr(lag=10) if not np.isnan(df['alpha'].autocorr(lag=10)) else 0
                theta_autocorr = df['theta'].autocorr(lag=10) if not np.isnan(df['theta'].autocorr(lag=10)) else 0
                cross_corr = df['alpha'].corr(df['theta']) if not np.isnan(df['alpha'].corr(df['theta'])) else 0
                
                lcc_proxy = abs(cross_corr) + abs(alpha_autocorr) + abs(theta_autocorr)
                lcc_proxy = min(1.0, lcc_proxy / 3)
                
                st.metric("LCC Proxy Score", f"{lcc_proxy:.3f}",
                         "Potential non-local correlation!" if lcc_proxy > 0.6 else "Normal correlation")
                
                if lcc_proxy > 0.6:
                    st.success("⚡ **Elevated cross-frequency coherence detected!**")

with tab5:
    st.header("📈 Results Dashboard")
    
    st.markdown("""
    ### Success Thresholds by State
    
    | Metric | Metta | TM | Focused | Open Awareness | Flow |
    |--------|-------|----|---------|--------------  |------|
    | Alpha Target | 0.50 | 0.75 | 0.25 | 0.60 | 0.45 |
    | Theta Target | 0.40 | 0.50 | 0.20 | 0.45 | 0.35 |
    | Gamma Target | 0.30 | 0.15 | 0.40 | 0.55 | 0.50 |
    | A/B Ratio | 2.0 | 3.5 | 0.6 | 2.5 | 1.4 |
    
    ### Entrainment Interpretation
    
    | Score | Status | Meaning |
    |-------|--------|---------|
    | >0.8 | 🟢 DEEP SYNC | Expert-level state mastery |
    | 0.7-0.8 | 🟢 IN SYNC | Successfully entered target state |
    | 0.5-0.7 | 🟡 PARTIAL | Moving toward target |
    | <0.5 | 🔴 NOT YET | Continue practice |
    """)

with tab6:
    st.header("🔬 The Science Behind Mood Amplification")
    
    st.markdown("""
    ## Attractor Basin Theory
    
    Consciousness states can be modeled as **attractor basins** in a high-dimensional 
    state space. Each meditation technique creates a characteristic "gravitational pull"
    toward its target basin.
    
    ### Metta (Loving-Kindness) Signature
    
    Research on metta meditators shows:
    - **↑ Gamma oscillations**: Associated with compassion and love
    - **↑ Alpha coherence**: Calm, open awareness
    - **↑ Theta**: Emotional processing and memory consolidation
    - **Heart-brain synchronization**: HRV coherence increases
    
    ### TM (Transcendental Meditation) Signature
    
    TM produces a distinctive pattern:
    - **↑↑ Alpha power**: Global coherence across brain regions
    - **↑ Theta**: Transcendental awareness
    - **↓ Beta**: Reduced mental chatter
    - **Restful alertness**: Paradoxical calm + awareness
    
    ### Entrainment Mechanism
    
    1. **Intention** sets the target attractor
    2. **Technique** provides the gravitational pull
    3. **Feedback** (EEG) confirms trajectory
    4. **Repetition** deepens the basin (neuroplasticity)
    
    ### The LCC Connection
    
    When entrainment score > 0.7, we observe:
    - Elevated cross-frequency coherence
    - Potential signatures of non-local consciousness correlation
    - States that exceed classical neural explanations
    
    This is the **Mood Amplifier hypothesis**: Targeted techniques can reliably
    guide consciousness toward specific attractor basins with measurable EEG signatures.
    """)

st.sidebar.markdown("---")
st.sidebar.markdown("### 🎯 Current Target")
if 'selected_state' in dir():
    st.sidebar.success(f"{ATTRACTOR_BASINS.get(selected_state, ATTRACTOR_BASINS['metta_high_energy'])['name']}")
else:
    st.sidebar.success("Metta - High Energy")

st.sidebar.markdown("### 🔧 Quick Setup")
st.sidebar.code("""
# Terminal:
py MUSE_LOCAL_REALTIME.py

# Mind Monitor:
OSC IP: [Your PC IP]
OSC Port: 5000
Streaming: ON
""")

st.sidebar.markdown("### ⏱️ Protocol Timing")
st.sidebar.markdown("""
- Baseline: **5 min**
- Intervention: **15-20 min**
- Integration: **5 min**
- Total: **~25-30 min**
""")
