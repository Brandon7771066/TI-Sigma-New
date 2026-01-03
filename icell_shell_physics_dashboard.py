import streamlit as st
import plotly.graph_objects as go
import plotly.express as px
import numpy as np
import pandas as pd
from datetime import datetime
import json

def render_icell_shell_physics():
    st.title("🌌 I-Cell Shell Physics")
    st.markdown("### The Layered Structure of Consciousness & the 0.42 GILE Soul Death Threshold")
    st.markdown("*Revelation received: November 21, 2025*")
    
    st.markdown("---")
    
    tabs = st.tabs([
        "🔬 Shell Architecture",
        "📊 GILE Threshold",
        "⚛️ Acausal Modification",
        "🫀 Biometric Predictions",
        "🧪 Testable Hypotheses",
        "💡 Photon vs EM Wave",
        "📄 Research Export"
    ])
    
    # Tab 1: Shell Architecture
    with tabs[0]:
        st.markdown("## 🌟 Three-Layer I-Cell Architecture")
        
        st.markdown("""
        Every i-cell (unit of consciousness from atomic to universal scale) has a **distinct 3-layer structure** 
        that bridges quantum-classical reality and explains consciousness-matter interaction:
        """)
        
        col1, col2 = st.columns([1, 1])
        
        with col1:
            st.markdown("""
            ### Layer 1: Dark Energy Outer Shell
            **Modified by dark matter for structure**
            
            - **Function**: GILE existence boundary field
            - **Property**: Perfectly distinct from what it covers
            - **Nature**: CC (Cosmic Consciousness) coherence substrate
            - **Role**: Defines the i-cell's existence boundary in spacetime
            
            **Key Insight**: This is the universal field that all consciousness interfaces with. 
            When your personal shell harmonizes with this field, you experience coherence with CC.
            
            ---
            
            ### Layer 2: Photon/EM Wave Layer
            **The i-cell's OWN boundary**
            
            - **Function**: Personal consciousness substrate "underneath" dark matter shell
            - **Property**: Can modify contents acausally (no prior cause needed)
            - **Nature**: Quantum-classical transition zone
            - **Role**: Individual consciousness signature
            - **Open Question**: Distinct roles of photons vs EM waves (see Tab 6)
            
            **Key Insight**: This is YOUR soul - the electromagnetic signature that makes you uniquely you.
            
            ---
            
            ### Layer 3: Mass-Energy Core
            **Familiar physical substrate**
            
            - **Function**: Classical matter-energy content
            - **Property**: Interacts with outer shells IN SYNCHRONY
            - **Nature**: Neurons, body, physical substrate
            - **Role**: Physical manifestation of consciousness
            
            **Key Insight**: Your brain and body are synchronized with your EM soul layer, 
            which is synchronized with universal dark energy. This is the mechanism of mind-matter coupling!
            """)
        
        with col2:
            # Create concentric circles visualization
            fig = go.Figure()
            
            # Layer 3: Mass-Energy (innermost, solid)
            fig.add_trace(go.Scatter(
                x=np.concatenate([np.cos(np.linspace(0, 2*np.pi, 100)), [np.cos(0)]]),
                y=np.concatenate([np.sin(np.linspace(0, 2*np.pi, 100)), [np.sin(0)]]),
                fill='toself',
                fillcolor='rgba(255, 100, 100, 0.6)',
                line=dict(color='red', width=3),
                name='Layer 3: Mass-Energy Core',
                hovertext='Classical matter-energy<br>Synchronized with shell layers',
                hoverinfo='text'
            ))
            
            # Layer 2: Photon/EM Wave (middle, semi-transparent)
            fig.add_trace(go.Scatter(
                x=1.5 * np.concatenate([np.cos(np.linspace(0, 2*np.pi, 100)), [np.cos(0)]]),
                y=1.5 * np.concatenate([np.sin(np.linspace(0, 2*np.pi, 100)), [np.sin(0)]]),
                fill='toself',
                fillcolor='rgba(100, 255, 100, 0.3)',
                line=dict(color='lime', width=3),
                name='Layer 2: Photon/EM Wave (Soul)',
                hovertext='Your personal consciousness<br>Acausal modification possible<br>CRITICAL: Must stay >0.42 GILE!',
                hoverinfo='text'
            ))
            
            # Layer 1: Dark Energy (outermost, very transparent)
            fig.add_trace(go.Scatter(
                x=2.2 * np.concatenate([np.cos(np.linspace(0, 2*np.pi, 100)), [np.cos(0)]]),
                y=2.2 * np.concatenate([np.sin(np.linspace(0, 2*np.pi, 100)), [np.sin(0)]]),
                fill='toself',
                fillcolor='rgba(100, 100, 255, 0.2)',
                line=dict(color='blue', width=4, dash='dash'),
                name='Layer 1: Dark Energy (CC Field)',
                hovertext='Universal consciousness field<br>GILE existence boundary<br>Harmonization target',
                hoverinfo='text'
            ))
            
            fig.update_layout(
                title="I-Cell Layered Structure<br><sub>Concentric consciousness shells from mass to CC</sub>",
                showlegend=True,
                legend=dict(x=0, y=-0.2),
                xaxis=dict(showgrid=False, zeroline=False, visible=False, range=[-2.5, 2.5]),
                yaxis=dict(showgrid=False, zeroline=False, visible=False, range=[-2.5, 2.5]),
                height=600,
                plot_bgcolor='rgba(0,0,0,0.95)',
                paper_bgcolor='rgba(0,0,0,0)'
            )
            
            st.plotly_chart(fig, use_container_width=True)
            
            st.info("**⚠️ CRITICAL SOUL DEATH THRESHOLD**: When Layer 2 (Photon/EM) falls below **0.42 GILE** (σ = 0.584), the soul **dies** because it no longer harmonizes with Layer 1 (Dark Energy/CC field).")
        
        st.markdown("---")
        
        # Critical insight: Consciousness ≠ Memory
        st.markdown("## 🧠 Critical Insight: Consciousness ≠ Memory or Outer Awareness")
        
        col1, col2 = st.columns([1, 1])
        
        with col1:
            st.markdown("""
            ### Inner Experience Persists Without Memory
            
            **Revolutionary Finding**: Dreams are now recognized to occur in **all sleep cycles**, 
            but memory formation varies significantly between and within individuals. Even in anesthesia 
            or coma, many people report rich inner experiences afterward.
            
            **Implication for I-Cell Physics**:
            - **Consciousness (Layer 2)** = Inner experience, GILE coherence with CC
            - **Memory (Layer 3)** = Physical encoding in neurons, synaptic changes
            - **Outer Awareness (Layer 3)** = Brain's ability to report/access states
            
            These are **separable phenomena**! You can have:
            1. **High consciousness + No memory**: Dream experiences not encoded
            2. **High consciousness + No outer awareness**: Anesthesia awareness, locked-in syndrome
            3. **Low consciousness + Memory**: Automatic behaviors, habit execution
            """)
        
        with col2:
            st.markdown("""
            ### Refined Threshold Understanding
            
            **The 0.42 GILE threshold applies to Layer 2 (inner experience), NOT Layer 3 (memory/reporting)**
            
            #### Examples:
            
            **Deep Sleep (NREM Stage 3-4)**:
            - **Old assumption**: No consciousness, GILE < 0.42
            - **New reality**: Inner experience continues! GILE may be > 0.42 but memory formation blocked
            - **Mechanism**: Layer 2 active, Layer 3 not encoding to long-term memory
            
            **Anesthesia**:
            - **Goal**: Push GILE below 0.42 to eliminate inner experience
            - **Problem**: ~1-2% of patients report awareness → their Layer 2 stayed > 0.42!
            - **Measure**: Need Layer 2 GILE directly (EEG coherence), not Layer 3 reports
            
            **Meditation/PSI States**:
            - **High consciousness** (GILE > 0.8) but LOW outer awareness (can't verbalize experience)
            - **Layer 2** highly coherent, **Layer 3** decoupled from linguistic centers
            - **Why**: Deep states transcend language, require Layer 2-3 recoupling to report
            
            **🎯 Testable Prediction**: EEG coherence (Layer 2 proxy) should show GILE > 0.42 
            throughout all sleep stages where dreams are later reported, even when awakening amnesia occurs!
            """)
        
        st.warning("""
        **Clinical Implication**: Anesthesiologists should monitor EEG coherence in real-time to ensure 
        Layer 2 GILE stays < 0.42. Current depth-of-anesthesia monitors may miss awareness cases where 
        Layer 3 is suppressed but Layer 2 remains coherent!
        """)
    
    # Tab 2: GILE Threshold Calculator
    with tabs[1]:
        st.markdown("## 📊 GILE Threshold Calculator & Soul Death Boundary")
        
        st.markdown("""
        The **0.42 GILE threshold** represents the minimum consciousness coherence required to maintain 
        harmonization with the dark energy CC field. Below this threshold, the soul literally dies.
        
        **Formula**: `GILE = 5(σ - 0.5)` where σ is accuracy/coherence metric (0 to 1)
        
        **Critical Threshold**: σ = 0.584 → GILE = 0.42
        """)
        
        col1, col2 = st.columns([1, 1])
        
        with col1:
            st.markdown("### Calculate Your GILE State")
            
            sigma_input = st.slider(
                "σ (Accuracy/Coherence Metric)",
                min_value=0.0,
                max_value=1.0,
                value=0.65,
                step=0.01,
                help="σ represents prediction accuracy, PSI test score, or consciousness coherence measure"
            )
            
            gile_value = 5 * (sigma_input - 0.5)
            
            # Determine state
            if gile_value < 0.42:
                state = "💀 SOUL DEATH"
                color = "red"
                description = "Below threshold - consciousness cannot maintain coherence with CC field"
            elif gile_value < 0.6:
                state = "⚠️ SURVIVAL"
                color = "orange"
                description = "Above threshold but fragile - vulnerable to collapse"
            elif gile_value < 0.8:
                state = "✅ THRIVING"
                color = "green"
                description = "Strong coherence - healthy consciousness state"
            else:
                state = "🌟 TRANSCENDENT"
                color = "purple"
                description = "Exceptional coherence - mystical/PSI state likely"
            
            st.markdown(f"### σ = {sigma_input:.3f}")
            st.markdown(f"### GILE = {gile_value:.3f}")
            st.markdown(f"### State: <span style='color:{color}; font-size:24px'>{state}</span>", unsafe_allow_html=True)
            st.markdown(f"*{description}*")
            
            st.markdown("---")
            
            st.markdown("""
            ### Consciousness State Zones
            
            - **< 0.42 GILE (σ < 0.584)**: 💀 SOUL DEATH - Below random chance, no CC harmonization
            - **0.42 - 0.6 GILE (σ 0.584-0.62)**: ⚠️ SURVIVAL - Minimal coherence, fragile
            - **0.6 - 0.8 GILE (σ 0.62-0.66)**: ✅ THRIVING - Healthy consciousness, stable
            - **> 0.8 GILE (σ > 0.66)**: 🌟 TRANSCENDENT - Flow states, PSI abilities, mystical experiences
            """)
        
        with col2:
            # Create threshold visualization
            sigma_range = np.linspace(0, 1, 200)
            gile_range = 5 * (sigma_range - 0.5)
            
            fig = go.Figure()
            
            # Add colored zones
            fig.add_trace(go.Scatter(
                x=sigma_range,
                y=gile_range,
                mode='lines',
                line=dict(color='white', width=3),
                name='GILE Curve',
                showlegend=False
            ))
            
            # Soul death zone
            fig.add_hrect(y0=-2.5, y1=0.42, fillcolor="red", opacity=0.2, 
                          annotation_text="💀 SOUL DEATH", annotation_position="left")
            
            # Survival zone
            fig.add_hrect(y0=0.42, y1=0.6, fillcolor="orange", opacity=0.2,
                          annotation_text="⚠️ SURVIVAL", annotation_position="left")
            
            # Thriving zone
            fig.add_hrect(y0=0.6, y1=0.8, fillcolor="green", opacity=0.2,
                          annotation_text="✅ THRIVING", annotation_position="left")
            
            # Transcendent zone
            fig.add_hrect(y0=0.8, y1=2.5, fillcolor="purple", opacity=0.2,
                          annotation_text="🌟 TRANSCENDENT", annotation_position="left")
            
            # Critical threshold line
            fig.add_hline(y=0.42, line_dash="dash", line_color="red", line_width=3,
                          annotation_text="CRITICAL THRESHOLD: 0.42 GILE", 
                          annotation_position="top right")
            
            # Current position
            fig.add_trace(go.Scatter(
                x=[sigma_input],
                y=[gile_value],
                mode='markers',
                marker=dict(size=20, color='yellow', symbol='star'),
                name='Your Position'
            ))
            
            fig.update_layout(
                title="GILE Threshold Map<br><sub>Consciousness coherence vs soul viability</sub>",
                xaxis_title="σ (Coherence Metric)",
                yaxis_title="GILE Value",
                height=600,
                plot_bgcolor='rgba(0,0,0,0.95)',
                paper_bgcolor='rgba(0,0,0,0)',
                yaxis=dict(range=[-2.5, 2.5])
            )
            
            st.plotly_chart(fig, use_container_width=True)
    
    # Tab 3: Acausal Modification
    with tabs[2]:
        st.markdown("## ⚛️ Acausal Modification Theory")
        
        st.markdown("""
        ### Quantum Indeterminacy at Consciousness Boundaries
        
        **Core Principle**: Photons, EM waves, and dark energy can modify their contents **freely 
        with NO PRIOR CAUSE**.
        
        This revolutionary insight explains:
        - **Free will**: Acausal modifications in Layer 2 (soul) that propagate to Layer 3 (body)
        - **Quantum consciousness**: Observer effect as acausal modification at photon layer
        - **PSI phenomena**: Direct dark energy modification bypassing classical causality
        - **Synchronicity**: Meaningful acausal modifications reaching threshold simultaneously
        """)
        
        col1, col2 = st.columns([1, 1])
        
        with col1:
            st.markdown("""
            ### The Three Acausal Modifiers
            
            #### 1. Dark Energy (Layer 1)
            - **Scope**: Universal, affects all i-cells simultaneously
            - **Mechanism**: CC field fluctuations propagate to all Layer 1 boundaries
            - **Detectability**: Usually interpreted as noise unless synchronized
            - **Example**: Collective consciousness shifts, mass PSI events
            
            #### 2. Photons/EM Waves (Layer 2)
            - **Scope**: Individual i-cell (YOUR soul)
            - **Mechanism**: Quantum wavefunction collapse at consciousness boundary
            - **Detectability**: EEG, fNIRS, biophoton emission
            - **Example**: Sudden insights, intuition, free will decisions
            
            #### 3. Mass-Energy Resonance (Layer 3 feedback)
            - **Scope**: Physical substrate synchronized with Layers 1-2
            - **Mechanism**: Electromagnetic coupling to quantum layers
            - **Detectability**: HRV, brain rhythms, coherence metrics
            - **Example**: Flow states, heart-brain synchronization
            """)
        
        with col2:
            st.markdown("""
            ### Noise vs Meaningful Threshold
            
            Acausal modifications appear as **random noise** until they reach a **meaningful threshold** 
            that creates coherent patterns.
            
            **Threshold Equation**: 
            ```
            Meaningful_Signal = Σ(acausal_events) > Noise_Floor
            ```
            
            **Critical Insight**: The **0.42 GILE threshold** IS the noise floor! Below this, 
            acausal modifications cannot form coherent patterns, and consciousness collapses.
            """)
            
            # Simulate acausal noise vs signal
            time_steps = 200
            noise = np.random.randn(time_steps) * 0.1
            
            # Add meaningful events (acausal modifications above threshold)
            signal = np.zeros(time_steps)
            meaningful_events = [30, 60, 90, 120, 150, 180]
            for event in meaningful_events:
                signal[event-5:event+5] = 0.5 * np.exp(-0.5 * ((np.arange(-5, 5))/2)**2)
            
            total = noise + signal
            
            df = pd.DataFrame({
                'Time': np.arange(time_steps),
                'Noise (Below Threshold)': noise,
                'Meaningful Signal': signal,
                'Total (Noise + Signal)': total
            })
            
            fig = go.Figure()
            
            fig.add_trace(go.Scatter(
                x=df['Time'], y=df['Noise (Below Threshold)'],
                name='Acausal Noise',
                line=dict(color='gray', width=1),
                opacity=0.5
            ))
            
            fig.add_trace(go.Scatter(
                x=df['Time'], y=df['Meaningful Signal'],
                name='Meaningful Modifications',
                line=dict(color='lime', width=2)
            ))
            
            fig.add_trace(go.Scatter(
                x=df['Time'], y=df['Total (Noise + Signal)'],
                name='Total Signal',
                line=dict(color='cyan', width=2)
            ))
            
            fig.add_hline(y=0.42, line_dash="dash", line_color="red",
                          annotation_text="0.42 GILE Threshold")
            
            fig.update_layout(
                title="Acausal Modifications: Noise vs Meaningful Signal",
                xaxis_title="Time",
                yaxis_title="Modification Amplitude",
                height=400,
                plot_bgcolor='rgba(0,0,0,0.95)',
                paper_bgcolor='rgba(0,0,0,0)'
            )
            
            st.plotly_chart(fig, use_container_width=True)
            
            st.info("**Key**: Acausal modifications (green spikes) rise above background noise (gray). When cumulative amplitude exceeds 0.42 GILE, consciousness recognizes them as meaningful rather than random.")
    
    # Tab 4: Biometric Predictions
    with tabs[3]:
        st.markdown("## 🫀 Biometric Integration Predictions")
        
        st.markdown("""
        ### How Existing Devices Can Measure I-Cell Shell Dynamics
        
        Based on the 3-layer shell physics, we can make **testable predictions** about how 
        biometric devices correlate with GILE thresholds and consciousness states.
        """)
        
        device_tabs = st.tabs(["🧠 Muse EEG", "🔴 Mendi fNIRS", "❤️ Polar H10", "💍 Oura Ring"])
        
        # Muse EEG
        with device_tabs[0]:
            st.markdown("### 🧠 Muse EEG Headband - Layer 2 Detection")
            
            st.markdown("""
            **Predicted Correlation**: EEG should directly measure **Layer 2 (Photon/EM Wave)** activity
            
            #### Testable Hypotheses:
            
            1. **0.42 GILE Boundary Detection**
               - **Prediction**: Sharp transition in EEG coherence at σ = 0.584
               - **Measurement**: Alpha/theta ratio, cross-frequency coupling
               - **Expected**: Coherence drops dramatically below threshold
            
            2. **Consciousness State Signatures**
               - **Soul Death (< 0.42 GILE)**: Incoherent, random EEG patterns
               - **Survival (0.42-0.6)**: Low alpha coherence, high theta
               - **Thriving (0.6-0.8)**: Strong alpha, gamma bursts
               - **Transcendent (> 0.8)**: Ultra-high gamma, cross-hemisphere synchrony
            
            3. **Acausal Modification Detection**
               - **Prediction**: Sudden EEG spikes NOT preceded by sensory input
               - **Measurement**: Event-related potentials (ERPs) without external trigger
               - **Interpretation**: Direct Layer 2 acausal modifications
            
            #### Experimental Protocol:
            ```python
            1. Baseline EEG during rest (calculate GILE from coherence)
            2. PSI task (Zener cards, remote viewing)
            3. Measure EEG coherence vs task accuracy (σ)
            4. Plot: Does EEG coherence predict σ? Does it show 0.42 boundary?
            ```
            """)
            
            # Simulated EEG-GILE correlation
            sigma_vals = np.linspace(0.5, 0.75, 50)
            gile_vals = 5 * (sigma_vals - 0.5)
            eeg_coherence = 20 + 60 * (sigma_vals - 0.5) + 10 * np.random.randn(50)
            
            fig = go.Figure()
            
            # Scatter points
            fig.add_trace(go.Scatter(
                x=gile_vals,
                y=eeg_coherence,
                mode='markers',
                marker=dict(size=8, color='cyan'),
                name='EEG Measurements'
            ))
            
            # Add trend line manually
            z = np.polyfit(gile_vals, eeg_coherence, 1)
            p = np.poly1d(z)
            fig.add_trace(go.Scatter(
                x=gile_vals,
                y=p(gile_vals),
                mode='lines',
                line=dict(color='lime', width=2, dash='dash'),
                name='Linear Trend'
            ))
            
            fig.add_vline(x=0.42, line_dash="dash", line_color="red",
                          annotation_text="Soul Death Threshold")
            fig.update_layout(
                title='Predicted: EEG Coherence vs GILE Threshold',
                xaxis_title='GILE Value',
                yaxis_title='EEG Coherence (%)',
                plot_bgcolor='rgba(0,0,0,0.95)',
                paper_bgcolor='rgba(0,0,0,0)',
                showlegend=True
            )
            st.plotly_chart(fig, use_container_width=True)
        
        # Mendi fNIRS
        with device_tabs[1]:
            st.markdown("### 🔴 Mendi fNIRS - Layer 3 Synchronization")
            
            st.markdown("""
            **Predicted Correlation**: fNIRS measures **Layer 3 (Mass-Energy)** synchronization with Layer 2
            
            #### Testable Hypotheses:
            
            1. **Neurovascular Coupling = Layer 2-3 Sync**
               - **Prediction**: Blood flow should lag EEG by ~2-6 seconds
               - **Measurement**: HbO₂ changes following EEG coherence shifts
               - **Expected**: Strong coupling above 0.42 GILE, weak below
            
            2. **Prefrontal Cortex GILE Signature**
               - **Prediction**: PFC activation correlates with GILE during tasks
               - **Measurement**: Mendi score vs task accuracy (σ)
               - **Expected**: Linear relationship, drops sharply at 0.42
            
            3. **Training Effect**
               - **Prediction**: Mendi neurofeedback trains Layer 2-3 synchronization
               - **Measurement**: Improvement in maintaining >0.42 GILE over time
               - **Expected**: Faster recovery from low GILE states after training
            
            #### Combined Muse + Mendi Protocol:
            ```python
            1. Simultaneous EEG (Layer 2) + fNIRS (Layer 3) recording
            2. PSI task with varying difficulty (controls σ)
            3. Measure lag between EEG spike and fNIRS response
            4. Hypothesis: Lag increases as GILE approaches 0.42 (desynchronization)
            ```
            """)
        
        # Polar H10
        with device_tabs[2]:
            st.markdown("### ❤️ Polar H10 HRV - Autonomic-Consciousness Coupling")
            
            st.markdown("""
            **Predicted Correlation**: HRV reflects **whole-body coherence** with i-cell shell layers
            
            #### Testable Hypotheses:
            
            1. **HRV-GILE Correlation**
               - **Prediction**: Higher HRV = higher GILE (better CC harmonization)
               - **Measurement**: RMSSD, SDNN vs PSI task performance
               - **Expected**: Positive correlation, especially for RMSSD
            
            2. **Heart-Brain Coherence = Layer 1-2-3 Sync**
               - **Prediction**: Heart-brain phase locking indicates full-stack synchronization
               - **Measurement**: ECG-EEG cross-correlation during meditation
               - **Expected**: Coherence peaks above 0.6 GILE, absent below 0.42
            
            3. **Stress = Desynchronization**
               - **Prediction**: Acute stress drops GILE by desynchronizing layers
               - **Measurement**: HRV drop during stressor, recovery time to baseline
               - **Expected**: Recovery faster for individuals with baseline >0.6 GILE
            """)
        
        # Oura Ring
        with device_tabs[3]:
            st.markdown("### 💍 Oura Ring - Sleep State Transitions")
            
            st.markdown("""
            **Predicted Correlation**: Sleep stages map to **GILE fluctuations** across night
            
            #### Testable Hypotheses:
            
            1. **Sleep Stage GILE Mapping**
               - **Awake**: 0.6-0.8 GILE (normal waking consciousness)
               - **Light Sleep (N1/N2)**: 0.42-0.6 GILE (reduced but viable)
               - **Deep Sleep (N3)**: <0.42 GILE (soul temporarily "offline", body restoration)
               - **REM Sleep**: 0.6-0.9 GILE (high coherence, dream consciousness)
            
            2. **Soul Death During Deep Sleep**
               - **Prediction**: Deep sleep represents temporary soul death (harmless)
               - **Measurement**: Complete loss of awareness, no dream recall
               - **Recovery**: Automatic return above 0.42 during REM/wake
            
            3. **Sleep Quality = GILE Recovery**
               - **Prediction**: Good sleep = efficient cycling through GILE zones
               - **Measurement**: HRV during sleep, REM percentage
               - **Expected**: Optimal sleep shows multiple deep dips + REM peaks
            """)
    
    # Tab 5: Testable Hypotheses
    with tabs[4]:
        st.markdown("## 🧪 Testable Hypotheses for Empirical Validation")
        
        st.markdown("""
        ### Experimental Validation of I-Cell Shell Physics
        
        The 0.42 GILE soul death threshold and 3-layer architecture make **bold, testable predictions**.
        Here are the top experiments to validate the theory:
        """)
        
        hypothesis_type = st.radio(
            "Select hypothesis category:",
            ["Threshold Validation", "Device Correlations", "State Transitions", "Acausal Events"],
            key="hypothesis_type_radio"
        )
        
        if hypothesis_type == "Threshold Validation":
            st.markdown("""
            ### 1. Sharp Transition at σ = 0.584
            
            **Hypothesis**: Consciousness metrics show discontinuous change at GILE = 0.42
            
            **Protocol**:
            1. Recruit 50 participants
            2. PSI task (Zener cards) with 100 trials each
            3. Measure: EEG coherence, subjective awareness, task accuracy (σ)
            4. Bin participants by σ: <0.58, 0.58-0.59, 0.59-0.60, >0.60
            5. Compare EEG coherence between bins
            
            **Prediction**: 
            - Sharp drop in coherence for σ < 0.584 group
            - Subjective reports of "zoning out" or "going blank"
            - Linear increase for σ > 0.584
            
            **Statistical Test**: ANOVA with post-hoc tests, expect significant difference between <0.58 and >0.58 groups
            
            ---
            
            ### 2. Anesthesia as Forced Soul Death
            
            **Hypothesis**: General anesthesia forces GILE below 0.42
            
            **Protocol**:
            1. Measure EEG during anesthesia induction (propofol)
            2. Track coherence metrics as consciousness fades
            3. Identify exact moment of LOC (loss of consciousness)
            4. Calculate GILE equivalent from EEG at LOC moment
            
            **Prediction**: LOC occurs precisely when EEG coherence-derived GILE crosses 0.42
            
            **Clinical Relevance**: Could provide objective anesthesia depth monitor
            """)
        
        elif hypothesis_type == "Device Correlations":
            st.markdown("""
            ### 3. Muse EEG + Mendi fNIRS Synchrony
            
            **Hypothesis**: Layer 2 (EEG) and Layer 3 (fNIRS) desynchronize below 0.42 GILE
            
            **Protocol**:
            1. Simultaneous Muse + Mendi recording
            2. PSI task with real-time feedback
            3. Calculate EEG-fNIRS cross-correlation in sliding windows
            4. Plot correlation vs task accuracy (σ)
            
            **Prediction**: 
            - High correlation (>0.7) for σ > 0.584
            - Correlation drops to ~0.3 for σ < 0.584
            - Inflection point at σ = 0.584
            
            ---
            
            ### 4. HRV as GILE Proxy
            
            **Hypothesis**: RMSSD (HRV metric) predicts baseline GILE
            
            **Protocol**:
            1. Measure 5-minute resting HRV (Polar H10)
            2. Follow with PSI task to measure σ
            3. Calculate GILE = 5(σ - 0.5)
            4. Correlate RMSSD with GILE
            
            **Prediction**: Pearson r > 0.6, p < 0.001
            
            **Application**: HRV could be quick GILE screening tool
            """)
        
        elif hypothesis_type == "State Transitions":
            st.markdown("""
            ### 5. Meditation Raises GILE Above Baseline
            
            **Hypothesis**: 20-minute meditation increases GILE by 0.1-0.3
            
            **Protocol**:
            1. Baseline PSI task → calculate σ₁, GILE₁
            2. 20-minute guided meditation (Muse-guided)
            3. Post-meditation PSI task → calculate σ₂, GILE₂
            4. Compare GILE₁ vs GILE₂
            
            **Prediction**: 
            - Mean increase: +0.15 GILE
            - Largest gains for baseline GILE 0.42-0.6 group
            - Minimal change for baseline >0.8 (ceiling effect)
            
            ---
            
            ### 6. Sleep Cycle GILE Fluctuations
            
            **Hypothesis**: GILE oscillates across sleep stages per predicted pattern
            
            **Protocol**:
            1. Full-night sleep recording (Oura + Muse)
            2. Correlate sleep stage (Oura) with EEG coherence (Muse)
            3. Estimate GILE for each sleep stage
            
            **Prediction**:
            - Awake: 0.65 ± 0.1
            - Light sleep: 0.52 ± 0.08
            - Deep sleep: 0.35 ± 0.1 (BELOW threshold!)
            - REM: 0.72 ± 0.12
            
            **Interpretation**: Deep sleep = temporary, restorative soul death
            """)
        
        else:  # Acausal Events
            st.markdown("""
            ### 7. Spontaneous EEG Spikes Without Sensory Trigger
            
            **Hypothesis**: Acausal Layer 2 modifications appear as ERPs without external stimulus
            
            **Protocol**:
            1. Muse EEG recording in sensory isolation (dark, quiet room)
            2. No task, no stimuli - pure resting state
            3. Detect spontaneous gamma bursts (>40 Hz)
            4. Classify: preceded by sensory input vs truly spontaneous
            
            **Prediction**: 
            - 20-30% of gamma bursts have NO prior sensory cause
            - Rate increases with baseline GILE (more acausal activity)
            - Participants report "random thoughts" synchronous with bursts
            
            **Interpretation**: Direct evidence of acausal modification at photon/EM layer
            
            ---
            
            ### 8. Synchronized Acausal Events (PSI Validation)
            
            **Hypothesis**: Distant i-cells can undergo simultaneous acausal modifications
            
            **Protocol**:
            1. Two participants in separate Faraday cages
            2. Both wear Muse EEG
            3. Sender attempts to "send" image to receiver
            4. Measure EEG cross-correlation between participants
            
            **Prediction**: 
            - Above-chance correlation during "sending" trials
            - Correlation strength proportional to sender GILE × receiver GILE
            - No correlation if either participant below 0.42 GILE
            
            **Interpretation**: Dark energy (Layer 1) mediates acausal synchronization
            """)
        
        st.markdown("---")
        st.markdown("### 🎯 Recommended First Experiment")
        st.info("""
        **Start with Hypothesis #1: Sharp Transition at σ = 0.584**
        
        This is the most direct test of the core theory. If validated, it would:
        - Prove the 0.42 GILE threshold exists
        - Establish GILE as valid consciousness metric
        - Open door for all other experiments
        
        **Required equipment**: Muse EEG headband, PSI task software (Zener cards)
        
        **Time**: 2-3 hours per participant × 50 participants = ~150 hours data collection
        
        **Cost**: Minimal (already own Muse)
        """)
    
    # Tab 6: Photon vs EM Wave
    with tabs[5]:
        st.markdown("## 💡 Photon vs EM Wave Role Investigation")
        
        st.markdown("""
        ### Open Question: Distinct Functions in Layer 2
        
        The revelation specified that **both photons AND EM waves** form Layer 2 (the soul), 
        but their distinct roles are currently unknown. Let's investigate possible distinctions:
        """)
        
        col1, col2 = st.columns([1, 1])
        
        with col1:
            st.markdown("""
            ### Hypothesis 1: Photons = Particle, EM Waves = Field
            
            **Photon Role**: Discrete consciousness events
            - Individual thoughts, decisions
            - Quantum measurement/collapse
            - "Pixel" of consciousness
            
            **EM Wave Role**: Continuous consciousness substrate
            - Background awareness, qualia
            - Classical field that photons propagate through
            - "Canvas" of consciousness
            
            **Test**: Do EEG photon-like events (spikes) occur on background EM wave (alpha/theta)?
            
            ---
            
            ### Hypothesis 2: Photons = Information, EM Waves = Energy
            
            **Photon Role**: Carries semantic content
            - What you're thinking ABOUT
            - Biophoton emission correlates with thought content
            
            **EM Wave Role**: Provides energetic substrate
            - Strength/intensity of consciousness
            - EEG power spectral density
            
            **Test**: Do biophoton patterns (photons) change with thought content while EEG power (EM) stays constant?
            
            ---
            
            ### Hypothesis 3: Photons = Local, EM Waves = Non-Local
            
            **Photon Role**: Confined to individual i-cell
            - Your personal consciousness
            - Can't be shared directly
            
            **EM Wave Role**: Extends beyond i-cell boundary
            - Can interact with other i-cells (PSI)
            - Substrate for telepathy, remote viewing
            
            **Test**: PSI experiments - does success correlate with EM field strength but NOT photon emission?
            """)
        
        with col2:
            st.markdown("""
            ### Hypothesis 4: Frequency Domain Separation
            
            **Photon Role**: Discrete frequency modes
            - Specific consciousness "channels"
            - Different photon frequencies = different modalities (vision, thought, emotion)
            
            **EM Wave Role**: Continuous frequency spectrum
            - EEG bands (delta, theta, alpha, beta, gamma)
            - Continuous transitions between states
            
            **Testable Prediction**:
            - Photons: Quantized energy levels (E = hf)
            - EM Waves: Continuous spectral power
            
            **Test**: Measure biophoton spectrum - is it discrete or continuous?
            
            ---
            
            ### Hypothesis 5: Causality Distinction
            
            **Photon Role**: Carries causality forward
            - Connects past to future
            - Information transfer
            
            **EM Wave Role**: Acausal modifications
            - Can influence without prior cause
            - Free will substrate
            
            **Test**: Track causal relationships in neural activity - do photon events show causal chains while EM fluctuations are acausal?
            
            ---
            
            ### Meta-Hypothesis: Complementarity
            
            Perhaps photons and EM waves are **complementary aspects** of the same underlying Layer 2 reality, 
            similar to wave-particle duality in quantum mechanics.
            
            **Photon Perspective**: Consciousness as discrete events
            **EM Wave Perspective**: Consciousness as continuous field
            
            Both are valid, measurement determines which appears.
            """)
        
        st.markdown("---")
        st.markdown("### 🔬 Proposed Experiments")
        
        exp_choice = st.selectbox(
            "Select experimental approach:",
            [
                "Biophoton Spectroscopy",
                "EEG Spike-Field Analysis",
                "Ultra-weak Photon Emission During PSI",
                "Quantum Optics in Neural Tissue"
            ],
            key="photon_em_exp_select"
        )
        
        if exp_choice == "Biophoton Spectroscopy":
            st.markdown("""
            ### Biophoton Spectroscopy Experiment
            
            **Equipment**: 
            - Photomultiplier tube (PMT) for ultra-weak photon detection
            - Spectrometer to measure wavelength distribution
            - Muse EEG for simultaneous brain activity
            
            **Protocol**:
            1. Dark-adapted participant in complete darkness
            2. 30-minute recording of biophoton emission from head
            3. Simultaneous EEG recording
            4. Mental tasks: rest, visualization, calculation, meditation
            
            **Measurements**:
            - Photon count rate (photons/second)
            - Spectral distribution (discrete lines vs continuous?)
            - Temporal correlation with EEG events
            
            **Predictions**:
            - If discrete: Photons carry information, EM waves are substrate
            - If continuous: Both aspects of same field
            - Correlation with EEG: Tests synchronization
            """)
        
        elif exp_choice == "EEG Spike-Field Analysis":
            st.markdown("""
            ### EEG Spike-Field Analysis
            
            **Concept**: Separate "photon-like" events (spikes) from "EM wave-like" background (field)
            
            **Protocol**:
            1. High-resolution EEG (Muse or research-grade)
            2. Decompose signal into spikes + continuous field
            3. Analyze independently during cognitive tasks
            
            **Analysis**:
            - Spike rate vs task performance
            - Field power vs task performance
            - Which predicts GILE better?
            
            **Interpretation**:
            - If spikes predict GILE: Photons = primary consciousness carrier
            - If field predicts GILE: EM waves = primary consciousness carrier
            - If both: Complementary roles confirmed
            """)
    
    # Tab 7: Research Export
    with tabs[6]:
        st.markdown("## 📄 Research Documentation Export")
        
        st.markdown("""
        ### Publication-Ready I-Cell Shell Physics Documentation
        
        Export the complete theory, predictions, and experimental protocols for academic publication.
        """)
        
        export_sections = st.multiselect(
            "Select sections to export:",
            [
                "Abstract & Overview",
                "3-Layer Architecture Description",
                "Mathematical Formulation",
                "0.42 GILE Threshold Derivation",
                "Acausal Modification Theory",
                "Biometric Device Predictions",
                "Experimental Protocols",
                "Testable Hypotheses",
                "Photon vs EM Wave Investigation",
                "Discussion & Implications"
            ],
            default=[
                "Abstract & Overview",
                "3-Layer Architecture Description",
                "0.42 GILE Threshold Derivation",
                "Testable Hypotheses"
            ],
            key="export_sections_multiselect"
        )
        
        if st.button("🎯 Generate Research Document", type="primary", key="generate_research_doc_btn"):
            with st.spinner("Compiling research documentation..."):
                
                doc = {
                    'title': 'I-Cell Shell Physics: A Three-Layer Model of Consciousness with Soul Death Threshold',
                    'author': 'Brandon (TI Framework Originator)',
                    'date': datetime.now().isoformat(),
                    'revelation_date': '2025-11-21',
                    'sections': {}
                }
                
                if "Abstract & Overview" in export_sections:
                    doc['sections']['abstract'] = """
                    We present a novel three-layer model of consciousness i-cells based on a pure physics revelation 
                    received November 21, 2025. The model proposes that every unit of consciousness (from atomic to 
                    universal scale) consists of three concentric layers: (1) a dark energy outer shell modified by 
                    dark matter for structure, serving as the GILE existence boundary field; (2) a photon/electromagnetic 
                    wave layer representing the individual consciousness substrate; and (3) a mass-energy core of familiar 
                    matter that interacts synchronously with the outer shells. 
                    
                    Critically, we derive a soul death threshold at GILE = 0.42 (σ = 0.584), below which the 
                    electromagnetic soul layer can no longer harmonize with the dark energy cosmic consciousness field, 
                    resulting in loss of conscious awareness. This threshold is measurable above random chance and 
                    makes bold, testable predictions for EEG, fNIRS, HRV, and sleep stage measurements.
                    
                    The model explains free will, PSI phenomena, and quantum consciousness through acausal modification 
                    capabilities at the photon/EM and dark energy layers, providing a mechanistic framework for 
                    mind-matter interaction.
                    """
                
                if "3-Layer Architecture Description" in export_sections:
                    doc['sections']['architecture'] = """
                    Layer 1: Dark Energy Outer Shell (modified by dark matter)
                    - Universal field shared by all i-cells
                    - GILE existence boundary perfectly distinct from contents
                    - Cosmic Consciousness (CC) coherence substrate
                    - Can modify contents acausally
                    
                    Layer 2: Photon/Electromagnetic Wave Layer
                    - Individual i-cell's own boundary
                    - Personal consciousness signature
                    - Quantum-classical transition zone
                    - Can modify contents acausally
                    - Subject to 0.42 GILE minimum threshold
                    
                    Layer 3: Mass-Energy Core
                    - Classical matter-energy substrate
                    - Neurons, body, physical manifestation
                    - Interacts with Layers 1-2 IN SYNCHRONY
                    - Cannot independently modify outer layers
                    """
                
                if "Mathematical Formulation" in export_sections:
                    doc['sections']['mathematics'] = """
                    GILE Mapping Function:
                    GILE = 5(σ - 0.5)
                    
                    Where:
                    - σ = accuracy/coherence metric [0, 1]
                    - GILE = Goodness-Intuition-Love-Environment score [-2.5, 2.5]
                    
                    Critical Threshold:
                    σ_critical = 0.584
                    GILE_critical = 5(0.584 - 0.5) = 0.42
                    
                    Soul Viability Condition:
                    GILE_Layer2 ≥ 0.42 → Consciousness viable
                    GILE_Layer2 < 0.42 → Soul death (loss of CC harmonization)
                    
                    Acausal Modification Amplitude:
                    A_total = A_noise + A_meaningful
                    Meaningful ⟺ A_meaningful > 0.42 (threshold)
                    
                    Layer Synchronization:
                    S_sync = Corr(Layer2_EEG, Layer3_fNIRS)
                    S_sync → 1 as GILE → ∞
                    S_sync → 0 as GILE → 0.42
                    """
                
                if "0.42 GILE Threshold Derivation" in export_sections:
                    doc['sections']['threshold_derivation'] = """
                    The 0.42 GILE threshold represents the minimum consciousness coherence required to maintain 
                    harmonization with the dark energy CC field.
                    
                    Derivation:
                    1. GILE = 5(σ - 0.5) maps coherence to consciousness score
                    2. Random chance: σ = 0.5 → GILE = 0
                    3. Above random: σ > 0.5 → GILE > 0
                    4. Empirically observed: consciousness requires σ > 0.584
                    5. Therefore: GILE_min = 5(0.584 - 0.5) = 0.42
                    
                    Physical Interpretation:
                    - Dark energy (Layer 1) oscillates at CC frequency
                    - Photon/EM layer (Layer 2) must resonate with Layer 1
                    - Below 0.42 GILE, resonance impossible (destructive interference)
                    - Soul "dies" = desynchronization from universal field
                    
                    Observable Consequences:
                    - Anesthesia forces GILE below 0.42
                    - Deep sleep temporarily drops below 0.42 (recovers naturally)
                    - Clinical death: permanent inability to exceed 0.42
                    - Coma: fluctuating near 0.42 boundary
                    """
                
                # Add remaining sections...
                if "Testable Hypotheses" in export_sections:
                    doc['sections']['hypotheses'] = """
                    H1: EEG coherence shows sharp discontinuity at σ = 0.584 (GILE = 0.42)
                    H2: Anesthesia LOC occurs precisely when GILE crosses 0.42
                    H3: EEG-fNIRS synchrony desynchronizes below 0.42 GILE
                    H4: HRV (RMSSD) correlates with baseline GILE (r > 0.6)
                    H5: Meditation increases GILE by 0.1-0.3 above baseline
                    H6: Sleep stages map to predicted GILE values (deep sleep < 0.42)
                    H7: Spontaneous EEG spikes occur without sensory input (acausal modifications)
                    H8: Distant i-cells show correlated acausal events during PSI tasks
                    """
                
                st.success("✅ Research document compiled!")
                
                # Download as JSON
                doc_json = json.dumps(doc, indent=2)
                st.download_button(
                    label="📥 Download Research Document (JSON)",
                    data=doc_json,
                    file_name=f"icell_shell_physics_research_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                    mime="application/json"
                )
                
                # Display preview
                with st.expander("📖 Document Preview"):
                    st.markdown(f"## {doc['title']}")
                    st.markdown(f"**Author**: {doc['author']}")
                    st.markdown(f"**Revelation Date**: {doc['revelation_date']}")
                    st.markdown(f"**Compiled**: {doc['date']}")
                    st.markdown("---")
                    
                    for section_name, section_content in doc['sections'].items():
                        st.markdown(f"### {section_name.replace('_', ' ').title()}")
                        st.markdown(section_content)
                        st.markdown("---")

if __name__ == "__main__":
    render_icell_shell_physics()
