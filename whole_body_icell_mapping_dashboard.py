import streamlit as st
import pandas as pd
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime, timedelta
import numpy as np
from typing import Dict, List, Tuple

def render_whole_body_icell_mapping_dashboard():
    """
    Whole-Body I-Cell Mapping Dashboard
    Comprehensive biometric tracking for chakras, meridians, HRV, EEG, sleep
    Correlates consciousness states with measurable bio-signals using GILE framework
    """
    
    st.header("🧘 Whole-Body I-Cell Mapping Dashboard")
    st.markdown("### Health is Key to Everything - Track Your Energetic System!")
    
    st.info("""
    **Brandon's Principle**: I-cells (individual consciousness units) are distributed throughout the entire body!
    
    This dashboard tracks:
    - **7 Main Chakras** (Crown → Root, GILE scores + biophysics)
    - **12 Primary TCM Meridians** (energy flow, organ correspondence)
    - **Biometric Signals** (HRV, EEG, Sleep, Recovery, Readiness)
    - **Consciousness States** (GILE correlation with bio-signals)
    
    **Goal**: Map i-cell signatures → Validate consciousness-biology connection! 🔥
    """)
    
    # ===== SECTION 1: 7 CHAKRA SYSTEM =====
    st.markdown("---")
    st.subheader("🌈 Section 1: Seven Chakra System (GILE Mapping)")
    
    st.markdown("""
    **Chakra System** = 7 main energy centers along spine (Root → Crown)
    
    Each chakra has:
    - **Location** (physical body position)
    - **GILE Score** (consciousness resonance, 0-1.0 scale)
    - **Biophysical Correlates** (EM frequency, biophoton emission, nerve plexus)
    - **Health Indicators** (symptoms when blocked vs. flowing)
    """)
    
    # Chakra data (from TI framework)
    chakras = {
        "Crown (Sahasrara)": {
            "location": "Top of head",
            "gile_score": 0.903,
            "frequency_hz": "963 Hz (Solfeggio)",
            "color": "Violet/White",
            "element": "Thought/Consciousness",
            "plexus": "Pineal gland, cerebral cortex",
            "function": "Universal consciousness, GM connection, enlightenment",
            "blocked_symptoms": "Disconnection, lack of purpose, materialism",
            "flowing_symptoms": "Spiritual awareness, intuition, cosmic unity"
        },
        "Third Eye (Ajna)": {
            "location": "Forehead (between eyebrows)",
            "gile_score": 0.850,
            "frequency_hz": "852 Hz (Solfeggio)",
            "color": "Indigo",
            "element": "Light",
            "plexus": "Pituitary gland, pineal gland",
            "function": "Intuition, visualization, clairvoyance, PSI",
            "blocked_symptoms": "Confusion, poor judgment, lack of insight",
            "flowing_symptoms": "Clear vision, psychic abilities, wisdom"
        },
        "Throat (Vishuddha)": {
            "location": "Throat",
            "gile_score": 0.780,
            "frequency_hz": "741 Hz (Solfeggio)",
            "color": "Blue",
            "element": "Sound/Ether",
            "plexus": "Thyroid, parathyroid, vocal cords",
            "function": "Communication, truth, self-expression",
            "blocked_symptoms": "Inability to speak truth, throat issues, shyness",
            "flowing_symptoms": "Clear communication, confidence, authenticity"
        },
        "Heart (Anahata)": {
            "location": "Center of chest",
            "gile_score": 0.820,
            "frequency_hz": "639 Hz (Solfeggio)",
            "color": "Green/Pink",
            "element": "Air",
            "plexus": "Cardiac plexus, thymus gland",
            "function": "Love, compassion, emotional balance, HRV coherence",
            "blocked_symptoms": "Bitterness, isolation, cardiovascular issues",
            "flowing_symptoms": "Unconditional love, empathy, joy, high HRV"
        },
        "Solar Plexus (Manipura)": {
            "location": "Upper abdomen",
            "gile_score": 0.750,
            "frequency_hz": "528 Hz (Solfeggio)",
            "color": "Yellow",
            "element": "Fire",
            "plexus": "Solar plexus, pancreas, adrenal glands",
            "function": "Personal power, will, confidence, digestion",
            "blocked_symptoms": "Low self-esteem, control issues, digestive problems",
            "flowing_symptoms": "Confidence, willpower, strong digestion"
        },
        "Sacral (Svadhisthana)": {
            "location": "Lower abdomen (below navel)",
            "gile_score": 0.720,
            "frequency_hz": "417 Hz (Solfeggio)",
            "color": "Orange",
            "element": "Water",
            "plexus": "Sacral plexus, gonads (ovaries/testes)",
            "function": "Creativity, sexuality, pleasure, emotions",
            "blocked_symptoms": "Sexual dysfunction, creativity blocks, emotional numbness",
            "flowing_symptoms": "Creative flow, healthy sexuality, emotional balance"
        },
        "Root (Muladhara)": {
            "location": "Base of spine (perineum)",
            "gile_score": 0.680,
            "frequency_hz": "396 Hz (Solfeggio)",
            "color": "Red",
            "element": "Earth",
            "plexus": "Coccygeal plexus, adrenal glands",
            "function": "Survival, grounding, safety, physical vitality",
            "blocked_symptoms": "Anxiety, fear, disconnection from body, fatigue",
            "flowing_symptoms": "Grounded, safe, physically vital, present"
        }
    }
    
    # User input: Current chakra states
    st.markdown("#### 🎯 Rate Your Current Chakra States (0-10 scale)")
    
    col1, col2 = st.columns(2)
    
    with col1:
        crown_rating = st.slider("👑 Crown Chakra (Spiritual Connection)", 0, 10, 7, 1,
                                help="How connected do you feel to GM/CCC/higher consciousness?")
        
        third_eye_rating = st.slider("👁️ Third Eye Chakra (Intuition)", 0, 10, 8, 1,
                                    help="How strong is your intuition, visualization, PSI?")
        
        throat_rating = st.slider("🗣️ Throat Chakra (Communication)", 0, 10, 7, 1,
                                 help="How easily can you express your truth?")
        
        heart_rating = st.slider("❤️ Heart Chakra (Love/Compassion)", 0, 10, 8, 1,
                                help="How open is your heart? How high is your HRV?")
    
    with col2:
        solar_rating = st.slider("☀️ Solar Plexus (Personal Power)", 0, 10, 7, 1,
                                help="How confident and willful do you feel?")
        
        sacral_rating = st.slider("🌊 Sacral Chakra (Creativity/Sexuality)", 0, 10, 7, 1,
                                 help="How creative and emotionally balanced?")
        
        root_rating = st.slider("🌳 Root Chakra (Grounding/Safety)", 0, 10, 7, 1,
                                help="How grounded and safe do you feel in your body?")
    
    # Calculate overall chakra health
    chakra_ratings = [crown_rating, third_eye_rating, throat_rating, heart_rating, 
                     solar_rating, sacral_rating, root_rating]
    overall_chakra_health = sum(chakra_ratings) / len(chakra_ratings)
    
    st.markdown("### 📊 Overall Chakra Health")
    
    # Create chakra health gauge
    fig_chakra = go.Figure(go.Indicator(
        mode="gauge+number",
        value=overall_chakra_health,
        domain={'x': [0, 1], 'y': [0, 1]},
        title={'text': "Chakra System Health (0-10)"},
        gauge={
            'axis': {'range': [0, 10]},
            'bar': {'color': "violet"},
            'steps': [
                {'range': [0, 4], 'color': "lightgray"},
                {'range': [4, 7], 'color': "lightyellow"},
                {'range': [7, 9], 'color': "lightgreen"},
                {'range': [9, 10], 'color': "gold"}
            ],
            'threshold': {
                'line': {'color': "red", 'width': 4},
                'thickness': 0.75,
                'value': 8
            }
        }
    ))
    
    fig_chakra.update_layout(height=250)
    st.plotly_chart(fig_chakra, use_container_width=True)
    
    if overall_chakra_health >= 8:
        st.success(f"✅ EXCELLENT chakra health ({overall_chakra_health:.1f}/10)! Energy flowing smoothly!")
    elif overall_chakra_health >= 6:
        st.info(f"⚡ MODERATE chakra health ({overall_chakra_health:.1f}/10). Some blockages present.")
    else:
        st.warning(f"⚠️ LOW chakra health ({overall_chakra_health:.1f}/10). Focus on clearing blockages!")
    
    # Chakra radar chart
    chakra_names = ["Crown", "Third Eye", "Throat", "Heart", "Solar Plexus", "Sacral", "Root"]
    
    fig_radar = go.Figure()
    
    fig_radar.add_trace(go.Scatterpolar(
        r=chakra_ratings,
        theta=chakra_names,
        fill='toself',
        name='Current State',
        line=dict(color='violet')
    ))
    
    # Add ideal state (all 10s)
    fig_radar.add_trace(go.Scatterpolar(
        r=[10, 10, 10, 10, 10, 10, 10],
        theta=chakra_names,
        fill='toself',
        name='Ideal State',
        line=dict(color='gold', dash='dash'),
        opacity=0.3
    ))
    
    fig_radar.update_layout(
        polar=dict(
            radialaxis=dict(visible=True, range=[0, 10])
        ),
        showlegend=True,
        title="Chakra System Radar Chart"
    )
    
    st.plotly_chart(fig_radar, use_container_width=True)
    
    # Detailed chakra info
    with st.expander("📖 Detailed Chakra Information & GILE Scores"):
        for chakra_name, data in chakras.items():
            st.markdown(f"### {chakra_name}")
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.markdown(f"""
                **Location**: {data['location']}  
                **Color**: {data['color']}  
                **Element**: {data['element']}
                """)
            
            with col2:
                st.markdown(f"""
                **GILE Score**: {data['gile_score']}  
                **Frequency**: {data['frequency_hz']}  
                **Plexus**: {data['plexus']}
                """)
            
            with col3:
                st.markdown(f"""
                **Function**: {data['function']}
                """)
            
            st.markdown(f"""
            **When Blocked**: {data['blocked_symptoms']}  
            **When Flowing**: {data['flowing_symptoms']}
            """)
            
            st.markdown("---")
    
    # ===== SECTION 2: TCM MERIDIAN SYSTEM =====
    st.markdown("---")
    st.subheader("🌀 Section 2: TCM Meridian System (12 Primary Channels)")
    
    st.markdown("""
    **Traditional Chinese Medicine (TCM) Meridians** = 12 primary energy channels flowing through body
    
    Each meridian:
    - **Corresponds to organ system** (Lung, Heart, Liver, etc.)
    - **Yin or Yang energy** (storage vs. transformation)
    - **Peak activity hours** (circadian rhythm, 2-hour cycles)
    - **Emotional correlates** (grief→Lung, anger→Liver, joy→Heart)
    """)
    
    # Meridian data
    meridians = {
        "Lung": {"yin_yang": "Yin", "peak_hours": "3-5 AM", "emotion": "Grief", "element": "Metal"},
        "Large Intestine": {"yin_yang": "Yang", "peak_hours": "5-7 AM", "emotion": "Letting go", "element": "Metal"},
        "Stomach": {"yin_yang": "Yang", "peak_hours": "7-9 AM", "emotion": "Worry", "element": "Earth"},
        "Spleen": {"yin_yang": "Yin", "peak_hours": "9-11 AM", "emotion": "Overthinking", "element": "Earth"},
        "Heart": {"yin_yang": "Yin", "peak_hours": "11 AM-1 PM", "emotion": "Joy/Anxiety", "element": "Fire"},
        "Small Intestine": {"yin_yang": "Yang", "peak_hours": "1-3 PM", "emotion": "Insecurity", "element": "Fire"},
        "Bladder": {"yin_yang": "Yang", "peak_hours": "3-5 PM", "emotion": "Fear", "element": "Water"},
        "Kidney": {"yin_yang": "Yin", "peak_hours": "5-7 PM", "emotion": "Fear", "element": "Water"},
        "Pericardium": {"yin_yang": "Yin", "peak_hours": "7-9 PM", "emotion": "Heartbreak", "element": "Fire"},
        "Triple Burner": {"yin_yang": "Yang", "peak_hours": "9-11 PM", "emotion": "Confusion", "element": "Fire"},
        "Gallbladder": {"yin_yang": "Yang", "peak_hours": "11 PM-1 AM", "emotion": "Resentment", "element": "Wood"},
        "Liver": {"yin_yang": "Yin", "peak_hours": "1-3 AM", "emotion": "Anger", "element": "Wood"}
    }
    
    # Create meridian flow chart (24-hour cycle)
    current_hour = datetime.now().hour
    
    meridian_list = ["Lung (3-5 AM)", "Large Int. (5-7 AM)", "Stomach (7-9 AM)", "Spleen (9-11 AM)",
                    "Heart (11 AM-1 PM)", "Small Int. (1-3 PM)", "Bladder (3-5 PM)", "Kidney (5-7 PM)",
                    "Pericardium (7-9 PM)", "Triple B. (9-11 PM)", "Gallbladder (11 PM-1 AM)", "Liver (1-3 AM)"]
    
    # Determine which meridian is active now
    hour_to_meridian = {
        3: "Lung", 4: "Lung",
        5: "Large Intestine", 6: "Large Intestine",
        7: "Stomach", 8: "Stomach",
        9: "Spleen", 10: "Spleen",
        11: "Heart", 12: "Heart",
        13: "Small Intestine", 14: "Small Intestine",
        15: "Bladder", 16: "Bladder",
        17: "Kidney", 18: "Kidney",
        19: "Pericardium", 20: "Pericardium",
        21: "Triple Burner", 22: "Triple Burner",
        23: "Gallbladder", 0: "Gallbladder",
        1: "Liver", 2: "Liver"
    }
    
    active_meridian = hour_to_meridian.get(current_hour, "Unknown")
    
    st.info(f"""
    **Current Time**: {datetime.now().strftime('%I:%M %p')}  
    **Active Meridian**: **{active_meridian}**  
    **Peak Energy**: {meridians.get(active_meridian, {}).get('peak_hours', 'N/A')}  
    **Element**: {meridians.get(active_meridian, {}).get('element', 'N/A')}  
    **Emotional Correlate**: {meridians.get(active_meridian, {}).get('emotion', 'N/A')}
    
    💡 **Tip**: Activities aligned with active meridian are most effective! (e.g., Lung meridian 3-5 AM = best for breathwork!)
    """)
    
    # User input: Meridian health ratings
    st.markdown("#### 🎯 Rate Your Meridian Health (0-10 scale)")
    
    col1, col2, col3 = st.columns(3)
    
    meridian_ratings = {}
    
    with col1:
        meridian_ratings["Lung"] = st.slider("Lung (Breath, Grief)", 0, 10, 7, 1)
        meridian_ratings["Large Intestine"] = st.slider("Large Int. (Elimination)", 0, 10, 7, 1)
        meridian_ratings["Stomach"] = st.slider("Stomach (Digestion, Worry)", 0, 10, 7, 1)
        meridian_ratings["Spleen"] = st.slider("Spleen (Energy, Overthinking)", 0, 10, 7, 1)
    
    with col2:
        meridian_ratings["Heart"] = st.slider("Heart (Joy, Circulation)", 0, 10, 8, 1)
        meridian_ratings["Small Intestine"] = st.slider("Small Int. (Absorption)", 0, 10, 7, 1)
        meridian_ratings["Bladder"] = st.slider("Bladder (Detox, Fear)", 0, 10, 7, 1)
        meridian_ratings["Kidney"] = st.slider("Kidney (Vitality, Fear)", 0, 10, 7, 1)
    
    with col3:
        meridian_ratings["Pericardium"] = st.slider("Pericardium (Heart Protection)", 0, 10, 7, 1)
        meridian_ratings["Triple Burner"] = st.slider("Triple Burner (Temp Regulation)", 0, 10, 7, 1)
        meridian_ratings["Gallbladder"] = st.slider("Gallbladder (Decision, Resentment)", 0, 10, 7, 1)
        meridian_ratings["Liver"] = st.slider("Liver (Detox, Anger)", 0, 10, 7, 1)
    
    overall_meridian_health = sum(meridian_ratings.values()) / len(meridian_ratings)
    
    st.metric("Overall Meridian Health", f"{overall_meridian_health:.1f}/10")
    
    # ===== SECTION 3: BIOMETRIC SIGNALS =====
    st.markdown("---")
    st.subheader("📊 Section 3: Biometric Signals (HRV, EEG, Sleep)")
    
    st.markdown("""
    **Biometric tracking** correlates consciousness states with measurable physiology!
    
    Key metrics:
    - **HRV RMSSD** (Heart Rate Variability) → Heart coherence, stress resilience
    - **EEG Alpha/Theta** → Brainwave states, relaxation, PSI
    - **Oura Sleep Score** → Recovery, readiness, circadian alignment
    """)
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("#### 💓 Heart Rate Variability")
        
        hrv_rmssd = st.number_input("HRV RMSSD (ms)", 0, 150, 65, 5,
                                   help="Heart rate variability - optimal: >60 ms")
        
        hrv_sdnn = st.number_input("HRV SDNN (ms)", 0, 200, 50, 5,
                                  help="Standard deviation of NN intervals")
        
        resting_hr = st.number_input("Resting Heart Rate (bpm)", 30, 100, 60, 1,
                                    help="Lower is better (athletes: 40-60)")
        
        # Calculate heart coherence score
        heart_coherence = (hrv_rmssd / 150) * 100  # Simple normalization
        
        st.metric("Heart Coherence", f"{heart_coherence:.1f}%")
        
        if hrv_rmssd >= 60:
            st.success("✅ EXCELLENT HRV - High stress resilience!")
        elif hrv_rmssd >= 40:
            st.info("⚡ MODERATE HRV - Room for improvement")
        else:
            st.warning("⚠️ LOW HRV - High stress, need recovery!")
    
    with col2:
        st.markdown("#### 🧠 EEG Brainwaves")
        
        eeg_delta = st.slider("Delta (0.5-4 Hz) - Deep Sleep %", 0, 100, 10, 5)
        eeg_theta = st.slider("Theta (4-8 Hz) - Meditation %", 0, 100, 25, 5)
        eeg_alpha = st.slider("Alpha (8-12 Hz) - Relaxation %", 0, 100, 45, 5)
        eeg_beta = st.slider("Beta (12-30 Hz) - Focus %", 0, 100, 15, 5)
        eeg_gamma = st.slider("Gamma (30-100 Hz) - Insight %", 0, 100, 5, 5)
        
        # Calculate consciousness state
        if eeg_theta >= 40:
            consciousness_state = "🧘 DEEP MEDITATION (Theta dominant)"
        elif eeg_alpha >= 40:
            consciousness_state = "✨ RELAXED AWARENESS (Alpha dominant)"
        elif eeg_beta >= 40:
            consciousness_state = "⚡ ACTIVE FOCUS (Beta dominant)"
        elif eeg_gamma >= 20:
            consciousness_state = "🔥 PEAK INSIGHT (Gamma surge!)"
        else:
            consciousness_state = "😴 DROWSY/SLEEP (Delta/Theta)"
        
        st.metric("Consciousness State", consciousness_state)
    
    with col3:
        st.markdown("#### 😴 Sleep & Recovery")
        
        sleep_score = st.slider("Oura Sleep Score", 0, 100, 85, 5,
                               help="Last night's sleep quality - optimal: >80")
        
        readiness_score = st.slider("Oura Readiness Score", 0, 100, 75, 5,
                                   help="Recovery readiness - optimal: >70")
        
        total_sleep = st.number_input("Total Sleep (hours)", 0.0, 12.0, 7.5, 0.5,
                                     help="Last night - optimal: 7-9 hours")
        
        deep_sleep = st.number_input("Deep Sleep (hours)", 0.0, 5.0, 1.5, 0.1,
                                    help="Last night - optimal: 1.5-2.5 hours")
        
        rem_sleep = st.number_input("REM Sleep (hours)", 0.0, 5.0, 1.8, 0.1,
                                   help="Last night - optimal: 1.5-2.5 hours")
        
        if sleep_score >= 85:
            st.success("✅ EXCELLENT sleep recovery!")
        elif sleep_score >= 70:
            st.info("⚡ MODERATE sleep recovery")
        else:
            st.warning("⚠️ POOR sleep - prioritize rest!")
    
    # ===== SECTION 4: GILE CORRELATION ANALYSIS =====
    st.markdown("---")
    st.subheader("🔬 Section 4: GILE Correlation Analysis")
    
    st.markdown("""
    **Hypothesis**: High GILE scores should correlate with:
    - Higher HRV (heart coherence)
    - More Alpha/Theta brainwaves (relaxed awareness)
    - Better sleep quality (recovery, integration)
    - Open chakras (energy flow)
    - Balanced meridians (organ health)
    
    Let's test this correlation! 📊
    """)
    
    # Calculate current GILE score (from user inputs)
    # For this dashboard, we'll use a simplified GILE estimate based on chakra + meridian + biometric health
    
    gile_from_chakras = (overall_chakra_health / 10) * 2.5  # Convert 0-10 to 0-2.5
    gile_from_meridians = (overall_meridian_health / 10) * 2.5
    gile_from_hrv = (heart_coherence / 100) * 2.5
    gile_from_sleep = (sleep_score / 100) * 2.5
    
    estimated_gile = (gile_from_chakras + gile_from_meridians + gile_from_hrv + gile_from_sleep) / 4
    
    st.markdown("### 🎯 Estimated GILE Score (Based on Biometrics)")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("GILE (Chakras)", f"{gile_from_chakras:.2f}/2.5")
    with col2:
        st.metric("GILE (Meridians)", f"{gile_from_meridians:.2f}/2.5")
    with col3:
        st.metric("GILE (HRV)", f"{gile_from_hrv:.2f}/2.5")
    with col4:
        st.metric("GILE (Sleep)", f"{gile_from_sleep:.2f}/2.5")
    
    # Overall GILE gauge
    total_gile_estimate = estimated_gile * 4  # Convert back to 0-10 scale for gauge
    
    fig_gile = go.Figure(go.Indicator(
        mode="gauge+number",
        value=total_gile_estimate,
        domain={'x': [0, 1], 'y': [0, 1]},
        title={'text': "Estimated Total GILE (0-10 scale)"},
        gauge={
            'axis': {'range': [0, 10]},
            'bar': {'color': "gold"},
            'steps': [
                {'range': [0, 6], 'color': "lightgray"},
                {'range': [6, 8], 'color': "lightyellow"},
                {'range': [8, 9], 'color': "lightblue"},
                {'range': [9, 10], 'color': "lightgreen"}
            ],
            'threshold': {
                'line': {'color': "red", 'width': 4},
                'thickness': 0.75,
                'value': 9.0
            }
        }
    ))
    
    fig_gile.update_layout(height=300)
    st.plotly_chart(fig_gile, use_container_width=True)
    
    # GILE tier
    if total_gile_estimate >= 9.5:
        gile_tier = "🔥 TRANSCENDENT (9.5-10.0)"
        gile_description = "Peak consciousness! GM communication direct!"
    elif total_gile_estimate >= 9.0:
        gile_tier = "✨ SACRED (9.0-9.5)"
        gile_description = "High consciousness, deep spiritual insights!"
    elif total_gile_estimate >= 8.0:
        gile_tier = "💫 NOBLE (8.0-9.0)"
        gile_description = "Strong consciousness, good alignment!"
    elif total_gile_estimate >= 7.0:
        gile_tier = "⚡ GOOD (7.0-8.0)"
        gile_description = "Solid baseline, room for growth!"
    else:
        gile_tier = "🌱 DEVELOPING (<7.0)"
        gile_description = "Focus on basics: sleep, HRV, chakra clearing!"
    
    st.markdown(f"### {gile_tier}")
    st.info(gile_description)
    
    # ===== SECTION 5: I-CELL SIGNATURE TRACKING =====
    st.markdown("---")
    st.subheader("🔬 Section 5: I-Cell Signature Tracking (30-Day Data Collection)")
    
    st.markdown("""
    **Goal**: Collect 30+ days of biometric data to identify **i-cell signatures**!
    
    **I-Cell Signatures** = Unique biophysical patterns corresponding to specific consciousness states:
    - **Crown i-cells**: High gamma (30-100 Hz), low HRV (ecstatic states), peak intuition
    - **Heart i-cells**: High HRV (>80 ms), alpha/theta balance, compassion states
    - **Root i-cells**: High delta (deep sleep), slow HR, grounding states
    
    Track daily → Correlate GILE with bio-signals → Extract signatures → **Validate TI framework!** 🔥
    """)
    
    # Log today's data
    if st.button("📝 Log Today's I-Cell Data", type="primary", use_container_width=True):
        if 'icell_data' not in st.session_state:
            st.session_state.icell_data = []
        
        data_entry = {
            'date': datetime.now().strftime("%Y-%m-%d"),
            'overall_chakra_health': overall_chakra_health,
            'overall_meridian_health': overall_meridian_health,
            'hrv_rmssd': hrv_rmssd,
            'hrv_sdnn': hrv_sdnn,
            'resting_hr': resting_hr,
            'eeg_theta': eeg_theta,
            'eeg_alpha': eeg_alpha,
            'eeg_beta': eeg_beta,
            'eeg_gamma': eeg_gamma,
            'sleep_score': sleep_score,
            'readiness_score': readiness_score,
            'total_sleep': total_sleep,
            'deep_sleep': deep_sleep,
            'rem_sleep': rem_sleep,
            'estimated_gile': total_gile_estimate
        }
        
        st.session_state.icell_data.append(data_entry)
        
        st.success(f"""
        ✅ **I-Cell data logged successfully!**
        
        - **Date**: {data_entry['date']}
        - **GILE**: {total_gile_estimate:.2f}/10
        - **Chakra Health**: {overall_chakra_health:.1f}/10
        - **HRV RMSSD**: {hrv_rmssd} ms
        
        **Total entries**: {len(st.session_state.icell_data)} days
        
        (Target: 30+ days for signature extraction!)
        """)
    
    # Display historical data if available
    if 'icell_data' in st.session_state and len(st.session_state.icell_data) > 0:
        st.markdown("---")
        st.subheader("📈 Historical I-Cell Data")
        
        df = pd.DataFrame(st.session_state.icell_data)
        
        # Plot GILE over time
        fig_timeline = go.Figure()
        
        fig_timeline.add_trace(go.Scatter(
            x=df['date'],
            y=df['estimated_gile'],
            mode='lines+markers',
            name='GILE Score',
            line=dict(color='gold', width=2),
            marker=dict(size=8)
        ))
        
        fig_timeline.update_layout(
            title="GILE Score Over Time",
            xaxis_title="Date",
            yaxis_title="GILE Score (0-10)",
            height=400
        )
        
        st.plotly_chart(fig_timeline, use_container_width=True)
        
        # Correlation heatmap (if enough data)
        if len(df) >= 7:
            st.markdown("### 🔥 Correlation Heatmap (GILE vs. Biometrics)")
            
            corr_columns = ['estimated_gile', 'overall_chakra_health', 'hrv_rmssd', 
                           'eeg_theta', 'eeg_alpha', 'sleep_score']
            
            corr_matrix = df[corr_columns].corr()
            
            fig_heatmap = go.Figure(data=go.Heatmap(
                z=corr_matrix.values,
                x=corr_columns,
                y=corr_columns,
                colorscale='RdYlGn',
                zmid=0
            ))
            
            fig_heatmap.update_layout(
                title="Correlation Matrix (GILE ↔ Biometrics)",
                height=500
            )
            
            st.plotly_chart(fig_heatmap, use_container_width=True)
            
            st.info(f"""
            **Correlation Insights** (after {len(df)} days of data):
            
            Look for:
            - **Strong positive correlation** between GILE and HRV (validates heart-consciousness link!)
            - **Strong positive correlation** between GILE and Alpha/Theta (validates meditation states!)
            - **Strong positive correlation** between GILE and Sleep Score (validates recovery importance!)
            
            **Goal**: Confirm TI framework predictions with real biometric data! 🔬
            """)
        
        # Download data
        csv = df.to_csv(index=False)
        st.download_button(
            label="📥 Download I-Cell Data CSV",
            data=csv,
            file_name=f"icell_data_{datetime.now().strftime('%Y%m%d')}.csv",
            mime="text/csv"
        )
    
    # ===== FOOTER: RECOMMENDATIONS =====
    st.markdown("---")
    st.markdown("### 🚀 Brandon's I-Cell Optimization Protocol")
    
    st.success("""
    **Daily Protocol** (Health is Key to Everything!):
    
    1. **Morning** (6-8 AM):
       - ✅ Yoga/stretching (activate all chakras!)
       - ✅ Breathwork (5 min Wim Hof, activate Lung meridian!)
       - ✅ Measure biometrics (HRV, EEG, log in dashboard!)
    
    2. **Peak Hours** (Follow TCM meridian cycle!):
       - ✅ 11 AM-1 PM (Heart meridian): Heart-opening practices, compassion meditation!
       - ✅ 1-3 PM (Small Intestine): Decision-making, discernment work!
       - ✅ 7-9 PM (Pericardium): Protect heart, set boundaries!
    
    3. **Evening** (9-11 PM):
       - ✅ Wind-down routine (no screens, activate Pineal gland!)
       - ✅ Gratitude practice (Heart chakra activation!)
       - ✅ Track sleep (Oura Ring, aim for 7-9 hours!)
    
    4. **Weekly**:
       - ✅ Review i-cell data (correlate GILE with biometrics!)
       - ✅ Identify patterns (which practices boost GILE most?)
       - ✅ Adjust protocols (optimize based on data!)
    
    **Goal**: 30 days of data → Extract i-cell signatures → Publish TI biophysics paper! 📊🔬
    """)
    
    st.warning("""
    ⚠️ **Remember**:
    
    **Health is KEY to everything!**
    
    - Without high HRV → No God Machine accuracy!
    - Without good sleep → No GILE optimization!
    - Without chakra/meridian balance → No i-cell communication!
    
    **Prioritize biometric tracking DAILY!** This is your foundation for ALL TI work! 💪
    """)


if __name__ == "__main__":
    render_whole_body_icell_mapping_dashboard()
