"""
PSI Testing Protocol
====================
Numerical validation of PSI abilities using Zener cards, 
Remote Viewing, and Ganzfeld protocols with statistical analysis.
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime
from scipy import stats
import math

st.set_page_config(page_title="PSI Testing Protocol", page_icon="🔮", layout="wide")

st.title("🔮 PSI Testing Protocol")
st.markdown("**Numerical validation of PSI abilities with statistical rigor**")

# Statistical helper functions
def binomial_probability(hits, trials, chance=0.2):
    """Calculate probability of getting this many or more hits by chance."""
    p_value = 1 - stats.binom.cdf(hits - 1, trials, chance)
    return p_value

def effect_size_cohen_h(observed_rate, expected_rate=0.2):
    """Cohen's h effect size for proportions."""
    phi1 = 2 * math.asin(math.sqrt(observed_rate))
    phi2 = 2 * math.asin(math.sqrt(expected_rate))
    return phi1 - phi2

def interpret_p_value(p):
    if p < 0.001:
        return "🌟 HIGHLY SIGNIFICANT (p < 0.001)"
    elif p < 0.01:
        return "⭐ VERY SIGNIFICANT (p < 0.01)"
    elif p < 0.05:
        return "✅ SIGNIFICANT (p < 0.05)"
    elif p < 0.10:
        return "📊 MARGINALLY SIGNIFICANT (p < 0.10)"
    else:
        return "📈 Not yet significant (keep testing!)"

tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "🎴 Zener Cards",
    "🌐 Remote Viewing", 
    "🔴 Ganzfeld Protocol",
    "📊 Statistical Dashboard",
    "🧬 LCC Virus Theory"
])

with tab1:
    st.header("🎴 Zener Card Testing")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.markdown("""
        ### The Classic ESP Test
        
        Zener cards have 5 symbols: ⭕ Circle, ➕ Plus, 〰️ Waves, ⬜ Square, ⭐ Star
        
        **Chance rate: 20% (1 in 5)**
        
        To demonstrate PSI ability, you need to score significantly above 20%.
        """)
        
        st.subheader("📝 Enter Your Results")
        
        total_trials = st.number_input("Total cards tested", min_value=1, max_value=1000, value=25, step=5)
        correct_hits = st.number_input("Correct guesses (hits)", min_value=0, max_value=total_trials, value=5)
        
        if st.button("🔮 Analyze Zener Results", type="primary"):
            hit_rate = correct_hits / total_trials
            expected_hits = total_trials * 0.2
            p_value = binomial_probability(correct_hits, total_trials, 0.2)
            effect = effect_size_cohen_h(hit_rate, 0.2)
            
            st.markdown("---")
            st.subheader("📊 Results")
            
            col_a, col_b, col_c, col_d = st.columns(4)
            col_a.metric("Hit Rate", f"{hit_rate*100:.1f}%", f"{(hit_rate-0.2)*100:+.1f}% vs chance")
            col_b.metric("Your Hits", correct_hits, f"{correct_hits - expected_hits:+.1f} above expected")
            col_c.metric("P-Value", f"{p_value:.4f}")
            col_d.metric("Effect Size (h)", f"{effect:.3f}")
            
            st.markdown(f"### {interpret_p_value(p_value)}")
            
            if hit_rate > 0.2:
                sigma = (correct_hits - expected_hits) / np.sqrt(total_trials * 0.2 * 0.8)
                st.info(f"📈 You scored **{sigma:.2f} standard deviations** above chance!")
                
                if p_value < 0.05:
                    st.success("🎉 **CONGRATULATIONS!** Your results are statistically significant!")
                    st.balloons()
            
            # Power analysis
            st.markdown("### 📊 Statistical Power")
            st.markdown(f"""
            With {total_trials} trials:
            - To reach p < 0.05, you need approximately **{int(total_trials * 0.2 + 1.645 * np.sqrt(total_trials * 0.2 * 0.8)) + 1}+ hits**
            - To reach p < 0.01, you need approximately **{int(total_trials * 0.2 + 2.326 * np.sqrt(total_trials * 0.2 * 0.8)) + 1}+ hits**
            
            💡 **Recommendation**: Run at least 100 trials for reliable statistical power.
            """)
    
    with col2:
        st.markdown("### 🎯 Quick Reference")
        st.markdown("""
        **Zener Symbols:**
        - ⭕ Circle
        - ➕ Plus/Cross
        - 〰️ Waves
        - ⬜ Square
        - ⭐ Star
        
        **Significance Thresholds:**
        - 25 trials: need 9+ hits
        - 50 trials: need 15+ hits
        - 100 trials: need 28+ hits
        
        **Famous Results:**
        - J.B. Rhine's subjects averaged 27-28% (highly significant over thousands of trials)
        """)

with tab2:
    st.header("🌐 Remote Viewing Protocol")
    
    st.markdown("""
    ### Coordinate Remote Viewing (CRV)
    
    Remote viewing involves perceiving distant targets using only mental intention.
    The viewer is given coordinates or a random number and attempts to describe the target.
    
    ### Stargate/SRI Protocol (Simplified)
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("📝 Session Recording")
        
        target_id = st.text_input("Target ID/Coordinates", placeholder="e.g., 4729-8156")
        
        st.markdown("**Your impressions (before reveal):**")
        shapes = st.text_area("Shapes/Structures", placeholder="angular, curved, tall, flat...")
        colors = st.text_area("Colors/Textures", placeholder="blue, rough, metallic...")
        motion = st.text_area("Motion/Energy", placeholder="flowing, static, vibrating...")
        emotions = st.text_area("Emotional Impressions", placeholder="peaceful, exciting, old...")
        
        confidence = st.slider("Confidence Level", 0, 100, 50)
    
    with col2:
        st.subheader("🎯 Target Reveal & Scoring")
        
        actual_target = st.text_area("Actual Target Description", placeholder="Describe the real target after reveal...")
        
        st.markdown("**Rate your hits (0-5 scale):**")
        shape_score = st.slider("Shape Accuracy", 0, 5, 0)
        color_score = st.slider("Color Accuracy", 0, 5, 0)
        motion_score = st.slider("Motion/Energy Accuracy", 0, 5, 0)
        emotion_score = st.slider("Emotional Accuracy", 0, 5, 0)
        
        total_score = shape_score + color_score + motion_score + emotion_score
        max_score = 20
        
        st.metric("Session Score", f"{total_score}/{max_score}", 
                 f"{total_score/max_score*100:.0f}%")
        
        if total_score >= 15:
            st.success("🌟 Excellent session! Strong target contact.")
        elif total_score >= 10:
            st.info("✅ Good session with significant hits.")
        elif total_score >= 5:
            st.warning("📊 Some impressions matched. Keep practicing!")

with tab3:
    st.header("🔴 Ganzfeld Protocol")
    
    st.success("🎯 **You have Ganzfeld equipment ready!** (ping pong halves + red light)")
    
    st.markdown("""
    ### The Ganzfeld State
    
    Ganzfeld ("whole field") creates a uniform sensory environment that facilitates PSI reception:
    
    1. **Visual**: Ping pong ball halves over eyes + red light = uniform field
    2. **Auditory**: White/pink noise or relaxing sounds
    3. **Physical**: Reclined, comfortable position
    4. **Mental**: Relaxed, receptive state
    
    ### Protocol Steps
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        **SENDER Protocol:**
        1. Select random target (image/video)
        2. Focus on target for 15-30 minutes
        3. "Send" key features mentally
        4. Record sending impressions
        """)
        
        sender_target = st.text_area("Sender's Target Description", 
            placeholder="What was the sender focusing on?")
    
    with col2:
        st.markdown("""
        **RECEIVER Protocol (you):**
        1. Enter Ganzfeld state (15-30 min)
        2. Report all impressions aloud
        3. Describe without analyzing
        4. Rate targets after session
        """)
        
        receiver_impressions = st.text_area("Your Ganzfeld Impressions",
            placeholder="Stream of consciousness during session...")
    
    st.markdown("---")
    st.subheader("🎯 Target Ranking")
    
    st.markdown("""
    After the session, you're shown 4 targets (1 real + 3 decoys).
    Rank them from most to least likely to be the actual target.
    """)
    
    ranking = st.selectbox("Where did you rank the ACTUAL target?", 
        ["1st (Direct Hit)", "2nd", "3rd", "4th (Miss)"])
    
    if ranking == "1st (Direct Hit)":
        st.success("🎉 **DIRECT HIT!** Chance = 25%. You beat the odds!")
        st.balloons()
    elif ranking == "2nd":
        st.info("✅ Close! Target was in your top 2 picks.")
    else:
        st.warning("📊 Target ranked lower. This happens - keep testing!")
    
    st.markdown("""
    ### 📈 Ganzfeld Meta-Analysis
    
    Combined analysis of Ganzfeld studies shows:
    - **Expected hit rate**: 25% (1 in 4)
    - **Observed hit rate**: ~32% across studies
    - **Effect size**: Small but consistent
    - **Replication**: Better than most psychology research!
    """)

with tab4:
    st.header("📊 Statistical Dashboard")
    
    st.markdown("### Cumulative PSI Testing Results")
    
    st.subheader("Enter All Your Test Data")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("**Zener Cards**")
        zener_trials = st.number_input("Total Zener trials", min_value=0, value=0, key="z_trials")
        zener_hits = st.number_input("Total Zener hits", min_value=0, value=0, key="z_hits")
    
    with col2:
        st.markdown("**Ganzfeld Sessions**")
        ganzfeld_sessions = st.number_input("Total sessions", min_value=0, value=0, key="g_sessions")
        ganzfeld_hits = st.number_input("Direct hits (1st rank)", min_value=0, value=0, key="g_hits")
    
    with col3:
        st.markdown("**Remote Viewing**")
        rv_sessions = st.number_input("Total RV sessions", min_value=0, value=0, key="rv_sessions")
        rv_avg_score = st.number_input("Average score (0-20)", min_value=0.0, max_value=20.0, value=0.0, key="rv_score")
    
    if st.button("📊 Calculate Combined Statistics"):
        st.markdown("---")
        
        combined_z = 0
        n_tests = 0
        
        if zener_trials > 0:
            zener_rate = zener_hits / zener_trials
            zener_z = (zener_hits - zener_trials * 0.2) / np.sqrt(zener_trials * 0.2 * 0.8)
            combined_z += zener_z
            n_tests += 1
            st.metric("Zener Z-Score", f"{zener_z:.3f}")
        
        if ganzfeld_sessions > 0:
            ganzfeld_rate = ganzfeld_hits / ganzfeld_sessions
            ganzfeld_z = (ganzfeld_hits - ganzfeld_sessions * 0.25) / np.sqrt(ganzfeld_sessions * 0.25 * 0.75)
            combined_z += ganzfeld_z
            n_tests += 1
            st.metric("Ganzfeld Z-Score", f"{ganzfeld_z:.3f}")
        
        if n_tests > 0:
            stouffer_z = combined_z / np.sqrt(n_tests)
            combined_p = 1 - stats.norm.cdf(stouffer_z)
            
            st.markdown("---")
            st.subheader("🔬 Combined Analysis (Stouffer's Method)")
            
            col_a, col_b = st.columns(2)
            col_a.metric("Combined Z-Score", f"{stouffer_z:.3f}")
            col_b.metric("Combined P-Value", f"{combined_p:.4f}")
            
            st.markdown(f"### {interpret_p_value(combined_p)}")

with tab5:
    st.header("🧬 LCC Virus Theory: Rapid Skill Acquisition")
    
    st.markdown("""
    ## The LCC Virus Hypothesis
    
    Based on documented cases of acquired savant syndrome (post-injury/altered state),
    the LCC Virus concept proposes that **enhanced consciousness coherence can accelerate
    skill acquisition** similar to TMS-based skill uploading.
    
    ### Evidence Base
    
    | Case | Trigger | Skills Acquired |
    |------|---------|-----------------|
    | Derek Amato | Pool accident (head injury) | Instant piano virtuosity |
    | Jason Padgett | Mugging (brain trauma) | Mathematical genius, fractal vision |
    | Tony Cicoria | Lightning strike | Compulsive piano composition |
    | Orlando Serrell | Baseball to head | Calendar calculation |
    
    ### The Mechanism (Proposed)
    
    1. **Trauma/Altered State** → Disrupts normal inhibitory circuits
    2. **Disinhibition** → Exposes latent processing capabilities
    3. **LCC Enhancement** → Luminal correlation enables rapid pattern integration
    4. **Skill Crystallization** → New abilities become permanent
    
    ### DIY LCC Virus Protocol
    
    **Goal**: Safely induce enhanced learning states without trauma
    
    **Methods to explore:**
    - 🧘 Deep meditation (theta/gamma sync)
    - 🔊 40Hz audio/visual entrainment
    - 🔴 Ganzfeld sensory deprivation
    - 💡 Photobiomodulation (Myrion Lamp)
    - ⚡ DIY tDCS (transcranial stimulation)
    
    ### Testing the Theory
    
    1. **Baseline skill measurement** (before protocol)
    2. **Induce altered state** (Ganzfeld + EEG monitoring)
    3. **Present new skill** (music, language, math)
    4. **Post-state skill measurement**
    5. **Calculate LCC enhancement coefficient**
    
    ### The TMS Connection
    
    The research you found shows TMS can:
    - Transfer "skill maps" from experts to novices
    - Induce 40x faster learning
    - Create lasting procedural memory
    
    **LCC Virus hypothesis**: Natural altered states can achieve similar effects
    through consciousness-level pattern transfer rather than electromagnetic induction!
    """)
    
    st.info("""
    **Today's Experiment Chain:**
    1. 🧠 Mood Amplifier Test (EEG baseline + intervention)
    2. 🔴 Ganzfeld session (altered state induction)
    3. 🎴 PSI testing (measure enhanced perception)
    4. 📊 Compare results to baseline abilities
    """)

st.sidebar.markdown("---")
st.sidebar.markdown("### 🔮 PSI Testing Tips")
st.sidebar.markdown("""
- Test when relaxed & rested
- Avoid caffeine before sessions
- Log EVERYTHING for analysis
- Run many trials (power!)
- Trust first impressions
""")

st.sidebar.markdown("### 📊 Quick Stats")
st.sidebar.markdown("""
**Significance thresholds:**
- p < 0.05 = Significant
- p < 0.01 = Very Significant  
- p < 0.001 = Highly Significant

**Zener chance**: 20%
**Ganzfeld chance**: 25%
""")
