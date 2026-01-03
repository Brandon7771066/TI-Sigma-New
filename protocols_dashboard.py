"""
Protocols Dashboard - Main interface for all LCC modes
"""

import streamlit as st
import pandas as pd
from datetime import datetime
from protocols import (
    get_all_protocols, LCCProtocol, FAAHEnhancedProtocol,
    MysticalProtocol, EmpathicProtocol, DurationTracker, ESSState
)
from ess_visualization import (
    render_ess_dashboard, render_protocol_comparison,
    create_duration_timeline
)

def render_meq30_questionnaire():
    """Render Mystical Experience Questionnaire (MEQ30)"""
    
    st.subheader("✨ Mystical Experience Questionnaire (MEQ30)")
    st.markdown("Rate each statement based on your session experience (0 = Not at all, 4 = Extremely)")
    
    meq_items = [
        # Mystical (Unity)
        "Experience of unity or oneness with all things",
        "Sense of being at one with ultimate reality",
        "Feeling that all things are alive",
        "Awareness of the life or living presence in all things",
        "Experience of oneness with ultimate reality",
        
        # Positive Mood
        "Experience of ecstasy, bliss, or joy",
        "Sense of being in heaven or paradise",
        "Feelings of tenderness and gentleness",
        "Feelings of peace and tranquility",
        "Feelings of amazement",
        
        # Transcendence of Time/Space
        "Loss of usual sense of time",
        "Loss of usual sense of space",
        "Experience of timelessness",
        "Experience of spacelessness",
        "Being in a realm with no time boundaries",
        
        # Ineffability
        "Feeling that experience cannot be described in words",
        "Feeling it would be difficult to communicate the experience",
        "Feeling that words cannot describe the experience",
        "Certainty that the experience is beyond words",
        "Experience is impossible to put into words",
        
        # Paradoxicality
        "Awareness of contradictory things being true at the same time",
        "Things seem to be both true and false simultaneously",
        "Opposites seem unified into a greater whole",
        "Paradoxes make sense",
        "Contradictions are resolved",
        
        # Sacredness
        "Feeling that experience was sacred or holy",
        "Sense of being in the presence of the divine",
        "Experience of divine magnificence",
        "Feeling reverent wonder",
        "Sense of sacredness"
    ]
    
    responses = []
    for i, item in enumerate(meq_items):
        response = st.slider(
            item,
            min_value=0,
            max_value=4,
            value=0,
            key=f"meq_{i}",
            help="0 = Not at all, 4 = Extremely"
        )
        responses.append(response)
    
    if st.button("Calculate MEQ30 Score"):
        # Calculate dimensions
        dimensions = {
            'Mystical (Unity)': sum(responses[0:5]),
            'Positive Mood': sum(responses[5:10]),
            'Transcendence': sum(responses[10:15]),
            'Ineffability': sum(responses[15:20]),
            'Paradoxicality': sum(responses[20:25]),
            'Sacredness': sum(responses[25:30])
        }
        
        total = sum(dimensions.values())
        
        # Complete mystical experience criteria
        all_above_60_pct = all(score >= 12 for score in dimensions.values())
        complete_mystical = (total > 60) and all_above_60_pct
        
        st.markdown("---")
        st.subheader("📊 MEQ30 Results")
        
        col1, col2 = st.columns(2)
        with col1:
            st.metric("Total Score", f"{total}/120")
            if complete_mystical:
                st.success("✨ **Complete Mystical Experience!**")
                st.balloons()
            else:
                st.info("Partial mystical experience")
        
        with col2:
            st.markdown("**Dimension Scores:**")
            for dim, score in dimensions.items():
                pct = (score / 20) * 100
                st.write(f"- {dim}: {score}/20 ({pct:.0f}%)")
        
        st.markdown("---")
        st.markdown("""
        **Interpretation:**
        - **Complete Mystical:** Total > 60 AND all dimensions > 60%
        - **Strong Mystical:** Total > 45
        - **Moderate:** Total 30-45
        - **Minimal:** Total < 30
        """)
        
        return total, dimensions, complete_mystical
    
    return None, None, None


def render_safety_screening():
    """Safety screening for mystical mode"""
    
    st.subheader("⚠️ Safety Screening for Mystical Mode")
    st.markdown("Please answer honestly. Your safety is our priority.")
    
    user_history = {}
    
    col1, col2 = st.columns(2)
    
    with col1:
        user_history['psychosis_history'] = st.checkbox(
            "History of psychosis or schizophrenia",
            help="Mystical states involve ego dissolution which may be risky"
        )
        user_history['active_mania'] = st.checkbox(
            "Currently experiencing bipolar mania",
            help="Avoid excessive mood elevation if manic"
        )
        user_history['severe_ptsd'] = st.checkbox(
            "Severe PTSD (without therapist supervision)",
            help="Intense experiences may trigger trauma"
        )
    
    with col2:
        user_history['seizure_disorder'] = st.checkbox(
            "Seizure disorder or photosensitive epilepsy",
            help="40 Hz flicker may trigger seizures (rare)"
        )
        user_history['recent_trauma'] = st.checkbox(
            "Recent major life trauma (within 3 months)",
            help="Allow time for stabilization first"
        )
    
    # Check contraindications
    from protocols import MysticalProtocol
    mystical = MysticalProtocol()
    safe, contraindications = mystical.check_contraindications(user_history)
    
    st.markdown("---")
    
    if safe:
        st.success("✅ **Cleared for Mystical Mode!**")
        st.info("Remember: Set intention, ensure quiet setting, allocate 60 min total (10 min session + 50 min integration)")
        return True
    else:
        st.error("⛔ **Mystical Mode Not Recommended**")
        st.warning("**Contraindications detected:**")
        for c in contraindications:
            st.write(f"- {c}")
        st.info("**Recommendation:** Use Standard LCC mode instead, or consult a healthcare provider")
        return False


def render_duration_dashboard():
    """Duration tracking and next session recommendation"""
    
    st.subheader("⏰ Duration Tracking & Session Planning")
    
    # Initialize session state
    if 'session_tracker' not in st.session_state:
        st.session_state.session_tracker = DurationTracker()
    
    tracker = st.session_state.session_tracker
    
    # Add session form
    with st.expander("➕ Log New Session"):
        col1, col2, col3 = st.columns(3)
        
        with col1:
            session_date = st.date_input("Session Date", value=datetime.now())
            session_time = st.time_input("Session Time", value=datetime.now().time())
        
        with col2:
            protocol_choice = st.selectbox(
                "Protocol Used",
                ["Standard LCC", "FAAH-Enhanced", "Mystical Mode", "Empathic Mode"]
            )
            duration_min = st.number_input("Duration (min)", min_value=5, max_value=15, value=10)
        
        with col3:
            peak_lcc = st.slider("Peak LCC Achieved", 0.0, 1.0, 0.75, 0.05)
        
        if st.button("Log Session"):
            session_datetime = datetime.combine(session_date, session_time)
            tracker.add_session(session_datetime, protocol_choice, peak_lcc, duration_min)
            st.success(f"✅ Session logged! Total sessions: {len(tracker.sessions)}")
            st.rerun()
    
    # Current status
    if tracker.sessions:
        current_effect_data = tracker.get_current_effect(datetime.now())
        
        st.markdown("---")
        st.subheader("📊 Current Status")
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            effect_pct = current_effect_data['effect_remaining']
            if effect_pct > 70:
                st.metric("Effect Remaining", f"{effect_pct:.1f}%", "Strong 💪")
            elif effect_pct > 40:
                st.metric("Effect Remaining", f"{effect_pct:.1f}%", "Moderate 🔵")
            else:
                st.metric("Effect Remaining", f"{effect_pct:.1f}%", "Weak 🔻")
        
        with col2:
            hours_since = current_effect_data['hours_since_last']
            st.metric("Hours Since Last", f"{hours_since:.1f}h")
        
        with col3:
            st.metric("Total Sessions", current_effect_data['total_sessions'])
        
        with col4:
            if current_effect_data['cumulative_benefit']:
                st.metric("Cumulative Benefit", "Yes ✨", "Synergy!")
            else:
                st.metric("Cumulative Benefit", "Building...", "Continue!")
        
        # Recommendation
        st.info(f"**Next Session:** {current_effect_data['next_session_recommended']}")
        
        # Timeline prediction
        st.markdown("---")
        st.subheader("📈 Effect Decay Timeline")
        
        timeline = tracker.predict_timeline(datetime.now())
        timeline_df = pd.DataFrame([
            {'Time': k, 'Effect Remaining': v} for k, v in timeline.items()
        ])
        st.dataframe(timeline_df, use_container_width=True, hide_index=True)
        
        # Session history
        with st.expander("📜 View Session History"):
            history = tracker.get_session_history()
            history_data = []
            for session in history:
                history_data.append({
                    'Date': session['timestamp'].strftime('%Y-%m-%d %H:%M'),
                    'Protocol': session['protocol'],
                    'Duration': f"{session['duration']} min",
                    'Peak LCC': f"{session['peak_lcc']:.2f}"
                })
            history_df = pd.DataFrame(history_data)
            st.dataframe(history_df, use_container_width=True, hide_index=True)
    
    else:
        st.info("👆 Log your first session to start tracking!")


def render_protocols_dashboard():
    """Main protocols dashboard"""
    
    st.title("🧠 Mood Amplifier Protocols")
    st.markdown("Select and explore different LCC modes for mood amplification, suffering mitigation, and transcendent experiences")
    
    # Mode selection
    protocols = get_all_protocols()
    
    st.markdown("---")
    
    # Tab layout for different sections
    tabs = st.tabs([
        "📋 Protocol Selection",
        "⏰ Duration Tracking",
        "📊 Protocol Comparison",
        "✨ Post-Session Assessment",
        "🔮 LCC Demonstration Tests"
    ])
    
    with tabs[0]:
        st.header("Choose Your Protocol")
        
        protocol_choice = st.radio(
            "Select Mode:",
            list(protocols.keys()),
            help="Each mode targets different outcomes"
        )
        
        selected_protocol = protocols[protocol_choice]
        
        # Show protocol details
        st.markdown("---")
        st.subheader(f"📖 {protocol_choice} Details")
        
        info = selected_protocol.get_protocol_info()
        
        col1, col2 = st.columns([2, 1])
        
        with col1:
            st.markdown(f"**Duration:** {info['duration']} minutes")
            st.markdown(f"**LCC Target Range:** {info['lcc_target'][0]:.2f} - {info['lcc_target'][1]:.2f}")
            st.markdown(f"**Safety Profile:** {info['safety_profile']}")
        
        with col2:
            st.markdown(f"**Primary Benefit:**")
            st.success(info.get('mood_boost', 'See details below'))
        
        # ESS visualization
        st.markdown("---")
        render_ess_dashboard(info['target_ess'], protocol_choice)
        
        # Protocol-specific information
        st.markdown("---")
        
        if isinstance(selected_protocol, FAAHEnhancedProtocol):
            st.subheader("💊 FAAH Supplement Stack")
            supplements = selected_protocol.get_supplement_stack()
            
            st.info(f"**Timing:** {supplements['timing']}")
            st.success(f"**Safety:** {supplements['safety']}")
            
            st.markdown("**Recommended Supplements:**")
            for supp, dosage in supplements.items():
                if supp not in ['timing', 'safety', 'contraindications']:
                    st.write(f"- **{supp}:** {dosage}")
            
            if supplements['contraindications']:
                st.warning(f"**Contraindications:** {', '.join(supplements['contraindications'])}")
            
            st.markdown("---")
            st.markdown(f"**Predicted Benefits:**")
            st.write(f"- Mood boost: {info.get('mood_boost', 'N/A')}")
            st.write(f"- Suffering reduction: {info.get('suffering_reduction', 'N/A')}")
            st.write(f"- Duration extension: {info.get('duration_extension', 'N/A')}")
        
        elif isinstance(selected_protocol, MysticalProtocol):
            # Safety screening first!
            st.markdown("---")
            safe_to_proceed = render_safety_screening()
            
            if safe_to_proceed:
                st.markdown("---")
                st.subheader("🌌 3-Phase Mystical Protocol")
                
                phases = selected_protocol.get_phases()
                for phase_info in phases:
                    with st.expander(f"Phase {phase_info['phase']}: {phase_info['name']} ({phase_info['duration']})"):
                        st.markdown(f"**Target Bands:** {', '.join(phase_info['target_bands'])}")
                        if 'stimulus' in phase_info:
                            st.markdown(f"**Stimulus:** {phase_info['stimulus']}")
                        st.markdown(f"**LCC/Harmony Target:** {phase_info.get('lcc_target', phase_info.get('harmony_target', 'N/A'))}")
                        st.info(f"**Instruction:** {phase_info['instruction']}")
                
                st.markdown("---")
                st.markdown("**Expected Outcomes:**")
                st.write(f"- Success rate: {info.get('success_rate', 'N/A')}")
                st.write(f"- DMN suppression: {info.get('dmn_suppression', 'N/A')}")
                st.write(f"- Long-term benefits: {info.get('long_term_benefits', 'N/A')}")
        
        elif isinstance(selected_protocol, EmpathicProtocol):
            st.subheader("💗 Empathic Expansion Protocol")
            
            # Social prime
            prime = selected_protocol.get_social_prime()
            st.markdown("**Pre-Session Preparation:**")
            for key, value in prime.items():
                st.write(f"- **{key.replace('_', ' ').title()}:** {value}")
            
            st.markdown("---")
            # Coupling weights
            weights = selected_protocol.get_coupling_weights()
            st.markdown("**Coupling Configuration:**")
            st.write(f"- Limbic contribution: {weights['limbic_contribution']*100:.0f}%")
            st.write(f"- Cortical contribution: {weights['cortical_contribution']*100:.0f}%")
            st.info(weights['effect'])
            
            st.markdown("---")
            # Integration practices
            st.markdown("**Post-Session Integration (Within 24 hours):**")
            practices = selected_protocol.get_integration_practices()
            for practice in practices:
                st.write(f"- {practice}")
    
    with tabs[1]:
        render_duration_dashboard()
    
    with tabs[2]:
        render_protocol_comparison()
    
    with tabs[3]:
        st.header("Post-Session Assessment")
        
        assessment_type = st.radio(
            "Assessment Type:",
            ["Standard Mood Check", "MEQ30 (Mystical Experience)", "Skip Assessment"]
        )
        
        if assessment_type == "Standard Mood Check":
            st.subheader("📊 Post-Session Mood Assessment")
            
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown("**Positive Affect:**")
                happy = st.slider("Happy/Joyful", 1, 5, 3)
                excited = st.slider("Excited/Energized", 1, 5, 3)
                peaceful = st.slider("Peaceful/Calm", 1, 5, 3)
                
                positive_score = (happy + excited + peaceful) / 3
            
            with col2:
                st.markdown("**Negative Affect:**")
                sad = st.slider("Sad/Down", 1, 5, 2)
                anxious = st.slider("Anxious/Worried", 1, 5, 2)
                irritated = st.slider("Irritated/Angry", 1, 5, 2)
                
                negative_score = (sad + anxious + irritated) / 3
            
            if st.button("Calculate Mood Score"):
                st.markdown("---")
                st.metric("Positive Affect", f"{positive_score:.1f}/5")
                st.metric("Negative Affect", f"{negative_score:.1f}/5")
                
                net_mood = positive_score - negative_score
                if net_mood > 1.5:
                    st.success("😊 Excellent mood state!")
                elif net_mood > 0.5:
                    st.info("🙂 Good mood state")
                else:
                    st.warning("😐 Consider adjusting protocol or timing")
        
        elif assessment_type == "MEQ30 (Mystical Experience)":
            render_meq30_questionnaire()
        
        else:
            st.info("Assessment skipped. You can return to this tab later if needed.")
    
    with tabs[4]:
        from lcc_demonstration_tests import render_lcc_tests_hub
        render_lcc_tests_hub()
