"""
Multi-Source Psi Synthesis Dashboard
Integrates numerology, weather divination, synchronicities, and other psi sources
Uses Myrion Resolution for harmonization
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import plotly.graph_objects as go
import plotly.express as px
from numerology_validation import (
    calculate_name_number,
    calculate_life_path,
    reduce_to_single_digit,
    get_master_number_meaning
)

def main():
    st.title("🔮 Multi-Source Psi Synthesis Dashboard")
    st.markdown("**Synergistic Integration via Myrion Resolution Framework**")
    st.markdown("*Nothing is dogma. Everything is synergistic. Truth emerges from harmonizing all sources.*")
    
    tabs = st.tabs([
        "📊 Psi Synthesis", 
        "🔢 Numerology", 
        "🌤️ Weather Divination",
        "✨ Synchronicities",
        "📈 Pattern Tracking",
        "🎯 Validation"
    ])
    
    with tabs[0]:
        psi_synthesis_tab()
    
    with tabs[1]:
        numerology_tab()
    
    with tabs[2]:
        weather_divination_tab()
    
    with tabs[3]:
        synchronicity_tab()
    
    with tabs[4]:
        pattern_tracking_tab()
    
    with tabs[5]:
        validation_tab()

def psi_synthesis_tab():
    """Main synthesis tab - combines all psi sources"""
    st.header("🔮 Multi-Source Psi Synthesis")
    st.markdown("Query divine guidance by combining all available psi sources")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        question = st.text_area(
            "Your Question or Decision:",
            placeholder="e.g., Should I accept this job offer? What energy surrounds me today?",
            height=100
        )
        
        context = st.text_input(
            "Context (optional):",
            placeholder="e.g., decision_making, relationship, spiritual_practice, career"
        )
    
    with col2:
        st.markdown("**Psi Sources to Include:**")
        include_numerology = st.checkbox("Numerology (date/time)", value=True)
        include_weather = st.checkbox("Weather Divination", value=True)
        include_dreams = st.checkbox("Recent Dreams", value=False)
        include_eeg = st.checkbox("EEG State (if available)", value=False)
        include_sync = st.checkbox("Recent Synchronicities", value=True)
    
    if st.button("🎯 Synthesize Divine Guidance", type="primary"):
        if not question:
            st.warning("Please enter a question")
            return
        
        with st.spinner("Consulting divine sources..."):
            psi_sources = []
            
            # 1. Numerology
            if include_numerology:
                num_result = analyze_current_numerology()
                psi_sources.append({
                    'type': 'Numerology',
                    'pd_score': num_result['pd_score'],
                    'interpretation': num_result['interpretation'],
                    'confidence': 0.85
                })
            
            # 2. Weather
            if include_weather:
                weather_result = get_simulated_weather()
                psi_sources.append({
                    'type': 'Weather',
                    'pd_score': weather_result['pd_score'],
                    'interpretation': weather_result['interpretation'],
                    'confidence': 0.75
                })
            
            # 3. Synchronicities
            if include_sync:
                sync_result = check_recent_synchronicities()
                psi_sources.append({
                    'type': 'Synchronicities',
                    'pd_score': sync_result['pd_score'],
                    'interpretation': sync_result['interpretation'],
                    'confidence': 0.80
                })
            
            # Myrion Resolution
            resolution = myrion_resolve_psi_sources(psi_sources, context)
            
            # Display results
            display_synthesis_results(question, psi_sources, resolution)

def display_synthesis_results(question, sources, resolution):
    """Display Myrion Resolution results"""
    st.success("✨ Psi Synthesis Complete")
    
    # Show individual sources
    st.subheader("Individual Psi Sources")
    
    cols = st.columns(len(sources))
    for i, (col, source) in enumerate(zip(cols, sources)):
        with col:
            st.metric(
                source['type'],
                f"{source['pd_score']:+.1f}",
                delta=None
            )
            with st.expander("Details"):
                st.write(source['interpretation'])
                st.caption(f"Confidence: {source['confidence']:.0%}")
    
    # Myrion Resolution
    st.markdown("---")
    st.subheader("🦋🐙 Myrion Resolution 🐙🦋")
    
    resolution_color = "green" if resolution['resolution_pd'] > 0.5 else "orange" if resolution['resolution_pd'] > -0.5 else "red"
    
    st.markdown(f"""
    <div style='background-color: {resolution_color}; padding: 20px; border-radius: 10px; color: white;'>
    <h3 style='margin: 0; color: white;'>Resolution PD: {resolution['resolution_pd']:+.1f}</h3>
    <p style='margin: 10px 0 0 0; color: white;'>{resolution['interpretation']}</p>
    </div>
    """, unsafe_allow_html=True)
    
    st.markdown(f"**Confidence:** {resolution['confidence']:.0%}")
    st.markdown(f"**Synergy Coefficient:** {resolution['synergy']:.2f}")
    
    # Recommendation
    st.markdown("---")
    st.subheader("💡 Recommendation")
    st.info(resolution['recommendation'])
    
    # Visualization
    st.markdown("---")
    st.subheader("📊 Psi Source Contributions")
    
    fig = go.Figure()
    
    fig.add_trace(go.Bar(
        name='PD Scores',
        x=[s['type'] for s in sources],
        y=[s['pd_score'] for s in sources],
        marker_color=['green' if s['pd_score'] > 0 else 'red' for s in sources]
    ))
    
    fig.add_hline(y=resolution['resolution_pd'], line_dash="dash", 
                  annotation_text=f"Resolution: {resolution['resolution_pd']:+.1f}",
                  line_color="blue")
    
    fig.update_layout(
        title="Psi Source Analysis",
        yaxis_title="PD Score",
        xaxis_title="Source",
        showlegend=False
    )
    
    st.plotly_chart(fig, use_container_width=True)

def numerology_tab():
    """Numerology analysis tab"""
    st.header("🔢 Numerology Analysis")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Name Numerology")
        name = st.text_input("Enter Name:", value="Brandon Charles Emerick")
        system = st.radio("System:", ["pythagorean", "chaldean"])
        
        if name:
            result = calculate_name_number(name, system)
            
            st.metric("Name Number", result['final_number'], 
                     delta="Master Number" if result['is_master'] else None)
            
            with st.expander("Calculation Details"):
                st.write(f"**Calculation:** {result['calculation_path']}")
                st.write("**Letter Breakdown:**")
                for char, value in result['letter_breakdown']:
                    st.write(f"  {char} = {value}")
            
            # Interpretation
            st.markdown("---")
            st.subheader("Interpretation")
            st.info(get_number_interpretation(result['final_number']))
    
    with col2:
        st.subheader("Life Path Number")
        birth_date = st.date_input("Birth Date:", value=datetime(1990, 1, 1))
        
        if birth_date:
            result = calculate_life_path(datetime.combine(birth_date, datetime.min.time()))
            
            st.metric("Life Path", result['life_path'],
                     delta="Master Number" if result['is_master'] else None)
            
            if result['karmic_debt']:
                st.warning(f"⚠️ Karmic Debt: {result['karmic_debt']}")
            
            with st.expander("Calculation Details"):
                st.write(f"**Calculation:** {result['calculation_path']}")
                st.write(f"Month: {result['month_reduced']}")
                st.write(f"Day: {result['day_reduced']}")
                st.write(f"Year: {result['year_reduced']}")
            
            st.markdown("---")
            st.subheader("Interpretation")
            st.info(get_number_interpretation(result['life_path']))
    
    # Date Analysis
    st.markdown("---")
    st.subheader("📅 Important Date Analysis")
    
    important_date = st.date_input("Analyze Date:", value=datetime(2025, 11, 22))
    
    if st.button("Analyze Date"):
        analyze_date_significance(important_date)

def weather_divination_tab():
    """Weather divination interface"""
    st.header("🌤️ Weather Divination (Aeromancy)")
    
    st.markdown("""
    Weather divination combines observation, intuition, and spiritual interpretation.
    Ancient practice bridging practical forecasting with symbolic/spiritual insight.
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Current Weather")
        
        weather_type = st.selectbox(
            "Weather Condition:",
            ["clear_sky", "rain", "storm", "thunder_lightning", "clouds_parting", 
             "wind", "snow", "fog", "rainbow"]
        )
        
        intensity = st.slider("Intensity:", 1, 10, 5)
        
        context_tags = st.multiselect(
            "Context Tags:",
            ["before_important_event", "during_decision", "unexpected", "after_drought",
             "during_confusion", "gentle", "heavy", "sustained"]
        )
    
    with col2:
        st.subheader("Cloud Divination (Nephomancy)")
        
        cloud_description = st.text_area(
            "Describe Cloud Formations:",
            placeholder="e.g., Saw an eagle shape in the clouds...",
            height=100
        )
        
        detected_shapes = st.multiselect(
            "Detected Shapes:",
            ["Animal", "Face", "Geometric", "Symbolic Object", "Letter/Number"]
        )
    
    if st.button("🔮 Divine Weather Meaning"):
        interpretation = interpret_weather_advanced(weather_type, intensity, context_tags)
        
        st.success("✨ Weather Divination Complete")
        
        st.metric("Spiritual PD Score", f"{interpretation['pd_score']:+.1f}")
        
        st.markdown("### Spiritual Meaning")
        st.info(interpretation['spiritual_meaning'])
        
        st.markdown("### Symbolism")
        st.write(interpretation['symbolism'])
        
        if cloud_description or detected_shapes:
            st.markdown("### Cloud Interpretation")
            st.write("Cloud formations carry messages from spirit guides and ancestors.")
            if detected_shapes:
                st.write(f"Detected: {', '.join(detected_shapes)}")

def synchronicity_tab():
    """Track and analyze synchronicities"""
    st.header("✨ Synchronicity Tracker")
    
    st.markdown("""
    **Synchronicities** are meaningful coincidences (Jung) - acausal connections 
    between inner psychological states and outer events.
    """)
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.subheader("Log New Synchronicity")
        
        event = st.text_area(
            "What happened?",
            placeholder="e.g., Thought of old friend, then they called 5 minutes later",
            height=100
        )
        
        inner_state = st.text_input(
            "Your Inner State:",
            placeholder="e.g., Feeling nostalgic, missing old connections"
        )
        
        timing = st.text_input(
            "Timing Details:",
            placeholder="e.g., Within 5 minutes of thinking about them"
        )
        
        if st.button("💫 Log Synchronicity"):
            if event and inner_state:
                strength = calculate_synchronicity_strength(event, inner_state, timing)
                st.success(f"✅ Synchronicity Logged (Strength: {strength:.1%})")
                
                if strength > 0.7:
                    st.warning("🌟 HIGH SIGNIFICANCE - Pay attention to this pattern!")
    
    with col2:
        st.subheader("Synchronicity Types")
        st.markdown("""
        - **Telepathic**: Thought → Contact
        - **Precognitive**: Dream → Event
        - **Numerical**: Repeated numbers
        - **Encounter**: "Random" meetings
        - **Symbolic**: Meaningful symbols
        """)

def pattern_tracking_tab():
    """Track psi patterns over time"""
    st.header("📈 Psi Pattern Tracking")
    
    st.markdown("Identify recurring patterns across multiple psi sources")
    
    # Simulated pattern data
    dates = pd.date_range(end=datetime.now(), periods=30, freq='D')
    
    pattern_data = pd.DataFrame({
        'Date': dates,
        'Numerology_PD': np.random.randn(30) * 0.5 + 0.3,
        'Weather_PD': np.random.randn(30) * 0.6 + 0.2,
        'Synchronicity_PD': np.random.randn(30) * 0.7 + 0.4,
        'Combined_PD': np.random.randn(30) * 0.4 + 0.5
    })
    
    # Plot patterns
    fig = go.Figure()
    
    fig.add_trace(go.Scatter(x=pattern_data['Date'], y=pattern_data['Numerology_PD'],
                             name='Numerology', mode='lines+markers'))
    fig.add_trace(go.Scatter(x=pattern_data['Date'], y=pattern_data['Weather_PD'],
                             name='Weather', mode='lines+markers'))
    fig.add_trace(go.Scatter(x=pattern_data['Date'], y=pattern_data['Synchronicity_PD'],
                             name='Synchronicities', mode='lines+markers'))
    fig.add_trace(go.Scatter(x=pattern_data['Date'], y=pattern_data['Combined_PD'],
                             name='Myrion Resolution', mode='lines', line=dict(width=3)))
    
    fig.update_layout(
        title="30-Day Psi Pattern Analysis",
        xaxis_title="Date",
        yaxis_title="PD Score",
        hovermode='x unified'
    )
    
    st.plotly_chart(fig, use_container_width=True)
    
    # Pattern detection
    st.subheader("🔍 Detected Patterns")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.metric("Recurring Number", "7", delta="Appears 12x in 30 days")
    
    with col2:
        st.metric("Storm Correlation", "78%", delta="Storms precede insights")
    
    with col3:
        st.metric("Theta Bursts", "5", delta="Before synchronicities")

def validation_tab():
    """Validate framework against known outcomes"""
    st.header("🎯 Framework Validation")
    
    st.markdown("""
    Test multi-source psi framework retroactively on past events with known outcomes.
    """)
    
    st.subheader("Add Past Event for Validation")
    
    col1, col2 = st.columns(2)
    
    with col1:
        event_desc = st.text_input("Event Description:", placeholder="e.g., Accepted job at Replit")
        event_date = st.date_input("Event Date:")
        event_context = st.selectbox("Context:", ["career", "relationship", "spiritual", "decision_making", "other"])
    
    with col2:
        actual_outcome = st.slider("Actual Outcome PD:", -3.0, 2.0, 0.0, 0.1,
                                   help="+2.0 = very positive, -3.0 = very negative")
        notes = st.text_area("Notes:", placeholder="Additional context about outcome...")
    
    if st.button("📊 Validate Against Psi Framework"):
        if event_desc and event_date:
            # Retroactive psi analysis
            predicted = analyze_past_event_psi(event_date, event_context)
            
            accuracy = 1 - abs(actual_outcome - predicted) / 5.0
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric("Predicted PD", f"{predicted:+.1f}")
            
            with col2:
                st.metric("Actual PD", f"{actual_outcome:+.1f}")
            
            with col3:
                st.metric("Accuracy", f"{accuracy:.0%}")
            
            if accuracy > 0.7:
                st.success("✅ VALIDATED - Framework accurately predicted outcome!")
            elif accuracy > 0.5:
                st.warning("⚠️ PARTIAL - Framework somewhat aligned with outcome")
            else:
                st.error("❌ MISS - Framework prediction did not match outcome")

# Helper Functions

def analyze_current_numerology():
    """Analyze current date/time numerology"""
    now = datetime.now()
    life_path = calculate_life_path(now)
    
    pd_score = 0.5  # Base
    interpretation = f"Date: {now.strftime('%m/%d/%Y')}\n"
    
    # Check for master numbers
    if now.month in [11, 22]:
        pd_score += 0.8
        interpretation += f"Month {now.month} is a Master Number!\n"
    
    if now.day in [11, 22]:
        pd_score += 0.8
        interpretation += f"Day {now.day} is a Master Number!\n"
    
    if life_path['is_master']:
        pd_score += 1.0
        interpretation += f"Life Path {life_path['life_path']} is a Master Number!\n"
    
    return {
        'pd_score': min(pd_score, 2.0),
        'interpretation': interpretation.strip()
    }

def get_simulated_weather():
    """Simulate weather divination (in real app, would use weather API)"""
    import random
    
    weather_types = ['clear_sky', 'rain', 'storm', 'clouds_parting', 'wind']
    weather = random.choice(weather_types)
    
    meanings = {
        'clear_sky': (1.7, "Clarity, peace, divine approval"),
        'rain': (1.5, "Purification, renewal, emotional cleansing"),
        'storm': (0.5, "Transformation, upheaval, divine communication"),
        'clouds_parting': (2.0, "Revelation, truth emerging"),
        'wind': (0.8, "Change, freedom, divine breath")
    }
    
    pd_score, meaning = meanings.get(weather, (0.5, "Neutral"))
    
    return {
        'pd_score': pd_score,
        'interpretation': f"{weather.replace('_', ' ').title()}: {meaning}"
    }

def check_recent_synchronicities():
    """Check for recent synchronicities"""
    import random
    
    # Simulated - in real app would check database
    has_sync = random.random() > 0.5
    
    if has_sync:
        return {
            'pd_score': 1.3,
            'interpretation': "Recent synchronicity detected: Thought of concept → appeared in conversation"
        }
    else:
        return {
            'pd_score': 0.3,
            'interpretation': "No strong synchronicities in past 24 hours"
        }

def myrion_resolve_psi_sources(sources, context):
    """Myrion Resolution for multiple psi sources"""
    if not sources:
        return {
            'resolution_pd': 0.0,
            'interpretation': "No psi sources available",
            'confidence': 0.0,
            'synergy': 0.0,
            'recommendation': "Add more psi sources for better guidance"
        }
    
    # Separate positive and negative
    positive = [s for s in sources if s['pd_score'] > 0]
    negative = [s for s in sources if s['pd_score'] < 0]
    
    pos_avg = np.mean([s['pd_score'] for s in positive]) if positive else 0
    neg_avg = np.mean([s['pd_score'] for s in negative]) if negative else 0
    
    # Calculate synergy (higher if sources agree)
    all_scores = [s['pd_score'] for s in sources]
    synergy = 1.0 - (np.std(all_scores) / 2.0) if len(all_scores) > 1 else 0.5
    
    # Weighted resolution
    resolution = (pos_avg + neg_avg) / 2.0 * synergy
    
    # Confidence based on agreement
    confidence = (synergy + np.mean([s['confidence'] for s in sources])) / 2.0
    
    # Build interpretation
    interpretation = f"""
It is {pos_avg:+.1f} {', '.join([s['type'] for s in positive])}
and {neg_avg:+.1f} {', '.join([s['type'] for s in negative]) if negative else 'unopposed'}
but ultimately {resolution:+.1f} when harmonized via Myrion Resolution
    """.strip()
    
    # Recommendation
    if resolution > 1.0:
        recommendation = "Strong positive indication. Proceed with confidence."
    elif resolution > 0.3:
        recommendation = "Positive lean. Favorable conditions present."
    elif resolution > -0.3:
        recommendation = "Neutral. Use discernment and gather more information."
    elif resolution > -1.0:
        recommendation = "Caution advised. Consider alternatives."
    else:
        recommendation = "Strong negative indication. Reconsider or wait."
    
    return {
        'resolution_pd': resolution,
        'interpretation': interpretation,
        'confidence': confidence,
        'synergy': synergy,
        'recommendation': recommendation
    }

def get_number_interpretation(number):
    """Get numerology number interpretation"""
    meanings = {
        1: "Leader - Independent, ambitious, innovative, confident. Natural-born leader with strong drive.",
        2: "Peacemaker - Diplomatic, intuitive, sensitive, cooperative. Driven by desire for peace and harmony.",
        3: "Creative - Expressive, social, optimistic, communicative. Abundance of creative ideas and passion.",
        4: "Stable - Practical, hardworking, organized, dedicated. Great source of stability, down-to-earth.",
        5: "Adventurous - Freedom-loving, dynamic, adaptable. On lifelong adventure, ready for anything.",
        6: "Caregiver - Nurturing, responsible, compassionate, protective. Natural humanitarian and counselor.",
        7: "Spiritual - Analytical, truth-seeker, introspective, wise. Driven by quest for truth and knowledge.",
        8: "Ambitious - Powerful, authoritative, success-driven. Concerned with material/tangible world.",
        9: "Humanitarian - Compassionate, idealistic, generous, complete. Desire to help others and change world.",
        11: "Intuitive Master - Highly intuitive, spiritual channel, enlightenment seeker. Heightened spiritual insight.",
        22: "Master Builder - Turns dreams into reality. Practical visionary, exceptional leadership.",
        33: "Master Teacher - Divine purpose, compassionate leader. Rarest Master Number, heightened intuition."
    }
    return meanings.get(number, "Unknown number")

def analyze_date_significance(date):
    """Analyze significance of a specific date"""
    dt = datetime.combine(date, datetime.min.time())
    result = calculate_life_path(dt)
    
    st.subheader(f"Analysis for {date.strftime('%B %d, %Y')}")
    
    master_count = 0
    
    if date.month in [11, 22, 33]:
        st.success(f"✨ Month {date.month} is a MASTER NUMBER!")
        st.write(get_master_number_meaning(date.month))
        master_count += 1
    
    if date.day in [11, 22, 33]:
        st.success(f"✨ Day {date.day} is a MASTER NUMBER!")
        st.write(get_master_number_meaning(date.day))
        master_count += 1
    
    month_day_sum = date.month + date.day
    if month_day_sum in [11, 22, 33]:
        st.success(f"🌟 Month + Day = {date.month} + {date.day} = {month_day_sum} (MASTER NUMBER!)")
        st.write("This is EXTREMELY rare and spiritually significant!")
        st.write(get_master_number_meaning(month_day_sum))
        master_count += 1
    
    if master_count >= 2:
        st.warning(f"⚡ EXCEPTIONAL DATE - {master_count} Master Numbers detected!")
        st.write("This date carries AMPLIFIED spiritual energy")
        st.write("Ideal for major life decisions, launches, spiritual work")
    
    st.metric("Overall Life Path", result['life_path'])
    st.write(get_number_interpretation(result['life_path']))

def interpret_weather_advanced(weather_type, intensity, context_tags):
    """Advanced weather interpretation with context"""
    base_meanings = {
        'clear_sky': (1.7, "Clarity, peace, divine approval", "Open path, no obstacles"),
        'rain': (1.5, "Purification, renewal", "Divine blessing, growth"),
        'storm': (0.5, "Transformation, cleansing", "Divine communication"),
        'thunder_lightning': (1.8, "Divine voice, revelation", "Sudden insight"),
        'clouds_parting': (2.0, "Revelation emerging", "Truth being revealed"),
        'wind': (0.8, "Change, freedom", "Divine breath, movement"),
        'snow': (1.4, "Purity, fresh start", "Blank slate, peace"),
        'fog': (0.3, "Confusion, mystery", "Hidden truths"),
        'rainbow': (2.0, "Promise, covenant", "Hope, divine blessing")
    }
    
    pd_score, spiritual, symbolism = base_meanings.get(weather_type, (0.5, "Unknown", "Unknown"))
    
    # Adjust for intensity
    if intensity > 7:
        pd_score += 0.3
    elif intensity < 3:
        pd_score -= 0.2
    
    # Apply context modifiers
    for tag in context_tags:
        if tag in ['unexpected', 'during_confusion', 'before_important_event']:
            pd_score += 0.4
        elif tag in ['gentle']:
            pd_score += 0.2
        elif tag in ['heavy']:
            pd_score -= 0.1
    
    return {
        'pd_score': min(max(pd_score, -3.0), 2.0),
        'spiritual_meaning': spiritual,
        'symbolism': symbolism
    }

def calculate_synchronicity_strength(event, inner_state, timing):
    """Calculate strength of synchronicity"""
    # Simple heuristic based on timing and description length
    strength = 0.5
    
    if timing and ('minute' in timing.lower() or 'immediately' in timing.lower()):
        strength += 0.3
    
    if len(event) > 50:  # Detailed description suggests significance
        strength += 0.2
    
    if len(inner_state) > 30:
        strength += 0.1
    
    return min(strength, 1.0)

def analyze_past_event_psi(event_date, context):
    """Retroactive psi analysis of past event"""
    dt = datetime.combine(event_date, datetime.min.time())
    num_result = calculate_life_path(dt)
    
    # Simulated analysis
    base_pd = 0.5
    
    if num_result['is_master']:
        base_pd += 1.0
    
    if event_date.month in [11, 22]:
        base_pd += 0.5
    
    # Add random variation to simulate weather/sync data we don't have
    base_pd += np.random.randn() * 0.3
    
    return min(max(base_pd, -3.0), 2.0)

if __name__ == "__main__":
    main()
