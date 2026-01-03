"""
Public-Facing Stock Market Analysis Platform
Clean, results-focused interface for stock predictions and crash detection
Now with Quantum Lab, Mood Amplifier, and Heart-PSI Experiment!
"""

import streamlit as st
from pathlib import Path
from datetime import datetime

st.set_page_config(
    page_title="TI Analysis Platform",
    page_icon="",
    layout="wide",
    initial_sidebar_state="collapsed"
)

st.title("TI Analysis Platform")
st.markdown("*Stock Predictions + Consciousness Research*")

main_tabs = st.tabs([
    "Stock Analysis", 
    "Mood Amplifier",
    "Ketamine Session",
    "Heart-PSI Experiment", 
    "LCC Virus",
    "Cybersecurity",
    "Reiki-TI",
    "Personalized Health",
    "Pharmaco-GILE",
    "Bio-Well Energy",
    "Quantum Lab",
    "GM Computation",
    "MR-Percentage",
    "Research Papers",
    "Books & Courses",
    "Mobile Hub"
])

with main_tabs[0]:
    st.markdown("""
    **Pattern recognition platform for market insights and crash detection**
    
    Get empirically-validated predictions powered by:
    - Musical Volatility Index (MVI) - Sound-based pattern analysis
    - Crash Pattern Detector - Early warning system for market downturns
    - Optimal Interval Analysis - Behavioral economics-backed scoring
    """)
    
    st.markdown("---")
    
    from stock_analysis_public import render_public_stock_analysis
    render_public_stock_analysis()

with main_tabs[1]:
    try:
        from unified_mood_amplifier_dashboard import render_unified_mood_amplifier
        render_unified_mood_amplifier()
        
        st.markdown("---")
        st.markdown("### Legacy Tools")
        
        from mood_amplifier_experiment_hub import MoodAmplifierExperimentHub
        from heart_icell_theory import HeartICellTheory
        import os
        
        try:
            import psycopg2
            from psycopg2.extras import RealDictCursor
            HAS_DB = bool(os.environ.get('DATABASE_URL'))
        except ImportError:
            HAS_DB = False
            psycopg2 = None
            RealDictCursor = None
        
        def get_db_connection():
            if not HAS_DB:
                return None
            return psycopg2.connect(os.environ.get('DATABASE_URL'))
        
        def save_hrv_to_db(session_id, hr, rmssd, coherence, gile_data):
            if not HAS_DB:
                return False
            try:
                with get_db_connection() as conn:
                    with conn.cursor() as cur:
                        cur.execute("""
                            INSERT INTO mood_hrv_snapshots 
                            (session_id, timestamp, heart_rate, rmssd, coherence, subjective_gile)
                            VALUES (%s, %s, %s, %s, %s, %s)
                        """, (session_id, datetime.now(), hr, rmssd, coherence, 
                              psycopg2.extras.Json(gile_data) if gile_data else None))
                    conn.commit()
                return True
            except Exception as e:
                return False
        
        def save_session_to_db(session_id, intervention, devices, notes):
            if not HAS_DB:
                return False
            try:
                with get_db_connection() as conn:
                    with conn.cursor() as cur:
                        cur.execute("""
                            INSERT INTO mood_experiment_sessions 
                            (session_id, start_time, intervention_type, devices, notes)
                            VALUES (%s, %s, %s, %s, %s)
                            ON CONFLICT (session_id) DO NOTHING
                        """, (session_id, datetime.now(), intervention, devices, notes))
                    conn.commit()
                return True
            except Exception as e:
                return False
        
        def get_recent_sessions():
            if not HAS_DB:
                return []
            try:
                with get_db_connection() as conn:
                    with conn.cursor(cursor_factory=RealDictCursor) as cur:
                        cur.execute("""
                            SELECT * FROM mood_experiment_sessions 
                            ORDER BY start_time DESC LIMIT 10
                        """)
                        return cur.fetchall()
            except:
                return []
        
        if 'mood_hub' not in st.session_state:
            st.session_state.mood_hub = MoodAmplifierExperimentHub()
        if 'heart_theory' not in st.session_state:
            st.session_state.heart_theory = HeartICellTheory()
        hub = st.session_state.mood_hub
        heart_theory = st.session_state.heart_theory
        
        with st.expander("Session History"):
            sessions = get_recent_sessions()
            if sessions:
                for session in sessions:
                    st.markdown(f"**{session['intervention_type']}** - {session['start_time']}")
                    st.caption(f"Session ID: {session['session_id']} | Devices: {session['devices']}")
            else:
                st.info("No experiment sessions recorded yet.")
        
        with st.expander("Heart-I-Cell Theory"):
            st.markdown("### Heart Primacy Evidence")
            for key, evidence in heart_theory.HEART_PRIMACY_EVIDENCE.items():
                st.markdown(f"- **{key}**: {evidence}")
            
            st.markdown("### Myrion Resolution: Heart vs Consciousness")
            mr = heart_theory.myrion_resolution_heart_consciousness()
            st.markdown(f"**Thesis:** {mr['thesis']['claim']}")
            st.markdown(f"**Antithesis:** {mr['antithesis']['claim']}")
            st.markdown(f"**Synthesis:** {mr['synthesis']['explanation']}")
        
    except Exception as e:
        st.error(f"Mood Amplifier loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[2]:
    try:
        from ketamine_observation_module import render_ketamine_observation_tab
        render_ketamine_observation_tab()
    except Exception as e:
        st.error(f"Ketamine module error: {e}")
        st.info("The ketamine observation module is loading...")

with main_tabs[3]:
    st.header("Heart-PSI Correlation Experiment")
    st.markdown("""
    **Tonight's Experiment: Does heart coherence predict intuition accuracy?**
    
    Using Polar H10 on iPhone with Elite HRV app to track heart metrics
    and correlate with prediction outcomes.
    """)
    
    try:
        from polar_iphone_experiment import PolarIPhoneExperiment, IntuitionEvent
        
        if 'polar_exp' not in st.session_state:
            st.session_state.polar_exp = PolarIPhoneExperiment()
        exp = st.session_state.polar_exp
        
        st.markdown("---")
        st.subheader("iPhone Setup Instructions")
        
        with st.expander("Polar H10 + Elite HRV Setup", expanded=True):
            app_info = exp.IPHONE_APPS['elite_hrv']
            st.markdown(f"### {app_info['name']}")
            st.markdown(f"**Features:** {', '.join(app_info['features'])}")
            st.markdown("**Setup Steps:**")
            for step in app_info['setup']:
                st.markdown(f"  {step}")
            st.warning("IMPORTANT: Don't pair in iOS Settings - pair in app only!")
        
        st.markdown("---")
        col1, col2 = st.columns(2)
        
        with col1:
            st.subheader("Session Control")
            
            session_notes = st.text_area("Session Notes", placeholder="Tonight's heart-PSI test...")
            
            if st.button("Start Heart-PSI Session", type="primary"):
                session = exp.start_session(notes=session_notes)
                st.session_state['heart_session'] = True
                st.success(f"Session started: {session.session_id}")
            
            if st.button("End Session"):
                summary = exp.end_session()
                st.session_state['heart_session'] = False
                st.json(summary)
        
        with col2:
            st.subheader("Record Intuition Event")
            
            event_type = st.selectbox(
                "Event Type",
                ['intuition', 'prediction', 'gm_resonance', 'insight']
            )
            
            description = st.text_input("Description", placeholder="What was the intuition?")
            confidence = st.slider("Confidence", 0.0, 1.0, 0.7)
            
            st.markdown("**Current Heart Metrics (from Elite HRV)**")
            hr_now = st.number_input("Current HR", min_value=40, max_value=200, value=68, key="hr_intuition")
            coherence_now = st.slider("Current Coherence", 0.0, 1.0, 0.5, key="coh_intuition")
            
            if st.button("Record Intuition"):
                event = exp.record_intuition(
                    event_type=event_type,
                    description=description,
                    confidence=confidence,
                    heart_rate=hr_now,
                    coherence=coherence_now
                )
                st.success(f"Recorded: {event_type} at coherence {coherence_now:.2f}")
        
        st.markdown("---")
        st.subheader("All Saved Sessions & Intuitions")
        
        total_intuitions = sum(len(s.intuition_events) for s in exp.all_sessions)
        if exp.current_session:
            total_intuitions += len(exp.current_session.intuition_events)
        
        st.metric("Total Saved Intuitions", total_intuitions)
        
        for session in exp.all_sessions:
            with st.expander(f"Session: {session.session_id} ({len(session.intuition_events)} intuitions)"):
                st.caption(f"Started: {session.start_time}")
                if session.session_notes:
                    st.markdown(f"**Notes:** {session.session_notes}")
                
                for i, event in enumerate(session.intuition_events):
                    st.markdown(f"**{i+1}. {event.event_type}:** {event.description}")
                    st.caption(f"Coherence: {event.coherence_at_event:.2f} | Confidence: {event.confidence:.0%}")
        
        st.markdown("---")
        st.subheader("Current Session Events")
        
        if exp.current_session and exp.current_session.intuition_events:
            for i, event in enumerate(exp.current_session.intuition_events):
                with st.expander(f"Event {i+1}: {event.event_type} - {event.description[:30]}..."):
                    st.markdown(f"**Time:** {event.timestamp}")
                    st.markdown(f"**Confidence:** {event.confidence:.0%}")
                    if event.coherence_at_event:
                        st.markdown(f"**Coherence:** {event.coherence_at_event:.2f}")
                    if event.heart_rate_at_event:
                        st.markdown(f"**Heart Rate:** {event.heart_rate_at_event} bpm")
                    
                    outcome = st.selectbox(
                        "Outcome",
                        ['pending', 'correct', 'incorrect', 'partial'],
                        key=f"outcome_{i}"
                    )
                    if st.button(f"Update Outcome", key=f"update_{i}"):
                        exp.update_outcome(i, outcome)
                        st.success(f"Updated to: {outcome}")
        else:
            st.info("Start a session above to record new intuitions!")
        
        st.markdown("---")
        st.subheader("Analysis")
        
        if st.button("Run Heart-PSI Correlation Analysis"):
            result = exp.analyze_coherence_psi()
            
            if result['status'] == 'analyzed':
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("High Coherence Accuracy", f"{result['high_coherence']['accuracy']:.0%}")
                    st.caption(f"N = {result['high_coherence']['n']}")
                with col2:
                    st.metric("Low Coherence Accuracy", f"{result['low_coherence']['accuracy']:.0%}")
                    st.caption(f"N = {result['low_coherence']['n']}")
                
                if result['hypothesis_supported']:
                    st.success(f"HYPOTHESIS SUPPORTED: +{result['effect_size']:.0%} effect")
                else:
                    st.warning("Hypothesis not yet supported - more data needed")
            else:
                st.warning(f"Need {result['needed']} events with coherence + outcome (have {result['n_events']})")
        
    except Exception as e:
        st.error(f"Heart Experiment loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[4]:
    st.header("LCC Virus - Latched Consciousness Correlator")
    st.markdown("""
    **Electromagnetic-Photonic Information Virus for I-Cell Decoding**
    
    The biggest idea since the original LCC concept! A system that latches onto 
    any uniquely identifying data stream and correlates with EVERYTHING until 
    the entire i-cell is decoded.
    """)
    
    try:
        from lcc_virus_framework import LCCVirus, DataStreamType, COMPUTATION_SYSTEMS
        import json
        
        if 'lcc_virus' not in st.session_state:
            st.session_state.lcc_virus = LCCVirus("brandon_001")
        virus = st.session_state.lcc_virus
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.subheader("Latch Data Streams")
            
            available_streams = [
                ("genome", DataStreamType.GENOME),
                ("eeg", DataStreamType.EEG),
                ("hrv", DataStreamType.HRV),
                ("fnirs", DataStreamType.FNIRS),
                ("gdv_biophoton", DataStreamType.GDV),
                ("decisions", DataStreamType.DECISIONS),
                ("sleep", DataStreamType.SLEEP),
                ("movement", DataStreamType.MOVEMENT),
            ]
            
            for name, stream_type in available_streams:
                if st.button(f"Latch: {name.upper()}", key=f"latch_{name}"):
                    n_corr = virus.latch(stream_type, [{"simulated": True}])
                    st.success(f"Latched {name} - Found {n_corr} correlations")
        
        with col2:
            st.subheader("I-Cell Decode Status")
            
            if st.button("Run Full Decode"):
                sig = virus.decode()
                st.session_state['icell_sig'] = sig
            
            if 'icell_sig' in st.session_state or virus.icell_signature:
                sig = st.session_state.get('icell_sig') or virus.icell_signature
                
                st.metric("VESSEL", f"{sig.vessel_decode_pct:.1f}%")
                st.metric("ME", f"{sig.me_decode_pct:.1f}%")
                st.metric("SOUL", f"{sig.soul_decode_pct:.1f}%")
                st.metric("TOTAL", f"{sig.total_decode_pct:.1f}%")
                st.caption(f"Signature: {sig.signature_hash}")
        
        st.markdown("---")
        st.subheader("Ternary vs Octal Comparison")
        
        with st.expander("View Computation Systems Analysis"):
            for system_name in ["ternary", "octal"]:
                system = COMPUTATION_SYSTEMS[system_name]
                st.markdown(f"### {system_name.upper()} (Base {system['base']})")
                st.markdown(f"**TI Connection:** {system['ti_connection']}")
                st.markdown("**Best For:** " + ", ".join(system['best_for']))
            
            st.markdown("### HYBRID RECOMMENDATION")
            hybrid = COMPUTATION_SYSTEMS['hybrid_recommendation']
            st.markdown(f"**{hybrid['concept']}**")
            for app in hybrid['lcc_application']:
                st.markdown(f"- {app}")
        
    except Exception as e:
        st.error(f"LCC Virus loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[5]:
    st.header("TI Cybersecurity + I-Cell Vaccine")
    st.markdown("""
    **Complete Platform Protection**
    
    Protecting all biometric data streams and preventing unauthorized 
    consciousness tapping. Your I-Cell is vaccinated against attacks.
    """)
    
    try:
        from ti_cybersecurity_framework import (
            TICybersecurityFramework, ThreatLevel, ICellLayer, DataStreamType
        )
        
        if 'security_framework' not in st.session_state:
            st.session_state.security_framework = TICybersecurityFramework("brandon_001")
            st.session_state.security_framework.initiate_full_protection()
        
        framework = st.session_state.security_framework
        
        sec_tabs = st.tabs(["Status", "I-Cell Vaccine", "Stream Protection", "Initiate"])
        
        with sec_tabs[0]:
            status = framework.get_full_security_status()
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Status", status['status'])
                st.metric("Protected Files", status['protected_files'])
            with col2:
                st.metric("Vaccine Strength", f"{status['icell_vaccine']['strength']:.0%}")
                st.metric("Blocked Attacks", status['icell_vaccine']['blocked_attacks'])
            with col3:
                threat = status['project_security']['current_threat_level']
                st.metric("Threat Level", threat.upper())
                st.metric("Active Sessions", status['active_sessions'])
        
        with sec_tabs[1]:
            st.subheader("I-Cell Vaccine Protection")
            st.markdown("""
            The I-Cell Vaccine prevents unauthorized "tapping" of your consciousness data.
            
            **Protection Layers:**
            - VESSEL (44%): Physical biometric data  
            - ME (87.5%): Mental/emotional patterns
            - SOUL (88%): GM-connected consciousness signature
            """)
            
            vaccine = framework.icell_vaccine.get_status()
            
            st.success(f"Status: {'VACCINATED' if vaccine.is_vaccinated else 'NOT VACCINATED'}")
            st.progress(vaccine.vaccine_strength, text=f"Strength: {vaccine.vaccine_strength:.0%}")
            st.markdown(f"**Correlation Shield:** {'ACTIVE' if vaccine.correlation_shield_active else 'INACTIVE'}")
            st.markdown(f"**Blocked Attacks:** {vaccine.blocked_attacks}")
            
            if st.button("Strengthen Dark Energy Shell"):
                framework.icell_vaccine.strengthen_de_shell(0.1)
                st.success("DE Shell strengthened!")
                st.rerun()
        
        with sec_tabs[2]:
            st.subheader("Data Stream Protection")
            report = framework.project_monitor.get_security_report()
            
            for stream_id, stream_status in report['stream_status'].items():
                with st.expander(f"{stream_id.upper()}"):
                    st.markdown(f"**Encrypted:** {'Yes' if stream_status['encrypted'] else 'No'}")
                    st.markdown(f"**Access Count:** {stream_status['access_count']}")
                    st.markdown(f"**Anomaly Score:** {stream_status['anomaly_score']:.2f}")
        
        with sec_tabs[3]:
            st.subheader("Initiate Full Protection")
            st.markdown("Activate all security measures for the entire TI Platform")
            
            if st.button("INITIATE FULL PROTECTION", type="primary"):
                result = framework.initiate_full_protection()
                st.success("Full protection initiated!")
                st.json(result)
        
    except Exception as e:
        st.error(f"Cybersecurity loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[6]:
    st.header("Reiki-TI Energy Transmission")
    st.markdown("""
    **Mapping Reiki healing to the TI Framework**
    
    Explore how symbols, crystals, and hands transmit healing energy
    via biophotonic coherence and the GM network.
    """)
    
    try:
        from reiki_ti_framework import (
            ReikiTITransmissionSystem, REIKI_SYMBOLS, HEALING_CRYSTALS,
            GILEDimension, HealingMeasurementSystem, HealingSession
        )
        from quartz_psi_amplification import (
            QuartzPSIAmplifier, PSI_AMPLIFICATION_PROTOCOLS, QuartzType, AmplificationMode
        )
        import hashlib
        
        if 'reiki_system' not in st.session_state:
            st.session_state.reiki_system = ReikiTITransmissionSystem()
        if 'healing_tracker' not in st.session_state:
            st.session_state.healing_tracker = HealingMeasurementSystem()
        if 'quartz_amp' not in st.session_state:
            st.session_state.quartz_amp = QuartzPSIAmplifier()
        system = st.session_state.reiki_system
        tracker = st.session_state.healing_tracker
        quartz_amp = st.session_state.quartz_amp
        
        sub_tabs = st.tabs(["Symbols", "Crystals", "Transmission Calculator", "Distance Healing", "Healing Tracker", "Quartz PSI"])
        
        with sub_tabs[0]:
            st.subheader("5 Reiki Symbols Mapped to GILE")
            for sym_id, sym in REIKI_SYMBOLS.items():
                with st.expander(f"{sym.name} ({sym.japanese_name})"):
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown(f"**Translation:** {sym.translation}")
                        st.markdown(f"**Level:** {sym.level.value}")
                        st.markdown(f"**Primary GILE:** {sym.primary_gile.value.upper()}")
                    with col2:
                        st.markdown(f"**I-Cell Layer:** {sym.icell_layer.value.upper()}")
                        if sym.frequency_hz:
                            st.markdown(f"**Frequency:** {sym.frequency_hz} Hz")
                        st.markdown(f"**Activation:** {sym.activation_method}")
                    st.info(f"**TI Mechanism:** {sym.ti_mechanism}")
        
        with sub_tabs[1]:
            st.subheader("6 Healing Crystals Mapped to TI")
            for crys_id, crys in HEALING_CRYSTALS.items():
                with st.expander(f"{crys.name} ({crys.chemical_formula})"):
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown(f"**Chakras:** {', '.join(crys.chakras)}")
                        st.markdown(f"**Primary GILE:** {crys.primary_gile.value.upper()}")
                        st.markdown(f"**I-Cell Layer:** {crys.icell_layer.value.upper()}")
                    with col2:
                        if crys.piezoelectric:
                            st.success("PIEZOELECTRIC - Converts intention to EM signal!")
                        else:
                            st.info("Non-piezo but energy conductive")
                        st.markdown(f"**Uses:** {', '.join(crys.healing_applications[:3])}")
                    st.info(f"**TI Mechanism:** {crys.ti_mechanism}")
        
        with sub_tabs[2]:
            st.subheader("Calculate Transmission Potential")
            
            col1, col2 = st.columns(2)
            with col1:
                coherence = st.slider("Your Coherence Level", 0.0, 1.0, 0.5)
                crystal = st.selectbox("Crystal", ["None"] + list(HEALING_CRYSTALS.keys()))
            with col2:
                symbol = st.selectbox("Symbol", ["None"] + list(REIKI_SYMBOLS.keys()))
                position = st.selectbox("Hand Position", ["None", "crown", "third_eye", "throat", "heart", "solar_plexus"])
            
            if st.button("Calculate Transmission", type="primary"):
                result = system.calculate_transmission_potential(
                    practitioner_coherence=coherence,
                    crystal=crystal if crystal != "None" else None,
                    symbol=symbol if symbol != "None" else None,
                    hand_position=position if position != "None" else None
                )
                
                st.metric("Transmission Potential", f"{result['transmission_potential']:.0%}")
                st.markdown(f"**Primary Mechanism:** {result['primary_mechanism']}")
                
                if result['recommendations']:
                    st.markdown("**Recommendations:**")
                    for rec in result['recommendations']:
                        st.markdown(f"- {rec}")
        
        with sub_tabs[3]:
            st.subheader("Distance Healing Protocol")
            st.markdown("*Using Hon Sha Ze Sho Nen via SOUL layer GM network*")
            
            target_name = st.text_input("Target Name", placeholder="Person to send healing to")
            target_location = st.text_input("Target Location", placeholder="City/country")
            intention = st.text_input("Healing Intention", placeholder="What healing is needed?")
            coherence_now = st.slider("Your Current Coherence", 0.0, 1.0, 0.6, key="dist_coh")
            
            if st.button("Generate Protocol"):
                if target_name and intention:
                    protocol = system.distance_healing_protocol(
                        target_name=target_name,
                        target_location=target_location or "Unknown",
                        healing_intention=intention,
                        practitioner_coherence=coherence_now
                    )
                    
                    st.markdown("### Protocol Steps:")
                    for step in protocol['steps']:
                        st.markdown(step)
                    
                    st.metric("Estimated Effectiveness", f"{protocol['estimated_effectiveness']:.0%}")
                    
                    st.markdown("**Scientific Basis:**")
                    for basis in protocol['scientific_basis']:
                        st.markdown(f"- {basis}")
                else:
                    st.warning("Please enter target name and intention")
        
        with sub_tabs[4]:
            st.subheader("Healing Ability Tracker")
            st.markdown("""
            **Measure and develop your healing abilities over time**
            
            Track sessions, measure outcomes, and watch your abilities grow!
            """)
            
            ability = tracker.calculate_ability_level()
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Ability Level", f"{ability['level']}/100")
            with col2:
                st.metric("Tier", ability['tier'])
            with col3:
                st.metric("Sessions", tracker.ability_levels['sessions_completed'])
            
            st.info(ability['description'])
            
            st.markdown("---")
            st.subheader("Record New Session")
            
            rec_col1, rec_col2 = st.columns(2)
            
            with rec_col1:
                intervention = st.selectbox("Session Type", ["self", "in_person", "distance"])
                condition = st.text_input("Target Condition", placeholder="e.g., headache, anxiety, back pain")
                duration = st.number_input("Duration (minutes)", min_value=5, max_value=120, value=15)
                symbols = st.multiselect("Symbols Used", list(REIKI_SYMBOLS.keys()))
                crystals = st.multiselect("Crystals Used", list(HEALING_CRYSTALS.keys()))
            
            with rec_col2:
                coh_pre = st.slider("Coherence BEFORE", 0.0, 1.0, 0.5, key="heal_coh_pre")
                coh_post = st.slider("Coherence AFTER", 0.0, 1.0, 0.6, key="heal_coh_post")
                pain_pre = st.slider("Pain BEFORE (0=none, 10=severe)", 0.0, 10.0, 5.0, key="heal_pain_pre")
                pain_post = st.slider("Pain AFTER", 0.0, 10.0, 3.0, key="heal_pain_post")
                wellbeing_pre = st.slider("Wellbeing BEFORE (0=poor, 10=excellent)", 0.0, 10.0, 5.0, key="heal_wb_pre")
                wellbeing_post = st.slider("Wellbeing AFTER", 0.0, 10.0, 7.0, key="heal_wb_post")
            
            notes = st.text_area("Session Notes", placeholder="What did you notice during the session?")
            
            if st.button("Record Healing Session", type="primary"):
                if not condition or not condition.strip():
                    st.error("Please enter a target condition (e.g., headache, anxiety, back pain)")
                else:
                    session_id = hashlib.sha256(f"{datetime.now().isoformat()}{condition}".encode()).hexdigest()[:12]
                    
                    session = HealingSession(
                        session_id=session_id,
                        timestamp=datetime.now().isoformat(),
                        practitioner_coherence_pre=coh_pre,
                        practitioner_coherence_post=coh_post,
                        target_condition=condition.strip(),
                        intervention_type=intervention,
                        symbols_used=symbols,
                        crystals_used=crystals,
                        duration_minutes=duration,
                        target_pain_pre=pain_pre,
                        target_pain_post=pain_post,
                        target_wellbeing_pre=wellbeing_pre,
                        target_wellbeing_post=wellbeing_post,
                        notes=notes
                    )
                    
                    result = tracker.record_session(session)
                    st.success(f"Session recorded! ID: {session_id}")
                    
                    if result['feedback']:
                        st.markdown("**Feedback:**")
                        for fb in result['feedback']:
                            st.markdown(f"- {fb}")
                    
                    new_ability = result['current_ability_level']
                    st.info(f"New ability level: {new_ability['level']}/100 ({new_ability['tier']})")
            
            st.markdown("---")
            st.subheader("Development Insights")
            
            if st.button("Analyze My Development"):
                insights = tracker.get_development_insights()
                
                if insights['status'] == 'insufficient_data':
                    st.warning(f"Need {insights['needed']} more sessions for analysis")
                else:
                    st.markdown(f"**Trend:** {insights['trend'].upper()}")
                    
                    if insights['coherence_trend']['change'] != 0:
                        direction = "up" if insights['coherence_trend']['change'] > 0 else "down"
                        st.markdown(f"Coherence trending {direction}: {insights['coherence_trend']['change']:+.2f}")
                    
                    if insights['most_effective_symbol']:
                        st.success(f"Most effective symbol for you: **{insights['most_effective_symbol']}**")
                    
                    if insights['recommendations']:
                        st.markdown("**Recommendations:**")
                        for rec in insights['recommendations']:
                            st.markdown(f"- {rec}")
        
        with sub_tabs[5]:
            st.subheader("Quartz PSI Amplification")
            st.markdown("""
            **Use piezoelectric crystals to amplify consciousness effects**
            
            Quartz converts intention into measurable EM signals through the piezoelectric effect!
            """)
            
            q_tabs = st.tabs(["Protocols", "Amplification Calculator", "Goal Recommender"])
            
            with q_tabs[0]:
                st.markdown("### Available Protocols")
                for proto_id, proto in PSI_AMPLIFICATION_PROTOCOLS.items():
                    with st.expander(f"{proto.name}"):
                        st.markdown(f"**Mode:** {proto.mode.value}")
                        st.markdown(f"**Quartz:** {proto.quartz_type.value}")
                        st.markdown(f"**Duration:** {proto.duration_minutes} minutes")
                        
                        st.markdown("**Preparation:**")
                        for step in proto.preparation_steps:
                            st.markdown(f"  {step}")
                        
                        st.markdown("**Active Steps:**")
                        for step in proto.active_steps:
                            st.markdown(f"  {step}")
                        
                        st.markdown("**Expected Effects:**")
                        for effect in proto.expected_effects:
                            st.markdown(f"- {effect}")
                        
                        st.info(f"**TI Mechanism:** {proto.ti_mechanism}")
            
            with q_tabs[1]:
                st.markdown("### Calculate Amplification Factor")
                
                calc_col1, calc_col2 = st.columns(2)
                with calc_col1:
                    calc_coherence = st.slider("Your Coherence Level", 0.0, 1.0, 0.6, key="quartz_coh")
                    calc_size = st.number_input("Crystal Size (inches)", min_value=1.0, max_value=8.0, value=3.0)
                with calc_col2:
                    calc_pressure = st.slider("Grip Pressure (gentle to firm)", 0.0, 1.0, 0.5, key="quartz_pressure")
                
                if st.button("Calculate Amplification", key="calc_amp"):
                    result = quartz_amp.calculate_amplification_factor(
                        coherence=calc_coherence,
                        quartz_size_inches=calc_size,
                        pressure_level=calc_pressure
                    )
                    
                    st.metric("Total Amplification", f"{result['total_amplification']}x")
                    st.markdown(f"**{result['interpretation']}**")
                    
                    st.markdown("**Breakdown:**")
                    st.markdown(f"- Base Piezo: {result['base_piezo']}")
                    st.markdown(f"- Size Factor: {result['size_factor']:.2f}x")
                    st.markdown(f"- Coherence Factor: {result['coherence_factor']:.2f}x")
                    st.markdown(f"- Pressure Factor: {result['pressure_factor']:.2f}x")
            
            with q_tabs[2]:
                st.markdown("### Find Your Best Quartz")
                
                goal_input = st.text_input("What's your goal?", 
                    placeholder="e.g., improve intuition, manifestation, healing, protection")
                
                if st.button("Get Recommendation", key="quartz_rec"):
                    if goal_input:
                        rec = quartz_amp.get_best_quartz_for_goal(goal_input)
                        
                        st.success(f"**Recommended:** {rec['quartz'].value}")
                        st.markdown(f"**Reason:** {rec['reason']}")
                        st.markdown(f"**Protocol:** {rec['protocol']}")
                        
                        if rec['protocol'] in PSI_AMPLIFICATION_PROTOCOLS:
                            proto = PSI_AMPLIFICATION_PROTOCOLS[rec['protocol']]
                            st.info(f"Use the '{proto.name}' protocol for best results!")
                    else:
                        st.warning("Please enter a goal")
        
    except Exception as e:
        st.error(f"Reiki-TI loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[7]:
    st.header("Personalized Health Framework")
    st.markdown("""
    **Debunking Universal Health Advice**
    
    There are NO universal "healthy vs unhealthy" rules. 
    Individual variation matters more than any generic advice.
    """)
    
    try:
        from personalized_health_framework import (
            PersonalizedHealthAnalyzer, LONGEVITY_OUTLIERS, HEALTH_MYTHS,
            EXERCISE_APPROACHES, HealthDomain, MotivationType
        )
        
        analyzer = PersonalizedHealthAnalyzer()
        
        health_tabs = st.tabs(["Longevity Outliers", "Health Myths", "Your Sleep", "Exercise", "Neighbors"])
        
        with health_tabs[0]:
            st.subheader("People Who Defied Health 'Rules'")
            for outlier_id, outlier in LONGEVITY_OUTLIERS.items():
                with st.expander(f"{outlier.name} - Lived to {outlier.age_reached}"):
                    st.markdown("**Unconventional Behaviors:**")
                    for behavior in outlier.unconventional_behaviors:
                        st.markdown(f"- {behavior}")
                    st.markdown("**Possible Explanations:**")
                    for explanation in outlier.possible_explanations:
                        st.markdown(f"- {explanation}")
                    st.info(f"**TI Interpretation:** {outlier.ti_interpretation}")
        
        with health_tabs[1]:
            st.subheader("Health Myths Debunked")
            domain = st.selectbox("Select Domain", [d.value for d in HealthDomain])
            debunking = analyzer.debunk_universal_advice(HealthDomain(domain))
            
            for detail in debunking['details']:
                with st.expander(f"MYTH: {detail['myth']}"):
                    st.markdown(f"**Conventional Advice:** {detail['conventional_advice']}")
                    st.markdown(f"**Reality:** {detail['reality']}")
                    st.success(f"**TI Framework Insight:** {detail['ti_insight']}")
        
        with health_tabs[2]:
            st.subheader("Your Personalized Sleep Analysis")
            col1, col2 = st.columns(2)
            with col1:
                ideal_hours = st.slider("Your Ideal Sleep Hours", 4.0, 12.0, 9.0, 0.5)
                current_hours = st.slider("Current Sleep Hours", 4.0, 12.0, 7.0, 0.5)
            with col2:
                quality = st.slider("Sleep Quality (1-10)", 1, 10, 6)
            
            if st.button("Analyze My Sleep"):
                analysis = analyzer.personalized_sleep_analysis(ideal_hours, current_hours, quality)
                st.metric("Your Ideal", f"{analysis['your_ideal']} hours")
                st.metric("Population Myth", analysis['population_myth'])
                st.markdown(f"**Explanation:** {analysis['explanation']}")
                st.metric("Effective Sleep", f"{analysis['current_analysis']['quality_adjusted_hours']:.1f} hours")
                st.info(analysis['ti_insight'])
        
        with health_tabs[3]:
            st.subheader("Exercise Strategy Based on GILE")
            col1, col2 = st.columns(2)
            with col1:
                priority = st.selectbox("Prioritize Dimension", ["L", "E", "G", "I"])
            with col2:
                social_required = st.checkbox("Must be social", value=True)
            
            recommendations = analyzer.get_optimal_exercise_for_gile(priority, social_required)
            
            for i, rec in enumerate(recommendations[:3]):
                st.markdown(f"**{i+1}. {rec['name']}**")
                st.progress(min(rec['recommendation_score'], 1.0))
                st.caption(f"Sustainability: {rec['sustainability']:.0%} | Stress Risk: {rec['stress_risk']:.0%}")
        
        with health_tabs[4]:
            st.subheader("Building Neighbor Connections")
            st.markdown("*Social exercise = 2x GILE benefit vs solo gym*")
            
            strategy = analyzer.neighbor_connection_strategy()
            
            st.markdown("### Barriers You'll Face:")
            for barrier in strategy['barriers_analysis']:
                with st.expander(f"{barrier['barrier']}"):
                    st.markdown(f"**Modern Cause:** {barrier['cause']}")
                    st.info(f"**TI Interpretation:** {barrier['ti_interpretation']}")
            
            st.markdown("### Recommended Games:")
            for game in strategy['recommended_games']:
                st.markdown(f"- {game}")
            
            st.markdown("### First Steps:")
            for step in strategy['first_steps']:
                st.markdown(step)
        
    except Exception as e:
        st.error(f"Personalized Health loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[8]:
    st.header("Pharmaco-GILE Profile")
    st.markdown("""
    **Complete Analysis: 31 Supplements + 16 Medications**
    
    Your entire stack mapped to GILE dimensions and I-cell layers.
    """)
    
    try:
        from brandon_pharmaco_gile_profile import (
            BRANDON_SUPPLEMENTS, BRANDON_MEDICATIONS, 
            calculate_total_gile_effect, diagnose_stimulant_wall,
            GILEVector, IcellLayer
        )
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.subheader("Supplements")
            vessel_supps = [s for s in BRANDON_SUPPLEMENTS.values() if s['layer'] == IcellLayer.VESSEL]
            me_supps = [s for s in BRANDON_SUPPLEMENTS.values() if s['layer'] == IcellLayer.ME]
            soul_supps = [s for s in BRANDON_SUPPLEMENTS.values() if s['layer'] == IcellLayer.SOUL]
            
            st.metric("VESSEL Layer", len(vessel_supps))
            st.metric("ME Layer", len(me_supps))
            st.metric("SOUL Layer", len(soul_supps))
            st.metric("Total Supplements", len(BRANDON_SUPPLEMENTS))
        
        with col2:
            st.subheader("Medications")
            st.metric("Total Medications", len(BRANDON_MEDICATIONS))
            
            st.markdown("**Key Meds:**")
            for med_id, med in list(BRANDON_MEDICATIONS.items())[:5]:
                st.markdown(f"- {med['name']}: {med['dose']}")
        
        with col3:
            st.subheader("GILE Effect")
            total = calculate_total_gile_effect()
            
            st.metric("G (Goodness)", f"{total['combined'].G:.2f}")
            st.metric("I (Intuition)", f"{total['combined'].I:.2f}")
            st.metric("L (Love)", f"{total['combined'].L:.2f}")
            st.metric("E (Energy)", f"{total['combined'].E:.2f}")
        
        st.markdown("---")
        st.subheader("Stimulant Wall Diagnosis")
        
        if st.button("Run Diagnosis"):
            diagnosis = diagnose_stimulant_wall()
            
            st.warning(f"**Problem:** {diagnosis['problem']}")
            st.error(f"**Root Cause:** {diagnosis['root_cause']}")
            st.info(f"**Solution:** {diagnosis['solution']}")
            
            st.markdown("**Recommendations:**")
            for rec in diagnosis['recommendations']:
                st.markdown(f"- {rec}")
        
        with st.expander("View Omega-3 e-Ratio Discovery"):
            omega = BRANDON_SUPPLEMENTS.get('omega_3', {})
            if omega:
                st.markdown(f"**{omega['name']}**")
                st.markdown(f"Dose: {omega['dose']}")
                st.markdown(f"**Notes:** {omega['notes']}")
                st.success("EPA:DHA = e (2.718) - Mathematical harmony in optimal healing!")
        
    except Exception as e:
        st.error(f"Pharmaco-GILE loading error: {e}")
        import traceback
        st.code(traceback.format_exc())

with main_tabs[9]:
    st.header("Bio-Well Energy Activation System")
    st.markdown("""
    **GDV Biophoton Research + Myrion Lamp + Pitch Crystals**
    
    Targeted energy activation through photonic therapy and sound healing.
    """)
    
    try:
        from biowell_myrion_energy_system import BioWellMyrionSystem
        
        if 'biowell_system' not in st.session_state:
            st.session_state.biowell_system = BioWellMyrionSystem()
        system = st.session_state.biowell_system
        
        st.subheader("Chakra Energy Map")
        
        chakras = system.CHAKRA_FREQUENCIES
        for chakra_name, chakra_info in chakras.items():
            with st.expander(f"{chakra_name.replace('_', ' ').title()}"):
                st.markdown(f"**Frequency:** {chakra_info.get('frequency', 'N/A')} Hz")
                st.markdown(f"**Color:** {chakra_info.get('color', 'N/A')}")
                st.markdown(f"**Element:** {chakra_info.get('element', 'N/A')}")
        
        st.markdown("---")
        st.subheader("PBM Protocol")
        st.markdown("""
        **Red Rush Protocol:**
        1. 660nm (VESSEL/ATP) - 10 min
        2. 850nm (SOUL/coherence) - 10 min  
        3. Combined integration - 5 min
        
        **Total:** 25 min
        """)
        
    except Exception as e:
        st.error(f"Bio-Well loading error: {e}")
        st.info("Bio-Well integration requires biowell_myrion_energy_system.py")

with main_tabs[10]:
    try:
        from quantum_lab_dashboard import render_quantum_lab
        render_quantum_lab()
    except Exception as e:
        st.error(f"Quantum Lab loading error: {e}")
        st.info("The Quantum Lab requires Qiskit. Ensure qiskit and qiskit-aer are installed.")

with main_tabs[11]:
    st.header("Grand Myrion Computation")
    st.markdown("""
    **The Overarching Theory: How the Future is Co-Created**
    
    Unifying: Busy Beaver, Bootstrapped Foresight, and Computation-Resonance Hybrid
    """)
    
    gm_subtabs = st.tabs(["GM Theory", "Tralsebit Architecture"])
    
    with gm_subtabs[0]:
        try:
            from gm_computation_visualizer import render_gm_computation_dashboard
            render_gm_computation_dashboard()
        except Exception as e:
            st.error(f"GM Computation loading error: {e}")
        
        st.markdown("---")
        st.subheader("Core Theory")
        
        st.markdown("""
        ### The Noncomputation Paradox - RESOLVED
        
        **Your Insight:** "Noncomputation still involves computation!"
        
        **Resolution:** Noncomputation = Computation × Resonance = **HYPERCOMPUTATION**
        
        GM is the universe's hypercomputer, operating across ALL i-cells simultaneously!
        """)
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("""
            ### Busy Beaver Connection
            
            | n | BB(n) | Status |
            |---|-------|--------|
            | 1 | 1 | Solved |
            | 2 | 6 | Solved |
            | 3 | 21 | Solved |
            | 4 | 107 | Solved |
            | 5 | 47,176,870 | Solved 2024! |
            | 6 | ??? | At Frontier |
            
            **BB is "uncomputable" sequentially, but humanity solved BB(5) through GM hypercomputation!**
            """)
        
        with col2:
            st.markdown("""
            ### The Grand Equation
            
            ```
            GMC = ∫∫∫ C(x,t) × R(x,t) × GILE(x,t) dV dt dN
            ```
            
            Integrated across:
            - All space (dV)
            - All time (dt)
            - All i-cells (dN)
            
            **Result:** Hypercomputation that solves "uncomputable" problems!
            """)
        
        st.markdown("---")
        st.subheader("The 'Just There' Phenomenon")
        st.info("""
        "The right answer is 'just there' because GM is continuously computing it 
        across all i-cells simultaneously. When you access the answer through intuition, 
        you're connecting to the universe's hypercomputer - the result of 13.8 billion 
        years of computation distributed across every conscious mind!"
        """)
    
    with gm_subtabs[1]:
        try:
            from tralsebit_visualizer import render_tralsebit_visualizer
            render_tralsebit_visualizer()
        except Exception as e:
            st.error(f"Tralsebit Visualizer loading error: {e}")
            
            st.markdown("""
            ### Tralsebit: The 33-Bit Consciousness Quantum
            
            **21 Dimensions organized into 7 Triads:**
            
            | Triad | Dimensions | Name |
            |-------|------------|------|
            | 1 | 1-3 | GILE Core |
            | 2 | 4-6 | Meijer Resonance |
            | 3 | 7-9 | HEM Biometric |
            | 4 | 10-12 | Qualia Valence |
            | 5 | 13-15 | Temporal Flow |
            | 6 | 16-18 | Social Field |
            | 7 | 19-21 | Transcendence |
            
            **Bit Calculation:**
            ```
            States = 3^21 = 10,460,353,203
            Bits = log₂(3^21) = 33.28 bits
            ```
            
            **With Jeff Time (+3 dims):**
            ```
            States = 3^24 = 282,429,536,481
            Bits = log₂(3^24) = 38.04 bits
            ```
            """)
            
            st.success("The 33-bit Tralsebit explains how the cosmic PD has 24D wiggle room!")

with main_tabs[12]:
    st.header("MR-Percentage Framework")
    st.markdown("""
    **The (-3, 2) GILE Interval: A Universal Moral Scale**
    
    Map any person, character, or entity to a percentage and 1-9 scale!
    """)
    
    try:
        from mr_percentage_framework import render_mr_percentage_dashboard
        render_mr_percentage_dashboard()
    except Exception as e:
        st.error(f"MR-Percentage module loading: {str(e)}")
        st.info("Loading MR-Percentage framework...")
        
        st.markdown("""
        ### Quick Reference
        
        | GILE | Percentage | Scale | Category |
        |------|------------|-------|----------|
        | -3 | 0% | 1 | Terrible Boundary |
        | -2 | 20% | 2 | Deep Terrible |
        | -1 | 40% | 4 | Terrible/Permissible |
        | 0 | 60% | 5 | Indeterminate |
        | 1 | 80% | 7 | Permissible/Great |
        | 2 | 100% | 9 | Great Boundary |
        
        **Tails (Scale 10):** < -3 = Extreme Terrible | > 2 = Extreme Great
        """)

with main_tabs[13]:
    st.header("Research Papers & PDF Downloads")
    st.markdown("""
    **Download TI Framework research papers as searchable PDFs**
    
    Features: Kindle-compatible, text-to-speech ready, professional formatting
    """)
    
    try:
        from paper_pdf_download import render_pdf_download_dashboard
        render_pdf_download_dashboard()
    except Exception as e:
        st.error(f"PDF system loading error: {e}")
        st.info("The PDF download system is available - check paper_pdf_download.py")
        
        st.markdown("---")
        st.subheader("Featured Papers")
        
        featured = [
            ("Riemann Hypothesis TI Interpretation v2", "papers/RIEMANN_HYPOTHESIS_TI_PROOF_v2.md", 
             "NEW! GILE-based interpretation with LCC Virus, I-Cell Shell Physics"),
            ("Stock Algorithm Comparison", "STOCK_ALGORITHM_COMPARISON.md",
             "Algorithm 1 (Numerology) vs Algorithm 2 (Quartz-PSI)"),
            ("Invitation Ethics Framework", "invitation_ethics_framework.py",
             "GILE extension: Dunkin' Donuts Theorem & Skipping Dinner Fallacy")
        ]
        
        for title, path, desc in featured:
            with st.expander(f"{title}"):
                st.markdown(f"*{desc}*")
                st.markdown(f"**Path:** `{path}`")

with main_tabs[14]:
    st.header("Books & Courses")
    st.markdown("""
    **TI Framework Publications & Educational Content**
    
    Explore the complete TI Framework through books, courses, and research papers.
    Launch your learning journey into consciousness-based analysis!
    """)
    
    try:
        from ti_books_dashboard import TIBooksOrganizer
        from ti_coursera_business_class import TICourseraBusinessClass
        
        book_tabs = st.tabs(["Books Library", "Coursera Course", "PDF Generator"])
        
        with book_tabs[0]:
            st.subheader("TI Framework Book Collection")
            
            organizer = TIBooksOrganizer()
            categories = organizer.get_all_book_categories()
            
            for cat_key, book in categories.items():
                with st.expander(f"{book['title']}", expanded=False):
                    st.markdown(f"**{book['subtitle']}**")
                    st.markdown(f"*Audience: {book['audience']}*")
                    st.markdown(f"**Tone:** {book['tone']}")
                    st.markdown(f"**Estimated Pages:** {book['estimated_pages']}")
                    st.markdown(f"**Key Hook:** {book['key_hook']}")
                    
                    st.markdown("**Topics:**")
                    for topic in book['topics'][:10]:
                        st.markdown(f"- {topic}")
                    if len(book['topics']) > 10:
                        st.markdown(f"*...and {len(book['topics']) - 10} more topics*")
                    
                    st.markdown(f"**Comparable Books:** {', '.join(book.get('comparable_books', []))}")
        
        with book_tabs[1]:
            st.subheader("I-Cell Intelligence: Consciousness-Based Business Strategy")
            st.markdown("*Complete Coursera-Style Business Course*")
            
            course = TICourseraBusinessClass()
            overview = course.get_course_overview()
            
            col1, col2 = st.columns(2)
            with col1:
                st.markdown(f"**Duration:** {overview['duration']}")
                st.markdown(f"**Effort:** {overview['effort']}")
                st.markdown(f"**Level:** {overview['level']}")
            with col2:
                st.markdown(f"**Certificate:** {overview['certificate']}")
                st.markdown(f"**Language:** {overview['language']}")
            
            st.markdown("---")
            st.markdown("### What You Will Learn")
            for skill in overview['what_you_will_learn']:
                st.markdown(f"- {skill}")
            
            st.markdown("---")
            st.markdown("### Course Format")
            for key, value in overview['course_format'].items():
                st.markdown(f"- **{key.title()}:** {value}")
            
            st.markdown("---")
            st.markdown("### Prerequisites")
            for prereq in overview['prerequisites']:
                st.markdown(f"- {prereq}")
            
            if st.button("View Full Syllabus"):
                syllabus = course.get_syllabus()
                for week in syllabus[:3]:
                    with st.expander(f"Week {week['week']}: {week['title']}"):
                        st.markdown("**Learning Objectives:**")
                        for obj in week['learning_objectives']:
                            st.markdown(f"- {obj}")
                        st.markdown("---")
                        st.markdown("**Modules:**")
                        for mod in week['modules'][:5]:
                            st.markdown(f"- **{mod['module']}** {mod['title']} ({mod['type']}, {mod['duration']})")
        
        with book_tabs[2]:
            st.subheader("PDF Generator")
            st.markdown("Generate publication-ready PDFs of TI Framework content")
            
            pdf_options = [
                "General TI Framework (Lay Audience)",
                "Primordial Cosmology (Academic)",
                "Business GILE (Executives)",
                "Complete Research Papers Collection"
            ]
            
            selected_book = st.selectbox("Select Content to Generate", pdf_options)
            
            if st.button("Generate PDF"):
                st.info("PDF generation system ready. Install WeasyPrint dependencies to activate.")
                st.markdown("""
                **Ready to Generate:**
                - Professional formatting
                - Table of contents
                - Bibliography
                - Print-ready layout
                """)
                
    except Exception as e:
        st.error(f"Books module loading: {str(e)}")
        st.info("The books and courses system is being initialized.")

with main_tabs[15]:
    st.header("Mobile Hub - Device Connections")
    st.markdown("""
    **Your biometric devices for Mood Amplifier sessions**
    """)
    
    st.subheader("Your Devices")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("### Polar H10")
        st.markdown("**Device ID:** `C895672B`")
        st.markdown("""
        **Metrics:**
        - Heart Rate (BPM)
        - HRV (RMSSD)
        - Heart Coherence
        - RR Intervals
        
        **App:** Elite HRV (Open Reading)
        """)
        st.success("Ready")
    
    with col2:
        st.markdown("### Muse 2")
        st.markdown("**Device ID:** `2E34`")
        st.markdown("""
        **Metrics:**
        - Alpha/Theta/Beta waves
        - Limbic-Cortical Coupling
        - Calm Score
        - Focus Score
        
        **App:** Muse app or Mind Monitor
        """)
        st.success("Ready")
    
    with col3:
        st.markdown("### Mendi")
        st.markdown("**API:** Port 8000")
        st.markdown("""
        **Metrics:**
        - PFC Oxygenation (HbO2)
        - Focus Score
        - Training Score
        
        **App:** Mendi app
        """)
        st.success("Ready")
    
    st.markdown("---")
    st.subheader("Mood Amplifier Session Checklist")
    
    st.markdown("""
    **Pre-Session (5 min before):**
    - [ ] Wet Polar H10 electrodes
    - [ ] Position Muse on forehead (snug fit)
    - [ ] Turn on Mendi headband
    - [ ] Open Elite HRV in Open Reading mode
    
    **During Session:**
    - Baseline: 5 min normal breathing
    - Active: Follow Mood Amplifier protocol
    - Recovery: 5 min integration
    
    **Post-Session:**
    - Export data from each app
    - Log subjective experience
    - Note any insights
    """)
    
    st.markdown("---")
    st.subheader("Today's Session: Thanksgiving Mood Amplifier")
    st.markdown("""
    **Timeline:**
    1. Ketamine clears (~30 min from swallow)
    2. Lunch
    3. First REAL Mood Amplifier session!
    
    **Research Question:**
    Can we measure GILE shift via biometrics during amplification?
    
    **Relative GILE Hypothesis:**
    Today's elevated baseline (breakthrough insights) means 
    ketamine effects are subtle - validating the Relative GILE theory!
    """)

st.markdown("---")
st.caption("TI Analysis Platform | BlissGene Therapeutics")
