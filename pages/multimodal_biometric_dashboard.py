"""
Multi-Modal Biometric Profiler Dashboard
==========================================
Streamlit dashboard for comprehensive biometric profiling,
consciousness measurement, and compatibility matching.
"""

import streamlit as st
import json
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.multimodal_biometric_profiler import MultiModalBiometricProfiler


def render_multimodal_biometric_dashboard():
    st.title("Multi-Modal Biometric Profiler")
    st.markdown("*12+ data channels for consciousness measurement, health assessment, and compatibility matching*")

    profiler = MultiModalBiometricProfiler()

    tabs = st.tabs([
        "Subject Management",
        "Data Ingestion",
        "Unified Profile",
        "Compatibility Matching",
        "Stranger Profiling",
    ])

    with tabs[0]:
        render_subject_management(profiler)

    with tabs[1]:
        render_data_ingestion(profiler)

    with tabs[2]:
        render_unified_profile(profiler)

    with tabs[3]:
        render_compatibility(profiler)

    with tabs[4]:
        render_stranger_profiling(profiler)


def render_subject_management(profiler):
    st.header("Subject Management")

    col1, col2 = st.columns(2)
    with col1:
        st.subheader("Create New Subject")
        name = st.text_input("Full Name", key="new_subject_name")
        ext_id = st.text_input("External ID (optional)", key="new_subject_ext_id")
        if st.button("Create Subject", type="primary"):
            if name:
                try:
                    sid = profiler.create_subject(name, ext_id if ext_id else None)
                    st.success(f"Subject created with ID: {sid}")
                except Exception as e:
                    st.error(f"Error: {str(e)}")
            else:
                st.warning("Please enter a name")

    with col2:
        st.subheader("Existing Subjects")
        try:
            subjects = profiler.list_subjects()
            if subjects:
                for s in subjects:
                    st.markdown(f"**{s['name']}** (ID: {s['id']}) - {s['modality_count']} modalities")
            else:
                st.info("No subjects yet. Create one to get started.")
        except Exception as e:
            st.error(f"Error loading subjects: {str(e)}")


def render_data_ingestion(profiler):
    st.header("Data Ingestion")

    try:
        subjects = profiler.list_subjects()
        subject_options = {f"{s['name']} (ID: {s['id']})": s['id'] for s in subjects}
    except:
        subject_options = {}

    if not subject_options:
        st.info("Create a subject first in the Subject Management tab.")
        return

    selected = st.selectbox("Select Subject", list(subject_options.keys()), key="ingest_subject")
    subject_id = subject_options[selected]

    modality = st.selectbox("Select Modality", [
        "typing", "fingerprint", "genetic", "spirometry",
        "apple_watch", "facial", "digit_ratio", "oura", "voice", "numerology"
    ], key="ingest_modality")

    st.markdown("---")

    if modality == "typing":
        render_typing_input(profiler, subject_id)
    elif modality == "fingerprint":
        render_fingerprint_input(profiler, subject_id)
    elif modality == "genetic":
        render_genetic_input(profiler, subject_id)
    elif modality == "spirometry":
        render_spirometry_input(profiler, subject_id)
    elif modality == "apple_watch":
        render_apple_watch_input(profiler, subject_id)
    elif modality == "facial":
        render_facial_input(profiler, subject_id)
    elif modality == "digit_ratio":
        render_digit_ratio_input(profiler, subject_id)
    elif modality == "oura":
        render_oura_input(profiler, subject_id)
    elif modality == "voice":
        render_voice_input(profiler, subject_id)
    elif modality == "numerology":
        render_numerology_input(profiler, subject_id)


def render_typing_input(profiler, subject_id):
    st.subheader("Keystroke Dynamics")
    st.markdown("Enter typing metrics or paste keystroke event data.")

    col1, col2 = st.columns(2)
    with col1:
        dwell = st.number_input("Mean Dwell Time (ms)", 50, 300, 100, key="typ_dwell")
        flight = st.number_input("Mean Flight Time (ms)", 30, 500, 150, key="typ_flight")
        wpm = st.number_input("Typing Speed (WPM)", 10, 200, 50, key="typ_wpm")
    with col2:
        error_rate = st.slider("Error Rate", 0.0, 0.3, 0.05, key="typ_err")
        rhythm_var = st.number_input("Rhythm Variance (ms)", 0, 200, 40, key="typ_var")
        total_keys = st.number_input("Total Keys Typed", 10, 10000, 500, key="typ_total")

    if st.button("Ingest Typing Data", type="primary", key="btn_typing"):
        events = [{'dwell_time': dwell, 'flight_time': flight, 'timestamp': i * 200, 'key': 'a'}
                  for i in range(min(total_keys, 100))]
        result = profiler.ingest_modality(subject_id, 'typing', {
            'keystroke_events': events,
            'summary': {
                'mean_dwell_time': dwell, 'mean_flight_time': flight,
                'typing_speed_wpm': wpm, 'error_rate': error_rate,
                'rhythm_variance': rhythm_var, 'total_keys': total_keys
            }
        })
        display_ingestion_result(result)


def render_fingerprint_input(profiler, subject_id):
    st.subheader("Dermatoglyphic Analysis")
    st.markdown("Enter fingerprint pattern data for each finger.")

    fingers = ['right_thumb', 'right_index', 'right_middle', 'right_ring', 'right_little',
               'left_thumb', 'left_index', 'left_middle', 'left_ring', 'left_little']
    patterns = {}
    cols = st.columns(5)
    for i, finger in enumerate(fingers):
        with cols[i % 5]:
            label = finger.replace('_', ' ').title()
            patterns[finger] = st.selectbox(label, ['loop', 'whorl', 'arch', 'composite'], key=f"fp_{finger}")

    ridge_count = st.number_input("Total Ridge Count", 50, 300, 150, key="fp_ridge")

    if st.button("Ingest Fingerprint Data", type="primary", key="btn_fp"):
        result = profiler.ingest_modality(subject_id, 'fingerprint', {
            'patterns': patterns,
            'total_ridge_count': ridge_count,
        })
        display_ingestion_result(result)


def render_genetic_input(profiler, subject_id):
    st.subheader("Genetic Data (SNP Markers)")
    st.markdown("Enter known SNP genotypes from genetic testing (23andMe, AncestryDNA, etc.)")

    snps = {}
    col1, col2 = st.columns(2)
    with col1:
        st.markdown("**Consciousness-Related:**")
        snps['rs4680'] = st.selectbox("COMT Val158Met (rs4680)", ['Unknown', 'GG', 'AG', 'AA'], key="gen_comt")
        snps['rs324420'] = st.selectbox("FAAH C385A (rs324420)", ['Unknown', 'CC', 'CA', 'AA'], key="gen_faah")
        snps['rs6265'] = st.selectbox("BDNF Val66Met (rs6265)", ['Unknown', 'CC', 'CT', 'TT'], key="gen_bdnf")
        snps['rs1800497'] = st.selectbox("DRD2 Taq1A (rs1800497)", ['Unknown', 'CC', 'CT', 'TT'], key="gen_drd2")

    with col2:
        st.markdown("**Pharmacogenomic:**")
        snps['rs3892097'] = st.selectbox("CYP2D6 (rs3892097)", ['Unknown', 'CC', 'CT', 'TT'], key="gen_cyp2d6")
        snps['rs4244285'] = st.selectbox("CYP2C19 (rs4244285)", ['Unknown', 'GG', 'GA', 'AA'], key="gen_cyp2c19")
        snps['rs1801133'] = st.selectbox("MTHFR C677T (rs1801133)", ['Unknown', 'CC', 'CT', 'TT'], key="gen_mthfr")

    clean_snps = {k: v for k, v in snps.items() if v != 'Unknown'}

    if st.button("Ingest Genetic Data", type="primary", key="btn_gen"):
        result = profiler.ingest_modality(subject_id, 'genetic', {'snps': clean_snps})
        display_ingestion_result(result)


def render_spirometry_input(profiler, subject_id):
    st.subheader("Spirometry / Breath Monitoring")

    col1, col2 = st.columns(2)
    with col1:
        rate = st.number_input("Respiratory Rate (breaths/min)", 3, 40, 15, key="sp_rate")
        ie_ratio = st.number_input("I:E Ratio", 1.0, 5.0, 2.0, 0.1, key="sp_ie")
        tidal = st.number_input("Tidal Volume (mL)", 200, 1500, 500, key="sp_tidal")
    with col2:
        hold = st.number_input("Breath Hold Time (sec)", 0, 120, 30, key="sp_hold")
        rsa = st.number_input("RSA Amplitude", 0.0, 50.0, 10.0, 1.0, key="sp_rsa")
        reg = st.slider("Regularity Score", 0.0, 1.0, 0.7, key="sp_reg")

    if st.button("Ingest Spirometry Data", type="primary", key="btn_sp"):
        result = profiler.ingest_modality(subject_id, 'spirometry', {
            'respiratory_rate': rate, 'ie_ratio': ie_ratio, 'tidal_volume': tidal,
            'breath_hold_seconds': hold, 'rsa_amplitude': rsa, 'regularity': reg,
        })
        display_ingestion_result(result)


def render_apple_watch_input(profiler, subject_id):
    st.subheader("Apple Watch / Apple Health Metrics")

    col1, col2, col3 = st.columns(3)
    with col1:
        st.markdown("**Cardiovascular**")
        rhr = st.number_input("Resting HR", 40, 120, 65, key="aw_rhr")
        hrv = st.number_input("HRV (SDNN ms)", 5, 200, 45, key="aw_hrv")
        vo2 = st.number_input("VO2 Max", 15, 70, 38, key="aw_vo2")
        spo2 = st.number_input("SpO2 (%)", 85, 100, 97, key="aw_spo2")

    with col2:
        st.markdown("**Movement**")
        steps = st.number_input("Steps Today", 0, 50000, 7000, key="aw_steps")
        gait_sym = st.slider("Gait Symmetry (%)", 30.0, 100.0, 95.0, key="aw_gait")
        walk_steady = st.selectbox("Walking Steadiness", ['OK', 'Low', 'Very Low'], key="aw_steady")
        walk_speed = st.number_input("Walking Speed (m/s)", 0.5, 2.5, 1.2, 0.1, key="aw_speed")

    with col3:
        st.markdown("**Temperature & Sleep**")
        temp_dev = st.number_input("Wrist Temp Deviation (C)", -3.0, 3.0, 0.0, 0.1, key="aw_temp")
        sleep_dur = st.number_input("Sleep Duration (hrs)", 3.0, 12.0, 7.5, 0.5, key="aw_sleep")
        deep_pct = st.number_input("Deep Sleep %", 0, 40, 18, key="aw_deep")
        rem_pct = st.number_input("REM Sleep %", 0, 40, 22, key="aw_rem")

    if st.button("Ingest Apple Watch Data", type="primary", key="btn_aw"):
        result = profiler.ingest_modality(subject_id, 'apple_watch', {
            'cardiovascular': {'resting_hr': rhr, 'hrv_sdnn': hrv, 'vo2_max': vo2, 'spo2': spo2},
            'movement': {'steps': steps, 'gait_symmetry': gait_sym, 'walking_steadiness': walk_steady,
                        'walking_speed': walk_speed, 'step_length': 0.7, 'double_support_time': 28},
            'temperature': {'wrist_deviation': temp_dev},
            'sleep': {'duration_hours': sleep_dur, 'deep_pct': deep_pct, 'rem_pct': rem_pct},
        })
        display_ingestion_result(result)


def render_facial_input(profiler, subject_id):
    st.subheader("Facial Ratio Analysis")

    col1, col2 = st.columns(2)
    with col1:
        fwhr = st.number_input("Facial Width-to-Height Ratio", 1.4, 2.5, 1.85, 0.01, key="fc_fwhr")
        sym = st.slider("Facial Symmetry Score", 0.0, 1.0, 0.88, key="fc_sym")
    with col2:
        golden = st.number_input("Golden Ratio Deviation", 0.0, 0.5, 0.08, 0.01, key="fc_golden")
        neo = st.slider("Neoteny Index", 0.0, 1.0, 0.55, key="fc_neo")

    if st.button("Ingest Facial Data", type="primary", key="btn_fc"):
        result = profiler.ingest_modality(subject_id, 'facial', {
            'fwhr': fwhr, 'symmetry_score': sym, 'golden_ratio_deviation': golden,
            'neoteny_index': neo, 'thirds_ratio': [0.33, 0.33, 0.34],
        })
        display_ingestion_result(result)


def render_digit_ratio_input(profiler, subject_id):
    st.subheader("Digit Ratio (2D:4D) Analysis")

    col1, col2 = st.columns(2)
    with col1:
        right = st.number_input("Right Hand 2D:4D", 0.85, 1.10, 0.95, 0.001, key="dr_right")
        left = st.number_input("Left Hand 2D:4D", 0.85, 1.10, 0.96, 0.001, key="dr_left")
    with col2:
        sex = st.selectbox("Biological Sex", ['unknown', 'male', 'female'], key="dr_sex")

    if st.button("Ingest Digit Ratio Data", type="primary", key="btn_dr"):
        result = profiler.ingest_modality(subject_id, 'digit_ratio', {
            'right_hand_ratio': right, 'left_hand_ratio': left, 'biological_sex': sex,
        })
        display_ingestion_result(result)


def render_oura_input(profiler, subject_id):
    st.subheader("Oura Ring Data")

    col1, col2, col3 = st.columns(3)
    with col1:
        st.markdown("**Sleep**")
        sleep_score = st.number_input("Sleep Score", 0, 100, 78, key="ou_sleep")
        deep = st.number_input("Deep Sleep %", 0, 50, 18, key="ou_deep")
        rem = st.number_input("REM Sleep %", 0, 50, 22, key="ou_rem")
        hrv_sleep = st.number_input("Average HRV (ms)", 5, 200, 42, key="ou_hrv")

    with col2:
        st.markdown("**Vitals**")
        rhr = st.number_input("Lowest Resting HR", 35, 100, 52, key="ou_rhr")
        resp = st.number_input("Respiratory Rate", 10.0, 25.0, 15.5, 0.5, key="ou_resp")
        temp = st.number_input("Temp Deviation", -3.0, 3.0, 0.1, 0.1, key="ou_temp")

    with col3:
        st.markdown("**Scores**")
        readiness = st.number_input("Readiness Score", 0, 100, 75, key="ou_ready")
        activity = st.number_input("Activity Score", 0, 100, 70, key="ou_activity")
        steps = st.number_input("Steps", 0, 30000, 6500, key="ou_steps")

    if st.button("Ingest Oura Data", type="primary", key="btn_ou"):
        result = profiler.ingest_modality(subject_id, 'oura', {
            'sleep': {'score': sleep_score, 'deep_sleep_pct': deep, 'rem_sleep_pct': rem,
                     'average_hrv': hrv_sleep, 'lowest_resting_hr': rhr,
                     'respiratory_rate': resp, 'temperature_deviation': temp},
            'readiness': {'score': readiness},
            'activity': {'score': activity, 'steps': steps},
        })
        display_ingestion_result(result)


def render_voice_input(profiler, subject_id):
    st.subheader("Voice Analysis")

    col1, col2 = st.columns(2)
    with col1:
        f0 = st.number_input("Fundamental Frequency (Hz)", 60, 400, 150, key="vc_f0")
        f0_range = st.number_input("F0 Range (Hz)", 10, 200, 50, key="vc_range")
        jitter = st.number_input("Jitter", 0.001, 0.1, 0.012, 0.001, key="vc_jitter", format="%.3f")
        shimmer = st.number_input("Shimmer", 0.001, 0.2, 0.035, 0.001, key="vc_shimmer", format="%.3f")
    with col2:
        hnr = st.number_input("Harmonics-to-Noise Ratio (dB)", 0, 40, 20, key="vc_hnr")
        rate = st.number_input("Speaking Rate (WPM)", 80, 220, 135, key="vc_rate")
        pause = st.slider("Pause Ratio", 0.0, 0.5, 0.15, key="vc_pause")

    if st.button("Ingest Voice Data", type="primary", key="btn_vc"):
        result = profiler.ingest_modality(subject_id, 'voice', {
            'fundamental_frequency': f0, 'f0_range': f0_range,
            'jitter': jitter, 'shimmer': shimmer, 'hnr': hnr,
            'speaking_rate_wpm': rate, 'pause_ratio': pause,
        })
        display_ingestion_result(result)


def render_numerology_input(profiler, subject_id):
    st.subheader("Name & Birthday Numerology / Astrology")
    st.info("This is a Tralse assessment - pattern-based, mechanism not scientifically established.")

    col1, col2 = st.columns(2)
    with col1:
        full_name = st.text_input("Full Birth Name", key="num_name")
        birth_date = st.text_input("Birth Date (YYYY-MM-DD)", key="num_bday")
    with col2:
        birth_time = st.text_input("Birth Time (HH:MM, optional)", key="num_time")
        birth_loc = st.text_input("Birth Location (optional)", key="num_loc")

    if st.button("Compute Numerology/Astrology", type="primary", key="btn_num"):
        if full_name or birth_date:
            result = profiler.ingest_modality(subject_id, 'numerology', {
                'full_name': full_name, 'birth_date': birth_date,
                'birth_time': birth_time, 'birth_location': birth_loc,
            })
            display_ingestion_result(result)
        else:
            st.warning("Please enter at least a name or birth date.")


def render_unified_profile(profiler):
    st.header("Unified GILE Profile")

    try:
        subjects = profiler.list_subjects()
        subject_options = {f"{s['name']} (ID: {s['id']})": s['id'] for s in subjects}
    except:
        subject_options = {}

    if not subject_options:
        st.info("Create a subject and add data first.")
        return

    selected = st.selectbox("Select Subject", list(subject_options.keys()), key="profile_subject")
    subject_id = subject_options[selected]

    if st.button("Build/Refresh Unified Profile", type="primary", key="btn_profile"):
        profile = profiler.build_unified_profile(subject_id)

        if 'error' in profile:
            st.error(profile['error'])
            return

        st.session_state['current_profile'] = profile

    profile = st.session_state.get('current_profile')
    if profile and 'error' not in (profile or {}):
        gile = profile['gile']

        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("G (Existence)", f"{gile['G']:.3f}")
        with col2:
            st.metric("I (Intuition)", f"{gile['I']:.3f}")
        with col3:
            st.metric("L (Love)", f"{gile['L']:.3f}")
        with col4:
            st.metric("E (Environment)", f"{gile['E']:.3f}")

        st.markdown("---")

        col1, col2, col3 = st.columns(3)
        with col1:
            mood = profile['mood_score']
            st.metric("Mood Score", f"{mood:.3f}",
                     delta="Good" if mood > 0.6 else "Moderate" if mood > 0.4 else "Low")
        with col2:
            health = profile['health_score']
            st.metric("Health Score", f"{health:.3f}",
                     delta="Good" if health > 0.6 else "Moderate" if health > 0.4 else "Low")
        with col3:
            cons = profile['consciousness_level']
            st.metric("Consciousness Level", f"{cons:.3f}",
                     delta="High" if cons > 0.7 else "Moderate" if cons > 0.4 else "Developing")

        st.markdown("---")

        col1, col2 = st.columns(2)
        with col1:
            st.metric("LCC Estimate", f"{profile['lcc_estimate']:.3f}")
        with col2:
            conf = profile['tralse_confidence']
            state = profile['tralse_state']
            color = "green" if state == 'true' else "orange" if state == 'tralse' else "red"
            st.metric("Tralse Confidence", f"{conf:.3f} ({state.upper()})")

        st.markdown(f"**Modalities Used:** {', '.join(profile['modalities_used'])} ({profile['modality_count']} total)")

        with st.expander("Modality Details"):
            for mod, details in profile.get('modality_details', {}).items():
                st.markdown(f"### {mod.replace('_', ' ').title()}")
                st.markdown(f"Evidence Level: **{details.get('evidence_level', 'unknown')}** | Quality: **{details.get('quality', 0):.3f}**")
                gile_mod = details.get('gile', {})
                st.markdown(f"GILE: G={gile_mod.get('G', 0):.3f} | I={gile_mod.get('I', 0):.3f} | L={gile_mod.get('L', 0):.3f} | E={gile_mod.get('E', 0):.3f}")
                with st.expander(f"Raw Features ({mod})"):
                    st.json(details.get('features', {}))

    history = None
    try:
        history = profiler.get_subject_history(subject_id)
    except:
        pass

    if history and history.get('profile_history'):
        with st.expander("Profile History"):
            for p in history['profile_history']:
                g = p['gile']
                st.markdown(f"**{p['timestamp']}** - G:{g['G']:.2f} I:{g['I']:.2f} L:{g['L']:.2f} E:{g['E']:.2f} | Mood:{p['mood']:.2f} | Health:{p['health']:.2f}")


def render_compatibility(profiler):
    st.header("Compatibility Matching")

    try:
        subjects = profiler.list_subjects()
        subject_options = {f"{s['name']} (ID: {s['id']})": s['id'] for s in subjects}
    except:
        subject_options = {}

    if len(subject_options) < 2:
        st.info("Need at least 2 subjects with data to compute compatibility.")
        return

    col1, col2 = st.columns(2)
    with col1:
        person_a = st.selectbox("Person A", list(subject_options.keys()), key="compat_a")
    with col2:
        remaining = [k for k in subject_options.keys() if k != person_a]
        person_b = st.selectbox("Person B", remaining, key="compat_b")

    context = st.selectbox("Compatibility Context", ['romantic', 'business', 'friendship'], key="compat_ctx")

    if st.button("Compute Compatibility", type="primary", key="btn_compat"):
        result = profiler.compute_compatibility(
            subject_options[person_a],
            subject_options[person_b],
            context
        )

        if 'error' in result:
            st.error(result['error'])
            return

        score = result['overall_score']
        if score >= 80:
            st.success(f"Overall Compatibility: {score:.1f}% - Excellent Match!")
        elif score >= 60:
            st.info(f"Overall Compatibility: {score:.1f}% - Good Match")
        elif score >= 40:
            st.warning(f"Overall Compatibility: {score:.1f}% - Moderate Match")
        else:
            st.error(f"Overall Compatibility: {score:.1f}% - Challenging Match")

        st.markdown("---")
        st.subheader("Dimensional Analysis")
        for dim, data in result.get('dimension_comparison', {}).items():
            dim_names = {'G': 'Goodness/Existence', 'I': 'Intuition', 'L': 'Love/Connection', 'E': 'Environment'}
            diff = data['diff']
            status = "Aligned" if diff < 0.15 else "Moderate Gap" if diff < 0.3 else "Significant Gap"
            st.markdown(f"**{dim_names.get(dim, dim)}**: A={data['a']:.3f} vs B={data['b']:.3f} ({status})")

        if result.get('strengths'):
            st.subheader("Strengths")
            for s in result['strengths']:
                st.markdown(f"- {s}")

        if result.get('growth_areas'):
            st.subheader("Growth Areas")
            for g in result['growth_areas']:
                st.markdown(f"- {g}")

        conf = result.get('tralse_confidence', 0)
        st.markdown(f"**Tralse Confidence:** {conf:.3f}")


def render_stranger_profiling(profiler):
    st.header("Public Data Profile Estimation")
    st.info("Estimates a GILE profile from publicly available data. All results carry low-Tralse confidence.")

    col1, col2 = st.columns(2)
    with col1:
        st.subheader("Identity Data")
        name = st.text_input("Name", key="str_name")
        birth_date = st.text_input("Birth Date (YYYY-MM-DD)", key="str_bday")

    with col2:
        st.subheader("Observable Data")
        voice_f0 = st.number_input("Voice F0 (Hz, from recordings)", 0, 400, 0, key="str_f0")
        fwhr = st.number_input("Facial WHR (from photos)", 0.0, 3.0, 0.0, 0.01, key="str_fwhr")
        facial_sym = st.slider("Est. Facial Symmetry", 0.0, 1.0, 0.0, key="str_sym")

    if st.button("Estimate Profile", type="primary", key="btn_stranger"):
        public_data = {}
        if name:
            public_data['full_name'] = name
            public_data['name'] = name
        if birth_date:
            public_data['birth_date'] = birth_date
        if voice_f0 > 0:
            public_data['voice_f0'] = voice_f0
        if fwhr > 0:
            public_data['fwhr'] = fwhr
        if facial_sym > 0:
            public_data['facial_symmetry'] = facial_sym

        if not public_data:
            st.warning("Enter at least some data to estimate a profile.")
            return

        result = profiler.estimate_stranger_profile(public_data)

        if 'error' in result:
            st.error(result['error'])
            return

        st.subheader("Estimated GILE Profile")
        gile = result['estimated_gile']
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("G (Existence)", f"{gile['G']:.3f}")
        with col2:
            st.metric("I (Intuition)", f"{gile['I']:.3f}")
        with col3:
            st.metric("L (Love)", f"{gile['L']:.3f}")
        with col4:
            st.metric("E (Environment)", f"{gile['E']:.3f}")

        st.markdown(f"**Data Sources:** {', '.join(result['modalities_available'])} ({result['data_sources']} channels)")
        st.warning(f"Confidence: {result['tralse_confidence']} - {result['confidence_note']}")

        with st.expander("Detailed Modality Analysis"):
            for mod, data in result.get('modality_details', {}).items():
                st.markdown(f"### {mod.replace('_', ' ').title()}")
                st.json(data.get('features', {}))


def display_ingestion_result(result):
    if 'error' in result:
        st.error(result['error'])
        return

    st.success(f"Data ingested for modality: **{result['modality']}** (Quality: {result['quality']:.3f})")

    gile = result.get('gile_scores', {})
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("G", f"{gile.get('G', 0):.3f}")
    with col2:
        st.metric("I", f"{gile.get('I', 0):.3f}")
    with col3:
        st.metric("L", f"{gile.get('L', 0):.3f}")
    with col4:
        st.metric("E", f"{gile.get('E', 0):.3f}")

    with st.expander("Full Feature Extraction"):
        st.json(result.get('features', {}))


if __name__ == "__main__":
    render_multimodal_biometric_dashboard()
