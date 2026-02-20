"""
MedGemma Impact Challenge Dashboard
======================================
Streamlit dashboard for the Google Research MedGemma Impact Challenge.
GILE-enhanced clinical decision support with emergency triage,
risk prediction, and MedGemma prompt generation.
"""

import streamlit as st
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.medgemma_health_engine import (
    GILEHealthScore, PatientProfile, TralseConfidenceScorer,
    RiskStratificationEngine, OfflineClinicalGuidelines,
    ESI_LEVELS, CRITICAL_SYMPTOMS, HIGH_PRIORITY_SYMPTOMS, VITAL_SIGN_RANGES,
)


def get_engine():
    if 'medgemma_engine' not in st.session_state:
        st.session_state['medgemma_engine'] = {
            'risk_engine': RiskStratificationEngine(),
            'tralse_scorer': TralseConfidenceScorer(),
            'guidelines': OfflineClinicalGuidelines(),
        }
    return st.session_state['medgemma_engine']


def display_gile_scores(gile_dict):
    cols = st.columns(4)
    color_map = {'G': '🟢', 'I': '🔵', 'L': '🩷', 'E': '🟠'}
    label_map = {'G': 'Goodness', 'I': 'Intuition', 'L': 'Love', 'E': 'Existence'}
    for idx, dim in enumerate(['G', 'I', 'L', 'E']):
        with cols[idx]:
            val = gile_dict.get(dim, 0)
            st.metric(f"{color_map[dim]} {dim} ({label_map[dim]})", f"{val:.3f}")


def display_tralse_badge(confidence_data):
    label = confidence_data.get('label', 'Tralse')
    conf = confidence_data.get('confidence', 0)
    if label == 'True':
        st.success(f"✅ Tralse Confidence: **{conf:.3f}** — {label} (High Confidence)")
    elif label == 'Tralse':
        st.warning(f"⚠️ Tralse Confidence: **{conf:.3f}** — {label} (Moderate — Review Needed)")
    else:
        st.error(f"❌ Tralse Confidence: **{conf:.3f}** — {label} (Low — Escalate)")


def render_medgemma_dashboard():
    st.title("🏥 MedGemma Impact Challenge")
    st.markdown("*GILE-Enhanced Clinical Decision Support for Google Research MedGemma Hackathon*")

    tabs = st.tabs([
        "Patient Assessment",
        "Emergency Triage",
        "Risk Prediction",
        "MedGemma Prompts",
        "Competition Info",
    ])

    with tabs[0]:
        render_patient_assessment()
    with tabs[1]:
        render_emergency_triage()
    with tabs[2]:
        render_risk_prediction()
    with tabs[3]:
        render_prompt_generator()
    with tabs[4]:
        render_competition_info()


def render_patient_assessment():
    st.header("Patient Assessment")
    st.markdown("Enter patient data for GILE health assessment with risk stratification.")

    with st.form("patient_assessment_form", clear_on_submit=False):
        col1, col2 = st.columns(2)
        with col1:
            age = st.number_input("Age", 1, 120, 55, key="pa_age")
            sex = st.selectbox("Sex", ["male", "female", "other"], key="pa_sex")
        with col2:
            smoking = st.selectbox("Smoking Status", ["never", "former", "current"], key="pa_smoking")

        st.subheader("Symptoms")
        all_symptoms = sorted(list(CRITICAL_SYMPTOMS | HIGH_PRIORITY_SYMPTOMS | {
            "fatigue", "nausea", "dizziness", "cough", "joint_pain",
            "back_pain", "insomnia", "anxiety", "weight_loss", "swelling",
        }))
        symptoms = st.multiselect("Select Symptoms", all_symptoms, key="pa_symptoms")

        st.subheader("Vital Signs")
        v1, v2, v3 = st.columns(3)
        with v1:
            systolic_bp = st.number_input("Systolic BP (mmHg)", 60, 250, 120, key="pa_sbp")
            diastolic_bp = st.number_input("Diastolic BP (mmHg)", 30, 160, 80, key="pa_dbp")
        with v2:
            heart_rate = st.number_input("Heart Rate (bpm)", 30, 220, 72, key="pa_hr")
            temperature = st.number_input("Temperature (°C)", 34.0, 42.0, 36.8, 0.1, key="pa_temp")
        with v3:
            spo2 = st.number_input("SpO2 (%)", 70, 100, 98, key="pa_spo2")
            resp_rate = st.number_input("Respiratory Rate", 5, 50, 16, key="pa_rr")

        st.subheader("Lab Values")
        l1, l2, l3 = st.columns(3)
        with l1:
            glucose = st.number_input("Fasting Glucose (mg/dL)", 30, 600, 95, key="pa_gluc")
            cholesterol = st.number_input("Total Cholesterol (mg/dL)", 80, 500, 200, key="pa_chol")
        with l2:
            hdl = st.number_input("HDL Cholesterol (mg/dL)", 10, 120, 55, key="pa_hdl")
            ldl = st.number_input("LDL Cholesterol (mg/dL)", 30, 300, 120, key="pa_ldl")
        with l3:
            triglycerides = st.number_input("Triglycerides (mg/dL)", 30, 800, 150, key="pa_trig")
            hba1c = st.number_input("HbA1c (%)", 3.0, 15.0, 5.4, 0.1, key="pa_hba1c")

        submitted = st.form_submit_button("Run GILE Health Assessment", type="primary")

    if submitted:
        try:
            engine = get_engine()
            patient_data = {
                'age': age, 'sex': sex, 'smoking_status': smoking,
                'systolic_bp': systolic_bp, 'diastolic_bp': diastolic_bp,
                'total_cholesterol': cholesterol, 'hdl_cholesterol': hdl,
                'fasting_glucose': glucose, 'hba1c': hba1c,
                'symptoms': symptoms,
            }

            vital_scores = []
            for vital, val in [('heart_rate', heart_rate), ('systolic_bp', systolic_bp),
                               ('temperature', temperature), ('spo2', spo2),
                               ('respiratory_rate', resp_rate)]:
                ranges = VITAL_SIGN_RANGES.get(vital, {})
                if ranges:
                    nl, nh = ranges.get('normal_low', 0), ranges.get('normal_high', 200)
                    if nl <= val <= nh:
                        vital_scores.append(1.0)
                    elif val < ranges.get('critical_low', 0) or val > ranges.get('critical_high', 300):
                        vital_scores.append(0.1)
                    else:
                        vital_scores.append(0.5)

            e_score = sum(vital_scores) / max(1, len(vital_scores))
            g_score = max(0, min(1, 1.0 - len([s for s in symptoms if s in CRITICAL_SYMPTOMS]) / 3.0))
            i_score = 0.8 if len(symptoms) <= 3 else 0.5
            l_score = 0.9 if smoking == 'never' else 0.6

            gile = GILEHealthScore(goodness=g_score, intuition=i_score, love=l_score, existence=e_score)

            st.markdown("---")
            st.subheader("GILE Health Assessment")
            display_gile_scores(gile.to_dict())

            c1, c2 = st.columns(2)
            with c1:
                st.metric("Composite Score", f"{gile.composite:.3f}")
            with c2:
                label = gile.tralse_label
                color = "🟢" if label == "True" else "🟡" if label == "Tralse" else "🔴"
                st.metric("Tralse Assessment", f"{color} {label}")

            cv_risk = engine['risk_engine'].cardiovascular_risk(patient_data)
            st.markdown("---")
            st.subheader("Risk Stratification")
            r1, r2 = st.columns(2)
            with r1:
                st.metric("CV Risk (10yr)", f"{cv_risk['ten_year_risk_pct']}%")
                st.caption(f"Category: **{cv_risk['risk_category'].replace('_', ' ').title()}**")
            with r2:
                if cv_risk.get('modifiable_factors'):
                    st.markdown("**Modifiable Factors:**")
                    for f in cv_risk['modifiable_factors']:
                        st.markdown(f"- {f.replace('_', ' ').title()}")

            if cv_risk.get('tralse_confidence'):
                display_tralse_badge(cv_risk['tralse_confidence'])

            conditions_to_check = []
            if systolic_bp >= 130 or diastolic_bp >= 80:
                conditions_to_check.append('hypertension')
            if hba1c >= 5.7 or glucose >= 100:
                conditions_to_check.append('diabetes_type2')

            if conditions_to_check:
                st.markdown("---")
                st.subheader("Intervention Recommendations")
                for cond in conditions_to_check:
                    guideline = OfflineClinicalGuidelines.get_guideline(cond)
                    if guideline:
                        with st.expander(f"📋 {cond.replace('_', ' ').title()} Guidelines"):
                            for intervention in guideline.get('interventions', []):
                                st.markdown(f"- {intervention}")
                            st.caption(f"Follow-up in {guideline.get('follow_up_days', 30)} days")

        except Exception as e:
            st.error(f"Assessment error: {str(e)}")


def render_emergency_triage():
    st.header("Emergency Triage")
    st.markdown("Quick ESI-based triage assessment with GILE scoring.")

    col1, col2 = st.columns(2)
    with col1:
        st.subheader("Symptom Checklist")
        critical_selected = []
        for sym in sorted(CRITICAL_SYMPTOMS):
            if st.checkbox(sym.replace('_', ' ').title(), key=f"triage_crit_{sym}"):
                critical_selected.append(sym)

    with col2:
        st.subheader("Vital Signs")
        t_hr = st.number_input("Heart Rate", 30, 250, 80, key="triage_hr")
        t_sbp = st.number_input("Systolic BP", 50, 250, 120, key="triage_sbp")
        t_rr = st.number_input("Respiratory Rate", 4, 60, 16, key="triage_rr")
        t_spo2 = st.number_input("SpO2 (%)", 50, 100, 97, key="triage_spo2")
        t_temp = st.number_input("Temperature (°C)", 34.0, 42.0, 37.0, 0.1, key="triage_temp")
        t_gcs = st.slider("GCS Score", 3, 15, 15, key="triage_gcs")

    if st.button("Calculate ESI Level", type="primary", key="btn_triage"):
        try:
            esi_level = 5
            if t_gcs <= 8 or any(s in critical_selected for s in ['cardiac_arrest', 'unconsciousness']):
                esi_level = 1
            elif len(critical_selected) > 0 or t_spo2 < 90:
                esi_level = 2
            elif t_hr > 130 or t_sbp < 90 or t_rr > 28 or t_temp > 39.0:
                esi_level = 2
            elif t_hr > 100 or t_sbp > 160 or t_rr > 22 or t_temp > 38.5:
                esi_level = 3
            elif len(critical_selected) == 0 and t_spo2 >= 95:
                esi_level = 4 if t_hr > 90 or t_temp > 37.5 else 5

            esi_info = ESI_LEVELS[esi_level]
            esi_colors = {1: '🔴', 2: '🟠', 3: '🟡', 4: '🟢', 5: '🔵'}

            st.markdown("---")
            st.subheader(f"{esi_colors[esi_level]} ESI Level {esi_level}: {esi_info['label']}")
            st.markdown(f"**{esi_info['description']}**")

            m1, m2, m3 = st.columns(3)
            with m1:
                st.metric("Max Wait", f"{esi_info['max_wait_minutes']} min")
            with m2:
                st.metric("Resources", esi_info['resources'].replace('_', ' ').title())
            with m3:
                st.metric("Critical Symptoms", len(critical_selected))

            if esi_level <= 2:
                st.error("⚠️ IMMEDIATE ATTENTION REQUIRED — Activate emergency protocol")
            elif esi_level == 3:
                st.warning("Urgent — Multiple resources likely needed")
            else:
                st.info("Stable — Standard assessment pathway")

            evidence = {
                'vital_stability': max(0.1, min(1.0, t_spo2 / 100.0)),
                'symptom_severity': max(0.1, 1.0 - len(critical_selected) / 5.0),
                'consciousness': t_gcs / 15.0,
            }
            tralse = TralseConfidenceScorer.score(evidence)
            display_tralse_badge(tralse)

        except Exception as e:
            st.error(f"Triage error: {str(e)}")


def render_risk_prediction():
    st.header("Risk Prediction Dashboard")
    st.markdown("Multi-disease risk assessment with GILE-enhanced scoring.")

    with st.form("risk_form", clear_on_submit=False):
        c1, c2, c3 = st.columns(3)
        with c1:
            r_age = st.number_input("Age", 18, 100, 50, key="risk_age")
            r_sex = st.selectbox("Sex", ["male", "female"], key="risk_sex")
            r_smoking = st.selectbox("Smoking", ["never", "former", "current"], key="risk_smoking")
        with c2:
            r_sbp = st.number_input("Systolic BP", 80, 220, 130, key="risk_sbp")
            r_chol = st.number_input("Total Cholesterol", 100, 400, 220, key="risk_chol")
            r_hdl = st.number_input("HDL", 20, 100, 50, key="risk_hdl")
        with c3:
            r_glucose = st.number_input("Fasting Glucose", 60, 400, 100, key="risk_gluc")
            r_hba1c = st.number_input("HbA1c", 4.0, 14.0, 5.6, 0.1, key="risk_hba1c")
            r_bmi = st.number_input("BMI", 15.0, 50.0, 26.0, 0.5, key="risk_bmi")
        submitted = st.form_submit_button("Calculate All Risks", type="primary")

    if submitted:
        try:
            patient = {
                'age': r_age, 'sex': r_sex, 'systolic_bp': r_sbp,
                'total_cholesterol': r_chol, 'hdl_cholesterol': r_hdl,
                'smoking_status': r_smoking, 'fasting_glucose': r_glucose,
                'hba1c': r_hba1c, 'bmi': r_bmi,
            }

            cv = RiskStratificationEngine.cardiovascular_risk(patient)
            db = RiskStratificationEngine.diabetes_risk(patient)
            mh = RiskStratificationEngine.mental_health_screening({
                'phq9_score': 3, 'gad7_score': 2, 'sleep_quality': 6,
                'social_support_score': 7,
            })

            resp_risk = max(0.05, min(0.8,
                (1 if r_smoking == 'current' else 0) * 0.3 +
                (r_age / 100) * 0.2 + 0.1
            ))

            st.markdown("---")
            st.subheader("Risk Summary")

            risks = [
                ("Cardiovascular", cv['ten_year_risk_pct'] / 30.0, cv['risk_category']),
                ("Diabetes", db['findrisc_score'] / 26.0, db['risk_level']),
                ("Respiratory", resp_risk, "elevated" if resp_risk > 0.3 else "low"),
                ("Mental Health", mh.get('gile_score', {}).get('composite', 0.3), mh.get('depression_severity', 'minimal')),
            ]

            for name, value, category in risks:
                c1, c2 = st.columns([3, 1])
                with c1:
                    st.markdown(f"**{name}**")
                    st.progress(min(1.0, max(0.0, value)))
                with c2:
                    st.caption(category.replace('_', ' ').title())

            st.markdown("---")
            st.subheader("Detailed GILE Scores")

            with st.expander("Cardiovascular GILE"):
                display_gile_scores(cv['gile_score'])
                display_tralse_badge(cv['tralse_confidence'])

            with st.expander("Diabetes GILE"):
                display_gile_scores(db['gile_score'])
                display_tralse_badge(db['tralse_confidence'])

        except Exception as e:
            st.error(f"Risk calculation error: {str(e)}")


def render_prompt_generator():
    st.header("MedGemma Prompt Generator")
    st.markdown("Generate formatted prompts for MedGemma tasks. Copy these for your Kaggle notebook.")

    task = st.selectbox("Select Task", [
        "Clinical Assessment",
        "Differential Diagnosis",
        "Treatment Planning",
        "Patient Education",
        "Radiology Report",
    ], key="prompt_task")

    prompts = {
        "Clinical Assessment": {
            "system": "You are MedGemma, a clinical decision support AI. Provide evidence-based assessments using GILE framework scoring (G=treatment efficacy, I=diagnostic confidence, L=patient care quality, E=physiological evidence).",
            "user_template": "Patient: {age}yo {sex}, presenting with {symptoms}.\nVitals: BP {bp}, HR {hr}, Temp {temp}°C, SpO2 {spo2}%.\nLabs: Glucose {glucose} mg/dL, HbA1c {hba1c}%.\n\nProvide:\n1. GILE health assessment scores (0-1 for each dimension)\n2. Primary assessment with confidence level\n3. Recommended next steps\n4. Tralse confidence classification (True/Tralse/False)",
        },
        "Differential Diagnosis": {
            "system": "You are MedGemma acting as a diagnostic reasoning engine. Generate differential diagnoses ranked by probability with GILE-weighted evidence scoring.",
            "user_template": "Chief complaint: {symptoms}\nHistory: {history}\nExam findings: {findings}\n\nGenerate top 5 differential diagnoses with:\n1. Probability estimate\n2. Key supporting evidence\n3. Key opposing evidence\n4. Recommended workup\n5. GILE confidence for each diagnosis",
        },
        "Treatment Planning": {
            "system": "You are MedGemma providing evidence-based treatment recommendations. Consider patient-specific factors, contraindications, and quality-of-life impact.",
            "user_template": "Diagnosis: {diagnosis}\nPatient: {age}yo {sex}, allergies: {allergies}, medications: {medications}\n\nProvide:\n1. First-line treatment with GILE scoring\n2. Alternative options\n3. Monitoring plan\n4. Expected outcomes with Tralse confidence",
        },
        "Patient Education": {
            "system": "You are MedGemma creating patient-friendly health education materials. Use clear language at a 6th-grade reading level.",
            "user_template": "Condition: {condition}\nPatient literacy level: {literacy}\n\nCreate:\n1. Simple explanation of the condition\n2. What the patient should do\n3. Warning signs to watch for\n4. When to seek emergency care",
        },
        "Radiology Report": {
            "system": "You are MedGemma analyzing medical imaging. Provide structured radiology reports with GILE confidence scoring for each finding.",
            "user_template": "Modality: {modality}\nIndication: {indication}\nFindings description: {findings}\n\nGenerate structured report with:\n1. Findings (with GILE confidence per finding)\n2. Impression\n3. Recommendations\n4. Overall Tralse confidence",
        },
    }

    prompt_data = prompts[task]

    st.markdown("### System Prompt")
    st.code(prompt_data["system"], language="text")

    st.markdown("### User Prompt Template")
    st.code(prompt_data["user_template"], language="text")

    st.markdown("### Usage in Kaggle Notebook")
    kaggle_code = f'''import google.generativeai as genai

genai.configure(api_key="YOUR_API_KEY")
model = genai.GenerativeModel("medgemma-multimodal")

response = model.generate_content([
    "{prompt_data['system']}",
    # Fill in your patient data below:
    """{prompt_data['user_template']}"""
])
print(response.text)'''
    st.code(kaggle_code, language="python")

    st.info("💡 Replace placeholder values with actual patient data before running in your Kaggle notebook.")


def render_competition_info():
    st.header("MedGemma Impact Challenge")

    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Deadline", "Feb 24, 2026")
    with c2:
        st.metric("Platform", "Kaggle")
    with c3:
        st.metric("Focus", "Healthcare AI")

    st.markdown("---")
    st.subheader("Competition Overview")
    st.markdown("""
    The **Google Research MedGemma Impact Challenge** invites participants to build
    impactful healthcare AI applications using the MedGemma family of models.

    **Our Approach — GILE-Enhanced Clinical Decision Support:**
    - **G (Goodness):** Treatment efficacy scoring and positive outcomes prediction
    - **I (Intuition):** Clinical pattern recognition and differential diagnosis
    - **L (Love):** Patient-centered care quality and holistic consideration
    - **E (Existence):** Physiological evidence strength and vital signs stability
    """)

    st.subheader("Strategy Overview")
    with st.expander("1. Offline/Edge Clinical Support"):
        st.markdown("""
        - Rule-based clinical guidelines cached locally
        - Triage decision trees for resource-constrained settings
        - Lightweight risk scoring without model inference
        - Ideal for rural clinics and field hospitals
        """)
    with st.expander("2. MedGemma-Augmented Diagnosis"):
        st.markdown("""
        - Structured prompt engineering for clinical assessment
        - Multi-turn diagnostic reasoning with evidence tracking
        - GILE-scored differential diagnosis generation
        - Tralse confidence for clinical decision uncertainty
        """)
    with st.expander("3. Risk Stratification Pipeline"):
        st.markdown("""
        - Framingham cardiovascular risk with GILE enhancement
        - FINDRISC diabetes screening with metabolic flags
        - PHQ-9/GAD-7 mental health screening
        - Multi-disease risk dashboard with progress tracking
        """)
    with st.expander("4. Submission Strategy"):
        st.markdown("""
        - Kaggle notebook with full pipeline demonstration
        - MedGemma API integration for inference
        - Offline fallback for edge deployment showcase
        - GILE framework adds unique evaluation dimension
        - Tralse confidence system addresses clinical uncertainty
        """)

    st.markdown("---")
    st.markdown("🔗 [Kaggle Competition Page](https://www.kaggle.com/competitions/medgemma-impact-challenge)")
