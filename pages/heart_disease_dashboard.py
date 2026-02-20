"""
Heart Disease Prediction Dashboard
=====================================
Streamlit dashboard for TI-Framework-Enhanced Heart Disease Classification.
Uses GILE feature engineering and Tralse confidence scoring on the
UCI/Cleveland heart disease dataset.
"""

import streamlit as st
import pandas as pd
import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.heart_disease_predictor import (
    HeartDiseasePredictor, FEATURE_COLUMNS, FEATURE_DESCRIPTIONS,
    GILE_FEATURE_MAP, TRALSE_THRESHOLDS,
)


def get_predictor():
    if 'heart_predictor' not in st.session_state:
        st.session_state['heart_predictor'] = HeartDiseasePredictor()
    return st.session_state['heart_predictor']


def display_gile_scores(gile_dict):
    cols = st.columns(4)
    color_map = {'G': '🟢', 'I': '🔵', 'L': '🩷', 'E': '🟠'}
    label_map = {'G': 'Goodness', 'I': 'Intuition', 'L': 'Love', 'E': 'Existence'}
    for idx, dim in enumerate(['G', 'I', 'L', 'E']):
        with cols[idx]:
            val = gile_dict.get(dim, gile_dict.get(f'{dim}_score', 0))
            if isinstance(val, dict):
                val = val.get('importance', 0)
            st.metric(f"{color_map[dim]} {dim} ({label_map[dim]})", f"{val:.3f}")


def render_heart_disease_dashboard():
    st.title("❤️ Heart Disease Prediction")
    st.markdown("*TI-Framework-Enhanced Classifier with GILE Feature Engineering & Tralse Confidence*")

    tabs = st.tabs([
        "Model Training",
        "GILE Feature Analysis",
        "Patient Prediction",
        "Model Comparison",
        "Cross-Validation",
        "Competition Info",
    ])

    with tabs[0]:
        render_model_training()
    with tabs[1]:
        render_gile_analysis()
    with tabs[2]:
        render_patient_prediction()
    with tabs[3]:
        render_model_comparison()
    with tabs[4]:
        render_cross_validation()
    with tabs[5]:
        render_competition_info()


def render_model_training():
    st.header("Model Training")
    predictor = get_predictor()

    if predictor.is_trained:
        st.success("✅ Models are trained and ready for predictions.")
    else:
        st.info("Train the ensemble on sample data (500 synthetic patients based on UCI Cleveland distributions).")

    if st.button("Train Ensemble Models", type="primary", key="btn_train"):
        try:
            with st.spinner("Loading and preprocessing data..."):
                df = predictor.load_data()
                X_train, X_test, y_train, y_test = predictor.preprocess(df)

            with st.spinner("Training 4 models + ensemble..."):
                train_results = predictor.train_ensemble(X_train, y_train)

            with st.spinner("Evaluating on test set..."):
                eval_results = predictor.evaluate(X_test, y_test)

            st.session_state['heart_train_results'] = train_results
            st.session_state['heart_eval_results'] = eval_results
            st.session_state['heart_test_data'] = (X_test, y_test)
            st.success("✅ All models trained and evaluated!")

        except Exception as e:
            st.error(f"Training error: {str(e)}")

    train_results = st.session_state.get('heart_train_results')
    eval_results = st.session_state.get('heart_eval_results')

    if train_results:
        st.markdown("---")
        st.subheader("Training Results")

        rows = []
        for name, metrics in train_results.items():
            if metrics.get('status') == 'trained':
                eval_m = eval_results.get(name, {}) if eval_results else {}
                rows.append({
                    'Model': name.replace('_', ' ').title(),
                    'Train Acc': metrics.get('train_accuracy', 0),
                    'Train AUC': metrics.get('train_auc', 0),
                    'Test Acc': eval_m.get('accuracy', '-'),
                    'Test AUC': eval_m.get('auc_roc', '-'),
                    'F1': eval_m.get('f1', '-'),
                })

        if rows:
            st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

    if eval_results and 'tralse_analysis' in eval_results:
        st.markdown("---")
        st.subheader("Tralse Zone Analysis")
        ta = eval_results['tralse_analysis']
        z1, z2, z3 = st.columns(3)
        zones = ta.get('zone_distribution', {})
        with z1:
            z_true = zones.get('True', {})
            st.metric("✅ True Zone", f"{z_true.get('count', 0)} ({z_true.get('percentage', 0)}%)")
            if z_true.get('accuracy') is not None:
                st.caption(f"Accuracy: {z_true['accuracy']:.1%}")
        with z2:
            z_tralse = zones.get('Tralse', {})
            st.metric("⚠️ Tralse Zone", f"{z_tralse.get('count', 0)} ({z_tralse.get('percentage', 0)}%)")
            if z_tralse.get('accuracy') is not None:
                st.caption(f"Accuracy: {z_tralse['accuracy']:.1%}")
        with z3:
            z_false = zones.get('False', {})
            st.metric("❌ False Zone", f"{z_false.get('count', 0)} ({z_false.get('percentage', 0)}%)")
            if z_false.get('accuracy') is not None:
                st.caption(f"Accuracy: {z_false['accuracy']:.1%}")

        st.metric("Specialist Review Needed", f"{ta.get('specialist_review_count', 0)} ({ta.get('specialist_review_pct', 0)}%)")


def render_gile_analysis():
    st.header("GILE Feature Analysis")
    st.markdown("How each of the 14 UCI features maps to GILE dimensions.")

    for dim in ['G', 'I', 'L', 'E']:
        info = GILE_FEATURE_MAP[dim]
        color_map = {'G': '🟢', 'I': '🔵', 'L': '🩷', 'E': '🟠'}
        with st.expander(f"{color_map[dim]} **{dim} — {info['description']}** (weight: {info['weight']})"):
            for feat in info['primary']:
                desc = FEATURE_DESCRIPTIONS.get(feat, feat)
                st.markdown(f"- **{feat}**: {desc}")

    predictor = get_predictor()
    if predictor.is_trained:
        st.markdown("---")
        st.subheader("Feature Importance by GILE Dimension")
        try:
            importance = predictor.feature_importance_gile()

            if 'gile_normalized' in importance:
                norm = importance['gile_normalized']
                chart_data = pd.DataFrame({
                    'Dimension': list(norm.keys()),
                    'Importance': list(norm.values()),
                })
                st.bar_chart(chart_data.set_index('Dimension'))

            if 'feature_importances' in importance:
                st.subheader("Individual Feature Importances")
                fi = importance['feature_importances']
                fi_df = pd.DataFrame({
                    'Feature': list(fi.keys()),
                    'Importance': list(fi.values()),
                }).sort_values('Importance', ascending=False)
                st.dataframe(fi_df, use_container_width=True, hide_index=True)

        except Exception as e:
            st.warning(f"Feature importance unavailable: {str(e)}")

    st.markdown("---")
    st.subheader("GILE Interaction Features")
    st.markdown("""
    The engine creates pairwise interaction features between GILE dimensions:
    """)
    interactions = [
        ("G×I", "Treatment response × Risk pattern"),
        ("G×L", "Treatment response × Lifestyle tolerance"),
        ("G×E", "Treatment response × Physiological stability"),
        ("I×L", "Risk pattern × Lifestyle tolerance"),
        ("I×E", "Risk pattern × Physiological stability"),
        ("L×E", "Lifestyle tolerance × Physiological stability"),
    ]
    for name, desc in interactions:
        st.markdown(f"- **{name}**: {desc}")
    st.markdown("Plus **GILE composite** and **Tralse risk indicator** engineered features.")


def render_patient_prediction():
    st.header("Patient Prediction")
    predictor = get_predictor()

    if not predictor.is_trained:
        st.warning("⚠️ Train the model first in the Model Training tab.")
        return

    with st.form("patient_pred_form", clear_on_submit=False):
        st.markdown("Enter UCI heart disease features:")
        c1, c2, c3 = st.columns(3)
        with c1:
            age = st.number_input("Age", 20, 90, 55, key="hp_age")
            sex = st.selectbox("Sex", [1, 0], format_func=lambda x: "Male" if x else "Female", key="hp_sex")
            cp = st.selectbox("Chest Pain Type", [0, 1, 2, 3],
                             format_func=lambda x: {0: "Typical Angina", 1: "Atypical", 2: "Non-anginal", 3: "Asymptomatic"}[x],
                             key="hp_cp")
            trestbps = st.number_input("Resting BP (mmHg)", 80, 220, 130, key="hp_bp")
            chol = st.number_input("Cholesterol (mg/dL)", 100, 600, 240, key="hp_chol")
        with c2:
            fbs = st.selectbox("Fasting Blood Sugar > 120", [0, 1],
                              format_func=lambda x: "Yes" if x else "No", key="hp_fbs")
            restecg = st.selectbox("Resting ECG", [0, 1, 2],
                                  format_func=lambda x: {0: "Normal", 1: "ST-T Abnormality", 2: "LV Hypertrophy"}[x],
                                  key="hp_ecg")
            thalach = st.number_input("Max Heart Rate", 60, 220, 150, key="hp_hr")
            exang = st.selectbox("Exercise Angina", [0, 1],
                                format_func=lambda x: "Yes" if x else "No", key="hp_exang")
        with c3:
            oldpeak = st.number_input("ST Depression", 0.0, 7.0, 1.0, 0.1, key="hp_oldpeak")
            slope = st.selectbox("ST Slope", [0, 1, 2],
                                format_func=lambda x: {0: "Upsloping", 1: "Flat", 2: "Downsloping"}[x],
                                key="hp_slope")
            ca = st.selectbox("Num Major Vessels (0-3)", [0, 1, 2, 3], key="hp_ca")
            thal = st.selectbox("Thalassemia", [1, 2, 3],
                               format_func=lambda x: {1: "Normal", 2: "Fixed Defect", 3: "Reversible Defect"}[x],
                               key="hp_thal")

        submitted = st.form_submit_button("Predict Heart Disease Risk", type="primary")

    if submitted:
        try:
            patient_df = pd.DataFrame([{
                'age': age, 'sex': sex, 'cp': cp, 'trestbps': trestbps,
                'chol': chol, 'fbs': fbs, 'restecg': restecg, 'thalach': thalach,
                'exang': exang, 'oldpeak': oldpeak, 'slope': slope, 'ca': ca,
                'thal': thal, 'target': 0,
            }])

            patient_enhanced = predictor.engineer_gile_features(patient_df)
            X = patient_enhanced[predictor.feature_columns].values
            X_scaled = predictor.scaler.transform(X)

            predictions = predictor.predict_with_tralse(X_scaled)
            pred = predictions[0]

            st.markdown("---")
            st.subheader("Prediction Result")

            p1, p2, p3 = st.columns(3)
            with p1:
                st.metric("Disease Probability", f"{pred['probability']:.1%}")
            with p2:
                st.metric("Prediction", "Positive ⚠️" if pred['prediction'] else "Negative ✅")
            with p3:
                zone = pred['tralse_zone']
                zone_icons = {'True': '✅', 'Tralse': '⚠️', 'False': '❌'}
                st.metric("Tralse Zone", f"{zone_icons.get(zone, '')} {zone}")

            if zone == 'True':
                st.error(f"**{pred['recommended_action']}**")
            elif zone == 'Tralse':
                st.warning(f"**{pred['recommended_action']}**")
            else:
                st.success(f"**{pred['recommended_action']}**")

            st.markdown("---")
            st.subheader("GILE Scores")
            gile_vals = {
                'G': float(patient_enhanced['G_score'].iloc[0]),
                'I': float(patient_enhanced['I_score'].iloc[0]),
                'L': float(patient_enhanced['L_score'].iloc[0]),
                'E': float(patient_enhanced['E_score'].iloc[0]),
            }
            display_gile_scores(gile_vals)
            st.metric("GILE Composite", f"{float(patient_enhanced['GILE_composite'].iloc[0]):.4f}")

            with st.expander("Uncertainty Decomposition"):
                unc = pred.get('uncertainty_decomposition', {})
                u1, u2, u3 = st.columns(3)
                with u1:
                    st.metric("Aleatoric", f"{unc.get('aleatoric', 0):.4f}")
                with u2:
                    st.metric("Epistemic", f"{unc.get('epistemic', 0):.4f}")
                with u3:
                    st.metric("Model Agreement", f"{unc.get('model_agreement', 0):.4f}")

                if 'individual_probs' in unc:
                    st.markdown("**Per-Model Probabilities:**")
                    for model_name, prob in unc['individual_probs'].items():
                        st.markdown(f"- {model_name.replace('_', ' ').title()}: {prob:.4f}")

        except Exception as e:
            st.error(f"Prediction error: {str(e)}")


def render_model_comparison():
    st.header("Model Comparison")
    predictor = get_predictor()

    if not predictor.is_trained:
        st.warning("⚠️ Train models first to see comparison.")
        return

    eval_results = st.session_state.get('heart_eval_results', {})
    if not eval_results:
        st.info("Run evaluation to see model comparison.")
        return

    try:
        rows = []
        for name in ['logistic_regression', 'random_forest', 'gradient_boosting', 'svm', 'ensemble']:
            m = eval_results.get(name, {})
            if 'accuracy' in m:
                rows.append({
                    'Model': name.replace('_', ' ').title(),
                    'Accuracy': m.get('accuracy', 0),
                    'Precision': m.get('precision', 0),
                    'Recall': m.get('recall', 0),
                    'F1 Score': m.get('f1', 0),
                    'AUC-ROC': m.get('auc_roc', 0),
                    'Sensitivity': m.get('sensitivity', 0),
                    'Specificity': m.get('specificity', 0),
                })

        if rows:
            df = pd.DataFrame(rows)
            st.dataframe(df, use_container_width=True, hide_index=True)

            st.subheader("AUC-ROC Comparison")
            chart_df = df[['Model', 'AUC-ROC']].set_index('Model')
            st.bar_chart(chart_df)

            st.subheader("F1 Score Comparison")
            chart_df2 = df[['Model', 'F1 Score']].set_index('Model')
            st.bar_chart(chart_df2)

        best = predictor.best_model_name
        if best:
            st.success(f"🏆 Best Model: **{best.replace('_', ' ').title()}**")

    except Exception as e:
        st.error(f"Comparison error: {str(e)}")


def render_cross_validation():
    st.header("Cross-Validation Results")
    predictor = get_predictor()

    if not predictor.is_trained:
        st.warning("⚠️ Train models first.")
        return

    if st.button("Run 5-Fold Cross-Validation", type="primary", key="btn_cv"):
        try:
            with st.spinner("Running cross-validation..."):
                df = predictor.generate_sample_data()
                df_enhanced = predictor.engineer_gile_features(df)
                X = df_enhanced[predictor.feature_columns].values
                y = df_enhanced['target'].values
                X_scaled = predictor.scaler.transform(X)

                cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

                cv_results = {}
                for name, model in predictor.models.items():
                    if name == 'ensemble':
                        continue
                    try:
                        scores = cross_val_score(model, X_scaled, y, cv=cv, scoring='roc_auc')
                        cv_results[name] = {
                            'mean_auc': round(float(np.mean(scores)), 4),
                            'std_auc': round(float(np.std(scores)), 4),
                            'fold_scores': [round(float(s), 4) for s in scores],
                        }
                    except Exception as e:
                        cv_results[name] = {'error': str(e)}

                st.session_state['heart_cv_results'] = cv_results

        except Exception as e:
            st.error(f"Cross-validation error: {str(e)}")

    cv_results = st.session_state.get('heart_cv_results')
    if cv_results:
        rows = []
        for name, res in cv_results.items():
            if 'mean_auc' in res:
                rows.append({
                    'Model': name.replace('_', ' ').title(),
                    'Mean AUC': res['mean_auc'],
                    'Std AUC': res['std_auc'],
                    'Fold 1': res['fold_scores'][0],
                    'Fold 2': res['fold_scores'][1],
                    'Fold 3': res['fold_scores'][2],
                    'Fold 4': res['fold_scores'][3],
                    'Fold 5': res['fold_scores'][4],
                })

        if rows:
            st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

            chart_df = pd.DataFrame({
                r['Model']: [r['Mean AUC']] for r in rows
            }, index=['Mean AUC']).T
            st.bar_chart(chart_df)


def render_competition_info():
    st.header("Kaggle Heart Disease Competition")

    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Dataset", "UCI Cleveland")
    with c2:
        st.metric("Features", "14 + GILE")
    with c3:
        st.metric("Models", "4 + Ensemble")

    st.markdown("---")
    st.subheader("Approach: GILE-Enhanced Classification")
    st.markdown("""
    **Standard 14 UCI features** enhanced with TI Framework feature engineering:

    1. **GILE Dimension Scores** — Map clinical features to G/I/L/E dimensions
    2. **Interaction Features** — 6 pairwise GILE interactions (G×I, G×L, etc.)
    3. **Composite Score** — Weighted GILE aggregate
    4. **Tralse Risk Indicator** — Inverse of composite for risk quantification

    Total engineered features: 14 original + 12 GILE = **26 features**
    """)

    st.subheader("Submission Strategy")
    with st.expander("Kaggle Notebook Structure"):
        st.markdown("""
        1. Load UCI heart disease data
        2. Apply GILE feature engineering
        3. Train ensemble (LR + RF + GB + SVM)
        4. Evaluate with Tralse confidence zones
        5. Generate submission CSV with probability + Tralse zone
        6. Include GILE analysis visualizations
        """)

    with st.expander("Key Differentiators"):
        st.markdown("""
        - **Tralse Confidence Scoring**: Three-zone classification instead of binary
        - **GILE Feature Engineering**: Clinically-meaningful dimension mapping
        - **Uncertainty Decomposition**: Aleatoric vs epistemic uncertainty per patient
        - **Specialist Review Flag**: Automatic flagging of uncertain predictions
        """)

    st.markdown("---")
    st.markdown("🔗 [UCI Heart Disease Dataset](https://archive.ics.uci.edu/dataset/45/heart+disease)")


from sklearn.model_selection import StratifiedKFold, cross_val_score
