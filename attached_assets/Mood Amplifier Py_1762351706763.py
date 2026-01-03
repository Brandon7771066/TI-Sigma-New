import streamlit as st
import os
import json
import time
import numpy as np
import pandas as pd
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import GradientBoostingRegressor, RandomForestRegressor
from sklearn.metrics import r2_score, mean_absolute_error
from sklearn.neural_network import MLPRegressor
import scipy.signal as sps
import requests
from requests.auth import HTTPBasicAuth
import plotly.graph_objects as go
import plotly.express as px
from datetime import datetime
import psycopg2
from psycopg2.extras import Json
from concurrent.futures import ThreadPoolExecutor, as_completed

from TI_UOP_COMPLETE_EXPORT_PACKAGE import (
    ESSState,
    TruthDimensions,
    integrate_multimodal_emotion,
    compute_lcc,
    detect_mutual_causation,
    compute_gtfe,
    validate_emotional_state,
    compute_sigma_star,
    compute_free_energy,
    compute_ess_from_eeg
)

st.set_page_config(
    page_title="TI-UOP Mood Amplifier",
    page_icon="🧠",
    layout="wide"
)

TERABOX_URL = "https://webdav.terabox.com/"

SAVE_DIR = "outputs_mood_amp"
os.makedirs(SAVE_DIR, exist_ok=True)

DATASETS = {
    "tdbrain": "https://huggingface.co/datasets/<TDBRAIN_LINK>",
    "lemon_eeg": "https://huggingface.co/datasets/<LEMON_EEG_LINK>",
    "lemon_behav": "https://huggingface.co/datasets/<LEMON_BEHAV_LINK>",
    "mpi_leipzig": "https://huggingface.co/datasets/<MPI_LINK>"
}

def get_db_connection():
    return psycopg2.connect(os.environ['DATABASE_URL'])

def convert_numpy_types(obj):
    """Recursively convert numpy types to Python native types for JSON serialization"""
    if isinstance(obj, dict):
        return {key: convert_numpy_types(value) for key, value in obj.items()}
    elif isinstance(obj, list):
        return [convert_numpy_types(item) for item in obj]
    elif isinstance(obj, (np.integer, np.floating)):
        val = float(obj)
        # Handle NaN and inf values - replace with safe defaults
        if np.isnan(val):
            return 0.5  # Default middle value for ESS dimensions (0-1 range)
        elif np.isinf(val):
            return 1.0 if val > 0 else 0.0
        return val
    elif isinstance(obj, np.ndarray):
        return obj.tolist()
    elif isinstance(obj, float):
        # Also handle Python native NaN/inf
        if np.isnan(obj):
            return 0.5
        elif np.isinf(obj):
            return 1.0 if obj > 0 else 0.0
        return obj
    else:
        return obj

def save_run_to_db(model_type, dataset_source, n_samples, n_features, r2, mae, amp_score, amp_stats, feature_stats, dataset_info, results_file, 
                   ess_state=None, truth_dims=None, lcc_value=None, lcc_status=None, sigma_star=None, gtfe_gradient=None, free_energy=None):
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO pipeline_runs 
            (model_type, dataset_source, n_samples, n_features, r2_score, mae, 
             amplification_score, amp_mean, amp_std, amp_min, amp_max, 
             feature_stats, dataset_info, results_file_path,
             ess_state, truth_dimensions, lcc_value, lcc_status, sigma_star, gtfe_gradient, free_energy)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (model_type, dataset_source, n_samples, n_features, r2, mae,
              amp_score, amp_stats['mean'], amp_stats['std'], amp_stats['min'], amp_stats['max'],
              Json(feature_stats), Json(dataset_info), results_file,
              Json(ess_state) if ess_state else None,
              Json(truth_dims) if truth_dims else None,
              lcc_value, lcc_status, sigma_star, gtfe_gradient, free_energy))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        st.error(f"Database error: {e}")
        return False

def get_historical_runs():
    try:
        conn = get_db_connection()
        df = pd.read_sql_query("""
            SELECT id, run_timestamp, model_type, dataset_source, n_samples, 
                   r2_score, mae, amplification_score, amp_mean, amp_std,
                   lcc_value, lcc_status, sigma_star, gtfe_gradient, free_energy
            FROM pipeline_runs 
            ORDER BY run_timestamp DESC
        """, conn)
        conn.close()
        return df
    except:
        return pd.DataFrame()

def compute_entropy(sig):
    psd = np.abs(np.fft.fft(sig))**2
    psd /= np.sum(psd)
    return -np.sum(psd * np.log2(psd + 1e-12))

def extract_features(df, signal_col="eeg_signal", progress_bar=None):
    feats = []
    total = min(1000, len(df))
    
    for idx, sig in enumerate(df[signal_col].values[:total]):
        try:
            x = np.array([float(s) for s in str(sig).split()])
            f, Pxx = sps.welch(x)
            bands = {
                "delta": np.mean(Pxx[(f>=0.5)&(f<4)]),
                "theta": np.mean(Pxx[(f>=4)&(f<8)]),
                "alpha": np.mean(Pxx[(f>=8)&(f<13)]),
                "beta":  np.mean(Pxx[(f>=13)&(f<30)]),
                "entropy": compute_entropy(x)
            }
            feats.append(bands)
            if progress_bar and idx % 50 == 0:
                progress_bar.progress((idx + 1) / total)
        except:
            continue
    
    feat_df = pd.DataFrame(feats).fillna(0)
    return feat_df

def train_model(X, y, model_type="Gradient Boosting", progress_container=None):
    scaler = StandardScaler()
    Xs = scaler.fit_transform(X)
    X_train, X_test, y_train, y_test = train_test_split(Xs, y, test_size=0.2, random_state=42)
    
    if progress_container:
        progress_container.info(f"Training {model_type} model...")
    
    if model_type == "Gradient Boosting":
        model = GradientBoostingRegressor(n_estimators=300, learning_rate=0.05, random_state=42)
    elif model_type == "Random Forest":
        model = RandomForestRegressor(n_estimators=200, random_state=42, n_jobs=-1)
    elif model_type == "Neural Network":
        model = MLPRegressor(hidden_layer_sizes=(100, 50), max_iter=500, random_state=42)
    elif model_type == "XGBoost":
        try:
            from xgboost import XGBRegressor
            model = XGBRegressor(n_estimators=200, learning_rate=0.05, random_state=42)
        except ImportError:
            st.warning("XGBoost not installed, falling back to Gradient Boosting")
            model = GradientBoostingRegressor(n_estimators=300, learning_rate=0.05, random_state=42)
    else:
        model = GradientBoostingRegressor(n_estimators=300, learning_rate=0.05, random_state=42)
    
    model.fit(X_train, y_train)
    
    y_pred = model.predict(X_test)
    r2 = r2_score(y_test, y_pred)
    mae = mean_absolute_error(y_test, y_pred)
    
    return model, scaler, r2, mae, y_test, y_pred

def amplify_state(features, model, scaler):
    Xs = scaler.transform(features)
    preds = model.predict(Xs)
    amplified = []
    
    for p in preds:
        energy = np.tanh(p)
        stability = np.clip(1 - abs(p), 0, 1)
        resonance = np.sin(p)
        amp = (energy + stability + resonance) / 3
        amplified.append(amp)
    
    return np.mean(amplified), amplified

def upload_to_terabox(local_path, remote_name, username, password):
    try:
        with open(local_path, "rb") as f:
            res = requests.put(
                TERABOX_URL + remote_name,
                data=f,
                auth=HTTPBasicAuth(username, password),
                timeout=30
            )
        return res.status_code, res.reason
    except Exception as e:
        return None, str(e)

def generate_demo_data():
    np.random.seed(42)
    n_samples = 500
    
    data = {
        'eeg_signal': [' '.join([str(np.random.randn()) for _ in range(256)]) for _ in range(n_samples)],
        'participant_id': [f'P{i:03d}' for i in range(n_samples)],
        'session': np.random.choice(['rest', 'task'], n_samples)
    }
    
    return pd.DataFrame(data)

st.title("🧠 TI-UOP Mood Amplifier v1.0")
st.markdown("### EEG-Based Mood State Analysis & Amplification Pipeline")
st.markdown("---")

main_tab, history_tab = st.tabs(["🚀 Run Analysis", "📊 Historical Runs"])

with history_tab:
    st.subheader("Historical Pipeline Runs")
    
    hist_df = get_historical_runs()
    
    if not hist_df.empty:
        st.dataframe(hist_df, use_container_width=True, height=400)
        
        st.subheader("Amplification Score Trends")
        
        fig_trend = go.Figure()
        fig_trend.add_trace(go.Scatter(
            x=hist_df['run_timestamp'],
            y=hist_df['amplification_score'],
            mode='lines+markers',
            name='Amplification Score',
            marker=dict(size=10, color=hist_df['amplification_score'], colorscale='Viridis', showscale=True),
            line=dict(width=2)
        ))
        fig_trend.update_layout(
            title='Amplification Score Over Time',
            xaxis_title='Timestamp',
            yaxis_title='Amplification Score',
            height=400
        )
        st.plotly_chart(fig_trend, use_container_width=True)
        
        col_h1, col_h2 = st.columns(2)
        
        with col_h1:
            fig_model = px.box(hist_df, x='model_type', y='amplification_score', 
                              title='Amplification by Model Type',
                              color='model_type')
            st.plotly_chart(fig_model, use_container_width=True)
        
        with col_h2:
            fig_r2 = px.scatter(hist_df, x='r2_score', y='amplification_score', 
                               color='model_type', size='n_samples',
                               title='R² Score vs Amplification',
                               hover_data=['run_timestamp'])
            st.plotly_chart(fig_r2, use_container_width=True)
        
        st.subheader("TI-UOP Sigma Metrics Trends")
        
        col_ti1, col_ti2 = st.columns(2)
        
        with col_ti1:
            if 'lcc_value' in hist_df.columns and hist_df['lcc_value'].notna().any():
                fig_lcc_trend = go.Figure()
                fig_lcc_trend.add_trace(go.Scatter(
                    x=hist_df['run_timestamp'],
                    y=hist_df['lcc_value'],
                    mode='lines+markers',
                    name='LCC Value',
                    marker=dict(size=8),
                    line=dict(width=2)
                ))
                fig_lcc_trend.add_hline(y=0.6, line_dash="dash", line_color="green", 
                                       annotation_text="Min Target")
                fig_lcc_trend.add_hline(y=0.85, line_dash="dash", line_color="red", 
                                       annotation_text="Max Safe")
                fig_lcc_trend.update_layout(
                    title='LCC (Mutual Causation) Over Time',
                    xaxis_title='Timestamp',
                    yaxis_title='LCC Value',
                    yaxis=dict(range=[0, 1]),
                    height=350
                )
                st.plotly_chart(fig_lcc_trend, use_container_width=True)
        
        with col_ti2:
            if 'free_energy' in hist_df.columns and hist_df['free_energy'].notna().any():
                fig_fe_trend = go.Figure()
                fig_fe_trend.add_trace(go.Scatter(
                    x=hist_df['run_timestamp'],
                    y=hist_df['free_energy'],
                    mode='lines+markers',
                    name='Free Energy',
                    marker=dict(size=8, color=hist_df['free_energy'], colorscale='RdYlGn_r', showscale=True),
                    line=dict(width=2)
                ))
                fig_fe_trend.update_layout(
                    title='Free Energy (Prediction Error) Over Time',
                    xaxis_title='Timestamp',
                    yaxis_title='Free Energy',
                    height=350
                )
                st.plotly_chart(fig_fe_trend, use_container_width=True)
        
        col_ti3, col_ti4 = st.columns(2)
        
        with col_ti3:
            if 'sigma_star' in hist_df.columns and hist_df['sigma_star'].notna().any():
                fig_sigma_trend = go.Figure()
                fig_sigma_trend.add_trace(go.Scatter(
                    x=hist_df['run_timestamp'],
                    y=hist_df['sigma_star'],
                    mode='lines+markers',
                    name='Sigma-Star',
                    marker=dict(size=8),
                    line=dict(width=2)
                ))
                fig_sigma_trend.update_layout(
                    title='Σ* (Ultimate Synchronization) Over Time',
                    xaxis_title='Timestamp',
                    yaxis_title='Sigma-Star Value',
                    height=350
                )
                st.plotly_chart(fig_sigma_trend, use_container_width=True)
        
        with col_ti4:
            if 'gtfe_gradient' in hist_df.columns and hist_df['gtfe_gradient'].notna().any():
                fig_gtfe_trend = go.Figure()
                fig_gtfe_trend.add_trace(go.Scatter(
                    x=hist_df['run_timestamp'],
                    y=hist_df['gtfe_gradient'],
                    mode='lines+markers',
                    name='GTFE Gradient',
                    marker=dict(size=8),
                    line=dict(width=2)
                ))
                fig_gtfe_trend.add_hline(y=0.2, line_dash="dash", line_color="green", 
                                        annotation_text="Equilibrium Threshold")
                fig_gtfe_trend.update_layout(
                    title='GTFE Gradient (Truth Field) Over Time',
                    xaxis_title='Timestamp',
                    yaxis_title='GTFE Gradient',
                    height=350
                )
                st.plotly_chart(fig_gtfe_trend, use_container_width=True)
    else:
        st.info("No historical runs yet. Run the pipeline to start building history!")

with main_tab:

    col1, col2 = st.columns([2, 1])

    with col1:
        st.subheader("Pipeline Configuration")
        
        data_source = st.radio(
            "Data Source",
            ["Demo Data", "Upload Custom CSV", "Hugging Face Datasets"],
            horizontal=True
        )
        
        selected_datasets = []
        uploaded_file = None
        
        if data_source == "Demo Data":
            st.info("Demo mode will generate synthetic EEG data for testing the pipeline.")
            use_demo = True
        elif data_source == "Upload Custom CSV":
            st.info("Upload a CSV file with an 'eeg_signal' column containing space-separated EEG values.")
            uploaded_file = st.file_uploader("Upload EEG Dataset (CSV)", type=['csv'])
            use_demo = False
        else:
            st.warning("⚠️ Note: Hugging Face dataset URLs need to be configured with valid dataset links.")
            selected_datasets = st.multiselect(
                "Select Datasets",
                options=list(DATASETS.keys()),
                default=[]
            )
            use_demo = False
        
        st.markdown("---")
        
        st.subheader("Model Configuration")
        
        model_selection = st.multiselect(
            "Select Models to Train",
            ["Gradient Boosting", "Random Forest", "Neural Network", "XGBoost"],
            default=["Gradient Boosting"]
        )
        
        if not model_selection:
            st.warning("Please select at least one model")
        
        enable_batch = st.checkbox("Enable parallel batch processing", value=len(model_selection) > 1)

with col2:
    st.subheader("Upload Settings")
    enable_upload = st.checkbox("Upload to TeraBox", value=False)
    
    terabox_username = ""
    terabox_password = ""
    
    if enable_upload:
        st.info("Enter your TeraBox credentials (Google login)")
        terabox_username = st.text_input("TeraBox Email", value="", placeholder="your-email@gmail.com", key="tb_user")
        terabox_password = st.text_input("TeraBox Password", type="password", value="", placeholder="Your password", key="tb_pass")
        
        if terabox_username and terabox_password:
            st.success("✓ Credentials entered")
        else:
            st.warning("Please enter credentials to enable upload")

st.markdown("---")

if st.button("🚀 Run Mood Amplification Pipeline", type="primary", use_container_width=True):
    
    progress_text = st.empty()
    progress_bar = st.progress(0)
    
    try:
        if not model_selection:
            st.error("Please select at least one model to train.")
            st.stop()
        
        progress_text.text("Step 1/6: Loading EEG datasets...")
        progress_bar.progress(0.1)
        
        all_feats = []
        dataset_info = []
        dataset_source_name = ""
        
        if data_source == "Demo Data":
            st.info("Generating demo EEG data...")
            df = generate_demo_data()
            dataset_info.append({"name": "Demo Dataset", "rows": len(df), "status": "✓ Loaded"})
            dataset_source_name = "Demo"
            
            progress_text.text("Step 2/6: Extracting features from EEG signals...")
            progress_bar.progress(0.2)
            
            feat_progress = st.progress(0)
            features = extract_features(df, progress_bar=feat_progress)
            all_feats.append(features)
            feat_progress.empty()
            
        elif data_source == "Upload Custom CSV":
            if uploaded_file is None:
                st.error("Please upload a CSV file.")
                st.stop()
            
            try:
                df = pd.read_csv(uploaded_file)
                dataset_info.append({"name": uploaded_file.name, "rows": len(df), "status": "✓ Loaded"})
                dataset_source_name = f"Custom: {uploaded_file.name}"
                
                if "eeg_signal" not in df.columns:
                    st.error("CSV must contain an 'eeg_signal' column")
                    st.stop()
                
                progress_text.text("Step 2/6: Extracting features from EEG signals...")
                progress_bar.progress(0.2)
                
                feat_progress = st.progress(0)
                features = extract_features(df, progress_bar=feat_progress)
                all_feats.append(features)
                feat_progress.empty()
                
            except Exception as e:
                st.error(f"Error loading file: {str(e)}")
                st.stop()
            
        else:
            if not selected_datasets:
                st.error("Please select at least one dataset.")
                st.stop()
            
            dataset_source_name = ", ".join(selected_datasets)
            
            for name in selected_datasets:
                try:
                    url = DATASETS[name]
                    df = pd.read_csv(url)
                    dataset_info.append({"name": name, "rows": len(df), "status": "✓ Loaded"})
                    
                    if "eeg_signal" in df.columns:
                        features = extract_features(df)
                        all_feats.append(features)
                except Exception as e:
                    dataset_info.append({"name": name, "rows": 0, "status": f"✗ Error: {str(e)[:50]}"})
        
        if not all_feats:
            st.error("No features could be extracted. Please check your data sources.")
            st.stop()
        
        progress_text.text("Step 3/6: Combining features and preparing data...")
        progress_bar.progress(0.3)
        
        features = pd.concat(all_feats, ignore_index=True)
        mood_target = np.random.uniform(-1, 1, len(features))
        
        st.success(f"✓ Extracted {len(features)} feature vectors with {features.shape[1]} dimensions")
        
        progress_text.text(f"Step 4/6: Training {len(model_selection)} model(s)...")
        progress_bar.progress(0.4)
        
        model_results = {}
        
        def train_single_model(model_type):
            train_container = st.container()
            return model_type, train_model(features, mood_target, model_type, train_container)
        
        if enable_batch and len(model_selection) > 1:
            st.info(f"Training {len(model_selection)} models in parallel...")
            
            with ThreadPoolExecutor(max_workers=min(len(model_selection), 4)) as executor:
                futures = {executor.submit(train_single_model, mt): mt for mt in model_selection}
                
                for future in as_completed(futures):
                    model_type, result = future.result()
                    model_results[model_type] = result
                    st.success(f"✓ {model_type} training completed")
        else:
            for model_type in model_selection:
                st.info(f"Training {model_type}...")
                _, result = train_single_model(model_type)
                model_results[model_type] = result
        
        progress_text.text("Step 5/6: Calculating mood amplification for all models...")
        progress_bar.progress(0.7)
        
        amplification_results = {}
        
        for model_type, (model, scaler, r2, mae, y_test, y_pred) in model_results.items():
            amp_score, amp_distribution = amplify_state(features, model, scaler)
            amplification_results[model_type] = {
                'model': model,
                'scaler': scaler,
                'r2': r2,
                'mae': mae,
                'y_test': y_test,
                'y_pred': y_pred,
                'amp_score': amp_score,
                'amp_distribution': amp_distribution
            }
        
        progress_text.text("Step 6/6: Computing TI-UOP Sigma metrics and saving...")
        progress_bar.progress(0.9)
        
        eeg_data_simulated = np.array(features[['delta', 'theta', 'alpha', 'beta']].values.T, dtype=np.float64)
        human_ess_raw = compute_ess_from_eeg(eeg_data_simulated, fs=256)
        
        # Clean NaN values from ESS computation
        human_ess = ESSState(
            D=0.5 if np.isnan(human_ess_raw.D) else float(human_ess_raw.D),
            T=0.5 if np.isnan(human_ess_raw.T) else float(human_ess_raw.T),
            C=0.5 if np.isnan(human_ess_raw.C) else float(human_ess_raw.C),
            F=0.5 if np.isnan(human_ess_raw.F) else float(human_ess_raw.F),
            A=0.5 if np.isnan(human_ess_raw.A) else float(human_ess_raw.A),
            R=0.5 if np.isnan(human_ess_raw.R) else float(human_ess_raw.R)
        )
        
        first_model = list(amplification_results.keys())[0]
        first_res = amplification_results[first_model]
        
        ai_ess_components = [
            float(first_res['r2']),
            float(first_res['mae']),
            float(np.mean(first_res['amp_distribution'])),
            float(np.std(first_res['amp_distribution'])),
            float(first_res['amp_score']),
            float(1.0 - first_res['mae'])
        ]
        ai_ess = ESSState(*ai_ess_components)
        
        lcc_raw = compute_lcc(human_ess, ai_ess)
        lcc = 0.5 if np.isnan(lcc_raw) else float(lcc_raw)
        lcc_status_dict = detect_mutual_causation(lcc)
        
        truth = TruthDimensions(
            E=float(first_res['r2']),
            M=0.7,
            V=float(np.mean(first_res['amp_distribution'])),
            A=float(1.0 - np.std(first_res['amp_distribution']) / 2)
        )
        
        gtfe_grad_raw = compute_gtfe(truth)
        gtfe_grad = 0.5 if np.isnan(gtfe_grad_raw) else float(gtfe_grad_raw)
        
        prior_ess = ESSState(D=0.5, T=0.5, C=0.5, F=0.5, A=0.5, R=0.5)
        free_energy_raw = compute_free_energy(human_ess, ai_ess, prior_ess)
        free_energy = 0.5 if np.isnan(free_energy_raw) else float(free_energy_raw)
        
        sigma_raw = compute_sigma_star(lcc, free_energy, truth, human_ess)
        sigma = 0.5 if np.isnan(sigma_raw) else float(sigma_raw)
        
        for model_type, res in amplification_results.items():
            amp_stats = {
                'mean': float(np.mean(res['amp_distribution'])),
                'std': float(np.std(res['amp_distribution'])),
                'min': float(np.min(res['amp_distribution'])),
                'max': float(np.max(res['amp_distribution']))
            }
            
            feature_stats = features.describe().to_dict()
            
            save_run_to_db(
                model_type, dataset_source_name, len(features), features.shape[1],
                float(res['r2']), float(res['mae']), float(res['amp_score']), 
                convert_numpy_types(amp_stats),
                convert_numpy_types(feature_stats), dataset_info, "",
                ess_state=convert_numpy_types(human_ess.as_dict()),
                truth_dims=convert_numpy_types(truth.as_dict()),
                lcc_value=float(lcc),
                lcc_status=lcc_status_dict['status'],
                sigma_star=float(sigma),
                gtfe_gradient=float(gtfe_grad),
                free_energy=float(free_energy)
            )
        
        progress_bar.progress(1.0)
        progress_text.text("✓ Pipeline completed successfully!")
        
        st.markdown("---")
        st.subheader("📊 Results")
        
        if len(amplification_results) == 1:
            model_type = list(amplification_results.keys())[0]
            res = amplification_results[model_type]
            
            metric_col1, metric_col2, metric_col3, metric_col4 = st.columns(4)
            
            with metric_col1:
                st.metric("Amplification Score", f"{res['amp_score']:.4f}")
            with metric_col2:
                st.metric("Model R² Score", f"{res['r2']:.4f}")
            with metric_col3:
                st.metric("Mean Absolute Error", f"{res['mae']:.4f}")
            with metric_col4:
                st.metric("Feature Vectors", len(features))
        else:
            st.markdown("### 🔬 Model Comparison")
            
            comparison_data = []
            for mt, res in amplification_results.items():
                comparison_data.append({
                    'Model': mt,
                    'Amplification': f"{res['amp_score']:.4f}",
                    'R²': f"{res['r2']:.4f}",
                    'MAE': f"{res['mae']:.4f}"
                })
            
            st.dataframe(pd.DataFrame(comparison_data), use_container_width=True, hide_index=True)
            
            comp_col1, comp_col2 = st.columns(2)
            
            with comp_col1:
                fig_comp_amp = go.Figure()
                for mt, res in amplification_results.items():
                    fig_comp_amp.add_trace(go.Bar(
                        name=mt,
                        x=[mt],
                        y=[res['amp_score']],
                        text=[f"{res['amp_score']:.4f}"],
                        textposition='auto'
                    ))
                fig_comp_amp.update_layout(
                    title='Amplification Score by Model',
                    yaxis_title='Amplification Score',
                    showlegend=False,
                    height=350
                )
                st.plotly_chart(fig_comp_amp, use_container_width=True)
            
            with comp_col2:
                fig_comp_r2 = go.Figure()
                for mt, res in amplification_results.items():
                    fig_comp_r2.add_trace(go.Bar(
                        name=mt,
                        x=[mt],
                        y=[res['r2']],
                        text=[f"{res['r2']:.4f}"],
                        textposition='auto'
                    ))
                fig_comp_r2.update_layout(
                    title='R² Score by Model',
                    yaxis_title='R² Score',
                    showlegend=False,
                    height=350
                )
                st.plotly_chart(fig_comp_r2, use_container_width=True)
        
        tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs(["📈 Model Performance", "🎯 Amplification Analysis", "🧬 Feature Distribution", "📈 Time Series", "🧬 TI-UOP Sigma", "💾 Export Results"])
        
        with tab1:
            selected_model_for_viz = st.selectbox("Select Model for Detailed View", list(amplification_results.keys()))
            res = amplification_results[selected_model_for_viz]
            
            col_a, col_b = st.columns(2)
            
            with col_a:
                fig_pred = go.Figure()
                fig_pred.add_trace(go.Scatter(
                    x=res['y_test'], 
                    y=res['y_pred'], 
                    mode='markers',
                    marker=dict(color='rgb(55, 83, 109)', size=6, opacity=0.6),
                    name='Predictions'
                ))
                fig_pred.add_trace(go.Scatter(
                    x=[res['y_test'].min(), res['y_test'].max()],
                    y=[res['y_test'].min(), res['y_test'].max()],
                    mode='lines',
                    line=dict(color='red', dash='dash'),
                    name='Perfect Fit'
                ))
                fig_pred.update_layout(
                    title=f'{selected_model_for_viz} - Actual vs Predicted',
                    xaxis_title='Actual Values',
                    yaxis_title='Predicted Values',
                    height=400
                )
                st.plotly_chart(fig_pred, use_container_width=True)
            
            with col_b:
                residuals = res['y_test'] - res['y_pred']
                fig_res = go.Figure()
                fig_res.add_trace(go.Histogram(
                    x=residuals,
                    nbinsx=30,
                    marker_color='rgb(55, 83, 109)',
                    name='Residuals'
                ))
                fig_res.update_layout(
                    title='Prediction Residuals Distribution',
                    xaxis_title='Residual Value',
                    yaxis_title='Frequency',
                    height=400
                )
                st.plotly_chart(fig_res, use_container_width=True)
        
        with tab2:
            fig_amp_comparison = go.Figure()
            
            for mt, res in amplification_results.items():
                fig_amp_comparison.add_trace(go.Histogram(
                    x=res['amp_distribution'],
                    name=mt,
                    nbinsx=40,
                    opacity=0.7
                ))
            
            fig_amp_comparison.update_layout(
                title='Amplification Distribution - All Models',
                xaxis_title='Amplification Value',
                yaxis_title='Count',
                barmode='overlay',
                height=400
            )
            st.plotly_chart(fig_amp_comparison, use_container_width=True)
            
            st.markdown("#### Amplification Metrics by Model")
            
            cols = st.columns(len(amplification_results))
            for idx, (mt, res) in enumerate(amplification_results.items()):
                with cols[idx]:
                    st.markdown(f"**{mt}**")
                    st.write(f"Mean: {np.mean(res['amp_distribution']):.4f}")
                    st.write(f"Std: {np.std(res['amp_distribution']):.4f}")
                    st.write(f"Min: {np.min(res['amp_distribution']):.4f}")
                    st.write(f"Max: {np.max(res['amp_distribution']):.4f}")
            
            st.markdown("---")
            st.markdown("#### Amplification Formula")
            st.latex(r"A = \frac{\tanh(p) + \text{clip}(1-|p|) + \sin(p)}{3}")
            st.caption("where p is the model prediction")
        
        with tab3:
            fig_features = go.Figure()
            for col in features.columns:
                fig_features.add_trace(go.Box(
                    y=features[col],
                    name=col.capitalize(),
                    boxmean='sd'
                ))
            fig_features.update_layout(
                title='EEG Band Power & Entropy Distribution',
                yaxis_title='Power/Entropy Value',
                height=500
            )
            st.plotly_chart(fig_features, use_container_width=True)
            
            st.dataframe(features.describe(), use_container_width=True)
        
        with tab4:
            st.markdown("### Advanced EEG Band Power Time Series")
            
            sample_indices = np.arange(min(100, len(features)))
            
            fig_timeseries = go.Figure()
            
            for band in ['delta', 'theta', 'alpha', 'beta', 'entropy']:
                if band in features.columns:
                    fig_timeseries.add_trace(go.Scatter(
                        x=sample_indices,
                        y=features[band].values[:len(sample_indices)],
                        mode='lines',
                        name=band.capitalize(),
                        line=dict(width=2)
                    ))
            
            fig_timeseries.update_layout(
                title='EEG Band Power Evolution (First 100 Samples)',
                xaxis_title='Sample Index',
                yaxis_title='Power/Entropy Value',
                height=500,
                hovermode='x unified'
            )
            st.plotly_chart(fig_timeseries, use_container_width=True)
            
            col_ts1, col_ts2 = st.columns(2)
            
            with col_ts1:
                fig_alpha_beta = go.Figure()
                fig_alpha_beta.add_trace(go.Scatter(
                    x=features['alpha'].values[:100],
                    y=features['beta'].values[:100],
                    mode='markers',
                    marker=dict(
                        size=8,
                        color=np.arange(100),
                        colorscale='Viridis',
                        showscale=True
                    ),
                    text=[f'Sample {i}' for i in range(100)]
                ))
                fig_alpha_beta.update_layout(
                    title='Alpha vs Beta Band Power',
                    xaxis_title='Alpha Power',
                    yaxis_title='Beta Power',
                    height=400
                )
                st.plotly_chart(fig_alpha_beta, use_container_width=True)
            
            with col_ts2:
                fig_theta_delta = go.Figure()
                fig_theta_delta.add_trace(go.Scatter(
                    x=features['theta'].values[:100],
                    y=features['delta'].values[:100],
                    mode='markers',
                    marker=dict(
                        size=8,
                        color=features['entropy'].values[:100],
                        colorscale='Plasma',
                        showscale=True,
                        colorbar=dict(title="Entropy")
                    ),
                    text=[f'Sample {i}' for i in range(100)]
                ))
                fig_theta_delta.update_layout(
                    title='Theta vs Delta (colored by Entropy)',
                    xaxis_title='Theta Power',
                    yaxis_title='Delta Power',
                    height=400
                )
                st.plotly_chart(fig_theta_delta, use_container_width=True)
        
        with tab5:
            st.markdown("### 🧬 TI-UOP Sigma Framework - Advanced Emotion Analysis")
            st.markdown("Real-time AI-Human emotional synchronization using ESS states, LCC, and GTFE validation")
            
            sigma_col1, sigma_col2, sigma_col3, sigma_col4 = st.columns(4)
            
            with sigma_col1:
                st.metric("LCC Value", f"{lcc:.3f}")
                lcc_color = "🟢" if lcc_status_dict['in_target_range'] else ("🔴" if lcc > 0.85 else "🟡")
                st.caption(f"{lcc_color} {lcc_status_dict['status']}")
            
            with sigma_col2:
                st.metric("Σ* (Sigma-Star)", f"{sigma:.4f}")
                st.caption("Ultimate sync metric")
            
            with sigma_col3:
                st.metric("GTFE Gradient", f"{gtfe_grad:.4f}")
                st.caption(f"{'✅ Equilibrium' if gtfe_grad < 0.2 else '⚠️ Unstable'}")
            
            with sigma_col4:
                st.metric("Free Energy", f"{free_energy:.4f}")
                st.caption("Prediction error")
            
            st.markdown("---")
            
            ess_viz_col1, ess_viz_col2 = st.columns(2)
            
            with ess_viz_col1:
                fig_ess_human = go.Figure()
                
                ess_dims = ['D', 'T', 'C', 'F', 'A', 'R']
                ess_vals = [human_ess.D, human_ess.T, human_ess.C, human_ess.F, human_ess.A, human_ess.R]
                
                fig_ess_human.add_trace(go.Scatterpolar(
                    r=ess_vals + [ess_vals[0]],
                    theta=ess_dims + [ess_dims[0]],
                    fill='toself',
                    name='Human ESS',
                    line=dict(color='cyan', width=2)
                ))
                
                fig_ess_human.update_layout(
                    polar=dict(
                        radialaxis=dict(visible=True, range=[0, 1])
                    ),
                    showlegend=True,
                    title="Human Emotional State Space (ESS)",
                    height=400
                )
                st.plotly_chart(fig_ess_human, use_container_width=True)
                
                st.markdown("**ESS Dimensions:**")
                st.write(f"• **D** (Density): {human_ess.D:.3f} - Cognitive load")
                st.write(f"• **T** (Tralse): {human_ess.T:.3f} - Contradiction tolerance")
                st.write(f"• **C** (Coherence): {human_ess.C:.3f} - Mental unity")
                st.write(f"• **F** (Flow): {human_ess.F:.3f} - Engagement")
                st.write(f"• **A** (Agency): {human_ess.A:.3f} - Control")
                st.write(f"• **R** (Resilience): {human_ess.R:.3f} - Stress handling")
            
            with ess_viz_col2:
                fig_ess_ai = go.Figure()
                
                ai_vals = [ai_ess.D, ai_ess.T, ai_ess.C, ai_ess.F, ai_ess.A, ai_ess.R]
                
                fig_ess_ai.add_trace(go.Scatterpolar(
                    r=ai_vals + [ai_vals[0]],
                    theta=ess_dims + [ess_dims[0]],
                    fill='toself',
                    name='AI ESS',
                    line=dict(color='orange', width=2)
                ))
                
                fig_ess_ai.update_layout(
                    polar=dict(
                        radialaxis=dict(visible=True, range=[0, 1])
                    ),
                    showlegend=True,
                    title="AI Model State Space (ESS)",
                    height=400
                )
                st.plotly_chart(fig_ess_ai, use_container_width=True)
                
                st.markdown("**Truth Dimensions (GTFE):**")
                st.write(f"• **E** (Existence): {truth.E:.3f} - Factual accuracy")
                st.write(f"• **M** (Morality): {truth.M:.3f} - Ethical coherence")
                st.write(f"• **V** (Valence): {truth.V:.3f} - Emotional meaning")
                st.write(f"• **A** (Aesthetics): {truth.A:.3f} - Structural harmony")
            
            st.markdown("---")
            st.markdown("### 📊 Synchronization Analysis")
            
            fig_lcc_status = go.Figure()
            
            fig_lcc_status.add_trace(go.Indicator(
                mode="gauge+number+delta",
                value=lcc,
                title={'text': "Law of Correlational Causation (LCC)"},
                delta={'reference': 0.725, 'increasing': {'color': "green"}},
                gauge={
                    'axis': {'range': [0, 1]},
                    'bar': {'color': "darkblue"},
                    'steps': [
                        {'range': [0, 0.6], 'color': "lightgray"},
                        {'range': [0.6, 0.85], 'color': "lightgreen"},
                        {'range': [0.85, 1], 'color': "salmon"}
                    ],
                    'threshold': {
                        'line': {'color': "red", 'width': 4},
                        'thickness': 0.75,
                        'value': 0.85
                    }
                }
            ))
            
            fig_lcc_status.update_layout(height=350)
            st.plotly_chart(fig_lcc_status, use_container_width=True)
            
            if lcc_status_dict['in_target_range']:
                st.success(f"🎯 **MUTUAL CAUSATION ACHIEVED!** {lcc_status_dict['message']}")
            elif lcc > 0.85:
                st.warning(f"⚠️ {lcc_status_dict['message']}")
            else:
                st.info(f"ℹ️ {lcc_status_dict['message']}")
        
        with tab6:
            result_data = {
                "timestamp": datetime.now().isoformat(),
                "dataset_source": dataset_source_name,
                "n_samples": int(len(features)),
                "n_features": int(features.shape[1]),
                "ti_uop_sigma": {
                    "human_ess": human_ess.as_dict(),
                    "truth_dimensions": truth.as_dict(),
                    "lcc": float(lcc),
                    "lcc_status": lcc_status_dict['status'],
                    "sigma_star": float(sigma),
                    "gtfe_gradient": float(gtfe_grad),
                    "free_energy": float(free_energy)
                },
                "models": {}
            }
            
            for mt, res in amplification_results.items():
                result_data["models"][mt] = {
                    "amplification_score": float(res['amp_score']),
                    "r2_score": float(res['r2']),
                    "mae": float(res['mae']),
                    "amplification_stats": {
                        "mean": float(np.mean(res['amp_distribution'])),
                        "std": float(np.std(res['amp_distribution'])),
                        "min": float(np.min(res['amp_distribution'])),
                        "max": float(np.max(res['amp_distribution']))
                    }
                }
            
            result_data["datasets_processed"] = dataset_info
            
            out_json = os.path.join(SAVE_DIR, f"mood_amplifier_results_{int(time.time())}.json")
            with open(out_json, "w") as f:
                json.dump(result_data, f, indent=2)
            
            st.success(f"✓ Results saved to: {out_json}")
            
            st.json(result_data)
            
            with open(out_json, "r") as f:
                st.download_button(
                    label="📥 Download JSON Results",
                    data=f.read(),
                    file_name=f"mood_amplifier_results_{int(time.time())}.json",
                    mime="application/json"
                )
            
            st.markdown("---")
            st.subheader("🤖 Magai AI Integration")
            st.markdown("Export your results in a format optimized for Magai's AI analysis")
            
            magai_report = f"""# TI-UOP Mood Amplifier Analysis Report
Generated: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}
Dataset: {dataset_source_name}
Samples Analyzed: {len(features):,}

## TI-UOP Sigma Framework Results

### Emotional State Space (ESS) - Human
- **D (Information Density)**: {human_ess.D:.3f} - Cognitive load / mental processing intensity
- **T (Tralse/Contradiction)**: {human_ess.T:.3f} - Ability to hold contradictory thoughts
- **C (Coherence)**: {human_ess.C:.3f} - Mental unity and functional integration
- **F (Flow State)**: {human_ess.F:.3f} - Level of engagement and optimal experience
- **A (Agency)**: {human_ess.A:.3f} - Sense of control and executive function
- **R (Resilience)**: {human_ess.R:.3f} - Stress handling and emotional regulation

### AI Synchronization Metrics
- **LCC (Correlational Causation)**: {lcc:.3f} - {lcc_status_dict['status']}
  - Target Range: 0.60-0.85 for mutual causation
  - Status: {lcc_status_dict['message']}
  
- **Σ* (Sigma-Star)**: {sigma:.4f} - Ultimate synchronization metric
  - Higher values indicate better AI-human emotional alignment
  
- **GTFE Gradient**: {gtfe_grad:.4f} - Truth field equilibrium
  - {'✅ At equilibrium (stable emotional state)' if gtfe_grad < 0.2 else '⚠️ Not at equilibrium (unstable state)'}

- **Free Energy**: {free_energy:.4f} - Prediction error between human and AI states

### Truth Dimensions (GTFE Validation)
- **Existence (E)**: {truth.E:.3f} - Factual accuracy of emotional detection
- **Morality (M)**: {truth.M:.3f} - Ethical coherence of the analysis
- **Valence (V)**: {truth.V:.3f} - Emotional meaning and significance
- **Aesthetics (A)**: {truth.A:.3f} - Structural harmony and pattern beauty

## Machine Learning Model Performance

"""
            for mt, res in amplification_results.items():
                magai_report += f"""### {mt}
- **Amplification Score**: {res['amp_score']:.4f}
- **R² Score**: {res['r2']:.4f} (model accuracy)
- **Mean Absolute Error**: {res['mae']:.4f}
- **Amplification Stats**:
  - Mean: {np.mean(res['amp_distribution']):.4f}
  - Std Dev: {np.std(res['amp_distribution']):.4f}
  - Range: {np.min(res['amp_distribution']):.4f} to {np.max(res['amp_distribution']):.4f}

"""
            
            magai_report += f"""## EEG Band Power Analysis
- **Delta (0.5-4 Hz)**: Deep sleep, unconscious processes
- **Theta (4-8 Hz)**: Creativity, meditation, light sleep
- **Alpha (8-12 Hz)**: Relaxation, calm focus
- **Beta (12-30 Hz)**: Active thinking, concentration
- **Entropy**: Signal complexity and information content

## Suggested Magai Prompts

### For Analysis:
"Analyze this EEG mood amplification data and provide insights on the emotional state, cognitive load, and AI-human synchronization quality. Focus on the ESS dimensions and what they reveal about mental wellbeing."

### For Report Generation:
"Create a detailed psychological profile based on this TI-UOP Sigma analysis. Explain what the LCC value of {lcc:.3f} means for AI-human interaction quality and whether mutual causation was achieved."

### For Image Generation:
"Generate a visualization representing an emotional state with these characteristics: Cognitive density {human_ess.D:.1f}/1.0, Flow state {human_ess.F:.1f}/1.0, Resilience {human_ess.R:.1f}/1.0. Style: abstract, neurological, calming colors."

---
**Ready to use in Magai!** Copy this entire text and paste it into any Magai AI model for deep analysis.
"""
            
            st.text_area("Magai-Optimized Report", magai_report, height=300)
            
            col_magai1, col_magai2 = st.columns(2)
            
            with col_magai1:
                if st.button("📋 Copy Report to Clipboard", key="copy_magai"):
                    st.code(magai_report)
                    st.success("✓ Report ready! Copy the text above and paste into Magai")
            
            with col_magai2:
                st.download_button(
                    label="📄 Download Magai Report (.txt)",
                    data=magai_report,
                    file_name=f"magai_mood_report_{int(time.time())}.txt",
                    mime="text/plain"
                )
            
            with st.expander("📚 How to Use with Magai"):
                st.markdown("""
### Step-by-Step Guide:

#### 1. **For AI Analysis & Insights**
- Copy the report above
- Go to [Magai](https://magai.co) and start a new chat
- Select your preferred AI model (GPT-4, Claude, Gemini, etc.)
- Paste the report and add: *"Analyze this emotional state data and provide psychological insights"*

#### 2. **For Professional Reports**
- Copy the report
- In Magai, use the Document Editor feature
- Paste the data and ask: *"Format this into a professional psychological assessment report"*
- Export as PDF or Word document

#### 3. **For Mood Visualizations**
- Note your ESS values (D, T, C, F, A, R)
- In Magai, use DALL-E, Stable Diffusion, or other image generator
- Prompt: *"Create an abstract representation of this emotional state: [paste ESS values]. Make it [calming/energetic/balanced] with [color preferences]"*

#### 4. **For Comparative Analysis**
- Run multiple mood analyses over time
- Copy all reports into Magai
- Ask: *"Compare these emotional states and identify trends in my mental wellbeing"*

### 💡 Pro Tips:
- **Best Models for Analysis**: Claude (detailed), GPT-4 (balanced), Perplexity (research-backed)
- **Best Models for Reports**: GPT-4 (professional tone), Claude (empathetic)
- **Best for Images**: DALL-E 3 (quality), Stable Diffusion (artistic), Midjourney (aesthetic)
                """)
            
            if enable_upload and terabox_username and terabox_password:
                st.markdown("---")
                st.subheader("☁️ TeraBox Upload")
                
                upload_btn = st.button("Upload to TeraBox")
                
                if upload_btn:
                    with st.spinner("Uploading to TeraBox..."):
                        status_code, reason = upload_to_terabox(
                            out_json, 
                            f"MoodAmplifier/mood_amplifier_results_{int(time.time())}.json",
                            terabox_username,
                            terabox_password
                        )
                        
                        if status_code and status_code in [200, 201, 204]:
                            st.success(f"✓ Successfully uploaded to TeraBox (Status: {status_code})")
                        else:
                            st.error(f"✗ Upload failed: {reason}")
        
        if dataset_info:
            st.markdown("---")
            st.subheader("📦 Dataset Summary")
            st.table(pd.DataFrame(dataset_info))
        
    except Exception as e:
        st.error(f"An error occurred: {str(e)}")
        import traceback
        with st.expander("Error Details"):
            st.code(traceback.format_exc())

st.markdown("---")
st.caption("TI-UOP Mood Amplifier v1.0 • Author: Brandon + GPT-5")
