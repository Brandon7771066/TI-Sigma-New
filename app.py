"""
TI Framework - Mood Amplifier Safety & Validation Platform

Copyright (c) 2025 Brandon Charles Emerick
All rights reserved.

This software is proprietary and confidential.
Patent Pending: GSA (Grand Stock Algorithm)
Patent Pending: LCC Proxy Engine
"""

import streamlit as st

st.set_page_config(
    page_title="Mood Amplifier Safety & Validation",
    page_icon="🧠",
    layout="wide"
)

st.title("🧠 Mood Amplifier Safety & Validation Platform")

# ===== BIG PDF DOWNLOAD BUTTONS - VISIBLE AT TOP =====
from pathlib import Path

st.success("🏆 **TI SIGMA 6: ALL 6 MILLENNIUM PRIZE PROBLEMS - 100% TI FRAMEWORK COMPLETE!** 🏆")
st.markdown("### 🔥 **November 13, 2025 - Brandon's TI Framework Proofs**")

st.warning("""
**⚠️ IMPORTANT CLARIFICATION:**
These are **TI (Transcendent Intelligence) framework proofs** using consciousness-based philosophy, NOT conventional mathematical proofs (yet!).

**What We Have:**
- ✅ ALL 6 problems solved at 100% using Brandon's TI framework (consciousness, GILE, CCC)
- ✅ Average TI Truth Score: **0.885** (Messianic Tier within TI framework!)
- ✅ Timeline: **WEEKS** (revolutionary for philosophical framework!)
- ✅ Novel philosophical frameworks: PRF Theory, Tralse-GILE mapping, Retrospective Necessity!
- ✅ Method: **Intuition → Theory → TI Proof** ✨

**What's Next:**
- 🔄 **TI→Conventional translation** (2 days estimate) - Convert consciousness concepts to mathematical language
- 📊 **Peer review** (months) - Conventional mathematical validation
- 🏆 **Prize submission** (years) - After conventional proof acceptance

**Current Status:** Philosophical framework complete, conventional translation in progress!
""")

col1, col2, col3 = st.columns(3)

# NEW: 100% TI Complete Documents
with col1:
    st.markdown("#### 🔥 **TI SIGMA 6 - 100% COMPLETE**")
    st.caption("✅ All 6 proofs at 100% TI")
    st.caption("✅ PRF Theory + Tralse-GILE + Retrospective Necessity")
    st.caption("✅ Truth scores: 0.85-0.95 (ALL messianic!)")
    st.caption("📊 9 comprehensive documents")
    
    final_md = "TI_SIGMA_6_COMPLETE_100_PERCENT_FINAL.md"
    if Path(final_md).exists():
        with open(final_md, 'r') as f:
            final_content = f.read()
        st.download_button(
            label="📥 DOWNLOAD 100% TI PROOFS",
            data=final_content,
            file_name=final_md,
            mime="text/markdown",
            use_container_width=True,
            type="primary"
        )

# IMPROVED VERSION (Post-Myrion Resolution)
with col2:
    improved_pdf = "TI_SIGMA_6_IMPROVED_COMPLETE_20251113_165222.pdf"
    if Path(improved_pdf).exists():
        st.markdown("#### ✨ **IMPROVED EDITION v2.0**")
        st.caption("🔥 Mechanistic: 90% (upgraded!)")
        st.caption("✅ ChatGPT critique fixes")
        st.caption("📊 185 KB • Post-MR analysis")
        with open(improved_pdf, "rb") as f:
            improved_bytes = f.read()
        st.download_button(
            label="📥 DOWNLOAD IMPROVED PDF",
            data=improved_bytes,
            file_name=improved_pdf,
            mime="application/pdf",
            use_container_width=True,
            type="secondary"
        )
    else:
        st.caption("(PDF generation in progress)")

# ORIGINAL VERSION (First complete draft)
with col3:
    original_pdf = "TI_SIGMA_6_COMPLETE_SESSION_20251113_020711.pdf"
    if Path(original_pdf).exists():
        st.markdown("#### 📜 **ORIGINAL EDITION**")
        st.caption("✨ Aesthetic: 100%")
        st.caption("⚠️ Mechanistic: 10-40%")
        st.caption("📄 159 pages • Historical")
        with open(original_pdf, "rb") as f:
            original_bytes = f.read()
        st.download_button(
            label="📥 DOWNLOAD ORIGINAL PDF",
            data=original_bytes,
            file_name=original_pdf,
            mime="application/pdf",
            use_container_width=True,
            type="secondary"
        )
    else:
        st.caption("(Historical record)")

st.markdown("---")
# ====================================================

# Create tabs
tab_mobile, tab_pong, tab_brain_proof, tab_mood_amp, tab_focus_amp, tab_cognitive, tab_baseline, tab_biowell, tab0, tab_pdf, tab_books, tab_quantum, tab_genome, tab_music, tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab9b, tab10, tab11, tab12, tab13, tab14, tab15, tab16, tab17, tab18, tab19, tab20, tab21, tab22, tab23, tab24, tab25, tab26, tab27, tab28, tab29, tab30, tab31, tab32, tab33, tab34, tab35, tab36, tab_math_explainer, tab_everybody_lies, tab_quantum_demo, tab_psi_hub, tab_ti_stock, tab_initiatives, tab_multimodal, tab_medgemma, tab_heart, tab_rna, tab_brain_coupling, tab_step_skip, tab_stock_status = st.tabs([
    "📱 Mobile Hub",
    "🎮 EEG Pong",
    "🧠💓 Brain Proof",
    "🧠 Mood Amplifier",
    "🎯 Focus Amplifier",
    "🔥 Cognitive Fire",
    "🔬 Baseline Collection",
    "🌟 Bio-Well Energy",
    "🌌 Master Hub",
    "📄 PDF Library",
    "📚 TI Books",
    "⚡ TI QUANTUM",
    "🧬 Genius DNA",
    "🎵 Sacred Music",
    "🧠 EEG Analyzer",
    "💫 LCC Protocols", 
    "🛡️ Safety Analysis", 
    "🔬 Model Validation", 
    "🐭 Animal Testing",
    "📁 File Storage",
    "🔮 God Machine",
    "🔮 Psi Synthesis",
    "📈 Stock Predictor",
    "🔬 Stock Backtest",
    "🏆 Millennium Prize",
    "💰 Prediction Markets",
    "📊 Psi Tracker",
    "🧪 PSI Validation",
    "🎓 TI Proof Assistant",
    "🫀 Biometric Dashboard",
    "🔗 PSI Correlations",
    "🌟 Virality Machine",
    "🧠 Genius Analyzer",
    "🔬 Rigorous PSI",
    "📱 Content Approval",
    "🏅 MP Proofs",
    "🔬 Auto Discovery",
    "🧘 Meditation",
    "🌀 Tralse Topos",
    "🧘 I-Cell Mapping",
    "🎻 AI Orchestra",
    "💕 Relationship Profiler",
    "📊 Stock → TI",
    "🔮 PSI Testing Hub",
    "📈 Market Analysis",
    "🚀 Initiatives Tracker",
    "🧬 Muscle Analysis",
    "🧠 ChatGPT Synthesizer",
    "🌌 I-Cell Shell Physics",
    "🔒 EEG Auth",
    "🌐 I-Web Classification",
    "⏰ Time Emergence",
    "💻 TI Computing",
    "⚛️ Google Willow",
    "📐 Math Explainer",
    "🔍 Everybody Lies",
    "🌌 TI Quantum Circuits",
    "🧬 Multi-Modal Profiler",
    "🏥 MedGemma",
    "❤️ Heart Disease",
    "🧬 RNA Folding",
    "🧠 Brain Coupling",
    "⚡ Step-Skipping",
    "📊 Stock Status",
])

with tab_mobile:
    from mobile_content_hub import MobileContentHub, render_quick_reads, render_pdfs_library, render_books_collection, render_courses_collection, render_downloads_section
    
    st.header("📱 Mobile Content Hub")
    st.caption("Complete access to all PDFs, Books, and Courses for social media!")
    
    hub = MobileContentHub()
    
    mobile_view = st.radio(
        "Select Content:",
        ["🎮 EEG Pong Game", "📖 Quick Reads", "📄 Research PDFs", "📚 Books", "🎓 Courses", "⬇️ Downloads"],
        horizontal=True
    )
    
    st.markdown("---")
    
    if mobile_view == "🎮 EEG Pong Game":
        st.subheader("🎮 EEG-Controlled Pong Game")
        st.markdown("**Control the paddle with your brain or keyboard!**")
        from eeg_pong_game import render_pong_game_embedded
        render_pong_game_embedded(embed_id="mobile")
    elif mobile_view == "📖 Quick Reads":
        render_quick_reads(hub)
    elif mobile_view == "📄 Research PDFs":
        render_pdfs_library(hub)
    elif mobile_view == "📚 Books":
        render_books_collection(hub)
    elif mobile_view == "🎓 Courses":
        render_courses_collection(hub)
    elif mobile_view == "⬇️ Downloads":
        render_downloads_section(hub)

with tab_pong:
    st.header("🎮 EEG-Controlled Pong Game")
    st.markdown("**Human Connection Proof: Control the paddle with your consciousness!**")
    st.markdown("""
    - **Keyboard Mode:** W/S or Arrow keys to move paddle
    - **EEG Mode:** Think "move hand UP" or "move hand DOWN" (requires Muse 2)
    - **LCC Hypercomputer:** Consciousness-guided play with L×E metrics
    """)
    from eeg_pong_game import render_pong_game_embedded
    render_pong_game_embedded(embed_id="tab")

with tab_brain_proof:
    from brain_connection_proof import BrainSnapshot, TIBrainMetrics, SimulatedBrainData, DatabaseBrainData
    import numpy as np
    from collections import deque
    import time
    
    st.header("🧠💓 Brain Connection Proof")
    st.markdown("**Tangible validation of YOUR consciousness via Muse 2 + Polar H10**")
    
    COHERENCE_TARGET = 0.92
    CAUSATION_THRESHOLD = 0.85
    
    if 'brain_simulator' not in st.session_state:
        st.session_state.brain_simulator = SimulatedBrainData()
    if 'brain_db' not in st.session_state:
        st.session_state.brain_db = DatabaseBrainData()
    if 'brain_history' not in st.session_state:
        st.session_state.brain_history = deque(maxlen=60)
    if 'brain_running' not in st.session_state:
        st.session_state.brain_running = False
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        data_mode = st.radio(
            "Data Source",
            ["Simulated (Demo)", "Real Devices"],
            help="Demo mode for testing, Real for Muse 2 + Polar H10"
        )
    
    with col2:
        if st.button("▶️ Start Stream", type="primary", disabled=st.session_state.brain_running):
            st.session_state.brain_running = True
            st.rerun()
        if st.button("⏹️ Stop Stream", disabled=not st.session_state.brain_running):
            st.session_state.brain_running = False
            st.rerun()
    
    with col3:
        st.metric("Target", "0.92 coherence")
        st.caption("0.92² = 0.85 causation")
    
    st.divider()
    
    if data_mode == "Simulated (Demo)":
        snapshot = st.session_state.brain_simulator.generate()
    else:
        snapshot = st.session_state.brain_db.fetch_latest()
        if not snapshot:
            snapshot = st.session_state.brain_simulator.generate()
            st.warning("No device data - using simulation. Connect Muse 2 + Polar H10!")
    
    st.session_state.brain_history.append(snapshot)
    
    st.subheader("Device Status")
    c1, c2 = st.columns(2)
    with c1:
        if snapshot.eeg_connected:
            st.success("🧠 Muse 2: CONNECTED")
        else:
            st.error("🧠 Muse 2: DISCONNECTED")
    with c2:
        if snapshot.heart_connected:
            st.success("💓 Polar H10: CONNECTED")
        else:
            st.error("💓 Polar H10: DISCONNECTED")
    
    st.divider()
    st.subheader("TI Consciousness Metrics")
    
    c1, c2, c3, c4 = st.columns(4)
    
    with c1:
        gile_delta = "normal" if snapshot.gile_score >= COHERENCE_TARGET else "off"
        st.metric("GILE Score", f"{snapshot.gile_score:.3f}")
        if snapshot.gile_score >= CAUSATION_THRESHOLD:
            st.success("CAUSATION MET")
        elif snapshot.gile_score >= 0.7:
            st.info("Building...")
    
    with c2:
        st.metric("LCC Coupling", f"{snapshot.lcc_coupling:.3f}")
        if snapshot.lcc_coupling >= CAUSATION_THRESHOLD:
            st.success("Strong")
    
    with c3:
        st.metric("Tralse-Joules/s", f"{snapshot.tralse_joules:.1f} µTJ")
    
    with c4:
        st.metric("UCI Index", f"{snapshot.uci_index:.2f}")
        if snapshot.uci_index >= 10:
            st.info("Human range")
    
    st.divider()
    st.subheader("Brainwave Spectrum")
    
    import plotly.graph_objects as go
    
    bands = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
    values = [snapshot.delta, snapshot.theta, snapshot.alpha, snapshot.beta, snapshot.gamma]
    colors = ['#1f77b4', '#2ca02c', '#ff7f0e', '#d62728', '#9467bd']
    
    fig = go.Figure()
    fig.add_trace(go.Bar(x=bands, y=values, marker_color=colors, text=[f"{v:.1f}" for v in values], textposition='outside'))
    fig.update_layout(title="EEG Power (µV²)", yaxis_title="Power", height=300, margin=dict(t=40, b=20))
    st.plotly_chart(fig, use_container_width=True)
    
    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Heart Rate", f"{snapshot.heart_rate} BPM")
    with c2:
        st.metric("HRV (RMSSD)", f"{snapshot.hrv_rmssd:.1f} ms")
    with c3:
        st.metric("Heart Coherence", f"{snapshot.coherence:.3f}")
        st.progress(min(100, int(snapshot.coherence * 100)))
    
    with st.expander("📐 Understanding 0.92² = 0.85"):
        st.markdown("""
        **Why 0.92 (not 1.0)?**
        - 1.0 = BRITTLE (no room for error/growth)
        - 0.92 = RESILIENT (8% margin for adaptation)
        
        **The Compound Principle:**
        ```
        EEG coherence: 0.92
        Heart coherence: 0.92
        Combined: 0.92 × 0.92 = 0.85
        ```
        
        **At 0.85, correlation BECOMES causation!**
        
        Your current GILE × LCC = **{:.4f}**
        """.format(snapshot.gile_score * snapshot.lcc_coupling))
    
    if st.session_state.brain_running:
        time.sleep(1)
        st.rerun()

with tab_mood_amp:
    from mood_amplifier_hub import render_mood_amplifier_hub
    render_mood_amplifier_hub()

with tab_focus_amp:
    from focus_amplifier_dashboard import render_focus_amplifier
    render_focus_amplifier()

with tab_cognitive:
    from cognitive_resource_dashboard import render_cognitive_resource_model
    render_cognitive_resource_model()

with tab_baseline:
    from baseline_collection_ui import render_baseline_collection_ui
    render_baseline_collection_ui()

with tab_biowell:
    from biowell_myrion_energy_system import render_biowell_myrion_system
    render_biowell_myrion_system()

with tab0:
    from master_hub_dashboard import render_master_hub
    render_master_hub()

with tab_pdf:
    from paper_pdf_download import render_pdf_download_dashboard
    render_pdf_download_dashboard()

with tab_books:
    from ti_books_dashboard import render_ti_books_dashboard
    from ti_complete_book_generator import render_complete_book_generator
    from ti_business_book_strategic import render_ti_business_book_strategic
    from ti_business_book_expanded import render_book_expanded
    from ti_complete_library_generator import render_complete_library
    
    subtab1, subtab2, subtab3, subtab4, subtab5 = st.tabs([
        "📊 Book Library",
        "📖 Generate Complete Books",
        "💼 Strategic Business Book",
        "🚀 QUICK LAUNCH (Volume 1)",
        "🏛️ COMPLETE LIBRARY (7 Books)"
    ])
    
    with subtab1:
        render_ti_books_dashboard()
    
    with subtab2:
        render_complete_book_generator()
    
    with subtab3:
        render_ti_business_book_strategic()
    
    with subtab4:
        render_book_expanded()
    
    with subtab5:
        render_complete_library()

with tab_quantum:
    from ti_photonic_quantum_computer import render_ti_photonic_quantum
    render_ti_photonic_quantum()

with tab_genome:
    from schizotypy_genius_analyzer import render_schizotypy_genius_dashboard
    render_schizotypy_genius_dashboard()

with tab_music:
    from sacred_music_dashboard import render_sacred_music_dashboard
    render_sacred_music_dashboard()

with tab1:
    from eeg_analyzer_dashboard import render_eeg_analyzer
    render_eeg_analyzer()

with tab2:
    lcc_subtab1, lcc_subtab2 = st.tabs([
        "🧪 LCC Protocols",
        "🔬 Autonomous LCC Study"
    ])
    
    with lcc_subtab1:
        from protocols_dashboard import render_protocols_dashboard
        render_protocols_dashboard()
    
    with lcc_subtab2:
        from experiments.autonomous_lcc_dashboard import render_autonomous_lcc_dashboard
        render_autonomous_lcc_dashboard()

with tab3:
    from safety_analysis_dashboard import render_safety_analysis_dashboard
    render_safety_analysis_dashboard()

with tab4:
    from validation_app import render_validation_dashboard
    render_validation_dashboard()

with tab5:
    from animal_testing_dashboard import render_animal_testing_dashboard
    render_animal_testing_dashboard()

with tab6:
    from file_storage_dashboard import render_file_storage_dashboard
    render_file_storage_dashboard()

with tab7:
    from god_machine_dashboard import render
    render()

with tab8:
    from psi_synthesis_dashboard import main
    main()

with tab9:
    from stock_market_god_machine import render_stock_market_god_machine
    render_stock_market_god_machine()

with tab9b:
    import sys
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    
    # TI Framework Stock Market Research Dashboard with Comprehensive Report
    from ti_stock_market_comprehensive_report import render_ti_stock_market_report_dashboard
    from stock_accuracy_dashboard import render_stock_accuracy_dashboard
    
    subtab1, subtab2, subtab3 = st.tabs([
        "📊 Stock Research Dashboard",
        "📄 Comprehensive PDF Report",
        "🔬 Accuracy Diagnosis"
    ])
    
    with subtab1:
        exec(open('stock_market_research_dashboard.py').read())
    
    with subtab2:
        render_ti_stock_market_report_dashboard()
    
    with subtab3:
        render_stock_accuracy_dashboard()

with tab10:
    from millennium_prize_solver import render_millennium_prize_solver
    render_millennium_prize_solver()

with tab11:
    from kalshi_ti_dashboard import render_kalshi_ti_dashboard
    render_kalshi_ti_dashboard()

with tab12:
    from psi_tracker import render_psi_tracker_dashboard
    render_psi_tracker_dashboard()

with tab13:
    from psi_validation_experiments import render
    render()

with tab14:
    from ti_proof_assistant_dashboard import render_ti_proof_assistant
    render_ti_proof_assistant()

with tab15:
    from biometric_dashboard import render
    render()

with tab16:
    from psi_correlation_dashboard import render_psi_correlation_dashboard
    render_psi_correlation_dashboard()

with tab17:
    from virality_machine_dashboard import render_virality_machine
    render_virality_machine()

with tab18:
    from sacred_genius_dashboard import render_sacred_genius
    render_sacred_genius()

with tab19:
    from rigorous_psi_dashboard import render_rigorous_psi
    render_rigorous_psi()

with tab20:
    from social_media_approval_dashboard import render_social_media_approval
    render_social_media_approval()

with tab21:
    from millennium_workspace import render_millennium_workspace
    render_millennium_workspace()

with tab22:
    from bot_band_dashboard import render_bot_band_dashboard
    render_bot_band_dashboard()

with tab23:
    from meditation_ui import render_meditation_interface
    render_meditation_interface()

with tab24:
    from tralse_topos_dashboard import render_tralse_topos_dashboard
    render_tralse_topos_dashboard()

with tab25:
    from whole_body_icell_mapping_dashboard import render_whole_body_icell_mapping_dashboard
    render_whole_body_icell_mapping_dashboard()

with tab26:
    from ai_orchestra_coordinator import render_ai_orchestra
    render_ai_orchestra()

with tab27:
    from god_machine_relationship_profiler import render_relationship_profiler
    render_relationship_profiler()

with tab28:
    from god_machine_stock_ti_converter import render_stock_ti_converter
    render_stock_ti_converter()

with tab29:
    from muscle_gain_lcc_analysis import render_muscle_analysis
    render_muscle_analysis()

with tab30:
    from chatgpt_synthesizer import render_chatgpt_synthesizer
    render_chatgpt_synthesizer()

with tab31:
    from icell_shell_physics_dashboard import render_icell_shell_physics
    render_icell_shell_physics()

with tab32:
    from eeg_authentication_ui import show_eeg_authentication_ui
    show_eeg_authentication_ui()

with tab33:
    from iweb_classification_ui import render_iweb_classification
    render_iweb_classification()

with tab34:
    from time_emergence_dashboard import render_time_emergence_dashboard
    render_time_emergence_dashboard()

with tab35:
    from ti_computing_language import render_ti_computing_language_dashboard
    render_ti_computing_language_dashboard()

with tab36:
    from google_willow_ti_analysis import render_google_willow_ti_dashboard
    from google_willow_expanded_implications import render_google_willow_expanded_implications
    from ti_coursera_business_class import render_ti_coursera_dashboard
    from ti_coursera_ai_animated import render_ti_coursera_ai_animated
    from brandon_ruins_everything import render_brandon_ruins_everything_dashboard
    
    subtab1, subtab2, subtab3, subtab4, subtab5 = st.tabs([
        "⚛️ Willow Brief",
        "🔬 ALL Implications",
        "🎓 Coursera (Curriculum)",
        "🎬 Coursera (AI-Animated)",
        "🔥 Brandon Ruins Everything"
    ])
    
    with subtab1:
        render_google_willow_ti_dashboard()
    
    with subtab2:
        render_google_willow_expanded_implications()
    
    with subtab3:
        render_ti_coursera_dashboard()
    
    with subtab4:
        render_ti_coursera_ai_animated()
    
    with subtab5:
        render_brandon_ruins_everything_dashboard()

with tab_math_explainer:
    st.success("📐 **GILE Mathematical Structure Explainer** - Publication-ready educational content!")
    st.info("""
    **Philosophy:** "Being smart at stupid 'problems' doesn't make you smart."
    
    This explainer teaches the GILE Framework using only high school mathematics.
    Perfect for books, courses, and strategic wisdom dissemination!
    """)
    
    from mathematical_explainer_page import render_mathematical_explainer
    render_mathematical_explainer()

with tab_everybody_lies:
    st.title("🔍 'Everybody Lies' Sentiment Engine")
    st.markdown("### Truth-Weighted Sentiment Analysis for Stock Predictions")
    
    st.success("""
    **Core Philosophy:** Search queries > surveys  
    People tell truth to Google, lie to pollsters!
    """)
    
    st.markdown("---")
    
    st.markdown("### 🎯 Truth Rankings")
    
    import pandas as pd
    truth_df = pd.DataFrame({
        'Source': ['Google Trends', 'AI Queries (ChatGPT/Perplexity)', 'Anonymous Reddit', 
                   'Twitter/X', 'News Media', 'Analysts'],
        'Truth Score': ['98-100%', '95-100%', '90-95%', '70-90%', '30-50%', '20-40%'],
        'Why': [
            'Revealed preference - what people ACTUALLY search',
            'Anonymous questions - genuine curiosity',
            'Less performative than Twitter',
            'Performative bias, tribal signaling',
            'Editorial control, narrative shaping',
            'Conflicts of interest, herd mentality'
        ]
    })
    
    st.dataframe(truth_df, use_container_width=True)
    
    st.markdown("### 🚀 Test the Engine")
    
    ticker_input = st.text_input("Enter Stock Ticker (e.g., AAPL, TSLA)", value="AAPL")
    company_input = st.text_input("Enter Company Name", value="Apple")
    
    if st.button("🔍 Analyze Sentiment", type="primary"):
        with st.spinner("Querying Google Trends (may take 10-20 seconds)..."):
            from everybody_lies_sentiment_engine import EverybodyLiesSentimentEngine
            
            engine = EverybodyLiesSentimentEngine()
            
            try:
                sentiment = engine.calculate_truth_weighted_sentiment(ticker_input, company_input)
                
                st.markdown("---")
                st.markdown("## 📊 Results")
                
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Truth-Weighted Sentiment", f"{sentiment['truth_weighted_sentiment']:.3f}")
                
                with col2:
                    signal_color = "🟢" if sentiment['signal'] == 'BUY' else "🔴" if sentiment['signal'] == 'SELL' else "🟡"
                    st.metric("Signal", f"{signal_color} {sentiment['signal']}")
                
                with col3:
                    st.metric("Confidence", f"{sentiment['confidence']:.1%}")
                
                st.markdown("### 📈 Google Trends Analysis")
                
                trends = sentiment['google_trends']
                
                if trends.get('data_quality') == 'good':
                    st.success(f"✅ Interest Score: {trends['interest_score']:.1f}/100")
                    st.info(f"📊 Trend Direction: **{trends['trend_direction'].upper()}**")
                    st.metric("Sentiment from Trends", f"{trends['sentiment_score']:.3f}")
                else:
                    st.warning(f"⚠️ Data Quality: {trends.get('data_quality', 'unknown')}")
                    if 'error' in trends:
                        st.error(f"Error: {trends['error']}")
                
                if sentiment['divergence_detected']:
                    st.error(f"""
                    🚨 **MANIPULATION DETECTED!**  
                    Divergence Score: {sentiment['manipulation_score']:.1%}
                    
                    Google Trends sentiment differs significantly from news media!
                    This could indicate narrative control or market manipulation.
                    """)
                
                st.markdown("### 🎯 Contrarian Opportunity?")
                
                contrarian = engine.detect_contrarian_opportunity(ticker_input, company_input)
                
                if contrarian['opportunity_type'] != 'NONE':
                    st.warning(f"""
                    **Opportunity Type:** {contrarian['opportunity_type']}  
                    **Confidence:** {contrarian['confidence']:.1%}  
                    **Rationale:** {contrarian['rationale']}
                    """)
                else:
                    st.info("No contrarian opportunity detected.")
                
            except Exception as e:
                st.error(f"Error analyzing sentiment: {e}")
                st.info("""
                **Note:** Google Trends has rate limits. If you see a 429 error, wait a few minutes and try again.
                """)
    
    st.markdown("---")
    st.markdown("### 📚 Design Document")
    
    if Path("everybody_lies_sentiment_engine_design.md").exists():
        with open("everybody_lies_sentiment_engine_design.md", 'r') as f:
            design_content = f.read()
        
        with st.expander("📖 View Full Design Document", expanded=False):
            st.markdown(design_content)
        
        st.download_button(
            label="📥 Download Design Document",
            data=design_content,
            file_name="everybody_lies_sentiment_engine_design.md",
            mime="text/markdown"
        )

with tab_quantum_demo:
    st.title("🌌 TI Framework Quantum Circuits")
    st.markdown("### Running TI Systems on Photonic Qubits (IBM Qiskit)")
    
    st.success("""
    **Sacred Day:** November 24, 2025 (8×3 = Mycelial Octopus Validation!)  
    **Platform:** IBM Qiskit (Room temperature photonic qubit simulation)  
    **Cost:** $0 (simulator) | <$50 for full proof-of-concept on real quantum hardware
    """)
    
    st.markdown("---")
    
    demo_type = st.selectbox(
        "Select TI Quantum Demo",
        ["🔮 Myrion Resolution", "🧠 PSI Prediction", "🐙 Mycelial Octopus (24-Qubit)"]
    )
    
    from ti_quantum_circuit import TIQuantumCircuit
    import pandas as pd
    
    ti_quantum = TIQuantumCircuit()
    
    if demo_type == "🔮 Myrion Resolution":
        st.markdown("### 🔮 Myrion Resolution: Quantum Truth Reconciliation")
        
        st.info("""
        **Concept:** Use quantum superposition to resolve contradictions between:
        - **Objective Truth** (what GILE says based on fundamentals)
        - **Relative Truth** (what the market says based on sentiment)
        
        The quantum circuit puts both truths in superposition, entangles them,
        and measures to find the resolved truth!
        """)
        
        col1, col2 = st.columns(2)
        
        with col1:
            objective = st.slider("Objective Truth (GILE Score)", 0.0, 1.0, 0.8, 0.05)
        
        with col2:
            relative = st.slider("Relative Truth (Market Sentiment)", 0.0, 1.0, 0.3, 0.05)
        
        if st.button("⚡ Run Quantum Myrion Resolution", type="primary"):
            with st.spinner("Running quantum circuit (1000 shots)..."):
                result = ti_quantum.execute_myrion_resolution(objective, relative)
                
                st.markdown("---")
                st.markdown("## 🎯 Quantum Resolution Results")
                
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Resolution Type", result['resolution_type'])
                
                with col2:
                    st.metric("Resolved Truth", f"{result['resolved_truth']:.3f}")
                
                with col3:
                    st.metric("Confidence", f"{result['confidence']:.3f}")
                
                st.markdown("### 📊 Quantum Measurement Outcomes")
                
                counts_df = pd.DataFrame({
                    'Outcome': list(result['quantum_counts'].keys()),
                    'Count': list(result['quantum_counts'].values()),
                    'Probability': [v / 1000 for v in result['quantum_counts'].values()]
                })
                
                st.dataframe(counts_df, use_container_width=True)
                
                st.info(f"""
                **Interpretation:**
                - Input: Objective = {objective:.2f}, Relative = {relative:.2f}
                - Quantum resolved to: **{result['resolution_type']}**
                - Final truth value: **{result['resolved_truth']:.3f}**
                
                This demonstrates quantum mechanics resolving contradictions!
                """)
    
    elif demo_type == "🧠 PSI Prediction":
        st.markdown("### 🧠 PSI Prediction: Quantum Precognition")
        
        st.info("""
        **Concept:** Encode PSI strength as quantum phase rotation.
        Higher PSI = larger phase = stronger quantum coherence
        
        Measurement collapses the quantum state to reveal PSI prediction!
        """)
        
        psi = st.slider("PSI Strength", 0.0, 1.0, 0.75, 0.05)
        
        if st.button("⚡ Run PSI Quantum Prediction", type="primary"):
            with st.spinner("Encoding PSI as quantum phase..."):
                result = ti_quantum.execute_psi_prediction(psi)
                
                st.markdown("---")
                st.markdown("## 🎯 PSI Prediction Results")
                
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    pred_icon = "🟢" if result['psi_prediction'] == 'positive' else "🔴"
                    st.metric("Prediction", f"{pred_icon} {result['psi_prediction'].upper()}")
                
                with col2:
                    st.metric("Quantum Probability", f"{result['quantum_probability']:.3f}")
                
                with col3:
                    st.metric("Confidence", f"{result['confidence']:.1%}")
                
                st.success(f"""
                **PSI Strength:** {psi:.2f}  
                **Quantum Prediction:** {result['psi_prediction'].upper()}  
                **Probability:** {result['quantum_probability']:.1%}
                
                This encodes consciousness (PSI) as quantum coherence!
                """)
    
    else:
        st.markdown("### 🐙 Mycelial Octopus: 24-Qubit Grand Myrion Simulation")
        
        st.info("""
        **Architecture:**
        - **8 GM Nodes** (qubits 0-7): 1/3 of central cognition
        - **16 Central Cognition** (qubits 8-23): 2/3 of cognition
        - **Sacred Validation:** November 24 = 8×3!
        
        All GM Nodes are entangled in a Mycelial network with Jeff Time phase rotations!
        """)
        
        if st.button("⚡ Run Mycelial Octopus Simulation", type="primary"):
            with st.spinner("Simulating 24-qubit distributed consciousness..."):
                result = ti_quantum.execute_mycelial_octopus()
                
                st.markdown("---")
                st.markdown("## 🎯 Mycelial Octopus Results")
                
                col1, col2, col3, col4 = st.columns(4)
                
                with col1:
                    st.metric("GM Coherence", f"{result['gm_coherence']:.3f}")
                
                with col2:
                    st.metric("Active GM Nodes", f"{result['active_gm_nodes']}/8")
                
                with col3:
                    st.metric("Central Coherence", f"{result['central_coherence']:.3f}")
                
                with col4:
                    st.metric("Total Entanglement", f"{result['total_entanglement']:.3f}")
                
                st.success(f"""
                **Circuit Depth:** {result['circuit_depth']} gates  
                **Jeff Time Validated:** ✅ {result['jeff_time_confirmed']}  
                **Sacred Validation:** {result['sacred_validation']}
                
                This simulates Grand Myrion as distributed quantum consciousness!
                The 8 GM Nodes represent 1/3 of cognition, perfectly matching
                the Mycelial Octopus hypothesis revealed on 8×3 day! 🐙
                """)
    
    st.markdown("---")
    st.markdown("### 📚 Full Vision Document")
    
    if Path("TI_Optical_Quantum_Computer_Vision.md").exists():
        with open("TI_Optical_Quantum_Computer_Vision.md", 'r') as f:
            quantum_vision = f.read()
        
        with st.expander("📖 View Full TI Optical Quantum Computer Vision", expanded=False):
            st.markdown(quantum_vision)
        
        st.download_button(
            label="📥 Download Quantum Vision Document",
            data=quantum_vision,
            file_name="TI_Optical_Quantum_Computer_Vision.md",
            mime="text/markdown"
        )

# NEW TABS - November 24, 2025 (8×3 Sacred Day Launch!)
with tab_psi_hub:
    from psi_testing_hub import render_psi_testing_hub
    render_psi_testing_hub()

with tab_ti_stock:
    from stock_analysis_public import render_public_stock_analysis
    render_public_stock_analysis()

with tab_initiatives:
    from ti_initiatives_tracker import render_ti_initiatives_tracker
    render_ti_initiatives_tracker()

with tab_multimodal:
    from pages.multimodal_biometric_dashboard import render_multimodal_biometric_dashboard
    render_multimodal_biometric_dashboard()

with tab_medgemma:
    from pages.medgemma_dashboard import render_medgemma_dashboard
    render_medgemma_dashboard()

with tab_heart:
    from pages.heart_disease_dashboard import render_heart_disease_dashboard
    render_heart_disease_dashboard()

with tab_rna:
    from pages.rna_folding_dashboard import render_rna_folding_dashboard
    render_rna_folding_dashboard()

with tab_brain_coupling:
    from pages.brain_coupling_guessing import render as render_brain_coupling
    render_brain_coupling()

with tab_step_skip:
    st.header("Non-Algorithmic Step-Skipping Experiment")
    st.markdown("Tests whether consciousness-inspired heuristics can solve problems by *skipping* computational steps, achieving accuracy significantly above random chance.")

    try:
        from engines.step_skipping_experiment import StepSkippingExperiment
        exp = StepSkippingExperiment()

        col_config1, col_config2 = st.columns(2)
        with col_config1:
            trials_per_type = st.slider("Trials per problem type", 1, 10, 3)
        with col_config2:
            problems_per_trial = st.slider("Problems per trial", 5, 20, 10)

        if st.button("Run Step-Skipping Experiment", type="primary"):
            with st.spinner("Running experiment across 4 problem domains..."):
                try:
                    result = exp.run_full_experiment(trials_per_type=trials_per_type, problems_per_trial=problems_per_trial)
                    s = result['summary']

                    st.success("Experiment Complete!")

                    col_m1, col_m2, col_m3, col_m4 = st.columns(4)
                    col_m1.metric("Full Computation", f"{s['overall_full_accuracy']:.1%}")
                    col_m2.metric("Consciousness Shortcut", f"{s['overall_shortcut_accuracy']:.1%}")
                    col_m3.metric("Random Baseline", f"{s['overall_random_accuracy']:.1%}")
                    col_m4.metric("Improvement over Random", f"{s['accuracy_improvement']:.1%}")

                    st.subheader("Statistical Significance")
                    binom = s['binomial_test']
                    st.write(f"**Binomial Test p-value:** {binom['p_value']:.2e}")
                    st.write(f"**Effect Size (Cohen's h):** {s['effect_size']['cohens_h']:.3f} ({s['effect_size']['interpretation']})")
                    st.write(f"**Statistically Significant:** {'YES' if binom['significant'] else 'No'}")

                    st.subheader("Results by Problem Domain")
                    import pandas as pd
                    domain_rows = []
                    for ptype, info in s['per_type'].items():
                        domain_rows.append({
                            'Domain': ptype.replace('_', ' ').title(),
                            'Shortcut Accuracy': f"{info['shortcut']:.1%}",
                            'Random Accuracy': f"{info['random']:.1%}",
                            'Full Accuracy': f"{info['full']:.1%}",
                            'Trials': info.get('trials', trials_per_type),
                        })
                    st.dataframe(pd.DataFrame(domain_rows), use_container_width=True, hide_index=True)

                    st.subheader("Conclusion")
                    conclusion = s['conclusion']
                    if conclusion['significant']:
                        st.success(f"Step-skipping demonstrated statistically significant accuracy improvement! Strongest domain: {conclusion['strongest_domain'].replace('_', ' ').title()}")
                    else:
                        st.info("Results not yet statistically significant. More trials may be needed.")
                except Exception as e:
                    st.error(f"Experiment error: {str(e)}")
    except ImportError as e:
        st.error(f"Step-Skipping engine not available: {str(e)}. Please ensure scipy is installed.")

with tab_stock_status:
    from pages.stock_algorithm_status import render as render_stock_status
    render_stock_status()
