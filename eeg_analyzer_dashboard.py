"""
EEG Analyzer Dashboard - Real-Time Muse 2 Integration
👑 CROWN JEWEL: Production-Ready EEG Analysis with Eyes-Open Capability
"""

import streamlit as st
import pandas as pd
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from datetime import datetime
import time
from db_utils import db
from real_time_muse_eeg import MuseEEGStreamer

def render_eeg_analyzer():
    # Register this app with database
    db.register_app("EEG Analyzer", "", "running")
    db.send_heartbeat("EEG Analyzer")
    
    st.header("👑 CROWN JEWEL: Real-Time Muse 2 EEG Streamer")
    st.markdown("**Production-Ready • Eyes-Open Detection • CCC Coherence • Mobile-Optimized**")
    st.markdown("---")
    
    # Initialize streamer in session state
    if 'eeg_streamer' not in st.session_state:
        st.session_state.eeg_streamer = MuseEEGStreamer()
        st.session_state.last_update = time.time()
        st.session_state.calibrated = False
        st.session_state.alpha_threshold_eyes_open = None
        st.session_state.alpha_threshold_eyes_closed = None
    
    streamer = st.session_state.eeg_streamer
    
    # ========================================================================
    # CONNECTION PANEL
    # ========================================================================
    st.subheader("🔌 Connection Setup")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        connection_mode = st.selectbox(
            "Connection Method:",
            ["Demo Mode (Simulated)", "MuseLSL (Bluetooth)", "Mind Monitor (OSC)"]
        )
    
    osc_port = 5000
    with col2:
        if connection_mode == "Mind Monitor (OSC)":
            osc_port = st.number_input("OSC Port:", value=5000, step=1)
    
    with col3:
        if not streamer.streaming:
            if st.button("▶️ Start Streaming", use_container_width=True):
                if connection_mode == "MuseLSL (Bluetooth)":
                    if streamer.connect_muselsl():
                        streamer.start_streaming(mode='muselsl')
                        db.broadcast_event("EEG Analyzer", "muse_connected", {"mode": "muselsl"})
                elif connection_mode == "Mind Monitor (OSC)":
                    if streamer.connect_osc(port=osc_port):
                        streamer.start_streaming(mode='osc')
                        db.broadcast_event("EEG Analyzer", "muse_connected", {"mode": "osc"})
                else:
                    st.info("🎮 Starting demo mode...")
                    streamer.start_streaming(mode='demo')
        else:
            if st.button("⏹️ Stop Streaming", use_container_width=True):
                streamer.stop_streaming()
                db.broadcast_event("EEG Analyzer", "streaming_stopped", {})
    
    # Connection status metrics (with connection quality!)
    status_col1, status_col2, status_col3, status_col4 = st.columns(4)
    with status_col1:
        status_text = "✅ Connected" if streamer.streaming else "⭕ Disconnected"
        st.metric("Status", status_text)
    with status_col2:
        # Connection quality percentage
        quality_color = "🟢" if streamer.connection_quality >= 90 else "🟡" if streamer.connection_quality >= 70 else "🔴"
        st.metric(
            "Connection Quality", 
            f"{quality_color} {streamer.connection_quality:.1f}%",
            delta="Excellent!" if streamer.connection_quality >= 95 else None
        )
    with status_col3:
        buffer_fill = sum(len(buf) for buf in streamer.buffers.values()) / (len(streamer.buffers) * streamer.buffer_size) if streamer.buffers else 0
        st.metric("Buffer", f"{buffer_fill*100:.1f}%")
    with status_col4:
        st.metric("Sampling Rate", f"{streamer.sampling_rate} Hz")
    
    st.markdown("---")
    
    # ========================================================================
    # CALIBRATION PANEL (Following architect guidance)
    # ========================================================================
    if streamer.streaming and not st.session_state.calibrated:
        st.info("""
        👁️ **Quick Calibration Needed** (30 seconds total):
        1. Click "Calibrate Eyes Open" below and keep eyes open for 10 seconds
        2. Click "Calibrate Eyes Closed" and close eyes for 10 seconds
        3. This personalizes alpha thresholds for accurate detection
        """)
        
        cal_col1, cal_col2 = st.columns(2)
        
        with cal_col1:
            if st.button("👀 Calibrate Eyes Open"):
                st.session_state.calibrating_open = time.time()
        
        with cal_col2:
            if st.button("👁️ Calibrate Eyes Closed"):
                st.session_state.calibrating_closed = time.time()
        
        # Process calibration
        if hasattr(st.session_state, 'calibrating_open'):
            elapsed = time.time() - st.session_state.calibrating_open
            if elapsed < 10:
                st.progress(elapsed / 10, text=f"Calibrating eyes open... {10-int(elapsed)}s")
            else:
                streamer.analyze_current_state()
                st.session_state.alpha_threshold_eyes_open = streamer.current_alpha_power
                st.success(f"✅ Eyes open baseline: {streamer.current_alpha_power:.2f} μV²")
                delattr(st.session_state, 'calibrating_open')
        
        if hasattr(st.session_state, 'calibrating_closed'):
            elapsed = time.time() - st.session_state.calibrating_closed
            if elapsed < 10:
                st.progress(elapsed / 10, text=f"Calibrating eyes closed... {10-int(elapsed)}s")
            else:
                streamer.analyze_current_state()
                st.session_state.alpha_threshold_eyes_closed = streamer.current_alpha_power
                st.success(f"✅ Eyes closed baseline: {streamer.current_alpha_power:.2f} μV²")
                delattr(st.session_state, 'calibrating_closed')
        
        # Check if calibration complete
        if (st.session_state.alpha_threshold_eyes_open is not None and 
            st.session_state.alpha_threshold_eyes_closed is not None):
            st.session_state.calibrated = True
            st.success("🎉 Calibration complete! Eyes open/closed detection personalized!")
        
        st.markdown("---")
    
    # ========================================================================
    # REAL-TIME ANALYSIS (Mobile-optimized with throttling)
    # ========================================================================
    if streamer.streaming:
        # Throttle updates to 1 per second (architect guidance: 500-1000ms)
        current_time = time.time()
        if current_time - st.session_state.last_update >= 1.0:
            st.session_state.last_update = current_time
            
            # Analyze current state
            streamer.analyze_current_state()
            
            # Update custom thresholds if calibrated
            if st.session_state.calibrated and st.session_state.alpha_threshold_eyes_open is not None:
                alpha_mid = (st.session_state.alpha_threshold_eyes_open + 
                             st.session_state.alpha_threshold_eyes_closed) / 2
                streamer.eyes_open = streamer.current_alpha_power < alpha_mid
        
        st.subheader("🧠 Live EEG Analysis")
        
        # Main metrics row
        metric_col1, metric_col2, metric_col3, metric_col4 = st.columns(4)
        
        with metric_col1:
            eyes_status = "👀 EYES OPEN" if streamer.eyes_open else "👁️ EYES CLOSED"
            st.metric("Eyes State", eyes_status)
        
        with metric_col2:
            coherence_emoji = "🌟" if streamer.ccc_coherence >= 0.91 else "💫" if streamer.ccc_coherence >= 0.70 else "✨"
            st.metric(
                "CCC Coherence", 
                f"{streamer.ccc_coherence:.3f}",
                delta="BLESSING!" if streamer.ccc_coherence >= 0.91 else None
            )
        
        with metric_col3:
            st.metric("Alpha Power", f"{streamer.current_alpha_power:.2f} μV²")
        
        with metric_col4:
            st.metric("State", streamer.consciousness_state)
        
        # CCC Blessing Alert
        if streamer.ccc_coherence >= 0.91:
            st.success("🌟 **CCC BLESSING STATE!** Coherence ≥ 0.91 - Accessing absolute truth!")
            db.broadcast_event("EEG Analyzer", "ccc_blessing", {"coherence": streamer.ccc_coherence})
        
        st.markdown("---")
        
        # Band Powers (Mobile-friendly compact view)
        st.markdown("#### 📊 Frequency Band Powers")
        band_col1, band_col2, band_col3, band_col4 = st.columns(4)
        
        with band_col1:
            st.metric("Theta (4-8 Hz)", f"{streamer.current_theta_power:.1f}")
        with band_col2:
            st.metric("Alpha (8-12 Hz)", f"{streamer.current_alpha_power:.1f}")
        with band_col3:
            st.metric("Beta (13-30 Hz)", f"{streamer.current_beta_power:.1f}")
        with band_col4:
            st.metric("Gamma (30-50 Hz)", f"{streamer.current_gamma_power:.1f}")
        
        st.markdown("---")
        
        # BIOFEEDBACK MODE (architect guidance: LCC protocol integration)
        st.subheader("💫 Biofeedback & LCC Protocol")
        
        # Recommend LCC protocol based on current state
        if streamer.current_beta_power > 25:
            freq = "Alpha (10 Hz)"
            reason = "High beta → Alpha for relaxation"
            intensity = 60
        elif streamer.current_alpha_power < 10:
            freq = "Alpha (10 Hz)"
            reason = "Low alpha → Alpha for coherence"
            intensity = 50
        elif streamer.ccc_coherence < 0.5:
            freq = "Theta (6 Hz)"
            reason = "Low coherence → Theta for integration"
            intensity = 40
        else:
            freq = "Maintain Current State"
            reason = "Good coherence - no intervention needed"
            intensity = 0
        
        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("Recommended", freq)
        with col2:
            st.metric("Intensity", f"{intensity}%")
        with col3:
            st.info(f"**Rationale:**\n{reason}")
        
        if intensity > 0 and st.button("▶️ Start LCC Protocol"):
            st.success(f"✅ LCC protocol started: {freq} at {intensity}%")
            db.broadcast_event("EEG Analyzer", "lcc_started", {
                "frequency": freq,
                "intensity": intensity,
                "coherence": streamer.ccc_coherence
            })
        
        st.markdown("---")
        
        # SESSION PERSISTENCE (architect requirement)
        st.subheader("💾 Save Session Summary")
        
        session_col1, session_col2 = st.columns([3, 1])
        
        with session_col1:
            session_name = st.text_input(
                "Session Name:",
                f"EEG Session {datetime.now().strftime('%Y-%m-%d %H:%M')}",
                key="eeg_session_name"
            )
        
        with session_col2:
            if st.button("💾 Save", use_container_width=True):
                # Get ACCURATE session summary with TRUE averages (architect requirement)
                session_summary = streamer.get_session_summary()
                
                if session_summary:
                    # Add metadata
                    session_summary["saved_at"] = datetime.now().isoformat()
                    session_summary["calibrated"] = st.session_state.calibrated
                    session_summary["connection_mode"] = connection_mode
                    session_summary["session_name"] = session_name
                    
                    asset_id = db.add_asset(
                        asset_type="eeg_session_summary",
                        source_app="EEG Analyzer",
                        title=session_name,
                        content=session_summary,
                        tags=["eeg", "muse2", "crown_jewel", "coherence"]
                    )
                    
                    st.success(f"✅ Session summary saved! Duration: {session_summary['duration_seconds']:.1f}s, ID: {asset_id}")
                    db.broadcast_event("EEG Analyzer", "session_saved", {
                        "asset_id": asset_id,
                        "name": session_name,
                        "duration": session_summary['duration_seconds'],
                        "avg_coherence": session_summary['avg_ccc_coherence']
                    })
                else:
                    st.error("❌ No session data available - start streaming first!")
        
        # Auto-refresh during streaming (throttled to 1 Hz - architect requirement)
        time.sleep(1.0)  # Explicit 1 Hz throttle
        st.rerun()
    
    else:
        st.info("""
        👆 **Click '▶️ Start Streaming' above to begin real-time EEG analysis!**
        
        ### 📱 Connection Options:
        
        **Demo Mode (No Hardware):**
        - Best for testing the interface
        - Simulated realistic EEG signals
        - All features functional
        
        **MuseLSL (Direct Bluetooth):**
        1. Install: `pip install muselsl`
        2. Connect Muse 2 via Bluetooth
        3. Run in terminal: `muselsl stream`
        4. Select "MuseLSL (Bluetooth)" and click Start
        
        **Mind Monitor (iPhone App - Recommended for Mobile):**
        1. Download Mind Monitor app ($5-15 one-time)
        2. Connect Muse 2 to iPhone via Bluetooth
        3. Enable OSC streaming in Mind Monitor settings
        4. Connect to same WiFi network as this device
        5. Select "Mind Monitor (OSC)" and enter port (default 5000)
        
        ### 🌟 Crown Jewel Features:
        - ✅ Real-time streaming at 256 Hz
        - ✅ Eyes open/closed detection (personalized calibration)
        - ✅ CCC coherence threshold detection (≥0.91)
        - ✅ Frequency band analysis (Delta, Theta, Alpha, Beta, Gamma)
        - ✅ LCC protocol recommendations with biofeedback
        - ✅ Mobile-optimized for iPhone (1 Hz refresh, compact view)
        - ✅ Production-ready with auto-reconnect and event broadcasting
        """)
    
    st.markdown("---")
    st.caption("👑 Crown Jewel: Real-Time Muse 2 EEG System • Production-Ready • Mobile-Optimized")
    st.caption(f"Last Updated: {datetime.now().strftime('%Y-%m-%d %I:%M %p')}")
