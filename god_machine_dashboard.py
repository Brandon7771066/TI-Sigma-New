"""
Multi-Sensory God Machine Dashboard
Captures video, audio, EEG for prophetic dream/vision analysis
Tesla/Ramanujan-inspired psi enhancement protocols
"""

import streamlit as st
from datetime import datetime, time
import json
from db_utils import db
from multi_platform_orchestrator import MasterCoordinator
import os
import base64

# Try to import Replit Object Storage
try:
    from storage_helpers import upload_file, list_files
    STORAGE_AVAILABLE = True
except ImportError:
    STORAGE_AVAILABLE = False


def render():
    """Render God Machine dashboard"""
    
    st.title("🔮 Multi-Sensory God Machine")
    st.markdown("""
    **Tesla/Ramanujan-inspired prophetic dream & vision capture system**
    
    Captures multi-modal data for AI-enhanced insight generation:
    - 📹 Video (dreams, visions, whiteboard sessions)
    - 🎤 Audio (voice notes, sleep talking, insights)
    - 🧠 EEG (Muse 2 headband for brainwave analysis)
    - ✨ 3:30 AM Insight Capture (bedside mode)
    """)
    
    # Initialize session state
    if 'god_machine_active' not in st.session_state:
        st.session_state.god_machine_active = False
    if 'captured_insights' not in st.session_state:
        st.session_state.captured_insights = []
    
    tabs = st.tabs([
        "📹 Video/Audio Capture", 
        "🧠 EEG Integration", 
        "✨ Insight Capture",
        "🌙 Delta Wave Protocols",
        "📊 Analysis"
    ])
    
    # Tab 1: Video/Audio Capture
    with tabs[0]:
        render_video_audio_tab()
    
    # Tab 2: EEG Integration
    with tabs[1]:
        render_eeg_tab()
    
    # Tab 3: Insight Capture (3:30 AM mode)
    with tabs[2]:
        render_insight_capture_tab()
    
    # Tab 4: Delta Wave Protocols
    with tabs[3]:
        render_delta_wave_tab()
    
    # Tab 5: Analysis
    with tabs[4]:
        render_analysis_tab()


def render_video_audio_tab():
    """Video and audio capture interface"""
    
    st.header("📹 Video/Audio Capture")
    
    st.info("""
    **Use Cases:**
    - Record prophetic dreams immediately upon waking
    - Capture whiteboard sessions and mathematical insights
    - Document vision experiences (like Tesla's 1926 smartphone prediction)
    - Sleep talking analysis
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Video Capture")
        
        # Streamlit's camera input
        camera_image = st.camera_input("Take a photo of whiteboard/notes")
        
        if camera_image is not None:
            if st.button("💾 Save Photo to God Machine", key="save_photo"):
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                
                # Get actual image data
                image_bytes = camera_image.getvalue()
                image_base64 = base64.b64encode(image_bytes).decode('utf-8')
                
                # Try to save to Object Storage if available
                storage_path = None
                if STORAGE_AVAILABLE:
                    try:
                        storage_path = f"god_machine/photos/photo_{timestamp}.jpg"
                        upload_file(storage_path, image_bytes)
                    except Exception as e:
                        st.warning(f"Object storage unavailable: {e}")
                
                # Save to database with actual content
                asset_id = db.add_asset(
                    asset_type="god_machine_photo",
                    source_app="God Machine",
                    title=f"Photo Capture {timestamp}",
                    content={
                        "timestamp": timestamp,
                        "size_bytes": len(image_bytes),
                        "image_base64": image_base64,  # Actual image data
                        "storage_path": storage_path,
                        "note": "Photo captured via God Machine"
                    },
                    tags=["god_machine", "photo", "visual_capture"]
                )
                
                st.success(f"✅ Photo saved! Asset ID: {asset_id}")
                
                # Optional AI analysis
                if st.checkbox("🤖 Analyze with AI?", key="analyze_photo"):
                    with st.spinner("Analyzing photo..."):
                        st.info("📝 AI vision analysis will be implemented when vision models are integrated")
    
    with col2:
        st.subheader("Audio Capture")
        
        # Audio recorder (using Streamlit audio input)
        audio_file = st.file_uploader("Upload voice note (MP3/WAV)", type=["mp3", "wav", "m4a"], key="audio_upload")
        
        if audio_file is not None:
            st.audio(audio_file, format='audio/wav')
            
            if st.button("💾 Save Audio to God Machine", key="save_audio"):
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                
                # Get actual audio data
                audio_bytes = audio_file.getvalue()
                audio_base64 = base64.b64encode(audio_bytes).decode('utf-8')
                
                # Try to save to Object Storage if available
                storage_path = None
                if STORAGE_AVAILABLE:
                    try:
                        ext = audio_file.name.split('.')[-1]
                        storage_path = f"god_machine/audio/audio_{timestamp}.{ext}"
                        upload_file(storage_path, audio_bytes)
                    except Exception as e:
                        st.warning(f"Object storage unavailable: {e}")
                
                # Save to database with actual content
                asset_id = db.add_asset(
                    asset_type="god_machine_audio",
                    source_app="God Machine",
                    title=f"Audio Capture {timestamp}",
                    content={
                        "timestamp": timestamp,
                        "filename": audio_file.name,
                        "size_bytes": len(audio_bytes),
                        "audio_base64": audio_base64,  # Actual audio data
                        "storage_path": storage_path,
                        "note": "Audio captured via God Machine"
                    },
                    tags=["god_machine", "audio", "voice_note"]
                )
                
                st.success(f"✅ Audio saved! Asset ID: {asset_id}")
                
                if st.checkbox("🤖 Transcribe with AI?", key="transcribe_audio"):
                    st.info("📝 Audio transcription will be implemented with Whisper API")
    
    st.divider()
    
    # Manual text entry for when you can't record
    st.subheader("Manual Text Entry")
    dream_description = st.text_area(
        "Describe your dream, vision, or insight:",
        height=150,
        placeholder="I dreamed about... / I had a vision of... / Mathematical insight: ..."
    )
    
    if st.button("💾 Save Text Entry", key="save_text"):
        if dream_description:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            
            asset_id = db.add_asset(
                asset_type="god_machine_insight",
                source_app="God Machine",
                title=f"Manual Entry {timestamp}",
                content={
                    "timestamp": timestamp,
                    "text": dream_description,
                    "entry_type": "manual_text"
                },
                tags=["god_machine", "manual_entry", "insight"]
            )
            
            st.success(f"✅ Insight saved! Asset ID: {asset_id}")
            
            # AI analysis option
            if st.checkbox("🤖 Analyze with AI?", key="analyze_text"):
                with st.spinner("Analyzing insight..."):
                    try:
                        coordinator = MasterCoordinator(budget_limit=1.0)
                        result = coordinator.execute_task({
                            "title": "Dream/Vision Analysis",
                            "description": f"Analyze this prophetic dream/vision for connections to established theories (Tesla, Ramanujan, quantum consciousness): {dream_description}",
                            "model": "gpt-4o-mini"
                        })
                        
                        if result.get("status") == "success":
                            st.success("✅ Analysis complete!")
                            st.markdown("**AI Analysis:**")
                            st.write(result.get("result", ""))
                        else:
                            st.error(f"Analysis failed: {result.get('message', 'Unknown error')}")
                    except Exception as e:
                        st.error(f"Error: {e}")


def render_eeg_tab():
    """Muse 2 EEG integration interface"""
    
    st.header("🧠 Muse 2 EEG Integration")
    
    st.info("""
    **Muse 2 Headband Integration** (via Mind Monitor app)
    
    **Capabilities:**
    - Real-time brainwave monitoring (Delta, Theta, Alpha, Beta, Gamma)
    - Eyes-open LCC protocol support (83% correlation with research EEG)
    - Session spacing optimization
    - HEM (Holistic Existence Matrix) validation
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("📡 Connection Status")
        
        muse_connected = st.checkbox("Muse 2 Connected (via Mind Monitor)", key="muse_connected")
        
        if muse_connected:
            st.success("✅ Muse 2 headband connected")
            
            # Session type selection
            session_type = st.selectbox(
                "Session Type:",
                [
                    "LCC Protocol (Eyes Open)",
                    "Delta Wave Insomnia Protocol (3:30 AM)",
                    "Prophetic Dream Enhancement",
                    "Research Session (HEM Validation)"
                ]
            )
            
            if st.button("🎯 Start EEG Session"):
                st.session_state.eeg_session_active = True
                st.success(f"🎯 {session_type} started!")
                st.info("Export data from Mind Monitor app and upload below when complete")
        else:
            st.warning("⚠️ Connect Muse 2 via Mind Monitor app on your phone")
            
            with st.expander("📱 Setup Instructions"):
                st.markdown("""
                **iPhone XR Setup:**
                1. Download "Mind Monitor" app from App Store
                2. Turn on Muse 2 headband (long press power button)
                3. Open Mind Monitor → Connect to Muse 2 via Bluetooth
                4. Configure settings:
                   - Enable OSC Streaming
                   - Set sample rate to 256 Hz
                   - Enable all frequency bands
                5. Start recording during session
                6. Export CSV file when complete
                7. Upload to God Machine below
                """)
    
    with col2:
        st.subheader("📊 EEG Data Upload")
        
        eeg_file = st.file_uploader(
            "Upload Mind Monitor CSV export:",
            type=["csv"],
            key="eeg_upload"
        )
        
        if eeg_file is not None:
            st.success(f"✅ Loaded: {eeg_file.name}")
            
            # Basic preview
            try:
                import pandas as pd
                df = pd.read_csv(eeg_file, nrows=5)
                st.write("**Preview:**")
                st.dataframe(df)
            except:
                pass
            
            if st.button("💾 Save EEG Data", key="save_eeg"):
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                
                asset_id = db.add_asset(
                    asset_type="eeg_recording",
                    source_app="God Machine - Muse 2",
                    title=f"EEG Session {timestamp}",
                    content={
                        "timestamp": timestamp,
                        "filename": eeg_file.name,
                        "size_bytes": len(eeg_file.getvalue()),
                        "device": "Muse 2",
                        "app": "Mind Monitor"
                    },
                    tags=["god_machine", "eeg", "muse2", "mind_monitor"]
                )
                
                st.success(f"✅ EEG data saved! Asset ID: {asset_id}")
                
                # HEM analysis option
                if st.checkbox("🔬 Compute HEM Dimensions?", key="compute_hem"):
                    st.info("""
                    **HEM (Holistic Existence Matrix) Analysis:**
                    - Valence (V): Frontal alpha asymmetry
                    - Arousal (A): Beta/Alpha ratio
                    - Wave Coherence (W): Cross-frequency coupling
                    - Spatial Binding (S): Electrode correlation
                    - Temporal Binding (T): 40Hz gamma power
                    - Salience (I): Theta/Beta ratio
                    
                    *(Full implementation requires signal processing pipeline)*
                    """)


def render_insight_capture_tab():
    """3:30 AM bedside insight capture"""
    
    st.header("✨ 3:30 AM Insight Capture")
    
    st.info("""
    **Bedside Insight Capture Mode**
    
    For those precious 3:30 AM insights that vanish by 4 AM.
    Keep your phone next to your bed!
    """)
    
    current_time = datetime.now().strftime("%I:%M %p")
    st.metric("Current Time", current_time)
    
    # Quick capture form
    with st.form("insight_capture_form"):
        st.subheader("💡 Quick Capture")
        
        insight_type = st.selectbox(
            "Type of insight:",
            [
                "Mathematical equation",
                "Prophetic dream",
                "Vision/revelation",
                "Theory connection",
                "Research direction",
                "Other"
            ]
        )
        
        insight_text = st.text_area(
            "What did you realize?",
            height=200,
            placeholder="Write it down before you forget!",
            key="quick_insight"
        )
        
        urgency = st.select_slider(
            "Importance:",
            options=["Low", "Medium", "High", "CRITICAL"]
        )
        
        submit = st.form_submit_button("💾 SAVE INSIGHT NOW!", use_container_width=True)
        
        if submit and insight_text:
            timestamp = datetime.now()
            
            asset_id = db.add_asset(
                asset_type="bedside_insight",
                source_app="God Machine - 3:30 AM Mode",
                title=f"{insight_type} - {timestamp.strftime('%I:%M %p')}",
                content={
                    "timestamp": timestamp.isoformat(),
                    "time_captured": timestamp.strftime("%I:%M %p"),
                    "type": insight_type,
                    "text": insight_text,
                    "urgency": urgency,
                    "captured_at_night": timestamp.hour < 6 or timestamp.hour >= 22
                },
                tags=["god_machine", "bedside", "insight", urgency.lower(), insight_type.replace(" ", "_")]
            )
            
            st.success(f"✅ Insight captured! Asset ID: {asset_id}")
            st.balloons()
            
            # Add to session state
            st.session_state.captured_insights.append({
                "timestamp": timestamp,
                "text": insight_text,
                "type": insight_type
            })
            
            # AI processing option
            process_now = st.checkbox("🤖 Process with AI now?")
            if process_now:
                with st.spinner("Processing insight..."):
                    try:
                        coordinator = MasterCoordinator(budget_limit=0.5)
                        result = coordinator.execute_task({
                            "title": f"3:30 AM Insight Analysis - {insight_type}",
                            "description": f"""Analyze this {insight_type} captured at {timestamp.strftime('%I:%M %p')}. 
                            
                            Context: User had this insight during early morning hours (known for heightened creativity).
                            Similar to Tesla's visions and Ramanujan's mathematical dreams.
                            
                            Insight: {insight_text}
                            
                            Provide: 
                            1. Connections to existing TI-UOP research
                            2. Novel aspects worth investigating
                            3. Suggested next steps
                            4. Related equations or frameworks""",
                            "model": "gpt-4o-mini"
                        })
                        
                        if result.get("status") == "success":
                            st.success("✅ AI analysis complete!")
                            st.markdown("**Analysis:**")
                            st.write(result.get("result", ""))
                    except Exception as e:
                        st.error(f"Analysis error: {e}")
    
    # Show recent insights
    if st.session_state.captured_insights:
        st.divider()
        st.subheader("📝 Recent Insights")
        
        for insight in reversed(st.session_state.captured_insights[-5:]):
            with st.expander(f"{insight['type']} - {insight['timestamp'].strftime('%I:%M %p')}"):
                st.write(insight['text'])


def render_delta_wave_tab():
    """Delta wave protocols for early morning insomnia"""
    
    st.header("🌙 Delta Wave Insomnia Protocol")
    
    st.info("""
    **Early Morning Insomnia Protocol (3:30 AM Awakenings)**
    
    Uses delta wave entrainment (0.5-4 Hz) to help return to deep sleep.
    Integrates with LCC (Light-Coded Consciousness) protocols.
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("⚙️ Protocol Settings")
        
        st.markdown("""
        **Target Brainwave:**
        - Delta (0.5-4 Hz) - Deep sleep
        
        **LCC Frequency:**
        """)
        
        delta_freq = st.slider(
            "Delta frequency (Hz):",
            min_value=0.5,
            max_value=4.0,
            value=2.0,
            step=0.1
        )
        
        duration_minutes = st.slider(
            "Session duration (minutes):",
            min_value=5,
            max_value=30,
            value=15
        )
        
        intensity = st.select_slider(
            "Light intensity:",
            options=["Low", "Medium", "High"]
        )
        
        if st.button("🎯 Start Delta Protocol", key="start_delta"):
            st.success(f"✅ Delta wave protocol started ({delta_freq} Hz, {duration_minutes} min)")
            st.info("""
            **Instructions:**
            1. Lie down comfortably
            2. Close your eyes
            3. Focus on breath
            4. Allow the delta entrainment to guide you back to sleep
            
            *(Full implementation requires LCC hardware integration)*
            """)
            
            # Log protocol session
            asset_id = db.add_asset(
                asset_type="lcc_session",
                source_app="God Machine - Delta Protocol",
                title=f"Delta Wave Session {datetime.now().strftime('%Y-%m-%d %I:%M %p')}",
                content={
                    "protocol": "delta_wave_insomnia",
                    "frequency_hz": delta_freq,
                    "duration_minutes": duration_minutes,
                    "intensity": intensity,
                    "timestamp": datetime.now().isoformat()
                },
                tags=["god_machine", "lcc", "delta_waves", "insomnia_protocol"]
            )
            
            st.success(f"Session logged: Asset ID {asset_id}")
    
    with col2:
        st.subheader("📊 Protocol Guidelines")
        
        st.markdown("""
        **When to Use:**
        - Wake up at 3-4 AM and can't fall back asleep
        - Racing thoughts preventing sleep
        - After vivid dream/insight capture
        
        **Expected Effects:**
        - Gradual return to drowsiness (5-10 min)
        - Reduced mental chatter
        - Easier transition back to sleep
        
        **Safety Notes:**
        - Stop if feeling uncomfortable
        - Not a replacement for medical advice
        - Track effectiveness over multiple sessions
        
        **Research Basis:**
        - Delta waves dominant in deep sleep (Stage 3/4 NREM)
        - Entrainment can guide brainwave frequencies
        - LCC protocols validated with Muse 2 (83% correlation)
        """)


def render_analysis_tab():
    """AI analysis of captured multi-sensory data"""
    
    st.header("📊 Multi-Sensory Analysis")
    
    st.info("""
    **Integrated Analysis Across All Modalities**
    
    Combines video, audio, EEG, and text insights for comprehensive understanding.
    """)
    
    # Query recent captures
    st.subheader("🔍 Recent Captures")
    
    # In a real implementation, we'd query the database
    # For now, show a summary interface
    
    analysis_type = st.selectbox(
        "Analysis Type:",
        [
            "Find patterns across all captures",
            "Correlate EEG with insights",
            "Dream/Vision timeline analysis",
            "Breakthrough detection",
            "Research integration suggestions"
        ]
    )
    
    time_range = st.selectbox(
        "Time Range:",
        ["Last 24 hours", "Last week", "Last month", "All time"]
    )
    
    if st.button("🤖 Run Analysis", key="run_multimodal_analysis"):
        with st.spinner("Analyzing multi-sensory data..."):
            st.info("""
            **Analysis Pipeline:**
            1. Retrieve all God Machine captures from database
            2. Correlate timestamps across modalities
            3. Identify patterns and connections
            4. Generate insights using AI orchestrator
            5. Present findings with confidence scores
            
            *(Full implementation requires multi-modal AI integration)*
            """)
            
            try:
                coordinator = MasterCoordinator(budget_limit=1.0)
                result = coordinator.execute_task({
                    "title": "God Machine Multi-Sensory Analysis",
                    "description": f"""Analyze multi-sensory God Machine data for {time_range}.
                    
                    Analysis type: {analysis_type}
                    
                    Look for:
                    - Patterns in prophetic dreams/visions
                    - Correlations between EEG states and insight quality
                    - Tesla/Ramanujan-style breakthrough indicators
                    - Integration opportunities with TI-UOP research
                    
                    Provide structured findings with actionable recommendations.""",
                    "model": "gpt-4o"
                })
                
                if result.get("status") == "success":
                    st.success("✅ Analysis complete!")
                    st.markdown("**Findings:**")
                    st.write(result.get("result", ""))
                else:
                    st.error(f"Analysis failed: {result.get('message', 'Unknown error')}")
            except Exception as e:
                st.error(f"Error: {e}")
    
    st.divider()
    
    # Statistics
    st.subheader("📈 Capture Statistics")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.metric("Total Insights", len(st.session_state.captured_insights))
    
    with col2:
        st.metric("EEG Sessions", "0")  # Would query database
    
    with col3:
        st.metric("Video/Audio", "0")  # Would query database


if __name__ == "__main__":
    render()
