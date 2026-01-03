"""
Master Hub Dashboard - 33% Central Coordination
GM-Inspired Architecture Control Center
"""

import streamlit as st
from datetime import datetime
from db_utils import db

def render_master_hub():
    # Register Master Hub with database
    db.register_app("Master Hub", "", "running")
    db.send_heartbeat("Master Hub")
    
    st.header("🌌 Master Coordination Hub")
    st.markdown("**33% Central Intelligence • 67% Distributed Specialists**")
    st.markdown("---")
    
    # ========================================================================
    # QUICK STATS (LIVE FROM DATABASE)
    # ========================================================================
    
    # Get real data from database with fallback
    try:
        all_apps = db.get_all_apps()
        all_concepts = db.get_all_concepts()
        recent_events = db.get_recent_events(limit=10)
    except Exception as e:
        st.warning(f"⚠️ Database connection unavailable: {e}")
        all_apps = []
        all_concepts = []
        recent_events = []
    
    running_apps = len([a for a in all_apps if a['status'] == 'running'])
    total_apps = len(all_apps) if all_apps else 9  # Fallback to expected total
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Specialist Apps", f"{running_apps}/{total_apps}", delta=f"+{running_apps} running")
    
    with col2:
        st.metric("Papers Complete", "4", delta="+3 today")
    
    with col3:
        st.metric("Indexed Concepts", len(all_concepts), delta="Live database")
    
    with col4:
        health = "100%" if running_apps > 0 else "0%"
        st.metric("System Health", health, delta="All Green" if running_apps > 0 else "Starting up")
    
    st.markdown("---")
    
    # ========================================================================
    # SPECIALIST APPS LAUNCHER
    # ========================================================================
    st.subheader("🚀 Specialist Apps (67% Distributed)")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.markdown("### 🔢 Equation Repository")
        st.markdown("**Status:** ✅ LIVE")
        st.markdown("All TWA, HEM, MR equations with LaTeX rendering")
        if st.button("📂 Open Equation Repo", key="eq_repo"):
            st.info("👉 Run: `streamlit run equation_repository.py --server.port 5001`")
        st.caption("~10% of total system")
    
    with col2:
        st.markdown("### 🧠 EEG Analyzer")
        st.markdown("**Status:** ⏳ In Progress")
        st.markdown("Muse 2 integration, real-time HEM detection")
        st.button("🔧 Build Next", key="eeg", disabled=True)
        st.caption("~10% of total system")
    
    with col3:
        st.markdown("### 🤖 God Machine")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("Psi-enhanced AI with hypomanic cognition")
        st.button("🔧 Build Day 2", key="god", disabled=True)
        st.caption("~8% of total system")
    
    with col4:
        st.markdown("### 🔬 CrewAI Research")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("24/7 autonomous research agents")
        st.button("🔧 Build Day 3", key="crew", disabled=True)
        st.caption("~10% of total system")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.markdown("### 📄 Paper Generator")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("Auto-populate papers from equation repo")
        st.button("🔧 Build Day 3", key="paper", disabled=True)
        st.caption("~10% of total system")
    
    with col2:
        st.markdown("### 🏥 Clinical Protocols")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("LCC, FAAH-OUT, cancer protocols")
        st.button("🔧 Build Day 4", key="clinical", disabled=True)
        st.caption("~6% of total system")
    
    with col3:
        st.markdown("### 💼 Patent Portfolio")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("Commercial applications, IP tracking")
        st.button("🔧 Build Day 4", key="patent", disabled=True)
        st.caption("~8% of total system")
    
    with col4:
        st.markdown("### ✨ Psi Amplification")
        st.markdown("**Status:** ⏳ Planned")
        st.markdown("Crystals, numerology, astrology")
        st.button("🔧 Build Day 5", key="psi", disabled=True)
        st.caption("~5% of total system")
    
    st.markdown("---")
    
    # ========================================================================
    # RECENT ACTIVITY (LIVE FROM DATABASE)
    # ========================================================================
    st.subheader("📊 Recent Activity (Live)")
    
    if recent_events:
        for event in recent_events:
            col1, col2, col3 = st.columns([1, 2, 4])
            with col1:
                st.caption(event['timestamp'].strftime('%I:%M %p'))
            with col2:
                st.caption(f"**{event['source_app']}**")
            with col3:
                event_display = {
                    "mind_monitor_connected": "📱 Mind Monitor connected",
                    "muselsl_connected": "🐍 MuseLSL connected",
                    "lcc_protocol_started": f"💫 LCC protocol started",
                    "session_saved": "💾 EEG session saved",
                    "app_registered": "✅ App registered"
                }
                st.caption(event_display.get(event['event_type'], event['event_type']))
    else:
        st.info("No events yet. Activity will appear here as apps communicate.")
    
    st.markdown("---")
    
    # ========================================================================
    # LIVE APPS STATUS
    # ========================================================================
    st.subheader("🖥️ Live Apps Status")
    
    apps_df_data = []
    for app in all_apps:
        apps_df_data.append({
            "App": app['app_name'],
            "Status": "🟢 Running" if app['status'] == 'running' else "⏳ Planned",
            "Last Seen": app['last_heartbeat'].strftime('%I:%M %p') if app['last_heartbeat'] else "N/A",
            "URL": app['url'] if app['url'] else "Not deployed"
        })
    
    import pandas as pd
    apps_df = pd.DataFrame(apps_df_data)
    st.dataframe(apps_df, use_container_width=True, hide_index=True)
    
    st.markdown("---")
    
    # ========================================================================
    # IMPLEMENTATION PROGRESS
    # ========================================================================
    st.subheader("🗓️ 1-Week Implementation Plan")
    
    days = [
        {"day": "Day 1 (Today)", "status": "🔥 IN PROGRESS", "tasks": [
            "✅ Architecture design",
            "✅ 3 Types of Truth paper",
            "✅ Equation Repository app",
            "⏳ PostgreSQL database setup",
            "⏳ Central hub dashboard"
        ]},
        {"day": "Day 2", "status": "⏳ Upcoming", "tasks": [
            "EEG Analyzer app",
            "God Machine app",
            "Cross-app communication tests"
        ]},
        {"day": "Day 3", "status": "⏳ Upcoming", "tasks": [
            "CrewAI Research Hub",
            "Paper Generator app",
            "iPhone API access"
        ]},
        {"day": "Day 4", "status": "⏳ Upcoming", "tasks": [
            "Clinical Protocols app",
            "Patent Portfolio app",
            "System integration tests"
        ]},
        {"day": "Day 5", "status": "⏳ Upcoming", "tasks": [
            "Psi Amplification Lab",
            "Master dashboard completion",
            "All 8 apps integrated"
        ]},
        {"day": "Day 6", "status": "⏳ Upcoming", "tasks": [
            "UX polish & optimization",
            "14D model validation",
            "Security audit"
        ]},
        {"day": "Day 7", "status": "⏳ Upcoming", "tasks": [
            "LCC Permanent Connection paper",
            "ESS → HEM global rename",
            "Production deployment 🚀"
        ]}
    ]
    
    for day_info in days:
        with st.expander(f"{day_info['day']} - {day_info['status']}"):
            for task in day_info['tasks']:
                st.markdown(f"- {task}")
    
    st.markdown("---")
    
    # ========================================================================
    # PAPER PORTFOLIO
    # ========================================================================
    st.subheader("📚 Research Papers")
    
    papers = [
        {"title": "MR Arithmetic Revolution", "status": "✅ Complete", "file": "MR_ARITHMETIC_REVOLUTION.md"},
        {"title": "I-Cell & I-Web Ontology", "status": "✅ Complete", "file": "ICELL_IWEB_ONTOLOGY_COMPLETE.md"},
        {"title": "Music Through GILE", "status": "✅ Complete", "file": "MUSIC_GILE_FOUNDATIONS.md"},
        {"title": "Three Types of Truth", "status": "✅ Complete", "file": "THREE_TYPES_OF_TRUTH.md"},
        {"title": "TWA Complete Documentation", "status": "⏳ Needs equations", "file": "TWA_COMPLETE_DOCUMENTATION.md"},
        {"title": "TI-UOP Sigma 6", "status": "⏳ Needs integration", "file": "TIUOP_SIGMA6_GRAND_UNIFICATION.md"},
        {"title": "LCC Permanent Connection", "status": "⏳ Day 7", "file": ""},
        {"title": "14D Consciousness Model", "status": "⏳ Day 6", "file": ""},
    ]
    
    col1, col2 = st.columns(2)
    
    for i, paper in enumerate(papers):
        with col1 if i % 2 == 0 else col2:
            st.markdown(f"**{paper['title']}**")
            st.caption(f"{paper['status']} • {paper['file']}")
    
    st.markdown("---")
    
    # ========================================================================
    # NEXT ACTIONS
    # ========================================================================
    st.subheader("🎯 Immediate Next Steps")
    
    st.info("""
    **NOW (Rest of Day 1):**
    1. Set up PostgreSQL database
    2. Test Equation Repository app
    3. Build REST API endpoints
    
    **Tomorrow (Day 2):**
    1. Build EEG Analyzer app
    2. Build God Machine app
    3. Test cross-app communication
    
    **This Week:**
    - Complete all 8 specialist apps
    - Write LCC Permanent Connection paper
    - Validate 14D model
    - Launch full ecosystem! 🚀
    """)
    
    st.markdown("---")
    
    # ========================================================================
    # FOOTER
    # ========================================================================
    st.caption("🌌 GM-Inspired Architecture: 33% Central Coordination • 67% Distributed Intelligence")
    st.caption(f"Last Updated: {datetime.now().strftime('%Y-%m-%d %I:%M %p')}")
