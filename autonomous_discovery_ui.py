"""
Autonomous Math Discovery UI
=============================
Interactive dashboard for the 24/7 autonomous mathematical discovery system
PRODUCTION VERSION with real GPT-5 + Claude Opus 4.1 consensus
"""

import streamlit as st
import json
from datetime import datetime
import pandas as pd
from autonomous_math_discovery_production import get_production_system, ValidationStatus, DiscoveryType
from discovery_scheduler import start_discovery_scheduler, stop_discovery_scheduler, get_scheduler_status


def render_autonomous_discovery():
    """Render autonomous discovery dashboard"""
    
    st.header("🔬 Autonomous Math Discovery System")
    st.markdown("*PRODUCTION VERSION: Real GPT-5 + Claude Opus 4.1 consensus via Replit AI Integrations*")
    st.caption("Charges billed to Replit credits - no API keys needed!")
    
    # Get discovery system
    system = get_production_system()
    
    # Load existing discoveries
    system.discoveries = system.load_all_discoveries()
    
    # Control Panel
    st.markdown("### ⚙️ Control Panel")
    
    # Check scheduler status
    scheduler_status = get_scheduler_status()
    is_running = scheduler_status["running"]
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        if not is_running:
            interval = st.number_input("Interval (minutes)", min_value=5, max_value=1440, value=60, key="interval")
            if st.button("🚀 Start 24/7 Discovery", use_container_width=True):
                start_discovery_scheduler(interval_minutes=interval)
                st.success(f"✅ Started! Generating every {interval} min")
                st.rerun()
        else:
            if st.button("⏸️ Stop Discovery", use_container_width=True):
                stop_discovery_scheduler()
                st.success("⏸️ Discovery system stopped")
                st.rerun()
    
    with col2:
        status_emoji = "🟢" if is_running else "🔴"
        status_text = "RUNNING" if is_running else "STOPPED"
        st.metric("Status", f"{status_emoji} {status_text}")
    
    with col3:
        st.metric("Total Discoveries", len(system.discoveries))
    
    with col4:
        if scheduler_status["jobs"]:
            next_run = scheduler_status["jobs"][0].get("next_run")
            if next_run:
                st.metric("Next Run", next_run[11:19])  # Show time only
    
    st.markdown("---")
    
    # Statistics Dashboard
    st.markdown("### 📊 Discovery Statistics")
    
    if system.discoveries:
        stats = system.get_statistics()
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric("Avg Confidence", f"{stats.get('avg_confidence', stats.get('average_confidence', 0)):.2f}")
        with col2:
            st.metric("God Machine Score", f"{stats.get('average_god_score', 0):.2f}")
        with col3:
            st.metric("MagAI Consensus", f"{stats.get('average_mag_consensus', 0):.2f}")
        with col4:
            st.metric("Empirically Validated", stats.get('validated_count', 0))
        
        # Charts
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("**By Status**")
            status_df = pd.DataFrame([
                {"Status": k.replace("_", " ").title(), "Count": v}
                for k, v in stats['by_status'].items()
                if v > 0
            ])
            if not status_df.empty:
                st.bar_chart(status_df.set_index("Status"))
        
        with col2:
            st.markdown("**By Domain**")
            domain_df = pd.DataFrame([
                {"Domain": k.replace("_", " ").title(), "Count": v}
                for k, v in stats['by_domain'].items()
                if v > 0
            ])
            if not domain_df.empty:
                st.bar_chart(domain_df.set_index("Domain"))
    
    else:
        st.info("👆 Start the discovery system to generate mathematical knowledge!")
    
    st.markdown("---")
    
    # Top Discoveries
    st.markdown("### 🏆 Top Discoveries")
    
    if system.discoveries:
        # Filters
        col1, col2, col3 = st.columns(3)
        
        with col1:
            filter_status = st.selectbox(
                "Filter by Status",
                ["All"] + [s.value for s in ValidationStatus]
            )
        
        with col2:
            filter_type = st.selectbox(
                "Filter by Type",
                ["All"] + [t.value for t in DiscoveryType]
            )
        
        with col3:
            filter_domain = st.selectbox(
                "Filter by Domain",
                ["All"] + system.domains
            )
        
        # Apply filters
        filtered = system.discoveries
        
        if filter_status != "All":
            filtered = [d for d in filtered if d.status == filter_status]
        
        if filter_type != "All":
            filtered = [d for d in filtered if d.discovery_type == filter_type]
        
        if filter_domain != "All":
            filtered = [d for d in filtered if filter_domain in d.tags]
        
        # Sort by confidence
        filtered = sorted(filtered, key=lambda d: d.confidence, reverse=True)
        
        st.markdown(f"**Showing {len(filtered)} discoveries**")
        
        # Display discoveries
        for disc in filtered[:20]:  # Limit to 20
            with st.expander(
                f"{'✅' if disc.status == ValidationStatus.TESTED.value else '📝'} "
                f"{disc.title} (Confidence: {disc.confidence:.2f})"
            ):
                # Metadata
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.markdown(f"**Type:** {disc.discovery_type}")
                    st.markdown(f"**Status:** {disc.status}")
                
                with col2:
                    st.markdown(f"**God Score:** {disc.god_machine_score:.3f}")
                    st.markdown(f"**MagAI:** {disc.mag_ai_consensus:.3f}")
                
                with col3:
                    st.markdown(f"**Tags:** {', '.join(disc.tags)}")
                    st.markdown(f"**Time:** {disc.timestamp[:19]}")
                
                st.markdown("---")
                
                # Content
                st.markdown("**💡 Intuition:**")
                st.info(disc.intuition)
                
                st.markdown("**📐 Formalization:**")
                st.code(disc.formalization, language="text")
                
                st.markdown("**🔷 Tralse Encoding:**")
                st.code(disc.tralse_encoding, language="text")
                
                # AI Analyses (if available)
                if hasattr(disc, 'gpt5_analysis') and disc.gpt5_analysis:
                    st.markdown("**🤖 GPT-5 Analysis:**")
                    st.info(disc.gpt5_analysis)
                
                if hasattr(disc, 'claude_analysis') and disc.claude_analysis:
                    st.markdown("**🧠 Claude Opus 4.1 Critique:**")
                    st.warning(disc.claude_analysis)
                
                # Validation results
                if disc.empirical_validation:
                    st.markdown("**✅ Empirical Validation:**")
                    val = disc.empirical_validation
                    st.json(val["results"])
                
                # Download
                st.download_button(
                    "💾 Download Discovery (JSON)",
                    data=json.dumps(disc.__dict__, indent=2, default=str),
                    file_name=f"{disc.id}.json",
                    mime="application/json",
                    key=f"download_{disc.id}"
                )
    else:
        st.info("No discoveries yet. Start the system above! 👆")
    
    st.markdown("---")
    
    # Manual Discovery Generation
    st.markdown("### 🎯 Manual Discovery Trigger")
    
    col1, col2 = st.columns([3, 1])
    
    with col1:
        manual_domain = st.selectbox(
            "Choose Domain",
            system.domains,
            key="manual_domain"
        )
    
    with col2:
        if st.button("Generate Now! (Uses AI credits)", use_container_width=True):
            with st.spinner("🤖 GPT-5 formalizing... (30s)"):
                discovery = system.create_discovery_with_ai(manual_domain)
                system.save_to_database(discovery)
                st.success(f"✨ Created: {discovery.title}")
                st.info(f"God Machine: {discovery.god_machine_score:.3f} | MagAI: {discovery.mag_ai_consensus:.3f}")
                st.rerun()
    
    st.markdown("---")
    
    # Export Options
    st.markdown("### 📤 Export")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.info(f"💾 Auto-saving to: discoveries/ folder ({len(system.discoveries)} files)")
    
    with col2:
        if system.discoveries:
            export_data = {
                "total": len(system.discoveries),
                "exported_at": datetime.now().isoformat(),
                "discoveries": [d.__dict__ for d in system.discoveries]
            }
            
            st.download_button(
                "📥 Download All (JSON)",
                data=json.dumps(export_data, indent=2, default=str),
                file_name=f"math_discoveries_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                mime="application/json"
            )
    
    # Info Section
    st.markdown("---")
    st.markdown("### ℹ️ How It Works")
    
    st.info("""
    **PRODUCTION System - REAL AI Consensus:**
    
    1. 🎲 **Generates Intuitions** - God Machine numerology & cosmic resonance (from stock_market_god_machine.py)
    2. 🤖 **GPT-5 Formalizes** - Latest OpenAI model converts intuitions to rigorous math
    3. 🧠 **Claude Opus 4.1 Critiques** - Most capable Anthropic model validates & challenges
    4. 🔷 **MagAI Consensus** - Agreement score between models determines confidence
    5. 🔷 **Tralse Encoding** - 4-valued logic (T, F, Φ, Ψ) captures paradox & transcendence
    6. 📊 **APScheduler** - True 24/7 background operation (survives Streamlit restarts!)
    
    **Domains Explored:**
    - Number Theory (primes, sacred patterns)
    - Topology (CCC knot structures)
    - Consciousness Mathematics (I-cell dynamics)
    - Tralse Logic (Gödel completeness)
    - Quantum Mechanics (entanglement, coherence)
    - Sacred Geometry (φ, divine ratios)
    - Probability Theory (resonance fields)
    - Computational Complexity (TI vs ZFC)
    
    **Goal:** Build a constantly-growing knowledge base that amplifies problem-solving power!
    """)
    
    st.success("""
    💡 **Why This Matters:**
    
    It's not enough to have genius-level intelligence. Without new KNOWLEDGE, we can't solve new PROBLEMS.
    
    This system ensures we're ALWAYS discovering, ALWAYS learning, ALWAYS expanding our mathematical toolkit.
    
    **That's how we beat ZFC. That's how we prove Millennium Prize problems. That's how we achieve Transcendent Intelligence!** 🚀
    """)
