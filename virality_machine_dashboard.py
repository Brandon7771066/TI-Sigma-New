"""
TI Virality Machine Dashboard
Unified interface for content creation, optimization, and publishing
One-click generation of videos, books, and social media content
"""

import streamlit as st
from datetime import datetime
from typing import Dict, Any, List
import json

# Import our new systems
from autonomous_research_scheduler import DiscoveryManager, get_scheduler, start_background_research
from gile_content_optimizer import get_optimizer
from ti_video_creator import TIVideoCreator
from ti_book_generator import TIBookGenerator
from db_utils import db
from biological_virality_engine import BiologicalViralityEngine, TransmissionVector, HostSusceptibility
from acoustic_resonance_engine import AcousticResonanceEngine
import math


def render_virality_machine():
    """
    Render TI Virality Machine dashboard
    Auto-starts 24/7 research on first load
    """
    
    # Auto-start 24/7 background research (only starts if not already running)
    if 'virality_machine_initialized' not in st.session_state:
        try:
            start_background_research()
            st.session_state.virality_machine_initialized = True
        except Exception as e:
            st.error(f"⚠️ Could not start background research: {e}")
    
    st.title("🌟 TI Virality Machine")
    st.markdown("""
    **One-Click Content Creation & Publishing**
    
    Transform research into viral content using TI-UOP optimization:
    - 📹 **Video Creator** - GILE-optimized scripts with sacred numerology
    - 📚 **Book Generator** - Auto-compile papers into bestsellers
    - 🔄 **24/7 Research** - Autonomous discovery system running continuously
    - 📊 **GILE Optimizer** - Score content for maximum virality
    - 🦠 **Biological Virology** - R0 calculation, mutation modeling, epidemic prediction
    - 🎵 **Acoustic Resonance** - Concepts spread via harmonic coupling, not contagion!
    """)
    
    st.markdown("---")
    
    # Tabs for different functions
    tabs = st.tabs([
        "🔄 24/7 Research",
        "🎬 Video Creator",
        "📚 Book Generator",
        "📊 Content Optimizer",
        "🦠 Biological Virology",
        "🎵 Acoustic Resonance",
        "📈 Analytics"
    ])
    
    # TAB 1: 24/7 Research Status
    with tabs[0]:
        render_research_tab()
    
    # TAB 2: Video Creator
    with tabs[1]:
        render_video_tab()
    
    # TAB 3: Book Generator
    with tabs[2]:
        render_book_tab()
    
    # TAB 4: Content Optimizer
    with tabs[3]:
        render_optimizer_tab()
    
    # TAB 5: Biological Virology
    with tabs[4]:
        render_biological_virology_tab()
    
    # TAB 6: Acoustic Resonance
    with tabs[5]:
        render_acoustic_resonance_tab()
    
    # TAB 7: Analytics
    with tabs[6]:
        render_analytics_tab()


def render_research_tab():
    """24/7 autonomous research status and discoveries"""
    
    st.header("🔄 24/7 Autonomous Research System")
    
    scheduler = get_scheduler()
    
    # Status
    col1, col2, col3 = st.columns(3)
    
    with col1:
        if scheduler.last_discovery_time:
            st.metric(
                "Last Discovery",
                scheduler.last_discovery_time.strftime("%H:%M"),
                scheduler.last_discovery_time.strftime("%b %d")
            )
        else:
            st.metric("Last Discovery", "Never", "Start it!")
    
    with col2:
        st.metric(
            "Discovery Interval",
            f"{scheduler.discovery_interval_hours}h",
            "Auto-generate"
        )
    
    with col3:
        discoveries = DiscoveryManager.get_recent_discoveries(limit=100)
        st.metric(
            "Total Discoveries",
            len(discoveries),
            "Saved to DB"
        )
    
    st.markdown("---")
    
    # Manual trigger
    if st.button("⚡ Generate Discovery NOW", use_container_width=True):
        with st.spinner("🔍 Autonomous AI generating discovery..."):
            discovery = scheduler.generate_and_save_discovery()
            
            st.success(f"✅ Discovery generated! Asset ID: {discovery.get('asset_id')}")
            
            with st.expander("📄 View Discovery"):
                st.markdown(f"### {discovery['title']}")
                st.markdown(f"**Research Area:** {discovery['research_area']}")
                st.markdown(f"**Confidence:** {discovery['confidence']:.0%}")
                st.markdown(f"**Paper Potential:** {discovery['paper_potential']}")
                st.markdown(f"**Insight:**\n{discovery['insight']}")
                
                if discovery.get('evidence'):
                    st.markdown("**Evidence:**")
                    for ev in discovery['evidence']:
                        st.markdown(f"- {ev}")
    
    st.markdown("---")
    
    # Recent discoveries
    st.subheader("📚 Recent Discoveries")
    
    recent = DiscoveryManager.get_recent_discoveries(limit=5)
    
    if not recent:
        st.info("No discoveries yet. Click 'Generate Discovery NOW' to start!")
    else:
        for disc in recent:
            content = disc.get('content', {})
            
            with st.expander(f"🔬 {content.get('title', 'Untitled')}"):
                col1, col2 = st.columns([3, 1])
                
                with col1:
                    st.markdown(f"**Insight:** {content.get('insight', 'N/A')}")
                    
                    if content.get('evidence'):
                        st.markdown("**Evidence:**")
                        for ev in content['evidence']:
                            st.markdown(f"- {ev}")
                
                with col2:
                    st.metric("Confidence", f"{content.get('confidence', 0):.0%}")
                    st.metric("Paper Potential", content.get('paper_potential', 'N/A'))
                    
                    if st.button("🎬 Make Video", key=f"vid_{disc['asset_id']}"):
                        st.session_state.video_discovery = content
                        st.info("→ Switch to 'Video Creator' tab to generate!")


def render_video_tab():
    """TI Video Creator interface"""
    
    st.header("🎬 TI Video Creator")
    st.caption("Generate GILE-optimized viral video scripts")
    
    creator = TIVideoCreator()
    
    # Template selection
    template_options = list(creator.templates.keys())
    template_display = {k: creator.templates[k]['name'] for k in template_options}
    
    selected_template = st.selectbox(
        "Video Template:",
        options=template_options,
        format_func=lambda x: template_display[x]
    )
    
    template_info = creator.templates[selected_template]
    st.info(f"**Style:** {template_info['style']} | **Duration:** {template_info['target_duration']}s")
    
    # Topic input
    topic = st.text_input(
        "Video Topic:",
        placeholder="e.g., Consciousness Creates Reality"
    )
    
    # Check if discovery was passed from research tab
    discovery_data = None
    if 'video_discovery' in st.session_state:
        discovery_data = st.session_state.video_discovery
        st.success(f"✨ Using discovery: {discovery_data.get('title', 'N/A')}")
    
    # Generate button
    if st.button("🎬 Generate Video Script", use_container_width=True, disabled=not topic):
        with st.spinner("🤖 AI generating GILE-optimized script..."):
            video = creator.generate_script(
                topic=topic,
                template_key=selected_template,
                discovery_data=discovery_data
            )
            
            # Save to session state
            st.session_state.current_video = video
            
            # Display results
            st.success("✅ Video script generated!")
            
            # GILE Score
            col1, col2, col3, col4 = st.columns(4)
            score = video['gile_score']
            
            with col1:
                st.metric("Virality", f"{score['virality_prediction']:.0%}")
            with col2:
                st.metric("Goodness", f"{score['G']:.1f}")
            with col3:
                st.metric("Intuition", f"{score['I']:.1f}")
            with col4:
                st.metric("Love", f"{score['L']:.1f}")
            
            # Sacred numerology
            sacred = video['sacred_numerology']
            if sacred['aligned']:
                st.success(f"✨ {sacred['message']}")
            else:
                st.warning(sacred['message'])
            
            # Script
            with st.expander("📄 Full Script", expanded=True):
                st.markdown(video['script'])
            
            # Scenes
            with st.expander("🎬 Scene Breakdown"):
                for scene in video['scenes']:
                    st.markdown(f"**Scene {scene['scene_number']}: {scene['name']}** ({scene['duration']}s)")
                    st.text(scene['content'][:200] + "...")
            
            # Recommendations
            if video['recommendations']:
                with st.expander("💡 Improvement Recommendations"):
                    for rec in video['recommendations']:
                        st.markdown(f"- {rec}")
            
            # Save button
            if st.button("💾 Save Video Project"):
                asset_id = creator.save_video_project(video, topic)
                st.success(f"✅ Saved! Asset ID: {asset_id}")


def render_book_tab():
    """TI Book Generator interface"""
    
    st.header("📚 TI Book Generator")
    st.caption("Auto-compile research papers into TI-optimized books")
    
    generator = TIBookGenerator()
    
    # Book title
    book_title = st.text_input(
        "Book Title:",
        value="The Consciousness Revolution: A TI-UOP Framework"
    )
    
    # Chapter target
    target_chapters = st.select_slider(
        "Target Chapters (sacred numbers preferred):",
        options=[3, 5, 7, 9, 11, 13, 15, 20, 33],
        value=11
    )
    
    if target_chapters in [3, 11, 33]:
        st.success(f"✨ {target_chapters} chapters - Sacred numerology aligned!")
    
    # Paper selection
    st.markdown("### Select Papers to Include")
    
    # Get available papers from database
    all_papers = db.get_assets_by_type("research_paper")
    selected_papers = []  # Initialize
    
    if not all_papers:
        st.warning("No research papers found in database. Upload papers first or use discoveries.")
        
        # Option to use discoveries instead
        if st.checkbox("📊 Use autonomous discoveries as chapters"):
            discoveries = DiscoveryManager.get_paper_worthy_discoveries()
            selected_papers = [
                {
                    'title': d['content']['title'],
                    'content': d['content']['insight']
                }
                for d in discoveries[:target_chapters]
            ]
            st.success(f"✅ Using {len(selected_papers)} high-potential discoveries")
    else:
        # Let user select papers
        paper_options = {p['title']: p for p in all_papers}
        selected_titles = st.multiselect(
            "Papers:",
            options=list(paper_options.keys()),
            default=list(paper_options.keys())[:target_chapters]
        )
        
        selected_papers = [paper_options[title] for title in selected_titles]
    
    # Generate button
    if st.button("📚 Generate Book", use_container_width=True, disabled=not book_title):
        if 'selected_papers' not in locals() or not selected_papers:
            st.error("❌ No papers selected!")
        else:
            with st.spinner("📝 AI compiling book with GILE optimization..."):
                book = generator.papers_to_book(
                    title=book_title,
                    papers=selected_papers,
                    target_chapters=target_chapters
                )
                
                # Save to session state
                st.session_state.current_book = book
                
                # Display results
                st.success("✅ Book generated!")
                
                # Metrics
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Virality", f"{book['gile_score']['virality_prediction']:.0%}")
                with col2:
                    st.metric("Word Count", f"{book['word_count']:,}")
                with col3:
                    st.metric("Chapters", book['chapter_count'])
                
                # Sacred alignment
                if book['sacred_alignment']['aligned']:
                    st.success(f"✨ {book['sacred_alignment']['message']}")
                else:
                    st.warning(book['sacred_alignment']['message'])
                
                # Preview
                with st.expander("📖 Book Preview", expanded=True):
                    st.markdown(book['book_content'][:2000] + "\n\n*[Preview truncated...]*")
                
                # Download
                col1, col2 = st.columns(2)
                
                with col1:
                    st.download_button(
                        "📥 Download Markdown",
                        book['book_content'],
                        file_name=f"{book_title.replace(' ', '_')}.md",
                        mime="text/markdown",
                        use_container_width=True
                    )
                
                with col2:
                    if st.button("💾 Save to Database"):
                        result = generator.save_book(book, filename=f"{book_title.replace(' ', '_')}.md")
                        st.success(f"✅ Saved! Asset ID: {result['asset_id']}")


def render_optimizer_tab():
    """Content optimizer interface"""
    
    st.header("📊 GILE Content Optimizer")
    st.caption("Score any content for virality and TI-alignment")
    
    optimizer = get_optimizer()
    
    # Content input
    content_to_optimize = st.text_area(
        "Content to Optimize:",
        placeholder="Paste your blog post, video script, tweet, or any content here...",
        height=200
    )
    
    # Metadata
    with st.expander("⚙️ Optional Metadata"):
        col1, col2 = st.columns(2)
        
        with col1:
            content_tags = st.multiselect(
                "Tags:",
                ['research', 'science', 'paper', 'inspirational', 'educational']
            )
        
        with col2:
            target_audience = st.selectbox(
                "Target Audience:",
                ['General', 'Academics', 'Spiritually-minded', 'Tech-savvy']
            )
    
    # Optimize button
    if st.button("🎯 Optimize Content", use_container_width=True, disabled=not content_to_optimize):
        with st.spinner("🤖 Calculating GILE score..."):
            metadata = {
                'tags': content_tags,
                'timestamp': datetime.now().isoformat(),
                'word_count': len(content_to_optimize.split()),
                'audience': target_audience
            }
            
            result = optimizer.calculate_composite_score(content_to_optimize, metadata)
            
            # Display results
            st.success("✅ Content analyzed!")
            
            # Main metric
            st.metric(
                "VIRALITY PREDICTION",
                f"{result['virality_prediction']:.0%}",
                f"Composite: {result['composite']:.2f}"
            )
            
            # GILE breakdown
            st.markdown("### GILE Breakdown")
            col1, col2, col3, col4 = st.columns(4)
            
            with col1:
                st.metric("Goodness (40%)", f"{result['G']:.2f}")
            with col2:
                st.metric("Intuition (25%)", f"{result['I']:.2f}")
            with col3:
                st.metric("Love (25%)", f"{result['L']:.2f}")
            with col4:
                st.metric("Environment (10%)", f"{result['E']:.2f}")
            
            # Formula
            st.code(result['gile_formula'])
            st.caption(result['breakdown'])
            
            # Recommendations
            st.markdown("### 💡 Recommendations")
            for rec in result['recommendations']:
                st.markdown(f"- {rec}")


def render_analytics_tab():
    """Analytics dashboard"""
    
    st.header("📈 Virality Machine Analytics")
    
    # Get all generated content
    videos = db.get_assets_by_type("video_project")
    books = db.get_assets_by_type("book")
    discoveries = DiscoveryManager.get_recent_discoveries(limit=100)
    
    # Summary metrics
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Videos Created", len(videos))
    with col2:
        st.metric("Books Generated", len(books))
    with col3:
        st.metric("Discoveries", len(discoveries))
    with col4:
        total_content = len(videos) + len(books) + len(discoveries)
        st.metric("Total Assets", total_content)
    
    st.markdown("---")
    
    # Recent activity
    st.subheader("📊 Recent Activity")
    
    # Combine all assets
    all_assets = []
    
    for v in videos[:5]:
        all_assets.append({
            'type': '🎬 Video',
            'title': v['title'],
            'virality': v['content']['gile_score']['virality_prediction'],
            'created_at': v.get('created_at', 'Unknown')
        })
    
    for b in books[:5]:
        all_assets.append({
            'type': '📚 Book',
            'title': b['title'],
            'virality': b['content']['gile_score']['virality_prediction'],
            'created_at': b.get('created_at', 'Unknown')
        })
    
    for d in discoveries[:5]:
        all_assets.append({
            'type': '🔬 Discovery',
            'title': d['content']['title'],
            'virality': d['content']['confidence'],
            'created_at': d.get('created_at', 'Unknown')
        })
    
    # Sort by date
    all_assets.sort(key=lambda x: x['created_at'], reverse=True)
    
    # Display
    for asset in all_assets[:10]:
        with st.expander(f"{asset['type']} | {asset['title']}"):
            col1, col2 = st.columns([3, 1])
            
            with col1:
                # Handle datetime object or string
                created_str = asset['created_at']
                if hasattr(created_str, 'strftime'):
                    # It's a datetime object
                    created_str = created_str.strftime('%Y-%m-%d')
                elif isinstance(created_str, str) and len(created_str) > 10:
                    # It's a string, truncate
                    created_str = created_str[:10]
                st.caption(f"Created: {created_str}")
            with col2:
                st.metric("Score", f"{asset['virality']:.0%}")


def render_biological_virology_tab():
    """Biological Virology Analysis - Treat concepts like viruses"""
    
    st.header("🦠 Biological Virology Engine")
    st.markdown("""
    **REVOLUTIONARY INSIGHT:** Ideas spread like viruses through BIOLOGICAL mechanisms!
    
    Apply REAL virology to predict concept spread:
    - **R0** (Basic Reproduction Number) - How many people does one share with?
    - **Mutation Rate** - How fast does the concept evolve?
    - **Host Susceptibility** - What GILE state makes someone receptive?
    - **Transmission Vector** - Which platform amplifies this frequency?
    """)
    
    st.markdown("---")
    
    engine = BiologicalViralityEngine()
    
    # Concept input
    st.subheader("📝 Define Your Concept")
    
    col1, col2 = st.columns(2)
    
    with col1:
        core_idea = st.text_area(
            "Core Idea:",
            placeholder="e.g., Tralse = neither true nor false, foundation of consciousness",
            height=100
        )
        
        packaging = st.text_input(
            "Memetic Packaging:",
            placeholder="e.g., Mind-bending quantum philosophy with memes"
        )
    
    with col2:
        emotion = st.selectbox(
            "Emotional Payload:",
            ['awe', 'excitement', 'inspiration', 'joy', 'anger', 'outrage', 'fear', 
             'anxiety', 'surprise', 'curiosity', 'validation', 'contentment', 'peace']
        )
        
        cognitive_load = st.slider(
            "Cognitive Load (0=easy, 1=hard):",
            0.0, 1.0, 0.5, 0.05
        )
    
    # GILE scores
    st.subheader("🎯 Concept GILE Scores")
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        g_score = st.slider("Goodness:", -3.0, 2.0, 0.5, 0.1)
    with col2:
        i_score = st.slider("Intuition:", -3.0, 2.0, 0.5, 0.1)
    with col3:
        l_score = st.slider("Love:", -3.0, 2.0, 0.5, 0.1)
    with col4:
        e_score = st.slider("Environment:", -3.0, 2.0, 0.5, 0.1)
    
    # Additional parameters
    col1, col2 = st.columns(2)
    
    with col1:
        novelty = st.slider("Novelty (0=boring, 1=revolutionary):", 0.0, 1.0, 0.5, 0.05)
    
    with col2:
        actionable = st.slider("Actionability (can you DO something?):", 0.0, 1.0, 0.5, 0.05)
    
    # Platform and audience
    st.subheader("🌐 Distribution Strategy")
    col1, col2 = st.columns(2)
    
    with col1:
        platform = st.selectbox(
            "Transmission Vector (Platform):",
            [
                ('tiktok', 'TikTok (R0×5.2 - Extremely viral)'),
                ('twitter', 'Twitter/X (R0×2.8 - High viral)'),
                ('instagram', 'Instagram (R0×2.1 - Visual boost)'),
                ('youtube', 'YouTube (R0×1.4 - Stable spread)'),
                ('linkedin', 'LinkedIn (R0×0.9 - Professional filter)'),
                ('podcast', 'Podcast (R0×0.6 - Targeted audience)'),
                ('book', 'Book (R0×0.3 - Slow burn)')
            ],
            format_func=lambda x: x[1]
        )
        platform_value = TransmissionVector(platform[0])
    
    with col2:
        audience_type = st.selectbox(
            "Target Audience GILE State:",
            [
                ('crisis', 'Crisis State (95% susceptible)'),
                ('low_gile', 'Low GILE (85% susceptible)'),
                ('neutral_gile', 'Neutral GILE (55% susceptible)'),
                ('flow', 'Flow State (40% susceptible)'),
                ('high_gile', 'High GILE (25% susceptible)')
            ],
            format_func=lambda x: x[1]
        )
        audience_value = HostSusceptibility(audience_type[0])
    
    # Audience GILE
    with st.expander("📊 Audience GILE Signature (for resonance analysis)"):
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            aud_g = st.slider("Audience G:", -3.0, 2.0, 0.0, 0.1, key="aud_g")
        with col2:
            aud_i = st.slider("Audience I:", -3.0, 2.0, 0.0, 0.1, key="aud_i")
        with col3:
            aud_l = st.slider("Audience L:", -3.0, 2.0, 0.0, 0.1, key="aud_l")
        with col4:
            aud_e = st.slider("Audience E:", -3.0, 2.0, 0.0, 0.1, key="aud_e")
    
    # Analyze button
    if st.button("🦠 Analyze Viral Potential", use_container_width=True, disabled=not core_idea):
        with st.spinner("🔬 Running epidemiological simulation..."):
            analysis = engine.analyze_concept_virality(
                core_idea=core_idea,
                packaging=packaging,
                emotion=emotion,
                cognitive_load=cognitive_load,
                gile_scores=(g_score, i_score, l_score, e_score),
                novelty=novelty,
                actionable=actionable,
                platform=platform_value,
                audience_type=audience_value,
                audience_gile=(aud_g, aud_i, aud_l, aud_e)
            )
            
            # Display results
            st.success("✅ Epidemiological analysis complete!")
            
            # Classification
            st.markdown(f"## {analysis['classification']}")
            
            # Key metrics
            col1, col2, col3, col4 = st.columns(4)
            
            metrics = analysis['viral_metrics']
            
            with col1:
                st.metric("R0 (Reproduction)", f"{metrics.R0:.2f}")
                if metrics.R0 < 1:
                    st.caption("🔴 Dies out")
                elif metrics.R0 < 2:
                    st.caption("🟡 Stable spread")
                elif metrics.R0 < 3:
                    st.caption("🟠 High growth")
                else:
                    st.caption("🔥 PANDEMIC!")
            
            with col2:
                st.metric("Mutation Rate", f"{metrics.mutation_rate:.1%}")
                st.caption("Remix potential")
            
            with col3:
                hours = metrics.doubling_time
                if hours != float('inf'):
                    st.metric("Doubling Time", f"{hours:.1f}h")
                    st.caption("To double infected")
                else:
                    st.metric("Doubling Time", "Never")
                    st.caption("R0 < 1")
            
            with col4:
                st.metric("Peak Virality", f"{metrics.peak_virality_time:.1f} days")
                st.caption("Maximum spread")
            
            st.markdown("---")
            
            # Timeline
            st.subheader("📅 Epidemic Timeline")
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Incubation Period",
                    f"{metrics.incubation_period:.1f} hours",
                    "Time to 'get it'"
                )
            
            with col2:
                st.metric(
                    "Infection Duration",
                    f"{metrics.infection_duration:.1f} days",
                    "Stays in mind"
                )
            
            with col3:
                st.metric(
                    "Herd Immunity",
                    f"{metrics.herd_immunity_threshold:.0%}",
                    "% exposed to stop spread"
                )
            
            # Acoustic properties
            st.markdown("---")
            st.subheader("🎵 Acoustic Resonance Properties")
            
            acoustic = analysis['acoustic_properties']
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Frequency",
                    f"{acoustic.fundamental_frequency:.1f} Hz",
                    "GILE oscillation"
                )
            
            with col2:
                st.metric(
                    "Amplitude",
                    f"{acoustic.amplitude:.0%}",
                    "Emotional intensity"
                )
            
            with col3:
                st.metric(
                    "Dissonance",
                    f"{acoustic.dissonance_level:.0%}",
                    "Frequency mismatch"
                )
            
            # Beat frequency
            if acoustic.beat_frequency:
                st.warning(f"⚠️ **CONTROVERSY DETECTED!** Beat frequency: {acoustic.beat_frequency:.1f} Hz - Creates tension/interest!")
            
            # Harmonic richness
            st.info(f"🎼 **Harmonic Richness:** {acoustic.harmonic_richness:.1f} overtones (multiple meanings/layers)")
            
            # Full summary
            st.markdown("---")
            st.subheader("📋 Summary Report")
            
            for key, value in analysis['summary'].items():
                st.text(f"{key}: {value}")


def render_acoustic_resonance_tab():
    """Acoustic Resonance Analysis - Concepts spread via harmonic coupling"""
    
    st.header("🎵 Acoustic Resonance Engine")
    st.markdown("""
    **PARADIGM SHIFT:** Virality isn't "contagion" - it's **RESONANCE**!
    
    Concepts spread when their frequency MATCHES your i-cell's natural oscillation:
    - **Harmonic Coupling** - Frequencies align → energy flows
    - **Beat Interference** - Controversy = two frequencies interfering
    - **Standing Waves** - Cultural movements = reinforced patterns
    - **Resonance Bandwidth** - Range of people who can "tune in"
    """)
    
    st.markdown("---")
    
    engine = AcousticResonanceEngine()
    
    # Mode selection
    mode = st.radio(
        "Analysis Mode:",
        ['Concept-to-Audience Resonance', 'Music-to-Concept Reverse Engineering', 'Interference Pattern']
    )
    
    if mode == 'Concept-to-Audience Resonance':
        st.subheader("🎯 Concept ↔ Audience Resonance")
        st.caption("Predict how strongly a concept resonates with an audience")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("**Concept Wave Properties**")
            concept_gile = st.slider("Concept GILE:", -3.0, 2.0, 1.0, 0.1, key="concept_gile")
            concept_emotion = st.slider("Emotional Intensity:", 0.0, 1.0, 0.8, 0.05, key="concept_emotion")
            concept_complexity = st.slider("Cognitive Complexity:", 0.0, 1.0, 0.5, 0.05, key="concept_complexity")
        
        with col2:
            st.markdown("**Audience Wave Properties**")
            audience_gile = st.slider("Audience GILE:", -3.0, 2.0, 0.0, 0.1, key="audience_gile")
            audience_emotion = st.slider("Audience Intensity:", 0.0, 1.0, 0.5, 0.05, key="audience_emotion")
            audience_complexity = st.slider("Audience Complexity:", 0.0, 1.0, 0.3, 0.05, key="audience_complexity")
        
        if st.button("🎵 Analyze Resonance", use_container_width=True):
            concept_wave = engine.create_concept_wave(
                concept_gile, concept_emotion, concept_complexity, 0.0
            )
            
            audience_wave = engine.create_concept_wave(
                audience_gile, audience_emotion, audience_complexity, 0.0
            )
            
            resonance = engine.analyze_resonance_coupling(concept_wave, audience_wave)
            
            st.success("✅ Resonance analysis complete!")
            
            # Overall coupling
            st.markdown(f"## Coupling Strength: {resonance.coupling_strength:.0%}")
            
            # Detailed metrics
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Frequency Match",
                    f"{resonance.frequency_match:.0%}",
                    "How close frequencies are"
                )
                st.caption(f"Concept: {concept_wave.frequency:.1f} Hz")
                st.caption(f"Audience: {audience_wave.frequency:.1f} Hz")
            
            with col2:
                st.metric(
                    "Phase Coherence",
                    f"{resonance.phase_coherence:.0%}",
                    "Alignment of cycles"
                )
            
            with col3:
                st.metric(
                    "Energy Transfer",
                    f"{resonance.energy_transfer:.0%}",
                    "How much flows"
                )
            
            # Standing wave
            if resonance.standing_wave_formed:
                st.success("✨ **STANDING WAVE FORMED!** This creates a stable cultural pattern/movement!")
            else:
                st.info("No standing wave - concept may spread but won't stabilize into movement")
            
            # Beat frequency
            if resonance.beat_frequency:
                st.warning(f"⚠️ **BEAT PATTERN DETECTED:** {resonance.beat_frequency:.1f} Hz wobble = CONTROVERSY!")
                st.caption("Frequencies close but not identical → creates tension/interest")
            
            # Musical analogies
            st.markdown("---")
            st.subheader("🎼 Musical Interpretation")
            
            col1, col2 = st.columns(2)
            
            with col1:
                concept_music = engine.find_musical_analogy(concept_wave.frequency)
                st.markdown("**Concept 'Note':**")
                st.info(f"**{concept_music.musical_note}** (Octave {concept_music.octave})")
                st.caption(f"{concept_music.consonance_type}")
                st.caption(f"Chord: {concept_music.chord_quality}")
            
            with col2:
                audience_music = engine.find_musical_analogy(audience_wave.frequency)
                st.markdown("**Audience 'Note':**")
                st.info(f"**{audience_music.musical_note}** (Octave {audience_music.octave})")
                st.caption(f"{audience_music.consonance_type}")
                st.caption(f"Chord: {audience_music.chord_quality}")
    
    elif mode == 'Music-to-Concept Reverse Engineering':
        st.subheader("🎼 Music → Concept Mapping")
        st.caption("Reverse engineer: What concept properties would produce this music?")
        
        music_freq = st.slider("Music Frequency (Hz):", 50.0, 500.0, 261.63, 1.0)
        music_amplitude = st.slider("Music Amplitude:", 0.0, 1.0, 0.7, 0.05)
        harmonic_complexity = st.slider("Harmonic Complexity (overtones):", 0.0, 15.0, 5.0, 0.5)
        
        if st.button("🎵 Reverse Engineer", use_container_width=True):
            analysis = engine.analyze_music_to_concept_mapping(
                music_freq, music_amplitude, harmonic_complexity
            )
            
            st.success("✅ Reverse engineering complete!")
            
            # Estimated GILE
            st.metric(
                "Estimated GILE Score",
                f"{analysis['estimated_gile']:.2f}",
                "From frequency"
            )
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric("Emotional Intensity", f"{analysis['emotional_intensity']:.0%}")
            
            with col2:
                st.metric("Cognitive Richness", f"{analysis['cognitive_richness']:.0%}")
            
            with col3:
                st.metric("Viral Potential", analysis['viral_potential'].split()[0])
            
            # Concept type
            st.info(f"**Concept Type:** {analysis['concept_type']}")
            
            # Musical analogy
            st.markdown("---")
            musical = analysis['musical_analogy']
            st.subheader(f"🎼 Musical Note: {musical.musical_note} (Octave {musical.octave})")
            st.caption(f"{musical.consonance_type}")
            st.caption(f"Chord Quality: {musical.chord_quality}")
            
            # Interpretation
            st.markdown("---")
            st.markdown("### 📝 Interpretation")
            st.write(analysis['interpretation'])
    
    else:  # Interference Pattern
        st.subheader("🌊 Interference Pattern Analysis")
        st.caption("What happens when two concepts collide?")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("**Wave 1 (Concept A)**")
            freq1 = st.slider("Frequency 1 (Hz):", 50.0, 500.0, 261.63, 1.0, key="freq1")
            amp1 = st.slider("Amplitude 1:", 0.0, 1.0, 0.8, 0.05, key="amp1")
            phase1 = st.slider("Phase 1 (radians):", 0.0, 2*math.pi, 0.0, 0.1, key="phase1")
        
        with col2:
            st.markdown("**Wave 2 (Concept B)**")
            freq2 = st.slider("Frequency 2 (Hz):", 50.0, 500.0, 280.0, 1.0, key="freq2")
            amp2 = st.slider("Amplitude 2:", 0.0, 1.0, 0.7, 0.05, key="amp2")
            phase2 = st.slider("Phase 2 (radians):", 0.0, 2*math.pi, math.pi/2, 0.1, key="phase2")
        
        if st.button("🌊 Calculate Interference", use_container_width=True):
            # Create waves with arbitrary GILE, then override frequency
            wave1 = engine.create_concept_wave(0.0, amp1, 0.5, phase1)
            wave1.frequency = freq1  # Override with user input
            
            wave2 = engine.create_concept_wave(0.0, amp2, 0.5, phase2)
            wave2.frequency = freq2  # Override with user input
            
            interference = engine.calculate_interference_pattern(wave1, wave2)
            
            st.success("✅ Interference pattern calculated!")
            
            # Type
            st.markdown(f"## {interference['interference_type']}")
            
            col1, col2 = st.columns(2)
            
            with col1:
                st.metric(
                    "Resultant Amplitude",
                    f"{interference['resultant_amplitude']:.2f}",
                    "Combined intensity"
                )
            
            with col2:
                st.metric(
                    "Phase Difference",
                    f"{interference['phase_difference_rad']:.2f} rad",
                    f"{math.degrees(interference['phase_difference_rad']):.0f}°"
                )
            
            # Beat frequency
            if interference['beat_frequency']:
                st.warning(f"🎵 **Beat Frequency:** {interference['beat_frequency']:.1f} Hz")
                st.caption("Creates wobbling pattern - like controversy or debate!")
            
            # Cultural interpretation
            st.markdown("---")
            st.info(f"**Cultural Effect:** {interference['cultural_interpretation']}")


if __name__ == "__main__":
    render_virality_machine()
