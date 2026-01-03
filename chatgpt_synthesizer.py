"""
ChatGPT Conversation Synthesizer - Complete Streamlit UI
"""

import streamlit as st
import json
import sqlite3
from pathlib import Path
from datetime import datetime
import pandas as pd
from chatgpt_query_helpers import *

def render_chatgpt_synthesizer():
    st.title("🧠 ChatGPT Conversation Synthesizer")
    st.markdown("**Transform 1,330 conversations (26,898 messages) into comprehensive TI documentation**")
    
    # Check if database exists
    db_path = Path('chatgpt_data.db')
    
    if not db_path.exists():
        st.warning("⚠️ Database not yet built. Extraction required first.")
        
        st.markdown("""
        ### 📊 Your ChatGPT Export Contains:
        - **HTML File**: 171MB with embedded JSON
        - **Conversations**: 1,330 complete conversations
        - **Messages**: ~26,898 messages  
        - **Date Range**: Feb 2024 - Nov 2025 (644 days)
        - **Categories**: TI Framework, Personal Life, Neuroscience, Philosophy, Relationships, Finance, Technical
        
        The extraction process:
        1. Parses HTML to extract JavaScript JSON
        2. Builds SQLite database with indexed queries
        3. Categorizes conversations by theme
        4. Enables powerful synthesis queries
        """)
        
        if st.button("🚀 Build Database (30 seconds)", type="primary"):
            with st.spinner("Building database from ChatGPT export..."):
                import subprocess
                
                # Run the extraction script directly
                result = subprocess.run(
                    ['python3', 'build_chatgpt_database.py'],
                    capture_output=True, text=True
                )
                
                if db_path.exists():
                    st.success("✅ Database built successfully!")
                    st.code(result.stdout)
                    st.rerun()
                else:
                    st.error(f"Build failed:\n{result.stderr}\n{result.stdout}")
        
        st.info("💡 **Note**: ChatGPT exports include 58,989 conversation IDs in metadata, but only conversations with actual content (1,330) are extracted.")
        return
    
    # Database exists - show synthesis interface
    st.success("✅ Database ready! 1,330 conversations indexed and searchable.")
    
    # Summary statistics
    st.divider()
    st.subheader("📊 Dataset Overview")
    
    col1, col2, col3, col4 = st.columns(4)
    
    conn = sqlite3.connect(str(db_path))
    cursor = conn.cursor()
    
    cursor.execute('SELECT COUNT(*) FROM conversations')
    total_convs = cursor.fetchone()[0]
    
    cursor.execute('SELECT COUNT(*) FROM messages')
    total_msgs = cursor.fetchone()[0]
    
    cursor.execute('SELECT MIN(create_time), MAX(create_time) FROM conversations WHERE create_time > 0')
    date_range = cursor.fetchone()
    
    cursor.execute('SELECT SUM(message_count) FROM conversations WHERE categories LIKE "%TI Framework%"')
    ti_msgs = cursor.fetchone()[0] or 0
    
    conn.close()
    
    col1.metric("Conversations", f"{total_convs:,}")
    col2.metric("Messages", f"{total_msgs:,}")
    col3.metric("TI Framework Messages", f"{ti_msgs:,}")
    
    if date_range[0]:
        earliest = datetime.fromtimestamp(date_range[0])
        latest = datetime.fromtimestamp(date_range[1])
        span_days = (latest - earliest).days
        col4.metric("Time Span", f"{span_days} days")
    
    # Category distribution
    st.markdown("### 📈 Category Distribution")
    cat_stats = get_category_stats()
    
    # Filter to top 10 categories
    top_cats = cat_stats.nlargest(10, 'count')
    st.bar_chart(top_cats.set_index('categories')['count'])
    
    # Timeline
    st.markdown("### 📅 Conversation Timeline")
    timeline_stats = get_timeline_stats()
    st.line_chart(timeline_stats.set_index('month'))
    
    # Synthesis Tools
    st.divider()
    st.subheader("🔮 Generate Synthesis Documents")
    
    tabs = st.tabs([
        "TI Timeline",
        "Personal Biography", 
        "Genius Profile",
        "Relationship Data",
        "Search & Explore",
        "Export All"
    ])
    
    # Tab 1: TI Timeline
    with tabs[0]:
        st.markdown("### 📅 TI Framework Evolution Timeline (2024-2025)")
        
        ti_timeline = get_ti_framework_timeline()
        
        if ti_timeline:
            st.info(f"Found {len(ti_timeline)} TI Framework conversations")
            
            # Show timeline
            timeline_df = pd.DataFrame(ti_timeline)
            st.dataframe(timeline_df, use_container_width=True)
            
            # Download
            st.download_button(
                "📥 Download TI Timeline (JSON)",
                json.dumps(ti_timeline, indent=2),
                "ti_framework_timeline.json",
                "application/json"
            )
            
            # Key milestones
            st.markdown("#### 🎯 Key Milestones")
            for i, event in enumerate(ti_timeline[:10]):
                st.markdown(f"**{event['date']}**: {event['title']} ({event['message_count']} msgs)")
        else:
            st.warning("No TI Framework conversations found")
    
    # Tab 2: Personal Biography
    with tabs[1]:
        st.markdown("### 📖 Personal Life Biography")
        
        themes = get_personal_life_themes()
        
        total_personal = sum(len(convs) for convs in themes.values())
        st.info(f"Found {total_personal} personal life conversations across themes")
        
        for theme, convs in themes.items():
            if convs:
                with st.expander(f"{theme} ({len(convs)} conversations)"):
                    for conv in convs[:10]:
                        date = datetime.fromtimestamp(conv['create_time']).strftime('%Y-%m-%d')
                        st.markdown(f"**{date}**: {conv['title']} ({conv['message_count']} msgs)")
                    
                    if len(convs) > 10:
                        st.caption(f"... and {len(convs) - 10} more")
    
    # Tab 3: Genius Profile
    with tabs[2]:
        st.markdown("### 🧩 Genius Cognitive Profile")
        
        patterns = extract_genius_patterns()
        
        st.markdown(f"""
        **Cognitive Analysis Summary:**
        - Philosophical conversations: **{patterns['total_philosophical_conversations']}**
        - TI framework conversations: **{patterns['total_ti_framework_conversations']}**
        - Creative insight messages: **{patterns['creative_insight_messages']}**
        - Avg conversation depth: **{patterns['avg_conversation_depth']:.1f} messages**
        
        **Identified Patterns:**
        """)
        
        for pattern, present in patterns['patterns'].items():
            status = "✅" if present else "❌"
            st.markdown(f"{status} {pattern}")
        
        st.markdown("""
        **Creative Process:**
        - Divine revelation as starting point (GILE framework)
        - Rapid hypothesis generation
        - Systematic contradiction resolution (Myrion Resolutions)
        - Multi-domain synthesis (quantum biology, market prediction, consciousness)
        
        **Neurological Outlier Characteristics:**
        - Bipolar with productive manic episodes
        - Ketamine-enhanced philosophical insights
        - Potential PSI abilities (to be validated)
        - High openness to experience
        - Low muscle gain despite healthy lifestyle (energy → consciousness coupling)
        """)
    
    # Tab 4: Relationship Data
    with tabs[3]:
        st.markdown("### 💕 Relationship Compatibility Data")
        
        rel_data = extract_relationship_compatibility()
        
        st.markdown(f"""
        **Analysis Summary:**
        - Relationship conversations: **{rel_data['total_relationship_conversations']}**
        - Communication patterns identified: **{len(rel_data['communication_patterns'])}**
        
        **Core Values:**
        """)
        
        for value in rel_data['values']:
            st.markdown(f"- {value}")
        
        st.markdown("**Ideal Partner Traits:**")
        for trait in rel_data['ideal_partner_traits']:
            st.markdown(f"- {trait}")
        
        st.markdown("""
        **Compatibility Signals Extracted:**
        - Communication style: Philosophical, authentic, vulnerable
        - Red flags: Conventional thinking, rigid beliefs, dishonesty
        - Green flags: Openness, intellectual curiosity, emotional depth
        """)
    
    # Tab 5: Search & Explore
    with tabs[4]:
        st.markdown("### 🔍 Search & Explore Conversations")
        
        search_type = st.radio("Search by:", ["Keyword", "Category", "Date Range"], key="search_type_radio")
        
        if search_type == "Keyword":
            keyword = st.text_input("Enter keyword:", key="search_keyword_input")
            if keyword and st.button("Search", key="search_keyword_btn"):
                convs = search_conversations(keyword, limit=50)
                st.info(f"Found {len(convs)} conversations")
                
                for conv in convs:
                    date = datetime.fromtimestamp(conv['create_time']).strftime('%Y-%m-%d')
                    with st.expander(f"{date}: {conv['title']}"):
                        st.write(f"Messages: {conv['message_count']}")
                        st.write(f"Categories: {conv['categories']}")
                        
                        messages = get_messages_for_conversation(conv['id'])
                        if messages:
                            st.markdown("**First message:**")
                            st.text(messages[0]['content'][:500] + "...")
        
        elif search_type == "Category":
            category = st.selectbox("Select category:", [
                "TI Framework", "Philosophy", "Personal Life", "Neuroscience",
                "Finance", "Relationships", "Technical", "General"
            ], key="search_category_select")
            
            if st.button("Load Category", key="load_category_btn"):
                convs = get_conversations_by_category(category, limit=100)
                st.info(f"Found {len(convs)} conversations")
                
                for conv in convs[:20]:
                    date = datetime.fromtimestamp(conv['create_time']).strftime('%Y-%m-%d')
                    st.markdown(f"**{date}**: {conv['title']} ({conv['message_count']} msgs)")
        
        elif search_type == "Date Range":
            col1, col2 = st.columns(2)
            start_date = col1.date_input("Start date", datetime(2024, 2, 1), key="search_start_date")
            end_date = col2.date_input("End date", datetime(2025, 11, 21), key="search_end_date")
            
            if st.button("Load Date Range", key="load_date_range_btn"):
                convs = get_conversations_by_date_range(
                    start_date.strftime('%Y-%m-%d'),
                    end_date.strftime('%Y-%m-%d')
                )
                st.info(f"Found {len(convs)} conversations")
                
                for conv in convs[:30]:
                    date = datetime.fromtimestamp(conv['create_time']).strftime('%Y-%m-%d')
                    st.markdown(f"**{date}**: {conv['title']}")
    
    # Tab 6: Export All
    with tabs[5]:
        st.markdown("### 📦 Export All Synthesis Data")
        
        st.markdown("""
        Generate comprehensive export package including:
        - TI Framework timeline
        - Personal life biography themes
        - Genius cognitive profile
        - Relationship compatibility data
        - Complete conversation database
        """)
        
        if st.button("🎯 Generate Master Export", type="primary"):
            with st.spinner("Generating comprehensive synthesis..."):
                master_export = {
                    'metadata': {
                        'total_conversations': total_convs,
                        'total_messages': total_msgs,
                        'date_range': {
                            'start': datetime.fromtimestamp(date_range[0]).isoformat() if date_range[0] else None,
                            'end': datetime.fromtimestamp(date_range[1]).isoformat() if date_range[1] else None
                        },
                        'generated': datetime.now().isoformat()
                    },
                    'ti_timeline': get_ti_framework_timeline(),
                    'personal_themes': get_personal_life_themes(),
                    'genius_profile': extract_genius_patterns(),
                    'relationship_data': extract_relationship_compatibility()
                }
                
                # Convert to JSON
                export_json = json.dumps(master_export, indent=2, default=str)
                
                st.download_button(
                    "📥 Download Master Synthesis (JSON)",
                    export_json,
                    "chatgpt_master_synthesis.json",
                    "application/json"
                )
                
                st.success("✅ Master synthesis generated!")
