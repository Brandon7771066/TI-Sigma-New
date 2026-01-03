"""
File Storage Dashboard - Simplified Version
Processes ChatGPT conversations directly from uploaded files.
"""

import streamlit as st
import json
import zipfile
from io import BytesIO
from datetime import datetime
from chatgpt_processor import ChatGPTProcessor
from paper_integration_engine import PaperIntegrationEngine

def render_file_storage_dashboard():
    """Render the simplified file processing interface."""
    
    st.header("📁 ChatGPT Conversation Analyzer")
    st.markdown("Upload your ChatGPT conversation export and get instant analysis categorized by concept!")
    
    # Create tabs
    tab1, tab2 = st.tabs([
        "📤 Upload & Process",
        "📝 Query Drafts"
    ])
    
    # TAB 1: Upload & Process
    with tab1:
        render_upload_and_process()
    
    # TAB 2: Query Drafts (simple text storage)
    with tab2:
        render_query_drafts_simple()


def render_upload_and_process():
    """Simple file upload and immediate processing."""
    
    st.subheader("📤 Upload ChatGPT Export")
    
    st.info("📝 **Supported Files:**\n"
            "- `conversations.json` (from ChatGPT export ZIP)\n"
            "- ChatGPT export ZIP file (will auto-extract)\n\n"
            "**File Size Limit:** 200 MB maximum")
    
    uploaded_file = st.file_uploader(
        "Choose your ChatGPT export file",
        type=['json', 'zip'],
        help="Upload conversations.json or the full ZIP export from ChatGPT"
    )
    
    if uploaded_file is not None:
        # Show file info
        file_size_mb = uploaded_file.size / (1024 * 1024)
        st.info(f"**File:** {uploaded_file.name}\n**Size:** {file_size_mb:.2f} MB")
        
        # Check size
        if file_size_mb > 200:
            st.error(f"❌ File too large: {file_size_mb:.1f} MB (limit: 200 MB)\n\n"
                    "**Solution:** Download a smaller ChatGPT export with a shorter date range.")
            return
        
        # Process button
        if st.button("🔍 Analyze Conversations", type="primary"):
            process_chatgpt_file(uploaded_file)


def process_chatgpt_file(uploaded_file):
    """Process the uploaded ChatGPT file and display results."""
    
    with st.spinner("Processing your ChatGPT conversations..."):
        try:
            # Determine file type and extract JSON
            conversations_data = None
            
            if uploaded_file.name.endswith('.json'):
                # Direct JSON file
                content = uploaded_file.read()
                conversations_data = json.loads(content)
                st.success("✅ JSON file loaded successfully!")
                
            elif uploaded_file.name.endswith('.zip'):
                # ZIP file - extract conversations.json
                with zipfile.ZipFile(BytesIO(uploaded_file.read())) as zip_ref:
                    # Look for conversations.json
                    json_files = [f for f in zip_ref.namelist() if f.endswith('conversations.json')]
                    
                    if not json_files:
                        st.error("❌ No conversations.json found in ZIP file")
                        return
                    
                    # Read the first conversations.json found
                    with zip_ref.open(json_files[0]) as json_file:
                        conversations_data = json.load(json_file)
                    
                    st.success(f"✅ Extracted {json_files[0]} from ZIP!")
            
            if conversations_data is None:
                st.error("❌ Could not load conversation data")
                return
            
            # Process conversations
            processor = ChatGPTProcessor()
            results = processor.process_conversations(conversations_data)
            
            # Display results
            display_analysis_results(results, conversations_data)
            
        except json.JSONDecodeError as e:
            st.error(f"❌ Invalid JSON format: {str(e)}")
        except zipfile.BadZipFile:
            st.error("❌ Invalid ZIP file")
        except Exception as e:
            st.error(f"❌ Processing error: {str(e)}")


def display_analysis_results(results, conversations_data):
    """Display the analysis results in a user-friendly format."""
    
    st.markdown("---")
    st.header("📊 Analysis Results")
    
    # Summary statistics
    col1, col2, col3 = st.columns(3)
    
    total_conversations = len(conversations_data) if isinstance(conversations_data, list) else 0
    total_concepts = len(results.get('by_concept', {}))
    total_months = len(results.get('by_date', {}))
    
    with col1:
        st.metric("Total Conversations", total_conversations)
    with col2:
        st.metric("Concepts Found", total_concepts)
    with col3:
        st.metric("Time Span (Months)", total_months)
    
    # Concept breakdown
    st.subheader("🎯 Conversations by Concept")
    
    by_concept = results.get('by_concept', {})
    if by_concept:
        # Create expandable sections for each concept
        for concept, conv_ids in sorted(by_concept.items(), key=lambda x: len(x[1]), reverse=True):
            with st.expander(f"**{concept}** ({len(conv_ids)} conversations)"):
                st.write(f"Found {len(conv_ids)} conversations about {concept}")
                
                # Show sample conversation titles
                sample_size = min(5, len(conv_ids))
                if sample_size > 0:
                    st.write("**Sample conversations:**")
                    
                    # Get conversation titles
                    if isinstance(conversations_data, list):
                        for conv_id in list(conv_ids)[:sample_size]:
                            # Find conversation
                            conv = next((c for c in conversations_data if c.get('id') == conv_id), None)
                            if conv and 'title' in conv:
                                st.write(f"- {conv['title']}")
    else:
        st.info("No concept categorization found. The processor may need conversation data.")
    
    # Timeline
    st.subheader("📅 Timeline of Insights")
    
    by_date = results.get('by_date', {})
    if by_date:
        for month, conv_ids in sorted(by_date.items(), reverse=True):
            st.write(f"**{month}**: {len(conv_ids)} conversations")
    else:
        st.info("No date-based organization available.")
    
    # Integration recommendations
    st.markdown("---")
    st.subheader("📄 Paper Integration Recommendations")
    
    engine = PaperIntegrationEngine()
    recommendations = engine.get_recommendations(by_concept)
    
    if recommendations:
        st.success(f"Found {len(recommendations)} papers that could benefit from these insights!")
        
        for rec in recommendations:
            with st.expander(f"📄 {rec['paper']}"):
                st.write(f"**Relevant concepts:** {', '.join(rec['concepts'])}")
                st.write(f"**Why update:** {rec['reason']}")
                st.write(f"**Suggested sections:** {', '.join(rec['sections'])}")
    else:
        st.info("No specific integration recommendations generated.")
    
    # Master index preview
    st.markdown("---")
    st.subheader("📋 Analysis Summary")
    
    master_index = results.get('master_index', '')
    if master_index:
        st.markdown(master_index[:2000])  # Show first 2000 chars
        if len(master_index) > 2000:
            st.info("(Preview truncated - full index generated)")
    
    # Download options
    st.markdown("---")
    st.subheader("💾 Download Results")
    
    col1, col2 = st.columns(2)
    
    with col1:
        if master_index:
            st.download_button(
                label="📥 Download Master Index",
                data=master_index,
                file_name=f"master_index_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md",
                mime="text/markdown"
            )
    
    with col2:
        timeline = results.get('timeline', '')
        if timeline:
            st.download_button(
                label="📥 Download Timeline",
                data=timeline,
                file_name=f"timeline_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md",
                mime="text/markdown"
            )


def render_query_drafts_simple():
    """Simple query drafts using session state (no cloud storage)."""
    
    st.subheader("📝 Query Drafts")
    st.markdown("Save your query drafts here to prevent losing work when the app restarts.")
    
    # Initialize session state
    if 'query_drafts' not in st.session_state:
        st.session_state.query_drafts = []
    
    # New draft
    st.write("**Create New Draft:**")
    draft_name = st.text_input("Draft name:", placeholder="e.g., TWA Analysis Query")
    draft_content = st.text_area("Query content:", height=150, placeholder="Enter your query here...")
    
    if st.button("💾 Save Draft"):
        if draft_name and draft_content:
            st.session_state.query_drafts.append({
                'name': draft_name,
                'content': draft_content,
                'timestamp': datetime.now().isoformat()
            })
            st.success(f"✅ Saved draft: {draft_name}")
            st.rerun()
        else:
            st.warning("Please provide both name and content")
    
    # Show existing drafts
    st.markdown("---")
    st.write("**Your Drafts:**")
    
    if st.session_state.query_drafts:
        for idx, draft in enumerate(st.session_state.query_drafts):
            with st.expander(f"📄 {draft['name']} ({draft['timestamp'][:10]})"):
                st.text_area(
                    "Content:",
                    value=draft['content'],
                    height=100,
                    key=f"draft_{idx}",
                    disabled=True
                )
                
                col1, col2 = st.columns(2)
                with col1:
                    if st.button(f"🗑️ Delete", key=f"delete_{idx}"):
                        st.session_state.query_drafts.pop(idx)
                        st.rerun()
                with col2:
                    st.download_button(
                        label="📥 Download",
                        data=draft['content'],
                        file_name=f"{draft['name']}.txt",
                        key=f"download_{idx}"
                    )
    else:
        st.info("No drafts saved yet. Create one above!")
        st.warning("⚠️ **Note:** Drafts are stored in session memory and will be lost when the app restarts. "
                  "Download important drafts to save them permanently.")
