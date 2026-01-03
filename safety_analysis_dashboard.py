"""
Safety Analysis Dashboard - Isolated module for tab2
"""

import streamlit as st
import os
from ai_integrations import OpenAIIntegration, AnthropicIntegration, PerplexityIntegration
from magai_integration import MagAIIntegration
from safety_analyzer import SafetyAnalyzer
from submission_logger import SubmissionLogger
import trafilatura
import json

def initialize_ai_clients():
    """Initialize all AI clients."""
    try:
        openai_client = OpenAIIntegration()
        anthropic_client = AnthropicIntegration()
        perplexity_api_key = os.environ.get("PERPLEXITY_API_KEY")
        
        if perplexity_api_key:
            perplexity_client = PerplexityIntegration()
        else:
            perplexity_client = None
            st.sidebar.warning("⚠️ Perplexity API key not found. Perplexity analysis will be skipped.")
        
        magai_email = os.environ.get("MAGAI_EMAIL")
        magai_password = os.environ.get("MAGAI_PASSWORD")
        
        if magai_email and magai_password:
            magai_client = MagAIIntegration(magai_email, magai_password)
        else:
            magai_client = None
            st.sidebar.info("ℹ️ MagAI credentials not configured. MagAI analysis will be skipped.")
        
        return openai_client, anthropic_client, perplexity_client, magai_client
    
    except Exception as e:
        st.error(f"Error initializing AI clients: {str(e)}")
        return None, None, None, None


def render_safety_analysis_dashboard():
    """Main Safety Analysis Dashboard"""
    
    # Clear any sidebar from other tabs
    st.sidebar.empty()
    st.sidebar.header("⚙️ Safety Analysis Configuration")
    st.sidebar.subheader("📥 Data Input Methods")
    input_method = st.sidebar.radio(
        "Choose input method:",
        ["Upload Files", "Paste Text", "URL Scraping", "Manual File Extraction Guide"]
    )
    
    content_to_analyze = ""
    file_name = None
    
    if input_method == "Upload Files":
        st.header("📤 Upload Project Documentation")
        st.markdown("Upload any documentation files from your Mood Amplifier project (PDFs, text files, research papers)")
        
        uploaded_files = st.file_uploader(
            "Choose files",
            accept_multiple_files=True,
            type=['txt', 'md', 'pdf', 'doc', 'docx']
        )
        
        if uploaded_files:
            for uploaded_file in uploaded_files:
                if uploaded_file.type == "text/plain":
                    content_to_analyze += f"\n\n--- File: {uploaded_file.name} ---\n"
                    content_to_analyze += uploaded_file.read().decode("utf-8")
                else:
                    st.info(f"📄 {uploaded_file.name} uploaded (text extraction for PDF coming soon)")
    
    elif input_method == "Paste Text":
        st.header("📝 Paste Project Content")
        st.markdown("Copy and paste content from individual files in your unresponsive Replit project")
        
        file_name = st.text_input("File name (optional):", placeholder="e.g., main.py, README.md")
        pasted_content = st.text_area(
            "Paste file content here:",
            height=400,
            placeholder="Paste the content from your Mood Amplifier project files..."
        )
        
        if pasted_content:
            if file_name:
                content_to_analyze = f"--- File: {file_name} ---\n{pasted_content}"
            else:
                content_to_analyze = pasted_content
            
            st.success(f"✅ Content loaded ({len(pasted_content)} characters)")
    
    elif input_method == "URL Scraping":
        st.header("🌐 URL Content Extraction")
        st.markdown("Extract content from the Replit project URL or any web-accessible documentation")
        
        url = st.text_input("Enter URL:", placeholder="https://replit.com/@username/project")
        
        if url and st.button("Extract Content"):
            with st.spinner("Scraping content from URL..."):
                try:
                    downloaded = trafilatura.fetch_url(url)
                    extracted_text = trafilatura.extract(downloaded)
                    
                    if extracted_text:
                        content_to_analyze = f"--- Content from: {url} ---\n{extracted_text}"
                        st.success(f"✅ Content extracted ({len(extracted_text)} characters)")
                        st.text_area("Extracted content preview:", extracted_text[:1000] + "...", height=200)
                    else:
                        st.error("❌ Could not extract text from URL. The page may require authentication.")
                except Exception as e:
                    st.error(f"Error scraping URL: {str(e)}")
    
    elif input_method == "Manual File Extraction Guide":
        st.header("🔧 Manual File Extraction Guide")
        st.markdown("""
        ### How to Extract Files from Your Unresponsive Replit
        
        If your Mood Amplifier Replit is too large and won't export, try these methods:
        
        #### Method 1: Browser Developer Tools
        1. Open your Replit project in Chrome or Firefox
        2. Press F12 to open Developer Tools
        3. Go to the "Console" tab
        4. Type: `fetch('/api/files').then(r => r.json()).then(console.log)`
        5. This will list all files - you can then fetch individual files
        
        #### Method 2: Individual File Copying
        1. Open each file in the Replit editor
        2. Select All (Ctrl+A / Cmd+A)
        3. Copy the content
        4. Use the "Paste Text" method above to add it here
        
        #### Method 3: Git Clone (if enabled)
        1. Check if your Repl has Git enabled (Version Control tab)
        2. Clone the repository locally: `git clone <your-repl-git-url>`
        3. Upload the files using the "Upload Files" method
        
        #### Method 4: Replit API (Advanced)
        1. Get your Replit API token from Account Settings
        2. Use the Replit API to programmatically fetch files
        3. Contact me if you need help with this method
        """)
    
    st.markdown("---")
    
    if content_to_analyze:
        st.header("🔍 Safety Analysis")
        
        col1, col2 = st.columns([3, 1])
        
        with col1:
            st.subheader("Content to Analyze")
            st.text_area("Preview:", content_to_analyze[:2000] + "..." if len(content_to_analyze) > 2000 else content_to_analyze, height=200)
        
        with col2:
            st.metric("Content Length", f"{len(content_to_analyze)} chars")
            st.metric("Estimated Tokens", f"~{len(content_to_analyze) // 4}")
        
        if st.button("🚀 Run Comprehensive Safety Analysis", type="primary"):
            # Initialize submission logger
            logger = SubmissionLogger()
            
            # Log the submission
            metadata = {
                'input_method': input_method,
                'file_name': file_name
            }
            submission_id = logger.log_submission(content_to_analyze, input_method, metadata)
            st.info(f"📝 Submission logged: {submission_id}")
            
            openai_client, anthropic_client, perplexity_client, magai_client = initialize_ai_clients()
            
            if not openai_client or not anthropic_client:
                st.error("Failed to initialize AI clients. Please check your configuration.")
            else:
                analyzer = SafetyAnalyzer(openai_client, anthropic_client, perplexity_client, magai_client)
                
                with st.spinner("🔬 Running comprehensive safety analysis across multiple AI models..."):
                    st.info("This may take 2-3 minutes as we query multiple AI systems...")
                    
                    results = analyzer.comprehensive_safety_analysis(content_to_analyze)
                    
                    # Log the results
                    logger.log_analysis_results(submission_id, results)
                    
                    st.success("✅ Analysis Complete!")
                    
                    st.header("📊 Safety Analysis Results")
                    
                    tabs = st.tabs([
                        "🐭 Animal Studies",
                        "🧬 Physical Mechanisms",
                        "💊 Tolerance & Addiction",
                        "⚠️ Brain Damage Risk",
                        "🤝 Consensus View",
                        "📋 Full Report"
                    ])
                    
                    with tabs[0]:
                        st.subheader("Animal Studies Verification")
                        if "animal_studies" in results:
                            for model, analysis in results["animal_studies"].items():
                                with st.expander(f"📝 {model.upper()} Analysis"):
                                    if "error" in analysis:
                                        st.error(f"Error: {analysis['error']}")
                                    elif "raw_response" in analysis:
                                        st.markdown(analysis["raw_response"])
                    
                    with tabs[1]:
                        st.subheader("Physical Mechanisms & Brain Effects")
                        if "physical_mechanisms" in results:
                            for model, analysis in results["physical_mechanisms"].items():
                                with st.expander(f"📝 {model.upper()} Analysis"):
                                    if "error" in analysis:
                                        st.error(f"Error: {analysis['error']}")
                                    elif "raw_response" in analysis:
                                        st.markdown(analysis["raw_response"])
                    
                    with tabs[2]:
                        st.subheader("Tolerance & Addiction Risk Assessment")
                        if "tolerance_addiction" in results:
                            for model, analysis in results["tolerance_addiction"].items():
                                with st.expander(f"📝 {model.upper()} Analysis"):
                                    if "error" in analysis:
                                        st.error(f"Error: {analysis['error']}")
                                    elif "raw_response" in analysis:
                                        st.markdown(analysis["raw_response"])
                    
                    with tabs[3]:
                        st.subheader("Brain Damage & Neurotoxicity Risk")
                        if "brain_damage" in results:
                            for model, analysis in results["brain_damage"].items():
                                with st.expander(f"📝 {model.upper()} Analysis"):
                                    if "error" in analysis:
                                        st.error(f"Error: {analysis['error']}")
                                    elif "raw_response" in analysis:
                                        st.markdown(analysis["raw_response"])
                    
                    with tabs[4]:
                        st.subheader("🤝 Cross-AI Consensus Analysis")
                        
                        if "disagreements" in results and results["disagreements"]:
                            st.error("⚠️ **Key Disagreements Between AI Models:**")
                            for disagreement in results["disagreements"]:
                                st.warning(f"• {disagreement}")
                            st.markdown("---")
                        
                        if "consensus" in results:
                            for aspect, consensus_data in results["consensus"].items():
                                st.subheader(f"📊 {aspect.replace('_', ' ').title()}")
                                
                                col1, col2 = st.columns(2)
                                with col1:
                                    st.metric("Models Analyzed", consensus_data.get("model_count", 0))
                                with col2:
                                    confidence = consensus_data.get("confidence", "unknown")
                                    confidence_color = {
                                        "high": "🟢",
                                        "moderate": "🟡",
                                        "low": "🟠",
                                        "none": "🔴",
                                        "unknown": "⚪"
                                    }.get(confidence, "⚪")
                                    st.metric("Confidence", f"{confidence_color} {confidence.upper()}")
                                
                                if consensus_data.get("agreements"):
                                    st.markdown("**Consensus Points:**")
                                    for agreement in consensus_data["agreements"]:
                                        st.success(f"✓ {agreement}")
                                
                                if consensus_data.get("key_findings"):
                                    st.markdown("**Key Findings:**")
                                    for finding in consensus_data["key_findings"]:
                                        if "⚠️" in finding or "HIGH" in finding:
                                            st.error(f"🚨 {finding}")
                                        else:
                                            st.info(f"• {finding}")
                                
                                st.markdown("---")
                        
                        if "overall_safety_rating" in results:
                            st.subheader("🎯 Overall Safety Rating")
                            rating = results["overall_safety_rating"]
                            st.warning(f"**Rating:** {rating.get('rating', 'Unknown')}")
                            st.info(f"**Recommendation:** {rating.get('recommendation', 'N/A')}")
                            
                            if "critical_concerns" in rating:
                                st.error("**Critical Concerns:**")
                                for concern in rating["critical_concerns"]:
                                    st.write(f"- {concern}")
                    
                    with tabs[5]:
                        st.subheader("Complete Analysis Report (JSON)")
                        st.json(results)
                        
                        st.download_button(
                            label="📥 Download Full Report (JSON)",
                            data=json.dumps(results, indent=2),
                            file_name="mood_amplifier_safety_analysis.json",
                            mime="application/json"
                        )
    
    else:
        st.info("👈 Please select an input method and provide your Mood Amplifier project documentation to begin the safety analysis.")
        
        st.markdown("---")
        st.header("🎯 What This Tool Analyzes")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.subheader("🐭 Animal Studies")
            st.markdown("""
            - Verification of cited animal research
            - Quality and credibility of studies
            - Key findings and safety concerns
            - Adequacy of preclinical testing
            """)
            
            st.subheader("💊 Tolerance & Addiction")
            st.markdown("""
            - Risk of developing tolerance over time
            - Addiction potential assessment
            - Withdrawal symptom analysis
            - Long-term safety considerations
            """)
        
        with col2:
            st.subheader("🧬 Physical Mechanisms")
            st.markdown("""
            - How the intervention affects the brain
            - Neurotransmitter systems involved
            - Scientific plausibility of claims
            - Evidence quality assessment
            """)
            
            st.subheader("⚠️ Brain Damage Risk")
            st.markdown("""
            - Neurotoxicity probability
            - Potential cognitive side effects
            - Long-term neurological risks
            - Reversibility of brain changes
            """)
    
    st.sidebar.markdown("---")
    st.sidebar.markdown("### ⚠️ Important Notice")
    st.sidebar.warning("""
    This tool provides AI-assisted analysis but **DOES NOT** replace professional medical or scientific review. 
    
    **Before using any mood amplification intervention on yourself:**
    - Consult qualified medical professionals
    - Review with neuroscience experts
    - Verify all scientific claims independently
    - Consider ethics board review
    
    **AI limitations:** AI models can hallucinate or misinterpret data. Always verify critical safety information.
    """)
