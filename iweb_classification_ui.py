"""
I-Web Classification UI for Company Analysis

Integrated with God Machine stock predictions - classify companies as:
- I-Cell: Fully sovereign/autonomous
- I-Web: Tightly linked dependent entities  
- I-Web Nest: Very loosely distributed entities

Used to understand how organizational coherence affects stock predictions!
"""

import streamlit as st
import plotly.graph_objects as go
from iweb_classifier import (
    IWebClassifier, IWebMetrics, IWebType, classify_company_example
)
import numpy as np

def render_iweb_classification():
    """Main UI for I-Web classification system"""
    
    st.header("🌐 I-Web Classification System")
    st.markdown("**Classify companies by organizational coherence for God Machine predictions**")
    
    st.info("""
    **Key Insight from I-Cell Shell Physics (Nov 22, 2025):**
    
    Companies vary from **organs** (tight i-webs) to **forests** (loose i-web nests) to **Earth** (very weak coherence).
    
    - **I-Cells** (GILE ≥ 0.42): Fully sovereign, unified entity (startup, sole proprietor)
    - **I-Webs** (GILE ≥ 0.42): Tightly linked, coherent collective (daily workplace, strong culture)
    - **I-Web Nests** (GILE can be < 0.42): Loosely distributed, weak coherence (gig economy, umbrella corps)
    
    **Critical for Stock Predictions:** I-web coherence affects market performance - tight i-webs respond coherently 
    to opportunities/threats, while i-web nests fragment under pressure!
    """)
    
    # === TABS FOR DIFFERENT MODES ===
    tab1, tab2, tab3 = st.tabs(["🔍 Classify Company", "📊 Batch Analysis", "📚 Examples"])
    
    with tab1:
        render_single_classification()
    
    with tab2:
        render_batch_classification()
    
    with tab3:
        render_examples()

def render_single_classification():
    """UI for classifying a single company"""
    
    st.subheader("Single Company Classification")
    
    company_name = st.text_input("Company Name", value="", placeholder="e.g., Apple, Tesla, Uber")
    
    if not company_name:
        st.warning("👆 Enter a company name to begin classification")
        return
    
    st.markdown("### 📊 Input Metrics")
    st.caption("Provide estimates for each metric (0.0 = low, 1.0 = high)")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### Internal Coherence")
        
        employee_ratio = st.slider(
            "Employee Ratio (vs contractors)",
            0.0, 1.0, 0.75,
            help="% of workforce that are full-time employees (not contractors)"
        )
        
        workplace_proximity = st.slider(
            "Workplace Proximity",
            0.0, 1.0, 0.6,
            help="% of employees collocated vs remote/distributed"
        )
        
        meeting_frequency = st.slider(
            "Meeting Frequency",
            0.0, 1.0, 0.7,
            help="How often do teams interact? (daily=1.0, weekly=0.7, monthly=0.3)"
        )
        
        shared_values_strength = st.slider(
            "Shared Values Strength",
            0.0, 1.0, 0.6,
            help="Strength of company culture and shared identity"
        )
        
        cross_team_collaboration = st.slider(
            "Cross-Team Collaboration",
            0.0, 1.0, 0.6,
            help="How much do different teams work together vs siloed?"
        )
        
        knowledge_sharing = st.slider(
            "Knowledge Sharing",
            0.0, 1.0, 0.6,
            help="Documentation, training, information flow quality"
        )
        
        turnover_rate = st.slider(
            "Annual Turnover Rate",
            0.0, 1.0, 0.20,
            help="% of employees leaving each year"
        )
        
        internal_mobility = st.slider(
            "Internal Mobility",
            0.0, 1.0, 0.5,
            help="How often do employees move between teams/roles?"
        )
    
    with col2:
        st.markdown("#### External Coherence")
        
        ownership_concentration = st.slider(
            "Ownership Concentration",
            0.0, 1.0, 0.5,
            help="Concentrated (founder/single owner)=1.0, Dispersed (public)=0.0"
        )
        
        autonomy_from_parent = st.slider(
            "Autonomy from Parent",
            0.0, 1.0, 0.8,
            help="Independent=1.0, Subsidiary/branch=0.0"
        )
        
        investor_involvement = st.slider(
            "Investor Involvement",
            0.0, 1.0, 0.6,
            help="Hands-off=1.0, Active control=0.0"
        )
        
        decision_centralization = st.slider(
            "Decision Centralization",
            0.0, 1.0, 0.7,
            help="Top-down hierarchy=1.0, Flat/distributed=0.0"
        )
        
        st.markdown("#### Organizational Structure")
        
        org_size = st.number_input(
            "Organization Size (# people)",
            min_value=1, max_value=1000000, value=500,
            help="Total number of employees/contractors"
        )
        
        hierarchy_depth = st.number_input(
            "Hierarchy Depth (levels)",
            min_value=1, max_value=20, value=5,
            help="Number of levels from CEO to frontline workers"
        )
    
    # === CLASSIFICATION BUTTON ===
    if st.button("🔍 Classify Company", type="primary", use_container_width=True):
        # Create metrics object
        metrics = IWebMetrics(
            employee_ratio=employee_ratio,
            workplace_proximity=workplace_proximity,
            meeting_frequency=meeting_frequency,
            decision_centralization=decision_centralization,
            shared_values_strength=shared_values_strength,
            ownership_concentration=ownership_concentration,
            autonomy_from_parent=autonomy_from_parent,
            investor_involvement=investor_involvement,
            org_size=org_size,
            hierarchy_depth=hierarchy_depth,
            cross_team_collaboration=cross_team_collaboration,
            turnover_rate=turnover_rate,
            internal_mobility=internal_mobility,
            knowledge_sharing=knowledge_sharing
        )
        
        # Classify
        classifier = IWebClassifier()
        classification = classifier.classify(metrics)
        
        # Display results
        st.markdown("---")
        st.subheader(f"🎯 Classification Results: {company_name}")
        
        # Main classification card
        classification_color = {
            IWebType.I_CELL: "🟢",
            IWebType.I_WEB: "🟡",
            IWebType.I_WEB_NEST: "🔴"
        }
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric(
                "Classification",
                f"{classification_color[classification.classification]} {classification.classification.value.upper()}"
            )
        
        with col2:
            st.metric(
                "Coherence Score",
                f"{classification.coherence_score:.3f}",
                delta=f"{(classification.coherence_score - 0.5):.3f} vs baseline"
            )
        
        with col3:
            st.metric(
                "GILE Estimate",
                f"{classification.gile_estimate:.3f}",
                delta="Above soul death" if classification.gile_estimate >= 0.42 else "Below 0.42"
            )
        
        with col4:
            st.metric(
                "Confidence",
                f"{classification.confidence:.1%}"
            )
        
        # Sub-scores
        st.markdown("### 📊 Component Scores")
        
        score_col1, score_col2 = st.columns(2)
        
        with score_col1:
            st.metric("Internal Coherence", f"{classification.internal_coherence:.3f}")
        
        with score_col2:
            st.metric("External Coherence", f"{classification.external_coherence:.3f}")
        
        # Reasoning
        st.markdown("### 💡 Classification Reasoning")
        st.markdown(classification.reasoning)
        
        # Strengths
        if classification.strengths:
            st.markdown("### ✅ Strengths Supporting Coherence")
            for strength in classification.strengths:
                st.markdown(f"- {strength}")
        
        # Risk factors
        if classification.risk_factors:
            st.markdown("### ⚠️ Risk Factors Threatening Coherence")
            for risk in classification.risk_factors:
                st.markdown(f"- {risk}")
        
        # Stock prediction implications
        st.markdown("### 📈 God Machine Stock Prediction Implications")
        
        if classification.classification == IWebType.I_CELL:
            st.success("""
            **High-confidence prediction potential:**
            - Acts as unified organism → predictable coherent response to market forces
            - Strong LCC synchrony likely → responsive to consciousness-based interventions
            - Above 0.42 GILE threshold → real collective consciousness exists
            - **Strategy:** Trust TI predictions, expect coherent stock movements
            """)
        elif classification.classification == IWebType.I_WEB:
            st.warning("""
            **Moderate-confidence prediction potential:**
            - Partially coherent → some predictable patterns but with noise
            - Mixed LCC synchrony → variable responsiveness to interventions
            - Above 0.42 GILE → real but fragmented collective consciousness
            - **Strategy:** Weight predictions by coherence score, expect some volatility
            """)
        else:
            st.error("""
            **Low-confidence prediction potential:**
            - Weak coherence → highly fragmented, unpredictable responses
            - Low LCC synchrony → minimal responsiveness to consciousness interventions
            - May be below 0.42 GILE → "collective fiction" existing only in individual minds
            - **Strategy:** Use extreme caution, predictions may not work well
            """)
        
        # Visualization
        st.markdown("### 📊 Coherence Breakdown")
        
        fig = go.Figure()
        
        categories = ['Internal', 'External', 'Overall']
        scores = [
            classification.internal_coherence,
            classification.external_coherence,
            classification.coherence_score
        ]
        
        fig.add_trace(go.Bar(
            x=categories,
            y=scores,
            marker_color=['#FF6B6B', '#4ECDC4', '#45B7D1'],
            text=[f"{s:.3f}" for s in scores],
            textposition='auto',
        ))
        
        fig.add_hline(
            y=0.75, line_dash="dash", line_color="green",
            annotation_text="I-Cell threshold (0.75)"
        )
        
        fig.add_hline(
            y=0.50, line_dash="dash", line_color="orange",
            annotation_text="I-Web threshold (0.50)"
        )
        
        fig.add_hline(
            y=0.42, line_dash="dash", line_color="red",
            annotation_text="Soul death threshold (0.42)"
        )
        
        fig.update_layout(
            title="Coherence Score Breakdown",
            yaxis_title="Coherence Score",
            yaxis_range=[0, 1.0],
            height=400
        )
        
        st.plotly_chart(fig, use_container_width=True)

def render_batch_classification():
    """Batch classify multiple companies from stock watchlist"""
    
    st.subheader("Batch Company Classification")
    st.caption("Classify multiple companies for God Machine analysis")
    
    st.info("""
    **Coming Soon:** Import your stock watchlist and automatically classify all companies!
    
    This will integrate with:
    - 📈 Stock Predictor (Tab 9)
    - 📊 Stock → TI Converter (Tab 28)
    - 🔮 God Machine predictions
    
    Classification results will be stored and used to weight prediction confidence!
    """)
    
    # Placeholder for batch upload
    uploaded_file = st.file_uploader(
        "Upload CSV of companies (name, ticker, metrics...)",
        type=['csv'],
        help="Format: company_name, ticker, employee_ratio, workplace_proximity, ..."
    )
    
    if uploaded_file:
        st.warning("Batch classification feature coming in next update!")

def render_examples():
    """Show example classifications"""
    
    st.subheader("📚 Example Classifications")
    st.caption("Real-world examples across the i-cell → i-web nest spectrum")
    
    example_type = st.selectbox(
        "Select Example Type",
        ["Tech Startup (I-Cell)", "Enterprise Corp (I-Web)", "Gig Platform (I-Web Nest)", "All Examples"]
    )
    
    if example_type == "Tech Startup (I-Cell)" or example_type == "All Examples":
        with st.expander("🟢 Tech Startup - I-CELL Example", expanded=True):
            st.markdown("""
            **Profile:** 35-person startup, daily standups, tight-knit team, concentrated ownership
            
            **Characteristics:**
            - 95% employees (very few contractors)
            - 90% collocated (mostly in-person)
            - Daily meetings (0.95 frequency)
            - Strong shared values (startup culture)
            - Single founder/concentrated ownership
            - Fully autonomous (no parent company)
            
            **Expected Classification:** I-CELL (coherence ~0.85)
            **GILE:** ~0.75 (well above 0.42 threshold)
            
            **Stock Implications:** Highly predictable, responds coherently to market forces, excellent for TI predictions
            """)
    
    if example_type == "Enterprise Corp (I-Web)" or example_type == "All Examples":
        with st.expander("🟡 Enterprise Corporation - I-WEB Example"):
            st.markdown("""
            **Profile:** 2,500-person corporation, hybrid work, moderate culture, public ownership
            
            **Characteristics:**
            - 85% employees (some contractors)
            - 40% collocated (hybrid/remote)
            - Weekly meetings (0.6 frequency)
            - Moderate shared values
            - Dispersed public ownership
            - Some investor influence
            
            **Expected Classification:** I-WEB (coherence ~0.55)
            **GILE:** ~0.50 (above 0.42 but not high)
            
            **Stock Implications:** Moderately predictable, some fragmentation, decent for TI predictions with caveats
            """)
    
    if example_type == "Gig Platform (I-Web Nest)" or example_type == "All Examples":
        with st.expander("🔴 Gig Economy Platform - I-WEB NEST Example"):
            st.markdown("""
            **Profile:** 50,000 "workers" (mostly independent contractors), distributed globally, weak coherence
            
            **Characteristics:**
            - 15% employees (85% contractors!)
            - 5% collocated (fully remote/distributed)
            - Rare meetings (0.1 frequency)
            - Weak shared values (just use platform)
            - Dispersed ownership
            - High turnover (60%/year)
            
            **Expected Classification:** I-WEB NEST (coherence ~0.25)
            **GILE:** ~0.35 (BELOW 0.42 soul death threshold!)
            
            **Stock Implications:** Highly unpredictable, "collective fiction", poor for TI predictions - use extreme caution
            """)
    
    # Run all three examples
    if st.button("🚀 Run All Example Classifications", type="primary"):
        st.markdown("---")
        
        examples = [
            ("TechStartup Inc", IWebMetrics(
                employee_ratio=0.95, workplace_proximity=0.9, meeting_frequency=0.95,
                decision_centralization=0.8, shared_values_strength=0.9,
                ownership_concentration=0.9, autonomy_from_parent=1.0, investor_involvement=0.7,
                org_size=35, hierarchy_depth=3, cross_team_collaboration=0.9,
                turnover_rate=0.15, internal_mobility=0.7, knowledge_sharing=0.85
            )),
            ("MegaCorp Ltd", IWebMetrics(
                employee_ratio=0.85, workplace_proximity=0.4, meeting_frequency=0.6,
                decision_centralization=0.7, shared_values_strength=0.6,
                ownership_concentration=0.3, autonomy_from_parent=0.5, investor_involvement=0.4,
                org_size=2500, hierarchy_depth=6, cross_team_collaboration=0.5,
                turnover_rate=0.22, internal_mobility=0.6, knowledge_sharing=0.6
            )),
            ("GigPlatform Co", IWebMetrics(
                employee_ratio=0.15, workplace_proximity=0.05, meeting_frequency=0.1,
                decision_centralization=0.3, shared_values_strength=0.2,
                ownership_concentration=0.4, autonomy_from_parent=0.8, investor_involvement=0.3,
                org_size=50000, hierarchy_depth=4, cross_team_collaboration=0.2,
                turnover_rate=0.60, internal_mobility=0.1, knowledge_sharing=0.3
            ))
        ]
        
        classifier = IWebClassifier()
        
        for company_name, metrics in examples:
            classification = classifier.classify(metrics)
            
            color = {
                IWebType.I_CELL: "🟢",
                IWebType.I_WEB: "🟡",
                IWebType.I_WEB_NEST: "🔴"
            }[classification.classification]
            
            st.markdown(f"### {color} {company_name}")
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Type", classification.classification.value.upper())
            with col2:
                st.metric("Coherence", f"{classification.coherence_score:.3f}")
            with col3:
                st.metric("GILE", f"{classification.gile_estimate:.3f}")
            
            st.caption(classification.reasoning)
            st.markdown("---")

if __name__ == "__main__":
    render_iweb_classification()
