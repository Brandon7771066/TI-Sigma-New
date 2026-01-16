"""
TI Marketing Optimizer - Streamlit Page
GILE-powered content and campaign optimization
"""

import streamlit as st
import sys
import os

sys.path.append('..')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kaggle.ti_marketing_engine import MarketingGILEEngine

st.set_page_config(page_title="Marketing Optimizer", page_icon="📈", layout="wide")

st.title("📈 TI Marketing Intelligence")
st.markdown("**GILE-powered content and campaign optimization**")

engine = MarketingGILEEngine()

st.divider()

tab1, tab2, tab3 = st.tabs(["📝 Content Analyzer", "📊 Campaign Predictor", "✨ Headline Optimizer"])

with tab1:
    st.markdown("### Analyze Content Resonance")
    st.markdown("Paste your content to get GILE-based optimization recommendations.")
    
    content = st.text_area(
        "Your Content",
        height=150,
        placeholder="Paste your ad copy, social post, email subject, or any marketing content here..."
    )
    
    col_type, col_audience = st.columns(2)
    with col_type:
        content_type = st.selectbox("Content Type", ['social', 'email', 'ad', 'blog'])
    with col_audience:
        audience = st.selectbox("Target Audience", ['B2C', 'B2B', 'Gen_Z', 'Professionals'])
    
    if st.button("🔍 Analyze Content", type="primary") and content.strip():
        analysis = engine.analyze_content(content, content_type, audience)
        
        st.divider()
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric("Resonance Score", f"{analysis.resonance_score:.0%}")
            st.metric("Viral Potential", f"{analysis.viral_potential:.0%}")
        
        with col2:
            st.markdown("**GILE Breakdown:**")
            st.progress(analysis.authenticity_score, text=f"G (Authenticity): {analysis.authenticity_score:.0%}")
            st.progress(analysis.clarity_score, text=f"I (Clarity): {analysis.clarity_score:.0%}")
            st.progress(analysis.resonance_score, text=f"L (Connection): {analysis.resonance_score:.0%}")
            st.progress(analysis.energy_score, text=f"E (Energy): {analysis.energy_score:.0%}")
        
        with col3:
            st.markdown("**Optimal Timing:**")
            st.info(f"Best time to post: **{analysis.optimal_timing}**")
        
        st.markdown("### Recommendations")
        for rec in analysis.recommendations:
            st.success(f"✅ {rec}")

with tab2:
    st.markdown("### Predict Campaign Performance")
    st.markdown("Enter your campaign details to predict engagement and ROI.")
    
    col_budget, col_duration, col_platform = st.columns(3)
    
    with col_budget:
        budget = st.number_input("Budget ($)", min_value=100, value=1000, step=100)
    with col_duration:
        duration = st.number_input("Duration (days)", min_value=1, value=14, step=1)
    with col_platform:
        platform = st.selectbox("Platform", ['instagram', 'facebook', 'linkedin', 'twitter', 'tiktok', 'mixed'])
    
    st.markdown("**Ad Variations (one per line):**")
    ad_content = st.text_area(
        "Campaign Content",
        height=150,
        placeholder="Variation 1: Transform your productivity today\nVariation 2: Join 10,000+ professionals\nVariation 3: Get started free"
    )
    
    if st.button("📊 Predict Performance", type="primary") and ad_content.strip():
        content_list = [line.strip() for line in ad_content.strip().split('\n') if line.strip()]
        
        if content_list:
            prediction = engine.predict_campaign_performance(
                content_list=content_list,
                budget=budget,
                duration_days=duration,
                platform=platform
            )
            
            st.divider()
            
            col1, col2, col3, col4 = st.columns(4)
            
            with col1:
                st.metric("Engagement Rate", f"{prediction.expected_engagement_rate:.2%}")
            with col2:
                st.metric("Conversion Rate", f"{prediction.expected_conversion_rate:.2%}")
            with col3:
                color = "normal" if prediction.expected_roi > 0 else "inverse"
                st.metric("Expected ROI", f"{prediction.expected_roi:.0f}%", delta_color=color)
            with col4:
                st.metric("Confidence", f"{prediction.confidence:.0%}")
            
            if prediction.risk_factors:
                st.markdown("### ⚠️ Risk Factors")
                for rf in prediction.risk_factors:
                    st.warning(rf)
            
            st.markdown("### 💡 Optimization Suggestions")
            for sug in prediction.optimization_suggestions:
                st.info(sug)

with tab3:
    st.markdown("### Optimize Headlines")
    st.markdown("Enter a headline to generate optimized variations.")
    
    headline = st.text_input(
        "Original Headline",
        placeholder="e.g., Learn how to improve your marketing"
    )
    
    num_variations = st.slider("Number of Variations", 3, 10, 5)
    
    if st.button("✨ Generate Variations", type="primary") and headline.strip():
        variations = engine.optimize_headline(headline, num_variations)
        
        st.divider()
        
        st.markdown("### Ranked Variations")
        
        for i, (var_headline, score) in enumerate(variations):
            is_best = i == 0
            col1, col2 = st.columns([4, 1])
            
            with col1:
                if is_best:
                    st.success(f"⭐ **{var_headline}**")
                elif var_headline == headline:
                    st.info(f"📝 {var_headline} (original)")
                else:
                    st.write(f"📌 {var_headline}")
            
            with col2:
                st.metric("Score", f"{score:.0%}")

st.divider()

with st.expander("💡 How GILE Scoring Works"):
    st.markdown("""
    **GILE = Goodness × Intuition × Love × Environment**
    
    | Dimension | Marketing Meaning | Optimizes For |
    |-----------|------------------|---------------|
    | **G (Goodness)** | Authenticity & trust | Brand credibility |
    | **I (Intuition)** | Message clarity | Understanding |
    | **L (Love)** | Audience connection | Engagement |
    | **E (Environment)** | Energy & urgency | Action |
    
    **Scoring:**
    - 80%+ = Excellent - ready to launch
    - 60-80% = Good - minor optimizations
    - 40-60% = Needs work - apply recommendations
    - Below 40% = Significant rewrite needed
    
    **Viral Potential** requires ALL factors to be high - you can't go viral with just one strong dimension.
    """)

with st.expander("📚 Best Practices"):
    st.markdown("""
    **High-Resonance Content:**
    1. Use "you" and "your" frequently
    2. Include specific numbers (50,000+ users)
    3. Add urgency without being pushy
    4. Tell a story or share a personal example
    5. End with a question to drive engagement
    
    **Common Mistakes:**
    - Too many exclamation points (spam signal)
    - Corporate buzzwords (synergy, leverage)
    - No clear call-to-action
    - Talking about "we" instead of "you"
    - Long, complex sentences
    """)
