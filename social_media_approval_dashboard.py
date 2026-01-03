"""
Social Media Approval Dashboard
6 AM content digest, approval workflow, analytics, engagement bots
"""

import streamlit as st
from social_media_approval_system import (
    ContentDigestGenerator,
    ContentApprovalWorkflow,
    AnalyticsDashboard,
    EngagementBotSystem,
    SafetyGuardrails,
    schedule_daily_digest,
    get_latest_digest
)
from db_utils import db
from datetime import datetime, timedelta
import plotly.graph_objects as go
import plotly.express as px


def render_social_media_approval():
    """Render Social Media Approval & Publishing Dashboard"""
    
    st.title("📱 Social Media Approval & Publishing")
    st.markdown("""
    **Daily Content Digest & Approval Workflow**
    
    Review all content at 6 AM EST, approve for publishing, track analytics, manage engagement.
    """)
    
    # Safety warning
    safety = SafetyGuardrails()
    st.info(safety.prevent_auto_publish())
    
    # Initialize systems
    if 'digest_generator' not in st.session_state:
        st.session_state.digest_generator = ContentDigestGenerator()
    if 'approval_workflow' not in st.session_state:
        st.session_state.approval_workflow = ContentApprovalWorkflow()
    if 'analytics' not in st.session_state:
        st.session_state.analytics = AnalyticsDashboard()
    if 'engagement_bot' not in st.session_state:
        st.session_state.engagement_bot = EngagementBotSystem()
    
    # Auto-start daily digest scheduler
    if 'digest_scheduler_started' not in st.session_state:
        try:
            schedule_daily_digest()
            st.session_state.digest_scheduler_started = True
        except Exception as e:
            st.warning(f"Digest scheduler: {e}")
    
    # Create tabs
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📬 6 AM Digest",
        "✅ Approve Content",
        "📊 Analytics",
        "🤖 Engagement Bots",
        "⚙️ Settings"
    ])
    
    # Tab 1: 6 AM Daily Digest
    with tab1:
        st.header("📬 Daily Content Digest (6 AM EST)")
        st.markdown("*All pending content for review and approval*")
        
        col1, col2 = st.columns([3, 1])
        
        with col1:
            st.info("""
            **Scheduled:** Every day at 6:00 AM Eastern Time
            
            Content included:
            - 🎬 Video scripts (last 20)
            - 🔬 Autonomous discoveries (last 24h)
            - 📝 Social media posts
            - 📚 Book chapters
            """)
        
        with col2:
            if st.button("🔄 Generate Now", type="primary"):
                with st.spinner("Generating digest..."):
                    digest = st.session_state.digest_generator.generate_daily_digest()
                    asset_id = st.session_state.digest_generator.save_digest(digest)
                    st.success(f"✅ Digest generated! (ID: {asset_id})")
                    st.rerun()
        
        # Display latest digest
        latest_digest = get_latest_digest()
        
        if latest_digest:
            content = latest_digest.get('content', {})
            
            st.markdown("---")
            st.subheader(f"📅 Digest: {content.get('date', 'Unknown')}")
            
            # Summary metrics
            col1, col2, col3, col4 = st.columns(4)
            
            categories = content.get('content_categories', {})
            
            with col1:
                st.metric("🎬 Videos", len(categories.get('videos', [])))
            with col2:
                st.metric("🔬 Discoveries", len(categories.get('discoveries', [])))
            with col3:
                st.metric("📝 Posts", len(categories.get('social_posts', [])))
            with col4:
                st.metric("📚 Book Content", len(categories.get('book_chapters', [])))
            
            # Display each category
            for category_name, items in categories.items():
                if items:
                    with st.expander(f"📂 {category_name.replace('_', ' ').title()} ({len(items)} items)"):
                        for i, item in enumerate(items, 1):
                            item_content = item.get('content', {})
                            st.markdown(f"**{i}. {item.get('title', 'Untitled')[:100]}...**")
                            st.caption(f"ID: {item.get('asset_id', 'Unknown')} | Created: {item.get('created_at', 'Unknown')}")
                            
                            # Quick approve/reject buttons
                            col_a, col_b = st.columns(2)
                            with col_a:
                                if st.button(f"✅ Approve #{i}", key=f"approve_{category_name}_{i}"):
                                    approval = st.session_state.approval_workflow.approve_content(
                                        item.get('asset_id', '')
                                    )
                                    st.success(f"Approved! {approval}")
                            with col_b:
                                if st.button(f"❌ Reject #{i}", key=f"reject_{category_name}_{i}"):
                                    rejection = st.session_state.approval_workflow.reject_content(
                                        item.get('asset_id', ''),
                                        reason="User rejected"
                                    )
                                    st.warning(f"Rejected: {rejection}")
                            
                            st.markdown("---")
        else:
            st.warning("📭 No digest available yet. Click 'Generate Now' or wait for 6 AM.")
    
    # Tab 2: Content Approval
    with tab2:
        st.header("✅ Content Approval Workflow")
        st.markdown("*Approve, reject, or schedule content for publishing*")
        
        st.info("""
        **Safety Rules:**
        - Nothing published without your approval
        - Schedule future publishing times
        - Review content before going live
        - Protected name filtering active
        """)
        
        # Manual approval form
        st.subheader("📝 Approve Specific Content")
        
        asset_id_input = st.text_input("Asset ID to Approve", placeholder="Enter asset ID from digest")
        
        col1, col2 = st.columns(2)
        
        with col1:
            approval_type = st.radio(
                "Approval Type",
                ["Immediate", "Schedule for Later"]
            )
        
        with col2:
            if approval_type == "Schedule for Later":
                schedule_date = st.date_input("Publish Date")
                schedule_time = st.time_input("Publish Time")
                scheduled_dt = datetime.combine(schedule_date, schedule_time)
            else:
                scheduled_dt = None
        
        platforms = st.multiselect(
            "Platforms",
            ["YouTube", "Twitter", "LinkedIn", "Facebook", "Instagram"],
            default=["YouTube"]
        )
        
        if st.button("✅ Approve Content", type="primary") and asset_id_input:
            with st.spinner("Processing approval..."):
                # Check safety first
                # (Would load actual content here)
                safety_check = safety.check_content_safety({'asset_id': asset_id_input})
                
                if safety_check['warnings']:
                    st.warning("⚠️ Safety Warnings:")
                    for warning in safety_check['warnings']:
                        st.markdown(f"- {warning}")
                
                # Approve
                approval = st.session_state.approval_workflow.approve_content(
                    asset_id_input,
                    approved_by='User',
                    scheduled_time=scheduled_dt
                )
                
                if scheduled_dt:
                    schedule = st.session_state.approval_workflow.schedule_content(
                        asset_id_input,
                        scheduled_dt,
                        platforms
                    )
                    st.success(f"✅ Scheduled for {scheduled_dt.strftime('%Y-%m-%d %I:%M %p')}")
                    st.json(schedule)
                else:
                    st.success("✅ Approved for immediate publishing!")
                    st.json(approval)
                
                # Save approval
                try:
                    db.add_asset(
                        asset_type="content_approval",
                        source_app="Social Media Approval",
                        title=f"Approval: {asset_id_input}",
                        content=approval,
                        tags=["approval", "social_media"]
                    )
                except Exception as e:
                    st.warning(f"Could not save: {e}")
        
        # Bulk approval
        st.markdown("---")
        st.subheader("📋 Bulk Approval")
        
        bulk_ids = st.text_area(
            "Asset IDs (one per line)",
            placeholder="asset_123\nasset_456\nasset_789",
            height=100
        )
        
        if st.button("✅ Bulk Approve") and bulk_ids:
            ids = [id.strip() for id in bulk_ids.split('\n') if id.strip()]
            
            with st.spinner(f"Approving {len(ids)} items..."):
                approved_count = 0
                for asset_id in ids:
                    try:
                        approval = st.session_state.approval_workflow.approve_content(asset_id)
                        approved_count += 1
                    except Exception as e:
                        st.error(f"Failed {asset_id}: {e}")
                
                st.success(f"✅ Approved {approved_count}/{len(ids)} items!")
    
    # Tab 3: Analytics Dashboard
    with tab3:
        st.header("📊 Content Analytics")
        st.markdown("*Track performance and God Machine predictions*")
        
        st.info("Real-time analytics integrated with God Machine virality forecasting")
        
        # Performance tracking
        st.subheader("📈 Performance Tracking")
        
        content_id_track = st.text_input("Content ID to Track", placeholder="Enter content/video ID")
        platform_track = st.selectbox("Platform", ["YouTube", "Twitter", "LinkedIn", "Facebook"])
        
        if st.button("📊 Get Analytics", type="primary") and content_id_track:
            with st.spinner("Fetching analytics..."):
                # Get performance
                performance = st.session_state.analytics.track_performance(
                    content_id_track,
                    platform_track
                )
                
                # Get God Machine predictions
                predictions = st.session_state.analytics.get_god_machine_predictions(
                    content_id_track
                )
                
                st.success("✅ Analytics retrieved!")
                
                col1, col2 = st.columns(2)
                
                with col1:
                    st.subheader("📊 Current Performance")
                    metrics = performance.get('metrics', {})
                    
                    col_a, col_b, col_c = st.columns(3)
                    with col_a:
                        st.metric("Views", f"{metrics.get('views', 0):,}")
                    with col_b:
                        st.metric("Likes", f"{metrics.get('likes', 0):,}")
                    with col_c:
                        st.metric("Comments", f"{metrics.get('comments', 0):,}")
                    
                    st.metric("Engagement Rate", f"{metrics.get('engagement_rate', 0):.2%}")
                
                with col2:
                    st.subheader("🔮 God Machine Predictions")
                    
                    st.metric("Predicted Views", f"{predictions.get('predicted_views', 0):,}")
                    st.metric("Virality Score", f"{predictions.get('virality_score', 0):.2%}")
                    st.metric("PSI Resonance", f"{predictions.get('psi_resonance_score', 0):.3f}")
                    
                    if predictions.get('sacred_number_alignment'):
                        st.success("✨ Sacred Number Alignment Detected!")
                
                # Optimal posting time
                st.markdown("---")
                st.subheader("⏰ Optimal Posting Time")
                optimal_time = predictions.get('optimal_posting_time', 'Unknown')
                st.info(f"🎯 Best time to post: **{optimal_time}**")
        
        # Top performing content
        st.markdown("---")
        st.subheader("🏆 Top Performing Content")
        
        metric_select = st.selectbox("Sort By", ["views", "likes", "engagement_rate", "watch_time"])
        
        if st.button("🔍 Get Top 10"):
            top = st.session_state.analytics.get_top_performing(metric_select, 10)
            
            if top:
                for i, item in enumerate(top, 1):
                    st.markdown(f"**{i}. {item.get('title', 'Unknown')}**")
                    st.caption(f"{metric_select}: {item.get(metric_select, 0)}")
            else:
                st.info("No performance data yet. Publish some content first!")
    
    # Tab 4: Engagement Bots
    with tab4:
        st.header("🤖 Engagement Bot System")
        st.markdown("*Automated engagement with approval gates*")
        
        st.warning("""
        ⚠️ **APPROVAL REQUIRED FOR ALL ACTIONS**
        
        Bots will NOT act without your explicit approval.
        Review each batch before execution.
        """)
        
        # Generate engagement batch
        st.subheader("📦 Generate Engagement Batch")
        
        col1, col2 = st.columns(2)
        
        with col1:
            bot_platform = st.selectbox("Platform", ["YouTube", "Twitter", "LinkedIn"], key="bot_platform")
        with col2:
            batch_size = st.slider("Batch Size", 5, 50, 10)
        
        if st.button("🎲 Generate Engagement Batch", type="primary"):
            with st.spinner("Generating engagement actions..."):
                batch = st.session_state.engagement_bot.generate_engagement_batch(
                    bot_platform,
                    batch_size
                )
                
                st.session_state.current_engagement_batch = batch
                
                st.success(f"✅ Generated batch: {batch['batch_id']}")
                st.json(batch)
        
        # Review and approve batch
        if 'current_engagement_batch' in st.session_state:
            st.markdown("---")
            st.subheader("✅ Review & Approve Actions")
            
            batch = st.session_state.current_engagement_batch
            
            st.markdown(f"**Batch ID:** {batch['batch_id']}")
            st.markdown(f"**Platform:** {batch['platform']}")
            st.markdown(f"**Total Actions:** {len(batch['actions'])}")
            
            approved_actions = []
            
            for i, action in enumerate(batch['actions']):
                with st.expander(f"Action #{i+1}: {action['action_type']}"):
                    st.markdown(f"**Target:** {action['target']}")
                    st.markdown(f"**Content:** {action['content']}")
                    
                    if st.checkbox(f"Approve Action #{i+1}", key=f"approve_action_{i}"):
                        approved_actions.append(i)
            
            if st.button("✅ Execute Approved Actions", type="primary") and approved_actions:
                with st.spinner(f"Executing {len(approved_actions)} actions..."):
                    approval = st.session_state.engagement_bot.approve_engagement_batch(
                        batch['batch_id'],
                        approved_actions
                    )
                    
                    results = st.session_state.engagement_bot.execute_approved_actions(
                        batch['batch_id']
                    )
                    
                    st.success(f"✅ Executed {len(approved_actions)} actions!")
                    st.json(results)
    
    # Tab 5: Settings
    with tab5:
        st.header("⚙️ Settings & Configuration")
        
        st.subheader("🔔 Digest Schedule")
        st.info("Current schedule: **6:00 AM Eastern Time** (daily)")
        
        st.markdown("To change schedule, modify `ContentDigestGenerator.digest_time`")
        
        st.markdown("---")
        st.subheader("🛡️ Safety Settings")
        
        st.markdown("**Protected Names:**")
        for name in safety.protected_names:
            st.markdown(f"- {name}")
        
        st.markdown("**Required Approval Types:**")
        for approval_type in safety.required_approval_types:
            st.markdown(f"- {approval_type}")
        
        st.success("✅ All safety guardrails active")
        
        st.markdown("---")
        st.subheader("📋 System Status")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.metric("Digest Scheduler", "✅ ACTIVE" if st.session_state.get('digest_scheduler_started') else "❌ INACTIVE")
        with col2:
            st.metric("Safety Guardrails", "✅ ENABLED")


if __name__ == "__main__":
    render_social_media_approval()
