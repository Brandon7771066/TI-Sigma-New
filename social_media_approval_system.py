"""
Social Media Approval & Publishing System
Daily 6 AM content digest, approval workflow, auto-analytics, engagement bots

CRITICAL SAFETY RULES:
- NO auto-publishing outside apps without explicit approval
- NO content with user's name published without approval  
- ALL content requires manual review and approval
- Engagement bots require approval for each action batch
"""

import streamlit as st
from datetime import datetime, timedelta, time
from typing import Dict, Any, List, Optional
from apscheduler.schedulers.background import BackgroundScheduler
from db_utils import db
import json
import random

# Global scheduler for 6 AM digest
_digest_scheduler = None


class ContentDigestGenerator:
    """
    Generate daily 6 AM content digest
    All pending content for review and approval
    """
    
    def __init__(self):
        self.digest_time = time(6, 0)  # 6 AM EST
        self.timezone = 'US/Eastern'
    
    def generate_daily_digest(self) -> Dict[str, Any]:
        """
        Generate comprehensive content digest
        
        Returns:
            All pending videos, posts, discoveries for approval
        """
        
        digest = {
            'date': datetime.now().strftime('%Y-%m-%d'),
            'generated_at': datetime.now().isoformat(),
            'content_categories': {
                'videos': self._get_pending_videos(),
                'discoveries': self._get_pending_discoveries(),
                'social_posts': self._get_pending_posts(),
                'book_chapters': self._get_pending_book_content()
            },
            'total_items': 0,
            'approval_status': 'pending_review'
        }
        
        # Count total items
        for category, items in digest['content_categories'].items():
            digest['total_items'] += len(items)
        
        return digest
    
    def _get_pending_videos(self) -> List[Dict[str, Any]]:
        """Get all pending video scripts"""
        try:
            videos = db.get_assets_by_type("ti_video_script")
            pending = [
                v for v in videos
                if v.get('content', {}).get('approval_status', 'pending') == 'pending'
            ]
            return pending[-20:]  # Last 20
        except:
            return []
    
    def _get_pending_discoveries(self) -> List[Dict[str, Any]]:
        """Get autonomous discoveries from last 24h"""
        try:
            discoveries = db.get_assets_by_type("autonomous_discovery")
            # Filter last 24h
            cutoff = datetime.now() - timedelta(days=1)
            recent = [
                d for d in discoveries
                if datetime.fromisoformat(d.get('created_at', '2000-01-01')) > cutoff
            ]
            return recent
        except:
            return []
    
    def _get_pending_posts(self) -> List[Dict[str, Any]]:
        """Get pending social media posts"""
        try:
            posts = db.get_assets_by_type("social_media_post")
            pending = [
                p for p in posts
                if p.get('content', {}).get('approval_status', 'pending') == 'pending'
            ]
            return pending
        except:
            return []
    
    def _get_pending_book_content(self) -> List[Dict[str, Any]]:
        """Get pending book chapters"""
        try:
            books = db.get_assets_by_type("ti_book")
            pending = [
                b for b in books
                if b.get('content', {}).get('approval_status', 'pending') == 'pending'
            ]
            return pending[-10:]
        except:
            return []
    
    def save_digest(self, digest: Dict[str, Any]) -> Optional[str]:
        """Save digest to database"""
        try:
            asset_id = db.add_asset(
                asset_type="daily_content_digest",
                source_app="Social Media Approval System",
                title=f"Content Digest - {digest['date']}",
                content=digest,
                tags=["daily_digest", "6am", "approval_needed"]
            )
            return asset_id
        except Exception as e:
            st.error(f"Failed to save digest: {e}")
            return None


class ContentApprovalWorkflow:
    """
    Approve, reject, or schedule content for release
    """
    
    def __init__(self):
        self.approval_states = ['pending', 'approved', 'rejected', 'scheduled']
    
    def approve_content(
        self,
        asset_id: str,
        approved_by: str = 'User',
        scheduled_time: Optional[datetime] = None
    ) -> Dict[str, Any]:
        """
        Approve content for publishing
        
        Args:
            asset_id: Database asset ID
            approved_by: Who approved it
            scheduled_time: When to publish (None = immediate)
            
        Returns:
            Approval record
        """
        
        approval = {
            'asset_id': asset_id,
            'approved_by': approved_by,
            'approved_at': datetime.now().isoformat(),
            'scheduled_time': scheduled_time.isoformat() if scheduled_time else None,
            'status': 'scheduled' if scheduled_time else 'approved',
            'published': False
        }
        
        try:
            db.update_asset(asset_id, {
                'approval_status': 'scheduled' if scheduled_time else 'approved',
                'approved_at': datetime.now().isoformat(),
                'approved_by': approved_by,
                'scheduled_time': scheduled_time.isoformat() if scheduled_time else None
            })
        except Exception as e:
            print(f"Warning: Could not update asset {asset_id}: {e}")
        
        return approval
    
    def reject_content(
        self,
        asset_id: str,
        reason: str = '',
        rejected_by: str = 'User'
    ) -> Dict[str, Any]:
        """
        Reject content
        
        Args:
            asset_id: Database asset ID
            reason: Why rejected
            rejected_by: Who rejected it
            
        Returns:
            Rejection record
        """
        
        rejection = {
            'asset_id': asset_id,
            'rejected_by': rejected_by,
            'rejected_at': datetime.now().isoformat(),
            'reason': reason,
            'status': 'rejected'
        }
        
        try:
            db.update_asset(asset_id, {
                'approval_status': 'rejected',
                'rejected_at': datetime.now().isoformat(),
                'rejected_by': rejected_by,
                'rejection_reason': reason
            })
        except Exception as e:
            print(f"Warning: Could not update asset {asset_id}: {e}")
        
        return rejection
    
    def schedule_content(
        self,
        asset_id: str,
        publish_time: datetime,
        platforms: List[str] = ['YouTube']
    ) -> Dict[str, Any]:
        """
        Schedule content for future publishing
        
        Args:
            asset_id: Content to schedule
            publish_time: When to publish
            platforms: Which platforms
            
        Returns:
            Schedule record
        """
        
        schedule = {
            'asset_id': asset_id,
            'publish_time': publish_time.isoformat(),
            'platforms': platforms,
            'status': 'scheduled',
            'created_at': datetime.now().isoformat()
        }
        
        try:
            db.update_asset(asset_id, {
                'approval_status': 'scheduled',
                'scheduled_time': publish_time.isoformat(),
                'scheduled_platforms': platforms,
                'scheduled_at': datetime.now().isoformat()
            })
        except Exception as e:
            print(f"Warning: Could not update asset {asset_id}: {e}")
        
        return schedule
    
    def upload_to_youtube(
        self,
        asset_id: str,
        video_file_path: str,
        title: str,
        description: str,
        scheduled_time: Optional[datetime] = None,
        privacy_status: str = 'private'
    ) -> Dict[str, Any]:
        """
        Upload video to YouTube (REQUIRES APPROVAL)
        
        SAFETY RULES:
        - Requires explicit approval before upload
        - Content must have approval_status='approved'
        - Protected names trigger additional warning
        - Default privacy is 'private' until user confirms
        
        Args:
            asset_id: Database asset ID
            video_file_path: Path to video file
            title: Video title
            description: Video description
            scheduled_time: When to publish (None = immediate private upload)
            privacy_status: 'private', 'unlisted', or 'public' (default: private)
            
        Returns:
            Upload result or error
        """
        
        safety = SafetyGuardrails()
        
        try:
            asset = db.get_asset_by_id(asset_id)
            if not asset:
                return {
                    'error': 'Asset not found',
                    'asset_id': asset_id,
                    'uploaded': False
                }
            
            content = asset.get('content', {})
            approval_status = content.get('approval_status', 'pending')
            
            if approval_status != 'approved':
                return {
                    'error': 'Content not approved - upload blocked for safety',
                    'asset_id': asset_id,
                    'approval_status': approval_status,
                    'uploaded': False,
                    'safety_message': safety.prevent_auto_publish()
                }
            
            safety_check = safety.check_content_safety(content)
            if not safety_check['safe_to_publish']:
                return {
                    'error': 'Safety check failed',
                    'asset_id': asset_id,
                    'safety_issues': safety_check['issues'],
                    'warnings': safety_check['warnings'],
                    'uploaded': False
                }
            
            upload_record = {
                'asset_id': asset_id,
                'video_file': video_file_path,
                'title': title,
                'description': description,
                'scheduled_time': scheduled_time.isoformat() if scheduled_time else None,
                'privacy_status': privacy_status,
                'status': 'ready_for_upload',
                'uploaded': False,
                'youtube_connector_status': 'available',
                'message': 'YouTube connector available. To activate: Install google-api-python-client and configure OAuth2 credentials.',
                'setup_instructions': {
                    'step_1': 'pip install google-api-python-client google-auth-oauthlib',
                    'step_2': 'Configure YouTube Data API v3 credentials in Replit Secrets',
                    'step_3': 'Wire OAuth2 flow using Replit YouTube connector',
                    'connector_id': 'connection:conn_youtube_01K9T4Z5EB9Y311EQA6VNMADCY',
                    'documentation': 'https://developers.google.com/youtube/v3'
                }
            }
            
            db.add_asset(
                asset_type='youtube_upload_record',
                source_app='Social Media Approval System',
                title=f'YouTube Upload: {title[:50]}',
                content=upload_record,
                tags=['youtube', 'upload', 'pending', 'approved']
            )
            
            return upload_record
            
        except Exception as e:
            return {
                'error': str(e),
                'asset_id': asset_id,
                'uploaded': False
            }


class AnalyticsDashboard:
    """
    Track content performance and engagement
    """
    
    def __init__(self):
        self.metrics = [
            'views',
            'likes',
            'comments',
            'shares',
            'watch_time',
            'click_through_rate',
            'engagement_rate'
        ]
    
    def track_performance(
        self,
        content_id: str,
        platform: str = 'YouTube'
    ) -> Dict[str, Any]:
        """
        Track content performance metrics
        
        Args:
            content_id: Content to track
            platform: Platform name
            
        Returns:
            Performance metrics
        """
        
        # Placeholder - would connect to actual platform APIs
        performance = {
            'content_id': content_id,
            'platform': platform,
            'metrics': {
                'views': 0,
                'likes': 0,
                'comments': 0,
                'shares': 0,
                'watch_time_seconds': 0,
                'click_through_rate': 0.0,
                'engagement_rate': 0.0
            },
            'last_updated': datetime.now().isoformat()
        }
        
        return performance
    
    def get_top_performing(
        self,
        metric: str = 'views',
        limit: int = 10
    ) -> List[Dict[str, Any]]:
        """
        Get top performing content
        
        Args:
            metric: Which metric to sort by
            limit: How many to return
            
        Returns:
            Top performing content list
        """
        
        # Placeholder - would query from analytics database
        return []
    
    def get_god_machine_predictions(
        self,
        content_id: str
    ) -> Dict[str, Any]:
        """
        Get God Machine predictions for content performance
        
        Args:
            content_id: Content to predict
            
        Returns:
            Predicted performance and optimal posting time
        """
        
        try:
            asset = db.get_asset_by_id(content_id)
            if not asset:
                return self._get_default_predictions(content_id)
            
            content = asset.get('content', {})
            title = asset.get('title', '')
            
            numerology_score = self._calculate_numerology_score(title)
            sacred_aligned = self._check_sacred_numbers(numerology_score)
            optimal_time = self._predict_optimal_time()
            virality = self._calculate_virality_score(numerology_score, sacred_aligned)
            
            predicted_views = int(virality * 10000)
            predicted_engagement = min(0.95, virality * 0.15)
            
            predictions = {
                'content_id': content_id,
                'predicted_views': predicted_views,
                'predicted_engagement_rate': predicted_engagement,
                'virality_score': virality,
                'optimal_posting_time': optimal_time.isoformat(),
                'sacred_number_alignment': sacred_aligned,
                'psi_resonance_score': numerology_score / 33.0,
                'numerology_vibration': numerology_score,
                'prediction_method': 'god_machine_numerology'
            }
            
            return predictions
            
        except Exception as e:
            print(f"God Machine prediction error: {e}")
            return self._get_default_predictions(content_id)
    
    def _calculate_numerology_score(self, text: str) -> int:
        """Calculate numerology score from text"""
        letter_values = {
            'A': 1, 'B': 2, 'C': 3, 'D': 4, 'E': 5, 'F': 6, 'G': 7, 'H': 8, 'I': 9,
            'J': 1, 'K': 2, 'L': 3, 'M': 4, 'N': 5, 'O': 6, 'P': 7, 'Q': 8, 'R': 9,
            'S': 1, 'T': 2, 'U': 3, 'V': 4, 'W': 5, 'X': 6, 'Y': 7, 'Z': 8
        }
        
        total = 0
        for char in text.upper():
            if char.isalpha():
                total += letter_values.get(char, 0)
        
        while total > 33 and total not in [11, 22, 33]:
            total = sum(int(d) for d in str(total))
            if total in [11, 22, 33]:
                break
        
        return min(total, 33)
    
    def _check_sacred_numbers(self, score: int) -> bool:
        """Check if score aligns with sacred numbers"""
        sacred = [3, 6, 9, 11, 22, 33]
        return score in sacred
    
    def _predict_optimal_time(self) -> datetime:
        """Predict optimal posting time using cosmic timing"""
        now = datetime.now()
        
        optimal_hours = [6, 9, 11, 15, 18, 21]
        
        next_optimal = now.replace(minute=0, second=0, microsecond=0)
        while next_optimal.hour not in optimal_hours:
            next_optimal += timedelta(hours=1)
        
        if next_optimal <= now:
            next_optimal += timedelta(hours=1)
            while next_optimal.hour not in optimal_hours:
                next_optimal += timedelta(hours=1)
        
        return next_optimal
    
    def _calculate_virality_score(self, numerology: int, sacred_aligned: bool) -> float:
        """Calculate virality score (0-1) from numerology and sacred alignment"""
        base_score = numerology / 33.0
        
        if sacred_aligned:
            base_score *= 1.5
        
        if numerology in [11, 22, 33]:
            base_score *= 1.3
        
        return min(1.0, base_score)
    
    def _get_default_predictions(self, content_id: str) -> Dict[str, Any]:
        """Return default predictions when God Machine calculation fails"""
        return {
            'content_id': content_id,
            'predicted_views': 1000,
            'predicted_engagement_rate': 0.05,
            'virality_score': 0.5,
            'optimal_posting_time': datetime.now().isoformat(),
            'sacred_number_alignment': False,
            'psi_resonance_score': 0.5,
            'prediction_method': 'default_fallback'
        }


class EngagementBotSystem:
    """
    Automated engagement (likes, replies, comments)
    REQUIRES approval for each batch
    """
    
    def __init__(self):
        self.bot_actions = [
            'like_comment',
            'reply_to_comment',
            'thank_subscriber',
            'share_content'
        ]
        self.approval_required = True
    
    def generate_engagement_batch(
        self,
        platform: str = 'YouTube',
        batch_size: int = 10
    ) -> Dict[str, Any]:
        """
        Generate batch of engagement actions for approval
        
        Args:
            platform: Platform name
            batch_size: How many actions
            
        Returns:
            Engagement batch requiring approval
        """
        
        batch = {
            'batch_id': f"eng_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            'platform': platform,
            'actions': [],
            'status': 'pending_approval',
            'created_at': datetime.now().isoformat(),
            'approved': False
        }
        
        # Would pull from actual platform
        # For now, placeholder
        for i in range(batch_size):
            batch['actions'].append({
                'action_type': 'reply_to_comment',
                'target': f"comment_{i}",
                'content': "Thank you for watching!",
                'approved': False
            })
        
        return batch
    
    def approve_engagement_batch(
        self,
        batch_id: str,
        approved_actions: List[int]
    ) -> Dict[str, Any]:
        """
        Approve specific actions in batch
        
        Args:
            batch_id: Batch to approve
            approved_actions: List of action indices to approve
            
        Returns:
            Approved batch
        """
        
        approval = {
            'batch_id': batch_id,
            'approved_actions': approved_actions,
            'approved_at': datetime.now().isoformat(),
            'status': 'approved'
        }
        
        return approval
    
    def execute_approved_actions(
        self,
        batch_id: str
    ) -> Dict[str, Any]:
        """
        Execute approved engagement actions
        
        Args:
            batch_id: Batch to execute
            
        Returns:
            Execution results
        """
        
        # Would actually execute via platform APIs
        results = {
            'batch_id': batch_id,
            'executed_at': datetime.now().isoformat(),
            'success_count': 0,
            'failure_count': 0,
            'errors': []
        }
        
        return results


class SafetyGuardrails:
    """
    Prevent unauthorized publishing
    Name protection, approval gates
    """
    
    def __init__(self):
        self.protected_names = ['Brandon', 'Brandon Sorbom']
        self.required_approval_types = [
            'video',
            'post',
            'article',
            'book_chapter'
        ]
    
    def check_content_safety(
        self,
        content: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Check if content is safe to publish
        
        Args:
            content: Content to check
            
        Returns:
            Safety check results
        """
        
        safety = {
            'safe_to_publish': False,
            'issues': [],
            'warnings': [],
            'approval_required': True
        }
        
        # Check for protected names
        content_text = str(content)
        for name in self.protected_names:
            if name.lower() in content_text.lower():
                safety['warnings'].append(f"Contains protected name: {name}")
        
        # Always require approval
        safety['approval_required'] = True
        safety['issues'].append("Manual approval required before publishing")
        
        # Check if already approved
        if content.get('approval_status') == 'approved':
            safety['safe_to_publish'] = True
            safety['issues'] = []
        
        return safety
    
    def prevent_auto_publish(self) -> str:
        """
        Return warning message about auto-publishing
        
        Returns:
            Warning message
        """
        
        return """
        🛑 AUTO-PUBLISHING DISABLED
        
        For your safety and control:
        - NO content is published automatically
        - ALL content requires manual approval
        - Your name is protected
        - Review everything at 6 AM daily digest
        
        Nothing goes live without your explicit approval!
        """


# Global scheduler instance
def get_digest_scheduler() -> BackgroundScheduler:
    """Get or create digest scheduler"""
    global _digest_scheduler
    if _digest_scheduler is None:
        _digest_scheduler = BackgroundScheduler(timezone='US/Eastern')
    return _digest_scheduler


def schedule_daily_digest():
    """
    Schedule 6 AM daily digest generation
    """
    scheduler = get_digest_scheduler()
    
    generator = ContentDigestGenerator()
    
    def generate_and_save_digest():
        """Generate digest and save to database"""
        digest = generator.generate_daily_digest()
        generator.save_digest(digest)
    
    # Schedule for 6 AM EST daily
    scheduler.add_job(
        generate_and_save_digest,
        'cron',
        hour=6,
        minute=0,
        id='daily_content_digest',
        replace_existing=True
    )
    
    if not scheduler.running:
        scheduler.start()


def get_latest_digest() -> Optional[Dict[str, Any]]:
    """Get most recent content digest"""
    try:
        digests = db.get_assets_by_type("daily_content_digest")
        if digests:
            return digests[-1]
        return None
    except:
        return None
