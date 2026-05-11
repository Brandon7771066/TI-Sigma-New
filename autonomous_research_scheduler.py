"""
24/7 Autonomous Research Scheduler
True background LHF (Low-Hanging Fruit) research system
Runs continuously, generates discoveries, saves to database
"""

import logging
import hashlib
from datetime import datetime, timedelta
from typing import Dict, Any, List, Optional
import random
from apscheduler.schedulers.background import BackgroundScheduler
from cosmic_ai_band_discoveries import CosmicAIBand
from db_utils import db

# Pass-44 dedup constants
DEDUP_LOOKBACK_DAYS = 7      # Reject titles seen in this window
DEDUP_MAX_RETRIES = 10       # Try up to 10 candidates before giving up
DEDUP_TITLE_HASH_TABLE_TTL = 300  # Refresh recent-titles cache every 5 min

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class AutonomousResearchScheduler:
    """
    24/7 background research system
    Generates discoveries every N hours automatically
    """
    
    def __init__(self, discovery_interval_hours: int = 4):
        """
        Args:
            discovery_interval_hours: How often to generate new discoveries
        """
        self.discovery_interval_hours = discovery_interval_hours
        self.cosmic_band = CosmicAIBand()
        self.scheduler = BackgroundScheduler()
        self.running = False
        self.last_discovery_time = None
        
    def _recent_title_hashes(self) -> set:
        """Pull title-hashes seen in last DEDUP_LOOKBACK_DAYS days from DB.
        Returns set of sha256(title)[:16] strings. Best-effort: any DB error
        returns empty set so dedup degrades gracefully (we still write)."""
        try:
            import psycopg2, os
            conn = psycopg2.connect(os.environ["DATABASE_URL"])
            cur = conn.cursor()
            cur.execute(
                "SELECT title FROM research_assets "
                "WHERE asset_type='autonomous_discovery' "
                "AND created_at > NOW() - INTERVAL %s",
                (f"{DEDUP_LOOKBACK_DAYS} days",))
            hashes = {hashlib.sha256(r[0].encode()).hexdigest()[:16]
                      for r in cur.fetchall()}
            cur.close(); conn.close()
            return hashes
        except Exception as e:
            logger.warning(f"Dedup lookup failed (degrading gracefully): {e}")
            return set()

    def _pick_novel_discovery(self) -> Optional[Dict[str, Any]]:
        """Sample up to DEDUP_MAX_RETRIES discoveries; return the first
        whose title-hash is NOT in the recent-titles set. Returns None if
        every sample collides (means corpus is truly exhausted right now)."""
        discoveries = self.cosmic_band.get_overnight_discoveries()
        if not discoveries:
            return None
        recent = self._recent_title_hashes()
        random.shuffle(discoveries)
        for cand in discoveries[:DEDUP_MAX_RETRIES]:
            h = hashlib.sha256(cand['title'].encode()).hexdigest()[:16]
            if h not in recent:
                return cand
        # All sampled discoveries are duplicates within lookback window
        return None

    def generate_and_save_discovery(self) -> Dict[str, Any]:
        """
        Generate one discovery and save to database (with Pass-44 dedup).

        Returns:
            Discovery object, or skip-marker dict if all candidates were dupes.
        """
        logger.info("🔍 Generating new autonomous discovery...")

        # Pass-44 dedup: pick a title we have NOT used in last 7 days
        discovery = self._pick_novel_discovery()
        if discovery is None:
            logger.info(
                f"⏭️  All {DEDUP_MAX_RETRIES} candidate discoveries were "
                f"duplicates within last {DEDUP_LOOKBACK_DAYS} days. "
                f"Skipping this cycle (corpus saturation). "
                f"Add new templates to CosmicAIBand to resume novelty.")
            return {"skipped": True, "reason": "all_candidates_recent_dupes"}

        # Add metadata
        discovery['generated_by'] = 'autonomous_scheduler'
        discovery['discovery_id'] = f"auto_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        # Save to database
        try:
            asset_id = db.add_asset(
                asset_type="autonomous_discovery",
                source_app="24/7 Research Scheduler",
                title=discovery['title'],
                content=discovery,
                tags=[
                    "autonomous",
                    "24_7_research",
                    "cosmic_ai_band",
                    discovery['research_area']
                ]
            )
            
            discovery['asset_id'] = asset_id
            logger.info(f"✅ Discovery saved! Asset ID: {asset_id}")
            logger.info(f"📊 Title: {discovery['title']}")
            logger.info(f"🎯 Confidence: {discovery['confidence']:.0%}")
            
        except Exception as e:
            logger.error(f"❌ Failed to save discovery: {e}")
            discovery['asset_id'] = None
        
        self.last_discovery_time = datetime.now()
        return discovery
    
    def should_generate_discovery(self) -> bool:
        """Check if it's time to generate a new discovery"""
        if self.last_discovery_time is None:
            return True
        
        time_since_last = datetime.now() - self.last_discovery_time
        threshold = timedelta(hours=self.discovery_interval_hours)
        
        return time_since_last >= threshold
    
    def run_once(self) -> Dict[str, Any]:
        """
        Run one iteration of the research cycle
        
        Returns:
            Discovery if generated, None if not time yet
        """
        if self.should_generate_discovery():
            return self.generate_and_save_discovery()
        else:
            time_until_next = self.discovery_interval_hours - \
                (datetime.now() - self.last_discovery_time).total_seconds() / 3600
            logger.info(f"⏰ Next discovery in {time_until_next:.1f} hours")
            return None
    
    def start(self):
        """
        Start the background scheduler
        Non-blocking! Runs in background thread automatically
        """
        if self.running:
            logger.warning("⚠️ Scheduler already running!")
            return
        
        logger.info("🚀 Starting 24/7 autonomous research scheduler...")
        logger.info(f"⏰ Discovery interval: {self.discovery_interval_hours} hours")
        
        # Generate first discovery immediately
        self.generate_and_save_discovery()
        
        # Schedule recurring discoveries
        self.scheduler.add_job(
            self.generate_and_save_discovery,
            'interval',
            hours=self.discovery_interval_hours,
            id='autonomous_discovery',
            replace_existing=True
        )
        
        # Start the scheduler (non-blocking)
        self.scheduler.start()
        self.running = True
        
        logger.info("✅ 24/7 scheduler started successfully! Running in background...")
    
    def stop(self):
        """Stop the scheduler"""
        if not self.running:
            logger.warning("⚠️ Scheduler not running!")
            return
        
        logger.info("🛑 Stopping autonomous research scheduler...")
        self.scheduler.shutdown(wait=False)
        self.running = False
        logger.info("✅ Scheduler stopped")
    
    def is_running(self) -> bool:
        """Check if scheduler is active"""
        return self.running and self.scheduler.running


class DiscoveryManager:
    """
    Manage and retrieve autonomous discoveries
    """
    
    @staticmethod
    def get_recent_discoveries(limit: int = 10) -> List[Dict[str, Any]]:
        """Get most recent autonomous discoveries"""
        assets = db.get_assets_by_type("autonomous_discovery")
        
        # Sort by created_at descending
        sorted_assets = sorted(
            assets,
            key=lambda x: x.get('created_at', ''),
            reverse=True
        )
        
        return sorted_assets[:limit]
    
    @staticmethod
    def get_discoveries_by_area(research_area: str) -> List[Dict[str, Any]]:
        """Get discoveries filtered by research area"""
        all_discoveries = DiscoveryManager.get_recent_discoveries(limit=100)
        
        filtered = [
            d for d in all_discoveries
            if d.get('content', {}).get('research_area') == research_area
        ]
        
        return filtered
    
    @staticmethod
    def get_high_confidence_discoveries(min_confidence: float = 0.8) -> List[Dict[str, Any]]:
        """Get discoveries above confidence threshold"""
        all_discoveries = DiscoveryManager.get_recent_discoveries(limit=100)
        
        filtered = [
            d for d in all_discoveries
            if d.get('content', {}).get('confidence', 0) >= min_confidence
        ]
        
        # Sort by confidence descending
        return sorted(
            filtered,
            key=lambda x: x.get('content', {}).get('confidence', 0),
            reverse=True
        )
    
    @staticmethod
    def get_paper_worthy_discoveries() -> List[Dict[str, Any]]:
        """Get discoveries with HIGH or EXTREME paper potential"""
        all_discoveries = DiscoveryManager.get_recent_discoveries(limit=100)
        
        paper_worthy = [
            d for d in all_discoveries
            if 'HIGH' in d.get('content', {}).get('paper_potential', '')
            or 'EXTREME' in d.get('content', {}).get('paper_potential', '')
        ]
        
        return paper_worthy


# Global scheduler instance
_global_scheduler = None


def get_scheduler() -> AutonomousResearchScheduler:
    """Get or create global scheduler instance"""
    global _global_scheduler
    
    if _global_scheduler is None:
        _global_scheduler = AutonomousResearchScheduler(discovery_interval_hours=4)
    
    return _global_scheduler


def start_background_research():
    """
    Start 24/7 background research
    Non-blocking! Runs in background thread
    """
    scheduler = get_scheduler()
    
    if not scheduler.is_running():
        scheduler.start()
        logger.info("✅ Background research started!")
    else:
        logger.info("ℹ️ Background research already running")
    
    return scheduler


if __name__ == "__main__":
    # Run standalone for testing
    import time
    
    print("🚀 Starting 24/7 Autonomous Research Scheduler...")
    print("⚡ Generating discoveries every 4 hours")
    print("💾 Saving to database automatically")
    print("🛑 Press Ctrl+C to stop\n")
    
    scheduler = start_background_research()
    
    try:
        # Keep main thread alive
        while True:
            time.sleep(60)
    except KeyboardInterrupt:
        print("\n⏸️ Shutting down...")
        scheduler.stop()
