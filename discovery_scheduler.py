"""
APScheduler-based 24/7 Discovery Engine
========================================
Runs autonomous math discovery in background independent of Streamlit
"""

import os
from apscheduler.schedulers.background import BackgroundScheduler
from apscheduler.triggers.interval import IntervalTrigger
from datetime import datetime
import logging

from autonomous_math_discovery_production import get_production_system

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global scheduler instance
_scheduler = None

def run_discovery_job():
    """Job function that generates one discovery"""
    try:
        system = get_production_system()
        
        # Pick random domain
        import random
        domain = random.choice(system.domains)
        
        logger.info(f"🔬 Generating discovery for {domain}...")
        
        # Create discovery with REAL AI (will raise if GPT/Claude fail)
        discovery = system.create_discovery_with_ai(domain)
        
        # Save to database ONLY if discovery is valid
        system.save_to_database(discovery)
        
        logger.info(f"✨ Discovery created: {discovery.title}")
        logger.info(f"   God Machine: {discovery.god_machine_score:.3f} | MagAI: {discovery.mag_ai_consensus:.3f}")
        logger.info(f"   Status: REAL AI consensus achieved - safe to persist!")
        
    except Exception as e:
        logger.error(f"❌ Discovery job FAILED (will retry next cycle): {e}")
        logger.error(f"   This is CORRECT behavior - we refuse to persist fake discoveries!")

def start_discovery_scheduler(interval_minutes: int = 60):
    """
    Start background discovery scheduler
    
    Args:
        interval_minutes: How often to generate discoveries (default 60 min)
    """
    global _scheduler
    
    if _scheduler is not None and _scheduler.running:
        logger.warning("⚠️ Scheduler already running!")
        return
    
    _scheduler = BackgroundScheduler()
    
    # Add discovery job
    _scheduler.add_job(
        run_discovery_job,
        trigger=IntervalTrigger(minutes=interval_minutes),
        id='discovery_generator',
        name='Autonomous Math Discovery',
        replace_existing=True
    )
    
    _scheduler.start()
    logger.info(f"🚀 Discovery scheduler started! Generating every {interval_minutes} minutes")
    
    # Run one immediately
    run_discovery_job()

def stop_discovery_scheduler():
    """Stop background scheduler"""
    global _scheduler
    
    if _scheduler is not None and _scheduler.running:
        _scheduler.shutdown()
        logger.info("⏸️ Discovery scheduler stopped")
    else:
        logger.warning("⚠️ Scheduler not running")

def get_scheduler_status():
    """Get scheduler status"""
    global _scheduler
    
    if _scheduler is None:
        return {"running": False, "jobs": []}
    
    return {
        "running": _scheduler.running,
        "jobs": [
            {
                "id": job.id,
                "name": job.name,
                "next_run": job.next_run_time.isoformat() if job.next_run_time else None
            }
            for job in _scheduler.get_jobs()
        ]
    }
