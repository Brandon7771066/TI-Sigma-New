"""
PostgreSQL Setup for Discoveries
==================================
Migrate from JSON files to PostgreSQL long-term storage
"""

import os
import psycopg2
from psycopg2.extras import Json
import json
from datetime import datetime
from autonomous_math_discovery_production import get_production_system, MathDiscovery

DATABASE_URL = os.environ.get("DATABASE_URL")

class DiscoveryDatabase:
    """PostgreSQL storage for autonomous discoveries"""
    
    def __init__(self):
        self.conn = psycopg2.connect(DATABASE_URL)
        self.setup_schema()
    
    def setup_schema(self):
        """Create discoveries table if it doesn't exist"""
        with self.conn.cursor() as cur:
            cur.execute("""
                CREATE TABLE IF NOT EXISTS autonomous_discoveries (
                    id VARCHAR(255) PRIMARY KEY,
                    timestamp TIMESTAMP NOT NULL,
                    title TEXT NOT NULL,
                    discovery_type VARCHAR(100),
                    intuition TEXT,
                    formalization TEXT,
                    tralse_encoding TEXT,
                    god_machine_score FLOAT,
                    mag_ai_consensus FLOAT,
                    gpt5_analysis TEXT,
                    claude_analysis TEXT,
                    confidence FLOAT,
                    status VARCHAR(50),
                    tags JSON,
                    dependencies JSON,
                    empirical_validation JSON,
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            # Create indexes for common queries
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_discovery_type ON autonomous_discoveries(discovery_type)
            """)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_confidence ON autonomous_discoveries(confidence DESC)
            """)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_timestamp ON autonomous_discoveries(timestamp DESC)
            """)
            
            self.conn.commit()
        
        print("✅ PostgreSQL schema created/verified")
    
    def save_discovery(self, discovery: MathDiscovery):
        """Save discovery to PostgreSQL"""
        with self.conn.cursor() as cur:
            cur.execute("""
                INSERT INTO autonomous_discoveries (
                    id, timestamp, title, discovery_type, intuition,
                    formalization, tralse_encoding, god_machine_score,
                    mag_ai_consensus, gpt5_analysis, claude_analysis,
                    confidence, status, tags, dependencies, empirical_validation
                ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (id) DO UPDATE SET
                    title = EXCLUDED.title,
                    formalization = EXCLUDED.formalization,
                    tralse_encoding = EXCLUDED.tralse_encoding,
                    god_machine_score = EXCLUDED.god_machine_score,
                    mag_ai_consensus = EXCLUDED.mag_ai_consensus,
                    gpt5_analysis = EXCLUDED.gpt5_analysis,
                    claude_analysis = EXCLUDED.claude_analysis,
                    confidence = EXCLUDED.confidence,
                    status = EXCLUDED.status,
                    tags = EXCLUDED.tags,
                    dependencies = EXCLUDED.dependencies,
                    empirical_validation = EXCLUDED.empirical_validation
            """, (
                discovery.id,
                datetime.fromisoformat(discovery.timestamp),
                discovery.title,
                discovery.discovery_type,
                discovery.intuition,
                discovery.formalization,
                discovery.tralse_encoding,
                discovery.god_machine_score,
                discovery.mag_ai_consensus,
                discovery.gpt5_analysis,
                discovery.claude_analysis,
                discovery.confidence,
                discovery.status,
                Json(discovery.tags),
                Json(discovery.dependencies),
                Json(discovery.empirical_validation) if discovery.empirical_validation else None
            ))
            
            self.conn.commit()
    
    def load_all_discoveries(self):
        """Load all discoveries from PostgreSQL"""
        with self.conn.cursor() as cur:
            cur.execute("""
                SELECT * FROM autonomous_discoveries
                ORDER BY timestamp DESC
            """)
            
            rows = cur.fetchall()
            columns = [desc[0] for desc in cur.description]
            
            discoveries = []
            for row in rows:
                data = dict(zip(columns, row))
                # Convert back to MathDiscovery
                discovery = MathDiscovery(
                    id=data['id'],
                    timestamp=data['timestamp'].isoformat(),
                    title=data['title'],
                    discovery_type=data['discovery_type'],
                    intuition=data['intuition'],
                    formalization=data['formalization'],
                    tralse_encoding=data['tralse_encoding'],
                    god_machine_score=data['god_machine_score'],
                    mag_ai_consensus=data['mag_ai_consensus'],
                    gpt5_analysis=data['gpt5_analysis'],
                    claude_analysis=data['claude_analysis'],
                    confidence=data['confidence'],
                    status=data['status'],
                    tags=data['tags'] or [],
                    dependencies=data['dependencies'] or [],
                    empirical_validation=data['empirical_validation']
                )
                discoveries.append(discovery)
            
            return discoveries
    
    def migrate_from_json(self):
        """Migrate existing JSON discoveries to PostgreSQL"""
        system = get_production_system()
        system.discoveries = system.load_all_discoveries()
        
        print(f"📦 Migrating {len(system.discoveries)} discoveries to PostgreSQL...")
        
        for discovery in system.discoveries:
            self.save_discovery(discovery)
        
        print(f"✅ Migrated {len(system.discoveries)} discoveries!")


def setup_postgresql():
    """Main setup function"""
    print("=" * 70)
    print("🐘 SETTING UP POSTGRESQL FOR DISCOVERIES")
    print("=" * 70)
    
    db = DiscoveryDatabase()
    db.migrate_from_json()
    
    print("\n✅ PostgreSQL setup complete!")
    print("   - Schema created")
    print("   - Indexes created")
    print("   - Existing discoveries migrated")
    
    return db


if __name__ == "__main__":
    setup_postgresql()
