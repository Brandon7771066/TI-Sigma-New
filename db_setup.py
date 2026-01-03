"""
Database Setup Script for GM-Inspired Multi-App Architecture
Creates schema for cross-app communication
"""

import os
import psycopg2
from psycopg2.extensions import ISOLATION_LEVEL_AUTOCOMMIT

def get_db_connection():
    """Get database connection using Replit environment variables"""
    return psycopg2.connect(
        host=os.getenv('PGHOST'),
        database=os.getenv('PGDATABASE'),
        user=os.getenv('PGUSER'),
        password=os.getenv('PGPASSWORD'),
        port=os.getenv('PGPORT')
    )

def create_schema():
    """Create database schema for multi-app ecosystem"""
    
    conn = get_db_connection()
    conn.set_isolation_level(ISOLATION_LEVEL_AUTOCOMMIT)
    cur = conn.cursor()
    
    # Apps table - tracks all specialist apps
    cur.execute("""
        CREATE TABLE IF NOT EXISTS apps (
            app_id SERIAL PRIMARY KEY,
            app_name VARCHAR(100) UNIQUE NOT NULL,
            url VARCHAR(255),
            status VARCHAR(50) DEFAULT 'pending',
            last_heartbeat TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """)
    print("✅ Created 'apps' table")
    
    # Research assets - shared equations, papers, protocols, insights
    cur.execute("""
        CREATE TABLE IF NOT EXISTS research_assets (
            asset_id SERIAL PRIMARY KEY,
            asset_type VARCHAR(50) NOT NULL,
            source_app VARCHAR(100),
            title VARCHAR(255) NOT NULL,
            content JSONB,
            tags TEXT[],
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """)
    print("✅ Created 'research_assets' table")
    
    # Cross-app events
    cur.execute("""
        CREATE TABLE IF NOT EXISTS events (
            event_id SERIAL PRIMARY KEY,
            source_app VARCHAR(100) NOT NULL,
            event_type VARCHAR(100) NOT NULL,
            payload JSONB,
            timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """)
    print("✅ Created 'events' table")
    
    # User sessions
    cur.execute("""
        CREATE TABLE IF NOT EXISTS user_sessions (
            session_id SERIAL PRIMARY KEY,
            user_id VARCHAR(100),
            current_app VARCHAR(100),
            session_data JSONB,
            started_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            last_activity TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """)
    print("✅ Created 'user_sessions' table")
    
    # Master index - cross-reference between concepts and resources
    cur.execute("""
        CREATE TABLE IF NOT EXISTS master_index (
            index_id SERIAL PRIMARY KEY,
            concept VARCHAR(100) UNIQUE NOT NULL,
            related_apps TEXT[],
            equations TEXT[],
            papers TEXT[],
            protocols TEXT[],
            last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
    """)
    print("✅ Created 'master_index' table")
    
    # Create indexes for performance
    cur.execute("CREATE INDEX IF NOT EXISTS idx_assets_type ON research_assets(asset_type);")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_assets_source ON research_assets(source_app);")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_events_time ON events(timestamp DESC);")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_sessions_user ON user_sessions(user_id);")
    print("✅ Created indexes")
    
    cur.close()
    conn.close()
    print("\n🎉 Database schema created successfully!")

def seed_initial_data():
    """Seed database with initial app registrations"""
    
    conn = get_db_connection()
    cur = conn.cursor()
    
    apps = [
        ("Mood Amplifier (Central Hub)", "https://mood-amplifier.replit.app", "running"),
        ("Equation Repository", "https://equation-repo.replit.app", "running"),
        ("EEG Analyzer", "", "planned"),
        ("God Machine", "", "planned"),
        ("CrewAI Research Hub", "", "planned"),
        ("Paper Generator", "", "planned"),
        ("Clinical Protocols", "", "planned"),
        ("Patent Portfolio", "", "planned"),
        ("Psi Amplification Lab", "", "planned"),
    ]
    
    for name, url, status in apps:
        cur.execute("""
            INSERT INTO apps (app_name, url, status)
            VALUES (%s, %s, %s)
            ON CONFLICT (app_name) DO NOTHING;
        """, (name, url, status))
    
    conn.commit()
    print("✅ Seeded apps table with 9 apps")
    
    # Add initial master index concepts
    concepts = [
        ("TWA", ["Equation Repository"], ["Fuse", "Split", "Rebase"], ["TWA_COMPLETE_DOCUMENTATION"], []),
        ("HEM", ["Equation Repository", "EEG Analyzer"], ["6D State Vector", "Mood Prediction"], ["Validation_Framework"], []),
        ("MR", ["Equation Repository"], ["Addition", "Subtraction", "PD"], ["MR_ARITHMETIC_REVOLUTION"], []),
        ("I-Cells", ["Equation Repository"], ["Centralization Law", "GM-Human Inversion"], ["ICELL_IWEB_ONTOLOGY"], []),
        ("Music-GILE", ["Equation Repository"], ["Consonance", "Overtone Series"], ["MUSIC_GILE_FOUNDATIONS"], []),
        ("Truth", ["Equation Repository"], ["Absolute", "Objective", "Relative"], ["THREE_TYPES_OF_TRUTH"], []),
    ]
    
    for concept, apps, equations, papers, protocols in concepts:
        cur.execute("""
            INSERT INTO master_index (concept, related_apps, equations, papers, protocols)
            VALUES (%s, %s, %s, %s, %s)
            ON CONFLICT (concept) DO NOTHING;
        """, (concept, apps, equations, papers, protocols))
    
    conn.commit()
    print("✅ Seeded master_index with 6 concepts")
    
    cur.close()
    conn.close()
    print("\n🎉 Initial data seeded successfully!")

if __name__ == "__main__":
    print("🔧 Setting up PostgreSQL database for GM-Inspired Architecture...\n")
    create_schema()
    seed_initial_data()
    print("\n✨ Database ready for cross-app communication!")
