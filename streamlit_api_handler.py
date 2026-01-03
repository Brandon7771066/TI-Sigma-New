"""
🧠💓 Streamlit API Handler - Process biometric data via query params
====================================================================

Since only port 5000 is externally accessible and Streamlit runs on it,
we can receive ESP32 data via GET requests with query parameters.

ESP32 uses: GET /api?hr=72&rr=850&alpha=0.5&...
Streamlit processes this and writes to database.
"""

import streamlit as st
import psycopg2
import os
from datetime import datetime
import json

def get_db():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

def init_tables():
    """Ensure biometric tables exist"""
    conn = get_db()
    cur = conn.cursor()
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS esp32_biometric_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            eeg_tp9 FLOAT, eeg_af7 FLOAT, eeg_af8 FLOAT, eeg_tp10 FLOAT,
            alpha FLOAT, beta FLOAT, theta FLOAT, gamma FLOAT, delta FLOAT,
            heart_rate INTEGER, rr_interval INTEGER, rmssd FLOAT, coherence FLOAT,
            muse_connected BOOLEAN, polar_connected BOOLEAN,
            device_id TEXT, session_id TEXT,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    conn.commit()
    cur.close()
    conn.close()

def process_api_request():
    """
    Check if this is an API request (has biometric data in query params)
    If so, save to database and return True
    """
    params = st.query_params
    
    # Check if this is an ESP32 data upload (has 'hr' or 'alpha' params)
    if 'hr' in params or 'alpha' in params or 'api' in params:
        try:
            conn = get_db()
            cur = conn.cursor()
            
            # Parse parameters
            hr = int(params.get('hr', 0) or 0)
            rr = int(params.get('rr', 0) or 0)
            alpha = float(params.get('alpha', 0) or 0)
            beta = float(params.get('beta', 0) or 0)
            theta = float(params.get('theta', 0) or 0)
            gamma = float(params.get('gamma', 0) or 0)
            delta = float(params.get('delta', 0) or 0)
            tp9 = float(params.get('tp9', 0) or 0)
            af7 = float(params.get('af7', 0) or 0)
            af8 = float(params.get('af8', 0) or 0)
            tp10 = float(params.get('tp10', 0) or 0)
            rmssd = float(params.get('rmssd', 0) or 0)
            coherence = float(params.get('coh', 0) or 0)
            muse_conn = params.get('muse', '0') == '1'
            polar_conn = params.get('polar', '0') == '1'
            device_id = params.get('dev', 'ESP32')
            session_id = params.get('sid', '')
            
            cur.execute("""
                INSERT INTO esp32_biometric_data 
                (timestamp, eeg_tp9, eeg_af7, eeg_af8, eeg_tp10,
                 alpha, beta, theta, gamma, delta, 
                 heart_rate, rr_interval, rmssd, coherence,
                 muse_connected, polar_connected, device_id, session_id)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                datetime.now(),
                tp9, af7, af8, tp10,
                alpha, beta, theta, gamma, delta,
                hr, rr, rmssd, coherence,
                muse_conn, polar_conn, device_id, session_id
            ))
            
            conn.commit()
            cur.close()
            conn.close()
            
            # Return JSON response for API
            if 'api' in params:
                st.json({"status": "ok", "hr": hr, "alpha": alpha})
                st.stop()
            
            return True
            
        except Exception as e:
            if 'api' in params:
                st.json({"error": str(e)})
                st.stop()
            return False
    
    return False

def get_latest_biometric_data(limit=10):
    """Get latest ESP32 biometric data"""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT * FROM esp32_biometric_data 
            ORDER BY timestamp DESC 
            LIMIT %s
        """, (limit,))
        
        rows = cur.fetchall()
        cols = [d[0] for d in cur.description]
        cur.close()
        conn.close()
        
        return [dict(zip(cols, row)) for row in rows]
    except:
        return []

def get_biometric_stats():
    """Get statistics from recent biometric data"""
    try:
        conn = get_db()
        cur = conn.cursor()
        
        cur.execute("""
            SELECT 
                COUNT(*) as total_records,
                AVG(heart_rate) as avg_hr,
                AVG(rmssd) as avg_rmssd,
                AVG(alpha) as avg_alpha,
                MAX(timestamp) as last_update
            FROM esp32_biometric_data
            WHERE timestamp > NOW() - INTERVAL '1 hour'
        """)
        
        row = cur.fetchone()
        cols = [d[0] for d in cur.description]
        cur.close()
        conn.close()
        
        return dict(zip(cols, row)) if row else {}
    except:
        return {}

# Initialize tables on import
try:
    init_tables()
except:
    pass
