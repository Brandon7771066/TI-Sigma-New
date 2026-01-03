"""
🧠💓 Biometric API - Receives data from ESP32 on port 3000
============================================================
Simple Flask API for ESP32 uploads. Run alongside Streamlit.
"""

from flask import Flask, request, jsonify
from flask_cors import CORS
import os
import psycopg2
from datetime import datetime
import json

app = Flask(__name__)
CORS(app)

def get_db():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

def init_db():
    conn = get_db()
    cur = conn.cursor()
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS esp32_biometric_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            device_timestamp BIGINT,
            eeg_tp9 FLOAT, eeg_af7 FLOAT, eeg_af8 FLOAT, eeg_tp10 FLOAT,
            alpha FLOAT, beta FLOAT, theta FLOAT, gamma FLOAT, delta FLOAT,
            heart_rate INTEGER, rr_interval INTEGER, rmssd FLOAT, coherence FLOAT,
            muse_connected BOOLEAN, polar_connected BOOLEAN,
            device_id TEXT DEFAULT 'ESP32_Bridge', session_id TEXT,
            metadata JSONB, created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS muse_eeg_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            tp9 FLOAT, af7 FLOAT, af8 FLOAT, tp10 FLOAT,
            alpha_power FLOAT, beta_power FLOAT, theta_power FLOAT,
            gamma_power FLOAT, delta_power FLOAT,
            attention FLOAT, meditation FLOAT, mellow FLOAT, concentration FLOAT,
            signal_quality FLOAT, battery_level INTEGER,
            device_id TEXT, session_id TEXT, source TEXT DEFAULT 'unknown',
            metadata JSONB, created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS polar_hrv_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            heart_rate INTEGER, rr_interval INTEGER, rr_intervals JSONB,
            rmssd FLOAT, sdnn FLOAT, lf_power FLOAT, hf_power FLOAT,
            lf_hf_ratio FLOAT, coherence FLOAT,
            device_id TEXT, session_id TEXT, source TEXT DEFAULT 'unknown',
            metadata JSONB, created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("CREATE INDEX IF NOT EXISTS idx_esp32_ts ON esp32_biometric_data(timestamp DESC)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_muse_ts ON muse_eeg_data(timestamp DESC)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_polar_ts ON polar_hrv_data(timestamp DESC)")
    
    conn.commit()
    cur.close()
    conn.close()
    print("✅ Database ready")

@app.route('/health')
def health():
    return jsonify({"status": "healthy", "service": "Biometric API", "port": 3000})

@app.route('/api/biometric/upload', methods=['POST'])
def upload_biometric():
    """ESP32 combined upload endpoint"""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data"}), 400
        
        conn = get_db()
        cur = conn.cursor()
        
        eeg = data.get('eeg', {})
        bands = data.get('bands', {})
        heart = data.get('heart', {})
        hrv = data.get('hrv', {})
        status = data.get('status', {})
        
        cur.execute("""
            INSERT INTO esp32_biometric_data 
            (timestamp, device_timestamp, eeg_tp9, eeg_af7, eeg_af8, eeg_tp10,
             alpha, beta, theta, gamma, delta, heart_rate, rr_interval, 
             rmssd, coherence, muse_connected, polar_connected, device_id, session_id)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            datetime.now(),
            data.get('timestamp'),
            eeg.get('tp9'), eeg.get('af7'), eeg.get('af8'), eeg.get('tp10'),
            bands.get('alpha'), bands.get('beta'), bands.get('theta'), 
            bands.get('gamma'), bands.get('delta'),
            heart.get('hr'), heart.get('rr_interval'),
            hrv.get('rmssd'), hrv.get('coherence'),
            status.get('muse'), status.get('polar'),
            data.get('device', 'ESP32'),
            data.get('session_id')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
        
        hr = heart.get('hr', 0)
        alpha = bands.get('alpha', 0) or 0
        print(f"📡 ESP32: HR={hr} | Alpha={alpha:.2f}")
        return jsonify({"status": "ok"}), 201
        
    except Exception as e:
        print(f"❌ Error: {e}")
        return jsonify({"error": str(e)}), 500

@app.route('/api/muse/upload', methods=['POST'])
def upload_muse():
    try:
        data = request.get_json()
        conn = get_db()
        cur = conn.cursor()
        
        raw = data.get('raw', {})
        bands = data.get('bands', {})
        
        cur.execute("""
            INSERT INTO muse_eeg_data 
            (timestamp, tp9, af7, af8, tp10, alpha_power, beta_power, 
             theta_power, gamma_power, delta_power, device_id, session_id, source)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            datetime.now(),
            raw.get('tp9'), raw.get('af7'), raw.get('af8'), raw.get('tp10'),
            bands.get('alpha'), bands.get('beta'), bands.get('theta'),
            bands.get('gamma'), bands.get('delta'),
            data.get('device_id'), data.get('session_id'), data.get('source', 'muse')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
        print(f"🧠 Muse: Alpha={bands.get('alpha', 0):.2f}")
        return jsonify({"status": "ok"}), 201
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/api/polar/upload', methods=['POST'])
def upload_polar():
    try:
        data = request.get_json()
        conn = get_db()
        cur = conn.cursor()
        
        hrv = data.get('hrv', {})
        
        cur.execute("""
            INSERT INTO polar_hrv_data 
            (timestamp, heart_rate, rr_interval, rr_intervals, rmssd, sdnn,
             coherence, device_id, session_id, source)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            datetime.now(),
            data.get('heart_rate'),
            data.get('rr_interval'),
            json.dumps(data.get('rr_intervals', [])),
            hrv.get('rmssd'), hrv.get('sdnn'),
            data.get('coherence') or hrv.get('coherence'),
            data.get('device_id'), data.get('session_id'), data.get('source', 'polar')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
        print(f"💓 Polar: HR={data.get('heart_rate')}")
        return jsonify({"status": "ok"}), 201
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/api/esp32/latest')
def get_latest():
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("SELECT * FROM esp32_biometric_data ORDER BY timestamp DESC LIMIT 5")
        rows = cur.fetchall()
        cols = [d[0] for d in cur.description]
        cur.close()
        conn.close()
        
        result = []
        for row in rows:
            r = dict(zip(cols, row))
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            if r.get('created_at'):
                r['created_at'] = r['created_at'].isoformat()
            result.append(r)
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == '__main__':
    print("\n" + "="*50)
    print("🧠💓 BIOMETRIC API - Port 3000")
    print("="*50)
    init_db()
    print("\n📡 ESP32 should POST to:")
    print("   /api/biometric/upload")
    print("   /api/muse/upload")
    print("   /api/polar/upload")
    print("="*50 + "\n")
    app.run(host='0.0.0.0', port=3000)
