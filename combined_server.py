"""
🚀 Combined Server - Biometric API + Streamlit UI on Port 5000
===============================================================

Runs both the biometric API (for ESP32 data upload) and Streamlit dashboard
on a single port so ESP32 can reach it from the internet.

API Routes: /api/*  → Flask handles biometric uploads
UI Routes:  /*      → Proxied to Streamlit (internal port 5001)
"""

from flask import Flask, request, jsonify, Response
from flask_cors import CORS
import os
import psycopg2
from datetime import datetime
import json
import subprocess
import threading
import time
import requests

app = Flask(__name__)
CORS(app)

STREAMLIT_PORT = 5001
streamlit_process = None

def get_db_connection():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

def init_database():
    """Create tables for biometric data"""
    conn = get_db_connection()
    cur = conn.cursor()
    
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
    
    cur.execute("CREATE INDEX IF NOT EXISTS idx_muse_ts ON muse_eeg_data(timestamp DESC)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_polar_ts ON polar_hrv_data(timestamp DESC)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_esp32_ts ON esp32_biometric_data(timestamp DESC)")
    
    conn.commit()
    cur.close()
    conn.close()
    print("✅ Database tables ready")

# ============ API ROUTES ============

@app.route('/health')
def health():
    return jsonify({
        "status": "healthy",
        "service": "Combined Biometric API + Streamlit",
        "timestamp": datetime.now().isoformat()
    })

@app.route('/api/biometric/upload', methods=['POST'])
def upload_esp32_biometric():
    """Receive combined data from ESP32 BLE Bridge"""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data provided"}), 400
        
        conn = get_db_connection()
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
        
        print(f"📡 ESP32: HR={heart.get('hr')} | Alpha={bands.get('alpha'):.2f if bands.get('alpha') else 0}")
        return jsonify({"status": "success", "source": "esp32"}), 201
        
    except Exception as e:
        print(f"❌ ESP32 upload error: {e}")
        return jsonify({"error": str(e)}), 500

@app.route('/api/muse/upload', methods=['POST'])
def upload_muse():
    """Receive Muse EEG data"""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data provided"}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        raw = data.get('raw', {})
        bands = data.get('bands', {})
        metrics = data.get('metrics', {})
        
        cur.execute("""
            INSERT INTO muse_eeg_data 
            (timestamp, tp9, af7, af8, tp10, alpha_power, beta_power, 
             theta_power, gamma_power, delta_power, attention, meditation,
             mellow, concentration, device_id, session_id, source)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            datetime.now(),
            raw.get('tp9'), raw.get('af7'), raw.get('af8'), raw.get('tp10'),
            bands.get('alpha'), bands.get('beta'), bands.get('theta'),
            bands.get('gamma'), bands.get('delta'),
            metrics.get('attention'), metrics.get('meditation'),
            metrics.get('mellow'), metrics.get('concentration'),
            data.get('device_id'), data.get('session_id'), data.get('source', 'unknown')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
        
        print(f"🧠 Muse: Alpha={bands.get('alpha'):.2f if bands.get('alpha') else 0}")
        return jsonify({"status": "success", "source": "muse"}), 201
        
    except Exception as e:
        print(f"❌ Muse upload error: {e}")
        return jsonify({"error": str(e)}), 500

@app.route('/api/polar/upload', methods=['POST'])
def upload_polar():
    """Receive Polar H10 HRV data"""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data provided"}), 400
        
        conn = get_db_connection()
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
            data.get('device_id'), data.get('session_id'), data.get('source', 'unknown')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
        
        print(f"💓 Polar: HR={data.get('heart_rate')} | RMSSD={hrv.get('rmssd', 0):.1f}")
        return jsonify({"status": "success", "source": "polar"}), 201
        
    except Exception as e:
        print(f"❌ Polar upload error: {e}")
        return jsonify({"error": str(e)}), 500

@app.route('/api/muse/latest')
def get_muse_latest():
    """Get latest Muse EEG data"""
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("SELECT * FROM muse_eeg_data ORDER BY timestamp DESC LIMIT 10")
        rows = cur.fetchall()
        cols = [desc[0] for desc in cur.description]
        cur.close()
        conn.close()
        
        result = [dict(zip(cols, row)) for row in rows]
        for r in result:
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            if r.get('created_at'):
                r['created_at'] = r['created_at'].isoformat()
        
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/api/polar/latest')
def get_polar_latest():
    """Get latest Polar HRV data"""
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("SELECT * FROM polar_hrv_data ORDER BY timestamp DESC LIMIT 10")
        rows = cur.fetchall()
        cols = [desc[0] for desc in cur.description]
        cur.close()
        conn.close()
        
        result = [dict(zip(cols, row)) for row in rows]
        for r in result:
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            if r.get('created_at'):
                r['created_at'] = r['created_at'].isoformat()
        
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/api/esp32/latest')
def get_esp32_latest():
    """Get latest ESP32 biometric data"""
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("SELECT * FROM esp32_biometric_data ORDER BY timestamp DESC LIMIT 10")
        rows = cur.fetchall()
        cols = [desc[0] for desc in cur.description]
        cur.close()
        conn.close()
        
        result = [dict(zip(cols, row)) for row in rows]
        for r in result:
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            if r.get('created_at'):
                r['created_at'] = r['created_at'].isoformat()
        
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ============ STREAMLIT PROXY ============

def start_streamlit():
    """Start Streamlit on internal port"""
    global streamlit_process
    print(f"🎨 Starting Streamlit on internal port {STREAMLIT_PORT}...")
    
    streamlit_process = subprocess.Popen([
        'streamlit', 'run', 'ti_website.py',
        '--server.port', str(STREAMLIT_PORT),
        '--server.address', '127.0.0.1',
        '--server.headless', 'true',
        '--browser.gatherUsageStats', 'false'
    ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    time.sleep(3)
    print("✅ Streamlit started")

@app.route('/', defaults={'path': ''})
@app.route('/<path:path>')
def proxy_streamlit(path):
    """Proxy all non-API requests to Streamlit"""
    try:
        streamlit_url = f"http://127.0.0.1:{STREAMLIT_PORT}/{path}"
        
        if request.query_string:
            streamlit_url += f"?{request.query_string.decode()}"
        
        resp = requests.request(
            method=request.method,
            url=streamlit_url,
            headers={k: v for k, v in request.headers if k.lower() != 'host'},
            data=request.get_data(),
            cookies=request.cookies,
            allow_redirects=False,
            stream=True,
            timeout=30
        )
        
        excluded_headers = ['content-encoding', 'content-length', 'transfer-encoding', 'connection']
        headers = [(name, value) for name, value in resp.raw.headers.items()
                   if name.lower() not in excluded_headers]
        
        return Response(resp.content, resp.status_code, headers)
        
    except requests.exceptions.RequestException as e:
        return f"<h1>Streamlit is starting...</h1><p>Please refresh in a few seconds.</p><p>Error: {e}</p>", 503

# ============ WEBSOCKET PROXY (for Streamlit) ============

@app.route('/_stcore/stream')
def proxy_stream():
    """Proxy Streamlit websocket endpoint"""
    return proxy_streamlit('_stcore/stream')

# ============ MAIN ============

if __name__ == '__main__':
    print("\n" + "="*60)
    print("🚀 COMBINED SERVER - Biometric API + Streamlit")
    print("="*60)
    
    init_database()
    
    streamlit_thread = threading.Thread(target=start_streamlit, daemon=True)
    streamlit_thread.start()
    
    time.sleep(2)
    
    print("\n📡 API Endpoints (for ESP32):")
    print("   POST /api/biometric/upload  - ESP32 combined data")
    print("   POST /api/muse/upload       - Muse EEG data")
    print("   POST /api/polar/upload      - Polar HRV data")
    print("   GET  /api/esp32/latest      - Latest ESP32 data")
    print("   GET  /api/muse/latest       - Latest Muse data")
    print("   GET  /api/polar/latest      - Latest Polar data")
    print("   GET  /health                - Health check")
    print("\n🎨 Streamlit Dashboard: All other routes")
    print("="*60 + "\n")
    
    app.run(host='0.0.0.0', port=5000, threaded=True)
