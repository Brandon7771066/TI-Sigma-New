"""
🌐 Combined Gateway - Flask API + Streamlit on Port 5000
=========================================================
Uses Werkzeug's DispatcherMiddleware to route:
  - /api/* -> Flask (for ESP32 uploads)
  - /* -> Streamlit (for web UI)
"""

import subprocess
import os
import time
import signal
import sys
import threading
from flask import Flask, request, jsonify
from flask_cors import CORS
import psycopg2
from datetime import datetime
import json

api = Flask('biometric_api')
CORS(api)

def get_db():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

@api.route('/health')
def health():
    return jsonify({"status": "healthy", "service": "ESP32 Gateway", "port": 5000})

@api.route('/upload', methods=['POST', 'GET'])
@api.route('/biometric/upload', methods=['POST', 'GET'])
def upload_biometric():
    try:
        conn = get_db()
        cur = conn.cursor()
        
        if request.method == 'POST':
            data = request.get_json() or {}
            eeg = data.get('eeg', {})
            bands = data.get('bands', {})
            heart = data.get('heart', {})
            hrv = data.get('hrv', {})
            status = data.get('status', {})
            
            hr = heart.get('hr', 0)
            rr = heart.get('rr_interval', 0)
            alpha = bands.get('alpha', 0) or 0
            beta = bands.get('beta', 0) or 0
            theta = bands.get('theta', 0) or 0
            gamma = bands.get('gamma', 0) or 0
            delta = bands.get('delta', 0) or 0
            rmssd = hrv.get('rmssd', 0)
            coh = hrv.get('coherence', 0)
            muse = status.get('muse', False)
            polar = status.get('polar', False)
            dev = data.get('device', 'ESP32')
            sid = data.get('session_id', '')
        else:
            hr = int(request.args.get('hr', 0))
            rr = int(request.args.get('rr', 0))
            alpha = float(request.args.get('alpha', 0))
            beta = float(request.args.get('beta', 0))
            theta = float(request.args.get('theta', 0))
            gamma = float(request.args.get('gamma', 0))
            delta = float(request.args.get('delta', 0))
            rmssd = float(request.args.get('rmssd', 0))
            coh = float(request.args.get('coh', 0))
            muse = request.args.get('muse', '0') == '1'
            polar = request.args.get('polar', '0') == '1'
            dev = request.args.get('dev', 'ESP32')
            sid = request.args.get('sid', '')
        
        cur.execute("""
            INSERT INTO esp32_biometric_data 
            (timestamp, heart_rate, rr_interval, alpha, beta, theta, gamma, delta,
             rmssd, coherence, muse_connected, polar_connected, device_id, session_id)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (datetime.now(), hr, rr, alpha, beta, theta, gamma, delta,
              rmssd, coh, muse, polar, dev, sid))
        
        conn.commit()
        cur.close()
        conn.close()
        
        print(f"📡 ESP32: HR={hr} | Alpha={alpha:.2f} | RMSSD={rmssd:.1f}")
        return jsonify({"status": "ok", "hr": hr, "alpha": alpha}), 201
        
    except Exception as e:
        print(f"❌ API Error: {e}")
        return jsonify({"error": str(e)}), 500

@api.route('/latest')
@api.route('/esp32/latest')
def get_latest():
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT id, timestamp, heart_rate, alpha, rmssd, coherence, 
                   muse_connected, polar_connected, device_id
            FROM esp32_biometric_data ORDER BY timestamp DESC LIMIT 10
        """)
        rows = cur.fetchall()
        cols = [d[0] for d in cur.description]
        cur.close()
        conn.close()
        
        result = []
        for row in rows:
            r = dict(zip(cols, row))
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            result.append(r)
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

streamlit_proc = None

def start_streamlit():
    global streamlit_proc
    print("🚀 Starting Streamlit on internal port 5001...")
    streamlit_proc = subprocess.Popen([
        'streamlit', 'run', 'ti_website.py',
        '--server.port', '5001',
        '--server.headless', 'true',
        '--browser.serverAddress', 'localhost'
    ], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

def cleanup(signum, frame):
    global streamlit_proc
    if streamlit_proc:
        streamlit_proc.terminate()
    sys.exit(0)

signal.signal(signal.SIGTERM, cleanup)
signal.signal(signal.SIGINT, cleanup)

if __name__ == '__main__':
    print("\n" + "="*60)
    print("🌐 COMBINED GATEWAY - Port 5000")
    print("="*60)
    print("📍 /api/* -> Flask (ESP32 uploads)")
    print("📍 /* -> Streamlit (Web UI)")
    print("="*60)
    
    streamlit_thread = threading.Thread(target=start_streamlit, daemon=True)
    streamlit_thread.start()
    
    time.sleep(3)
    
    try:
        from werkzeug.middleware.dispatcher import DispatcherMiddleware
        from werkzeug.serving import run_simple
        import requests
        
        def streamlit_proxy(environ, start_response):
            path = environ.get('PATH_INFO', '/')
            query = environ.get('QUERY_STRING', '')
            url = f"http://localhost:5001{path}"
            if query:
                url += f"?{query}"
            
            try:
                method = environ.get('REQUEST_METHOD', 'GET')
                headers = {}
                for key, value in environ.items():
                    if key.startswith('HTTP_'):
                        header_name = key[5:].replace('_', '-')
                        headers[header_name] = value
                
                resp = requests.request(method, url, headers=headers, stream=True)
                
                response_headers = [(k, v) for k, v in resp.headers.items()
                                   if k.lower() not in ('transfer-encoding', 'connection')]
                start_response(f'{resp.status_code} {resp.reason}', response_headers)
                return [resp.content]
            except Exception as e:
                start_response('502 Bad Gateway', [('Content-Type', 'text/plain')])
                return [f"Streamlit not ready: {e}".encode()]
        
        app = DispatcherMiddleware(streamlit_proxy, {
            '/api': api,
        })
        
        print("\n✅ Gateway ready! ESP32 can POST to /api/upload")
        run_simple('0.0.0.0', 5000, app, threaded=True, use_reloader=False)
        
    except ImportError as e:
        print(f"Werkzeug not available: {e}")
        print("Falling back to Flask-only mode...")
        api.run(host='0.0.0.0', port=5000, threaded=True)
