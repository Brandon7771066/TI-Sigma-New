"""
🌐 Streamlit + API Server
=========================
Adds API routes to Streamlit's Tornado server for ESP32 uploads
"""

import os
import sys
import json
import psycopg2
from datetime import datetime
import tornado.web
import threading
import time

def get_db():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

class BiometricUploadHandler(tornado.web.RequestHandler):
    def set_default_headers(self):
        self.set_header("Access-Control-Allow-Origin", "*")
        self.set_header("Access-Control-Allow-Headers", "Content-Type")
        self.set_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.set_header("Content-Type", "application/json")
    
    def options(self):
        self.set_status(204)
        self.finish()
    
    def get(self):
        try:
            conn = get_db()
            cur = conn.cursor()
            
            hr = int(self.get_argument('hr', '0'))
            rr = int(self.get_argument('rr', '0'))
            alpha = float(self.get_argument('alpha', '0'))
            beta = float(self.get_argument('beta', '0'))
            theta = float(self.get_argument('theta', '0'))
            gamma = float(self.get_argument('gamma', '0'))
            delta = float(self.get_argument('delta', '0'))
            rmssd = float(self.get_argument('rmssd', '0'))
            coh = float(self.get_argument('coh', '0'))
            muse = self.get_argument('muse', '0') == '1'
            polar = self.get_argument('polar', '0') == '1'
            dev = self.get_argument('dev', 'ESP32')
            sid = self.get_argument('sid', '')
            
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
            
            print(f"📡 ESP32 GET: HR={hr} | Alpha={alpha:.2f}")
            self.write({"status": "ok", "hr": hr, "alpha": alpha})
        except Exception as e:
            print(f"❌ API Error: {e}")
            self.set_status(500)
            self.write({"error": str(e)})
    
    def post(self):
        try:
            conn = get_db()
            cur = conn.cursor()
            
            data = json.loads(self.request.body) if self.request.body else {}
            eeg = data.get('eeg', {})
            bands = data.get('bands', {})
            heart = data.get('heart', {})
            hrv = data.get('hrv', {})
            status = data.get('status', {})
            
            hr = heart.get('hr', 0) or 0
            rr = heart.get('rr_interval', 0) or 0
            alpha = bands.get('alpha', 0) or 0
            beta = bands.get('beta', 0) or 0
            theta = bands.get('theta', 0) or 0
            gamma = bands.get('gamma', 0) or 0
            delta = bands.get('delta', 0) or 0
            rmssd = hrv.get('rmssd', 0) or 0
            coh = hrv.get('coherence', 0) or 0
            muse = status.get('muse', False)
            polar = status.get('polar', False)
            dev = data.get('device', 'ESP32')
            sid = data.get('session_id', '')
            
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
            
            print(f"📡 ESP32 POST: HR={hr} | Alpha={alpha:.2f}")
            self.write({"status": "ok", "hr": hr})
        except Exception as e:
            print(f"❌ API Error: {e}")
            self.set_status(500)
            self.write({"error": str(e)})

class HealthHandler(tornado.web.RequestHandler):
    def set_default_headers(self):
        self.set_header("Content-Type", "application/json")
        self.set_header("Access-Control-Allow-Origin", "*")
    
    def get(self):
        self.write({"status": "healthy", "service": "Streamlit+API", "port": 5000})

class LatestHandler(tornado.web.RequestHandler):
    def set_default_headers(self):
        self.set_header("Content-Type", "application/json")
        self.set_header("Access-Control-Allow-Origin", "*")
    
    def get(self):
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
            self.write({"data": result})
        except Exception as e:
            self.set_status(500)
            self.write({"error": str(e)})

def inject_api_routes():
    """Inject API routes into Streamlit's running Tornado server"""
    from streamlit.web.server import Server
    import asyncio
    
    while True:
        time.sleep(1)
        try:
            server = Server.get_current()
            if server and hasattr(server, '_runtime'):
                io_loop = server._runtime._ioloop
                
                api_routes = [
                    (r"/api/health", HealthHandler),
                    (r"/api/upload", BiometricUploadHandler),
                    (r"/api/biometric/upload", BiometricUploadHandler),
                    (r"/api/latest", LatestHandler),
                    (r"/api/esp32/latest", LatestHandler),
                ]
                
                def add_routes():
                    try:
                        http_server = server._server
                        if http_server and hasattr(http_server, 'request_callback'):
                            app = http_server.request_callback
                            if hasattr(app, 'add_handlers'):
                                app.add_handlers(".*", api_routes)
                                print("✅ API routes injected into Streamlit server!")
                                return True
                    except Exception as e:
                        print(f"⚠️ Route injection attempt: {e}")
                    return False
                
                if io_loop:
                    io_loop.add_callback(add_routes)
                    print("✅ API route injection scheduled")
                    break
        except Exception as e:
            pass

if __name__ == "__main__":
    print("\n" + "="*60)
    print("🌐 STREAMLIT + API SERVER - Port 5000")
    print("="*60)
    print("📍 /api/upload -> ESP32 biometric uploads (GET/POST)")
    print("📍 /api/health -> Health check")
    print("📍 /api/latest -> Latest readings")
    print("📍 /* -> Streamlit web UI")
    print("="*60 + "\n")
    
    injector_thread = threading.Thread(target=inject_api_routes, daemon=True)
    injector_thread.start()
    
    import streamlit.web.cli as stcli
    sys.argv = ['streamlit', 'run', 'ti_website.py', '--server.port', '5000', 
                '--server.headless', 'true', '--server.address', '0.0.0.0']
    stcli.main()
