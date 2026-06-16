"""
🌐 Async Gateway - Flask API + Streamlit Proxy on Port 5000
============================================================
Uses aiohttp for async HTTP/WebSocket proxying to Streamlit.
API routes handled directly, everything else proxied.

Copyright (c) 2025 Brandon Charles Emerick
All rights reserved.

This software is proprietary and confidential.
Unauthorized copying, modification, or distribution is prohibited.

Patent Pending: GSA (Grand Stock Algorithm)
Patent Pending: LCC Proxy Engine

For licensing inquiries: See /api/v1/register
"""

import asyncio
import aiohttp
from aiohttp import web
import subprocess
import signal
import sys
import os
import json
import psycopg2
from datetime import datetime, timedelta
import secrets as py_secrets

streamlit_proc = None

RATE_LIMITS = {'basic': 100, 'pro': 10000, 'enterprise': 100000}

LIVE_SESSION = {
    "hr": None, "rmssd": None, "sdnn": None, "coherence": None,
    "rr_intervals": [], "mendi_score": None, "lcc_proxy": None,
    "lcc_zone": None, "updated_at": None, "source": None
}
TIER_PRICES = {'basic': 99, 'pro': 499, 'enterprise': 'custom'}
STREAMLIT_PORT = 5002

def get_db():
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

async def health_handler(request):
    return web.json_response({"status": "healthy", "service": "ESP32 Gateway", "port": 5000})

async def upload_handler(request):
    # Log ALL incoming upload requests for debugging
    print(f"📥 UPLOAD REQUEST: {request.method} from {request.remote} | Path: {request.path}")
    print(f"   Query: {dict(request.query)}")
    try:
        conn = get_db()
        cur = conn.cursor()
        
        if request.method == 'POST':
            data = await request.json() if request.body_exists else {}
            print(f"   POST Body: {data}")
            
            # Support both nested format (ESP32 firmware) and flat format (direct API calls)
            bands = data.get('bands', {})
            heart = data.get('heart', {})
            hrv = data.get('hrv', {})
            status = data.get('status', {})
            
            # Try nested first, then flat keys
            hr = heart.get('hr', 0) or data.get('heart_rate', 0) or data.get('hr', 0) or 0
            rr = heart.get('rr_interval', 0) or data.get('rr_interval', 0) or data.get('rr', 0) or 0
            alpha = bands.get('alpha', 0) or data.get('alpha', 0) or 0
            beta = bands.get('beta', 0) or data.get('beta', 0) or 0
            theta = bands.get('theta', 0) or data.get('theta', 0) or 0
            gamma = bands.get('gamma', 0) or data.get('gamma', 0) or 0
            delta = bands.get('delta', 0) or data.get('delta', 0) or 0
            rmssd = hrv.get('rmssd', 0) or data.get('rmssd', 0) or 0
            coh = hrv.get('coherence', 0) or data.get('coherence', 0) or 0
            muse = status.get('muse', False) or data.get('muse_connected', False) or data.get('muse', False)
            polar = status.get('polar', False) or data.get('polar_connected', False) or data.get('polar', False)
            dev = data.get('device', '') or data.get('device_id', '') or 'ESP32'
            sid = data.get('session_id', '')
        else:
            def safe_int(val, default=0):
                try:
                    return int(val) if val else default
                except (ValueError, TypeError):
                    return default
            
            def safe_float(val, default=0.0):
                try:
                    return float(val) if val else default
                except (ValueError, TypeError):
                    return default
            
            hr = safe_int(request.query.get('hr'))
            rr = safe_int(request.query.get('rr'))
            alpha = safe_float(request.query.get('alpha'))
            beta = safe_float(request.query.get('beta'))
            theta = safe_float(request.query.get('theta'))
            gamma = safe_float(request.query.get('gamma'))
            delta = safe_float(request.query.get('delta'))
            rmssd = safe_float(request.query.get('rmssd'))
            coh = safe_float(request.query.get('coh'))
            muse = request.query.get('muse', '0') == '1'
            polar = request.query.get('polar', '0') == '1'
            dev = request.query.get('dev', 'ESP32') or 'ESP32'
            sid = request.query.get('sid', '') or ''
        
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
        return web.json_response({"status": "ok", "hr": hr, "alpha": alpha}, status=201)
        
    except Exception as e:
        print(f"❌ API Error: {e}")
        return web.json_response({"error": str(e)}, status=500)

async def debug_handler(request):
    """Debug endpoint to help troubleshoot ESP32 connection"""
    try:
        conn = get_db()
        cur = conn.cursor()
        
        cur.execute("SELECT COUNT(*) FROM esp32_biometric_data")
        total_row = cur.fetchone()
        total = total_row[0] if total_row else 0
        
        cur.execute("SELECT MAX(timestamp), MIN(timestamp) FROM esp32_biometric_data")
        times = cur.fetchone() or (None, None)
        
        cur.execute("""
            SELECT timestamp, device_id, heart_rate, alpha 
            FROM esp32_biometric_data 
            ORDER BY timestamp DESC LIMIT 5
        """)
        recent = cur.fetchall()
        
        cur.close()
        conn.close()
        
        recent_data = []
        for r in recent:
            recent_data.append({
                "timestamp": r[0].isoformat() if r[0] else None,
                "device": r[1],
                "hr": r[2],
                "alpha": r[3]
            })
        
        from datetime import datetime
        now = datetime.now()
        last_data_age = None
        if times[0]:
            age_seconds = (now - times[0]).total_seconds()
            if age_seconds < 60:
                last_data_age = f"{int(age_seconds)} seconds ago"
            elif age_seconds < 3600:
                last_data_age = f"{int(age_seconds/60)} minutes ago"
            else:
                last_data_age = f"{age_seconds/3600:.1f} hours ago"
        
        return web.json_response({
            "status": "ESP32 Gateway Debug",
            "server_time": now.isoformat(),
            "total_records": total,
            "last_data": times[0].isoformat() if times[0] else None,
            "last_data_age": last_data_age,
            "first_data": times[1].isoformat() if times[1] else None,
            "recent_uploads": recent_data,
            "test_url": "Try: curl 'YOUR_REPLIT_URL/api/upload?hr=72&alpha=0.7&muse=1&polar=1'",
            "esp32_checklist": [
                "1. Is ESP32 powered on? (Blue LED blinking)",
                "2. Is WiFi connected? (Check Serial Monitor for 'WiFi connected')",
                "3. Can ESP32 reach internet? (ping test in setup)",
                "4. Is Muse 2 turned on? (White LED breathing)",
                "5. Is Polar H10 worn and wet? (Wet the strap contacts)"
            ]
        })
    except Exception as e:
        return web.json_response({"error": str(e)}, status=500)

async def latest_handler(request):
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT id, timestamp, heart_rate, alpha, rmssd, coherence, 
                   muse_connected, polar_connected, device_id
            FROM esp32_biometric_data ORDER BY timestamp DESC LIMIT 10
        """)
        rows = cur.fetchall()
        cols = [d[0] for d in cur.description] if cur.description else []
        cur.close()
        conn.close()
        
        result = []
        for row in rows:
            r = dict(zip(cols, row))
            if r.get('timestamp'):
                r['timestamp'] = r['timestamp'].isoformat()
            result.append(r)
        return web.json_response({"data": result})
    except Exception as e:
        return web.json_response({"error": str(e)}, status=500)


async def mendi_latest_handler(request):
    """GET /api/mendi/latest — most recent Mendi fNIRS row."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT hbo2, hbr, oxygenation_percent, signal_quality, created_at
            FROM mendi_realtime_data
            ORDER BY created_at DESC LIMIT 1
        """)
        row = cur.fetchone()
        cur.close()
        conn.close()
        if row:
            return web.json_response({
                "hbo2": row[0], "hbr": row[1],
                "oxygenation_percent": row[2], "signal_quality": row[3],
                "created_at": row[4].isoformat() if row[4] else None,
            })
        return web.json_response({"error": "no_data"}, status=404)
    except Exception as exc:
        return web.json_response({"error": str(exc)}, status=500)


async def polar_latest_handler(request):
    """GET /api/polar/latest — most recent Polar H10 row."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT heart_rate, hrv_rmssd, coherence, created_at
            FROM polar_realtime_data
            ORDER BY created_at DESC LIMIT 1
        """)
        row = cur.fetchone()
        cur.close()
        conn.close()
        if row:
            return web.json_response({
                "heart_rate": row[0],
                "hrv": {"rmssd": row[1], "coherence": row[2]},
                "created_at": row[3].isoformat() if row[3] else None,
            })
        return web.json_response({"error": "no_data"}, status=404)
    except Exception as exc:
        return web.json_response({"error": str(exc)}, status=500)


async def muse_latest_handler(request):
    """GET /api/muse/latest — most recent Muse 2 EEG row."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT alpha, beta, theta, gamma, delta, source, created_at
            FROM muse_realtime_data
            ORDER BY created_at DESC LIMIT 1
        """)
        row = cur.fetchone()
        cur.close()
        conn.close()
        if row:
            return web.json_response({
                "bands": {
                    "alpha": row[0], "beta": row[1], "theta": row[2],
                    "gamma": row[3], "delta": row[4],
                },
                "source": row[5],
                "created_at": row[6].isoformat() if row[6] else None,
            })
        return web.json_response({"error": "no_data"}, status=404)
    except Exception as exc:
        return web.json_response({"error": str(exc)}, status=500)

async def proxy_websocket(request):
    protocols_str = request.headers.get('Sec-WebSocket-Protocol', '')
    protocols = [p.strip() for p in protocols_str.split(',') if p.strip()] if protocols_str else []
    
    print(f"📡 WebSocket connect: {request.path} protocols: {protocols}")
    
    ws_server = web.WebSocketResponse(protocols=protocols if protocols else [])
    await ws_server.prepare(request)
    
    selected_protocol = ws_server.ws_protocol
    print(f"✅ WebSocket server ready, selected protocol: {selected_protocol}")
    
    async with aiohttp.ClientSession() as session:
        path = request.path
        query = request.query_string
        ws_url = f"ws://localhost:{STREAMLIT_PORT}{path}"
        if query:
            ws_url += f"?{query}"
        
        headers = {}
        for key, value in request.headers.items():
            if key.lower().startswith('sec-websocket') or key.lower() in ('origin', 'host'):
                continue
            headers[key] = value
        
        try:
            print(f"🔗 Connecting to Streamlit WS: {ws_url}")
            async with session.ws_connect(
                ws_url, 
                protocols=protocols if protocols else [],
                headers=headers
            ) as ws_client:
                print(f"✅ Connected to Streamlit WS")
                
                async def forward_to_client():
                    try:
                        async for msg in ws_client:
                            if msg.type == aiohttp.WSMsgType.TEXT:
                                await ws_server.send_str(msg.data)
                            elif msg.type == aiohttp.WSMsgType.BINARY:
                                await ws_server.send_bytes(msg.data)
                            elif msg.type in (aiohttp.WSMsgType.CLOSE, aiohttp.WSMsgType.CLOSED):
                                break
                            elif msg.type == aiohttp.WSMsgType.ERROR:
                                print(f"WS client error: {msg.data}")
                                break
                    except Exception as e:
                        print(f"Forward to client error: {e}")
                
                async def forward_to_server():
                    try:
                        async for msg in ws_server:
                            if msg.type == aiohttp.WSMsgType.TEXT:
                                await ws_client.send_str(msg.data)
                            elif msg.type == aiohttp.WSMsgType.BINARY:
                                await ws_client.send_bytes(msg.data)
                            elif msg.type in (aiohttp.WSMsgType.CLOSE, aiohttp.WSMsgType.CLOSED):
                                break
                            elif msg.type == aiohttp.WSMsgType.ERROR:
                                print(f"WS server error: {msg.data}")
                                break
                    except Exception as e:
                        print(f"Forward to server error: {e}")
                
                await asyncio.gather(forward_to_client(), forward_to_server(), return_exceptions=True)
        except Exception as e:
            print(f"❌ WebSocket proxy error: {e}")
    
    return ws_server

async def proxy_http(request):
    path = request.path
    query = request.query_string
    url = f"http://localhost:{STREAMLIT_PORT}{path}"
    if query:
        url += f"?{query}"
    
    headers = dict(request.headers)
    headers.pop('Host', None)
    
    body = await request.read() if request.body_exists else None
    
    max_retries = 3
    for attempt in range(max_retries):
        try:
            async with aiohttp.ClientSession() as session:
                async with session.request(
                    request.method, url,
                    headers=headers,
                    data=body,
                    allow_redirects=False
                ) as resp:
                    response_headers = {}
                    for key, value in resp.headers.items():
                        if key.lower() not in ('transfer-encoding', 'content-encoding', 'content-length'):
                            response_headers[key] = value
                    
                    resp_body = await resp.read()
                    return web.Response(
                        status=resp.status,
                        headers=response_headers,
                        body=resp_body
                    )
        except aiohttp.ClientConnectorError:
            if attempt < max_retries - 1:
                print(f"⏳ Streamlit not ready, retrying... ({attempt+1}/{max_retries})")
                await asyncio.sleep(1)
            else:
                print(f"Error handling request from {request.remote}")
                return web.Response(status=502, text="Gateway Error: Streamlit not available")
    return web.Response(status=502, text="Gateway Error: Unexpected error")

async def proxy_handler(request):
    if request.headers.get('Upgrade', '').lower() == 'websocket':
        return await proxy_websocket(request)
    else:
        return await proxy_http(request)

async def init_api_tables():
    """Initialize API licensing tables. Gracefully handles missing DATABASE_URL."""
    database_url = os.environ.get('DATABASE_URL')
    if not database_url:
        print("⚠️ DATABASE_URL not set - API licensing tables not initialized")
        return False
    
    try:
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS api_keys (
                id SERIAL PRIMARY KEY,
                api_key VARCHAR(64) UNIQUE NOT NULL,
                user_email VARCHAR(255) NOT NULL,
                tier VARCHAR(20) DEFAULT 'basic',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                expires_at TIMESTAMP,
                is_active BOOLEAN DEFAULT TRUE,
                daily_calls INTEGER DEFAULT 0,
                last_reset DATE DEFAULT CURRENT_DATE
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS api_usage (
                id SERIAL PRIMARY KEY,
                api_key_id INTEGER REFERENCES api_keys(id),
                endpoint VARCHAR(100) NOT NULL,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                success BOOLEAN DEFAULT TRUE
            )
        """)
        conn.commit()
        cur.close()
        conn.close()
        print("✅ API licensing tables initialized")
        return True
    except Exception as e:
        print(f"⚠️ Could not initialize API tables: {e}")
        return False

async def validate_api_key(request):
    """Validate API key and check rate limits."""
    api_key = request.headers.get('X-API-Key') or request.query.get('api_key')
    if not api_key:
        return None, web.json_response({'error': 'API key required'}, status=401)
    
    database_url = os.environ.get('DATABASE_URL')
    if not database_url:
        return None, web.json_response({'error': 'Database not configured'}, status=503)
    
    try:
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        cur.execute("SELECT * FROM api_keys WHERE api_key = %s AND is_active = TRUE", (api_key,))
        row = cur.fetchone()
        
        if not row:
            cur.close()
            conn.close()
            return None, web.json_response({'error': 'Invalid API key'}, status=401)
        
        key_data = {'id': row[0], 'api_key': row[1], 'tier': row[3], 'daily_calls': row[7]}
        
        tier_limit = RATE_LIMITS.get(key_data['tier'], 100)
        if key_data['daily_calls'] >= tier_limit:
            cur.close()
            conn.close()
            return None, web.json_response({'error': 'Rate limit exceeded', 'limit': tier_limit}, status=429)
        
        cur.execute("UPDATE api_keys SET daily_calls = daily_calls + 1 WHERE id = %s", (key_data['id'],))
        conn.commit()
        cur.close()
        conn.close()
        
        return key_data, None
    except Exception as e:
        return None, web.json_response({'error': 'Database error', 'details': str(e)}, status=503)

async def api_v1_health_handler(request):
    """API v1 health check."""
    return web.json_response({
        'status': 'healthy',
        'version': '1.0.0',
        'framework': 'TI Framework API',
        'endpoints': ['/api/v1/register', '/api/v1/lcc/calculate', '/api/v1/gsa/signal', '/api/v1/tralse/evaluate']
    })

async def api_register_handler(request):
    """Register for an API key."""
    try:
        data = await request.json()
    except:
        data = {}
    
    email = data.get('email')
    tier = data.get('tier', 'basic')
    
    if not email:
        return web.json_response({'error': 'Email required'}, status=400)
    
    if tier not in TIER_PRICES:
        return web.json_response({'error': f'Invalid tier. Options: {list(TIER_PRICES.keys())}'}, status=400)
    
    database_url = os.environ.get('DATABASE_URL')
    if not database_url:
        return web.json_response({'error': 'Database not configured'}, status=503)
    
    api_key = f"ti_{py_secrets.token_hex(32)}"
    
    try:
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO api_keys (api_key, user_email, tier, expires_at)
            VALUES (%s, %s, %s, %s)
            RETURNING id
        """, (api_key, email, tier, datetime.now() + timedelta(days=30)))
        conn.commit()
        cur.close()
        conn.close()
        
        return web.json_response({
            'success': True,
            'api_key': api_key,
            'tier': tier,
            'rate_limit': RATE_LIMITS[tier],
            'price_usd': TIER_PRICES[tier],
            'expires_in_days': 30
        })
    except Exception as e:
        return web.json_response({'error': 'Database error', 'details': str(e)}, status=503)

async def live_biometric_post_handler(request):
    """Receive live biometric data from Web Bluetooth browser component."""
    global LIVE_SESSION
    try:
        data = await request.json()
    except Exception:
        return web.json_response({"error": "invalid json"}, status=400)

    import math
    PHI = (1 + math.sqrt(5)) / 2
    SQRT2 = math.sqrt(2)
    LCC_TRALSE = SQRT2 - 1
    LCC_EMERICK = 1 / SQRT2
    LCC_HIGH = 0.851
    LCC_RADIANT = math.sqrt(math.e / math.pi)

    hr = data.get("hr")
    rmssd = data.get("rmssd")
    sdnn = data.get("sdnn")
    mendi_score = data.get("mendi_score")
    rr_list = data.get("rr_intervals", [])

    LIVE_SESSION["updated_at"] = datetime.utcnow().isoformat()
    if hr is not None:
        LIVE_SESSION["hr"] = hr
    if rmssd is not None:
        LIVE_SESSION["rmssd"] = rmssd
    if sdnn is not None:
        LIVE_SESSION["sdnn"] = sdnn
    if rr_list:
        LIVE_SESSION["rr_intervals"] = rr_list[-30:]
    if mendi_score is not None:
        LIVE_SESSION["mendi_score"] = mendi_score
    LIVE_SESSION["source"] = data.get("source", "web_bluetooth")

    hrv_component = min(1.0, (rmssd or 0) / 80.0)
    coherence = data.get("coherence")
    if coherence is None and rmssd and hr:
        nn50 = sum(1 for i in range(1, len(rr_list)) if abs(rr_list[i] - rr_list[i-1]) > 50)
        pnn50 = nn50 / max(1, len(rr_list) - 1)
        coherence = min(1.0, pnn50 * 3.0 + hrv_component * 0.5)
    LIVE_SESSION["coherence"] = coherence

    mendi_lcc = 0.0
    if mendi_score is not None:
        mendi_lcc = LCC_TRALSE + (mendi_score / 100.0) * (LCC_RADIANT - LCC_TRALSE)

    if rmssd is not None and mendi_score is not None:
        lcc = hrv_component * 0.6 + mendi_lcc * 0.4
    elif rmssd is not None:
        lcc = hrv_component * 0.85
    elif mendi_score is not None:
        lcc = mendi_lcc
    else:
        lcc = 0.0

    LIVE_SESSION["lcc_proxy"] = round(lcc, 4)

    if lcc >= LCC_RADIANT:
        zone = "RADIANT"
    elif lcc >= LCC_HIGH:
        zone = "HIGH"
    elif lcc >= LCC_EMERICK:
        zone = "EMERICK"
    elif lcc >= LCC_TRALSE:
        zone = "TRALSE"
    else:
        zone = "BELOW"
    LIVE_SESSION["lcc_zone"] = zone

    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS live_session_stream (
                id SERIAL PRIMARY KEY,
                ts TIMESTAMP DEFAULT NOW(),
                hr INTEGER, rmssd FLOAT, sdnn FLOAT, coherence FLOAT,
                mendi_score INTEGER, lcc_proxy FLOAT, lcc_zone TEXT, source TEXT
            )
        """)
        cur.execute("""
            INSERT INTO live_session_stream
            (hr, rmssd, sdnn, coherence, mendi_score, lcc_proxy, lcc_zone, source)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
        """, (hr, rmssd, sdnn, coherence, mendi_score,
              LIVE_SESSION["lcc_proxy"], zone, LIVE_SESSION["source"]))
        conn.commit()
        conn.close()
    except Exception:
        pass

    return web.json_response({"ok": True, "lcc_proxy": LIVE_SESSION["lcc_proxy"], "zone": zone})


async def live_biometric_get_handler(request):
    """Return current live biometric state for Streamlit polling."""
    return web.json_response(LIVE_SESSION)


# ============================================================
# MYCELIAL RESONANCE — LIVE CLOSED-LOOP BIOFEEDBACK ENDPOINTS
# ============================================================

async def mycelial_state_handler(request):
    """Return latest band-power state + estimated alpha-peak."""
    try:
        import mycelial_resonance_engine as _mre
        s = _mre.read_current_state()
        if not s:
            return web.json_response({"ok": False, "error": "no state"}, status=404)
        peak = _mre.estimate_alpha_peak(s)
        created = s.get("created_at")
        age_s = None
        if created:
            try:
                age_s = (datetime.now() - created).total_seconds()
            except Exception:
                age_s = None
        return web.json_response({
            "ok": True,
            "alpha_peak_hz": round(float(peak), 3),
            "alpha": float(s.get("alpha") or 0),
            "beta": float(s.get("beta") or 0),
            "theta": float(s.get("theta") or 0),
            "gamma": float(s.get("gamma") or 0),
            "delta": float(s.get("delta") or 0),
            "heart_rate": int(s.get("heart_rate") or 0),
            "rmssd": float(s.get("rmssd") or 0),
            "coherence": float(s.get("coherence") or 0),
            "session_id": s.get("session_id"),
            "sample_age_s": age_s,
        })
    except Exception as e:
        return web.json_response({"ok": False, "error": str(e)}, status=500)


async def mycelial_attractors_handler(request):
    """Return the registered attractor catalog."""
    try:
        import mycelial_resonance_engine as _mre
        out = []
        for k, a in _mre.MOOD_ATTRACTORS.items():
            out.append({
                "key": k, "name": a.name, "target_hz": a.target_hz,
                "overlay_hz": getattr(a, "overlay_hz", None),
                "description": a.description,
            })
        return web.json_response({"ok": True, "attractors": out})
    except Exception as e:
        return web.json_response({"ok": False, "error": str(e)}, status=500)


async def mycelial_generate_handler(request):
    """Generate a calibrated WAV for the chosen attractor; return relative URL."""
    try:
        import mycelial_resonance_engine as _mre
        body = await request.json()
        mood_key = body.get("mood_key", "BLISSFUL_EMPATHIC")
        duration_s = int(body.get("duration_s", 900))
        harmonic_bed = bool(body.get("harmonic_bed", True))
        result = _mre.generate_for_mood(
            mood_key=mood_key, duration_s=duration_s,
            use_current_state=True, mode="isochronic",
            harmonic_bed=harmonic_bed,
        )
        fname = os.path.basename(result["path"])
        return web.json_response({
            "ok": True,
            "wav_url": f"/api/mycelial/track/{fname}",
            "start_hz": result["start_hz"],
            "target_hz": result["target_hz"],
            "duration_s": result["duration_s"],
        })
    except Exception as e:
        return web.json_response({"ok": False, "error": str(e)}, status=500)


async def mycelial_track_handler(request):
    """Serve a generated WAV from tracks/."""
    fname = request.match_info.get("fname", "")
    if "/" in fname or "\\" in fname or ".." in fname:
        return web.Response(status=400, text="bad name")
    path = os.path.join("tracks", fname)
    if not os.path.isfile(path):
        return web.Response(status=404, text="not found")
    return web.FileResponse(path, headers={"Content-Type": "audio/wav"})


async def mycelial_log_handler(request):
    """Persist a completed live session to mre_live_sessions."""
    try:
        import mycelial_resonance_engine as _mre
        b = await request.json()
        rid = _mre.save_live_session_log(
            mood_key=b.get("mood_key", "UNKNOWN"),
            target_hz=float(b.get("target_hz", 0)),
            baseline_peak_hz=float(b.get("baseline_peak_hz", 0)),
            final_peak_hz=float(b.get("final_peak_hz", 0)),
            drift_hz=float(b.get("drift_hz", 0)),
            time_in_band_pct=float(b.get("time_in_band_pct", 0)),
            samples=int(b.get("samples", 0)),
            baseline_min=float(b.get("baseline_min", 0)),
            steering_min=float(b.get("steering_min", 0)),
            notes=str(b.get("notes", "web")),
        )
        return web.json_response({"ok": True, "id": rid})
    except Exception as e:
        return web.json_response({"ok": False, "error": str(e)}, status=500)


async def mycelial_sessions_handler(request):
    """Return last 10 logged live sessions."""
    try:
        with psycopg2.connect(os.environ["DATABASE_URL"]) as conn:
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT id, started_at, mood_key, target_hz,
                           baseline_peak_hz, final_peak_hz, drift_hz,
                           time_in_band_pct, samples
                    FROM mre_live_sessions
                    ORDER BY started_at DESC LIMIT 10
                """)
                rows = cur.fetchall()
        out = [{
            "id": r[0],
            "started_at": r[1].isoformat() if r[1] else None,
            "mood_key": r[2], "target_hz": float(r[3]) if r[3] is not None else None,
            "baseline_peak_hz": float(r[4]) if r[4] is not None else None,
            "final_peak_hz": float(r[5]) if r[5] is not None else None,
            "drift_hz": float(r[6]) if r[6] is not None else None,
            "time_in_band_pct": float(r[7]) if r[7] is not None else None,
            "samples": int(r[8]) if r[8] is not None else 0,
        } for r in rows]
        return web.json_response({"ok": True, "sessions": out})
    except Exception as e:
        return web.json_response({"ok": True, "sessions": [], "warning": str(e)})


async def mycelial_page_handler(request):
    """Self-contained live closed-loop biofeedback HTML page."""
    return web.Response(text=MYCELIAL_HTML, content_type="text/html")


MYCELIAL_HTML = r"""<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>🍄 Mycelial Resonance — Live Closed-Loop Biofeedback</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
  *{box-sizing:border-box;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
  body{margin:0;background:#0d0a16;color:#eaddff;padding:20px;max-width:1200px;margin:auto}
  h1{color:#c89bff;margin:0 0 4px 0}
  .sub{color:#9b86c4;margin-bottom:20px;font-size:14px}
  .grid{display:grid;grid-template-columns:1fr 1fr;gap:20px;margin-bottom:20px}
  .card{background:#1a142b;border:1px solid #3a2a5c;border-radius:10px;padding:16px}
  label{display:block;font-size:13px;margin:10px 0 4px 0;color:#b6a3d8}
  select,input[type=range],input[type=number]{width:100%;background:#2a1f44;border:1px solid #4a3870;color:#eaddff;padding:7px;border-radius:6px;font-size:14px}
  input[type=checkbox]{margin-right:6px;transform:scale(1.2)}
  .row{display:flex;gap:8px;align-items:center}
  button{background:linear-gradient(135deg,#a86ef0,#6e3fc8);color:white;border:none;padding:12px 18px;
         border-radius:8px;font-size:15px;font-weight:600;cursor:pointer;width:100%;margin-top:10px}
  button:hover{filter:brightness(1.15)}
  button:disabled{opacity:.4;cursor:not-allowed}
  .phase{font-size:22px;font-weight:700;color:#fff;padding:14px;border-radius:8px;text-align:center;margin-bottom:14px}
  .phase.baseline{background:linear-gradient(90deg,#1f4480,#3060c0)}
  .phase.steering{background:linear-gradient(90deg,#1f8050,#30c080)}
  .phase.debrief{background:linear-gradient(90deg,#80501f,#c08030)}
  .phase.idle{background:#2a1f44;color:#9b86c4}
  .metrics{display:grid;grid-template-columns:repeat(5,1fr);gap:10px;margin-bottom:14px}
  .m{background:#2a1f44;padding:10px;border-radius:6px;text-align:center}
  .m .v{font-size:20px;font-weight:700;color:#fff}
  .m .l{font-size:11px;color:#9b86c4;margin-top:2px;text-transform:uppercase;letter-spacing:.05em}
  .pre-flight{background:#241936;padding:10px;border-radius:6px;font-size:13px;margin-bottom:10px}
  .ok{color:#7be38f}.warn{color:#f0c060}.err{color:#f06070}
  audio{width:100%;margin:10px 0}
  .progress-wrap{background:#241936;height:24px;border-radius:6px;overflow:hidden;margin-bottom:10px;position:relative}
  .progress-bar{background:linear-gradient(90deg,#6e3fc8,#a86ef0);height:100%;transition:width .3s}
  .progress-text{position:absolute;top:0;left:0;right:0;line-height:24px;text-align:center;font-size:12px;font-weight:600;color:white}
  table{width:100%;border-collapse:collapse;font-size:12px}
  th,td{padding:6px;border-bottom:1px solid #3a2a5c;text-align:left}
  th{color:#9b86c4;font-weight:600}
  .desc{font-size:12px;color:#9b86c4;font-style:italic;margin-top:4px}
  #chartWrap{height:280px;background:#241936;border-radius:6px;padding:8px}
</style></head><body>

<h1>🍄 Mycelial Resonance — Live Closed-Loop Biofeedback</h1>
<div class="sub">Baseline → calibrated audio → live α-peak steering → debrief. Reads <code>esp32_biometric_data</code>.</div>

<div class="grid">
  <div class="card">
    <h3 style="margin-top:0;color:#c89bff">Configuration</h3>
    <label>Mood attractor</label>
    <select id="mood"></select>
    <div id="moodDesc" class="desc"></div>

    <label>Baseline duration: <span id="baselineLbl">5</span> min</label>
    <input type="range" id="baseline" min="1" max="10" value="5" step="1"/>

    <label>Steering duration: <span id="steeringLbl">15</span> min</label>
    <input type="range" id="steering" min="3" max="30" value="15" step="1"/>

    <label>Poll interval: <span id="pollLbl">2</span> sec</label>
    <input type="range" id="poll" min="1" max="5" value="2" step="1"/>

    <label>Target band tolerance: ±<span id="bandLbl">0.5</span> Hz</label>
    <input type="range" id="band" min="0.2" max="2.0" value="0.5" step="0.1"/>

    <label><input type="checkbox" id="bed" checked/> L4 GILE harmonic bed</label>

    <button id="startBtn">▶ Start live closed-loop session</button>
    <button id="stopBtn" style="background:#604070;display:none">■ Stop session</button>
  </div>

  <div class="card">
    <h3 style="margin-top:0;color:#c89bff">Pre-flight</h3>
    <div id="preflight" class="pre-flight">Checking live stream...</div>
    <div class="metrics">
      <div class="m"><div class="v" id="pfAlpha">—</div><div class="l">α</div></div>
      <div class="m"><div class="v" id="pfPeak">—</div><div class="l">α-peak Hz</div></div>
      <div class="m"><div class="v" id="pfHr">—</div><div class="l">HR bpm</div></div>
      <div class="m"><div class="v" id="pfRmssd">—</div><div class="l">RMSSD</div></div>
      <div class="m"><div class="v" id="pfAge">—</div><div class="l">age s</div></div>
    </div>
  </div>
</div>

<div class="card">
  <div id="phase" class="phase idle">IDLE — configure and press Start</div>
  <div id="audioWrap"></div>
  <div class="metrics">
    <div class="m"><div class="v" id="mPeak">—</div><div class="l">Current α-peak</div></div>
    <div class="m"><div class="v" id="mBaseline">—</div><div class="l">Baseline mean</div></div>
    <div class="m"><div class="v" id="mTarget">—</div><div class="l">Target Hz</div></div>
    <div class="m"><div class="v" id="mDelta">—</div><div class="l">Δ to target</div></div>
    <div class="m"><div class="v" id="mHr">—</div><div class="l">HR bpm</div></div>
  </div>
  <div class="progress-wrap"><div class="progress-bar" id="bandBar" style="width:0%"></div>
    <div class="progress-text" id="bandText">Time-in-band: —</div></div>
  <div id="chartWrap"><canvas id="chart"></canvas></div>
</div>

<div class="card" style="margin-top:20px">
  <h3 style="margin-top:0;color:#c89bff">Recent sessions</h3>
  <div id="sessions">loading...</div>
</div>

<script>
let ATTRACTORS=[],MOOD={},chart,history=[],baselinePeaks=[],steeringPeaks=[];
let phaseState="idle",startT=null,baselineDur=0,steeringDur=0,pollInterval=2000,bandHz=0.5;
let pollTimer=null,audioStarted=false,abortRequested=false;

async function loadAttractors(){
  const r=await fetch("/api/mycelial/attractors");const j=await r.json();
  ATTRACTORS=j.attractors||[];
  const sel=document.getElementById("mood");sel.innerHTML="";
  ATTRACTORS.forEach(a=>{MOOD[a.key]=a;const o=document.createElement("option");
    o.value=a.key;o.textContent=`${a.name} (${a.target_hz} Hz)`;sel.appendChild(o);});
  if(MOOD.BLISSFUL_EMPATHIC) sel.value="BLISSFUL_EMPATHIC";
  updateDesc();
}
function updateDesc(){const k=document.getElementById("mood").value;
  document.getElementById("moodDesc").textContent=MOOD[k]?.description||"";}
document.getElementById("mood").addEventListener("change",updateDesc);

["baseline","steering","poll","band"].forEach(id=>{
  document.getElementById(id).addEventListener("input",e=>{
    document.getElementById(id+"Lbl").textContent=e.target.value;
  });
});

async function preflight(){
  try{const r=await fetch("/api/mycelial/state");const s=await r.json();
    if(!s.ok){document.getElementById("preflight").innerHTML='<span class="err">⚠️ No state — start your bridge.</span>';return;}
    document.getElementById("pfAlpha").textContent=s.alpha.toFixed(3);
    document.getElementById("pfPeak").textContent=s.alpha_peak_hz.toFixed(2);
    document.getElementById("pfHr").textContent=s.heart_rate;
    document.getElementById("pfRmssd").textContent=s.rmssd.toFixed(1);
    document.getElementById("pfAge").textContent=s.sample_age_s!==null?s.sample_age_s.toFixed(1):"?";
    let html="";
    if(s.sample_age_s===null||s.sample_age_s>15) html='<span class="warn">⚠️ Sample is '+(s.sample_age_s||"unknown")+'s old — your bridge isn\'t streaming. Live α-peak will be flat.</span>';
    else if(s.heart_rate===0) html='<span class="warn">⚠️ HR=0 — Polar H10 not connected. EEG will work but HRV metrics flat.</span>';
    else html='<span class="ok">✅ Stream is live — ready to start.</span>';
    document.getElementById("preflight").innerHTML=html;
  }catch(e){document.getElementById("preflight").innerHTML='<span class="err">'+e+'</span>';}
}
preflight();setInterval(preflight,5000);

async function loadSessions(){
  try{const r=await fetch("/api/mycelial/sessions");const j=await r.json();
    const s=j.sessions||[];if(!s.length){document.getElementById("sessions").innerHTML='<div class="desc">(no sessions logged yet)</div>';return;}
    let h='<table><thead><tr><th>id</th><th>when</th><th>mood</th><th>target</th><th>baseline</th><th>final</th><th>drift</th><th>in-band %</th><th>samples</th></tr></thead><tbody>';
    s.forEach(r=>{h+=`<tr><td>${r.id}</td><td>${(r.started_at||"").replace("T"," ").slice(0,19)}</td><td>${r.mood_key}</td><td>${r.target_hz?.toFixed(2)}</td><td>${r.baseline_peak_hz?.toFixed(2)}</td><td>${r.final_peak_hz?.toFixed(2)}</td><td>${r.drift_hz?.toFixed(2)}</td><td>${(r.time_in_band_pct*100).toFixed(0)}%</td><td>${r.samples}</td></tr>`;});
    h+="</tbody></table>";document.getElementById("sessions").innerHTML=h;
  }catch(e){document.getElementById("sessions").innerHTML='<div class="err">'+e+'</div>';}
}
loadSessions();

function initChart(targetHz){
  if(chart)chart.destroy();
  const ctx=document.getElementById("chart").getContext("2d");
  chart=new Chart(ctx,{type:"line",data:{labels:[],datasets:[
    {label:"α-peak (Hz)",data:[],borderColor:"#c89bff",backgroundColor:"rgba(200,155,255,.2)",tension:.3,pointRadius:1.5},
    {label:"target",data:[],borderColor:"#7be38f",borderDash:[6,4],pointRadius:0,fill:false},
    {label:"target +band",data:[],borderColor:"#3a6f48",borderDash:[2,3],pointRadius:0,fill:false},
    {label:"target -band",data:[],borderColor:"#3a6f48",borderDash:[2,3],pointRadius:0,fill:false},
  ]},options:{responsive:true,maintainAspectRatio:false,
    scales:{x:{ticks:{color:"#9b86c4"},grid:{color:"#3a2a5c"}},
            y:{ticks:{color:"#9b86c4"},grid:{color:"#3a2a5c"},suggestedMin:targetHz-2,suggestedMax:targetHz+2}},
    plugins:{legend:{labels:{color:"#eaddff"}}}}});
}

function setPhase(label,cls){const p=document.getElementById("phase");p.className="phase "+cls;p.textContent=label;}
function fmtTime(s){s=Math.max(0,Math.floor(s));return Math.floor(s/60)+":"+String(s%60).padStart(2,"0");}

async function poll(){
  if(abortRequested) return finishSession();
  const now=Date.now()/1000, elapsed=now-startT;
  const totalDur=baselineDur+steeringDur;
  if(elapsed>=totalDur) return finishSession();

  let s=null;
  try{const r=await fetch("/api/mycelial/state");if(r.ok){s=await r.json();}}catch(e){}
  if(s&&s.ok){
    history.push({t:elapsed,peak:s.alpha_peak_hz,alpha:s.alpha,beta:s.beta,theta:s.theta,gamma:s.gamma,hr:s.heart_rate,rmssd:s.rmssd});
    document.getElementById("mHr").textContent=s.heart_rate;
  }

  const inBaseline=elapsed<baselineDur;
  const targetHz=MOOD[document.getElementById("mood").value].target_hz;

  if(inBaseline){
    setPhase(`🔵 BASELINE — remaining ${fmtTime(baselineDur-elapsed)}`,"baseline");
    if(s&&s.ok) baselinePeaks.push(s.alpha_peak_hz);
  } else {
    setPhase(`🟢 STEERING — remaining ${fmtTime(totalDur-elapsed)}`,"steering");
    if(s&&s.ok) steeringPeaks.push(s.alpha_peak_hz);
    if(!audioStarted){
      audioStarted=true;
      const baselineMean=baselinePeaks.length?baselinePeaks.reduce((a,b)=>a+b,0)/baselinePeaks.length:10.0;
      document.getElementById("audioWrap").innerHTML=`<div class="desc">⏳ Generating ${steeringDur/60} min track calibrated to baseline ${baselineMean.toFixed(2)} Hz...</div>`;
      try{
        const gr=await fetch("/api/mycelial/generate",{method:"POST",headers:{"Content-Type":"application/json"},
          body:JSON.stringify({mood_key:document.getElementById("mood").value,duration_s:steeringDur,harmonic_bed:document.getElementById("bed").checked})});
        const gj=await gr.json();
        if(gj.ok){
          document.getElementById("audioWrap").innerHTML=`<audio controls autoplay src="${gj.wav_url}"></audio><div class="desc">🔊 Drift ${gj.start_hz} Hz → ${gj.target_hz} Hz over ${gj.duration_s}s · L4 bed ${document.getElementById("bed").checked?"on":"off"}</div>`;
        } else {document.getElementById("audioWrap").innerHTML='<div class="err">Audio generation failed: '+gj.error+'</div>';}
      }catch(e){document.getElementById("audioWrap").innerHTML='<div class="err">'+e+'</div>';}
    }
  }

  // metrics
  if(history.length){
    const last=history[history.length-1];
    document.getElementById("mPeak").textContent=last.peak.toFixed(2)+" Hz";
    document.getElementById("mTarget").textContent=targetHz.toFixed(2)+" Hz";
    document.getElementById("mDelta").textContent=Math.abs(last.peak-targetHz).toFixed(2)+" Hz";
  }
  if(baselinePeaks.length){
    const bm=baselinePeaks.reduce((a,b)=>a+b,0)/baselinePeaks.length;
    document.getElementById("mBaseline").textContent=bm.toFixed(2)+" Hz";
  }
  // chart
  if(chart&&history.length){
    chart.data.labels=history.map(h=>Math.round(h.t)+"s");
    chart.data.datasets[0].data=history.map(h=>h.peak);
    chart.data.datasets[1].data=history.map(_=>targetHz);
    chart.data.datasets[2].data=history.map(_=>targetHz+bandHz);
    chart.data.datasets[3].data=history.map(_=>targetHz-bandHz);
    chart.update("none");
  }
  // band progress
  if(steeringPeaks.length){
    const inBand=steeringPeaks.filter(p=>Math.abs(p-targetHz)<bandHz).length;
    const pct=inBand/steeringPeaks.length;
    document.getElementById("bandBar").style.width=(pct*100)+"%";
    document.getElementById("bandText").textContent=`Time-in-target-band (±${bandHz} Hz): ${(pct*100).toFixed(0)}%  (${inBand}/${steeringPeaks.length})`;
  }
  pollTimer=setTimeout(poll,pollInterval);
}

async function finishSession(){
  clearTimeout(pollTimer);pollTimer=null;
  const targetHz=MOOD[document.getElementById("mood").value].target_hz;
  const bm=baselinePeaks.length?baselinePeaks.reduce((a,b)=>a+b,0)/baselinePeaks.length:0;
  const sm=steeringPeaks.length?steeringPeaks.reduce((a,b)=>a+b,0)/steeringPeaks.length:bm;
  const drift=bm-sm;
  const inBand=steeringPeaks.length?steeringPeaks.filter(p=>Math.abs(p-targetHz)<bandHz).length/steeringPeaks.length:0;
  setPhase(`📊 DEBRIEF — baseline ${bm.toFixed(2)} → final ${sm.toFixed(2)} (drift ${(-drift>=0?"+":"")+(-drift).toFixed(2)} Hz toward target) · in-band ${(inBand*100).toFixed(0)}%`,"debrief");
  document.getElementById("startBtn").style.display="";
  document.getElementById("stopBtn").style.display="none";
  // log
  if(baselinePeaks.length&&steeringPeaks.length){
    try{
      await fetch("/api/mycelial/log",{method:"POST",headers:{"Content-Type":"application/json"},
        body:JSON.stringify({mood_key:document.getElementById("mood").value,target_hz:targetHz,
          baseline_peak_hz:bm,final_peak_hz:sm,drift_hz:drift,time_in_band_pct:inBand,
          samples:history.length,baseline_min:baselineDur/60,steering_min:steeringDur/60,notes:"web"})});
      loadSessions();
    }catch(e){}
  }
}

document.getElementById("startBtn").addEventListener("click",()=>{
  history=[];baselinePeaks=[];steeringPeaks=[];audioStarted=false;abortRequested=false;
  baselineDur=parseInt(document.getElementById("baseline").value)*60;
  steeringDur=parseInt(document.getElementById("steering").value)*60;
  pollInterval=parseInt(document.getElementById("poll").value)*1000;
  bandHz=parseFloat(document.getElementById("band").value);
  const targetHz=MOOD[document.getElementById("mood").value].target_hz;
  initChart(targetHz);
  document.getElementById("audioWrap").innerHTML="";
  document.getElementById("startBtn").style.display="none";
  document.getElementById("stopBtn").style.display="";
  startT=Date.now()/1000;poll();
});
document.getElementById("stopBtn").addEventListener("click",()=>{abortRequested=true;});

loadAttractors();
</script>
</body></html>
"""


async def api_lcc_handler(request):
    """Calculate LCC (Law of Correlational Causation) proxy."""
    key_data, error = await validate_api_key(request)
    if error:
        return error
    
    try:
        data = await request.json()
    except:
        data = {}
    
    hrv_coherence = data.get('hrv_coherence', 0.5)
    alpha_power = data.get('alpha_power', 0.5)
    hrv_rmssd = data.get('hrv_rmssd', 50)
    
    hrv_component = min(1.0, hrv_coherence)
    eeg_component = min(1.0, alpha_power)
    stability_component = min(1.0, hrv_rmssd / 100)
    
    lcc_raw = (hrv_component * 0.4 + eeg_component * 0.4 + stability_component * 0.2)
    lcc_calibrated = lcc_raw * 0.85 + 0.15 * (lcc_raw ** 2)
    
    noise_floor = 0.42
    causation_threshold = 0.85
    
    if lcc_calibrated < noise_floor:
        signal_quality = 'below_noise_floor'
    elif lcc_calibrated < causation_threshold:
        signal_quality = 'signal_detected'
    else:
        signal_quality = 'causation_threshold_exceeded'
    
    return web.json_response({
        'lcc_score': round(lcc_calibrated, 4),
        'components': {'hrv': round(hrv_component, 4), 'eeg': round(eeg_component, 4), 'stability': round(stability_component, 4)},
        'thresholds': {'noise_floor': noise_floor, 'causation_threshold': causation_threshold},
        'signal_quality': signal_quality
    })

async def api_gsa_handler(request):
    """GSA (Grand Stock Algorithm) trading signal."""
    key_data, error = await validate_api_key(request)
    if error:
        return error
    
    try:
        data = await request.json()
    except:
        data = {}
    
    symbol = data.get('symbol', 'SPY')
    price = data.get('price', 100)
    volatility = data.get('volatility', 0.2)
    
    if volatility < 0.15:
        regime = 'low_volatility'
        base_confidence = 0.7
    elif volatility < 0.30:
        regime = 'normal'
        base_confidence = 0.6
    else:
        regime = 'high_volatility'
        base_confidence = 0.4
    
    import random
    random.seed(hash(f"{symbol}{price}{datetime.now().date()}"))
    signal_strength = random.uniform(-1, 1)
    
    if signal_strength > 0.3:
        signal = 'BUY'
    elif signal_strength < -0.3:
        signal = 'SELL'
    else:
        signal = 'HOLD'
    
    return web.json_response({
        'symbol': symbol,
        'signal': signal,
        'confidence': round(base_confidence * abs(signal_strength), 4),
        'regime': regime,
        'timestamp': datetime.now().isoformat(),
        'disclaimer': 'Not financial advice.'
    })

async def api_tralse_handler(request):
    """Evaluate proposition using Tralse logic."""
    key_data, error = await validate_api_key(request)
    if error:
        return error
    
    try:
        data = await request.json()
    except:
        data = {}
    
    proposition = data.get('proposition', '')
    evidence_for = data.get('evidence_for', 0.5)
    evidence_against = data.get('evidence_against', 0.5)
    
    truth_value = (evidence_for - evidence_against + 1) / 2
    truth_value = max(0, min(1, truth_value))
    
    if truth_value > 0.92:
        classification = 'TRUE'
    elif truth_value > 0.58:
        classification = 'TRALSE_TRUE'
    elif truth_value > 0.42:
        classification = 'TRALSE_FALSE'
    else:
        classification = 'FALSE'
    
    return web.json_response({
        'proposition': proposition,
        'truth_value': round(truth_value, 4),
        'classification': classification,
        'thresholds': {'true': 0.92, 'tralse_true': 0.58, 'tralse_false': 0.42, 'false': 0}
    })

async def gsa_landing_handler(request):
    """Serve the GSA landing page"""
    try:
        with open('content/gsa_landing_page.html', 'r') as f:
            html = f.read()
        return web.Response(text=html, content_type='text/html')
    except Exception as e:
        return web.Response(text=f"Error loading landing page: {e}", status=500)

VALID_GSA_PRICES = {
    ('basic', 'monthly'): 'price_1SjrKmI62HaqkFeXoLjsbwV2',
    ('basic', 'yearly'): 'price_1SjrKmI62HaqkFeXcdSpNdAi',
    ('pro', 'monthly'): 'price_1SjrKnI62HaqkFeXveDeJWYV',
    ('pro', 'yearly'): 'price_1SjrKnI62HaqkFeX9mMCFmMu',
    ('enterprise', 'monthly'): 'price_1SjrKoI62HaqkFeXEVNTYna4',
}

async def gsa_checkout_handler(request):
    """Create Stripe checkout session for GSA subscription."""
    try:
        data = await request.json()
        tier = data.get('tier', 'basic')
        billing = data.get('billing', 'monthly')
        
        if tier not in ('basic', 'pro', 'enterprise'):
            return web.json_response({'error': 'Invalid tier'}, status=400)
        if billing not in ('monthly', 'yearly'):
            return web.json_response({'error': 'Invalid billing cycle'}, status=400)
        
        price_id = VALID_GSA_PRICES.get((tier, billing))
        if not price_id:
            return web.json_response({'error': 'Invalid plan selection'}, status=400)
        
        secret_key = await get_stripe_client()
        if not secret_key:
            return web.json_response({'error': 'Payment system unavailable'}, status=500)
        
        host = request.headers.get('Host', 'localhost:5000')
        protocol = 'https' if 'replit' in host else 'http'
        base_url = f"{protocol}://{host}"
        
        import stripe
        stripe.api_key = secret_key
        
        session = await asyncio.get_event_loop().run_in_executor(
            None,
            lambda: stripe.checkout.Session.create(
                payment_method_types=['card'],
                line_items=[{'price': price_id, 'quantity': 1}],
                mode='subscription',
                success_url=f"{base_url}/gsa?success=true&tier={tier}",
                cancel_url=f"{base_url}/gsa?canceled=true",
                metadata={'tier': tier, 'billing': billing}
            )
        )
        
        return web.json_response({'url': session.url})
    except Exception as e:
        print(f"Checkout error: {e}")
        return web.json_response({'error': 'Unable to create checkout session'}, status=500)

async def get_stripe_client():
    """Get Stripe client from Replit connection."""
    try:
        hostname = os.environ.get('REPLIT_CONNECTORS_HOSTNAME')
        token = os.environ.get('REPL_IDENTITY')
        
        if not hostname or not token:
            return None
        
        url = f"https://{hostname}/api/v2/connection?include_secrets=true&connector_names=stripe&environment=development"
        
        async with aiohttp.ClientSession() as client_session:
            async with client_session.get(url, headers={
                'Accept': 'application/json',
                'X_REPLIT_TOKEN': f'repl {token}'
            }) as resp:
                data = await resp.json()
        
        settings = data.get('items', [{}])[0].get('settings', {})
        secret_key = settings.get('secret')
        
        if not secret_key:
            return None
        
        return secret_key
    except Exception as e:
        print(f"Stripe client error: {e}")
        return None

def start_streamlit():
    global streamlit_proc
    print(f"🚀 Starting Streamlit on internal port {STREAMLIT_PORT}...")
    streamlit_proc = subprocess.Popen([
        'streamlit', 'run', 'ti_website.py',
        '--server.port', str(STREAMLIT_PORT),
        '--server.headless', 'true',
        '--server.address', 'localhost'
    ])

def cleanup(signum=None, frame=None):
    global streamlit_proc
    if streamlit_proc:
        streamlit_proc.terminate()
        streamlit_proc.wait()
    sys.exit(0)

async def wait_for_streamlit(max_retries=30, delay=1.0):
    """Wait for Streamlit to be ready by polling the health endpoint"""
    import socket
    for i in range(max_retries):
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(1)
            result = sock.connect_ex(('127.0.0.1', STREAMLIT_PORT))
            sock.close()
            if result == 0:
                print(f"✅ Streamlit ready on port {STREAMLIT_PORT}")
                return True
        except Exception:
            pass
        print(f"⏳ Waiting for Streamlit... ({i+1}/{max_retries})")
        await asyncio.sleep(delay)
    print(f"❌ Streamlit failed to start after {max_retries} attempts")
    return False

async def download_bridge_handler(request):
    """Serve bridge scripts as direct downloads."""
    script = request.rel_url.query.get('script', 'polar')
    base = os.path.dirname(__file__)
    options = {
        'polar':        ('polar_h10_bridge.py',      os.path.join(base, 'polar_h10_bridge.py')),
        'muse':         ('mind_monitor_bridge.py',   os.path.join(base, 'mind_monitor_bridge.py')),
        'full':         ('ACER_LIVE_BRIDGE.py',      os.path.join(base, 'hardware', 'ACER_LIVE_BRIDGE.py')),
    }
    fname, fpath = options.get(script, options['polar'])
    try:
        with open(fpath, 'r') as f:
            content = f.read()
        return web.Response(
            body=content.encode('utf-8'),
            content_type='application/octet-stream',
            headers={'Content-Disposition': f'attachment; filename="{fname}"'}
        )
    except Exception as e:
        return web.json_response({"error": f"Script not found: {e}"}, status=500)


async def download_page_handler(request):
    """HTML setup page with download buttons for Acer bridge scripts."""
    html = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Mood Amplifier — Acer Bridge Setup</title>
<style>
  body { font-family: monospace; background: #0a0a0a; color: #e0e0e0; max-width: 700px; margin: 40px auto; padding: 20px; }
  h1 { color: #7df; margin-bottom: 4px; }
  h2 { color: #adf; margin-top: 32px; border-bottom: 1px solid #333; padding-bottom: 6px; }
  .step { background: #111; border-left: 3px solid #4af; padding: 12px 16px; margin: 12px 0; border-radius: 4px; }
  code { background: #1a1a2e; color: #7df; padding: 2px 6px; border-radius: 3px; }
  .btn { display: inline-block; background: #1a4a8a; color: #fff; padding: 10px 22px; border-radius: 6px;
         text-decoration: none; margin: 6px 6px 6px 0; font-size: 15px; border: 1px solid #4af; }
  .btn:hover { background: #2a6aba; }
  .note { color: #fa8; font-size: 13px; margin-top: 6px; }
  .green { color: #4f8; }
  .ip { color: #ff8; font-size: 20px; font-weight: bold; }
</style>
</head>
<body>
<h1>🧠❤️ Mood Amplifier — Acer Bridge Scripts</h1>
<p>You are viewing this page on your Acer. Follow all 4 steps below.</p>

<h2>Step 1 — Download both scripts right now</h2>
<a class="btn" href="/download/bridge?script=muse">⬇ mind_monitor_bridge.py</a>
<a class="btn" href="/download/bridge?script=polar">⬇ polar_h10_bridge.py</a>
<p class="note">They will land in your <b>Downloads</b> folder automatically.</p>

<h2>Step 2 — Install dependencies (one time only)</h2>
<div class="step">Open <b>Command Prompt</b> and paste this exactly:<br><br>
<code>python -m pip install python-osc requests bleak</code><br><br>
<span class="note">⚠ Use <b>python -m pip</b> — not just "pip" — on Python 3.14</span>
</div>

<h2>Step 3 — Mind Monitor (Muse 2 EEG)</h2>
<div class="step">
<b>On your phone (Mind Monitor app):</b><br>
1. Connect Muse 2 in Mind Monitor<br>
2. Settings → OSC Stream<br>
3. Host = <span class="ip">192.168.4.46</span> &nbsp;(your Acer's WiFi IP)<br>
4. Port = <code>5005</code><br>
5. Toggle <b>OSC Stream ON</b><br><br>
<b>On Acer — Terminal 1, paste both lines:</b><br>
<code>cd %USERPROFILE%\Downloads</code><br>
<code>python mind_monitor_bridge.py</code><br><br>
<span class="green">✓ You'll see alpha/beta/theta bars printing every 2 seconds.</span><br><br>
<span class="note">🔥 If it says "No Muse data" after 10 seconds:</span><br>
<span class="note">Windows Firewall is blocking it. Run this in Command Prompt <b>as Administrator</b>:</span><br>
<code>netsh advfirewall firewall add rule name="MindMonitorBridge" dir=in action=allow protocol=UDP localport=5005</code><br>
<span class="note">Then close and re-run the script.</span>
</div>

<h2>Step 4 — Polar H10 (Heart Rate + HRV)</h2>
<div class="step">
<b>Before running:</b> Pair Polar H10 in Windows first:<br>
Windows Settings → Bluetooth &amp; devices → Add device → Bluetooth → select <b>Polar H10</b><br><br>
<b>Physical:</b> Wet the two electrode bumps on the strap. Wear snugly.<br>
Close Polar Flow / Polar Beat — they block BLE access.<br><br>
<b>On Acer — Terminal 2, paste both lines:</b><br>
<code>cd %USERPROFILE%\Downloads</code><br>
<code>python polar_h10_bridge.py</code><br><br>
<span class="green">✓ Script will list all BLE devices it finds, then connect and upload every 5s.</span><br><br>
<span class="note">If the scan shows your Polar but still fails: remove it from Bluetooth settings and re-pair.</span>
</div>

<h2>Step 5 — Open the Mood Amplifier</h2>
<div class="step">
Once both scripts are running, open the Mood Amplifier Hub in your browser.<br>
Both devices will show as connected within ~10 seconds.
</div>
</body>
</html>"""
    return web.Response(text=html, content_type='text/html')

async def main():
    start_streamlit()
    await wait_for_streamlit()
    await init_api_tables()
    
    app = web.Application()
    
    app.router.add_route('*', '/api/health', health_handler)
    app.router.add_route('*', '/api/debug', debug_handler)
    app.router.add_route('*', '/api/upload', upload_handler)
    app.router.add_route('*', '/api/biometric/upload', upload_handler)
    app.router.add_route('*', '/api/muse/upload', upload_handler)
    app.router.add_route('*', '/api/polar/upload', upload_handler)
    app.router.add_route('*', '/api/latest', latest_handler)
    app.router.add_route('*', '/api/esp32/latest', latest_handler)
    app.router.add_route('GET', '/api/mendi/latest', mendi_latest_handler)
    app.router.add_route('GET', '/api/polar/latest', polar_latest_handler)
    app.router.add_route('GET', '/api/muse/latest', muse_latest_handler)
    app.router.add_route('POST', '/api/biometric/live', live_biometric_post_handler)
    app.router.add_route('GET', '/api/biometric/current', live_biometric_get_handler)
    
    app.router.add_route('GET', '/api/v1/health', api_v1_health_handler)
    app.router.add_route('POST', '/api/v1/register', api_register_handler)
    app.router.add_route('POST', '/api/v1/lcc/calculate', api_lcc_handler)
    app.router.add_route('POST', '/api/v1/gsa/signal', api_gsa_handler)
    app.router.add_route('POST', '/api/v1/tralse/evaluate', api_tralse_handler)
    app.router.add_route('GET', '/gsa', gsa_landing_handler)
    app.router.add_route('GET', '/gsa/', gsa_landing_handler)
    app.router.add_route('POST', '/api/v1/gsa/checkout', gsa_checkout_handler)
    app.router.add_route('GET', '/download/bridge', download_bridge_handler)
    app.router.add_route('GET', '/download', download_page_handler)
    app.router.add_route('GET', '/download/', download_page_handler)
    app.router.add_route('GET', '/mycelial', mycelial_page_handler)
    app.router.add_route('GET', '/mycelial/', mycelial_page_handler)
    app.router.add_route('GET', '/api/mycelial/state', mycelial_state_handler)
    app.router.add_route('GET', '/api/mycelial/attractors', mycelial_attractors_handler)
    app.router.add_route('POST', '/api/mycelial/generate', mycelial_generate_handler)
    app.router.add_route('GET', '/api/mycelial/track/{fname}', mycelial_track_handler)
    app.router.add_route('POST', '/api/mycelial/log', mycelial_log_handler)
    app.router.add_route('GET', '/api/mycelial/sessions', mycelial_sessions_handler)

    app.router.add_route('*', '/{path:.*}', proxy_handler)
    
    runner = web.AppRunner(app)
    await runner.setup()
    site_5000 = web.TCPSite(runner, '0.0.0.0', 5000)
    site_5001 = web.TCPSite(runner, '0.0.0.0', 5001)

    print("\n" + "="*60)
    print("🌐 TI FRAMEWORK GATEWAY - Ports 5000 + 5001")
    print("="*60)
    print("📍 /api/upload -> EEG/biometric uploads")
    print("📍 /api/health -> Health check")
    print("📍 /api/v1/* -> TI Framework API (LCC, GSA, Tralse)")
    print("📍 /* -> Streamlit proxy")
    print("="*60 + "\n")

    await site_5000.start()
    await site_5001.start()
    
    while True:
        await asyncio.sleep(3600)

if __name__ == '__main__':
    signal.signal(signal.SIGTERM, cleanup)
    signal.signal(signal.SIGINT, cleanup)
    
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        cleanup()
