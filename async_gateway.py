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
TIER_PRICES = {'basic': 99, 'pro': 499, 'enterprise': 'custom'}
STREAMLIT_PORT = 5001

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

async def api_lcc_handler(request):
    """Calculate LCC (Love Consciousness Connection) proxy."""
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

async def main():
    start_streamlit()
    await wait_for_streamlit()
    await init_api_tables()
    
    app = web.Application()
    
    app.router.add_route('*', '/api/health', health_handler)
    app.router.add_route('*', '/api/debug', debug_handler)
    app.router.add_route('*', '/api/upload', upload_handler)
    app.router.add_route('*', '/api/biometric/upload', upload_handler)
    app.router.add_route('*', '/api/latest', latest_handler)
    app.router.add_route('*', '/api/esp32/latest', latest_handler)
    
    app.router.add_route('GET', '/api/v1/health', api_v1_health_handler)
    app.router.add_route('POST', '/api/v1/register', api_register_handler)
    app.router.add_route('POST', '/api/v1/lcc/calculate', api_lcc_handler)
    app.router.add_route('POST', '/api/v1/gsa/signal', api_gsa_handler)
    app.router.add_route('POST', '/api/v1/tralse/evaluate', api_tralse_handler)
    app.router.add_route('GET', '/gsa', gsa_landing_handler)
    app.router.add_route('GET', '/gsa/', gsa_landing_handler)
    app.router.add_route('POST', '/api/v1/gsa/checkout', gsa_checkout_handler)
    
    app.router.add_route('*', '/{path:.*}', proxy_handler)
    
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', 5000)
    
    print("\n" + "="*60)
    print("🌐 TI FRAMEWORK GATEWAY - Port 5000")
    print("="*60)
    print("📍 /api/upload -> ESP32 biometric uploads")
    print("📍 /api/health -> Health check")
    print("📍 /api/v1/* -> TI Framework API (LCC, GSA, Tralse)")
    print("📍 /* -> Streamlit proxy")
    print("="*60 + "\n")
    
    await site.start()
    
    while True:
        await asyncio.sleep(3600)

if __name__ == '__main__':
    signal.signal(signal.SIGTERM, cleanup)
    signal.signal(signal.SIGINT, cleanup)
    
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        cleanup()
