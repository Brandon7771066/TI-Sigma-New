"""
TI Framework API Licensing Server

This module provides the API infrastructure for licensing TI Framework components:
- LCC Proxy Engine
- GSA Stock Algorithm
- Mood Amplifier Safety Validation
- Tralse Logic Processor

Revenue Model:
- Basic: $99/month (100 API calls/day)
- Pro: $499/month (unlimited calls)
- Enterprise: Custom pricing

Author: Brandon Charles Emerick
Date: December 2025
"""

import os
import json
import hashlib
import secrets
from datetime import datetime, timedelta
from functools import wraps
from flask import Flask, request, jsonify, g
from flask_cors import CORS
import psycopg2
from psycopg2.extras import RealDictCursor

app = Flask(__name__)
CORS(app)

DATABASE_URL = os.environ.get('DATABASE_URL')

RATE_LIMITS = {
    'basic': 100,
    'pro': 10000,
    'enterprise': 100000
}

TIER_PRICES = {
    'basic': 99,
    'pro': 499,
    'enterprise': 'custom'
}

def get_db():
    """Get database connection."""
    if 'db' not in g:
        g.db = psycopg2.connect(DATABASE_URL, cursor_factory=RealDictCursor)
    return g.db

@app.teardown_appcontext
def close_db(error):
    """Close database connection."""
    db = g.pop('db', None)
    if db is not None:
        db.close()

def init_api_tables():
    """Initialize API licensing tables."""
    conn = psycopg2.connect(DATABASE_URL)
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
            last_reset DATE DEFAULT CURRENT_DATE,
            metadata JSONB DEFAULT '{}'
        )
    """)
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS api_usage (
            id SERIAL PRIMARY KEY,
            api_key_id INTEGER REFERENCES api_keys(id),
            endpoint VARCHAR(100) NOT NULL,
            timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            response_time_ms INTEGER,
            success BOOLEAN DEFAULT TRUE,
            request_data JSONB,
            response_summary TEXT
        )
    """)
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS api_billing (
            id SERIAL PRIMARY KEY,
            api_key_id INTEGER REFERENCES api_keys(id),
            billing_period_start DATE NOT NULL,
            billing_period_end DATE NOT NULL,
            tier VARCHAR(20) NOT NULL,
            amount_cents INTEGER NOT NULL,
            status VARCHAR(20) DEFAULT 'pending',
            paid_at TIMESTAMP
        )
    """)
    
    conn.commit()
    cur.close()
    conn.close()

def generate_api_key():
    """Generate a secure API key."""
    return f"ti_{secrets.token_hex(32)}"

def require_api_key(f):
    """Decorator to require valid API key."""
    @wraps(f)
    def decorated(*args, **kwargs):
        api_key = request.headers.get('X-API-Key') or request.args.get('api_key')
        
        if not api_key:
            return jsonify({'error': 'API key required', 'code': 'NO_API_KEY'}), 401
        
        db = get_db()
        cur = db.cursor()
        
        cur.execute("""
            SELECT * FROM api_keys 
            WHERE api_key = %s AND is_active = TRUE
        """, (api_key,))
        
        row = cur.fetchone()
        
        if not row:
            return jsonify({'error': 'Invalid API key', 'code': 'INVALID_KEY'}), 401
        
        key_data: dict = dict(row) if row else {}
        
        if key_data.get('expires_at') and key_data['expires_at'] < datetime.now():
            return jsonify({'error': 'API key expired', 'code': 'EXPIRED_KEY'}), 401
        
        today = datetime.now().date()
        if key_data.get('last_reset') and key_data['last_reset'] < today:
            cur.execute("""
                UPDATE api_keys SET daily_calls = 0, last_reset = %s
                WHERE id = %s
            """, (today, key_data['id']))
            db.commit()
            key_data['daily_calls'] = 0
        
        tier_limit = RATE_LIMITS.get(key_data.get('tier', 'basic'), 100)
        if key_data.get('daily_calls', 0) >= tier_limit:
            return jsonify({
                'error': 'Daily rate limit exceeded',
                'code': 'RATE_LIMITED',
                'limit': tier_limit,
                'resets_at': str(today + timedelta(days=1))
            }), 429
        
        cur.execute("""
            UPDATE api_keys SET daily_calls = daily_calls + 1
            WHERE id = %s
        """, (key_data['id'],))
        db.commit()
        
        g.api_key_data = key_data
        return f(*args, **kwargs)
    
    return decorated

@app.route('/api/v1/health', methods=['GET'])
def health_check():
    """Health check endpoint (no auth required)."""
    return jsonify({
        'status': 'healthy',
        'version': '1.0.0',
        'framework': 'TI Framework',
        'timestamp': datetime.now().isoformat()
    })

@app.route('/api/v1/register', methods=['POST'])
def register_api_key():
    """Register for a new API key."""
    data = request.json or {}
    email = data.get('email')
    tier = data.get('tier', 'basic')
    
    if not email:
        return jsonify({'error': 'Email required'}), 400
    
    if tier not in TIER_PRICES:
        return jsonify({'error': f'Invalid tier. Options: {list(TIER_PRICES.keys())}'}), 400
    
    api_key = generate_api_key()
    
    db = get_db()
    cur = db.cursor()
    
    cur.execute("""
        INSERT INTO api_keys (api_key, user_email, tier, expires_at)
        VALUES (%s, %s, %s, %s)
        RETURNING id, api_key, tier, created_at
    """, (api_key, email, tier, datetime.now() + timedelta(days=30)))
    
    row = cur.fetchone()
    db.commit()
    
    result: dict = dict(row) if row else {}
    
    return jsonify({
        'success': True,
        'api_key': result.get('api_key', api_key),
        'tier': result.get('tier', tier),
        'rate_limit': RATE_LIMITS[tier],
        'price_usd': TIER_PRICES[tier],
        'expires_at': str(datetime.now() + timedelta(days=30)),
        'documentation': '/api/v1/docs'
    })

@app.route('/api/v1/lcc/calculate', methods=['POST'])
@require_api_key
def calculate_lcc():
    """
    Calculate LCC (Love Consciousness Connection) proxy value.
    
    Input: Biometric data (HRV, EEG features, etc.)
    Output: LCC score (0.0 - 1.0) with component breakdown
    """
    data = request.json or {}
    
    hrv_coherence = data.get('hrv_coherence', 0.5)
    alpha_power = data.get('alpha_power', 0.5)
    theta_alpha_ratio = data.get('theta_alpha_ratio', 1.0)
    heart_rate_variability = data.get('hrv_rmssd', 50)
    
    hrv_component = min(1.0, hrv_coherence)
    eeg_component = min(1.0, alpha_power * (2.0 - min(2.0, theta_alpha_ratio)))
    stability_component = min(1.0, heart_rate_variability / 100)
    
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
    
    log_usage(g.api_key_data['id'], '/api/v1/lcc/calculate', True)
    
    return jsonify({
        'lcc_score': round(lcc_calibrated, 4),
        'components': {
            'hrv': round(hrv_component, 4),
            'eeg': round(eeg_component, 4),
            'stability': round(stability_component, 4)
        },
        'thresholds': {
            'noise_floor': noise_floor,
            'causation_threshold': causation_threshold
        },
        'signal_quality': signal_quality,
        'interpretation': get_lcc_interpretation(lcc_calibrated)
    })

@app.route('/api/v1/gsa/signal', methods=['POST'])
@require_api_key
def gsa_signal():
    """
    GSA (Grand Stock Algorithm) trading signal.
    
    Input: Market data (price, volume, regime indicators)
    Output: Trading signal with confidence
    
    NOTE: This is a simplified demo. Full algorithm is proprietary.
    """
    data = request.json or {}
    
    symbol = data.get('symbol', 'SPY')
    price = data.get('price')
    volume = data.get('volume')
    volatility = data.get('volatility', 0.2)
    
    if not price:
        return jsonify({'error': 'Price required'}), 400
    
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
    
    confidence = base_confidence * abs(signal_strength)
    
    log_usage(g.api_key_data['id'], '/api/v1/gsa/signal', True)
    
    return jsonify({
        'symbol': symbol,
        'signal': signal,
        'confidence': round(confidence, 4),
        'regime': regime,
        'timestamp': datetime.now().isoformat(),
        'disclaimer': 'This is not financial advice. Past performance does not guarantee future results.'
    })

@app.route('/api/v1/tralse/evaluate', methods=['POST'])
@require_api_key
def tralse_evaluate():
    """
    Evaluate a proposition using Tralse logic.
    
    Input: Proposition with evidence scores
    Output: Tralse value (0.0 - 1.0) with classification
    """
    data = request.json or {}
    
    evidence_for = data.get('evidence_for', 0.5)
    evidence_against = data.get('evidence_against', 0.5)
    prior = data.get('prior', 0.5)
    
    evidence_for = max(0, min(1, evidence_for))
    evidence_against = max(0, min(1, evidence_against))
    prior = max(0, min(1, prior))
    
    net_evidence = evidence_for - evidence_against
    posterior = prior + (1 - prior) * net_evidence if net_evidence > 0 else prior * (1 + net_evidence)
    tralse_value = max(0, min(1, posterior))
    
    if tralse_value == 0:
        category = 'FALSE'
    elif tralse_value < 0.5:
        category = 'TRALSE_FALSE'
    elif tralse_value < 1:
        category = 'TRALSE_TRUE'
    else:
        category = 'TRUE'
    
    log_usage(g.api_key_data['id'], '/api/v1/tralse/evaluate', True)
    
    return jsonify({
        'tralse_value': round(tralse_value, 4),
        'category': category,
        'inputs': {
            'evidence_for': evidence_for,
            'evidence_against': evidence_against,
            'prior': prior
        },
        'interpretation': get_tralse_interpretation(tralse_value, category)
    })

@app.route('/api/v1/mood/validate', methods=['POST'])
@require_api_key
def mood_validate():
    """
    Mood Amplifier safety validation.
    
    Input: Proposed mood intervention parameters
    Output: Safety assessment and recommendations
    """
    data = request.json or {}
    
    intervention_type = data.get('type', 'unknown')
    intensity = data.get('intensity', 0.5)
    duration_minutes = data.get('duration_minutes', 30)
    user_baseline = data.get('user_baseline', {})
    
    intensity = max(0, min(1, intensity))
    
    safety_score = 1.0
    warnings = []
    recommendations = []
    
    if intensity > 0.8:
        safety_score *= 0.7
        warnings.append('High intensity interventions require gradual buildup')
        recommendations.append('Start at 50% intensity and increase over 3 sessions')
    
    if duration_minutes > 60:
        safety_score *= 0.8
        warnings.append('Extended duration may cause fatigue')
        recommendations.append('Take 5-minute breaks every 30 minutes')
    
    baseline_stress = user_baseline.get('stress_level', 0.5)
    if baseline_stress > 0.7:
        safety_score *= 0.6
        warnings.append('User baseline stress is elevated')
        recommendations.append('Begin with relaxation protocol before intervention')
    
    if safety_score >= 0.8:
        status = 'APPROVED'
    elif safety_score >= 0.5:
        status = 'APPROVED_WITH_CAUTION'
    else:
        status = 'REQUIRES_MODIFICATION'
    
    log_usage(g.api_key_data['id'], '/api/v1/mood/validate', True)
    
    return jsonify({
        'status': status,
        'safety_score': round(safety_score, 4),
        'warnings': warnings,
        'recommendations': recommendations,
        'intervention': {
            'type': intervention_type,
            'intensity': intensity,
            'duration_minutes': duration_minutes
        }
    })

@app.route('/api/v1/usage', methods=['GET'])
@require_api_key
def get_usage():
    """Get API usage statistics for the current key."""
    key_data = g.api_key_data
    tier_limit = RATE_LIMITS.get(key_data['tier'], 100)
    
    return jsonify({
        'tier': key_data['tier'],
        'daily_calls_used': key_data['daily_calls'],
        'daily_limit': tier_limit,
        'remaining_calls': tier_limit - key_data['daily_calls'],
        'resets_at': str(datetime.now().date() + timedelta(days=1)),
        'expires_at': str(key_data['expires_at']) if key_data['expires_at'] else None
    })

@app.route('/api/v1/docs', methods=['GET'])
def api_docs():
    """API documentation."""
    return jsonify({
        'name': 'TI Framework API',
        'version': '1.0.0',
        'description': 'API access to TI Framework components',
        'base_url': '/api/v1',
        'authentication': {
            'type': 'API Key',
            'header': 'X-API-Key',
            'register': 'POST /api/v1/register'
        },
        'tiers': {
            'basic': {
                'price': '$99/month',
                'rate_limit': '100 calls/day',
                'features': ['LCC calculation', 'Tralse evaluation', 'Mood validation']
            },
            'pro': {
                'price': '$499/month',
                'rate_limit': '10,000 calls/day',
                'features': ['All basic features', 'GSA signals', 'Priority support']
            },
            'enterprise': {
                'price': 'Custom',
                'rate_limit': '100,000 calls/day',
                'features': ['All pro features', 'Custom integration', 'SLA guarantee']
            }
        },
        'endpoints': {
            '/api/v1/lcc/calculate': {
                'method': 'POST',
                'description': 'Calculate LCC proxy value from biometric data',
                'requires_auth': True
            },
            '/api/v1/gsa/signal': {
                'method': 'POST',
                'description': 'Get GSA trading signal',
                'requires_auth': True,
                'tier': 'pro+'
            },
            '/api/v1/tralse/evaluate': {
                'method': 'POST',
                'description': 'Evaluate proposition using Tralse logic',
                'requires_auth': True
            },
            '/api/v1/mood/validate': {
                'method': 'POST',
                'description': 'Validate mood amplifier intervention safety',
                'requires_auth': True
            },
            '/api/v1/usage': {
                'method': 'GET',
                'description': 'Get API usage statistics',
                'requires_auth': True
            }
        },
        'contact': 'brandon@tiframework.com'
    })

def get_lcc_interpretation(lcc_score):
    """Get human-readable interpretation of LCC score."""
    if lcc_score < 0.3:
        return "Low coherence state. Consider grounding practices."
    elif lcc_score < 0.5:
        return "Below average coherence. Room for optimization."
    elif lcc_score < 0.7:
        return "Moderate coherence. Good baseline state."
    elif lcc_score < 0.85:
        return "High coherence. Approaching causation threshold."
    else:
        return "Exceptional coherence. Causation threshold exceeded. Effects highly reliable."

def get_tralse_interpretation(value, category):
    """Get human-readable interpretation of Tralse evaluation."""
    interpretations = {
        'FALSE': "Proposition is definitively false based on evidence.",
        'TRALSE_FALSE': f"Proposition leans false ({value:.0%} confidence). Additional evidence needed.",
        'TRALSE_TRUE': f"Proposition leans true ({value:.0%} confidence). Additional evidence could strengthen.",
        'TRUE': "Proposition is definitively true based on evidence."
    }
    return interpretations.get(category, "Unable to interpret.")

def log_usage(api_key_id, endpoint, success):
    """Log API usage for analytics."""
    try:
        db = get_db()
        cur = db.cursor()
        cur.execute("""
            INSERT INTO api_usage (api_key_id, endpoint, success)
            VALUES (%s, %s, %s)
        """, (api_key_id, endpoint, success))
        db.commit()
    except Exception:
        pass

if __name__ == '__main__':
    init_api_tables()
    app.run(host='0.0.0.0', port=5001, debug=True)
