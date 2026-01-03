"""
🌉 Biometric Data Bridge API - HTTP Endpoint for Real-Time Device Data
======================================================================

Receives real-time biometric data from:
- Mendi fNIRS (via export/forward or companion scripts)
- Muse EEG (via Mind Monitor OSC or MuseLSL forwarding)
- Polar H10 HRV (via companion scripts)
- ESP32 BLE Bridge (unified device streaming)

Data flows: Device → Phone/Laptop → HTTP POST → This API → PostgreSQL → Streamlit Dashboard

Author: Brandon Emerick
Date: November 28, 2025
Framework: Transcendent Intelligence (TI)
"""

from flask import Flask, request, jsonify
from flask_cors import CORS
import os
import psycopg2
from datetime import datetime
import json

app = Flask(__name__)
CORS(app)

# Database connection
def get_db_connection():
    """Connect to PostgreSQL database"""
    return psycopg2.connect(os.environ.get('DATABASE_URL'))

# Initialize database table for Mendi data
def init_database():
    """Create tables for all biometric data"""
    conn = get_db_connection()
    cur = conn.cursor()
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS mendi_realtime_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            hbo2 FLOAT NOT NULL,
            hbr FLOAT NOT NULL,
            total_hb FLOAT,
            oxygenation_percent FLOAT,
            signal_quality FLOAT,
            device_id TEXT,
            session_id TEXT,
            metadata JSONB,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE TABLE IF NOT EXISTS esp32_biometric_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            device_timestamp BIGINT,
            
            eeg_tp9 FLOAT,
            eeg_af7 FLOAT,
            eeg_af8 FLOAT,
            eeg_tp10 FLOAT,
            
            fnirs_hbo2 FLOAT,
            fnirs_hbr FLOAT,
            fnirs_oxygenation_pct FLOAT,
            
            heart_rate INTEGER,
            rr_interval INTEGER,
            
            muse_connected BOOLEAN,
            mendi_connected BOOLEAN,
            polar_connected BOOLEAN,
            
            device_id TEXT DEFAULT 'ESP32_Bridge',
            session_id TEXT,
            metadata JSONB,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_esp32_timestamp 
        ON esp32_biometric_data(timestamp DESC)
    """)
    
    cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_esp32_session 
        ON esp32_biometric_data(session_id)
    """)
    
    # Muse EEG raw data table
    cur.execute("""
        CREATE TABLE IF NOT EXISTS muse_eeg_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            
            -- Raw channel values (microvolts)
            tp9 FLOAT,
            af7 FLOAT,
            af8 FLOAT,
            tp10 FLOAT,
            
            -- FFT band powers (calculated client-side or here)
            alpha_power FLOAT,
            beta_power FLOAT,
            theta_power FLOAT,
            gamma_power FLOAT,
            delta_power FLOAT,
            
            -- Derived metrics
            attention FLOAT,
            meditation FLOAT,
            mellow FLOAT,
            concentration FLOAT,
            
            -- Connection info
            signal_quality FLOAT,
            battery_level INTEGER,
            device_id TEXT,
            session_id TEXT,
            source TEXT DEFAULT 'unknown',  -- 'mind_monitor', 'muselsl', 'direct_ble'
            
            metadata JSONB,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_muse_timestamp 
        ON muse_eeg_data(timestamp DESC)
    """)
    
    cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_muse_session 
        ON muse_eeg_data(session_id)
    """)
    
    # Polar H10 HRV data table
    cur.execute("""
        CREATE TABLE IF NOT EXISTS polar_hrv_data (
            id SERIAL PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            
            -- Core metrics
            heart_rate INTEGER,
            rr_interval INTEGER,
            rr_intervals FLOAT[],
            
            -- Calculated HRV metrics
            rmssd FLOAT,
            sdnn FLOAT,
            lf_power FLOAT,
            hf_power FLOAT,
            lf_hf_ratio FLOAT,
            
            -- Coherence
            coherence FLOAT,
            
            -- Device info
            device_id TEXT,
            session_id TEXT,
            source TEXT DEFAULT 'unknown',  -- 'polar_sensor_logger', 'ble_direct'
            
            metadata JSONB,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)
    
    cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_polar_timestamp 
        ON polar_hrv_data(timestamp DESC)
    """)
    
    conn.commit()
    cur.close()
    conn.close()
    print("✅ Database initialized (Mendi + Muse + Polar + ESP32 tables)")

@app.route('/health', methods=['GET'])
def health_check():
    """Health check endpoint"""
    return jsonify({
        'status': 'healthy',
        'service': 'Mendi Data Bridge API',
        'timestamp': datetime.now().isoformat()
    })

@app.route('/api/mendi/upload', methods=['POST'])
def upload_mendi_data():
    """
    Upload Mendi fNIRS data
    
    Expected JSON format:
    {
        "timestamp": "2025-11-23T08:30:00",
        "hbo2": 65.3,
        "hbr": 45.2,
        "total_hb": 110.5,
        "oxygenation_percent": 59.1,
        "signal_quality": 0.87,
        "device_id": "mendi-abc123",
        "session_id": "session-2025-11-23",
        "metadata": {}
    }
    
    Or batch upload:
    {
        "samples": [
            {"timestamp": "...", "hbo2": ..., "hbr": ...},
            {"timestamp": "...", "hbo2": ..., "hbr": ...}
        ]
    }
    """
    try:
        data = request.get_json()
        
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        # Handle batch upload
        if 'samples' in data:
            samples = data['samples']
            inserted = 0
            
            for sample in samples:
                cur.execute("""
                    INSERT INTO mendi_realtime_data 
                    (timestamp, hbo2, hbr, total_hb, oxygenation_percent, 
                     signal_quality, device_id, session_id, metadata)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                """, (
                    sample.get('timestamp', datetime.now()),
                    sample['hbo2'],
                    sample['hbr'],
                    sample.get('total_hb'),
                    sample.get('oxygenation_percent'),
                    sample.get('signal_quality', 1.0),
                    sample.get('device_id', 'unknown'),
                    sample.get('session_id'),
                    json.dumps(sample.get('metadata', {}))
                ))
                inserted += 1
            
            conn.commit()
            cur.close()
            conn.close()
            
            return jsonify({
                'status': 'success',
                'message': f'Uploaded {inserted} samples',
                'count': inserted
            }), 201
        
        # Handle single sample upload
        else:
            cur.execute("""
                INSERT INTO mendi_realtime_data 
                (timestamp, hbo2, hbr, total_hb, oxygenation_percent, 
                 signal_quality, device_id, session_id, metadata)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING id
            """, (
                data.get('timestamp', datetime.now()),
                data['hbo2'],
                data['hbr'],
                data.get('total_hb'),
                data.get('oxygenation_percent'),
                data.get('signal_quality', 1.0),
                data.get('device_id', 'unknown'),
                data.get('session_id'),
                json.dumps(data.get('metadata', {}))
            ))
            
            result = cur.fetchone()
            inserted_id = result[0] if result else None
            conn.commit()
            cur.close()
            conn.close()
            
            return jsonify({
                'status': 'success',
                'message': 'Data uploaded successfully',
                'id': inserted_id
            }), 201
    
    except KeyError as e:
        return jsonify({'error': f'Missing required field: {e}'}), 400
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/mendi/latest', methods=['GET'])
def get_latest_data():
    """Get latest Mendi data points"""
    try:
        limit = request.args.get('limit', 100, type=int)
        session_id = request.args.get('session_id')
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        if session_id:
            cur.execute("""
                SELECT timestamp, hbo2, hbr, total_hb, oxygenation_percent,
                       signal_quality, device_id, session_id
                FROM mendi_realtime_data
                WHERE session_id = %s
                ORDER BY timestamp DESC
                LIMIT %s
            """, (session_id, limit))
        else:
            cur.execute("""
                SELECT timestamp, hbo2, hbr, total_hb, oxygenation_percent,
                       signal_quality, device_id, session_id
                FROM mendi_realtime_data
                ORDER BY timestamp DESC
                LIMIT %s
            """, (limit,))
        
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        samples = []
        for row in rows:
            samples.append({
                'timestamp': row[0].isoformat(),
                'hbo2': row[1],
                'hbr': row[2],
                'total_hb': row[3],
                'oxygenation_percent': row[4],
                'signal_quality': row[5],
                'device_id': row[6],
                'session_id': row[7]
            })
        
        return jsonify({
            'status': 'success',
            'count': len(samples),
            'samples': samples
        })
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/mendi/sessions', methods=['GET'])
def get_sessions():
    """Get list of all sessions"""
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        
        cur.execute("""
            SELECT DISTINCT session_id, 
                   MIN(timestamp) as start_time,
                   MAX(timestamp) as end_time,
                   COUNT(*) as sample_count
            FROM mendi_realtime_data
            WHERE session_id IS NOT NULL
            GROUP BY session_id
            ORDER BY MIN(timestamp) DESC
        """)
        
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        sessions = []
        for row in rows:
            sessions.append({
                'session_id': row[0],
                'start_time': row[1].isoformat(),
                'end_time': row[2].isoformat(),
                'sample_count': row[3]
            })
        
        return jsonify({
            'status': 'success',
            'count': len(sessions),
            'sessions': sessions
        })
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/muse/upload', methods=['POST'])
def upload_muse_data():
    """
    Upload Muse EEG data from local collector
    
    Expected JSON format (from Mind Monitor or MuseLSL forwarder):
    {
        "timestamp": "2025-11-28T08:30:00",
        "raw": {
            "tp9": 850.2,
            "af7": 823.1,
            "af8": 812.4,
            "tp10": 845.7
        },
        "bands": {
            "alpha": 0.65,
            "beta": 0.42,
            "theta": 0.38,
            "gamma": 0.22,
            "delta": 0.15
        },
        "metrics": {
            "attention": 0.72,
            "meditation": 0.58,
            "mellow": 0.45,
            "concentration": 0.68
        },
        "signal_quality": 0.95,
        "battery": 85,
        "device_id": "Muse-XXXX",
        "session_id": "session-2025-11-28",
        "source": "mind_monitor"
    }
    
    Or batch upload:
    {
        "samples": [...]
    }
    """
    try:
        data = request.get_json()
        
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        def insert_sample(sample):
            raw = sample.get('raw', {})
            bands = sample.get('bands', {})
            metrics = sample.get('metrics', {})
            
            cur.execute("""
                INSERT INTO muse_eeg_data 
                (timestamp, tp9, af7, af8, tp10,
                 alpha_power, beta_power, theta_power, gamma_power, delta_power,
                 attention, meditation, mellow, concentration,
                 signal_quality, battery_level, device_id, session_id, source, metadata)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING id
            """, (
                sample.get('timestamp', datetime.now()),
                raw.get('tp9'), raw.get('af7'), raw.get('af8'), raw.get('tp10'),
                bands.get('alpha'), bands.get('beta'), bands.get('theta'), 
                bands.get('gamma'), bands.get('delta'),
                metrics.get('attention'), metrics.get('meditation'),
                metrics.get('mellow'), metrics.get('concentration'),
                sample.get('signal_quality', 1.0),
                sample.get('battery'),
                sample.get('device_id', 'Muse'),
                sample.get('session_id'),
                sample.get('source', 'unknown'),
                json.dumps(sample.get('metadata', {}))
            ))
            return cur.fetchone()[0]
        
        # Handle batch upload
        if 'samples' in data:
            samples = data['samples']
            inserted = 0
            for sample in samples:
                insert_sample(sample)
                inserted += 1
            
            conn.commit()
            cur.close()
            conn.close()
            
            return jsonify({
                'status': 'success',
                'message': f'Uploaded {inserted} Muse samples',
                'count': inserted
            }), 201
        
        # Handle single sample upload
        else:
            inserted_id = insert_sample(data)
            conn.commit()
            cur.close()
            conn.close()
            
            return jsonify({
                'status': 'success',
                'message': 'Muse EEG data uploaded successfully',
                'id': inserted_id
            }), 201
    
    except KeyError as e:
        return jsonify({'error': f'Missing required field: {e}'}), 400
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/muse/latest', methods=['GET'])
def get_latest_muse_data():
    """Get latest Muse EEG data points"""
    try:
        limit = request.args.get('limit', 100, type=int)
        session_id = request.args.get('session_id')
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        if session_id:
            cur.execute("""
                SELECT timestamp, tp9, af7, af8, tp10,
                       alpha_power, beta_power, theta_power, gamma_power,
                       attention, meditation, signal_quality, device_id, session_id
                FROM muse_eeg_data
                WHERE session_id = %s
                ORDER BY timestamp DESC
                LIMIT %s
            """, (session_id, limit))
        else:
            cur.execute("""
                SELECT timestamp, tp9, af7, af8, tp10,
                       alpha_power, beta_power, theta_power, gamma_power,
                       attention, meditation, signal_quality, device_id, session_id
                FROM muse_eeg_data
                ORDER BY timestamp DESC
                LIMIT %s
            """, (limit,))
        
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        samples = []
        for row in rows:
            samples.append({
                'timestamp': row[0].isoformat(),
                'raw': {
                    'tp9': row[1], 'af7': row[2], 'af8': row[3], 'tp10': row[4]
                },
                'bands': {
                    'alpha': row[5], 'beta': row[6], 'theta': row[7], 'gamma': row[8]
                },
                'attention': row[9],
                'meditation': row[10],
                'signal_quality': row[11],
                'device_id': row[12],
                'session_id': row[13]
            })
        
        return jsonify({
            'status': 'success',
            'count': len(samples),
            'samples': samples
        })
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/polar/upload', methods=['POST'])
def upload_polar_data():
    """
    Upload Polar H10 HRV data from local collector
    
    Expected JSON format:
    {
        "timestamp": "2025-11-28T08:30:00",
        "heart_rate": 72,
        "rr_interval": 833,
        "rr_intervals": [833, 845, 821, 850],
        "hrv": {
            "rmssd": 45.2,
            "sdnn": 52.1,
            "lf_power": 1250,
            "hf_power": 980,
            "lf_hf_ratio": 1.28
        },
        "coherence": 0.72,
        "device_id": "Polar H10 XXXXX",
        "session_id": "session-2025-11-28",
        "source": "polar_sensor_logger"
    }
    """
    try:
        data = request.get_json()
        
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        hrv = data.get('hrv', {})
        rr_intervals = data.get('rr_intervals', [])
        
        cur.execute("""
            INSERT INTO polar_hrv_data 
            (timestamp, heart_rate, rr_interval, rr_intervals,
             rmssd, sdnn, lf_power, hf_power, lf_hf_ratio, coherence,
             device_id, session_id, source, metadata)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            data.get('timestamp', datetime.now()),
            data.get('heart_rate'),
            data.get('rr_interval'),
            rr_intervals if rr_intervals else None,
            hrv.get('rmssd'),
            hrv.get('sdnn'),
            hrv.get('lf_power'),
            hrv.get('hf_power'),
            hrv.get('lf_hf_ratio'),
            data.get('coherence'),
            data.get('device_id', 'Polar H10'),
            data.get('session_id'),
            data.get('source', 'unknown'),
            json.dumps(data.get('metadata', {}))
        ))
        
        result = cur.fetchone()
        inserted_id = result[0] if result else None
        conn.commit()
        cur.close()
        conn.close()
        
        return jsonify({
            'status': 'success',
            'message': 'Polar HRV data uploaded successfully',
            'id': inserted_id
        }), 201
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/polar/latest', methods=['GET'])
def get_latest_polar_data():
    """Get latest Polar H10 HRV data"""
    try:
        limit = request.args.get('limit', 100, type=int)
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        cur.execute("""
            SELECT timestamp, heart_rate, rr_interval, rmssd, sdnn, 
                   lf_hf_ratio, coherence, device_id, session_id
            FROM polar_hrv_data
            ORDER BY timestamp DESC
            LIMIT %s
        """, (limit,))
        
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        samples = []
        for row in rows:
            samples.append({
                'timestamp': row[0].isoformat(),
                'heart_rate': row[1],
                'rr_interval': row[2],
                'rmssd': row[3],
                'sdnn': row[4],
                'lf_hf_ratio': row[5],
                'coherence': row[6],
                'device_id': row[7],
                'session_id': row[8]
            })
        
        return jsonify({
            'status': 'success',
            'count': len(samples),
            'samples': samples
        })
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/biometric/upload', methods=['POST'])
def upload_esp32_biometric_data():
    """
    Upload unified biometric data from ESP32 BLE Bridge
    
    Expected JSON format (from ESP32):
    {
        "timestamp": 12345678,  // millis() from ESP32
        "device": "ESP32_BLE_Bridge",
        "eeg": {
            "tp9": 0.45,
            "af7": 0.52,
            "af8": 0.48,
            "tp10": 0.51
        },
        "fnirs": {
            "hbo2": 65.3,
            "hbr": 45.0,
            "oxygenation_pct": 59.1
        },
        "heart": {
            "hr": 72,
            "rr_interval": 850
        },
        "connection_status": {
            "muse": true,
            "mendi": true,
            "polar": true
        }
    }
    """
    try:
        data = request.get_json()
        
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        eeg = data.get('eeg', {})
        fnirs = data.get('fnirs', {})
        heart = data.get('heart', {})
        status = data.get('connection_status', {})
        
        cur.execute("""
            INSERT INTO esp32_biometric_data 
            (timestamp, device_timestamp, 
             eeg_tp9, eeg_af7, eeg_af8, eeg_tp10,
             fnirs_hbo2, fnirs_hbr, fnirs_oxygenation_pct,
             heart_rate, rr_interval,
             muse_connected, mendi_connected, polar_connected,
             device_id, session_id, metadata)
            VALUES (NOW(), %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            data.get('timestamp'),
            eeg.get('tp9'),
            eeg.get('af7'),
            eeg.get('af8'),
            eeg.get('tp10'),
            fnirs.get('hbo2'),
            fnirs.get('hbr'),
            fnirs.get('oxygenation_pct'),
            heart.get('hr'),
            heart.get('rr_interval'),
            status.get('muse', False),
            status.get('mendi', False),
            status.get('polar', False),
            data.get('device', 'ESP32_Bridge'),
            data.get('session_id'),
            json.dumps(data.get('metadata', {}))
        ))
        
        result = cur.fetchone()
        inserted_id = result[0] if result else None
        conn.commit()
        cur.close()
        conn.close()
        
        return jsonify({
            'status': 'success',
            'message': 'Biometric data uploaded successfully',
            'id': inserted_id,
            'devices_connected': {
                'muse': status.get('muse', False),
                'mendi': status.get('mendi', False),
                'polar': status.get('polar', False)
            }
        }), 201
    
    except Exception as e:
        return jsonify({
            'status': 'error',
            'error': str(e)
        }), 500

@app.route('/api/biometric-data', methods=['POST'])
def upload_simple_biometric_data():
    """
    Simple endpoint for ESP32 Arduino sketch
    Matches the format from ESP32_MoodAmplifier.ino
    """
    try:
        data = request.get_json()
        
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        # Parse the simple format from Arduino
        eeg_channels = data.get('eeg_channels', [0, 0, 0, 0])
        rr_intervals = data.get('rr_intervals', [])
        
        cur.execute("""
            INSERT INTO esp32_biometric_data 
            (timestamp, device_timestamp, 
             eeg_tp9, eeg_af7, eeg_af8, eeg_tp10,
             fnirs_hbo2, fnirs_hbr, fnirs_oxygenation_pct,
             heart_rate, rr_interval,
             muse_connected, mendi_connected, polar_connected,
             device_id, metadata)
            VALUES (NOW(), %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            data.get('timestamp'),
            eeg_channels[0] if len(eeg_channels) > 0 else None,
            eeg_channels[1] if len(eeg_channels) > 1 else None,
            eeg_channels[2] if len(eeg_channels) > 2 else None,
            eeg_channels[3] if len(eeg_channels) > 3 else None,
            None,  # hbo2 not sent directly
            data.get('hemoglobin'),
            data.get('oxygenation'),
            data.get('heart_rate'),
            rr_intervals[0] if len(rr_intervals) > 0 else None,
            data.get('muse_connected', False),
            data.get('mendi_connected', False),
            data.get('polar_connected', False),
            'ESP32_MoodAmplifier',
            json.dumps({'rr_intervals': rr_intervals, 'attention': data.get('attention'), 'meditation': data.get('meditation')})
        ))
        
        result = cur.fetchone()
        inserted_id = result[0] if result else None
        conn.commit()
        cur.close()
        conn.close()
        
        return jsonify({
            'status': 'ok',
            'id': inserted_id,
            'hr': data.get('heart_rate', 0)
        }), 201
    
    except Exception as e:
        return jsonify({'status': 'error', 'error': str(e)}), 500

@app.route('/api/biometric/latest', methods=['GET'])
def get_latest_esp32_data():
    """Get latest biometric readings from ESP32"""
    try:
        limit = int(request.args.get('limit', 100))
        
        conn = get_db_connection()
        cur = conn.cursor()
        
        cur.execute("""
            SELECT timestamp, eeg_tp9, eeg_af7, eeg_af8, eeg_tp10,
                   fnirs_hbo2, fnirs_hbr, fnirs_oxygenation_pct,
                   heart_rate, rr_interval,
                   muse_connected, mendi_connected, polar_connected,
                   device_id, session_id
            FROM esp32_biometric_data
            ORDER BY timestamp DESC
            LIMIT %s
        """, (limit,))
        
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        samples = []
        for row in rows:
            samples.append({
                'timestamp': row[0].isoformat(),
                'eeg': {
                    'tp9': row[1],
                    'af7': row[2],
                    'af8': row[3],
                    'tp10': row[4]
                },
                'fnirs': {
                    'hbo2': row[5],
                    'hbr': row[6],
                    'oxygenation_pct': row[7]
                },
                'heart': {
                    'rate': row[8],
                    'rr_interval': row[9]
                },
                'connected': {
                    'muse': row[10],
                    'mendi': row[11],
                    'polar': row[12]
                },
                'device_id': row[13],
                'session_id': row[14]
            })
        
        return jsonify({
            'status': 'success',
            'count': len(samples),
            'samples': samples
        })
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500

if __name__ == '__main__':
    print("🌉 Starting Biometric Data Bridge API...")
    print("🌟 Mood Amplifier - Real-time biometric streaming!", flush=True)
    init_database()
    
    port = int(os.environ.get('PORT', 8000))
    print(f"\n✅ API listening on port {port}")
    print(f"\n📡 Upload Endpoints:")
    print(f"   - Muse EEG:    POST http://0.0.0.0:{port}/api/muse/upload")
    print(f"   - Polar HRV:   POST http://0.0.0.0:{port}/api/polar/upload")
    print(f"   - Mendi fNIRS: POST http://0.0.0.0:{port}/api/mendi/upload")
    print(f"   - ESP32 All:   POST http://0.0.0.0:{port}/api/biometric/upload")
    print(f"\n📊 Read Endpoints:")
    print(f"   - Muse Latest:   GET http://0.0.0.0:{port}/api/muse/latest")
    print(f"   - Polar Latest:  GET http://0.0.0.0:{port}/api/polar/latest")
    print(f"   - Mendi Latest:  GET http://0.0.0.0:{port}/api/mendi/latest")
    print(f"   - Health Check:  GET http://0.0.0.0:{port}/health")
    print(f"\n🔗 Run local_biometric_collector.py on your laptop to stream data!", flush=True)
    
    app.run(host='0.0.0.0', port=port, debug=False, threaded=True, use_reloader=False)
