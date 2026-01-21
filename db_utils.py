"""
Database Utilities for Cross-App Communication
Shared library for all specialist apps
"""

import os
import psycopg2
from psycopg2.extras import RealDictCursor
from datetime import datetime
import json

class DatabaseManager:
    """Shared database manager for multi-app ecosystem"""
    
    def __init__(self):
        self.conn_params = {
            'host': os.getenv('PGHOST'),
            'database': os.getenv('PGDATABASE'),
            'user': os.getenv('PGUSER'),
            'password': os.getenv('PGPASSWORD'),
            'port': os.getenv('PGPORT')
        }
        self._connection_available = None
    
    def _check_connection(self):
        """Check if database connection is available"""
        if self._connection_available is None:
            try:
                conn = psycopg2.connect(**self.conn_params)
                conn.close()
                self._connection_available = True
            except Exception:
                self._connection_available = False
        return self._connection_available
    
    def get_connection(self):
        """Get database connection with error handling"""
        if not self._check_connection():
            raise ConnectionError("Database connection not available")
        return psycopg2.connect(**self.conn_params)
    
    # ========================================================================
    # APPS MANAGEMENT
    # ========================================================================
    
    def register_app(self, app_name, url="", status="running"):
        """Register or update an app"""
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO apps (app_name, url, status, last_heartbeat)
                VALUES (%s, %s, %s, CURRENT_TIMESTAMP)
                ON CONFLICT (app_name) 
                DO UPDATE SET 
                    url = EXCLUDED.url,
                    status = EXCLUDED.status,
                    last_heartbeat = CURRENT_TIMESTAMP;
            """, (app_name, url, status))
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Warning: Could not register app {app_name}: {e}")
    
    def send_heartbeat(self, app_name):
        """Update app heartbeat"""
        try:
            conn = self.get_connection()
        except ConnectionError:
            return

        cur = conn.cursor()
        
        cur.execute("""
            UPDATE apps 
            SET last_heartbeat = CURRENT_TIMESTAMP
            WHERE app_name = %s;
        """, (app_name,))
        
        conn.commit()
        cur.close()
        conn.close()
    
    def get_all_apps(self):
        """Get status of all apps"""
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT app_name, url, status, last_heartbeat, created_at
                FROM apps
                ORDER BY created_at;
            """)
            
            apps = cur.fetchall()
            cur.close()
            conn.close()
            
            return apps
        except Exception as e:
            print(f"Warning: Could not fetch apps: {e}")
            return []
    
    # ========================================================================
    # EEG TRALSE AUTHENTICATION
    # ========================================================================
    
    def init_authentication_tables(self):
        """Initialize EEG Tralse authentication tables"""
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            # Authentication profiles table
            cur.execute("""
                CREATE TABLE IF NOT EXISTS eeg_auth_profiles (
                    username VARCHAR(255) PRIMARY KEY,
                    password_hash VARCHAR(64) NOT NULL,
                    signature JSONB NOT NULL,
                    tralse_key_values JSONB NOT NULL,
                    enrolled_at TIMESTAMP NOT NULL,
                    enrollment_quality VARCHAR(50),
                    last_auth_success TIMESTAMP,
                    last_auth_attempt TIMESTAMP,
                    total_auth_attempts INTEGER DEFAULT 0,
                    successful_auths INTEGER DEFAULT 0,
                    failed_auths INTEGER DEFAULT 0,
                    is_locked BOOLEAN DEFAULT FALSE,
                    locked_until TIMESTAMP,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
            """)
            
            # Authentication logs table
            cur.execute("""
                CREATE TABLE IF NOT EXISTS eeg_auth_logs (
                    log_id SERIAL PRIMARY KEY,
                    username VARCHAR(255) NOT NULL,
                    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    authenticated BOOLEAN NOT NULL,
                    confidence FLOAT,
                    status VARCHAR(100),
                    threshold_used FLOAT,
                    reason VARCHAR(255),
                    is_automated_attack BOOLEAN DEFAULT FALSE,
                    locked_out BOOLEAN DEFAULT FALSE,
                    unlock_time TIMESTAMP,
                    message TEXT
                );
            """)
            
            # Intrusion detection table
            cur.execute("""
                CREATE TABLE IF NOT EXISTS eeg_intrusion_attempts (
                    attempt_id SERIAL PRIMARY KEY,
                    username VARCHAR(255) NOT NULL,
                    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    confidence FLOAT,
                    is_automated BOOLEAN DEFAULT FALSE,
                    source_info JSONB
                );
            """)
            
            conn.commit()
            cur.close()
            conn.close()
            print("✅ EEG authentication tables initialized")
        except Exception as e:
            print(f"Warning: Could not initialize auth tables: {e}")
    
    def save_eeg_enrollment(self, enrollment_data):
        """Save EEG enrollment data"""
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO eeg_auth_profiles 
                (username, password_hash, signature, tralse_key_values, 
                 enrolled_at, enrollment_quality)
                VALUES (%s, %s, %s, %s, %s, %s)
                ON CONFLICT (username)
                DO UPDATE SET
                    password_hash = EXCLUDED.password_hash,
                    signature = EXCLUDED.signature,
                    tralse_key_values = EXCLUDED.tralse_key_values,
                    enrolled_at = EXCLUDED.enrolled_at,
                    enrollment_quality = EXCLUDED.enrollment_quality;
            """, (
                enrollment_data['username'],
                enrollment_data['password_hash'],
                json.dumps(enrollment_data['signature']),
                json.dumps(enrollment_data['tralse_key_values']),
                enrollment_data['enrolled_at'],
                enrollment_data['enrollment_quality']
            ))
            
            conn.commit()
            cur.close()
            conn.close()
            return True
        except Exception as e:
            print(f"Error saving enrollment: {e}")
            return False
    
    def get_eeg_enrollment(self, username):
        """Retrieve EEG enrollment for user"""
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT * FROM eeg_auth_profiles
                WHERE username = %s;
            """, (username,))
            
            profile = cur.fetchone()
            cur.close()
            conn.close()
            
            if profile:
                # Convert JSONB back to dicts
                profile = dict(profile)
                profile['signature'] = json.loads(profile['signature']) if isinstance(profile['signature'], str) else profile['signature']
                profile['tralse_key_values'] = json.loads(profile['tralse_key_values']) if isinstance(profile['tralse_key_values'], str) else profile['tralse_key_values']
            
            return profile
        except Exception as e:
            print(f"Error retrieving enrollment: {e}")
            return None
    
    def log_eeg_authentication(self, auth_result):
        """Log authentication attempt"""
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO eeg_auth_logs
                (username, authenticated, confidence, status, threshold_used,
                 reason, is_automated_attack, locked_out, unlock_time, message)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s);
            """, (
                auth_result.get('username'),
                auth_result.get('authenticated', False),
                auth_result.get('confidence'),
                auth_result.get('status'),
                auth_result.get('threshold_used'),
                auth_result.get('reason'),
                auth_result.get('automated_attack_detected', False),
                auth_result.get('locked_out', False),
                auth_result.get('unlock_time'),
                auth_result.get('message')
            ))
            
            # Update profile stats
            if auth_result.get('authenticated'):
                cur.execute("""
                    UPDATE eeg_auth_profiles
                    SET last_auth_success = CURRENT_TIMESTAMP,
                        last_auth_attempt = CURRENT_TIMESTAMP,
                        total_auth_attempts = total_auth_attempts + 1,
                        successful_auths = successful_auths + 1,
                        is_locked = FALSE,
                        locked_until = NULL
                    WHERE username = %s;
                """, (auth_result.get('username'),))
            else:
                cur.execute("""
                    UPDATE eeg_auth_profiles
                    SET last_auth_attempt = CURRENT_TIMESTAMP,
                        total_auth_attempts = total_auth_attempts + 1,
                        failed_auths = failed_auths + 1
                    WHERE username = %s;
                """, (auth_result.get('username'),))
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Error logging authentication: {e}")
    
    def check_eeg_lockout(self, username):
        """Check if user is locked out"""
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT is_locked, locked_until
                FROM eeg_auth_profiles
                WHERE username = %s;
            """, (username,))
            
            result = cur.fetchone()
            cur.close()
            conn.close()
            
            if result and result['is_locked']:
                if result['locked_until']:
                    from datetime import datetime
                    if datetime.now() < result['locked_until']:
                        return True, result['locked_until']
                    else:
                        # Lockout expired, clear it
                        self._clear_lockout(username)
                        return False, None
            
            return False, None
        except Exception as e:
            print(f"Error checking lockout: {e}")
            return False, None
    
    def _clear_lockout(self, username):
        """Clear lockout status"""
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                UPDATE eeg_auth_profiles
                SET is_locked = FALSE,
                    locked_until = NULL
                WHERE username = %s;
            """, (username,))
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Error clearing lockout: {e}")
    
    # ========================================================================
    # RESEARCH ASSETS
    # ========================================================================
    
    def add_asset(self, asset_type, source_app, title, content, tags=None):
        """Add research asset (equation, paper, protocol, insight)"""
        conn = self.get_connection()
        cur = conn.cursor()
        
        cur.execute("""
            INSERT INTO research_assets 
            (asset_type, source_app, title, content, tags)
            VALUES (%s, %s, %s, %s, %s)
            RETURNING asset_id;
        """, (asset_type, source_app, title, json.dumps(content), tags or []))
        
        asset_id = cur.fetchone()[0]
        
        conn.commit()
        cur.close()
        conn.close()
        
        return asset_id
    
    def add_god_machine_prediction(self, prediction_data):
        """
        Store God Machine stock prediction for tracking and validation
        
        Args:
            prediction_data: Dict with ticker, signal, GILE scores, rationale, etc.
        
        Returns:
            asset_id of stored prediction
        """
        return self.add_asset(
            asset_type="god_machine_stock_prediction",
            source_app="God Machine Stock Market",
            title=f"{prediction_data['ticker']} - {prediction_data['signal']} ({prediction_data['timestamp'][:10]})",
            content=prediction_data,
            tags=[
                "god_machine",
                "stock_prediction",
                prediction_data['ticker'],
                prediction_data['signal'],
                f"gile_{prediction_data['gile_score']:.2f}"
            ]
        )
    
    def save_stock_prediction(self, prediction_data):
        """
        Save stock prediction to dedicated stock_predictions table for accuracy tracking
        
        Args:
            prediction_data: Dict with ticker, signal, GILE scores, targets, etc.
        
        Returns:
            prediction_id of saved prediction
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO stock_predictions 
                (ticker, company_name, signal, direction, confidence_score, 
                 gile_score, sigma, above_threshold, uop_score, gtfe_score, lcc_score,
                 target_price, target_change_pct, current_price)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING prediction_id;
            """, (
                prediction_data.get('ticker'),
                prediction_data.get('name', prediction_data.get('company_name')),
                prediction_data.get('signal'),
                prediction_data.get('direction'),
                prediction_data.get('confidence'),
                prediction_data.get('gile_score'),
                prediction_data.get('sigma'),
                prediction_data.get('above_threshold'),
                prediction_data.get('uop_score'),
                prediction_data.get('gtfe_score'),
                prediction_data.get('lcc_score'),
                prediction_data.get('target_price'),
                prediction_data.get('target_change_pct'),
                prediction_data.get('current_price')
            ))
            
            prediction_id = cur.fetchone()[0]
            
            conn.commit()
            cur.close()
            conn.close()
            
            return prediction_id
        except Exception as e:
            print(f"Error saving stock prediction: {e}")
            raise
    
    def get_god_machine_predictions(self, limit=100):
        """
        Retrieve stored God Machine predictions for validation tracking
        
        Returns: List of predictions sorted by timestamp descending
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT asset_id, title, content, tags, created_at
                FROM research_assets
                WHERE asset_type = 'god_machine_stock_prediction'
                ORDER BY created_at DESC
                LIMIT %s;
            """, (limit,))
            
            predictions = cur.fetchall()
            cur.close()
            conn.close()
            
            # Parse JSON content
            for pred in predictions:
                pred['content'] = json.loads(pred['content']) if isinstance(pred['content'], str) else pred['content']
            
            return predictions
        except Exception as e:
            print(f"Warning: Could not fetch God Machine predictions: {e}")
            return []
    
    def get_stock_predictions(self, limit=100, ticker=None, pending_only=False):
        """
        Get stock predictions from dedicated table
        
        Args:
            limit: Max number to return
            ticker: Optional ticker filter
            pending_only: If True, only return predictions without actual outcomes
        
        Returns:
            List of predictions with all fields
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            base_query = "SELECT * FROM stock_predictions"
            conditions = []
            params = []
            
            if ticker:
                conditions.append("ticker = %s")
                params.append(ticker)
            
            if pending_only:
                conditions.append("actual_outcome IS NULL")
            
            if conditions:
                base_query += " WHERE " + " AND ".join(conditions)
            
            base_query += " ORDER BY prediction_date DESC LIMIT %s"
            params.append(limit)
            
            cur.execute(base_query, tuple(params))
            
            predictions = cur.fetchall()
            cur.close()
            conn.close()
            
            return predictions
        except Exception as e:
            print(f"Error fetching stock predictions: {e}")
            return []
    
    def update_stock_prediction_evaluation(self, prediction_id, actual_outcome, actual_price=None, is_correct=None):
        """
        Update stock prediction with actual market outcome for accuracy tracking
        
        Args:
            prediction_id: ID of prediction to update
            actual_outcome: 'win', 'loss', 'pending', or 'error'
            actual_price: Actual price at evaluation time
            is_correct: Boolean - was the prediction correct?
        
        Returns:
            True if successful, False otherwise
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                UPDATE stock_predictions
                SET actual_outcome = %s,
                    actual_price = %s,
                    is_correct = %s,
                    outcome_date = CURRENT_TIMESTAMP,
                    updated_at = CURRENT_TIMESTAMP
                WHERE prediction_id = %s;
            """, (actual_outcome, actual_price, is_correct, prediction_id))
            
            conn.commit()
            cur.close()
            conn.close()
            
            return True
        except Exception as e:
            print(f"Error updating prediction evaluation: {e}")
            return False
    
    def add_i_cell_company(self, ticker, company_name, sector, is_i_cell=True, 
                           coherence_score=None, leadership_stability_years=None,
                           has_realtime_kpis=False, kpi_sources=None):
        """
        Add i-cell company to tracking database
        
        Args:
            ticker: Stock ticker symbol
            company_name: Full company name
            sector: Industry sector
            is_i_cell: True if coherent i-cell, False if fragmented i-web
            coherence_score: 0-1 coherence rating
            leadership_stability_years: Years of stable leadership
            has_realtime_kpis: Whether real-time KPI data is available
            kpi_sources: JSON dict of KPI data sources
        
        Returns:
            company_id if successful, None otherwise
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO i_cell_companies 
                (ticker, company_name, sector, is_i_cell, coherence_score, 
                 leadership_stability_years, has_realtime_kpis, data_sources)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (ticker) DO UPDATE SET
                    company_name = EXCLUDED.company_name,
                    sector = EXCLUDED.sector,
                    updated_at = CURRENT_TIMESTAMP
                RETURNING company_id;
            """, (ticker, company_name, sector, is_i_cell, coherence_score,
                  leadership_stability_years, has_realtime_kpis, 
                  json.dumps(kpi_sources) if kpi_sources else None))
            
            result = cur.fetchone()
            company_id = result[0] if result else None
            
            conn.commit()
            cur.close()
            conn.close()
            
            return company_id
        except Exception as e:
            print(f"Error adding i-cell company: {e}")
            return None
    
    def get_i_cell_companies(self, i_cells_only=True, limit=100):
        """
        Get i-cell companies from database
        
        Args:
            i_cells_only: If True, only return coherent i-cells (not i-webs)
            limit: Max companies to return
        
        Returns:
            List of company records
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            if i_cells_only:
                cur.execute("""
                    SELECT * FROM i_cell_companies
                    WHERE is_i_cell = true
                    ORDER BY best_accuracy_pct DESC, coherence_score DESC
                    LIMIT %s;
                """, (limit,))
            else:
                cur.execute("""
                    SELECT * FROM i_cell_companies
                    ORDER BY best_accuracy_pct DESC, coherence_score DESC
                    LIMIT %s;
                """, (limit,))
            
            companies = cur.fetchall()
            cur.close()
            conn.close()
            
            return companies
        except Exception as e:
            print(f"Error fetching i-cell companies: {e}")
            return []
    
    def get_all_companies(self, limit=100):
        """
        Alias for get_i_cell_companies() - returns all i-cell companies
        Used by physics prediction engine
        
        Args:
            limit: Max companies to return
        
        Returns:
            List of company records with full KPIs
        """
        return self.get_i_cell_companies(i_cells_only=True, limit=limit)
    
    def update_company_baseline(self, ticker, gile_baseline_sigma=None, gile_baseline_shift=None,
                                pd_baselines=None, accuracy_pct=None):
        """
        Update company's contextual GILE baseline after iteration
        
        Args:
            ticker: Company ticker
            gile_baseline_sigma: New baseline sigma value
            gile_baseline_shift: Shift from standard distribution
            pd_baselines: Dict with g, i, l, e baseline values
            accuracy_pct: Accuracy percentage achieved with this baseline
        
        Returns:
            True if successful, False otherwise
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor()
            
            update_fields = []
            params = []
            
            if gile_baseline_sigma is not None:
                update_fields.append("gile_baseline_sigma = %s")
                params.append(gile_baseline_sigma)
            
            if gile_baseline_shift is not None:
                update_fields.append("gile_baseline_shift = %s")
                params.append(gile_baseline_shift)
            
            if pd_baselines:
                if 'g' in pd_baselines:
                    update_fields.append("pd_baseline_g = %s")
                    params.append(pd_baselines['g'])
                if 'i' in pd_baselines:
                    update_fields.append("pd_baseline_i = %s")
                    params.append(pd_baselines['i'])
                if 'l' in pd_baselines:
                    update_fields.append("pd_baseline_l = %s")
                    params.append(pd_baselines['l'])
                if 'e' in pd_baselines:
                    update_fields.append("pd_baseline_e = %s")
                    params.append(pd_baselines['e'])
            
            if accuracy_pct is not None:
                update_fields.append("best_accuracy_pct = %s")
                params.append(accuracy_pct)
            
            update_fields.append("baseline_iterations = baseline_iterations + 1")
            update_fields.append("last_baseline_update = CURRENT_TIMESTAMP")
            update_fields.append("updated_at = CURRENT_TIMESTAMP")
            
            params.append(ticker)
            
            query = f"""
                UPDATE i_cell_companies
                SET {', '.join(update_fields)}
                WHERE ticker = %s;
            """
            
            cur.execute(query, params)
            conn.commit()
            cur.close()
            conn.close()
            
            return True
        except Exception as e:
            print(f"Error updating company baseline: {e}")
            return False
    
    def get_assets_by_type(self, asset_type):
        """Get all assets of specific type"""
        conn = self.get_connection()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        
        cur.execute("""
            SELECT asset_id, source_app, title, content, tags, created_at
            FROM research_assets
            WHERE asset_type = %s
            ORDER BY created_at DESC;
        """, (asset_type,))
        
        assets = cur.fetchall()
        cur.close()
        conn.close()
        
        return assets
    
    def search_assets(self, query):
        """Search assets by keyword in title or tags"""
        conn = self.get_connection()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        
        cur.execute("""
            SELECT asset_id, asset_type, source_app, title, content, tags, created_at
            FROM research_assets
            WHERE 
                title ILIKE %s OR
                %s = ANY(tags)
            ORDER BY created_at DESC;
        """, (f'%{query}%', query))
        
        assets = cur.fetchall()
        cur.close()
        conn.close()
        
        return assets
    
    def get_asset_by_id(self, asset_id):
        """Get a single asset by ID"""
        conn = self.get_connection()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        
        cur.execute("""
            SELECT asset_id, asset_type, source_app, title, content, tags, created_at
            FROM research_assets
            WHERE asset_id = %s;
        """, (asset_id,))
        
        asset = cur.fetchone()
        cur.close()
        conn.close()
        
        return asset
    
    def update_asset(self, asset_id, content_updates):
        """
        Update an asset's content field
        
        Args:
            asset_id: ID of asset to update
            content_updates: Dictionary of fields to update in the content JSON
            
        Returns:
            True if successful, False otherwise
        """
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT content FROM research_assets WHERE asset_id = %s;
            """, (asset_id,))
            
            result = cur.fetchone()
            if not result:
                cur.close()
                conn.close()
                return False
            
            current_content = result['content']
            
            current_content.update(content_updates)
            
            cur.execute("""
                UPDATE research_assets
                SET content = %s
                WHERE asset_id = %s;
            """, (json.dumps(current_content), asset_id))
            
            conn.commit()
            cur.close()
            conn.close()
            
            return True
        except Exception as e:
            print(f"Error updating asset {asset_id}: {e}")
            return False
    
    # ========================================================================
    # EVENTS
    # ========================================================================
    
    def broadcast_event(self, source_app, event_type, payload):
        """Broadcast event to all apps"""
        conn = self.get_connection()
        cur = conn.cursor()
        
        cur.execute("""
            INSERT INTO events (source_app, event_type, payload)
            VALUES (%s, %s, %s)
            RETURNING event_id;
        """, (source_app, event_type, json.dumps(payload)))
        
        event_id = cur.fetchone()[0]
        
        conn.commit()
        cur.close()
        conn.close()
        
        return event_id
    
    def get_recent_events(self, limit=50):
        """Get recent events across all apps"""
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT event_id, source_app, event_type, payload, timestamp
                FROM events
                ORDER BY timestamp DESC
                LIMIT %s;
            """, (limit,))
            
            events = cur.fetchall()
            cur.close()
            conn.close()
            
            return events
        except Exception as e:
            print(f"Warning: Could not fetch events: {e}")
            return []
    
    # ========================================================================
    # MASTER INDEX
    # ========================================================================
    
    def get_concept_index(self, concept):
        """Get all resources related to concept"""
        conn = self.get_connection()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        
        cur.execute("""
            SELECT concept, related_apps, equations, papers, protocols, last_updated
            FROM master_index
            WHERE concept = %s;
        """, (concept,))
        
        result = cur.fetchone()
        cur.close()
        conn.close()
        
        return result
    
    def update_concept_index(self, concept, related_apps=None, equations=None, papers=None, protocols=None):
        """Update master index for concept"""
        conn = self.get_connection()
        cur = conn.cursor()
        
        updates = []
        params = []
        
        if related_apps is not None:
            updates.append("related_apps = %s")
            params.append(related_apps)
        if equations is not None:
            updates.append("equations = %s")
            params.append(equations)
        if papers is not None:
            updates.append("papers = %s")
            params.append(papers)
        if protocols is not None:
            updates.append("protocols = %s")
            params.append(protocols)
        
        if updates:
            updates.append("last_updated = CURRENT_TIMESTAMP")
            params.append(concept)
            
            query = f"""
                UPDATE master_index
                SET {', '.join(updates)}
                WHERE concept = %s;
            """
            
            cur.execute(query, params)
            conn.commit()
        
        cur.close()
        conn.close()
    
    def get_all_concepts(self):
        """Get all concepts in master index"""
        try:
            conn = self.get_connection()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            cur.execute("""
                SELECT concept, related_apps, equations, papers, protocols, last_updated
                FROM master_index
                ORDER BY concept;
            """)
            
            concepts = cur.fetchall()
            cur.close()
            conn.close()
            
            return concepts
        except Exception as e:
            print(f"Warning: Could not fetch concepts: {e}")
            return []

# Global instance for easy import
db = DatabaseManager()
