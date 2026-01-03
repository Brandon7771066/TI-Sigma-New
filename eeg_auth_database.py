"""
EEG Tralse Authentication Database Schema
==========================================

Production-ready database storage for EEG authentication system with:
- Bcrypt password hashing (salted)
- Fernet encryption at rest
- PostgreSQL storage

Author: Brandon Emerick
Date: November 21, 2025
"""

import psycopg2
from psycopg2.extras import RealDictCursor
import os
from typing import Dict, Any, Optional, List
from datetime import datetime
import json

class EEGAuthDatabase:
    """
    Database manager for EEG Tralse Authentication
    
    Tables:
    - eeg_enrollments: User enrollment data (encrypted biometric data)
    - eeg_auth_sessions: Active authentication sessions
    - eeg_intrusion_log: Failed authentication attempts for firewall
    """
    
    def __init__(self, database_url: Optional[str] = None):
        """Initialize database connection"""
        self.database_url = database_url or os.getenv('DATABASE_URL')
        if not self.database_url:
            raise ValueError("DATABASE_URL environment variable not set")
    
    def get_connection(self):
        """Get database connection"""
        return psycopg2.connect(self.database_url)
    
    def initialize_schema(self):
        """
        Create database tables for EEG authentication
        
        ✨ PRODUCTION-READY SCHEMA with security best practices
        """
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                # Table 1: EEG Enrollments (encrypted biometric data)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS eeg_enrollments (
                        id SERIAL PRIMARY KEY,
                        username VARCHAR(255) UNIQUE NOT NULL,
                        password_hash_bcrypt BYTEA NOT NULL,
                        encrypted_biometric_data TEXT NOT NULL,
                        encryption_key_id VARCHAR(255),
                        enrolled_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                        last_authenticated_at TIMESTAMP,
                        security_version VARCHAR(50) NOT NULL DEFAULT '2.0_bcrypt_fernet',
                        is_active BOOLEAN NOT NULL DEFAULT TRUE,
                        created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                        updated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP
                    );
                    
                    CREATE INDEX IF NOT EXISTS idx_eeg_enrollments_username 
                        ON eeg_enrollments(username);
                    CREATE INDEX IF NOT EXISTS idx_eeg_enrollments_active 
                        ON eeg_enrollments(is_active);
                """)
                
                # Table 2: Authentication Sessions (disappearing password windows)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS eeg_auth_sessions (
                        id SERIAL PRIMARY KEY,
                        username VARCHAR(255) NOT NULL,
                        session_token VARCHAR(255) UNIQUE NOT NULL,
                        window_created_at TIMESTAMP NOT NULL,
                        window_expires_at TIMESTAMP NOT NULL,
                        current_threshold FLOAT NOT NULL,
                        is_expired BOOLEAN NOT NULL DEFAULT FALSE,
                        authenticated_successfully BOOLEAN DEFAULT NULL,
                        confidence_score FLOAT,
                        created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP
                    );
                    
                    CREATE INDEX IF NOT EXISTS idx_eeg_sessions_username 
                        ON eeg_auth_sessions(username);
                    CREATE INDEX IF NOT EXISTS idx_eeg_sessions_token 
                        ON eeg_auth_sessions(session_token);
                    CREATE INDEX IF NOT EXISTS idx_eeg_sessions_expires 
                        ON eeg_auth_sessions(window_expires_at);
                """)
                
                # Table 3: Intrusion Log (firewall failed attempts)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS eeg_intrusion_log (
                        id SERIAL PRIMARY KEY,
                        username VARCHAR(255) NOT NULL,
                        attempt_time TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                        failure_reason VARCHAR(100) NOT NULL,
                        confidence_score FLOAT,
                        is_automated_attack BOOLEAN DEFAULT FALSE,
                        ip_address VARCHAR(45),
                        user_agent TEXT,
                        locked_until TIMESTAMP
                    );
                    
                    CREATE INDEX IF NOT EXISTS idx_eeg_intrusion_username 
                        ON eeg_intrusion_log(username);
                    CREATE INDEX IF NOT EXISTS idx_eeg_intrusion_time 
                        ON eeg_intrusion_log(attempt_time);
                """)
                
                # Table 4: Encryption Keys Management (for key rotation)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS eeg_encryption_keys (
                        id SERIAL PRIMARY KEY,
                        key_id VARCHAR(255) UNIQUE NOT NULL,
                        encrypted_master_key BYTEA NOT NULL,
                        created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                        is_active BOOLEAN NOT NULL DEFAULT TRUE,
                        rotated_at TIMESTAMP
                    );
                    
                    CREATE INDEX IF NOT EXISTS idx_eeg_keys_id 
                        ON eeg_encryption_keys(key_id);
                    CREATE INDEX IF NOT EXISTS idx_eeg_keys_active 
                        ON eeg_encryption_keys(is_active);
                """)
                
                conn.commit()
                print("✅ EEG authentication database schema initialized successfully!")
                
        except Exception as e:
            conn.rollback()
            print(f"❌ Failed to initialize schema: {e}")
            raise
        finally:
            conn.close()
    
    def store_enrollment(self, enrollment_data: Dict[str, Any]) -> int:
        """
        Store user enrollment data in database
        
        Args:
            enrollment_data: Dict from EEGTralseAuthenticator.enroll_user()
        
        Returns:
            Enrollment ID
        """
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("""
                    INSERT INTO eeg_enrollments 
                        (username, password_hash_bcrypt, encrypted_biometric_data, 
                         enrolled_at, security_version)
                    VALUES (%s, %s, %s, %s, %s)
                    RETURNING id
                """, (
                    enrollment_data['username'],
                    enrollment_data['password_hash_bcrypt'],
                    enrollment_data['encrypted_biometric_data'],
                    enrollment_data['enrolled_at'],
                    enrollment_data['security_version']
                ))
                
                enrollment_id = cur.fetchone()[0]
                conn.commit()
                return enrollment_id
                
        except Exception as e:
            conn.rollback()
            raise
        finally:
            conn.close()
    
    def get_enrollment(self, username: str) -> Optional[Dict[str, Any]]:
        """
        Retrieve user enrollment data for authentication
        
        Args:
            username: Username to retrieve
        
        Returns:
            Enrollment data dict or None if not found
        """
        conn = self.get_connection()
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT * FROM eeg_enrollments 
                    WHERE username = %s AND is_active = TRUE
                """, (username,))
                
                result = cur.fetchone()
                return dict(result) if result else None
                
        finally:
            conn.close()
    
    def update_last_authenticated(self, username: str):
        """Update last authenticated timestamp"""
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("""
                    UPDATE eeg_enrollments 
                    SET last_authenticated_at = CURRENT_TIMESTAMP,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE username = %s
                """, (username,))
                conn.commit()
        except Exception as e:
            conn.rollback()
            raise
        finally:
            conn.close()
    
    def log_intrusion_attempt(
        self, 
        username: str, 
        failure_reason: str, 
        confidence_score: Optional[float] = None,
        is_automated: bool = False
    ):
        """Log failed authentication attempt for firewall"""
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("""
                    INSERT INTO eeg_intrusion_log 
                        (username, failure_reason, confidence_score, is_automated_attack)
                    VALUES (%s, %s, %s, %s)
                """, (username, failure_reason, confidence_score, is_automated))
                conn.commit()
        except Exception as e:
            conn.rollback()
            raise
        finally:
            conn.close()
    
    def get_recent_failed_attempts(self, username: str, hours: int = 24) -> List[Dict[str, Any]]:
        """Get recent failed authentication attempts for a user"""
        conn = self.get_connection()
        try:
            with conn.cursor(cursor_factory=RealDictCursor) as cur:
                cur.execute("""
                    SELECT * FROM eeg_intrusion_log 
                    WHERE username = %s 
                        AND attempt_time > NOW() - INTERVAL '%s hours'
                    ORDER BY attempt_time DESC
                """, (username, hours))
                
                return [dict(row) for row in cur.fetchall()]
        finally:
            conn.close()
    
    def deactivate_enrollment(self, username: str):
        """Deactivate user enrollment (soft delete)"""
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("""
                    UPDATE eeg_enrollments 
                    SET is_active = FALSE,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE username = %s
                """, (username,))
                conn.commit()
        except Exception as e:
            conn.rollback()
            raise
        finally:
            conn.close()


# Initialize database on module import (for streamlit)
if __name__ == "__main__":
    print("🔒 Initializing EEG Authentication Database Schema...")
    db = EEGAuthDatabase()
    db.initialize_schema()
    print("✅ Database ready for production use!")
