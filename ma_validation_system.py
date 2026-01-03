"""
Mood Amplifier Autonomous Validation System
============================================

Comprehensive validation for the Mood Amplifier including:
1. Real-time EEG/Polar H10 data flow validation
2. Animal-to-human parameter transfer with LCC Virus correlation
3. ChatGPT error-prevention safeguards
4. Emotional response validation tests
5. TI Framework Tralseness integration

Author: Brandon Emerick
Date: December 18, 2025
Framework: TI Framework + GILE + LCC Virus
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any, Callable
from datetime import datetime, timedelta
from enum import Enum
import json
import os

try:
    import psycopg2
    HAS_DB = True
except ImportError:
    HAS_DB = False


# ============================================================================
# VALIDATION STATUS & THRESHOLDS
# ============================================================================

class ValidationStatus(Enum):
    """Validation result status"""
    PASSED = "passed"
    WARNING = "warning"
    FAILED = "failed"
    SKIPPED = "skipped"
    PENDING = "pending"


class TralsenessThreshold(Enum):
    """TI Framework Tralseness thresholds"""
    COHERENT_CAUSATION = 0.85  # Major truth threshold (0.92² ≈ 0.85)
    SUSTAINABLE_COHERENCE = 0.92  # Sustainable True-Tralseness
    LOW_RESONANCE = 0.42  # Below this = GILE < 0.42
    MEDIUM_RESONANCE = 0.65  # GILE 0.42-0.7
    HIGH_RESONANCE = 0.91  # GILE > 0.91 = CCC threshold


@dataclass
class ValidationResult:
    """Single validation test result"""
    test_name: str
    status: ValidationStatus
    message: str
    details: Dict[str, Any] = field(default_factory=dict)
    tralseness_score: float = 0.5
    timestamp: datetime = field(default_factory=datetime.now)
    
    @property
    def passed(self) -> bool:
        return self.status == ValidationStatus.PASSED
    
    def to_dict(self) -> Dict:
        return {
            'test_name': self.test_name,
            'status': self.status.value,
            'message': self.message,
            'details': self.details,
            'tralseness_score': self.tralseness_score,
            'timestamp': self.timestamp.isoformat()
        }


@dataclass
class ValidationReport:
    """Complete validation report"""
    report_id: str
    created_at: datetime
    results: List[ValidationResult]
    overall_tralseness: float = 0.0
    gile_scores: Dict[str, float] = field(default_factory=dict)
    
    @property
    def passed_count(self) -> int:
        return sum(1 for r in self.results if r.passed)
    
    @property
    def failed_count(self) -> int:
        return sum(1 for r in self.results if r.status == ValidationStatus.FAILED)
    
    @property
    def warning_count(self) -> int:
        return sum(1 for r in self.results if r.status == ValidationStatus.WARNING)
    
    @property
    def overall_status(self) -> ValidationStatus:
        if self.failed_count > 0:
            return ValidationStatus.FAILED
        if self.warning_count > 0:
            return ValidationStatus.WARNING
        return ValidationStatus.PASSED
    
    def to_dict(self) -> Dict:
        return {
            'report_id': self.report_id,
            'created_at': self.created_at.isoformat(),
            'results': [r.to_dict() for r in self.results],
            'summary': {
                'passed': self.passed_count,
                'failed': self.failed_count,
                'warnings': self.warning_count,
                'total': len(self.results),
                'overall_status': self.overall_status.value,
                'overall_tralseness': self.overall_tralseness
            },
            'gile_scores': self.gile_scores
        }


# ============================================================================
# 1. BIOMETRIC DATA FLOW VALIDATION
# ============================================================================

class BiometricDataFlowValidator:
    """Validates real-time EEG and Polar H10 data streams"""
    
    # Expected data freshness thresholds (seconds)
    MAX_DATA_AGE_STREAMING = 5.0
    MAX_DATA_AGE_WARNING = 15.0
    MAX_DATA_AGE_STALE = 30.0
    
    # Valid data ranges
    EEG_RANGES = {
        'alpha': (0.0, 100.0),
        'beta': (0.0, 100.0),
        'theta': (0.0, 100.0),
        'gamma': (0.0, 100.0),
        'delta': (0.0, 100.0)
    }
    
    POLAR_RANGES = {
        'heart_rate': (30, 220),
        'rmssd': (0, 300),
        'sdnn': (0, 500),
        'coherence': (0.0, 1.0)
    }
    
    def __init__(self):
        self.last_eeg_timestamp: Optional[datetime] = None
        self.last_polar_timestamp: Optional[datetime] = None
        self.validation_history: List[ValidationResult] = []
    
    def validate_eeg_stream(self, eeg_data: Optional[Dict]) -> ValidationResult:
        """Validate EEG data stream from Muse 2 or ESP32"""
        
        if eeg_data is None:
            return ValidationResult(
                test_name="EEG Stream Validation",
                status=ValidationStatus.FAILED,
                message="No EEG data received",
                details={'error': 'null_data'},
                tralseness_score=0.0
            )
        
        # Check data freshness
        if 'timestamp' in eeg_data:
            ts = eeg_data['timestamp']
            if isinstance(ts, str):
                ts = datetime.fromisoformat(ts)
            elif isinstance(ts, datetime):
                pass
            else:
                ts = datetime.now()
            
            age = (datetime.now() - ts).total_seconds()
            
            if age > self.MAX_DATA_AGE_STALE:
                return ValidationResult(
                    test_name="EEG Stream Validation",
                    status=ValidationStatus.FAILED,
                    message=f"EEG data is stale ({age:.1f}s old)",
                    details={'age_seconds': age, 'threshold': self.MAX_DATA_AGE_STALE},
                    tralseness_score=0.1
                )
            elif age > self.MAX_DATA_AGE_WARNING:
                status = ValidationStatus.WARNING
                tralseness = 0.5
            else:
                status = ValidationStatus.PASSED
                tralseness = 0.9
        else:
            status = ValidationStatus.WARNING
            tralseness = 0.6
            age = 0
        
        # Validate data ranges
        range_errors = []
        for band, (min_val, max_val) in self.EEG_RANGES.items():
            if band in eeg_data:
                val = eeg_data[band]
                if not (min_val <= val <= max_val):
                    range_errors.append(f"{band}={val} outside [{min_val}, {max_val}]")
        
        if range_errors:
            return ValidationResult(
                test_name="EEG Stream Validation",
                status=ValidationStatus.WARNING,
                message=f"EEG values out of range: {', '.join(range_errors)}",
                details={'range_errors': range_errors},
                tralseness_score=0.4
            )
        
        return ValidationResult(
            test_name="EEG Stream Validation",
            status=status,
            message=f"EEG stream valid (age: {age:.1f}s)",
            details={'age_seconds': age, 'bands_validated': list(self.EEG_RANGES.keys())},
            tralseness_score=tralseness
        )
    
    def validate_polar_stream(self, polar_data: Optional[Dict]) -> ValidationResult:
        """Validate Polar H10 heart data stream"""
        
        if polar_data is None:
            return ValidationResult(
                test_name="Polar H10 Stream Validation",
                status=ValidationStatus.FAILED,
                message="No Polar H10 data received",
                details={'error': 'null_data'},
                tralseness_score=0.0
            )
        
        # Check heart rate validity
        hr = polar_data.get('heart_rate', 0)
        min_hr, max_hr = self.POLAR_RANGES['heart_rate']
        
        if not (min_hr <= hr <= max_hr):
            return ValidationResult(
                test_name="Polar H10 Stream Validation",
                status=ValidationStatus.FAILED,
                message=f"Heart rate {hr} outside valid range [{min_hr}, {max_hr}]",
                details={'heart_rate': hr},
                tralseness_score=0.1
            )
        
        # Check HRV metrics
        rmssd = polar_data.get('rmssd', 0)
        min_rmssd, max_rmssd = self.POLAR_RANGES['rmssd']
        
        if rmssd < 20:
            status = ValidationStatus.WARNING
            msg = f"Low HRV (RMSSD={rmssd}ms) - stress indicator"
            tralseness = 0.5
        elif rmssd > 100:
            status = ValidationStatus.PASSED
            msg = f"Excellent HRV (RMSSD={rmssd}ms)"
            tralseness = 0.95
        else:
            status = ValidationStatus.PASSED
            msg = f"Good HRV (RMSSD={rmssd}ms)"
            tralseness = 0.8
        
        return ValidationResult(
            test_name="Polar H10 Stream Validation",
            status=status,
            message=msg,
            details={
                'heart_rate': hr,
                'rmssd': rmssd,
                'coherence': polar_data.get('coherence', 0)
            },
            tralseness_score=tralseness
        )
    
    def validate_esp32_bridge(self) -> ValidationResult:
        """Validate ESP32 BLE bridge connectivity and data flow"""
        
        if not HAS_DB:
            return ValidationResult(
                test_name="ESP32 Bridge Validation",
                status=ValidationStatus.SKIPPED,
                message="Database not available",
                tralseness_score=0.5
            )
        
        try:
            conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
            cur = conn.cursor()
            
            cur.execute("""
                SELECT timestamp, heart_rate, alpha, muse_connected, polar_connected
                FROM esp32_biometric_data 
                ORDER BY timestamp DESC LIMIT 1
            """)
            row = cur.fetchone()
            cur.close()
            conn.close()
            
            if not row:
                return ValidationResult(
                    test_name="ESP32 Bridge Validation",
                    status=ValidationStatus.FAILED,
                    message="No ESP32 data in database",
                    tralseness_score=0.0
                )
            
            last_ts = row[0]
            if isinstance(last_ts, datetime):
                age = (datetime.now() - last_ts).total_seconds()
            else:
                age = 999
            
            muse_connected = row[3] or False
            polar_connected = row[4] or False
            
            if age > 60:
                status = ValidationStatus.FAILED
                msg = f"ESP32 data stale ({age:.0f}s old)"
                tralseness = 0.1
            elif not (muse_connected or polar_connected):
                status = ValidationStatus.WARNING
                msg = "ESP32 active but no devices connected"
                tralseness = 0.4
            elif age > 30:
                status = ValidationStatus.WARNING
                msg = f"ESP32 data aging ({age:.0f}s)"
                tralseness = 0.6
            else:
                status = ValidationStatus.PASSED
                msg = f"ESP32 streaming (age: {age:.0f}s)"
                tralseness = 0.9
            
            return ValidationResult(
                test_name="ESP32 Bridge Validation",
                status=status,
                message=msg,
                details={
                    'age_seconds': age,
                    'muse_connected': muse_connected,
                    'polar_connected': polar_connected,
                    'heart_rate': row[1],
                    'alpha': row[2]
                },
                tralseness_score=tralseness
            )
            
        except Exception as e:
            return ValidationResult(
                test_name="ESP32 Bridge Validation",
                status=ValidationStatus.FAILED,
                message=f"Database error: {str(e)}",
                tralseness_score=0.0
            )


# ============================================================================
# 2. ANIMAL-TO-HUMAN PARAMETER TRANSFER VALIDATION
# ============================================================================

class AnimalHumanTransferValidator:
    """Validates animal-to-human parameter transfer using LCC Virus"""
    
    # Human physiological bounds
    HUMAN_HR_RANGE = (40, 180)
    HUMAN_RMSSD_RANGE = (10, 200)
    HUMAN_ALPHA_RANGE = (0, 100)
    
    # Species similarity coefficients (1.0 = identical to human)
    SPECIES_SIMILARITY = {
        'macaque': 0.92,
        'dog': 0.75,
        'cat': 0.68,
        'rat': 0.55,
        'mouse': 0.50,
        'rabbit': 0.45
    }
    
    # Gene profile scaling factors for human transfer
    GENE_TRANSFER_FACTORS = {
        'dopamine_sensitivity': 1.15,  # Humans slightly more sensitive
        'serotonin_sensitivity': 1.20,
        'gaba_efficiency': 0.95,
        'faah_activity': 0.80,  # Jo Cameron effect
        'bdnf_expression': 1.10,
        'comt_activity': 1.05
    }
    
    def __init__(self):
        self.validation_results: List[ValidationResult] = []
    
    def validate_species_transfer(
        self,
        source_species: str,
        animal_lcc: float,
        animal_gile: Dict[str, float]
    ) -> ValidationResult:
        """Validate that species parameters can transfer to humans"""
        
        similarity = self.SPECIES_SIMILARITY.get(source_species.lower(), 0.5)
        
        if similarity < 0.5:
            return ValidationResult(
                test_name="Species Transfer Validation",
                status=ValidationStatus.WARNING,
                message=f"Low species similarity ({similarity:.0%}) - transfer may be inaccurate",
                details={
                    'species': source_species,
                    'similarity': similarity,
                    'recommended_species': 'macaque'
                },
                tralseness_score=similarity * 0.8
            )
        
        # Calculate transfer confidence
        transfer_confidence = similarity * animal_lcc
        
        if transfer_confidence > 0.75:
            status = ValidationStatus.PASSED
            msg = f"High transfer confidence ({transfer_confidence:.0%})"
        elif transfer_confidence > 0.5:
            status = ValidationStatus.WARNING
            msg = f"Moderate transfer confidence ({transfer_confidence:.0%})"
        else:
            status = ValidationStatus.FAILED
            msg = f"Low transfer confidence ({transfer_confidence:.0%})"
        
        return ValidationResult(
            test_name="Species Transfer Validation",
            status=status,
            message=msg,
            details={
                'species': source_species,
                'similarity': similarity,
                'animal_lcc': animal_lcc,
                'animal_gile': animal_gile,
                'transfer_confidence': transfer_confidence
            },
            tralseness_score=transfer_confidence
        )
    
    def validate_parameter_bounds(
        self,
        transferred_params: Dict[str, float]
    ) -> ValidationResult:
        """Validate that transferred parameters are within human bounds"""
        
        violations = []
        
        if 'heart_rate' in transferred_params:
            hr = transferred_params['heart_rate']
            if not (self.HUMAN_HR_RANGE[0] <= hr <= self.HUMAN_HR_RANGE[1]):
                violations.append(f"HR={hr} outside human range {self.HUMAN_HR_RANGE}")
        
        if 'rmssd' in transferred_params:
            rmssd = transferred_params['rmssd']
            if not (self.HUMAN_RMSSD_RANGE[0] <= rmssd <= self.HUMAN_RMSSD_RANGE[1]):
                violations.append(f"RMSSD={rmssd} outside human range {self.HUMAN_RMSSD_RANGE}")
        
        if 'alpha' in transferred_params:
            alpha = transferred_params['alpha']
            if not (self.HUMAN_ALPHA_RANGE[0] <= alpha <= self.HUMAN_ALPHA_RANGE[1]):
                violations.append(f"Alpha={alpha} outside human range {self.HUMAN_ALPHA_RANGE}")
        
        if violations:
            return ValidationResult(
                test_name="Parameter Bounds Validation",
                status=ValidationStatus.FAILED,
                message=f"Parameters outside human bounds: {'; '.join(violations)}",
                details={'violations': violations},
                tralseness_score=0.2
            )
        
        return ValidationResult(
            test_name="Parameter Bounds Validation",
            status=ValidationStatus.PASSED,
            message="All parameters within human physiological bounds",
            details={'params_validated': list(transferred_params.keys())},
            tralseness_score=0.9
        )
    
    def apply_human_transfer_factors(
        self,
        animal_gene_profile: Dict[str, float]
    ) -> Tuple[Dict[str, float], ValidationResult]:
        """Apply transfer factors to convert animal genes to human equivalents"""
        
        human_profile = {}
        adjustments = []
        
        for gene, animal_value in animal_gene_profile.items():
            factor = self.GENE_TRANSFER_FACTORS.get(gene, 1.0)
            human_value = np.clip(animal_value * factor, 0.0, 1.0)
            human_profile[gene] = float(human_value)
            
            if abs(factor - 1.0) > 0.1:
                adjustments.append(f"{gene}: {animal_value:.2f} → {human_value:.2f} (×{factor})")
        
        return human_profile, ValidationResult(
            test_name="Gene Transfer Factors",
            status=ValidationStatus.PASSED,
            message=f"Applied {len(adjustments)} transfer adjustments",
            details={
                'animal_profile': animal_gene_profile,
                'human_profile': human_profile,
                'adjustments': adjustments
            },
            tralseness_score=0.85
        )


# ============================================================================
# 3. CHATGPT ERROR-PREVENTION SAFEGUARDS
# ============================================================================

class ChatGPTErrorPrevention:
    """
    Safeguards to prevent ChatGPT/AI-induced errors in mood amplification.
    
    Key error types:
    1. Hallucinated biometric values
    2. Unsafe GILE recommendations
    3. Mismatched species parameters
    4. Out-of-bounds consciousness states
    """
    
    # GILE safety thresholds
    MIN_SAFE_GILE = -2.0
    MAX_SAFE_GILE = 2.5
    
    # Consciousness state safety
    MIN_SAFE_ALPHA = 5.0  # Minimum alpha to prevent dissociation
    MAX_SAFE_BETA = 80.0  # Maximum beta to prevent anxiety
    MAX_SAFE_GAMMA = 60.0  # Maximum gamma to prevent overstimulation
    
    # Session safety limits
    MAX_SESSION_DURATION_MINUTES = 60
    MIN_SESSION_DURATION_MINUTES = 3
    MAX_MOOD_SHIFT_PER_SESSION = 0.8
    
    def __init__(self):
        self.error_log: List[Dict] = []
    
    def validate_gile_input(self, gile_scores: Dict[str, float]) -> ValidationResult:
        """Validate GILE scores are within safe bounds"""
        
        errors = []
        
        for dimension in ['G', 'I', 'L', 'E', 'overall']:
            if dimension in gile_scores:
                val = gile_scores[dimension]
                
                # Check for None/NaN
                if val is None or (isinstance(val, float) and np.isnan(val)):
                    errors.append(f"{dimension} is null/NaN")
                    continue
                
                # Check bounds
                if not (self.MIN_SAFE_GILE <= val <= self.MAX_SAFE_GILE):
                    errors.append(f"{dimension}={val:.2f} outside safe range [{self.MIN_SAFE_GILE}, {self.MAX_SAFE_GILE}]")
        
        if errors:
            self._log_error("GILE Bounds Violation", errors)
            return ValidationResult(
                test_name="GILE Input Validation",
                status=ValidationStatus.FAILED,
                message=f"Unsafe GILE values: {'; '.join(errors)}",
                details={'errors': errors, 'input': gile_scores},
                tralseness_score=0.1
            )
        
        return ValidationResult(
            test_name="GILE Input Validation",
            status=ValidationStatus.PASSED,
            message="GILE scores within safe bounds",
            details={'gile': gile_scores},
            tralseness_score=0.9
        )
    
    def validate_consciousness_state(
        self,
        alpha: float,
        beta: float,
        gamma: float,
        theta: float = 0,
        delta: float = 0
    ) -> ValidationResult:
        """Validate consciousness state is safe for amplification"""
        
        warnings = []
        critical = []
        
        # Check for dissociative risk (very low alpha)
        if alpha < self.MIN_SAFE_ALPHA:
            critical.append(f"Alpha too low ({alpha:.1f}) - dissociation risk")
        
        # Check for anxiety risk (high beta)
        if beta > self.MAX_SAFE_BETA:
            warnings.append(f"Beta elevated ({beta:.1f}) - anxiety indicator")
        
        # Check for overstimulation (high gamma)
        if gamma > self.MAX_SAFE_GAMMA:
            warnings.append(f"Gamma elevated ({gamma:.1f}) - overstimulation risk")
        
        # Check for drowsiness/unconsciousness (high delta)
        if delta > 60:
            warnings.append(f"Delta elevated ({delta:.1f}) - drowsiness")
        
        # Determine overall state
        if critical:
            self._log_error("Consciousness State Critical", critical)
            return ValidationResult(
                test_name="Consciousness State Validation",
                status=ValidationStatus.FAILED,
                message=f"CRITICAL: {'; '.join(critical)}",
                details={'bands': {'alpha': alpha, 'beta': beta, 'gamma': gamma, 'theta': theta, 'delta': delta}},
                tralseness_score=0.1
            )
        
        if warnings:
            return ValidationResult(
                test_name="Consciousness State Validation",
                status=ValidationStatus.WARNING,
                message=f"Warnings: {'; '.join(warnings)}",
                details={'bands': {'alpha': alpha, 'beta': beta, 'gamma': gamma, 'theta': theta, 'delta': delta}},
                tralseness_score=0.5
            )
        
        return ValidationResult(
            test_name="Consciousness State Validation",
            status=ValidationStatus.PASSED,
            message="Consciousness state safe for amplification",
            details={'bands': {'alpha': alpha, 'beta': beta, 'gamma': gamma, 'theta': theta, 'delta': delta}},
            tralseness_score=0.9
        )
    
    def validate_session_parameters(
        self,
        duration_minutes: float,
        target_mood_shift: float,
        faah_tier: int
    ) -> ValidationResult:
        """Validate session parameters are safe"""
        
        errors = []
        
        if duration_minutes > self.MAX_SESSION_DURATION_MINUTES:
            errors.append(f"Duration {duration_minutes}min exceeds max {self.MAX_SESSION_DURATION_MINUTES}min")
        
        if duration_minutes < self.MIN_SESSION_DURATION_MINUTES:
            errors.append(f"Duration {duration_minutes}min below min {self.MIN_SESSION_DURATION_MINUTES}min")
        
        if abs(target_mood_shift) > self.MAX_MOOD_SHIFT_PER_SESSION:
            errors.append(f"Mood shift {target_mood_shift:.2f} exceeds safe max {self.MAX_MOOD_SHIFT_PER_SESSION}")
        
        if faah_tier not in [1, 2, 3, 4]:
            errors.append(f"Invalid FAAH tier {faah_tier} (must be 1-4)")
        
        if errors:
            self._log_error("Session Parameters Unsafe", errors)
            return ValidationResult(
                test_name="Session Parameters Validation",
                status=ValidationStatus.FAILED,
                message=f"Unsafe parameters: {'; '.join(errors)}",
                details={'errors': errors},
                tralseness_score=0.2
            )
        
        return ValidationResult(
            test_name="Session Parameters Validation",
            status=ValidationStatus.PASSED,
            message="Session parameters within safe bounds",
            details={
                'duration': duration_minutes,
                'mood_shift': target_mood_shift,
                'faah_tier': faah_tier
            },
            tralseness_score=0.9
        )
    
    def detect_hallucinated_values(
        self,
        biometric_data: Dict[str, Any],
        expected_source: str = "real"
    ) -> ValidationResult:
        """Detect if biometric values appear to be AI-generated/hallucinated"""
        
        hallucination_indicators = []
        
        # Check for suspiciously round numbers
        for key, val in biometric_data.items():
            if isinstance(val, (int, float)):
                # Exact integers in continuous measurements are suspicious
                if key in ['heart_rate', 'rmssd', 'alpha', 'beta'] and val == round(val) and val % 5 == 0:
                    hallucination_indicators.append(f"{key}={val} is suspiciously round")
        
        # Check for impossible combinations
        if 'heart_rate' in biometric_data and 'rmssd' in biometric_data:
            hr = biometric_data['heart_rate']
            rmssd = biometric_data['rmssd']
            
            # Very high HR with very high HRV is physiologically unlikely
            if hr > 150 and rmssd > 100:
                hallucination_indicators.append(f"HR={hr} with RMSSD={rmssd} is physiologically unlikely")
        
        # Check for perfect patterns (real data has noise)
        if 'alpha' in biometric_data and 'beta' in biometric_data:
            if biometric_data['alpha'] + biometric_data['beta'] == 100:
                hallucination_indicators.append("Alpha + Beta = exactly 100 suggests synthetic data")
        
        if hallucination_indicators:
            self._log_error("Hallucination Detection", hallucination_indicators)
            return ValidationResult(
                test_name="Hallucination Detection",
                status=ValidationStatus.WARNING,
                message=f"Possible hallucinated values: {'; '.join(hallucination_indicators)}",
                details={'indicators': hallucination_indicators, 'data': biometric_data},
                tralseness_score=0.4
            )
        
        return ValidationResult(
            test_name="Hallucination Detection",
            status=ValidationStatus.PASSED,
            message="Data appears authentic",
            details={'data': biometric_data, 'source': expected_source},
            tralseness_score=0.9
        )
    
    def _log_error(self, error_type: str, details: List[str]):
        """Log error for audit trail"""
        self.error_log.append({
            'timestamp': datetime.now().isoformat(),
            'type': error_type,
            'details': details
        })


# ============================================================================
# 4. EMOTIONAL RESPONSE VALIDATION
# ============================================================================

class EmotionalResponseValidator:
    """
    Validates emotional responses using biometric correlation scoring.
    Maps physiological signals to emotional states via TI Framework.
    """
    
    # Emotional state signatures (expected biometric patterns)
    EMOTIONAL_SIGNATURES = {
        'calm': {
            'alpha_range': (40, 80),
            'beta_range': (10, 30),
            'hr_range': (55, 75),
            'rmssd_min': 50,
            'expected_gile': 0.7
        },
        'focused': {
            'alpha_range': (20, 50),
            'beta_range': (35, 60),
            'hr_range': (65, 90),
            'rmssd_min': 30,
            'expected_gile': 0.6
        },
        'anxious': {
            'alpha_range': (5, 25),
            'beta_range': (50, 80),
            'hr_range': (85, 120),
            'rmssd_min': 0,  # Often low
            'expected_gile': 0.3
        },
        'flow': {
            'alpha_range': (35, 55),
            'gamma_range': (30, 50),
            'hr_range': (60, 80),
            'rmssd_min': 60,
            'expected_gile': 0.9
        },
        'meditative': {
            'theta_range': (40, 70),
            'alpha_range': (45, 75),
            'hr_range': (50, 65),
            'rmssd_min': 70,
            'expected_gile': 0.85
        }
    }
    
    def __init__(self):
        self.response_history: List[Dict] = []
    
    def detect_emotional_state(
        self,
        alpha: float,
        beta: float,
        gamma: float,
        theta: float,
        heart_rate: float,
        rmssd: float
    ) -> Tuple[str, float, ValidationResult]:
        """
        Detect current emotional state from biometrics.
        Returns: (state_name, confidence, validation_result)
        """
        
        best_match = 'neutral'
        best_score = 0.0
        match_details = {}
        
        for state, signature in self.EMOTIONAL_SIGNATURES.items():
            score = 0.0
            matches = 0
            total_checks = 0
            
            # Check alpha
            if 'alpha_range' in signature:
                total_checks += 1
                a_min, a_max = signature['alpha_range']
                if a_min <= alpha <= a_max:
                    score += 1.0
                    matches += 1
                else:
                    # Partial match for nearby values
                    dist = min(abs(alpha - a_min), abs(alpha - a_max))
                    score += max(0, 1 - dist / 20)
            
            # Check beta
            if 'beta_range' in signature:
                total_checks += 1
                b_min, b_max = signature['beta_range']
                if b_min <= beta <= b_max:
                    score += 1.0
                    matches += 1
            
            # Check gamma
            if 'gamma_range' in signature:
                total_checks += 1
                g_min, g_max = signature['gamma_range']
                if g_min <= gamma <= g_max:
                    score += 1.0
                    matches += 1
            
            # Check theta
            if 'theta_range' in signature:
                total_checks += 1
                t_min, t_max = signature['theta_range']
                if t_min <= theta <= t_max:
                    score += 1.0
                    matches += 1
            
            # Check heart rate
            if 'hr_range' in signature:
                total_checks += 1
                hr_min, hr_max = signature['hr_range']
                if hr_min <= heart_rate <= hr_max:
                    score += 1.0
                    matches += 1
            
            # Check RMSSD
            if 'rmssd_min' in signature:
                total_checks += 1
                if rmssd >= signature['rmssd_min']:
                    score += 1.0
                    matches += 1
            
            normalized_score = score / total_checks if total_checks > 0 else 0
            match_details[state] = {
                'score': normalized_score,
                'matches': matches,
                'total_checks': total_checks
            }
            
            if normalized_score > best_score:
                best_score = normalized_score
                best_match = state
        
        # Calculate Tralseness based on coherence
        tralseness = best_score * 0.9  # Scale to 0-0.9 range
        
        if best_score > 0.7:
            status = ValidationStatus.PASSED
            msg = f"Detected emotional state: {best_match} (confidence: {best_score:.0%})"
        elif best_score > 0.4:
            status = ValidationStatus.WARNING
            msg = f"Uncertain emotional state: {best_match} (confidence: {best_score:.0%})"
        else:
            status = ValidationStatus.WARNING
            msg = f"Unclear emotional state (best guess: {best_match}, confidence: {best_score:.0%})"
        
        result = ValidationResult(
            test_name="Emotional State Detection",
            status=status,
            message=msg,
            details={
                'detected_state': best_match,
                'confidence': best_score,
                'all_matches': match_details,
                'input': {
                    'alpha': alpha, 'beta': beta, 'gamma': gamma,
                    'theta': theta, 'heart_rate': heart_rate, 'rmssd': rmssd
                }
            },
            tralseness_score=tralseness
        )
        
        self.response_history.append({
            'timestamp': datetime.now().isoformat(),
            'state': best_match,
            'confidence': best_score
        })
        
        return best_match, best_score, result
    
    def validate_mood_shift_response(
        self,
        pre_state: str,
        post_state: str,
        target_direction: str,
        shift_magnitude: float
    ) -> ValidationResult:
        """Validate that mood shift achieved target direction"""
        
        # Define state positivity scores
        STATE_POSITIVITY = {
            'flow': 1.0,
            'calm': 0.8,
            'meditative': 0.85,
            'focused': 0.6,
            'neutral': 0.5,
            'anxious': 0.2
        }
        
        pre_positivity = STATE_POSITIVITY.get(pre_state, 0.5)
        post_positivity = STATE_POSITIVITY.get(post_state, 0.5)
        
        actual_shift = post_positivity - pre_positivity
        
        # Check if shift matches target direction
        if target_direction == 'positive' and actual_shift > 0:
            success = True
            msg = f"Positive shift achieved: {pre_state} → {post_state} (+{actual_shift:.2f})"
        elif target_direction == 'negative' and actual_shift < 0:
            success = True
            msg = f"Negative shift achieved: {pre_state} → {post_state} ({actual_shift:.2f})"
        elif target_direction == 'neutral' and abs(actual_shift) < 0.2:
            success = True
            msg = f"Neutral state maintained: {pre_state} → {post_state}"
        else:
            success = False
            msg = f"Shift mismatch: wanted {target_direction}, got {actual_shift:+.2f}"
        
        # Calculate effectiveness
        if success:
            effectiveness = min(1.0, abs(actual_shift) / max(shift_magnitude, 0.1))
            tralseness = 0.7 + 0.3 * effectiveness
            status = ValidationStatus.PASSED
        else:
            effectiveness = 0.0
            tralseness = 0.3
            status = ValidationStatus.FAILED
        
        return ValidationResult(
            test_name="Mood Shift Response Validation",
            status=status,
            message=msg,
            details={
                'pre_state': pre_state,
                'post_state': post_state,
                'target_direction': target_direction,
                'actual_shift': actual_shift,
                'target_magnitude': shift_magnitude,
                'effectiveness': effectiveness
            },
            tralseness_score=tralseness
        )


# ============================================================================
# 5. TRALSENESS INTEGRATION
# ============================================================================

class TralsenessValidator:
    """
    Integrates TI Framework Tralseness scoring across all validation domains.
    Computes overall consciousness coherence based on spectral truth theory.
    """
    
    def __init__(self):
        self.threshold_coherent = TralsenessThreshold.COHERENT_CAUSATION.value
        self.threshold_sustainable = TralsenessThreshold.SUSTAINABLE_COHERENCE.value
    
    def compute_session_tralseness(
        self,
        biometric_results: List[ValidationResult],
        transfer_results: List[ValidationResult],
        safety_results: List[ValidationResult],
        emotional_results: List[ValidationResult]
    ) -> Tuple[float, Dict[str, float], ValidationResult]:
        """
        Compute overall session Tralseness from all validation domains.
        
        Returns: (overall_tralseness, domain_scores, validation_result)
        """
        
        def domain_score(results: List[ValidationResult]) -> float:
            if not results:
                return 0.5
            return np.mean([r.tralseness_score for r in results])
        
        biometric_score = domain_score(biometric_results)
        transfer_score = domain_score(transfer_results)
        safety_score = domain_score(safety_results)
        emotional_score = domain_score(emotional_results)
        
        # GILE-weighted combination
        # G (Goodness) = Safety (30%)
        # I (Intuition) = Emotional (25%)
        # L (Love) = Transfer/connection (20%)
        # E (Environment) = Biometric context (25%)
        
        gile_weighted = float(
            0.30 * safety_score +      # G
            0.25 * emotional_score +   # I
            0.20 * transfer_score +    # L
            0.25 * biometric_score     # E
        )
        
        domain_scores = {
            'G_safety': safety_score,
            'I_emotional': emotional_score,
            'L_transfer': transfer_score,
            'E_biometric': biometric_score,
            'overall': gile_weighted
        }
        
        # Determine consciousness coherence level
        if gile_weighted >= self.threshold_sustainable:
            status = ValidationStatus.PASSED
            coherence_level = "SUSTAINABLE_COHERENCE"
            msg = f"🌟 Sustainable coherence achieved ({gile_weighted:.2f} ≥ 0.92)"
        elif gile_weighted >= self.threshold_coherent:
            status = ValidationStatus.PASSED
            coherence_level = "COHERENT_CAUSATION"
            msg = f"✅ Coherent causation level ({gile_weighted:.2f} ≥ 0.85)"
        elif gile_weighted >= 0.65:
            status = ValidationStatus.WARNING
            coherence_level = "MEDIUM_RESONANCE"
            msg = f"⚠️ Medium resonance ({gile_weighted:.2f})"
        elif gile_weighted >= 0.42:
            status = ValidationStatus.WARNING
            coherence_level = "LOW_RESONANCE"
            msg = f"⚠️ Low resonance ({gile_weighted:.2f})"
        else:
            status = ValidationStatus.FAILED
            coherence_level = "BELOW_THRESHOLD"
            msg = f"❌ Below resonance threshold ({gile_weighted:.2f} < 0.42)"
        
        result = ValidationResult(
            test_name="Session Tralseness Computation",
            status=status,
            message=msg,
            details={
                'domain_scores': domain_scores,
                'coherence_level': coherence_level,
                'thresholds': {
                    'sustainable': self.threshold_sustainable,
                    'coherent': self.threshold_coherent
                }
            },
            tralseness_score=gile_weighted
        )
        
        return gile_weighted, domain_scores, result


# ============================================================================
# 6. COMPREHENSIVE VALIDATION ORCHESTRATOR
# ============================================================================

class MoodAmplifierValidator:
    """
    Master orchestrator for all Mood Amplifier validation.
    Runs complete validation suite and generates comprehensive reports.
    """
    
    def __init__(self):
        self.biometric_validator = BiometricDataFlowValidator()
        self.transfer_validator = AnimalHumanTransferValidator()
        self.error_prevention = ChatGPTErrorPrevention()
        self.emotional_validator = EmotionalResponseValidator()
        self.tralseness_validator = TralsenessValidator()
        
        self.validation_history: List[ValidationReport] = []
    
    def run_full_validation(
        self,
        eeg_data: Optional[Dict] = None,
        polar_data: Optional[Dict] = None,
        animal_session: Optional[Dict] = None,
        session_params: Optional[Dict] = None
    ) -> ValidationReport:
        """
        Run complete validation suite.
        
        Args:
            eeg_data: Current EEG readings
            polar_data: Current Polar H10 readings
            animal_session: Animal training session for transfer validation
            session_params: Current session parameters
            
        Returns:
            Complete ValidationReport
        """
        
        import uuid
        report_id = str(uuid.uuid4())[:8]
        
        all_results: List[ValidationResult] = []
        biometric_results: List[ValidationResult] = []
        transfer_results: List[ValidationResult] = []
        safety_results: List[ValidationResult] = []
        emotional_results: List[ValidationResult] = []
        
        # 1. Biometric Data Flow Validation
        if eeg_data:
            result = self.biometric_validator.validate_eeg_stream(eeg_data)
            biometric_results.append(result)
            all_results.append(result)
        
        if polar_data:
            result = self.biometric_validator.validate_polar_stream(polar_data)
            biometric_results.append(result)
            all_results.append(result)
        
        # ESP32 validation
        result = self.biometric_validator.validate_esp32_bridge()
        biometric_results.append(result)
        all_results.append(result)
        
        # 2. Animal-to-Human Transfer Validation
        if animal_session:
            species = animal_session.get('species', 'macaque')
            lcc = animal_session.get('lcc_strength', 0.7)
            gile = animal_session.get('gile', {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5})
            
            result = self.transfer_validator.validate_species_transfer(species, lcc, gile)
            transfer_results.append(result)
            all_results.append(result)
            
            if 'transferred_params' in animal_session:
                result = self.transfer_validator.validate_parameter_bounds(
                    animal_session['transferred_params']
                )
                transfer_results.append(result)
                all_results.append(result)
        
        # 3. Safety/Error Prevention
        if eeg_data and 'alpha' in eeg_data:
            gile_input = {
                'G': eeg_data.get('gile_g', 0.5),
                'I': eeg_data.get('gile_i', 0.5),
                'L': eeg_data.get('gile_l', 0.5),
                'E': eeg_data.get('gile_e', 0.5),
                'overall': eeg_data.get('gile', 0.5)
            }
            result = self.error_prevention.validate_gile_input(gile_input)
            safety_results.append(result)
            all_results.append(result)
            
            result = self.error_prevention.validate_consciousness_state(
                alpha=eeg_data.get('alpha', 50),
                beta=eeg_data.get('beta', 30),
                gamma=eeg_data.get('gamma', 10),
                theta=eeg_data.get('theta', 20),
                delta=eeg_data.get('delta', 10)
            )
            safety_results.append(result)
            all_results.append(result)
            
            # Hallucination detection
            combined_data = {**eeg_data}
            if polar_data:
                combined_data.update(polar_data)
            result = self.error_prevention.detect_hallucinated_values(combined_data)
            safety_results.append(result)
            all_results.append(result)
        
        if session_params:
            result = self.error_prevention.validate_session_parameters(
                duration_minutes=session_params.get('duration', 10),
                target_mood_shift=session_params.get('mood_shift', 0.5),
                faah_tier=session_params.get('faah_tier', 2)
            )
            safety_results.append(result)
            all_results.append(result)
        
        # 4. Emotional Response Validation
        if eeg_data and polar_data:
            state, confidence, result = self.emotional_validator.detect_emotional_state(
                alpha=eeg_data.get('alpha', 50),
                beta=eeg_data.get('beta', 30),
                gamma=eeg_data.get('gamma', 10),
                theta=eeg_data.get('theta', 20),
                heart_rate=polar_data.get('heart_rate', 70),
                rmssd=polar_data.get('rmssd', 50)
            )
            emotional_results.append(result)
            all_results.append(result)
        
        # 5. Compute Overall Tralseness
        overall_tralseness, gile_scores, tralseness_result = self.tralseness_validator.compute_session_tralseness(
            biometric_results,
            transfer_results,
            safety_results,
            emotional_results
        )
        all_results.append(tralseness_result)
        
        # Build report
        report = ValidationReport(
            report_id=report_id,
            created_at=datetime.now(),
            results=all_results,
            overall_tralseness=overall_tralseness,
            gile_scores=gile_scores
        )
        
        self.validation_history.append(report)
        
        return report
    
    def run_quick_validation(self) -> ValidationReport:
        """Run quick validation with demo/simulated data"""
        
        demo_eeg = {
            'timestamp': datetime.now(),
            'alpha': 45.0 + np.random.normal(0, 5),
            'beta': 28.0 + np.random.normal(0, 3),
            'gamma': 12.0 + np.random.normal(0, 2),
            'theta': 22.0 + np.random.normal(0, 3),
            'delta': 15.0 + np.random.normal(0, 2),
            'gile': 0.65
        }
        
        demo_polar = {
            'heart_rate': 68 + np.random.randint(-5, 5),
            'rmssd': 55 + np.random.randint(-10, 10),
            'coherence': 0.72
        }
        
        demo_session = {
            'duration': 10,
            'mood_shift': 0.5,
            'faah_tier': 2
        }
        
        demo_animal = {
            'species': 'macaque',
            'lcc_strength': 0.78,
            'gile': {'G': 0.7, 'I': 0.65, 'L': 0.72, 'E': 0.68}
        }
        
        return self.run_full_validation(
            eeg_data=demo_eeg,
            polar_data=demo_polar,
            animal_session=demo_animal,
            session_params=demo_session
        )


# ============================================================================
# STREAMLIT DASHBOARD
# ============================================================================

def render_ma_validation_dashboard():
    """Streamlit dashboard for MA validation system"""
    import streamlit as st
    
    st.header("🔬 Mood Amplifier Validation System")
    st.markdown("""
    Comprehensive autonomous validation for the Mood Amplifier including:
    - Real-time EEG/Polar H10 data flow validation
    - Animal-to-human parameter transfer (LCC Virus)
    - ChatGPT error-prevention safeguards
    - Emotional response validation with biometric correlation
    - TI Framework Tralseness integration
    """)
    
    if 'ma_validator' not in st.session_state:
        st.session_state.ma_validator = MoodAmplifierValidator()
    
    validator = st.session_state.ma_validator
    
    tabs = st.tabs(["🚀 Quick Validation", "📊 Full Validation", "📜 History", "⚙️ Settings"])
    
    with tabs[0]:
        st.subheader("Quick Validation (Demo Mode)")
        st.info("Runs validation with simulated biometric data to test the system.")
        
        if st.button("▶️ Run Quick Validation", type="primary"):
            with st.spinner("Running validation suite..."):
                report = validator.run_quick_validation()
                
                # Display results
                status_emoji = "✅" if report.overall_status == ValidationStatus.PASSED else "⚠️" if report.overall_status == ValidationStatus.WARNING else "❌"
                
                st.markdown(f"### {status_emoji} Validation Complete")
                
                col1, col2, col3, col4 = st.columns(4)
                col1.metric("Overall Tralseness", f"{report.overall_tralseness:.2f}")
                col2.metric("Passed", report.passed_count)
                col3.metric("Warnings", report.warning_count)
                col4.metric("Failed", report.failed_count)
                
                # GILE breakdown
                st.markdown("#### GILE Domain Scores")
                gile_cols = st.columns(5)
                for i, (key, val) in enumerate(report.gile_scores.items()):
                    gile_cols[i].metric(key, f"{val:.2f}")
                
                # Individual results
                st.markdown("#### Validation Results")
                for result in report.results:
                    with st.expander(f"{result.status.value.upper()}: {result.test_name}"):
                        st.write(f"**Message:** {result.message}")
                        st.write(f"**Tralseness Score:** {result.tralseness_score:.2f}")
                        if result.details:
                            st.json(result.details)
    
    with tabs[1]:
        st.subheader("Full Validation (Live Data)")
        st.warning("Requires connected Muse 2 and Polar H10 devices.")
        
        # Show current device status
        st.markdown("#### Device Status")
        esp32_result = validator.biometric_validator.validate_esp32_bridge()
        
        if esp32_result.status == ValidationStatus.PASSED:
            st.success(f"ESP32: {esp32_result.message}")
        elif esp32_result.status == ValidationStatus.WARNING:
            st.warning(f"ESP32: {esp32_result.message}")
        else:
            st.error(f"ESP32: {esp32_result.message}")
        
        if st.button("▶️ Run Full Validation"):
            st.info("Full validation requires live biometric data. Using quick validation for demo.")
            report = validator.run_quick_validation()
            st.success(f"Report ID: {report.report_id}")
    
    with tabs[2]:
        st.subheader("Validation History")
        
        if validator.validation_history:
            for i, report in enumerate(reversed(validator.validation_history[-10:])):
                status_emoji = "✅" if report.overall_status == ValidationStatus.PASSED else "⚠️" if report.overall_status == ValidationStatus.WARNING else "❌"
                with st.expander(f"{status_emoji} Report {report.report_id} - {report.created_at.strftime('%Y-%m-%d %H:%M:%S')}"):
                    st.json(report.to_dict())
        else:
            st.info("No validation history yet. Run a validation to see results here.")
    
    with tabs[3]:
        st.subheader("Validation Settings")
        
        st.markdown("#### Safety Thresholds")
        col1, col2 = st.columns(2)
        with col1:
            st.number_input("Max Session Duration (min)", value=60, min_value=5, max_value=120)
            st.number_input("Min Alpha for Safety", value=5.0, min_value=0.0, max_value=20.0)
        with col2:
            st.number_input("Max Mood Shift per Session", value=0.8, min_value=0.1, max_value=1.0)
            st.number_input("Max Beta for Safety", value=80.0, min_value=50.0, max_value=100.0)
        
        st.markdown("#### Tralseness Thresholds")
        st.slider("Coherent Causation Threshold", 0.5, 1.0, 0.85)
        st.slider("Sustainable Coherence Threshold", 0.5, 1.0, 0.92)


if __name__ == "__main__":
    # Run validation test
    print("Mood Amplifier Validation System - Test Run")
    print("=" * 60)
    
    validator = MoodAmplifierValidator()
    report = validator.run_quick_validation()
    
    print(f"\nReport ID: {report.report_id}")
    print(f"Overall Status: {report.overall_status.value}")
    print(f"Overall Tralseness: {report.overall_tralseness:.2f}")
    print(f"\nResults: {report.passed_count} passed, {report.warning_count} warnings, {report.failed_count} failed")
    
    print("\nGILE Domain Scores:")
    for key, val in report.gile_scores.items():
        print(f"  {key}: {val:.2f}")
    
    print("\nDetailed Results:")
    for result in report.results:
        print(f"  [{result.status.value}] {result.test_name}: {result.message}")
