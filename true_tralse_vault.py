"""
True-Tralse Vault: GILE Prediction Verification & Backtesting System

This module provides:
1. Storage of 0.92+ GILE predictions with timestamps
2. Verification of predictions after they occur (minutes/hours/days)
3. Backtesting capability against historical data
4. Confidence-weighted scoring system

The Vault operates on the principle that predictions above the 0.92 True-Tralseness
threshold should manifest with 85%+ accuracy (0.92² ≈ 0.85).
"""

import json
import os
from datetime import datetime, timedelta
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple, Any
from enum import Enum
import hashlib


class PredictionStatus(Enum):
    PENDING = "pending"
    VERIFIED_TRUE = "verified_true"
    VERIFIED_FALSE = "verified_false"
    EXPIRED = "expired"
    INCONCLUSIVE = "inconclusive"


class PredictionCategory(Enum):
    STOCK_MOVEMENT = "stock_movement"
    MOOD_SHIFT = "mood_shift"
    RELATIONSHIP = "relationship"
    HEALTH = "health"
    SYNCHRONIZATION = "synchronization"
    MARKET_TREND = "market_trend"
    PSI_EVENT = "psi_event"
    CONSCIOUSNESS = "consciousness"
    OTHER = "other"


@dataclass
class GILEPrediction:
    """A single GILE-based prediction stored in the vault."""
    
    prediction_id: str
    timestamp_created: str
    
    prediction_text: str
    category: str
    
    gile_score: float
    confidence: float
    
    verification_deadline: str
    verification_criteria: str
    
    status: str = "pending"
    outcome_text: Optional[str] = None
    verified_at: Optional[str] = None
    accuracy_score: Optional[float] = None
    
    gile_breakdown: Dict[str, float] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def __post_init__(self):
        if not self.prediction_id:
            content = f"{self.timestamp_created}{self.prediction_text}"
            self.prediction_id = hashlib.sha256(content.encode()).hexdigest()[:16]


@dataclass
class VaultStatistics:
    """Aggregate statistics for the vault."""
    
    total_predictions: int = 0
    verified_true: int = 0
    verified_false: int = 0
    pending: int = 0
    expired: int = 0
    
    average_gile_score: float = 0.0
    accuracy_rate: float = 0.0
    
    category_breakdown: Dict[str, int] = field(default_factory=dict)
    threshold_performance: Dict[str, Dict] = field(default_factory=dict)


class TrueTralseVault:
    """
    The True-Tralse Vault stores and verifies GILE predictions.
    
    Key Thresholds (TI Framework):
    - 0.92+: True-Tralseness threshold (sustainable coherence)
    - 0.85+: Causation/Major truth threshold (0.92² ≈ 0.85)
    - 0.70+: Moderate confidence
    - 0.50+: Slight lean toward true
    """
    
    VAULT_FILE = "vault_predictions.json"
    
    TRUE_TRALSENESS_THRESHOLD = 0.92
    CAUSATION_THRESHOLD = 0.85
    MODERATE_THRESHOLD = 0.70
    
    def __init__(self, vault_path: Optional[str] = None):
        self.vault_path = vault_path or self.VAULT_FILE
        self.predictions: List[GILEPrediction] = []
        self._load_vault()
    
    def _load_vault(self) -> None:
        """Load predictions from persistent storage."""
        if os.path.exists(self.vault_path):
            try:
                with open(self.vault_path, 'r') as f:
                    data = json.load(f)
                    self.predictions = [
                        GILEPrediction(**p) for p in data.get("predictions", [])
                    ]
            except (json.JSONDecodeError, Exception) as e:
                print(f"Warning: Could not load vault: {e}")
                self.predictions = []
    
    def _save_vault(self) -> None:
        """Save predictions to persistent storage."""
        data = {
            "last_updated": datetime.now().isoformat(),
            "version": "1.0",
            "predictions": [asdict(p) for p in self.predictions]
        }
        with open(self.vault_path, 'w') as f:
            json.dump(data, f, indent=2)
    
    def add_prediction(
        self,
        prediction_text: str,
        category: PredictionCategory,
        gile_score: float,
        confidence: float,
        verification_deadline: datetime,
        verification_criteria: str,
        gile_breakdown: Optional[Dict[str, float]] = None,
        metadata: Optional[Dict] = None,
        enforce_threshold: bool = True
    ) -> GILEPrediction:
        """
        Add a new prediction to the vault.
        
        Args:
            prediction_text: What is being predicted
            category: Type of prediction
            gile_score: Overall GILE alignment (0.0-1.0)
            confidence: Confidence level (0.0-1.0)
            verification_deadline: When this can be verified
            verification_criteria: How to verify (measurable)
            gile_breakdown: Optional G, I, L, E individual scores
            metadata: Additional data (stock symbol, etc.)
            enforce_threshold: If True, reject predictions below 0.92
        
        Returns:
            The created prediction
            
        Raises:
            ValueError: If gile_score < 0.92 and enforce_threshold is True
        """
        if enforce_threshold and gile_score < self.TRUE_TRALSENESS_THRESHOLD:
            raise ValueError(
                f"GILE score {gile_score:.3f} below True-Tralseness threshold (0.92). "
                f"Only 0.92+ predictions are stored in the vault. "
                f"Set enforce_threshold=False to override."
            )
        
        if gile_score < self.MODERATE_THRESHOLD:
            print(f"Warning: GILE score {gile_score:.3f} below moderate threshold (0.70)")
        
        prediction = GILEPrediction(
            prediction_id="",
            timestamp_created=datetime.now().isoformat(),
            prediction_text=prediction_text,
            category=category.value,
            gile_score=gile_score,
            confidence=confidence,
            verification_deadline=verification_deadline.isoformat(),
            verification_criteria=verification_criteria,
            gile_breakdown=gile_breakdown or {},
            metadata=metadata or {}
        )
        
        self.predictions.append(prediction)
        self._save_vault()
        
        tier = self._get_threshold_tier(gile_score)
        print(f"Prediction stored: {prediction.prediction_id}")
        print(f"  GILE: {gile_score:.3f} ({tier})")
        print(f"  Verify by: {verification_deadline}")
        
        return prediction
    
    def _get_threshold_tier(self, gile_score: float) -> str:
        """Get the threshold tier for a GILE score."""
        if gile_score >= self.TRUE_TRALSENESS_THRESHOLD:
            return "TRUE-TRALSENESS (0.92+)"
        elif gile_score >= self.CAUSATION_THRESHOLD:
            return "CAUSATION (0.85+)"
        elif gile_score >= self.MODERATE_THRESHOLD:
            return "MODERATE (0.70+)"
        else:
            return "LOW (<0.70)"
    
    def verify_prediction(
        self,
        prediction_id: str,
        outcome: bool,
        outcome_text: str,
        accuracy_score: Optional[float] = None
    ) -> GILEPrediction:
        """
        Verify a prediction after the event occurs.
        
        Args:
            prediction_id: The prediction to verify
            outcome: True if prediction was correct, False otherwise
            outcome_text: Description of what actually happened
            accuracy_score: Optional 0-1 score for partial matches
        
        Returns:
            The updated prediction
        """
        for pred in self.predictions:
            if pred.prediction_id == prediction_id:
                pred.status = (
                    PredictionStatus.VERIFIED_TRUE.value if outcome
                    else PredictionStatus.VERIFIED_FALSE.value
                )
                pred.outcome_text = outcome_text
                pred.verified_at = datetime.now().isoformat()
                pred.accuracy_score = accuracy_score if accuracy_score else (1.0 if outcome else 0.0)
                
                self._save_vault()
                
                tier = self._get_threshold_tier(pred.gile_score)
                status = "CORRECT" if outcome else "INCORRECT"
                print(f"Prediction {prediction_id} verified: {status}")
                print(f"  Original GILE: {pred.gile_score:.3f} ({tier})")
                print(f"  Accuracy: {pred.accuracy_score:.1%}")
                
                return pred
        
        raise ValueError(f"Prediction {prediction_id} not found")
    
    def get_pending_predictions(self) -> List[GILEPrediction]:
        """Get all predictions awaiting verification."""
        now = datetime.now()
        pending = []
        
        for pred in self.predictions:
            if pred.status == PredictionStatus.PENDING.value:
                deadline = datetime.fromisoformat(pred.verification_deadline)
                if deadline > now:
                    pending.append(pred)
                else:
                    pred.status = PredictionStatus.EXPIRED.value
                    self._save_vault()
        
        return pending
    
    def get_overdue_verifications(self) -> List[GILEPrediction]:
        """Get predictions past deadline that need verification."""
        now = datetime.now()
        overdue = []
        
        for pred in self.predictions:
            if pred.status == PredictionStatus.PENDING.value:
                deadline = datetime.fromisoformat(pred.verification_deadline)
                if deadline <= now:
                    overdue.append(pred)
        
        return overdue
    
    def compute_statistics(self) -> VaultStatistics:
        """Compute aggregate statistics for the vault."""
        stats = VaultStatistics()
        stats.total_predictions = len(self.predictions)
        
        gile_sum = 0.0
        category_counts = {}
        threshold_results = {
            "true_tralseness": {"correct": 0, "total": 0},
            "causation": {"correct": 0, "total": 0},
            "moderate": {"correct": 0, "total": 0},
            "low": {"correct": 0, "total": 0}
        }
        
        for pred in self.predictions:
            gile_sum += pred.gile_score
            
            cat = pred.category
            category_counts[cat] = category_counts.get(cat, 0) + 1
            
            if pred.status == PredictionStatus.VERIFIED_TRUE.value:
                stats.verified_true += 1
            elif pred.status == PredictionStatus.VERIFIED_FALSE.value:
                stats.verified_false += 1
            elif pred.status == PredictionStatus.PENDING.value:
                stats.pending += 1
            elif pred.status == PredictionStatus.EXPIRED.value:
                stats.expired += 1
            
            if pred.status in [PredictionStatus.VERIFIED_TRUE.value, 
                               PredictionStatus.VERIFIED_FALSE.value]:
                tier_key = self._get_tier_key(pred.gile_score)
                threshold_results[tier_key]["total"] += 1
                if pred.status == PredictionStatus.VERIFIED_TRUE.value:
                    threshold_results[tier_key]["correct"] += 1
        
        stats.category_breakdown = category_counts
        stats.average_gile_score = gile_sum / max(1, stats.total_predictions)
        
        verified_total = stats.verified_true + stats.verified_false
        if verified_total > 0:
            stats.accuracy_rate = stats.verified_true / verified_total
        
        for tier, results in threshold_results.items():
            if results["total"] > 0:
                results["accuracy"] = results["correct"] / results["total"]
            else:
                results["accuracy"] = None
        stats.threshold_performance = threshold_results
        
        return stats
    
    def _get_tier_key(self, gile_score: float) -> str:
        """Get tier key for statistics."""
        if gile_score >= self.TRUE_TRALSENESS_THRESHOLD:
            return "true_tralseness"
        elif gile_score >= self.CAUSATION_THRESHOLD:
            return "causation"
        elif gile_score >= self.MODERATE_THRESHOLD:
            return "moderate"
        else:
            return "low"
    
    def backtest(
        self,
        min_gile: float = 0.85,
        category: Optional[PredictionCategory] = None
    ) -> Dict:
        """
        Run backtesting analysis on verified predictions.
        
        Args:
            min_gile: Minimum GILE score to include
            category: Optional category filter
        
        Returns:
            Backtesting results with accuracy by threshold
        """
        filtered = []
        for pred in self.predictions:
            if pred.gile_score < min_gile:
                continue
            if category and pred.category != category.value:
                continue
            if pred.status not in [PredictionStatus.VERIFIED_TRUE.value,
                                    PredictionStatus.VERIFIED_FALSE.value]:
                continue
            filtered.append(pred)
        
        if not filtered:
            return {
                "status": "no_data",
                "message": f"No verified predictions with GILE >= {min_gile}"
            }
        
        results = {
            "total_predictions": len(filtered),
            "correct": sum(1 for p in filtered 
                          if p.status == PredictionStatus.VERIFIED_TRUE.value),
            "incorrect": sum(1 for p in filtered 
                            if p.status == PredictionStatus.VERIFIED_FALSE.value),
            "average_gile": sum(p.gile_score for p in filtered) / len(filtered),
            "predictions": []
        }
        
        results["accuracy"] = results["correct"] / results["total_predictions"]
        
        expected_accuracy = min_gile ** 2
        results["expected_accuracy"] = expected_accuracy
        results["performance_vs_expected"] = results["accuracy"] - expected_accuracy
        
        if results["accuracy"] >= expected_accuracy:
            results["validation_status"] = "VALIDATES_TI_FRAMEWORK"
        else:
            results["validation_status"] = "BELOW_EXPECTED"
        
        for pred in sorted(filtered, key=lambda p: p.gile_score, reverse=True):
            results["predictions"].append({
                "id": pred.prediction_id,
                "text": pred.prediction_text[:50] + "...",
                "gile": pred.gile_score,
                "correct": pred.status == PredictionStatus.VERIFIED_TRUE.value
            })
        
        return results
    
    def generate_report(self) -> str:
        """Generate a human-readable vault report."""
        stats = self.compute_statistics()
        
        report = []
        report.append("=" * 60)
        report.append("TRUE-TRALSE VAULT REPORT")
        report.append("GILE Prediction Verification System")
        report.append("=" * 60)
        report.append("")
        
        report.append(f"Total Predictions: {stats.total_predictions}")
        report.append(f"  Verified True:   {stats.verified_true}")
        report.append(f"  Verified False:  {stats.verified_false}")
        report.append(f"  Pending:         {stats.pending}")
        report.append(f"  Expired:         {stats.expired}")
        report.append("")
        
        report.append(f"Overall Accuracy: {stats.accuracy_rate:.1%}")
        report.append(f"Average GILE:     {stats.average_gile_score:.3f}")
        report.append("")
        
        report.append("THRESHOLD PERFORMANCE:")
        report.append("-" * 40)
        for tier, results in stats.threshold_performance.items():
            if results["total"] > 0:
                acc = results["accuracy"]
                expected = self._get_expected_accuracy(tier)
                status = "PASS" if acc >= expected else "FAIL"
                report.append(f"  {tier.upper()}: {acc:.1%} (n={results['total']}) [{status}]")
                report.append(f"    Expected: {expected:.1%}")
        report.append("")
        
        if stats.category_breakdown:
            report.append("CATEGORY BREAKDOWN:")
            report.append("-" * 40)
            for cat, count in sorted(stats.category_breakdown.items()):
                report.append(f"  {cat}: {count}")
        
        report.append("")
        report.append("=" * 60)
        
        return "\n".join(report)
    
    def _get_expected_accuracy(self, tier: str) -> float:
        """Get expected accuracy for a tier based on TI Framework."""
        thresholds = {
            "true_tralseness": 0.92 ** 2,
            "causation": 0.85 ** 2,
            "moderate": 0.70 ** 2,
            "low": 0.50 ** 2
        }
        return thresholds.get(tier, 0.5)


def demo_vault():
    """Demonstrate the True-Tralse Vault."""
    vault = TrueTralseVault("demo_vault.json")
    
    print("=" * 60)
    print("TRUE-TRALSE VAULT DEMO")
    print("=" * 60)
    
    vault.add_prediction(
        prediction_text="AAPL will rise 2%+ within 3 trading days",
        category=PredictionCategory.STOCK_MOVEMENT,
        gile_score=0.94,
        confidence=0.88,
        verification_deadline=datetime.now() + timedelta(days=3),
        verification_criteria="Check AAPL close price vs today's close",
        gile_breakdown={"G": 0.92, "I": 0.95, "L": 0.93, "E": 0.96},
        metadata={"symbol": "AAPL", "current_price": 195.50}
    )
    
    vault.add_prediction(
        prediction_text="Synchronization event will occur during meditation",
        category=PredictionCategory.SYNCHRONIZATION,
        gile_score=0.97,
        confidence=0.92,
        verification_deadline=datetime.now() + timedelta(hours=2),
        verification_criteria="Monitor HRV and EEG for coherence spike",
        gile_breakdown={"G": 0.98, "I": 0.96, "L": 0.97, "E": 0.97}
    )
    
    vault.add_prediction(
        prediction_text="Mood will shift from 6/10 to 8+/10 after supplement",
        category=PredictionCategory.MOOD_SHIFT,
        gile_score=0.93,
        confidence=0.85,
        verification_deadline=datetime.now() + timedelta(hours=4),
        verification_criteria="Self-reported mood rating 4 hours post-dose",
        gile_breakdown={"G": 0.94, "I": 0.91, "L": 0.95, "E": 0.92}
    )
    
    print("\n" + vault.generate_report())
    
    pending = vault.get_pending_predictions()
    print(f"\nPending verifications: {len(pending)}")
    for p in pending:
        print(f"  {p.prediction_id}: {p.prediction_text[:40]}...")
    
    print("\n[Simulating verification...]")
    if len(vault.predictions) >= 2:
        vault.verify_prediction(
            vault.predictions[0].prediction_id,
            outcome=True,
            outcome_text="AAPL rose 2.3% in 2 days",
            accuracy_score=1.0
        )
        vault.verify_prediction(
            vault.predictions[1].prediction_id,
            outcome=True,
            outcome_text="HRV coherence reached 0.94 during session",
            accuracy_score=0.95
        )
    
    print("\n" + vault.generate_report())
    
    print("\nBACKTEST (GILE >= 0.90):")
    print("-" * 40)
    backtest = vault.backtest(min_gile=0.90)
    if backtest.get("status") != "no_data":
        print(f"Accuracy: {backtest['accuracy']:.1%}")
        print(f"Expected: {backtest['expected_accuracy']:.1%}")
        print(f"Status: {backtest['validation_status']}")
    else:
        print(backtest["message"])
    
    if os.path.exists("demo_vault.json"):
        os.remove("demo_vault.json")


if __name__ == "__main__":
    demo_vault()
