"""
MEDGEMMA IMPACT CHALLENGE ENGINE
====================================
GILE-Enhanced Clinical Decision Support System for the Google Research
MedGemma Impact Challenge (Kaggle Hackathon, deadline Feb 24, 2026).

Builds human-centered healthcare AI using MedGemma models with
rule-based fallback for offline/edge deployment scenarios.

GILE HEALTH MAPPING:
    G (Goodness): Treatment efficacy, positive outcomes probability
    I (Intuition): Clinical pattern recognition confidence, differential diagnosis insight
    L (Love): Patient care quality, empathy metrics, holistic consideration
    E (Existence): Physiological state, vital signs stability, biomarker evidence

TRALSE CONFIDENCE SCORING:
    True  (>0.85): High confidence diagnosis/recommendation
    Tralse (0.40-0.85): Requires additional testing/specialist review
    False (<0.40): Insufficient evidence, flag for escalation

RISK STRATIFICATION:
    - Cardiovascular (Framingham-based + GILE enhancement)
    - Diabetes (Finnish Diabetes Risk Score + metabolic GILE)
    - Mental Health (PHQ-9/GAD-7 mapped to GILE dimensions)
    - Respiratory risk assessment

OFFLINE/EDGE FEATURES:
    - Lightweight scoring without model inference
    - Cached clinical guidelines for common conditions
    - Local decision trees for triage

ARCHITECTURE:
    1. GILEHealthAssessor - Core clinical assessment engine
    2. MedGemmaInterface - Prompt formatting and response parsing for MedGemma
    3. RiskStratificationEngine - Multi-disease risk prediction
    4. OfflineClinicalGuidelines - Cached guidelines for edge deployment
    5. TralseConfidenceScorer - Medical decision confidence framework
"""

import json
import math
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple, Any, Union
from dataclasses import dataclass, field, asdict


ESI_LEVELS = {
    1: {"label": "Resuscitation", "description": "Immediate life-saving intervention required",
        "max_wait_minutes": 0, "resources": "full_team"},
    2: {"label": "Emergent", "description": "High risk of deterioration, severe pain/distress",
        "max_wait_minutes": 10, "resources": "multiple"},
    3: {"label": "Urgent", "description": "Stable but requires multiple resources",
        "max_wait_minutes": 30, "resources": "multiple"},
    4: {"label": "Less Urgent", "description": "Stable, requires one resource",
        "max_wait_minutes": 60, "resources": "single"},
    5: {"label": "Non-Urgent", "description": "Stable, no resources anticipated",
        "max_wait_minutes": 120, "resources": "none"},
}

CRITICAL_SYMPTOMS = {
    "chest_pain", "severe_bleeding", "difficulty_breathing", "stroke_symptoms",
    "unconsciousness", "anaphylaxis", "seizure", "cardiac_arrest",
    "severe_trauma", "acute_psychosis", "sepsis_signs",
}

HIGH_PRIORITY_SYMPTOMS = {
    "high_fever", "abdominal_pain_severe", "headache_worst_ever",
    "vision_loss_sudden", "limb_weakness", "confusion", "hematemesis",
    "chest_tightness", "syncope", "severe_dehydration",
}

VITAL_SIGN_RANGES = {
    "heart_rate": {"critical_low": 40, "low": 60, "normal_low": 60, "normal_high": 100,
                   "high": 100, "critical_high": 150, "unit": "bpm"},
    "systolic_bp": {"critical_low": 70, "low": 90, "normal_low": 90, "normal_high": 140,
                    "high": 140, "critical_high": 180, "unit": "mmHg"},
    "diastolic_bp": {"critical_low": 40, "low": 60, "normal_low": 60, "normal_high": 90,
                     "high": 90, "critical_high": 120, "unit": "mmHg"},
    "respiratory_rate": {"critical_low": 8, "low": 12, "normal_low": 12, "normal_high": 20,
                         "high": 20, "critical_high": 30, "unit": "breaths/min"},
    "temperature": {"critical_low": 35.0, "low": 36.1, "normal_low": 36.1, "normal_high": 37.2,
                    "high": 38.0, "critical_high": 40.0, "unit": "°C"},
    "spo2": {"critical_low": 88, "low": 92, "normal_low": 95, "normal_high": 100,
             "high": 100, "critical_high": 100, "unit": "%"},
    "blood_glucose": {"critical_low": 40, "low": 70, "normal_low": 70, "normal_high": 140,
                      "high": 200, "critical_high": 400, "unit": "mg/dL"},
}


@dataclass
class GILEHealthScore:
    goodness: float = 0.5
    intuition: float = 0.5
    love: float = 0.5
    existence: float = 0.5

    @property
    def composite(self) -> float:
        return (self.goodness * 0.25 + self.intuition * 0.25 +
                self.love * 0.20 + self.existence * 0.30)

    @property
    def tralse_label(self) -> str:
        c = self.composite
        if c > 0.85:
            return "True"
        elif c >= 0.40:
            return "Tralse"
        else:
            return "False"

    def to_dict(self) -> Dict:
        return {
            "G": round(self.goodness, 3),
            "I": round(self.intuition, 3),
            "L": round(self.love, 3),
            "E": round(self.existence, 3),
            "composite": round(self.composite, 3),
            "tralse_label": self.tralse_label,
        }


@dataclass
class PatientProfile:
    age: int = 0
    sex: str = "unknown"
    weight_kg: float = 0.0
    height_cm: float = 0.0
    smoking_status: str = "unknown"
    medical_history: List[str] = field(default_factory=list)
    current_medications: List[str] = field(default_factory=list)
    allergies: List[str] = field(default_factory=list)
    family_history: List[str] = field(default_factory=list)

    @property
    def bmi(self) -> float:
        if self.height_cm > 0 and self.weight_kg > 0:
            height_m = self.height_cm / 100.0
            return round(self.weight_kg / (height_m ** 2), 1)
        return 0.0


class TralseConfidenceScorer:
    """Tralse confidence scoring for medical decisions.

    Maps clinical evidence strength to a three-tier confidence system:
        True (>0.85): High confidence - proceed with recommendation
        Tralse (0.40-0.85): Moderate confidence - additional testing/specialist review
        False (<0.40): Low confidence - insufficient evidence, escalate
    """

    @staticmethod
    def score(evidence_factors: Dict[str, float], weights: Optional[Dict[str, float]] = None) -> Dict:
        if not evidence_factors:
            return {"confidence": 0.0, "label": "False", "action": "escalate",
                    "factors": {}, "recommendation": "Insufficient data for assessment"}

        if weights is None:
            weights = {k: 1.0 / len(evidence_factors) for k in evidence_factors}

        total_weight = sum(weights.get(k, 0) for k in evidence_factors)
        if total_weight == 0:
            total_weight = 1.0

        weighted_sum = sum(evidence_factors[k] * weights.get(k, 0) for k in evidence_factors)
        confidence = weighted_sum / total_weight

        confidence = max(0.0, min(1.0, confidence))

        if confidence > 0.85:
            label, action = "True", "proceed"
            recommendation = "High confidence assessment. Proceed with clinical pathway."
        elif confidence >= 0.40:
            label, action = "Tralse", "review"
            recommendation = "Moderate confidence. Recommend additional testing or specialist consultation."
        else:
            label, action = "False", "escalate"
            recommendation = "Low confidence. Escalate to senior clinician for review."

        return {
            "confidence": round(confidence, 3),
            "label": label,
            "action": action,
            "factors": {k: round(v, 3) for k, v in evidence_factors.items()},
            "recommendation": recommendation,
        }

    @staticmethod
    def aggregate_scores(scores: List[Dict]) -> Dict:
        if not scores:
            return {"overall_confidence": 0.0, "label": "False", "weakest_factor": None}

        confidences = [s.get("confidence", 0) for s in scores]
        overall = float(np.mean(confidences))
        minimum = min(confidences)

        weakest_idx = confidences.index(minimum)

        if minimum < 0.40:
            label = "False"
        elif overall > 0.85 and minimum > 0.60:
            label = "True"
        else:
            label = "Tralse"

        return {
            "overall_confidence": round(overall, 3),
            "minimum_confidence": round(minimum, 3),
            "label": label,
            "weakest_factor_index": weakest_idx,
            "n_assessments": len(scores),
        }


class OfflineClinicalGuidelines:
    """Cached clinical guidelines for offline/edge deployment.

    Provides rule-based clinical decision support without requiring
    model inference, suitable for resource-constrained environments.
    """

    CONDITION_GUIDELINES = {
        "hypertension": {
            "criteria": {"systolic_bp": 140, "diastolic_bp": 90},
            "staging": {
                "stage_1": {"systolic": (130, 139), "diastolic": (80, 89)},
                "stage_2": {"systolic": (140, 179), "diastolic": (90, 119)},
                "crisis": {"systolic": (180, 999), "diastolic": (120, 999)},
            },
            "interventions": [
                "Lifestyle modifications (DASH diet, exercise, sodium restriction)",
                "Weight management if BMI > 25",
                "Regular blood pressure monitoring",
                "Consider ACE inhibitor or ARB if stage 2 or high risk",
            ],
            "follow_up_days": 30,
        },
        "diabetes_type2": {
            "criteria": {"fasting_glucose": 126, "hba1c": 6.5, "random_glucose": 200},
            "staging": {
                "prediabetes": {"hba1c": (5.7, 6.4), "fasting_glucose": (100, 125)},
                "controlled": {"hba1c": (6.5, 7.0)},
                "uncontrolled": {"hba1c": (7.0, 9.0)},
                "severe": {"hba1c": (9.0, 99.0)},
            },
            "interventions": [
                "Dietary counseling and carbohydrate management",
                "Regular physical activity (150 min/week moderate intensity)",
                "Blood glucose self-monitoring education",
                "Metformin initiation if HbA1c >= 6.5%",
                "Regular HbA1c monitoring every 3 months",
            ],
            "follow_up_days": 90,
        },
        "acute_coronary_syndrome": {
            "criteria": {"chest_pain": True, "troponin_elevated": True},
            "red_flags": ["ST elevation on ECG", "hemodynamic instability",
                         "ongoing chest pain >20 min", "diaphoresis"],
            "interventions": [
                "Immediate 12-lead ECG",
                "Aspirin 325mg unless contraindicated",
                "Establish IV access",
                "Continuous cardiac monitoring",
                "Cardiology consultation",
            ],
            "follow_up_days": 7,
        },
        "asthma_exacerbation": {
            "criteria": {"wheezing": True, "dyspnea": True, "peak_flow_reduced": True},
            "severity": {
                "mild": {"peak_flow_pct": (70, 100), "spo2": (95, 100)},
                "moderate": {"peak_flow_pct": (40, 69), "spo2": (91, 94)},
                "severe": {"peak_flow_pct": (0, 39), "spo2": (0, 90)},
            },
            "interventions": [
                "Short-acting bronchodilator (albuterol) via nebulizer or MDI",
                "Systemic corticosteroids if moderate-severe",
                "Supplemental oxygen to maintain SpO2 > 94%",
                "Reassess after initial treatment",
                "Asthma action plan review",
            ],
            "follow_up_days": 14,
        },
        "major_depressive_disorder": {
            "criteria": {"phq9_score": 10, "duration_weeks": 2},
            "severity": {
                "mild": {"phq9": (5, 9)},
                "moderate": {"phq9": (10, 14)},
                "moderately_severe": {"phq9": (15, 19)},
                "severe": {"phq9": (20, 27)},
            },
            "interventions": [
                "Psychotherapy referral (CBT or IPT)",
                "Assess suicide risk (PHQ-9 item 9)",
                "Consider SSRI if moderate or higher severity",
                "Sleep hygiene counseling",
                "Regular follow-up and PHQ-9 reassessment",
                "Social support network assessment",
            ],
            "follow_up_days": 14,
        },
        "community_acquired_pneumonia": {
            "criteria": {"cough": True, "fever": True, "consolidation": True},
            "severity_markers": ["confusion", "respiratory_rate_>30", "low_bp",
                                "age_>65", "multilobar"],
            "interventions": [
                "Chest X-ray if not already obtained",
                "Sputum culture if productive cough",
                "Empiric antibiotic therapy per guidelines",
                "Assess CURB-65 score for disposition",
                "Hydration and supportive care",
            ],
            "follow_up_days": 7,
        },
    }

    TRIAGE_DECISION_TREE = {
        "unresponsive": {"esi": 1, "action": "immediate_resuscitation"},
        "severe_respiratory_distress": {"esi": 1, "action": "immediate_airway_management"},
        "active_hemorrhage": {"esi": 1, "action": "immediate_hemorrhage_control"},
        "chest_pain_with_ecg_changes": {"esi": 2, "action": "cardiac_protocol"},
        "stroke_symptoms_acute": {"esi": 2, "action": "stroke_protocol"},
        "high_fever_immunocompromised": {"esi": 2, "action": "sepsis_protocol"},
        "abdominal_pain_peritoneal": {"esi": 2, "action": "surgical_consult"},
        "fracture_open": {"esi": 2, "action": "orthopedic_emergency"},
        "moderate_pain_stable": {"esi": 3, "action": "standard_workup"},
        "laceration_simple": {"esi": 4, "action": "wound_care"},
        "prescription_refill": {"esi": 5, "action": "routine_care"},
        "minor_complaint_stable": {"esi": 5, "action": "routine_assessment"},
    }

    @classmethod
    def get_guideline(cls, condition: str) -> Optional[Dict]:
        return cls.CONDITION_GUIDELINES.get(condition)

    @classmethod
    def triage_lookup(cls, presentation: str) -> Optional[Dict]:
        return cls.TRIAGE_DECISION_TREE.get(presentation)

    @classmethod
    def get_all_conditions(cls) -> List[str]:
        return list(cls.CONDITION_GUIDELINES.keys())


class RiskStratificationEngine:
    """Multi-disease risk prediction with GILE enhancement.

    Implements validated clinical risk scores augmented with
    GILE framework scoring for holistic risk assessment.
    """

    @staticmethod
    def cardiovascular_risk(patient: Dict) -> Dict:
        """Framingham-based cardiovascular risk with GILE enhancement."""
        age = patient.get("age", 50)
        sex = patient.get("sex", "male")
        systolic_bp = patient.get("systolic_bp", 120)
        total_cholesterol = patient.get("total_cholesterol", 200)
        hdl_cholesterol = patient.get("hdl_cholesterol", 50)
        smoking = patient.get("smoking_status", "never") in ("current", "active")
        diabetes = "diabetes" in patient.get("medical_history", [])
        bp_treated = patient.get("bp_treated", False)

        points = 0

        if sex == "male":
            if age < 35: points += -9
            elif age < 40: points += -4
            elif age < 45: points += 0
            elif age < 50: points += 3
            elif age < 55: points += 6
            elif age < 60: points += 8
            elif age < 65: points += 10
            elif age < 70: points += 11
            elif age < 75: points += 12
            else: points += 13
        else:
            if age < 35: points += -7
            elif age < 40: points += -3
            elif age < 45: points += 0
            elif age < 50: points += 3
            elif age < 55: points += 6
            elif age < 60: points += 8
            elif age < 65: points += 10
            elif age < 70: points += 12
            elif age < 75: points += 14
            else: points += 16

        if total_cholesterol < 160: points += 0
        elif total_cholesterol < 200: points += 1
        elif total_cholesterol < 240: points += 2
        elif total_cholesterol < 280: points += 3
        else: points += 4

        if hdl_cholesterol >= 60: points -= 1
        elif hdl_cholesterol >= 50: points += 0
        elif hdl_cholesterol >= 40: points += 1
        else: points += 2

        if bp_treated:
            if systolic_bp < 120: points += 0
            elif systolic_bp < 130: points += 1
            elif systolic_bp < 140: points += 2
            elif systolic_bp < 160: points += 3
            else: points += 4
        else:
            if systolic_bp < 120: points += 0
            elif systolic_bp < 130: points += 0
            elif systolic_bp < 140: points += 1
            elif systolic_bp < 160: points += 1
            else: points += 2

        if smoking: points += 2
        if diabetes: points += 2

        risk_pct = min(30.0, max(1.0, points * 1.2))

        if risk_pct < 5:
            category = "low"
        elif risk_pct < 10:
            category = "borderline"
        elif risk_pct < 20:
            category = "intermediate"
        else:
            category = "high"

        gile = GILEHealthScore(
            goodness=max(0, min(1, 1.0 - risk_pct / 30.0)),
            intuition=0.75 if total_cholesterol > 0 and hdl_cholesterol > 0 else 0.4,
            love=0.8 if not smoking else 0.5,
            existence=max(0, min(1, 1.0 - abs(systolic_bp - 120) / 60.0)),
        )

        evidence = {
            "age_data": 0.9 if age > 0 else 0.3,
            "lipid_panel": 0.85 if total_cholesterol > 0 else 0.2,
            "blood_pressure": 0.9 if systolic_bp > 0 else 0.2,
            "smoking_history": 0.8,
            "diabetes_status": 0.8 if diabetes else 0.7,
        }
        tralse = TralseConfidenceScorer.score(evidence)

        return {
            "risk_type": "cardiovascular",
            "framingham_points": points,
            "ten_year_risk_pct": round(risk_pct, 1),
            "risk_category": category,
            "gile_score": gile.to_dict(),
            "tralse_confidence": tralse,
            "modifiable_factors": [
                f for f in [
                    "smoking_cessation" if smoking else None,
                    "lipid_management" if total_cholesterol > 200 else None,
                    "blood_pressure_control" if systolic_bp > 130 else None,
                    "glucose_management" if diabetes else None,
                    "weight_management" if patient.get("bmi", 0) > 25 else None,
                ] if f is not None
            ],
        }

    @staticmethod
    def diabetes_risk(patient: Dict) -> Dict:
        """Finnish Diabetes Risk Score (FINDRISC) with metabolic GILE."""
        age = patient.get("age", 45)
        bmi = patient.get("bmi", 25)
        waist_cm = patient.get("waist_circumference", 0)
        sex = patient.get("sex", "unknown")
        physical_activity = patient.get("physical_activity_daily", True)
        vegetables_daily = patient.get("vegetables_daily", True)
        bp_medication = patient.get("bp_medication", False)
        high_glucose_history = patient.get("high_glucose_history", False)
        family_diabetes = patient.get("family_diabetes", "none")
        fasting_glucose = patient.get("fasting_glucose", 90)
        hba1c = patient.get("hba1c", 5.4)

        score = 0

        if age < 45: score += 0
        elif age < 55: score += 2
        elif age < 65: score += 3
        else: score += 4

        if bmi < 25: score += 0
        elif bmi < 30: score += 1
        else: score += 3

        if waist_cm > 0:
            if sex == "male":
                if waist_cm < 94: score += 0
                elif waist_cm < 102: score += 3
                else: score += 4
            else:
                if waist_cm < 80: score += 0
                elif waist_cm < 88: score += 3
                else: score += 4

        if not physical_activity: score += 2
        if not vegetables_daily: score += 1
        if bp_medication: score += 2
        if high_glucose_history: score += 5

        if family_diabetes == "parent_or_sibling": score += 5
        elif family_diabetes == "grandparent_or_cousin": score += 3

        if score < 7: risk_level = "low"
        elif score < 12: risk_level = "slightly_elevated"
        elif score < 15: risk_level = "moderate"
        elif score < 21: risk_level = "high"
        else: risk_level = "very_high"

        metabolic_flags = []
        if fasting_glucose >= 100: metabolic_flags.append("impaired_fasting_glucose")
        if hba1c >= 5.7: metabolic_flags.append("prediabetic_hba1c")
        if bmi >= 30: metabolic_flags.append("obesity")
        if waist_cm > 0:
            threshold = 102 if sex == "male" else 88
            if waist_cm > threshold:
                metabolic_flags.append("central_obesity")

        gile = GILEHealthScore(
            goodness=max(0, min(1, 1.0 - score / 26.0)),
            intuition=0.8 if fasting_glucose > 0 and hba1c > 0 else 0.5,
            love=0.85 if physical_activity and vegetables_daily else 0.5,
            existence=max(0, min(1, 1.0 - len(metabolic_flags) / 4.0)),
        )

        evidence = {
            "anthropometric": 0.9 if bmi > 0 else 0.3,
            "glucose_data": 0.9 if fasting_glucose > 0 else 0.2,
            "lifestyle_data": 0.7,
            "family_history": 0.8 if family_diabetes != "none" else 0.5,
        }
        tralse = TralseConfidenceScorer.score(evidence)

        return {
            "risk_type": "diabetes",
            "findrisc_score": score,
            "risk_level": risk_level,
            "metabolic_flags": metabolic_flags,
            "gile_score": gile.to_dict(),
            "tralse_confidence": tralse,
            "interventions": [
                f for f in [
                    "dietary_modification" if not vegetables_daily or bmi > 25 else None,
                    "increase_physical_activity" if not physical_activity else None,
                    "weight_reduction_program" if bmi >= 30 else None,
                    "glucose_monitoring" if fasting_glucose >= 100 else None,
                    "hba1c_recheck_3months" if hba1c >= 5.7 else None,
                ] if f is not None
            ],
        }

    @staticmethod
    def mental_health_screening(patient: Dict) -> Dict:
        """PHQ-9/GAD-7 screening mapped to GILE dimensions."""
        phq9_score = patient.get("phq9_score", 0)
        gad7_score = patient.get("gad7_score", 0)
        sleep_quality = patient.get("sleep_quality", 5)
        social_support = patient.get("social_support_score", 5)
        functional_impairment = patient.get("functional_impairment", 0)
        substance_use = patient.get("substance_use", "none")
        suicidal_ideation = patient.get("suicidal_ideation", False)

        if phq9_score < 5: depression_severity = "minimal"
        elif phq9_score < 10: depression_severity = "mild"
        elif phq9_score < 15: depression_severity = "moderate"
        elif phq9_score < 20: depression_severity = "moderately_severe"
        else: depression_severity = "severe"

        if gad7_score < 5: anxiety_severity = "minimal"
        elif gad7_score < 10: anxiety_severity = "mild"
        elif gad7_score < 15: anxiety_severity = "moderate"
        else: anxiety_severity = "severe"

        combined_burden = (phq9_score / 27.0 + gad7_score / 21.0) / 2.0

        gile = GILEHealthScore(
            goodness=max(0, min(1, 1.0 - combined_burden)),
            intuition=0.7 if phq9_score > 0 and gad7_score > 0 else 0.4,
            love=max(0.1, min(1, social_support / 10.0)),
            existence=max(0.1, min(1, sleep_quality / 10.0 * (1 - functional_impairment / 10.0))),
        )

        urgent_flags = []
        if suicidal_ideation: urgent_flags.append("SUICIDE_RISK_PRESENT")
        if phq9_score >= 20: urgent_flags.append("SEVERE_DEPRESSION")
        if gad7_score >= 15: urgent_flags.append("SEVERE_ANXIETY")
        if substance_use not in ("none", "minimal"): urgent_flags.append("SUBSTANCE_USE_CONCERN")

        evidence = {
            "phq9_completed": 0.9 if phq9_score > 0 else 0.2,
            "gad7_completed": 0.9 if gad7_score > 0 else 0.2,
            "functional_assessment": 0.7 if functional_impairment > 0 else 0.4,
            "social_context": 0.8 if social_support > 0 else 0.3,
        }
        tralse = TralseConfidenceScorer.score(evidence)

        return {
            "risk_type": "mental_health",
            "phq9_score": phq9_score,
            "depression_severity": depression_severity,
            "gad7_score": gad7_score,
            "anxiety_severity": anxiety_severity,
            "combined_burden": round(combined_burden, 3),
            "urgent_flags": urgent_flags,
            "gile_score": gile.to_dict(),
            "tralse_confidence": tralse,
            "recommended_actions": [
                f for f in [
                    "immediate_safety_assessment" if suicidal_ideation else None,
                    "psychiatry_referral" if phq9_score >= 15 or gad7_score >= 15 else None,
                    "psychotherapy_referral" if phq9_score >= 10 or gad7_score >= 10 else None,
                    "medication_evaluation" if phq9_score >= 15 else None,
                    "sleep_hygiene_counseling" if sleep_quality < 5 else None,
                    "substance_use_screening" if substance_use not in ("none", "minimal") else None,
                    "social_support_intervention" if social_support < 3 else None,
                    "follow_up_2_weeks" if phq9_score >= 10 else "follow_up_4_weeks",
                ] if f is not None
            ],
        }

    @staticmethod
    def respiratory_risk(patient: Dict) -> Dict:
        """Respiratory risk assessment with GILE scoring."""
        age = patient.get("age", 50)
        smoking_pack_years = patient.get("smoking_pack_years", 0)
        fev1_predicted_pct = patient.get("fev1_predicted_pct", 100)
        fev1_fvc_ratio = patient.get("fev1_fvc_ratio", 0.80)
        spo2 = patient.get("spo2", 97)
        dyspnea_score = patient.get("dyspnea_mrc_score", 0)
        exacerbation_history = patient.get("exacerbations_last_year", 0)
        respiratory_history = patient.get("respiratory_history", [])

        risk_score = 0
        if smoking_pack_years > 20: risk_score += 3
        elif smoking_pack_years > 10: risk_score += 2
        elif smoking_pack_years > 0: risk_score += 1

        if fev1_predicted_pct < 30: risk_score += 4
        elif fev1_predicted_pct < 50: risk_score += 3
        elif fev1_predicted_pct < 80: risk_score += 2

        if fev1_fvc_ratio < 0.70: risk_score += 2
        if spo2 < 92: risk_score += 3
        elif spo2 < 95: risk_score += 1
        if dyspnea_score >= 3: risk_score += 2
        if exacerbation_history >= 2: risk_score += 2

        if risk_score <= 2: risk_level = "low"
        elif risk_score <= 5: risk_level = "moderate"
        elif risk_score <= 8: risk_level = "high"
        else: risk_level = "very_high"

        copd_suspected = fev1_fvc_ratio < 0.70 and smoking_pack_years > 10

        gile = GILEHealthScore(
            goodness=max(0, min(1, fev1_predicted_pct / 100.0)),
            intuition=0.8 if fev1_predicted_pct > 0 else 0.4,
            love=max(0, min(1, 1.0 - smoking_pack_years / 40.0)),
            existence=max(0, min(1, spo2 / 100.0)),
        )

        evidence = {
            "spirometry_data": 0.9 if fev1_predicted_pct < 100 else 0.3,
            "smoking_history": 0.85,
            "pulse_oximetry": 0.9 if spo2 > 0 else 0.2,
            "symptom_assessment": 0.7 if dyspnea_score > 0 else 0.4,
        }
        tralse = TralseConfidenceScorer.score(evidence)

        return {
            "risk_type": "respiratory",
            "risk_score": risk_score,
            "risk_level": risk_level,
            "copd_suspected": copd_suspected,
            "gold_stage": (
                "IV" if fev1_predicted_pct < 30 else
                "III" if fev1_predicted_pct < 50 else
                "II" if fev1_predicted_pct < 80 else "I"
            ) if copd_suspected else None,
            "gile_score": gile.to_dict(),
            "tralse_confidence": tralse,
            "interventions": [
                f for f in [
                    "smoking_cessation" if smoking_pack_years > 0 else None,
                    "pulmonary_rehabilitation" if fev1_predicted_pct < 80 else None,
                    "bronchodilator_therapy" if copd_suspected else None,
                    "supplemental_oxygen" if spo2 < 88 else None,
                    "influenza_pneumococcal_vaccination",
                    "spirometry_followup" if fev1_fvc_ratio < 0.75 else None,
                ] if f is not None
            ],
        }


class GILEHealthAssessor:
    """Core clinical assessment engine with GILE framework integration.

    Provides comprehensive patient assessment, triage, risk prediction,
    and intervention recommendations using the GILE health mapping:
        G (Goodness): Treatment efficacy, positive outcomes probability
        I (Intuition): Clinical pattern recognition confidence
        L (Love): Patient care quality, empathy metrics
        E (Existence): Physiological state, vital signs stability
    """

    def __init__(self):
        self.risk_engine = RiskStratificationEngine()
        self.guidelines = OfflineClinicalGuidelines()
        self.tralse_scorer = TralseConfidenceScorer()
        self._assessment_history: List[Dict] = []

    def assess_patient(self, patient_data: Dict) -> Dict:
        """Comprehensive patient assessment with GILE-scored health evaluation.

        Args:
            patient_data: Dictionary containing demographics, symptoms, vitals,
                         lab results, and medical history.

        Returns:
            GILE-scored health assessment with risk stratification, confidence
            scoring, and recommended next steps.
        """
        demographics = patient_data.get("demographics", {})
        symptoms = patient_data.get("symptoms", [])
        vitals = patient_data.get("vitals", {})
        labs = patient_data.get("lab_results", {})
        history = patient_data.get("medical_history", [])

        profile = PatientProfile(
            age=demographics.get("age", 0),
            sex=demographics.get("sex", "unknown"),
            weight_kg=demographics.get("weight_kg", 0),
            height_cm=demographics.get("height_cm", 0),
            smoking_status=demographics.get("smoking_status", "unknown"),
            medical_history=history,
            current_medications=patient_data.get("medications", []),
            allergies=patient_data.get("allergies", []),
            family_history=patient_data.get("family_history", []),
        )

        vitals_assessment = self._assess_vitals(vitals)
        symptom_analysis = self._analyze_symptoms(symptoms, vitals)
        lab_analysis = self._analyze_labs(labs)

        gile = self._compute_patient_gile(
            vitals_assessment, symptom_analysis, lab_analysis, profile
        )

        risk_predictions = self.predict_risk_factors({
            **demographics,
            "medical_history": history,
            "bmi": profile.bmi,
            **vitals,
            **labs,
        })

        evidence = {
            "vitals_completeness": vitals_assessment.get("completeness", 0),
            "symptom_clarity": symptom_analysis.get("clarity_score", 0.5),
            "lab_data_available": min(1.0, len(labs) / 5.0),
            "history_depth": min(1.0, (len(history) + len(patient_data.get("medications", []))) / 8.0),
            "demographic_data": 0.9 if profile.age > 0 else 0.3,
        }
        confidence = self.tralse_scorer.score(evidence)

        acuity = "stable"
        if vitals_assessment.get("critical_flags"):
            acuity = "critical"
        elif vitals_assessment.get("abnormal_count", 0) >= 3:
            acuity = "acute"
        elif symptom_analysis.get("severity", "low") in ("high", "critical"):
            acuity = "acute"

        assessment = {
            "timestamp": datetime.utcnow().isoformat(),
            "patient_profile": {
                "age": profile.age,
                "sex": profile.sex,
                "bmi": profile.bmi,
            },
            "gile_score": gile.to_dict(),
            "tralse_confidence": confidence,
            "acuity": acuity,
            "vitals_assessment": vitals_assessment,
            "symptom_analysis": symptom_analysis,
            "lab_analysis": lab_analysis,
            "risk_predictions": risk_predictions,
            "recommended_actions": self._generate_actions(
                acuity, vitals_assessment, symptom_analysis, gile
            ),
        }

        self._assessment_history.append({
            "timestamp": assessment["timestamp"],
            "gile_composite": gile.composite,
            "acuity": acuity,
        })

        return assessment

    def triage_patient(self, symptoms: List[str], vitals: Dict) -> Dict:
        """Emergency triage using GILE framework mapped to ESI levels 1-5.

        Args:
            symptoms: List of presenting symptoms.
            vitals: Dictionary of vital sign measurements.

        Returns:
            Triage result with ESI level, urgency, and recommended actions.
        """
        critical_present = [s for s in symptoms if s in CRITICAL_SYMPTOMS]
        high_priority = [s for s in symptoms if s in HIGH_PRIORITY_SYMPTOMS]

        vitals_stability = self._assess_vitals_stability(vitals)

        if critical_present or vitals_stability["critical"]:
            esi_level = 1
        elif len(critical_present) == 0 and (high_priority or vitals_stability["abnormal"]):
            if vitals_stability.get("unstable", False):
                esi_level = 2
            elif len(high_priority) >= 2:
                esi_level = 2
            else:
                esi_level = 3
        elif len(symptoms) > 0:
            resource_estimate = self._estimate_resources(symptoms)
            if resource_estimate >= 2:
                esi_level = 3
            elif resource_estimate == 1:
                esi_level = 4
            else:
                esi_level = 5
        else:
            esi_level = 5

        gile = GILEHealthScore(
            goodness=max(0, min(1, 1.0 - (5 - esi_level) / 4.0)),
            intuition=0.8 if len(symptoms) > 0 else 0.4,
            love=0.9,
            existence=vitals_stability.get("stability_score", 0.5),
        )

        evidence = {
            "symptom_assessment": 0.8 if symptoms else 0.3,
            "vitals_available": 0.9 if vitals else 0.2,
            "critical_screening": 0.95,
        }
        confidence = self.tralse_scorer.score(evidence)

        esi_info = ESI_LEVELS.get(esi_level, {})

        return {
            "esi_level": esi_level,
            "esi_label": esi_info.get("label", "Unknown"),
            "esi_description": esi_info.get("description", ""),
            "max_wait_minutes": esi_info.get("max_wait_minutes", 120),
            "critical_symptoms": critical_present,
            "high_priority_symptoms": high_priority,
            "vitals_stability": vitals_stability,
            "gile_score": gile.to_dict(),
            "tralse_confidence": confidence,
            "recommended_actions": self._triage_actions(esi_level, critical_present, vitals_stability),
            "disposition_recommendation": (
                "immediate_resuscitation" if esi_level == 1 else
                "emergent_evaluation" if esi_level == 2 else
                "urgent_evaluation" if esi_level == 3 else
                "standard_evaluation" if esi_level == 4 else
                "routine_care"
            ),
        }

    def generate_clinical_summary(self, patient_data: Dict, assessment: Dict) -> str:
        """Creates a structured clinical note from patient data and assessment.

        Args:
            patient_data: Raw patient data dictionary.
            assessment: Assessment result from assess_patient().

        Returns:
            Formatted clinical note string.
        """
        demographics = patient_data.get("demographics", {})
        symptoms = patient_data.get("symptoms", [])
        vitals = patient_data.get("vitals", {})
        labs = patient_data.get("lab_results", {})
        medications = patient_data.get("medications", [])
        history = patient_data.get("medical_history", [])

        gile = assessment.get("gile_score", {})
        confidence = assessment.get("tralse_confidence", {})
        acuity = assessment.get("acuity", "unknown")

        lines = [
            "=" * 60,
            "CLINICAL DECISION SUPPORT SUMMARY",
            f"Generated: {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}",
            f"Assessment Engine: GILE-Enhanced MedGemma v1.0",
            "=" * 60,
            "",
            "PATIENT DEMOGRAPHICS:",
            f"  Age: {demographics.get('age', 'N/A')} | Sex: {demographics.get('sex', 'N/A')}",
            f"  BMI: {assessment.get('patient_profile', {}).get('bmi', 'N/A')}",
            "",
            "CHIEF COMPLAINT / PRESENTING SYMPTOMS:",
        ]

        if symptoms:
            for s in symptoms:
                lines.append(f"  - {s.replace('_', ' ').title()}")
        else:
            lines.append("  No symptoms reported")

        lines.extend(["", "VITAL SIGNS:"])
        if vitals:
            for k, v in vitals.items():
                unit = VITAL_SIGN_RANGES.get(k, {}).get("unit", "")
                lines.append(f"  {k.replace('_', ' ').title()}: {v} {unit}")
        else:
            lines.append("  No vital signs recorded")

        lines.extend(["", "LABORATORY RESULTS:"])
        if labs:
            for k, v in labs.items():
                lines.append(f"  {k.replace('_', ' ').title()}: {v}")
        else:
            lines.append("  No laboratory data available")

        lines.extend(["", "MEDICAL HISTORY:"])
        if history:
            for h in history:
                lines.append(f"  - {h}")
        else:
            lines.append("  No significant history reported")

        lines.extend(["", "CURRENT MEDICATIONS:"])
        if medications:
            for m in medications:
                lines.append(f"  - {m}")
        else:
            lines.append("  None reported")

        lines.extend([
            "",
            "-" * 60,
            "GILE HEALTH ASSESSMENT:",
            f"  Goodness (Treatment Efficacy):     {gile.get('G', 'N/A')}",
            f"  Intuition (Pattern Confidence):     {gile.get('I', 'N/A')}",
            f"  Love (Care Quality):                {gile.get('L', 'N/A')}",
            f"  Existence (Physiological State):    {gile.get('E', 'N/A')}",
            f"  Composite Score:                    {gile.get('composite', 'N/A')}",
            f"  Tralse Classification:              {gile.get('tralse_label', 'N/A')}",
            "",
            f"CLINICAL ACUITY: {acuity.upper()}",
            f"CONFIDENCE LEVEL: {confidence.get('label', 'N/A')} ({confidence.get('confidence', 'N/A')})",
            "",
        ])

        risk_preds = assessment.get("risk_predictions", {})
        if risk_preds:
            lines.append("RISK STRATIFICATION:")
            for risk_type, risk_data in risk_preds.items():
                if isinstance(risk_data, dict) and "risk_level" in risk_data:
                    lines.append(f"  {risk_type.upper()}: {risk_data['risk_level']}")
                elif isinstance(risk_data, dict) and "risk_category" in risk_data:
                    lines.append(f"  {risk_type.upper()}: {risk_data['risk_category']}")
            lines.append("")

        actions = assessment.get("recommended_actions", [])
        if actions:
            lines.append("RECOMMENDED ACTIONS:")
            for i, action in enumerate(actions, 1):
                lines.append(f"  {i}. {action}")
            lines.append("")

        lines.extend([
            "-" * 60,
            "DISCLAIMER: This is a clinical decision support tool.",
            "All recommendations require clinician review and judgment.",
            "This system does not replace professional medical evaluation.",
            "=" * 60,
        ])

        return "\n".join(lines)

    def predict_risk_factors(self, patient_data: Dict) -> Dict:
        """Multi-disease risk prediction across cardiovascular, diabetes,
        respiratory, and mental health domains.

        Args:
            patient_data: Flat dictionary with patient clinical data.

        Returns:
            Dictionary of risk predictions by disease domain.
        """
        predictions = {}

        age = patient_data.get("age", 0)
        if age >= 20 and (patient_data.get("systolic_bp", 0) > 0 or
                          patient_data.get("total_cholesterol", 0) > 0):
            predictions["cardiovascular"] = self.risk_engine.cardiovascular_risk(patient_data)

        if (patient_data.get("bmi", 0) > 0 or patient_data.get("fasting_glucose", 0) > 0):
            predictions["diabetes"] = self.risk_engine.diabetes_risk(patient_data)

        if (patient_data.get("phq9_score", 0) > 0 or patient_data.get("gad7_score", 0) > 0):
            predictions["mental_health"] = self.risk_engine.mental_health_screening(patient_data)

        if (patient_data.get("smoking_pack_years", 0) > 0 or
            patient_data.get("fev1_predicted_pct", 0) > 0 or
            patient_data.get("spo2", 0) > 0):
            predictions["respiratory"] = self.risk_engine.respiratory_risk(patient_data)

        return predictions

    def recommend_interventions(self, assessment: Dict) -> List[str]:
        """Evidence-based intervention recommendations from assessment results.

        Args:
            assessment: Assessment result from assess_patient().

        Returns:
            Ordered list of recommended interventions.
        """
        interventions = []
        acuity = assessment.get("acuity", "stable")

        if acuity == "critical":
            interventions.extend([
                "STAT: Activate rapid response / code team",
                "Continuous vital sign monitoring",
                "Establish IV access and obtain STAT labs",
                "Notify attending physician immediately",
            ])

        if acuity == "acute":
            interventions.extend([
                "Place patient on continuous monitoring",
                "Obtain comprehensive lab panel",
                "Physician evaluation within 30 minutes",
            ])

        risk_preds = assessment.get("risk_predictions", {})

        cv_risk = risk_preds.get("cardiovascular", {})
        if cv_risk.get("risk_category") in ("intermediate", "high"):
            interventions.extend(cv_risk.get("modifiable_factors", []))

        dm_risk = risk_preds.get("diabetes", {})
        if dm_risk.get("risk_level") in ("moderate", "high", "very_high"):
            interventions.extend(dm_risk.get("interventions", []))

        mh_risk = risk_preds.get("mental_health", {})
        if mh_risk.get("urgent_flags"):
            interventions.extend(mh_risk.get("recommended_actions", []))

        resp_risk = risk_preds.get("respiratory", {})
        if resp_risk.get("risk_level") in ("moderate", "high", "very_high"):
            interventions.extend(resp_risk.get("interventions", []))

        vitals_assessment = assessment.get("vitals_assessment", {})
        for flag in vitals_assessment.get("critical_flags", []):
            interventions.append(f"Address critical vital sign: {flag}")

        gile = assessment.get("gile_score", {})
        if gile.get("L", 1) < 0.5:
            interventions.append("Enhance patient communication and shared decision-making")
        if gile.get("E", 1) < 0.4:
            interventions.append("Prioritize physiological stabilization before further workup")

        seen = set()
        unique = []
        for item in interventions:
            if item not in seen:
                seen.add(item)
                unique.append(item)

        return unique

    def offline_mode_assessment(self, limited_data: Dict) -> Dict:
        """Assessment with minimal data for offline/edge deployment.

        Works with as little as symptoms and basic vitals, using cached
        clinical guidelines and local decision trees.

        Args:
            limited_data: Dictionary with whatever data is available
                         (symptoms, basic vitals, age, sex).

        Returns:
            Simplified assessment suitable for resource-constrained environments.
        """
        symptoms = limited_data.get("symptoms", [])
        vitals = limited_data.get("vitals", {})
        age = limited_data.get("age", 0)
        sex = limited_data.get("sex", "unknown")

        triage = self.triage_patient(symptoms, vitals)

        matched_conditions = []
        for condition, guideline in self.guidelines.CONDITION_GUIDELINES.items():
            criteria = guideline.get("criteria", {})
            match_score = 0
            total_criteria = len(criteria)

            for criterion, threshold in criteria.items():
                if isinstance(threshold, bool):
                    if criterion in symptoms:
                        match_score += 1
                elif isinstance(threshold, (int, float)):
                    value = vitals.get(criterion, limited_data.get(criterion, 0))
                    if value >= threshold:
                        match_score += 1

            if total_criteria > 0 and match_score / total_criteria >= 0.5:
                matched_conditions.append({
                    "condition": condition,
                    "match_score": round(match_score / total_criteria, 2),
                    "interventions": guideline.get("interventions", []),
                    "follow_up_days": guideline.get("follow_up_days", 30),
                })

        vitals_status = {}
        for vital_name, value in vitals.items():
            if vital_name in VITAL_SIGN_RANGES:
                ranges = VITAL_SIGN_RANGES[vital_name]
                if value <= ranges["critical_low"] or value >= ranges["critical_high"]:
                    vitals_status[vital_name] = "critical"
                elif value < ranges["normal_low"] or value > ranges["normal_high"]:
                    vitals_status[vital_name] = "abnormal"
                else:
                    vitals_status[vital_name] = "normal"

        data_completeness = 0
        if symptoms: data_completeness += 0.3
        if vitals: data_completeness += 0.3
        if age > 0: data_completeness += 0.2
        if sex != "unknown": data_completeness += 0.1
        if limited_data.get("medical_history"): data_completeness += 0.1

        gile = GILEHealthScore(
            goodness=0.5,
            intuition=min(1.0, data_completeness),
            love=0.7,
            existence=triage["gile_score"]["E"],
        )

        return {
            "mode": "offline",
            "timestamp": datetime.utcnow().isoformat(),
            "data_completeness": round(data_completeness, 2),
            "triage": {
                "esi_level": triage["esi_level"],
                "esi_label": triage["esi_label"],
                "disposition": triage["disposition_recommendation"],
            },
            "vitals_status": vitals_status,
            "matched_conditions": matched_conditions,
            "gile_score": gile.to_dict(),
            "confidence_note": (
                "Limited data assessment - confidence reduced. "
                "Seek full clinical evaluation when connectivity/resources available."
            ),
            "immediate_actions": triage.get("recommended_actions", []),
        }

    def _assess_vitals(self, vitals: Dict) -> Dict:
        abnormals = []
        critical_flags = []
        normal_count = 0
        total_checked = 0

        for vital_name, value in vitals.items():
            if vital_name not in VITAL_SIGN_RANGES:
                continue
            total_checked += 1
            ranges = VITAL_SIGN_RANGES[vital_name]

            if value <= ranges["critical_low"] or value >= ranges["critical_high"]:
                critical_flags.append(f"{vital_name}: {value} {ranges['unit']} (CRITICAL)")
            elif value < ranges["normal_low"] or value > ranges["normal_high"]:
                status = "low" if value < ranges["normal_low"] else "high"
                abnormals.append(f"{vital_name}: {value} {ranges['unit']} ({status})")
            else:
                normal_count += 1

        completeness = min(1.0, total_checked / 5.0)

        return {
            "total_checked": total_checked,
            "normal_count": normal_count,
            "abnormal_count": len(abnormals),
            "abnormals": abnormals,
            "critical_flags": critical_flags,
            "completeness": completeness,
            "overall_stability": max(0, 1.0 - len(critical_flags) * 0.3 - len(abnormals) * 0.1),
        }

    def _analyze_symptoms(self, symptoms: List[str], vitals: Dict) -> Dict:
        critical = [s for s in symptoms if s in CRITICAL_SYMPTOMS]
        high = [s for s in symptoms if s in HIGH_PRIORITY_SYMPTOMS]
        other = [s for s in symptoms if s not in CRITICAL_SYMPTOMS and s not in HIGH_PRIORITY_SYMPTOMS]

        if critical:
            severity = "critical"
        elif len(high) >= 2:
            severity = "high"
        elif high:
            severity = "moderate"
        elif symptoms:
            severity = "low"
        else:
            severity = "none"

        clarity_score = min(1.0, len(symptoms) / 3.0) if symptoms else 0.0

        return {
            "total_symptoms": len(symptoms),
            "critical_symptoms": critical,
            "high_priority_symptoms": high,
            "other_symptoms": other,
            "severity": severity,
            "clarity_score": clarity_score,
        }

    def _analyze_labs(self, labs: Dict) -> Dict:
        findings = []

        glucose = labs.get("fasting_glucose", labs.get("blood_glucose", 0))
        if glucose > 0:
            if glucose >= 200:
                findings.append({"test": "glucose", "value": glucose, "flag": "critical_high"})
            elif glucose >= 126:
                findings.append({"test": "glucose", "value": glucose, "flag": "high"})
            elif glucose < 70:
                findings.append({"test": "glucose", "value": glucose, "flag": "low"})

        hba1c = labs.get("hba1c", 0)
        if hba1c > 0:
            if hba1c >= 6.5:
                findings.append({"test": "hba1c", "value": hba1c, "flag": "diabetic_range"})
            elif hba1c >= 5.7:
                findings.append({"test": "hba1c", "value": hba1c, "flag": "prediabetic"})

        chol = labs.get("total_cholesterol", 0)
        if chol > 0 and chol > 200:
            findings.append({"test": "total_cholesterol", "value": chol, "flag": "elevated"})

        ldl = labs.get("ldl_cholesterol", 0)
        if ldl > 0 and ldl > 130:
            findings.append({"test": "ldl_cholesterol", "value": ldl, "flag": "elevated"})

        creatinine = labs.get("creatinine", 0)
        if creatinine > 0 and creatinine > 1.2:
            findings.append({"test": "creatinine", "value": creatinine, "flag": "elevated"})

        wbc = labs.get("wbc", 0)
        if wbc > 0:
            if wbc > 11.0:
                findings.append({"test": "wbc", "value": wbc, "flag": "elevated"})
            elif wbc < 4.0:
                findings.append({"test": "wbc", "value": wbc, "flag": "low"})

        hemoglobin = labs.get("hemoglobin", 0)
        if hemoglobin > 0:
            if hemoglobin < 12.0:
                findings.append({"test": "hemoglobin", "value": hemoglobin, "flag": "anemia"})

        troponin = labs.get("troponin", 0)
        if troponin > 0 and troponin > 0.04:
            findings.append({"test": "troponin", "value": troponin, "flag": "elevated_cardiac"})

        return {
            "tests_analyzed": len(labs),
            "abnormal_findings": findings,
            "abnormal_count": len(findings),
        }

    def _compute_patient_gile(self, vitals_assessment: Dict, symptom_analysis: Dict,
                               lab_analysis: Dict, profile: PatientProfile) -> GILEHealthScore:
        goodness = 0.5
        if vitals_assessment["completeness"] > 0.5:
            goodness = vitals_assessment["overall_stability"] * 0.7 + 0.3
        if lab_analysis["abnormal_count"] > 3:
            goodness *= 0.7

        intuition = min(1.0, (vitals_assessment["completeness"] * 0.4 +
                              symptom_analysis["clarity_score"] * 0.3 +
                              min(1.0, lab_analysis["tests_analyzed"] / 5.0) * 0.3))

        love = 0.8
        if profile.allergies:
            love = min(love, 0.9)
        if profile.current_medications:
            love = min(love, 0.85)

        existence = vitals_assessment.get("overall_stability", 0.5)
        if symptom_analysis["severity"] == "critical":
            existence *= 0.5
        elif symptom_analysis["severity"] == "high":
            existence *= 0.7

        return GILEHealthScore(
            goodness=max(0, min(1, goodness)),
            intuition=max(0, min(1, intuition)),
            love=max(0, min(1, love)),
            existence=max(0, min(1, existence)),
        )

    def _assess_vitals_stability(self, vitals: Dict) -> Dict:
        critical = False
        abnormal = False
        unstable = False
        abnormal_count = 0

        for vital_name, value in vitals.items():
            if vital_name not in VITAL_SIGN_RANGES:
                continue
            ranges = VITAL_SIGN_RANGES[vital_name]
            if value <= ranges["critical_low"] or value >= ranges["critical_high"]:
                critical = True
                abnormal_count += 1
            elif value < ranges["normal_low"] or value > ranges["normal_high"]:
                abnormal = True
                abnormal_count += 1

        if abnormal_count >= 3:
            unstable = True

        stability_score = max(0, 1.0 - abnormal_count * 0.15)

        return {
            "critical": critical,
            "abnormal": abnormal,
            "unstable": unstable,
            "abnormal_count": abnormal_count,
            "stability_score": round(stability_score, 3),
        }

    def _estimate_resources(self, symptoms: List[str]) -> int:
        resource_map = {
            "laceration": 1, "sprain": 1, "rash": 1, "sore_throat": 1,
            "cough": 1, "headache": 1, "back_pain": 1, "urinary_symptoms": 1,
            "abdominal_pain": 2, "vomiting": 2, "fracture_suspected": 2,
            "fever": 2, "chest_pain": 2, "dyspnea": 2,
        }
        total = sum(resource_map.get(s, 1) for s in symptoms)
        return min(total, 3)

    def _generate_actions(self, acuity: str, vitals_assessment: Dict,
                           symptom_analysis: Dict, gile: GILEHealthScore) -> List[str]:
        actions = []

        if acuity == "critical":
            actions.extend([
                "Immediate physician evaluation required",
                "Initiate continuous monitoring",
                "Prepare for potential intervention",
            ])
        elif acuity == "acute":
            actions.extend([
                "Physician evaluation within 30 minutes",
                "Place on telemetry monitoring",
            ])

        if vitals_assessment.get("completeness", 0) < 0.6:
            actions.append("Complete vital sign assessment (missing data)")

        if symptom_analysis.get("severity") in ("critical", "high"):
            actions.append("Focused physical examination of affected systems")

        if gile.composite < 0.4:
            actions.append("Consider additional diagnostic workup")
        elif gile.composite < 0.6:
            actions.append("Monitor and reassess in 2-4 hours")
        else:
            actions.append("Continue current management plan")

        return actions

    def _triage_actions(self, esi_level: int, critical_symptoms: List[str],
                         vitals_stability: Dict) -> List[str]:
        actions = []

        if esi_level == 1:
            actions.extend([
                "ACTIVATE CODE TEAM / RAPID RESPONSE",
                "Immediate airway-breathing-circulation assessment",
                "Establish large-bore IV access",
                "STAT labs, ECG, imaging as indicated",
            ])
        elif esi_level == 2:
            actions.extend([
                "Immediate nursing assessment",
                "Place in monitored bed",
                "Physician evaluation within 10 minutes",
                "Obtain focused labs and diagnostics",
            ])
        elif esi_level == 3:
            actions.extend([
                "Nursing assessment within 15 minutes",
                "Initiate appropriate workup",
                "Physician evaluation within 30 minutes",
            ])
        elif esi_level == 4:
            actions.extend([
                "Standard nursing assessment",
                "Physician evaluation within 60 minutes",
            ])
        else:
            actions.append("Routine evaluation and discharge planning")

        for symptom in critical_symptoms:
            protocol = {
                "chest_pain": "Activate chest pain protocol",
                "stroke_symptoms": "Activate stroke alert protocol",
                "anaphylaxis": "Administer epinephrine per protocol",
                "cardiac_arrest": "Initiate ACLS protocol",
                "severe_bleeding": "Apply direct pressure, type and cross",
                "seizure": "Seizure precautions, benzodiazepine standby",
            }
            if symptom in protocol:
                actions.append(protocol[symptom])

        return actions


class MedGemmaInterface:
    """Interface for formatting prompts and parsing responses for MedGemma models.

    Provides structured prompt generation for various clinical tasks and
    response parsing to convert model outputs into structured clinical data.
    Designed to work with MedGemma multimodal models for text and image analysis.
    """

    TASK_TEMPLATES = {
        "clinical_assessment": (
            "You are a clinical decision support system. Analyze the following patient data "
            "and provide a structured assessment.\n\n"
            "Patient Information:\n{patient_info}\n\n"
            "Provide your assessment in the following format:\n"
            "1. PRIMARY IMPRESSION:\n"
            "2. DIFFERENTIAL DIAGNOSES (ranked by likelihood):\n"
            "3. RECOMMENDED INVESTIGATIONS:\n"
            "4. RISK FACTORS:\n"
            "5. MANAGEMENT RECOMMENDATIONS:\n"
            "6. FOLLOW-UP PLAN:\n"
        ),
        "chest_xray_analysis": (
            "You are a radiology AI assistant. Analyze the following chest X-ray image "
            "and clinical context.\n\n"
            "Clinical Context:\n{patient_info}\n\n"
            "Provide your analysis in the following format:\n"
            "1. TECHNICAL QUALITY: (adequate/limited/poor)\n"
            "2. FINDINGS:\n"
            "   - Heart: \n"
            "   - Lungs: \n"
            "   - Mediastinum: \n"
            "   - Bones: \n"
            "   - Soft Tissues: \n"
            "3. IMPRESSION:\n"
            "4. RECOMMENDATIONS:\n"
        ),
        "lab_report_extraction": (
            "Extract structured laboratory data from the following report.\n\n"
            "Report:\n{patient_info}\n\n"
            "Return each result in the format:\n"
            "TEST_NAME | VALUE | UNIT | REFERENCE_RANGE | FLAG (Normal/High/Low/Critical)\n"
        ),
        "clinical_documentation": (
            "Generate a clinical note based on the following patient encounter data.\n\n"
            "Encounter Data:\n{patient_info}\n\n"
            "Format the note using standard SOAP structure:\n"
            "SUBJECTIVE:\n"
            "OBJECTIVE:\n"
            "ASSESSMENT:\n"
            "PLAN:\n"
        ),
        "medication_review": (
            "Review the following medication list for a patient and identify potential "
            "interactions, contraindications, and optimization opportunities.\n\n"
            "Patient Profile:\n{patient_info}\n\n"
            "Provide analysis in the following format:\n"
            "1. DRUG INTERACTIONS:\n"
            "2. CONTRAINDICATIONS:\n"
            "3. DOSAGE APPROPRIATENESS:\n"
            "4. THERAPEUTIC DUPLICATIONS:\n"
            "5. OPTIMIZATION RECOMMENDATIONS:\n"
        ),
        "triage_assessment": (
            "Assess the following emergency presentation and provide triage recommendations.\n\n"
            "Presentation:\n{patient_info}\n\n"
            "Provide assessment in the following format:\n"
            "1. ESI LEVEL (1-5):\n"
            "2. ACUITY JUSTIFICATION:\n"
            "3. IMMEDIATE ACTIONS:\n"
            "4. DIFFERENTIAL CONSIDERATIONS:\n"
            "5. RED FLAGS:\n"
        ),
    }

    RESPONSE_SECTIONS = {
        "clinical_assessment": [
            "PRIMARY IMPRESSION", "DIFFERENTIAL DIAGNOSES",
            "RECOMMENDED INVESTIGATIONS", "RISK FACTORS",
            "MANAGEMENT RECOMMENDATIONS", "FOLLOW-UP PLAN",
        ],
        "chest_xray_analysis": [
            "TECHNICAL QUALITY", "FINDINGS", "IMPRESSION", "RECOMMENDATIONS",
        ],
        "lab_report_extraction": [],
        "clinical_documentation": [
            "SUBJECTIVE", "OBJECTIVE", "ASSESSMENT", "PLAN",
        ],
        "medication_review": [
            "DRUG INTERACTIONS", "CONTRAINDICATIONS", "DOSAGE APPROPRIATENESS",
            "THERAPEUTIC DUPLICATIONS", "OPTIMIZATION RECOMMENDATIONS",
        ],
        "triage_assessment": [
            "ESI LEVEL", "ACUITY JUSTIFICATION", "IMMEDIATE ACTIONS",
            "DIFFERENTIAL CONSIDERATIONS", "RED FLAGS",
        ],
    }

    def format_prompt_for_medgemma(self, task: str, patient_data: Dict) -> str:
        """Creates structured prompts for MedGemma inference.

        Args:
            task: One of the supported task types (clinical_assessment,
                  chest_xray_analysis, lab_report_extraction, etc.)
            patient_data: Patient data dictionary to embed in the prompt.

        Returns:
            Formatted prompt string ready for MedGemma model input.
        """
        template = self.TASK_TEMPLATES.get(task)
        if not template:
            template = self.TASK_TEMPLATES["clinical_assessment"]

        patient_info = self._format_patient_info(patient_data)
        return template.format(patient_info=patient_info)

    def parse_medgemma_response(self, response: str, task: str = "clinical_assessment") -> Dict:
        """Parses MedGemma model outputs into structured data.

        Args:
            response: Raw text response from MedGemma model.
            task: The task type used to generate the prompt.

        Returns:
            Structured dictionary with parsed sections.
        """
        sections = self.RESPONSE_SECTIONS.get(task, [])
        parsed = {"raw_response": response, "task": task, "sections": {}}

        if task == "lab_report_extraction":
            parsed["lab_results"] = self._parse_lab_results(response)
            return parsed

        current_section = None
        current_content = []

        for line in response.split("\n"):
            stripped = line.strip()
            matched = False
            for section in sections:
                if section.lower() in stripped.lower() and (stripped.endswith(":") or stripped[0].isdigit()):
                    if current_section:
                        parsed["sections"][current_section] = "\n".join(current_content).strip()
                    current_section = section
                    current_content = []
                    content_after = stripped.split(":", 1)
                    if len(content_after) > 1 and content_after[1].strip():
                        current_content.append(content_after[1].strip())
                    matched = True
                    break
            if not matched and current_section:
                current_content.append(line)

        if current_section:
            parsed["sections"][current_section] = "\n".join(current_content).strip()

        parsed["completeness"] = len(parsed["sections"]) / max(len(sections), 1)
        return parsed

    def chest_xray_analysis(self, clinical_context: Dict) -> str:
        """Generate a prompt for chest X-ray analysis."""
        return self.format_prompt_for_medgemma("chest_xray_analysis", clinical_context)

    def lab_report_extraction(self, report_data: Dict) -> str:
        """Generate a prompt for lab report extraction."""
        return self.format_prompt_for_medgemma("lab_report_extraction", report_data)

    def clinical_documentation(self, encounter_data: Dict) -> str:
        """Generate a prompt for clinical documentation."""
        return self.format_prompt_for_medgemma("clinical_documentation", encounter_data)

    def medication_review(self, patient_data: Dict) -> str:
        """Generate a prompt for medication review."""
        return self.format_prompt_for_medgemma("medication_review", patient_data)

    def triage_assessment(self, presentation_data: Dict) -> str:
        """Generate a prompt for triage assessment."""
        return self.format_prompt_for_medgemma("triage_assessment", presentation_data)

    def _format_patient_info(self, patient_data: Dict) -> str:
        lines = []
        section_order = [
            ("demographics", "Demographics"),
            ("symptoms", "Presenting Symptoms"),
            ("vitals", "Vital Signs"),
            ("lab_results", "Laboratory Results"),
            ("medical_history", "Medical History"),
            ("medications", "Current Medications"),
            ("allergies", "Allergies"),
            ("imaging_findings", "Imaging Findings"),
            ("clinical_notes", "Clinical Notes"),
        ]

        for key, label in section_order:
            value = patient_data.get(key)
            if value is None:
                continue

            lines.append(f"\n{label}:")
            if isinstance(value, dict):
                for k, v in value.items():
                    unit = VITAL_SIGN_RANGES.get(k, {}).get("unit", "")
                    lines.append(f"  {k.replace('_', ' ').title()}: {v} {unit}".rstrip())
            elif isinstance(value, list):
                for item in value:
                    lines.append(f"  - {item}")
            else:
                lines.append(f"  {value}")

        if not lines:
            for k, v in patient_data.items():
                if isinstance(v, (str, int, float)):
                    lines.append(f"  {k.replace('_', ' ').title()}: {v}")

        return "\n".join(lines)

    def _parse_lab_results(self, response: str) -> List[Dict]:
        results = []
        for line in response.split("\n"):
            stripped = line.strip()
            if "|" in stripped:
                parts = [p.strip() for p in stripped.split("|")]
                if len(parts) >= 3:
                    result = {
                        "test_name": parts[0],
                        "value": parts[1],
                        "unit": parts[2] if len(parts) > 2 else "",
                        "reference_range": parts[3] if len(parts) > 3 else "",
                        "flag": parts[4] if len(parts) > 4 else "Normal",
                    }
                    results.append(result)
        return results


def create_health_assessor() -> GILEHealthAssessor:
    """Factory function to create a configured GILEHealthAssessor instance."""
    return GILEHealthAssessor()


def create_medgemma_interface() -> MedGemmaInterface:
    """Factory function to create a configured MedGemmaInterface instance."""
    return MedGemmaInterface()


def demo_assessment():
    """Demonstration of the GILE-Enhanced Clinical Decision Support System."""
    assessor = create_health_assessor()

    patient_data = {
        "demographics": {
            "age": 58,
            "sex": "male",
            "weight_kg": 92,
            "height_cm": 175,
            "smoking_status": "former",
        },
        "symptoms": ["chest_tightness", "dyspnea", "fatigue"],
        "vitals": {
            "heart_rate": 88,
            "systolic_bp": 148,
            "diastolic_bp": 92,
            "respiratory_rate": 18,
            "temperature": 37.0,
            "spo2": 95,
        },
        "lab_results": {
            "total_cholesterol": 245,
            "hdl_cholesterol": 38,
            "ldl_cholesterol": 162,
            "fasting_glucose": 118,
            "hba1c": 6.1,
            "creatinine": 1.1,
            "troponin": 0.02,
        },
        "medical_history": ["hypertension", "hyperlipidemia"],
        "medications": ["lisinopril 10mg", "atorvastatin 20mg"],
        "allergies": ["penicillin"],
        "family_history": ["father_mi_age_62", "mother_diabetes"],
    }

    assessment = assessor.assess_patient(patient_data)
    clinical_note = assessor.generate_clinical_summary(patient_data, assessment)
    interventions = assessor.recommend_interventions(assessment)

    triage_result = assessor.triage_patient(
        symptoms=["chest_tightness", "dyspnea"],
        vitals={"heart_rate": 88, "systolic_bp": 148, "spo2": 95},
    )

    offline_result = assessor.offline_mode_assessment({
        "symptoms": ["fever", "cough"],
        "vitals": {"heart_rate": 102, "temperature": 38.5, "spo2": 94},
        "age": 72,
    })

    interface = create_medgemma_interface()
    prompt = interface.format_prompt_for_medgemma("clinical_assessment", patient_data)

    return {
        "assessment": assessment,
        "clinical_note": clinical_note,
        "interventions": interventions,
        "triage": triage_result,
        "offline_assessment": offline_result,
        "medgemma_prompt_preview": prompt[:500] + "...",
    }


if __name__ == "__main__":
    results = demo_assessment()
    print(json.dumps(results["assessment"]["gile_score"], indent=2))
    print(f"\nTriage ESI Level: {results['triage']['esi_level']}")
    print(f"Offline Mode: {results['offline_assessment']['triage']['esi_label']}")
    print(f"\nInterventions ({len(results['interventions'])}):")
    for i, intervention in enumerate(results["interventions"], 1):
        print(f"  {i}. {intervention}")
