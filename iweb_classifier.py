"""
I-Web Classification System for Companies & Organizations

Classifies entities along the spectrum:
- I-Cell: Fully sovereign/autonomous (e.g., sole proprietor, tight startup)
- I-Web: Tightly linked dependent entities (e.g., daily workplace, strong culture)
- I-Web Nest: Very loosely distributed entities (e.g., gig economy, umbrella orgs)

Used for God Machine stock predictions - i-web coherence affects market performance!
"""

import numpy as np
from dataclasses import dataclass
from typing import Dict, List, Tuple
from enum import Enum

class IWebType(Enum):
    """Classification types for organizational coherence"""
    I_CELL = "i-cell"  # Fully sovereign/autonomous (GILE ≥ 0.42, high coherence)
    I_WEB = "i-web"  # Tightly linked (GILE ≥ 0.42, moderate-high coherence)
    I_WEB_NEST = "i-web-nest"  # Loosely distributed (can be < 0.42 GILE)

@dataclass
class IWebMetrics:
    """Measurable metrics for i-web classification"""
    
    # INTERNAL COHERENCE (how integrated internally)
    employee_ratio: float  # 0-1: % full-time employees vs contractors
    workplace_proximity: float  # 0-1: % collocated vs remote
    meeting_frequency: float  # 0-1: daily=1, weekly=0.7, monthly=0.3, never=0
    decision_centralization: float  # 0-1: hierarchical=1, flat/distributed=0
    shared_values_strength: float  # 0-1: strong culture=1, weak=0
    
    # EXTERNAL COHERENCE (relationship to investors/parent)
    ownership_concentration: float  # 0-1: single owner=1, dispersed=0
    autonomy_from_parent: float  # 0-1: independent=1, branch/subsidiary=0
    investor_involvement: float  # 0-1: hands-off=1, active board=0.5, PE control=0
    
    # ORGANIZATIONAL STRUCTURE
    org_size: int  # Number of people
    hierarchy_depth: int  # Levels from CEO to frontline
    cross_team_collaboration: float  # 0-1: high=1, siloed=0
    
    # BEHAVIORAL INDICATORS
    turnover_rate: float  # Annual churn %
    internal_mobility: float  # 0-1: high internal movement=1
    knowledge_sharing: float  # 0-1: high documentation/training=1

@dataclass
class IWebClassification:
    """Complete classification with scores and reasoning"""
    classification: IWebType
    coherence_score: float  # Overall coherence (0-1)
    gile_estimate: float  # Estimated GILE score
    confidence: float  # Classification confidence (0-1)
    internal_coherence: float  # Internal integration score
    external_coherence: float  # External sovereignty score
    reasoning: str  # Human-readable explanation
    risk_factors: List[str]  # Factors that could destabilize coherence
    strengths: List[str]  # Factors supporting coherence

class IWebClassifier:
    """
    TI-compatible classifier for organizational coherence
    
    Based on i-cell vs i-web theory:
    - I-cells have coherent dark energy boundary (self-awareness) ≥ 0.42 GILE
    - I-webs can exist with collective coherence < 0.42 (relative truths)
    - Companies vary from organs (tight) to forests (loose) to Earth (very loose)
    """
    
    def __init__(self):
        # Threshold values (calibrated empirically)
        self.I_CELL_THRESHOLD = 0.75  # Very high coherence
        self.I_WEB_THRESHOLD = 0.50   # Moderate coherence
        # Below 0.50 = I-Web Nest
        
        # GILE thresholds
        self.SOUL_DEATH_THRESHOLD = 0.42  # Below this = soul dies (for i-cells)
        
    def classify(self, metrics: IWebMetrics) -> IWebClassification:
        """
        Main classification method - returns full classification with reasoning
        """
        
        # Calculate sub-scores
        internal_coherence = self._calculate_internal_coherence(metrics)
        external_coherence = self._calculate_external_coherence(metrics)
        structural_coherence = self._calculate_structural_coherence(metrics)
        
        # Overall coherence score (weighted average)
        coherence_score = (
            0.5 * internal_coherence +  # Internal is most important
            0.3 * external_coherence +   # External sovereignty matters
            0.2 * structural_coherence   # Structure supports the rest
        )
        
        # Estimate GILE score from coherence
        # Note: I-webs CAN exist below 0.42 (unlike i-cells which die)
        gile_estimate = self._coherence_to_gile(coherence_score, metrics.org_size)
        
        # Classify based on coherence score
        if coherence_score >= self.I_CELL_THRESHOLD:
            classification = IWebType.I_CELL
            confidence = min(0.95, coherence_score)
        elif coherence_score >= self.I_WEB_THRESHOLD:
            classification = IWebType.I_WEB
            confidence = 0.7 + (coherence_score - self.I_WEB_THRESHOLD) * 0.5
        else:
            classification = IWebType.I_WEB_NEST
            confidence = 0.6 + (self.I_WEB_THRESHOLD - coherence_score) * 0.4
        
        # Generate reasoning and risk factors
        reasoning = self._generate_reasoning(
            classification, coherence_score, internal_coherence, 
            external_coherence, metrics
        )
        
        risk_factors = self._identify_risk_factors(metrics, coherence_score)
        strengths = self._identify_strengths(metrics, coherence_score)
        
        return IWebClassification(
            classification=classification,
            coherence_score=coherence_score,
            gile_estimate=gile_estimate,
            confidence=confidence,
            internal_coherence=internal_coherence,
            external_coherence=external_coherence,
            reasoning=reasoning,
            risk_factors=risk_factors,
            strengths=strengths
        )
    
    def _calculate_internal_coherence(self, m: IWebMetrics) -> float:
        """How tightly integrated are the internal components?"""
        
        # Factors that increase internal coherence:
        # 1. High employee ratio (not contractors)
        # 2. Physical proximity (not remote)
        # 3. Frequent meetings/interactions
        # 4. Strong shared values/culture
        # 5. High cross-team collaboration
        # 6. Low turnover
        # 7. High knowledge sharing
        
        score = (
            0.20 * m.employee_ratio +
            0.15 * m.workplace_proximity +
            0.15 * m.meeting_frequency +
            0.15 * m.shared_values_strength +
            0.15 * m.cross_team_collaboration +
            0.10 * (1.0 - min(1.0, m.turnover_rate / 0.5)) +  # 50% turnover = 0 score
            0.10 * m.knowledge_sharing
        )
        
        return np.clip(score, 0.0, 1.0)
    
    def _calculate_external_coherence(self, m: IWebMetrics) -> float:
        """How sovereign/autonomous is the entity externally?"""
        
        # Factors that increase external coherence:
        # 1. High ownership concentration (not dispersed)
        # 2. High autonomy from parent company
        # 3. Low investor involvement (not controlled)
        # 4. Centralized decision-making (not fragmented)
        
        score = (
            0.30 * m.ownership_concentration +
            0.35 * m.autonomy_from_parent +
            0.25 * m.investor_involvement +
            0.10 * m.decision_centralization
        )
        
        return np.clip(score, 0.0, 1.0)
    
    def _calculate_structural_coherence(self, m: IWebMetrics) -> float:
        """How does organizational structure support coherence?"""
        
        # Optimal size: not too small (< 5), not too large (> 1000)
        if m.org_size < 5:
            size_score = m.org_size / 5.0  # Penalize very small
        elif m.org_size <= 150:  # Dunbar's number
            size_score = 1.0
        elif m.org_size <= 1000:
            size_score = 1.0 - (m.org_size - 150) / 850 * 0.3
        else:
            size_score = 0.7 - min(0.4, (m.org_size - 1000) / 10000 * 0.4)
        
        # Optimal hierarchy: 3-5 levels (not too flat, not too deep)
        if m.hierarchy_depth < 2:
            hierarchy_score = 0.6  # Too flat
        elif 3 <= m.hierarchy_depth <= 5:
            hierarchy_score = 1.0  # Optimal
        elif m.hierarchy_depth <= 8:
            hierarchy_score = 1.0 - (m.hierarchy_depth - 5) / 3 * 0.3
        else:
            hierarchy_score = 0.5  # Too bureaucratic
        
        # Internal mobility supports coherence
        mobility_score = m.internal_mobility
        
        score = (
            0.4 * size_score +
            0.3 * hierarchy_score +
            0.3 * mobility_score
        )
        
        return np.clip(score, 0.0, 1.0)
    
    def _coherence_to_gile(self, coherence: float, org_size: int) -> float:
        """
        Convert coherence score to estimated GILE
        
        Key insight: I-webs CAN exist below 0.42 GILE threshold!
        - I-cells below 0.42 = soul dies (individuals, atoms)
        - I-webs below 0.42 = "collective fictions" (exist only in minds)
        - I-webs above 0.42 = real collective consciousness
        
        Small orgs behave more like i-cells (higher GILE requirement)
        Large orgs can survive with lower GILE (distributed nature)
        """
        
        # Size factor: smaller orgs need higher coherence
        if org_size < 10:
            size_penalty = 0.0  # Acts like i-cell
        elif org_size < 100:
            size_penalty = -0.05 * np.log10(org_size / 10)
        else:
            size_penalty = -0.10 * np.log10(org_size / 100)
        
        # Map coherence to GILE (with size adjustment)
        # Coherence 1.0 → GILE ~0.85
        # Coherence 0.5 → GILE ~0.42 (soul death threshold)
        # Coherence 0.0 → GILE ~0.20 (barely exists)
        
        gile = 0.20 + coherence * 0.65 + size_penalty
        
        return np.clip(gile, 0.0, 1.0)
    
    def _generate_reasoning(self, classification: IWebType, coherence: float,
                           internal: float, external: float, 
                           metrics: IWebMetrics) -> str:
        """Generate human-readable classification reasoning"""
        
        reasoning_parts = []
        
        # Classification summary
        if classification == IWebType.I_CELL:
            reasoning_parts.append(
                f"**I-CELL**: Highly coherent, sovereign entity (coherence: {coherence:.2f}). "
                f"Functions as a unified organism with strong internal integration and external autonomy."
            )
        elif classification == IWebType.I_WEB:
            reasoning_parts.append(
                f"**I-WEB**: Moderately coherent collective (coherence: {coherence:.2f}). "
                f"Tightly linked components with shared identity, but not fully sovereign."
            )
        else:
            reasoning_parts.append(
                f"**I-WEB NEST**: Loosely distributed collective (coherence: {coherence:.2f}). "
                f"Weak internal coherence - more like a network than an organism."
            )
        
        # Internal analysis
        if internal >= 0.7:
            reasoning_parts.append(
                f"Strong internal integration ({internal:.2f}) - members are tightly coupled "
                f"through {['low','moderate','high'][int(metrics.workplace_proximity * 2)]} proximity, "
                f"{['rare','regular','frequent'][int(metrics.meeting_frequency * 2)]} interaction, "
                f"and {['weak','moderate','strong'][int(metrics.shared_values_strength * 2)]} shared culture."
            )
        elif internal >= 0.4:
            reasoning_parts.append(
                f"Moderate internal integration ({internal:.2f}) - some cohesion but "
                f"notable fragmentation from "
                f"{'high contractor ratio, ' if metrics.employee_ratio < 0.5 else ''}"
                f"{'remote work, ' if metrics.workplace_proximity < 0.5 else ''}"
                f"{'infrequent interaction, ' if metrics.meeting_frequency < 0.5 else ''}"
                f"or weak culture."
            )
        else:
            reasoning_parts.append(
                f"Weak internal integration ({internal:.2f}) - heavily fragmented with "
                f"limited shared identity or coordination."
            )
        
        # External analysis
        if external >= 0.7:
            reasoning_parts.append(
                f"High external sovereignty ({external:.2f}) - entity operates autonomously "
                f"with concentrated ownership and minimal external control."
            )
        elif external >= 0.4:
            reasoning_parts.append(
                f"Moderate external sovereignty ({external:.2f}) - some autonomy but "
                f"{'dependent on parent company, ' if metrics.autonomy_from_parent < 0.5 else ''}"
                f"{'dispersed ownership, ' if metrics.ownership_concentration < 0.5 else ''}"
                f"{'or significant investor control' if metrics.investor_involvement < 0.5 else ''}."
            )
        else:
            reasoning_parts.append(
                f"Low external sovereignty ({external:.2f}) - heavily controlled by "
                f"external forces (parent company, investors, distributed ownership)."
            )
        
        return " ".join(reasoning_parts)
    
    def _identify_risk_factors(self, metrics: IWebMetrics, coherence: float) -> List[str]:
        """Identify factors that could destabilize coherence"""
        
        risks = []
        
        if metrics.turnover_rate > 0.3:
            risks.append(f"High turnover ({metrics.turnover_rate:.0%}) threatens institutional knowledge")
        
        if metrics.employee_ratio < 0.5:
            risks.append(f"Heavy contractor dependency ({1-metrics.employee_ratio:.0%}) reduces commitment")
        
        if metrics.workplace_proximity < 0.3:
            risks.append("Highly distributed workforce limits spontaneous collaboration")
        
        if metrics.ownership_concentration < 0.3:
            risks.append("Dispersed ownership could lead to fragmented decision-making")
        
        if metrics.autonomy_from_parent < 0.3:
            risks.append("Strong parent control limits independent action")
        
        if metrics.shared_values_strength < 0.4:
            risks.append("Weak culture provides little cohesive force")
        
        if metrics.org_size > 5000:
            risks.append(f"Very large size ({metrics.org_size}) makes coherence difficult")
        
        if metrics.hierarchy_depth > 7:
            risks.append(f"Deep hierarchy ({metrics.hierarchy_depth} levels) slows information flow")
        
        return risks
    
    def _identify_strengths(self, metrics: IWebMetrics, coherence: float) -> List[str]:
        """Identify factors supporting coherence"""
        
        strengths = []
        
        if metrics.employee_ratio > 0.8:
            strengths.append(f"Strong employee base ({metrics.employee_ratio:.0%}) ensures commitment")
        
        if metrics.workplace_proximity > 0.7:
            strengths.append("High colocation enables organic collaboration")
        
        if metrics.meeting_frequency > 0.8:
            strengths.append("Frequent interaction maintains alignment")
        
        if metrics.shared_values_strength > 0.7:
            strengths.append("Strong culture provides cohesive identity")
        
        if metrics.ownership_concentration > 0.7:
            strengths.append("Concentrated ownership enables decisive action")
        
        if metrics.autonomy_from_parent > 0.8:
            strengths.append("High autonomy permits adaptive strategy")
        
        if metrics.cross_team_collaboration > 0.7:
            strengths.append("Strong cross-functional collaboration")
        
        if metrics.knowledge_sharing > 0.7:
            strengths.append("Excellent knowledge sharing infrastructure")
        
        if 10 <= metrics.org_size <= 150:
            strengths.append(f"Optimal size ({metrics.org_size}) for coherence (within Dunbar number)")
        
        return strengths

def classify_company_example(company_name: str, metrics: IWebMetrics) -> IWebClassification:
    """
    Example function showing how to classify a company
    """
    classifier = IWebClassifier()
    classification = classifier.classify(metrics)
    
    print(f"\n{'='*80}")
    print(f"I-WEB CLASSIFICATION: {company_name}")
    print(f"{'='*80}\n")
    print(f"Type: {classification.classification.value.upper()}")
    print(f"Coherence Score: {classification.coherence_score:.3f}")
    print(f"GILE Estimate: {classification.gile_estimate:.3f}")
    print(f"Confidence: {classification.confidence:.3f}")
    print(f"\nInternal Coherence: {classification.internal_coherence:.3f}")
    print(f"External Coherence: {classification.external_coherence:.3f}")
    print(f"\n{classification.reasoning}")
    
    if classification.strengths:
        print(f"\n✅ STRENGTHS:")
        for strength in classification.strengths:
            print(f"  • {strength}")
    
    if classification.risk_factors:
        print(f"\n⚠️  RISK FACTORS:")
        for risk in classification.risk_factors:
            print(f"  • {risk}")
    
    print(f"\n{'='*80}\n")
    
    return classification


if __name__ == "__main__":
    # Example 1: Tech startup (I-CELL - tight, autonomous)
    startup = IWebMetrics(
        employee_ratio=0.95,
        workplace_proximity=0.9,
        meeting_frequency=0.95,
        decision_centralization=0.8,
        shared_values_strength=0.9,
        ownership_concentration=0.9,
        autonomy_from_parent=1.0,
        investor_involvement=0.7,
        org_size=35,
        hierarchy_depth=3,
        cross_team_collaboration=0.9,
        turnover_rate=0.15,
        internal_mobility=0.7,
        knowledge_sharing=0.85
    )
    
    classify_company_example("TechStartup Inc", startup)
    
    # Example 2: Enterprise corp (I-WEB - moderate coherence)
    corp = IWebMetrics(
        employee_ratio=0.85,
        workplace_proximity=0.4,
        meeting_frequency=0.6,
        decision_centralization=0.7,
        shared_values_strength=0.6,
        ownership_concentration=0.3,
        autonomy_from_parent=0.5,
        investor_involvement=0.4,
        org_size=2500,
        hierarchy_depth=6,
        cross_team_collaboration=0.5,
        turnover_rate=0.22,
        internal_mobility=0.6,
        knowledge_sharing=0.6
    )
    
    classify_company_example("MegaCorp Ltd", corp)
    
    # Example 3: Gig platform (I-WEB NEST - very loose)
    gig = IWebMetrics(
        employee_ratio=0.15,
        workplace_proximity=0.05,
        meeting_frequency=0.1,
        decision_centralization=0.3,
        shared_values_strength=0.2,
        ownership_concentration=0.4,
        autonomy_from_parent=0.8,
        investor_involvement=0.3,
        org_size=50000,
        hierarchy_depth=4,
        cross_team_collaboration=0.2,
        turnover_rate=0.60,
        internal_mobility=0.1,
        knowledge_sharing=0.3
    )
    
    classify_company_example("GigPlatform Co", gig)
