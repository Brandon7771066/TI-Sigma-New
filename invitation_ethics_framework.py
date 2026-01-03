"""
Invitation Ethics Framework
A GILE Extension for Understanding the Anti-Love Nature of Unnecessary Rejection

Core Insight (Brandon Emerick, November 2025):
- Declining invitations harms BOTH parties (inviter and decliner)
- It breeds arrogance (in decliner), humiliation (in inviter), and loneliness (in both)
- Most rejections are unjustified convenience excuses, not genuine conflicts
- Examples: "No time for coffee" when you make coffee at home anyway
         "No time for dinner" when you eat dinner anyway

GILE Framework Integration:
- Rejecting invitations is anti-LOVE (L dimension violation)
- False excuses are anti-GOODNESS (G dimension violation)
- Ignoring social connection opportunities damages INTUITION (I dimension)
- Creates toxic ENVIRONMENT (E dimension degradation)

Mathematical Foundation:
- Invitation Rejection Cost (IRC) = harm to both parties
- Convenience Excuse Coefficient (CEC) = dishonesty factor
- Connection Opportunity Value (COV) = what was lost
- Total Anti-GILE Score = IRC * (1 + CEC) / COV
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from enum import Enum
from datetime import datetime
import math


class InvitationType(Enum):
    """Categories of social invitations"""
    ROMANTIC = "romantic"           # Dating, relationship-building
    BUSINESS = "business"           # Networking, professional growth
    FRIENDSHIP = "friendship"       # Casual connection, companionship
    FAMILY = "family"               # Kinship obligations
    SPONTANEOUS = "spontaneous"     # Spur-of-moment opportunities


class RejectionReason(Enum):
    """Types of rejection reasons"""
    GENUINE_CONFLICT = "genuine_conflict"       # True scheduling conflict
    CONVENIENCE_EXCUSE = "convenience_excuse"   # "No time" when you have time
    ARROGANCE = "arrogance"                     # Feeling "above" the invitation
    FEAR = "fear"                               # Social anxiety, vulnerability
    LAZINESS = "laziness"                       # Effort avoidance
    LEGITIMATE_BOUNDARY = "legitimate_boundary" # Safety, values, health


@dataclass
class Invitation:
    """Represents a social invitation"""
    invitation_type: InvitationType
    inviter_name: str
    activity: str
    convenience_level: float  # 0-1, how convenient is acceptance?
    connection_value: float   # 0-1, potential relationship value
    time_required_hours: float
    description: Optional[str] = None
    timestamp: datetime = field(default_factory=datetime.now)


@dataclass
class RejectionAnalysis:
    """Analysis of a rejection decision"""
    invitation: Invitation
    reason: RejectionReason
    excuse_given: str
    true_reason: str
    harm_to_inviter: float    # 0-1 scale
    harm_to_decliner: float   # 0-1 scale
    convenience_excuse_coefficient: float  # 0-1, dishonesty factor
    anti_gile_score: float
    gile_dimensions_affected: Dict[str, float]
    recommendation: str


class InvitationEthicsAnalyzer:
    """
    Analyzes invitations and rejections through the GILE lens
    
    Core Thesis: Most rejections are ANTI-GILE and harm both parties.
    The convenience excuse is the most common form of social dishonesty.
    """
    
    # Convenience excuse patterns that are usually dishonest
    CONVENIENCE_EXCUSE_PATTERNS = [
        "no time",
        "too busy",
        "can't make it",
        "maybe next time",
        "let me check",      # Then never responds
        "i'll get back to you", # Then never does
        "not feeling well",   # When actually fine
        "have plans",         # But no specific plans
    ]
    
    # Activities that EVERYONE does anyway
    UNIVERSAL_ACTIVITIES = {
        "coffee": {
            "excuse": "No time for coffee",
            "reality": "You make coffee at home anyway",
            "time_cost_hours": 0.5,
            "dishonesty_coefficient": 0.9
        },
        "dinner": {
            "excuse": "No time for dinner",
            "reality": "You eat dinner anyway - you don't skip meals",
            "time_cost_hours": 1.5,
            "dishonesty_coefficient": 0.95
        },
        "lunch": {
            "excuse": "Working through lunch",
            "reality": "You eat lunch anyway",
            "time_cost_hours": 1.0,
            "dishonesty_coefficient": 0.85
        },
        "walk": {
            "excuse": "Too busy to walk",
            "reality": "You walk places anyway",
            "time_cost_hours": 0.5,
            "dishonesty_coefficient": 0.8
        },
        "call": {
            "excuse": "No time to talk",
            "reality": "You spend time on social media anyway",
            "time_cost_hours": 0.25,
            "dishonesty_coefficient": 0.9
        }
    }
    
    # The 10+ rejections threshold (from user's insight)
    REJECTION_THRESHOLD = 10
    
    def __init__(self):
        self.rejection_history: List[RejectionAnalysis] = []
        
    def analyze_rejection(self, invitation: Invitation, 
                         excuse_given: str, 
                         true_reason: Optional[str] = None) -> RejectionAnalysis:
        """
        Analyze a rejection decision for its GILE implications
        
        Args:
            invitation: The invitation being declined
            excuse_given: What you told the person
            true_reason: What you actually felt (if different)
        
        Returns:
            Complete analysis of the rejection's anti-GILE score
        """
        # Detect if this is a convenience excuse
        cec = self._calculate_convenience_excuse_coefficient(
            excuse_given, 
            invitation.activity,
            invitation.convenience_level
        )
        
        # Determine the real reason
        reason = self._classify_reason(excuse_given, true_reason, cec)
        
        # Calculate harm to both parties
        harm_inviter = self._calculate_inviter_harm(invitation, reason)
        harm_decliner = self._calculate_decliner_harm(invitation, reason)
        
        # Calculate GILE dimension impacts
        gile_impacts = self._calculate_gile_impacts(invitation, reason, cec)
        
        # Total anti-GILE score (higher = worse)
        anti_gile = self._calculate_total_anti_gile(
            harm_inviter, harm_decliner, cec, invitation.connection_value
        )
        
        # Generate recommendation
        recommendation = self._generate_recommendation(
            invitation, reason, anti_gile, cec
        )
        
        analysis = RejectionAnalysis(
            invitation=invitation,
            reason=reason,
            excuse_given=excuse_given,
            true_reason=true_reason or excuse_given,
            harm_to_inviter=harm_inviter,
            harm_to_decliner=harm_decliner,
            convenience_excuse_coefficient=cec,
            anti_gile_score=anti_gile,
            gile_dimensions_affected=gile_impacts,
            recommendation=recommendation
        )
        
        self.rejection_history.append(analysis)
        return analysis
    
    def _calculate_convenience_excuse_coefficient(self, excuse: str, 
                                                  activity: str,
                                                  convenience: float) -> float:
        """
        Calculate how dishonest a convenience excuse is
        
        Higher = more dishonest
        """
        cec = 0.0
        excuse_lower = excuse.lower()
        
        # Check against known excuse patterns
        for pattern in self.CONVENIENCE_EXCUSE_PATTERNS:
            if pattern in excuse_lower:
                cec = max(cec, 0.7)
                break
        
        # Check if this is a universal activity
        activity_lower = activity.lower()
        for activity_key, info in self.UNIVERSAL_ACTIVITIES.items():
            if activity_key in activity_lower:
                cec = max(cec, info['dishonesty_coefficient'])
                break
        
        # If highly convenient but still declined, likely an excuse
        if convenience > 0.8:
            cec = max(cec, convenience * 0.9)
        
        return min(cec, 1.0)
    
    def _classify_reason(self, excuse: str, true_reason: Optional[str], 
                        cec: float) -> RejectionReason:
        """Classify the real reason for rejection"""
        if cec > 0.8:
            return RejectionReason.CONVENIENCE_EXCUSE
        elif cec > 0.5:
            return RejectionReason.LAZINESS
        elif true_reason and "afraid" in true_reason.lower():
            return RejectionReason.FEAR
        elif true_reason and "better" in true_reason.lower():
            return RejectionReason.ARROGANCE
        elif cec < 0.2:
            return RejectionReason.GENUINE_CONFLICT
        else:
            return RejectionReason.CONVENIENCE_EXCUSE
    
    def _calculate_inviter_harm(self, invitation: Invitation, 
                               reason: RejectionReason) -> float:
        """
        Calculate harm to the person who invited
        
        Harm includes:
        - Humiliation from rejection
        - Discouragement from future inviting
        - Loneliness from failed connection attempt
        """
        base_harm = 0.3  # Baseline hurt from any rejection
        
        # Romantic rejections hurt most
        if invitation.invitation_type == InvitationType.ROMANTIC:
            base_harm += 0.4
        
        # Convenience excuses add insult to injury
        if reason == RejectionReason.CONVENIENCE_EXCUSE:
            base_harm += 0.2  # They know it's fake
        
        # High connection value = more was at stake
        base_harm += invitation.connection_value * 0.2
        
        return min(base_harm, 1.0)
    
    def _calculate_decliner_harm(self, invitation: Invitation,
                                reason: RejectionReason) -> float:
        """
        Calculate harm to the person who declined
        
        Harm includes:
        - Missed connection opportunity
        - Reinforced isolation patterns
        - Karma accumulation (though Karma doesn't exist per TI Framework,
          the pattern of rejection breeds arrogance)
        - Atrophy of social skills
        """
        harm = 0.0
        
        # Missing high-value connections hurts you
        harm += invitation.connection_value * 0.4
        
        # Convenience excuses corrupt your character
        if reason == RejectionReason.CONVENIENCE_EXCUSE:
            harm += 0.3  # Dishonesty degrades soul
        
        # Arrogance compounds over time
        if reason == RejectionReason.ARROGANCE:
            harm += 0.4  # Creates isolation spiral
        
        # Easy invitations rejected = wasted opportunity
        harm += invitation.convenience_level * 0.2
        
        return min(harm, 1.0)
    
    def _calculate_gile_impacts(self, invitation: Invitation,
                               reason: RejectionReason,
                               cec: float) -> Dict[str, float]:
        """
        Calculate impact on each GILE dimension
        
        Negative values = harm to that dimension
        """
        impacts = {
            'goodness': 0.0,
            'intuition': 0.0,
            'love': 0.0,
            'environment': 0.0
        }
        
        # GOODNESS: Dishonesty hurts this dimension
        if cec > 0.5:
            impacts['goodness'] = -cec * 0.8  # Lying is anti-G
        if reason == RejectionReason.ARROGANCE:
            impacts['goodness'] = -0.7  # Pride is anti-G
        
        # INTUITION: Rejecting spontaneous invitations hurts this
        if invitation.invitation_type == InvitationType.SPONTANEOUS:
            impacts['intuition'] = -0.5  # Ignoring flow states
        # Rejections train you to ignore social intuition
        impacts['intuition'] -= 0.2
        
        # LOVE: This is the primary dimension harmed
        impacts['love'] = -0.6  # All rejections hurt love
        if invitation.invitation_type == InvitationType.ROMANTIC:
            impacts['love'] = -0.9  # Romantic rejections devastate love
        if invitation.invitation_type == InvitationType.FRIENDSHIP:
            impacts['love'] = -0.5
        
        # ENVIRONMENT: Your social environment degrades
        impacts['environment'] = -0.3  # Fewer connections = worse environment
        if self._get_rejection_count() > self.REJECTION_THRESHOLD:
            impacts['environment'] = -0.7  # Pattern of rejection = toxic environment
        
        return impacts
    
    def _calculate_total_anti_gile(self, harm_inviter: float, 
                                   harm_decliner: float,
                                   cec: float,
                                   connection_value: float) -> float:
        """
        Calculate total Anti-GILE score
        
        Formula: IRC * (1 + CEC) / max(COV, 0.1)
        
        Where:
        - IRC = Invitation Rejection Cost = harm_inviter + harm_decliner
        - CEC = Convenience Excuse Coefficient
        - COV = Connection Opportunity Value
        """
        irc = harm_inviter + harm_decliner
        cov = max(connection_value, 0.1)  # Avoid division by zero
        
        anti_gile = irc * (1 + cec) / cov
        
        # Scale to 0-10 range
        return min(anti_gile * 2, 10.0)
    
    def _generate_recommendation(self, invitation: Invitation,
                                reason: RejectionReason,
                                anti_gile: float,
                                cec: float) -> str:
        """Generate actionable recommendation"""
        
        if reason == RejectionReason.GENUINE_CONFLICT:
            return "This appears to be a genuine conflict. Rejection is justified, but offer an alternative time."
        
        if reason == RejectionReason.LEGITIMATE_BOUNDARY:
            return "Boundary setting is healthy. This rejection is GILE-positive."
        
        if anti_gile > 7:
            return f"CRITICAL: This rejection has Anti-GILE score of {anti_gile:.1f}. Strongly reconsider. The harm to both parties is severe."
        
        if anti_gile > 4:
            return f"WARNING: Anti-GILE score of {anti_gile:.1f}. This rejection is harmful. Consider accepting - it costs less than you think."
        
        if cec > 0.8:
            activity = invitation.activity.lower()
            if "coffee" in activity:
                return "You make coffee at home anyway! Going with someone costs no extra time. Accept this."
            if "dinner" in activity:
                return "You eat dinner anyway - you don't skip meals! Share that time with someone. Accept this."
            if "lunch" in activity:
                return "You eat lunch anyway. Why not eat it with someone? Accept this."
            return f"Your excuse has a dishonesty coefficient of {cec:.0%}. Be honest with yourself and accept."
        
        return f"Anti-GILE score: {anti_gile:.1f}. Consider whether rejection is truly necessary."
    
    def _get_rejection_count(self) -> int:
        """Get total rejections in history"""
        return len(self.rejection_history)
    
    def get_rejection_pattern_analysis(self) -> Dict:
        """
        Analyze patterns in rejection history
        
        Key insight: If you've rejected 10+ people (romantic context),
        you're being anti-Love/anti-Goodness
        """
        if not self.rejection_history:
            return {"status": "No rejection history to analyze"}
        
        total = len(self.rejection_history)
        avg_anti_gile = sum(r.anti_gile_score for r in self.rejection_history) / total
        
        by_type = {}
        for r in self.rejection_history:
            t = r.invitation.invitation_type.value
            if t not in by_type:
                by_type[t] = 0
            by_type[t] += 1
        
        convenience_excuse_rate = sum(
            1 for r in self.rejection_history 
            if r.convenience_excuse_coefficient > 0.7
        ) / total
        
        # Check the 10+ threshold for romantic
        romantic_rejections = by_type.get('romantic', 0)
        threshold_warning = None
        if romantic_rejections >= self.REJECTION_THRESHOLD:
            threshold_warning = (
                f"You have rejected {romantic_rejections} romantic invitations. "
                "This pattern is anti-Love and anti-Goodness. It breeds arrogance, "
                "humiliation (in those you reject), and loneliness (in both of you). "
                "Consider lowering your standards and accepting more invitations."
            )
        
        return {
            "total_rejections": total,
            "average_anti_gile_score": round(avg_anti_gile, 2),
            "rejections_by_type": by_type,
            "convenience_excuse_rate": f"{convenience_excuse_rate:.0%}",
            "threshold_warning": threshold_warning,
            "cumulative_love_damage": sum(
                r.gile_dimensions_affected['love'] for r in self.rejection_history
            ),
            "recommendation": self._get_pattern_recommendation(
                avg_anti_gile, convenience_excuse_rate, romantic_rejections
            )
        }
    
    def _get_pattern_recommendation(self, avg_anti_gile: float,
                                    excuse_rate: float,
                                    romantic_rejections: int) -> str:
        """Generate overall pattern recommendation"""
        if romantic_rejections >= self.REJECTION_THRESHOLD:
            return (
                "CRITICAL: Your rejection pattern indicates anti-GILE behavior. "
                "You are harming yourself and others. Start saying YES to invitations. "
                "The coffee costs nothing. The dinner happens anyway. "
                "The only thing missing is connection - which you're denying yourself."
            )
        
        if excuse_rate > 0.7:
            return (
                "You frequently use convenience excuses. This is a form of social "
                "dishonesty that degrades your Goodness dimension. Be honest about "
                "your reasons or, better yet, just accept the invitations."
            )
        
        if avg_anti_gile > 5:
            return (
                "Your rejections have high Anti-GILE scores. Consider that acceptance "
                "often costs less than you imagine, while rejection costs more than you realize."
            )
        
        return "Your rejection patterns are within acceptable ranges, but always lean toward acceptance."


class DunkinDonutsTheorem:
    """
    The Dunkin' Donuts Theorem (Brandon Emerick, 2025)
    
    If an activity:
    1. Is "on the way" to something you're already doing
    2. Involves something you do anyway (coffee, food, etc.)
    3. Adds social connection to a solo activity
    
    Then rejection is NEVER justified on time/convenience grounds.
    
    Proof:
    - You're going to work anyway (path is set)
    - You're going to have coffee anyway (activity is set)
    - The ONLY difference is: alone vs. with someone
    - Choosing "alone" when "with someone" costs nothing extra is anti-Love
    
    QED: The excuse "no time for coffee" when Dunkin' is on your commute is dishonest.
    """
    
    @staticmethod
    def evaluate(activity: str, on_the_way: bool, 
                 do_anyway: bool, current_plan_solo: bool) -> Dict:
        """
        Evaluate if an invitation meets Dunkin' Donuts Theorem criteria
        
        If all three conditions are True, rejection is unjustified.
        """
        theorem_applies = on_the_way and do_anyway and current_plan_solo
        
        if theorem_applies:
            return {
                "theorem_applies": True,
                "rejection_justified": False,
                "dishonesty_if_rejected": 0.95,
                "explanation": (
                    f"You're already going that way. You're already going to {activity}. "
                    "The only thing you're rejecting is COMPANY. "
                    "This is anti-Love disguised as time management."
                ),
                "recommendation": "ACCEPT. There is no legitimate excuse."
            }
        else:
            missing = []
            if not on_the_way:
                missing.append("not on the way")
            if not do_anyway:
                missing.append("activity not planned anyway")
            if not current_plan_solo:
                missing.append("already have company planned")
            
            return {
                "theorem_applies": False,
                "rejection_justified": True if len(missing) >= 2 else "Maybe",
                "dishonesty_if_rejected": 0.3 if len(missing) >= 2 else 0.6,
                "explanation": f"Theorem doesn't fully apply: {', '.join(missing)}",
                "recommendation": "Consider accepting anyway, but rejection is less egregious."
            }


class SkippingDinnerFallacy:
    """
    The "Skipping Dinner" Fallacy (Brandon Emerick, 2025)
    
    The claim: "I don't have time for dinner"
    The reality: You eat dinner anyway. You don't skip meals.
    
    This fallacy exposes the dishonesty of time-based rejection excuses.
    When someone says "no time for dinner," what they mean is:
    - "I don't want to have dinner WITH YOU"
    - "I want to eat alone" (anti-Love choice)
    - "I'm choosing isolation over connection"
    
    The only legitimate form of this excuse:
    - "I have dinner plans WITH SOMEONE ELSE"
    
    Even then, the meta-pattern matters:
    - If you ALWAYS have plans with someone else, you're not
    - If you FREQUENTLY reject, you're pattern-rejecting
    """
    
    @staticmethod
    def analyze_claim(claim: str, actual_dinner_plan: str) -> Dict:
        """
        Analyze a dinner rejection claim for fallacy
        
        Args:
            claim: What they said (e.g., "No time for dinner")
            actual_dinner_plan: What they actually did (e.g., "Ate alone watching TV")
        """
        is_fallacy = False
        fallacy_severity = 0.0
        
        claim_lower = claim.lower()
        
        # Detect time-based excuses
        time_excuses = ["no time", "too busy", "can't make time", "working late"]
        if any(excuse in claim_lower for excuse in time_excuses):
            # Check if they actually ate
            actual_lower = actual_dinner_plan.lower()
            solo_activities = ["alone", "by myself", "at desk", "watching tv", "ordered in", "delivery"]
            
            if any(solo in actual_lower for solo in solo_activities):
                is_fallacy = True
                fallacy_severity = 0.95
            elif "with" in actual_lower and "someone else" in actual_lower:
                is_fallacy = False
                fallacy_severity = 0.1
            else:
                is_fallacy = True
                fallacy_severity = 0.7
        
        return {
            "is_fallacy": is_fallacy,
            "fallacy_severity": fallacy_severity,
            "claim": claim,
            "actual": actual_dinner_plan,
            "explanation": (
                "You ate dinner anyway. 'No time' meant 'no time WITH YOU.' "
                "This is anti-Love disguised as productivity."
                if is_fallacy else
                "This may be a legitimate schedule conflict."
            ),
            "recommendation": (
                "Next time, be honest: 'I'd prefer to eat alone tonight.' "
                "Then examine why that's your preference."
                if is_fallacy else
                "No dishonesty detected in this instance."
            )
        }


# Integration with GILE scoring
def calculate_social_gile_adjustment(invitation_ethics: InvitationEthicsAnalyzer) -> Dict:
    """
    Calculate GILE adjustment based on invitation acceptance patterns
    
    High rejection patterns = lower overall GILE
    High acceptance patterns = higher overall GILE (especially Love dimension)
    """
    pattern = invitation_ethics.get_rejection_pattern_analysis()
    
    if pattern.get("status") == "No rejection history to analyze":
        return {"adjustment": 0.0, "reason": "No data"}
    
    avg_anti_gile = pattern.get("average_anti_gile_score", 0)
    
    # Convert anti-GILE to GILE adjustment
    # High anti-GILE = negative adjustment
    adjustment = -0.1 * avg_anti_gile
    
    return {
        "gile_adjustment": round(adjustment, 3),
        "love_dimension_adjustment": round(pattern.get("cumulative_love_damage", 0) / 10, 3),
        "source": "invitation_ethics_framework",
        "pattern_summary": pattern
    }


# Example usage and demonstration
if __name__ == "__main__":
    print("=" * 60)
    print("INVITATION ETHICS FRAMEWORK")
    print("A GILE Extension for Social Connection")
    print("=" * 60)
    
    analyzer = InvitationEthicsAnalyzer()
    
    # Example 1: Dunkin Donuts coffee (on the way to work)
    print("\n--- Example 1: Dunkin' Donuts Coffee ---")
    inv1 = Invitation(
        invitation_type=InvitationType.FRIENDSHIP,
        inviter_name="Coworker Sarah",
        activity="Coffee at Dunkin' on the way to work",
        convenience_level=0.95,  # Extremely convenient
        connection_value=0.6,
        time_required_hours=0.25
    )
    
    result1 = analyzer.analyze_rejection(
        inv1,
        excuse_given="Sorry, no time this morning",
        true_reason="I prefer making coffee at home alone"
    )
    
    print(f"Anti-GILE Score: {result1.anti_gile_score:.1f}/10")
    print(f"Convenience Excuse Coefficient: {result1.convenience_excuse_coefficient:.0%}")
    print(f"Harm to Inviter: {result1.harm_to_inviter:.0%}")
    print(f"Harm to Decliner: {result1.harm_to_decliner:.0%}")
    print(f"Recommendation: {result1.recommendation}")
    
    # Example 2: Dinner invitation
    print("\n--- Example 2: Dinner Invitation ---")
    inv2 = Invitation(
        invitation_type=InvitationType.ROMANTIC,
        inviter_name="Date prospect",
        activity="Dinner at a nice restaurant",
        convenience_level=0.7,
        connection_value=0.8,
        time_required_hours=2.0
    )
    
    result2 = analyzer.analyze_rejection(
        inv2,
        excuse_given="I don't really have time for dinner this week",
        true_reason="I'm nervous and would rather eat alone"
    )
    
    print(f"Anti-GILE Score: {result2.anti_gile_score:.1f}/10")
    print(f"Convenience Excuse Coefficient: {result2.convenience_excuse_coefficient:.0%}")
    print(f"Recommendation: {result2.recommendation}")
    
    # Dunkin' Donuts Theorem
    print("\n--- Dunkin' Donuts Theorem Evaluation ---")
    dunkin_result = DunkinDonutsTheorem.evaluate(
        activity="coffee",
        on_the_way=True,
        do_anyway=True,
        current_plan_solo=True
    )
    print(f"Theorem Applies: {dunkin_result['theorem_applies']}")
    print(f"Rejection Justified: {dunkin_result['rejection_justified']}")
    print(f"Explanation: {dunkin_result['explanation']}")
    
    # Skipping Dinner Fallacy
    print("\n--- Skipping Dinner Fallacy Analysis ---")
    fallacy_result = SkippingDinnerFallacy.analyze_claim(
        claim="I don't have time for dinner tonight",
        actual_dinner_plan="Ate alone watching Netflix"
    )
    print(f"Is Fallacy: {fallacy_result['is_fallacy']}")
    print(f"Severity: {fallacy_result['fallacy_severity']:.0%}")
    print(f"Explanation: {fallacy_result['explanation']}")
    
    print("\n" + "=" * 60)
    print("CORE INSIGHT: Every rejection harms BOTH parties.")
    print("The coffee is on the way. The dinner happens anyway.")
    print("What you're really rejecting is CONNECTION.")
    print("=" * 60)
