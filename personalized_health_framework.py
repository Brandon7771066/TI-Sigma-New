"""
Personalized Health Framework - Debunking Universal Health Advice

Core Thesis: There are NO universal "healthy vs unhealthy" foods, exercise routines,
or sleep prescriptions. Individual variation matters more than any general rule.

Evidence:
- Warren Buffett (95): "Terrible" diet of junk food, vital to his wellbeing
- Mimi (93): Very little food, much junk food in old age
- Jeanne Calment (122): Ate chocolate, smoked for much of her life

The LCC Virus approach: Decode individual i-cells to determine person-specific
optimal protocols rather than following generic advice.
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from enum import Enum
from datetime import datetime


class HealthDomain(Enum):
    DIET = "diet"
    EXERCISE = "exercise"
    SLEEP = "sleep"
    STRESS = "stress"
    SOCIAL = "social"
    PURPOSE = "purpose"


class MotivationType(Enum):
    INTRINSIC = "intrinsic"  # Joy, play, genuine desire
    EXTRINSIC = "extrinsic"  # Should, guilt, showing off


@dataclass
class LongevityOutlier:
    """People who defy conventional health wisdom yet lived exceptionally long"""
    name: str
    age_reached: int
    unconventional_behaviors: List[str]
    possible_explanations: List[str]
    ti_interpretation: str


LONGEVITY_OUTLIERS = {
    "warren_buffett": LongevityOutlier(
        name="Warren Buffett",
        age_reached=95,
        unconventional_behaviors=[
            "Diet primarily of hamburgers, Coca-Cola, and ice cream",
            "Minimal exercise beyond walking",
            "Claims junk food is vital to his wellbeing"
        ],
        possible_explanations=[
            "Extreme stress reduction through financial security",
            "Genuine enjoyment/GILE from his diet choices",
            "Strong purpose/meaning in life (L and G dimensions)",
            "Low cortisol from doing what he loves daily"
        ],
        ti_interpretation="His i-cell is optimized for his specific diet - forcing 'healthy' food would increase stress and reduce GILE"
    ),
    "mimi": LongevityOutlier(
        name="Mimi (Grandmother)",
        age_reached=93,
        unconventional_behaviors=[
            "Very little food intake in old age",
            "Much junk food when she did eat",
            "No structured exercise program"
        ],
        possible_explanations=[
            "Caloric restriction (even if unintentional) linked to longevity",
            "Low metabolic stress from reduced eating",
            "Family/social connection maintaining GILE",
            "Generation with less chronic stress exposure"
        ],
        ti_interpretation="Her VESSEL layer had lower caloric needs - forcing more 'nutritious' food could have overloaded her system"
    ),
    "jeanne_calment": LongevityOutlier(
        name="Jeanne Calment",
        age_reached=122,  # Oldest verified human ever
        unconventional_behaviors=[
            "Ate 2+ pounds of chocolate per week",
            "Smoked for ~100 years (quit at 117)",
            "Drank port wine regularly",
            "Rode bicycle until age 100"
        ],
        possible_explanations=[
            "Exceptional genetic factors (very low stress response genes)",
            "Genuine enjoyment of life activities (high GILE)",
            "Strong social connections in French culture",
            "Never exercised out of guilt or obligation"
        ],
        ti_interpretation="Her SOUL layer coherence was so high that VESSEL-level 'damage' was continuously repaired by GM-connected healing"
    )
}


@dataclass
class HealthMyth:
    """A commonly believed health 'truth' that is actually oversimplified"""
    myth: str
    domain: HealthDomain
    conventional_advice: str
    reality: str
    individual_variation: str
    ti_framework_insight: str
    exceptions: List[str]


HEALTH_MYTHS = {
    "universal_healthy_food": HealthMyth(
        myth="Some foods are universally 'healthy' and others 'unhealthy'",
        domain=HealthDomain.DIET,
        conventional_advice="Eat vegetables, avoid processed foods, limit sugar",
        reality="How much diet affects health varies person-to-person AND food-to-food",
        individual_variation="Some people thrive on carnivore diets, others on vegan; some tolerate sugar well, others don't",
        ti_framework_insight="Each i-cell has unique VESSEL layer requirements - what's 'healthy' depends on YOUR specific biochemistry",
        exceptions=["Warren Buffett", "Mimi", "Jeanne Calment", "Inuit traditional diet", "Okinawan centenarians"]
    ),
    "diet_importance": HealthMyth(
        myth="Diet is one of the most important factors in health",
        domain=HealthDomain.DIET,
        conventional_advice="Focus heavily on what you eat",
        reality="The IMPORTANCE and DELICIOUSNESS of diet to one's life matters more than nutritional content",
        individual_variation="For some, food is fuel; for others, it's deep connection, culture, and joy",
        ti_framework_insight="Food enjoyment directly affects L (Love) and E (Energy) dimensions - guilt about eating reduces GILE more than 'bad' food",
        exceptions=["Cultural food traditions in Blue Zones", "Emotional eating that provides genuine comfort"]
    ),
    "exercise_is_always_good": HealthMyth(
        myth="More exercise is always better for health",
        domain=HealthDomain.EXERCISE,
        conventional_advice="Get 150+ minutes of moderate exercise per week",
        reality="Exercise can WORSEN wellbeing if it causes stress, compulsion, or guilt",
        individual_variation="Intrinsic motivation vs extrinsic motivation completely changes the health effect",
        ti_framework_insight="Exercise from extrinsic motivation (should, guilt, showing off) activates anti-GILE stress pathways, negating physical benefits",
        exceptions=["Obsessive gym-goers with worse mental health", "Sedentary but low-stress individuals who live long"]
    ),
    "gym_superiority": HealthMyth(
        myth="Heavy gym workouts are necessary for fitness",
        domain=HealthDomain.EXERCISE,
        conventional_advice="Weight training, HIIT, structured workout programs",
        reality="Brisk walking and yoga would mostly suffice for most health goals",
        individual_variation="Some people genuinely enjoy gym; others find it torturous",
        ti_framework_insight="The VESSEL layer benefits most from movement that doesn't stress the ME layer (mental/emotional)",
        exceptions=["Athletes", "Those with genuine gym enjoyment", "Specific medical conditions"]
    ),
    "asocial_exercise": HealthMyth(
        myth="Individual exercise programs are effective",
        domain=HealthDomain.EXERCISE,
        conventional_advice="Follow a personal workout plan",
        reality="Exercise interventions fail because they're asocial and often about showing off",
        individual_variation="Social play (tag, sports, games) activates different motivational circuits than solo gym work",
        ti_framework_insight="Exercise through GAMES with neighbors activates L (Love/connection) AND E (Energy) - double GILE benefit",
        exceptions=["Introverts who genuinely prefer solo activity", "Meditation/yoga practitioners"]
    ),
    "seven_hours_sleep": HealthMyth(
        myth="Everyone needs 7-8 hours of sleep",
        domain=HealthDomain.SLEEP,
        conventional_advice="Get 7-8 hours every night",
        reality="Individual sleep needs vary from 4-9+ hours based on genetics",
        individual_variation="Some need 9 hours, others only 4-6 (genetic mutations in DEC2/ADRB1 genes)",
        ti_framework_insight="VESSEL layer repair cycles vary by i-cell - forcing 'standard' sleep can cause more stress than benefit",
        exceptions=["Short sleepers (genetic)", "Long sleepers (genetic)", "Variable sleepers (circadian flexibility)"]
    ),
    "sleep_quality_advice": HealthMyth(
        myth="'Get better sleep' is actionable advice",
        domain=HealthDomain.SLEEP,
        conventional_advice="Improve your sleep hygiene",
        reality="Most people don't quantify OR improve sleep quality - advice is meaningless without measurement",
        individual_variation="Sleep quality factors vary: temperature, light, sound, stress, digestion, breathing all differ by person",
        ti_framework_insight="Sleep is when VESSEL and ME layers repair - without measuring YOUR specific disruptors, generic advice fails",
        exceptions=["Those with sleep trackers and data", "Sleep apnea patients with CPAP data"]
    )
}


@dataclass 
class ExerciseIntervention:
    """Comparison of exercise approaches"""
    name: str
    motivation_type: MotivationType
    social_component: bool
    gile_impact: Dict[str, float]  # G, I, L, E scores
    sustainability: float  # 0-1 how likely to stick with it
    stress_risk: float  # 0-1 how likely to cause negative stress


EXERCISE_APPROACHES = {
    "gym_solo": ExerciseIntervention(
        name="Solo Gym Workout",
        motivation_type=MotivationType.EXTRINSIC,
        social_component=False,
        gile_impact={"G": 0.1, "I": 0.0, "L": -0.1, "E": 0.3},
        sustainability=0.2,  # Most people quit
        stress_risk=0.6  # Guilt, comparison, obligation
    ),
    "gym_social": ExerciseIntervention(
        name="Gym with Friends",
        motivation_type=MotivationType.INTRINSIC,
        social_component=True,
        gile_impact={"G": 0.2, "I": 0.1, "L": 0.4, "E": 0.4},
        sustainability=0.5,
        stress_risk=0.3
    ),
    "brisk_walking": ExerciseIntervention(
        name="Brisk Walking",
        motivation_type=MotivationType.INTRINSIC,
        social_component=False,
        gile_impact={"G": 0.2, "I": 0.3, "L": 0.1, "E": 0.3},
        sustainability=0.7,
        stress_risk=0.1
    ),
    "yoga": ExerciseIntervention(
        name="Yoga Practice",
        motivation_type=MotivationType.INTRINSIC,
        social_component=False,
        gile_impact={"G": 0.3, "I": 0.4, "L": 0.2, "E": 0.2},
        sustainability=0.6,
        stress_risk=0.1
    ),
    "neighborhood_games": ExerciseIntervention(
        name="Games with Neighbors (tag, capture the flag, sports)",
        motivation_type=MotivationType.INTRINSIC,
        social_component=True,
        gile_impact={"G": 0.4, "I": 0.3, "L": 0.8, "E": 0.5},  # Highest L!
        sustainability=0.8,  # Fun = sustainable
        stress_risk=0.05  # Play rarely causes stress
    ),
    "sports_league": ExerciseIntervention(
        name="Local Sports League",
        motivation_type=MotivationType.INTRINSIC,
        social_component=True,
        gile_impact={"G": 0.3, "I": 0.2, "L": 0.6, "E": 0.5},
        sustainability=0.7,
        stress_risk=0.2  # Some competition stress
    )
}


@dataclass
class NeighborConnectionBarrier:
    """Barriers to building neighbor relationships"""
    barrier: str
    modern_cause: str
    ti_interpretation: str
    potential_solutions: List[str]


NEIGHBOR_BARRIERS = [
    NeighborConnectionBarrier(
        barrier="Apathy",
        modern_cause="Digital connection replacing physical; exhaustion from work",
        ti_interpretation="ME layer overwhelmed, insufficient E for new social investment",
        potential_solutions=[
            "Start with low-energy interactions (wave, nod)",
            "Find shared practical needs (tools, packages)",
            "Host simple gatherings (front yard, porch)"
        ]
    ),
    NeighborConnectionBarrier(
        barrier="Coldness",
        modern_cause="Fear of rejection, urban anonymity norms, past bad experiences",
        ti_interpretation="L dimension protection mechanism - walls prevent hurt",
        potential_solutions=[
            "Consistent small kindnesses over time",
            "Offer help without expectation",
            "Be vulnerable first (share struggles)"
        ]
    ),
    NeighborConnectionBarrier(
        barrier="Suspicion",
        modern_cause="Media fear narratives, stranger danger culture, crime awareness",
        ti_interpretation="G dimension uncertainty - unknown intent = assumed bad",
        potential_solutions=[
            "Slow trust-building through repeated presence",
            "Transparency about who you are and why you're there",
            "Introduce through mutual connections"
        ]
    )
]


class PersonalizedHealthAnalyzer:
    """System for generating person-specific health recommendations"""
    
    def __init__(self):
        self.myths = HEALTH_MYTHS
        self.outliers = LONGEVITY_OUTLIERS
        self.exercise_approaches = EXERCISE_APPROACHES
        self.neighbor_barriers = NEIGHBOR_BARRIERS
    
    def debunk_universal_advice(self, domain: HealthDomain) -> Dict:
        """Get all myth debunking for a health domain"""
        relevant_myths = {k: v for k, v in self.myths.items() 
                         if v.domain == domain}
        
        return {
            "domain": domain.value,
            "myths_debunked": len(relevant_myths),
            "details": [
                {
                    "myth": myth.myth,
                    "conventional_advice": myth.conventional_advice,
                    "reality": myth.reality,
                    "ti_insight": myth.ti_framework_insight,
                    "notable_exceptions": myth.exceptions
                }
                for myth in relevant_myths.values()
            ]
        }
    
    def get_optimal_exercise_for_gile(self, 
                                       prioritize_dimension: str = "L",
                                       must_be_social: bool = True) -> List[Dict]:
        """Recommend exercise based on GILE priorities"""
        
        candidates = []
        for name, approach in self.exercise_approaches.items():
            if must_be_social and not approach.social_component:
                continue
            
            score = approach.gile_impact.get(prioritize_dimension, 0)
            total_gile = sum(approach.gile_impact.values())
            
            candidates.append({
                "name": approach.name,
                f"{prioritize_dimension}_score": score,
                "total_gile": total_gile,
                "sustainability": approach.sustainability,
                "stress_risk": approach.stress_risk,
                "recommendation_score": score * approach.sustainability * (1 - approach.stress_risk)
            })
        
        return sorted(candidates, key=lambda x: x["recommendation_score"], reverse=True)
    
    def personalized_sleep_analysis(self, 
                                    your_ideal_hours: float,
                                    current_hours: float,
                                    quality_1_10: int) -> Dict:
        """Analyze your sleep relative to YOUR needs, not population averages"""
        
        sleep_debt = your_ideal_hours - current_hours
        quality_factor = quality_1_10 / 10
        
        effective_sleep = current_hours * quality_factor
        effective_debt = your_ideal_hours - effective_sleep
        
        return {
            "your_ideal": your_ideal_hours,
            "population_myth": "7-8 hours",
            "your_deviation_from_myth": your_ideal_hours - 7.5,
            "explanation": self._explain_sleep_variation(your_ideal_hours),
            "current_analysis": {
                "raw_hours": current_hours,
                "quality_adjusted_hours": effective_sleep,
                "effective_debt": effective_debt,
                "debt_severity": "critical" if effective_debt > 2 else "moderate" if effective_debt > 1 else "minimal"
            },
            "ti_insight": "Sleep is VESSEL layer repair - YOUR ideal is based on YOUR repair needs, not averages"
        }
    
    def _explain_sleep_variation(self, hours: float) -> str:
        if hours <= 5:
            return "You may have short-sleeper genetics (DEC2/ADRB1 mutations) - rare but real"
        elif hours <= 6:
            return "On the shorter end of normal - ensure high quality over quantity"
        elif hours <= 8:
            return "Within typical range - still varies by individual"
        elif hours <= 9:
            return "Long-sleeper phenotype - your brain may process more during sleep"
        else:
            return "Extended sleep need - may indicate higher recovery requirements or underlying condition"
    
    def neighbor_connection_strategy(self) -> Dict:
        """Generate strategy for building neighbor relationships"""
        
        return {
            "core_insight": "Social exercise (games with neighbors) provides 2x GILE benefit vs solo gym",
            "barriers_analysis": [
                {
                    "barrier": b.barrier,
                    "cause": b.modern_cause,
                    "ti_interpretation": b.ti_interpretation,
                    "solutions": b.potential_solutions
                }
                for b in self.neighbor_barriers
            ],
            "recommended_games": [
                "Tag (cardio + laughter + connection)",
                "Capture the flag (strategy + teams + movement)",
                "Volleyball/badminton (low barrier, all ages)",
                "Frisbee (casual, conversational)",
                "Walking groups (low intensity, high connection)"
            ],
            "first_steps": [
                "1. Identify 2-3 neighbors you've at least waved to",
                "2. Propose a simple outdoor activity (not 'exercise')",
                "3. Frame as fun/play, never as 'working out'",
                "4. Start with one-time event, let it grow organically"
            ],
            "gile_projection": {
                "solo_gym_monthly": {"G": 0.1, "I": 0.0, "L": -0.1, "E": 0.3},
                "neighbor_games_monthly": {"G": 0.4, "I": 0.3, "L": 0.8, "E": 0.5},
                "improvement": "+0.3 G, +0.3 I, +0.9 L, +0.2 E"
            }
        }
    
    def generate_personalized_protocol(self, 
                                        sleep_hours_needed: float,
                                        diet_enjoyment_importance: float,  # 0-1
                                        exercise_motivation: MotivationType,
                                        social_preference: float) -> Dict:  # 0-1
        """Generate fully personalized health protocol"""
        
        return {
            "sleep_protocol": {
                "target_hours": sleep_hours_needed,
                "ignore_advice": "7-8 hours for everyone",
                "focus_on": "Quality measurement (HRV during sleep, sleep stages)"
            },
            "diet_protocol": {
                "if_high_enjoyment_importance": diet_enjoyment_importance > 0.6,
                "recommendation": "Prioritize ENJOYMENT over 'health' - stress reduction > nutrient optimization" 
                                  if diet_enjoyment_importance > 0.6 
                                  else "Balance enjoyment with nutritional goals",
                "ti_insight": "Your L and E dimensions benefit more from food joy than from 'clean eating'"
            },
            "exercise_protocol": {
                "motivation_type": exercise_motivation.value,
                "recommendation": self.get_optimal_exercise_for_gile(
                    prioritize_dimension="L" if social_preference > 0.5 else "E",
                    must_be_social=social_preference > 0.5
                )[:3],
                "avoid": "Any exercise that feels like obligation or causes guilt"
            },
            "meta_insight": "These recommendations are for YOUR i-cell based on YOUR inputs - "
                           "they would be different for anyone else"
        }


def render_personalized_health_ui():
    """Streamlit UI for personalized health framework"""
    import streamlit as st
    
    st.header("Personalized Health Framework")
    st.markdown("""
    **Debunking Universal Health Advice**
    
    There are NO universal "healthy vs unhealthy" rules. Individual variation 
    matters more than any generic advice.
    """)
    
    analyzer = PersonalizedHealthAnalyzer()
    
    tabs = st.tabs(["Longevity Outliers", "Health Myths", "Your Sleep", "Exercise Strategy", "Neighbor Connection"])
    
    with tabs[0]:
        st.subheader("People Who Defied Health 'Rules'")
        for outlier_id, outlier in LONGEVITY_OUTLIERS.items():
            with st.expander(f"{outlier.name} - Lived to {outlier.age_reached}"):
                st.markdown("**Unconventional Behaviors:**")
                for behavior in outlier.unconventional_behaviors:
                    st.markdown(f"- {behavior}")
                
                st.markdown("**Possible Explanations:**")
                for explanation in outlier.possible_explanations:
                    st.markdown(f"- {explanation}")
                
                st.info(f"**TI Interpretation:** {outlier.ti_interpretation}")
    
    with tabs[1]:
        st.subheader("Health Myths Debunked")
        
        domain = st.selectbox("Select Domain", [d.value for d in HealthDomain])
        
        debunking = analyzer.debunk_universal_advice(HealthDomain(domain))
        
        for detail in debunking['details']:
            with st.expander(f"MYTH: {detail['myth']}"):
                st.markdown(f"**Conventional Advice:** {detail['conventional_advice']}")
                st.markdown(f"**Reality:** {detail['reality']}")
                st.success(f"**TI Framework Insight:** {detail['ti_insight']}")
                st.markdown("**Notable Exceptions:** " + ", ".join(detail['notable_exceptions'][:3]))
    
    with tabs[2]:
        st.subheader("Your Personalized Sleep Analysis")
        
        col1, col2 = st.columns(2)
        with col1:
            ideal_hours = st.slider("Your Ideal Sleep Hours", 4.0, 12.0, 9.0, 0.5)
            current_hours = st.slider("Current Sleep Hours", 4.0, 12.0, 7.0, 0.5)
        with col2:
            quality = st.slider("Sleep Quality (1-10)", 1, 10, 6)
        
        if st.button("Analyze My Sleep"):
            analysis = analyzer.personalized_sleep_analysis(ideal_hours, current_hours, quality)
            
            st.metric("Your Ideal", f"{analysis['your_ideal']} hours")
            st.metric("Population Myth", analysis['population_myth'])
            st.metric("Your Deviation from Myth", f"{analysis['your_deviation_from_myth']:+.1f} hours")
            
            st.markdown(f"**Explanation:** {analysis['explanation']}")
            
            st.markdown("---")
            st.markdown("**Current Analysis:**")
            st.metric("Effective Sleep (Quality-Adjusted)", f"{analysis['current_analysis']['quality_adjusted_hours']:.1f} hours")
            st.metric("Effective Debt", f"{analysis['current_analysis']['effective_debt']:.1f} hours")
            
            if analysis['current_analysis']['debt_severity'] == 'critical':
                st.error("Critical sleep debt - prioritize sleep recovery")
            elif analysis['current_analysis']['debt_severity'] == 'moderate':
                st.warning("Moderate sleep debt - address when possible")
            else:
                st.success("Minimal sleep debt - good job!")
            
            st.info(analysis['ti_insight'])
    
    with tabs[3]:
        st.subheader("Exercise Strategy Based on GILE")
        
        col1, col2 = st.columns(2)
        with col1:
            priority = st.selectbox("Prioritize Dimension", ["L (Love/Connection)", "E (Energy)", "G (Goodness)", "I (Intuition)"])
            priority_letter = priority.split()[0]
        with col2:
            social_required = st.checkbox("Must be social", value=True)
        
        recommendations = analyzer.get_optimal_exercise_for_gile(priority_letter, social_required)
        
        st.markdown("**Top Recommendations:**")
        for i, rec in enumerate(recommendations[:3]):
            st.markdown(f"**{i+1}. {rec['name']}**")
            st.progress(rec['recommendation_score'])
            st.caption(f"Sustainability: {rec['sustainability']:.0%} | Stress Risk: {rec['stress_risk']:.0%}")
    
    with tabs[4]:
        st.subheader("Building Neighbor Connections")
        st.markdown("*Social exercise provides 2x GILE benefit vs solo gym*")
        
        strategy = analyzer.neighbor_connection_strategy()
        
        st.markdown("### Barriers You'll Face:")
        for barrier in strategy['barriers_analysis']:
            with st.expander(f"{barrier['barrier']}"):
                st.markdown(f"**Modern Cause:** {barrier['cause']}")
                st.info(f"**TI Interpretation:** {barrier['ti_interpretation']}")
                st.markdown("**Solutions:**")
                for sol in barrier['solutions']:
                    st.markdown(f"- {sol}")
        
        st.markdown("### Recommended Games:")
        for game in strategy['recommended_games']:
            st.markdown(f"- {game}")
        
        st.markdown("### First Steps:")
        for step in strategy['first_steps']:
            st.markdown(step)
        
        st.markdown("### GILE Comparison:")
        col1, col2 = st.columns(2)
        with col1:
            st.markdown("**Solo Gym (monthly):**")
            for dim, val in strategy['gile_projection']['solo_gym_monthly'].items():
                st.metric(dim, f"{val:+.1f}")
        with col2:
            st.markdown("**Neighbor Games (monthly):**")
            for dim, val in strategy['gile_projection']['neighbor_games_monthly'].items():
                st.metric(dim, f"{val:+.1f}")


if __name__ == "__main__":
    render_personalized_health_ui()
