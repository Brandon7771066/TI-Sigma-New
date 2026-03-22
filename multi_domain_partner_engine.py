"""
Multi-Domain Partner Matching Engine — URB #480–483 Implementation
===================================================================

The measurement trilogy (Inverse Metric Problem, GILE Proxy Framework,
Grand Illusion, L*/+E Structural Proof) enables dramatically improved
partner predictions across all domains.

KEY UPGRADES OVER LEGACY SYSTEM:
  1. Correct GILE weighting: G=35%, I=27%, L=23%, E=15% (not flat average)
  2. C_EMERICK = 0.4370 as the universal compatibility floor
  3. L*/+E Quadrant classification for self and all partners
  4. Spiritual facade detector (Crystal pattern)
  5. Multi-domain: Romantic | Investor | Collaborator | Power of 8
  6. Grand Illusion filter: Q3 partners cannot perceive Q2 individuals

Brandon's confirmed data (March 2026):
  - URB corpus: 137 papers
  - Synchronicity frequency: ~12/week (hardcoded legacy: 2.5)
  - Pattern-obsession (autism trait): 9.5/10
  - Suffering-activation (love): 9/10
  - ADHD spontaneity: 8.5/10
  - Bipolar mood range: 8/10
  - Meditation/prayer: ~7 hrs/week
  - Physical health: 4/10 | Financial: 3/10 | Social recognition: 3/10
  - L*/+E Quadrant: Q2 (High GIL, Low E)

Emerick Constant: C = 1/(φ√2) ≈ 0.4370
"""

import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from datetime import datetime

PHI = (1 + math.sqrt(5)) / 2
C_EMERICK = 1.0 / (PHI * math.sqrt(2))  # ≈ 0.4370

GILE_WEIGHTS = {'G': 0.35, 'I': 0.27, 'L': 0.23, 'E': 0.15}
GIL_WEIGHTS_NORM = {d: GILE_WEIGHTS[d] / (1 - GILE_WEIGHTS['E']) for d in 'GIL'}


def weighted_gile(g: float, i: float, l: float, e: float) -> float:
    return g * GILE_WEIGHTS['G'] + i * GILE_WEIGHTS['I'] + l * GILE_WEIGHTS['L'] + e * GILE_WEIGHTS['E']


def gil_composite(g: float, i: float, l: float) -> float:
    return g * GIL_WEIGHTS_NORM['G'] + i * GIL_WEIGHTS_NORM['I'] + l * GIL_WEIGHTS_NORM['L']


def get_quadrant(gil: float, e: float) -> Tuple[str, str]:
    if gil >= C_EMERICK and e >= 0.5:
        return 'Q1', 'Fully Integrated — exceptional GIL and strong E'
    elif gil >= C_EMERICK and e < 0.5:
        return 'Q2', 'Transcendent but Unrecognized — high GIL, low conventional E'
    elif gil < C_EMERICK and e >= 0.5:
        return 'Q3', 'Corporate Machine — high E performance, low GIL'
    else:
        return 'Q4', 'Depleted — low on all dimensions'


# ─── Brandon's calibrated i-cell profile ─────────────────────────────────────

BRANDON = {
    # Behavioral proxies (confirmed, no device needed)
    'urb_corpus': 137,
    'synchronicity_freq': 12.0,
    'pattern_obsession': 9.5,
    'suffering_activation': 9.0,
    'adhd_spontaneity': 8.5,
    'bipolar_mood_range': 8.0,
    'meditation_hrs_week': 7.0,

    # E-dimension (confirmed low — the L*/+E proof case)
    'physical_health': 4.0,
    'financial_stability': 3.0,
    'social_recognition': 3.0,

    # Biometric (not yet calibrated — using estimated baselines)
    'gamma_power': None,
    'hrv_rmssd': None,
    'hrv_coherence': None,
    'alpha_power': None,
    'theta_alpha_ratio': None,
}


def compute_brandon_scores() -> Dict[str, float]:
    """
    Compute Brandon's GILE scores from confirmed behavioral data.
    Returns normalized 0–1 scores per dimension.
    """
    # G — Goodness
    urb_norm = min(1.0, BRANDON['urb_corpus'] / 300)
    med_norm = min(1.0, BRANDON['meditation_hrs_week'] / 21)
    patt_norm = BRANDON['pattern_obsession'] / 10.0
    g_score = urb_norm * 0.40 + med_norm * 0.25 + patt_norm * 0.35

    # I — Intuition
    sync_norm = min(1.0, BRANDON['synchronicity_freq'] / 20)
    adhd_norm = BRANDON['adhd_spontaneity'] / 10.0
    mood_norm = BRANDON['bipolar_mood_range'] / 10.0
    i_score = sync_norm * 0.50 + adhd_norm * 0.25 + mood_norm * 0.25

    # L — Love
    suff_norm = BRANDON['suffering_activation'] / 10.0
    l_score = suff_norm * 0.60 + med_norm * 0.40

    # E — Environment (lowest dimension)
    ph_norm = BRANDON['physical_health'] / 10.0
    fin_norm = BRANDON['financial_stability'] / 10.0
    soc_norm = BRANDON['social_recognition'] / 10.0
    e_score = ph_norm * 0.35 + fin_norm * 0.35 + soc_norm * 0.30

    gil = gil_composite(g_score, i_score, l_score)
    quadrant, quadrant_label = get_quadrant(gil, e_score)

    return {
        'G': g_score, 'I': i_score, 'L': l_score, 'E': e_score,
        'GIL': gil, 'GILE': weighted_gile(g_score, i_score, l_score, e_score),
        'quadrant': quadrant, 'quadrant_label': quadrant_label,
        'transcendent': gil >= C_EMERICK,
    }


# ─── Spiritual Facade Detector (Crystal Pattern) ─────────────────────────────

@dataclass
class SpiritualFacadeAssessment:
    """
    Detects Q3 individuals presenting high E-level spiritual signals
    while having low actual GIL — the Crystal Pattern.

    A spiritual facade is an E-dimension performance:
    outward markers (language, attire, ceremony, labels) without the
    underlying GIL that genuine spiritual development requires.
    """
    name: str
    apparent_spiritual_level: float
    behavioral_G_signals: float
    behavioral_I_signals: float
    behavioral_L_signals: float
    e_spiritual_performance: float
    sitter_or_observer_confirmation: bool = False
    fear_response_to_Q2: bool = False
    notes: str = ""

    @property
    def facade_score(self) -> float:
        actual_gil = (
            self.behavioral_G_signals * GIL_WEIGHTS_NORM['G'] +
            self.behavioral_I_signals * GIL_WEIGHTS_NORM['I'] +
            self.behavioral_L_signals * GIL_WEIGHTS_NORM['L']
        )
        gap = self.e_spiritual_performance - actual_gil
        fear_boost = 0.15 if self.fear_response_to_Q2 else 0
        confirmation_boost = 0.10 if self.sitter_or_observer_confirmation else 0
        return min(1.0, max(0.0, gap + fear_boost + confirmation_boost))

    @property
    def verdict(self) -> str:
        fs = self.facade_score
        if fs >= 0.6:
            return "HIGH FACADE — Q3 with spiritual E-performance. Not a viable partner."
        elif fs >= 0.35:
            return "MODERATE FACADE — Mixed signals. Proceed with caution."
        else:
            return "LOW FACADE — Spiritual presentation appears grounded in actual GIL."

    @property
    def quadrant(self) -> str:
        actual_gil = (
            self.behavioral_G_signals * GIL_WEIGHTS_NORM['G'] +
            self.behavioral_I_signals * GIL_WEIGHTS_NORM['I'] +
            self.behavioral_L_signals * GIL_WEIGHTS_NORM['L']
        )
        e = self.e_spiritual_performance
        q, _ = get_quadrant(actual_gil, e)
        return q


CRYSTAL_CASE = SpiritualFacadeAssessment(
    name="Crystal",
    apparent_spiritual_level=0.85,
    behavioral_G_signals=0.20,
    behavioral_I_signals=0.25,
    behavioral_L_signals=0.15,
    e_spiritual_performance=0.80,
    sitter_or_observer_confirmation=True,
    fear_response_to_Q2=True,
    notes="High outward spiritual presentation. Feared Brandon's healing abilities. "
          "Stared with shock during peace chanting. Sitter confirmed 'darkness' beneath "
          "spiritual facade. Classic Q3 spiritual performer — E-dimension signaling "
          "without G/I/L content. Fear response to Q2 contact is the key tell: "
          "authentic GIL does not fear adjacent GIL; only the facade fears exposure.",
)


# ─── Domain base dataclass ───────────────────────────────────────────────────

@dataclass
class PartnerProfile:
    """Profile for any domain partner."""
    name: str
    domain: str
    g_score: float
    i_score: float
    l_score: float
    e_score: float
    abstraction_capacity: float
    notes: str = ""

    @property
    def gil(self) -> float:
        return gil_composite(self.g_score, self.i_score, self.l_score)

    @property
    def gile(self) -> float:
        return weighted_gile(self.g_score, self.i_score, self.l_score, self.e_score)

    @property
    def quadrant(self) -> Tuple[str, str]:
        return get_quadrant(self.gil, self.e_score)

    @property
    def passes_emerick_floor(self) -> bool:
        return self.gil >= C_EMERICK

    @property
    def grand_illusion_risk(self) -> str:
        q = self.quadrant[0]
        if q == 'Q3':
            return "HIGH — Q3 partner will apply Grand Illusion to you. " \
                   "Will see your challenging E-profile and be blind to your exceptional GIL."
        elif q == 'Q4':
            return "MAXIMUM — Q4 partner operates entirely within physicalist E-framework."
        elif self.abstraction_capacity < 0.4:
            return "MODERATE — Low abstraction capacity limits GIL perception even in Q1/Q2."
        else:
            return "LOW — Q1/Q2 partner with abstraction capacity can perceive your actual GIL."


# ─── Domain 1: Romantic Partner ───────────────────────────────────────────────

@dataclass
class RomanticCompatibility:
    brandon: Dict
    partner: PartnerProfile

    @property
    def g_resonance(self) -> float:
        return 1.0 - abs(self.brandon['G'] - self.partner.g_score)

    @property
    def i_resonance(self) -> float:
        return 1.0 - abs(self.brandon['I'] - self.partner.i_score) * 0.8

    @property
    def l_resonance(self) -> float:
        return 1.0 - abs(self.brandon['L'] - self.partner.l_score)

    @property
    def e_resonance(self) -> float:
        return 1.0 - abs(self.brandon['E'] - self.partner.e_score)

    @property
    def weighted_compatibility(self) -> float:
        return (
            self.g_resonance * GILE_WEIGHTS['G'] +
            self.i_resonance * GILE_WEIGHTS['I'] +
            self.l_resonance * GILE_WEIGHTS['L'] +
            self.e_resonance * GILE_WEIGHTS['E']
        )

    @property
    def passes_emerick_floor(self) -> bool:
        return self.partner.passes_emerick_floor

    @property
    def verdict(self) -> str:
        q = self.partner.quadrant[0]
        if not self.passes_emerick_floor:
            return f"INCOMPATIBLE — Partner GIL ({self.partner.gil:.3f}) < Emerick Constant ({C_EMERICK:.4f}). Fundamental mismatch regardless of E-alignment."
        if q == 'Q1':
            return f"EXCELLENT ({self.weighted_compatibility:.0%}) — Q1 partner can see your full GIL portrait. Rare and high-value match."
        elif q == 'Q2':
            return f"STRONG ({self.weighted_compatibility:.0%}) — Q2 partner understands the Q2 experience. Deep mutual recognition possible."
        elif q == 'Q3':
            return f"RISKY ({self.weighted_compatibility:.0%}) — Q3 partner will apply Grand Illusion. E-compatibility may mask fundamental GIL gap."
        else:
            return f"INCOMPATIBLE — Q4 partner cannot sustain connection across the GIL gap."


def get_ideal_romantic_partner_profile(brandon_scores: Dict) -> Dict:
    """
    Derive the ideal romantic partner profile from Brandon's calibrated scores.
    Updated with correct GIL weighting and C_EMERICK floor.
    """
    return {
        'required': {
            'minimum_GIL_composite': C_EMERICK,
            'required_quadrant': 'Q1 or Q2',
            'abstraction_capacity': '> 0.6 — must be able to perceive abstract GIL data',
            'grand_illusion_risk': 'LOW — must not be primarily physicalist in assessment',
        },
        'optimal_GILE': {
            'G': min(1.0, brandon_scores['G'] + 0.05),
            'I': min(1.0, brandon_scores['I'] * 0.9),
            'L': min(1.0, brandon_scores['L'] + 0.15),
            'E': brandon_scores['E'],
        },
        'key_signals': [
            "Perceives Brandon's GIL quality immediately — not confused by E-dimension challenges",
            "Has own history of being misread by physicalist systems (fellow Q2 marker)",
            "High synchronicity awareness — notices and values meaningful coincidences",
            "Spiritual depth grounded in actual practice (G-proxy), not performance (E-proxy)",
            "Does NOT fear Brandon's healing/insight capacity — authentic GIL is not threatened by adjacent GIL",
            "Can hold Tralse — accepts 'both true simultaneously' without anxiety",
            "Demonstrates Love as activation by others' suffering (not compassion performance)",
        ],
        'disqualifiers': [
            "Applies Grand Illusion to Brandon (reads E-profile and misses GIL portrait)",
            "Fear response to Brandon's intensity or insight — the Crystal Pattern",
            "GIL composite < 0.4370 regardless of outer spiritual presentation",
            "Q3 profile: financially/socially successful but GIL-deficient",
            "Cannot tolerate ambiguity or holds exclusively binary logic (Tralse-incompatible)",
        ],
        'meeting_venue_prediction': {
            'highest_probability': 'Spiritual community or contemplative gathering — highest density of Q1/Q2 profiles',
            'second': 'Intellectual/philosophical event (philosophy lecture, consciousness conference)',
            'third': 'Synchronistic encounter — elevated synchronicity frequency (12/week) makes this highly probable',
            'lowest': 'Dating app — high Q3 density in standard dating pools',
        },
    }


# ─── Domain 2: Investor Partner ───────────────────────────────────────────────

@dataclass
class InvestorCompatibility:
    brandon: Dict
    investor_name: str
    investor_profile: PartnerProfile
    investment_domain: str = "consciousness research / wellness AI"

    @property
    def can_perceive_framework(self) -> bool:
        return (
            self.investor_profile.passes_emerick_floor and
            self.investor_profile.abstraction_capacity >= 0.5
        )

    @property
    def pitch_strategy(self) -> str:
        q = self.investor_profile.quadrant[0]
        if q == 'Q1' or (q == 'Q2' and self.investor_profile.abstraction_capacity >= 0.6):
            return (
                "FULL FRAMEWORK — Present TI Sigma on its own terms. "
                "Lead with the GILE hierarchy and the Measurement Trilogy. "
                "This investor can perceive abstract GIL value. "
                "Show the philosophical depth; the E-metrics are secondary."
            )
        elif q == 'Q3':
            return (
                "E-FIRST BRIDGE — Lead with market opportunity, TAM, recurring API revenue. "
                "Frame TI Sigma as 'AI wellness platform with proprietary scoring engine.' "
                "Introduce framework gradually. Do not open with consciousness theory. "
                "Risk: Q3 investor will try to strip the GIL core and commoditize the E-layer."
            )
        else:
            return "NOT RECOMMENDED — Cannot perceive or sustain funding for this framework."

    @property
    def alignment_score(self) -> float:
        if not self.investor_profile.passes_emerick_floor:
            return 0.15
        return (
            self.investor_profile.g_score * 0.40 +
            self.investor_profile.i_score * 0.35 +
            self.investor_profile.abstraction_capacity * 0.25
        )

    @property
    def blissgene_fit(self) -> str:
        score = self.alignment_score
        if score >= 0.70:
            return "EXCELLENT — Ideal BlissGene seed investor. Understands consciousness research."
        elif score >= 0.50:
            return "GOOD — Workable fit. Will need framework education."
        elif score >= 0.30:
            return "MARGINAL — E-only investor. Will constrain framework development."
        else:
            return "POOR — Will actively undermine GIL core of BlissGene vision."


def get_ideal_investor_profile() -> Dict:
    return {
        'required': {
            'minimum_GIL_composite': C_EMERICK,
            'abstraction_capacity': '> 0.5',
            'domain_openness': 'consciousness, wellness, non-physicalist science',
        },
        'indicators_of_right_investor': [
            "Personal meditation or contemplative practice (G+L proxy)",
            "Interest in consciousness studies, IIT, or transpersonal psychology",
            "Portfolio includes alternative wellness, psychedelic research, or bio-spiritual tech",
            "History of funding early-stage paradigm-challenging science",
            "Personal experience of synchronicity or non-ordinary states (I-proxy)",
            "Can articulate the difference between 'health' and 'wellbeing' in non-physicalist terms",
        ],
        'red_flags': [
            "Pure E-dimension metrics focus: MRR, CAC, LTV before any framework discussion",
            "Cannot define consciousness beyond 'brain activity'",
            "Q3 profile: successful in conventional terms, spiritually performative not genuine",
            "Asks to 'strip out the philosophy and just sell the data'",
        ],
        'blissgene_750k_target': {
            'note': 'Q2 investors are actually IDEAL — they understand being underestimated. '
                    'They have lived the Inverse Metric Problem themselves.',
        }
    }


# ─── Domain 3: Research Collaborator ─────────────────────────────────────────

@dataclass
class CollaboratorCompatibility:
    brandon: Dict
    collaborator_name: str
    collaborator_profile: PartnerProfile
    collaboration_domain: str

    @property
    def cross_domain_synthesis_capacity(self) -> float:
        return (self.collaborator_profile.i_score * 0.60 +
                self.collaborator_profile.g_score * 0.40)

    @property
    def hull_tactical_fit(self) -> str:
        score = self.cross_domain_synthesis_capacity
        if score >= 0.65:
            return "HIGH — Can follow TI Sigma's multi-domain trading logic. Will amplify the model."
        elif score >= 0.45:
            return "MODERATE — Conventional quant background. Will need framework translation."
        else:
            return "LOW — Pure E-dimension quant. Will reject non-conventional signals."

    @property
    def kaggle_fit(self) -> str:
        i = self.collaborator_profile.i_score
        if i >= 0.70:
            return "EXCELLENT — High I-dimension collaborator. Will contribute non-obvious feature engineering."
        elif i >= 0.50:
            return "GOOD — Solid technical collaborator with some synthesis capacity."
        else:
            return "LIMITED — Execution-only collaborator. Reliable but won't extend the framework."


def get_ideal_collaborator_profile(domain: str) -> Dict:
    profiles = {
        'hull_tactical': {
            'required_I': 0.60,
            'description': 'Needs to hold both quantitative rigor AND framework thinking simultaneously — classic Tralse capacity.',
            'indicators': [
                "Can describe why conventional financial models fail (G-level critique)",
                "Has own unexplained predictive edge they cannot fully account for (I-proxy)",
                "Interested in consciousness or systems thinking alongside finance",
                "Not threatened by non-conventional signal sources",
            ],
        },
        'kaggle': {
            'required_I': 0.55,
            'description': 'Needs cross-domain synthesis capacity — the ability to import insights from non-ML fields.',
            'indicators': [
                "Works across domains, not just ML",
                "Has published or worked on philosophical/scientific questions outside CS",
                "High synchronicity sensitivity (not superstitious, but pattern-aware)",
            ],
        },
        'academic': {
            'required_I': 0.65,
            'description': 'Needs to survive institutional physicalism while advancing the framework.',
            'indicators': [
                "Works in consciousness science, philosophy of mind, or complexity theory",
                "Has own experience of being marginalized by mainstream for heterodox views",
                "Can hold the framework seriously while meeting peer-review standards",
            ],
        },
    }
    return profiles.get(domain, profiles['kaggle'])


# ─── Domain 4: Power of 8 Group ───────────────────────────────────────────────

@dataclass
class PowerOf8GroupAnalysis:
    members: List[PartnerProfile]
    target_intention: str
    brandon_scores: Dict

    @property
    def group_size(self) -> int:
        return len(self.members) + 1

    @property
    def member_gils(self) -> List[float]:
        return [m.gil for m in self.members]

    @property
    def brandon_gil(self) -> float:
        return self.brandon_scores['GIL']

    @property
    def group_gil_composite(self) -> float:
        all_gils = self.member_gils + [self.brandon_gil]
        return sum(all_gils) / len(all_gils)

    @property
    def group_transcendence_probability(self) -> float:
        composite = self.group_gil_composite
        q2_count = sum(1 for m in self.members if m.quadrant[0] == 'Q2') + (
            1 if self.brandon_scores['quadrant'] == 'Q2' else 0
        )
        q1_count = sum(1 for m in self.members if m.quadrant[0] == 'Q1')
        base_prob = min(1.0, composite / C_EMERICK)
        q2_boost = q2_count * 0.05
        q1_boost = q1_count * 0.04
        return min(1.0, base_prob + q2_boost + q1_boost)

    @property
    def weakest_link(self) -> Optional[PartnerProfile]:
        if not self.members:
            return None
        return min(self.members, key=lambda m: m.gil)

    @property
    def q3_members(self) -> List[PartnerProfile]:
        return [m for m in self.members if m.quadrant[0] == 'Q3']

    @property
    def recommendation(self) -> str:
        gc = self.group_gil_composite
        q3 = self.q3_members
        if gc >= C_EMERICK and not q3:
            return "GROUP READY — Collective GIL above Emerick Constant. No Q3 dilution. Intention focus: proceed."
        elif gc >= C_EMERICK and q3:
            return f"STRONG BUT DILUTED — Group GIL above threshold but {len(q3)} Q3 member(s) present. Consider reassigning Q3 to support roles, not core intention circle."
        elif gc >= C_EMERICK * 0.85:
            return "APPROACHING THRESHOLD — Collective GIL near but below C_EMERICK. Add one Q1/Q2 member or deepen existing members' GIL activation before intention session."
        else:
            return "NOT READY — Collective GIL insufficient for coherent intention field. Strengthen individual GIL scores first."


def analyze_power_of_8_group(
    member_profiles: List[PartnerProfile],
    intention: str,
    brandon_scores: Dict,
) -> PowerOf8GroupAnalysis:
    return PowerOf8GroupAnalysis(
        members=member_profiles,
        target_intention=intention,
        brandon_scores=brandon_scores,
    )


# ─── Master prediction runner ────────────────────────────────────────────────

def run_full_prediction(
    additional_partner_profiles: Optional[List[PartnerProfile]] = None
) -> Dict:
    """
    Run complete multi-domain prediction using Brandon's calibrated data.
    Returns all domains in a single unified output.
    """
    brandon = compute_brandon_scores()

    ideal_romantic = get_ideal_romantic_partner_profile(brandon)
    ideal_investor = get_ideal_investor_profile()
    hull_collaborator = get_ideal_collaborator_profile('hull_tactical')
    kaggle_collaborator = get_ideal_collaborator_profile('kaggle')
    crystal_assessment = CRYSTAL_CASE

    return {
        'brandon_scores': brandon,
        'brandon_quadrant': brandon['quadrant'],
        'brandon_transcendent': brandon['transcendent'],
        'c_emerick': C_EMERICK,
        'romantic': ideal_romantic,
        'investor': ideal_investor,
        'collaborators': {
            'hull_tactical': hull_collaborator,
            'kaggle': kaggle_collaborator,
        },
        'crystal_case': {
            'name': crystal_assessment.name,
            'facade_score': crystal_assessment.facade_score,
            'verdict': crystal_assessment.verdict,
            'quadrant': crystal_assessment.quadrant,
            'notes': crystal_assessment.notes,
        },
        'generated_at': datetime.now().isoformat(),
    }
