"""
TI Pharmacological Simulator
============================
Personalized drug/supplement effect modeling using:
- Consciousness metrics (LCC, GILE, True-Tralseness)
- Genetic variants (FAAH, COMT, serotonin receptors, schizotypy SNPs)
- Biometrics (HRV, EEG, heart rate)
- HEM D2 Tralse meter (URB #619)
- EV/PD distribution (URB #609, #615)
- Historical response patterns

Canonical GILE weights (URB #576): G=√2−1≈0.4142, I=0.25, L=0.18, E=0.15
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from datetime import datetime, timedelta
import json
import os
import psycopg2
from psycopg2.extras import RealDictCursor

DATABASE_URL = os.environ.get('DATABASE_URL')

# Canonical GILE weights (URB #576 — Emerick Threshold G = √2−1)
GILE_W_G = 0.4142
GILE_W_I = 0.25
GILE_W_L = 0.18
GILE_W_E = 0.15


@dataclass
class GeneticProfile:
    """User's genetic variants affecting pharmacology"""
    faah_activity: float = 1.0      # 0.0 = low (good), 1.0 = normal, 2.0 = high (fast metabolism)
    comt_activity: float = 1.0      # 0.0 = low (worrier), 1.0 = normal, 2.0 = high (warrior)
    serotonin_sensitivity: float = 1.0
    bdnf_expression: float = 1.0
    schizotypy_snp_count: int = 0   # Number of schizotypy-related SNPs
    cb1_receptor_density: float = 1.0
    gaba_sensitivity: float = 1.0
    dopamine_sensitivity: float = 1.0

    def consciousness_amplification_factor(self) -> float:
        """How much consciousness effects are amplified by genetics"""
        base = 1.0
        base += (self.schizotypy_snp_count / 100) * 0.5
        base += (self.cb1_receptor_density - 1.0) * 0.3
        base += (self.serotonin_sensitivity - 1.0) * 0.2
        return max(0.5, min(2.0, base))


@dataclass
class ConsciousnessState:
    """Current consciousness metrics"""
    lcc: float = 0.5        # Love-Consciousness Coupling (0-1)
    gile_g: float = 0.5
    gile_i: float = 0.5
    gile_l: float = 0.5
    gile_e: float = 0.5
    coherence: float = 0.5
    true_tralseness: float = 0.5  # kept for backward compat; see gile_truth below

    @property
    def gile_composite(self) -> float:
        """Canonical GILE weights (URB #576)"""
        return (GILE_W_G * self.gile_g + GILE_W_I * self.gile_i
                + GILE_W_L * self.gile_l + GILE_W_E * self.gile_e)

    @property
    def gile_truth_score(self) -> float:
        """GILE Truth Score = gile_composite × coherence"""
        return self.gile_composite * self.coherence

    @property
    def hem_d2(self) -> float:
        """
        HEM D2 (Contradiction Ratio / Tralse Meter — URB #619).
        Derived from coherence vs. the tension between high-activation dimensions.
        D2 = 0 → fully resolved (True/False); D2 > 0.65 → DT risk.
        """
        # Internal contradiction = variance across GILE dimensions
        dims = [self.gile_g, self.gile_i, self.gile_l, self.gile_e]
        variance = float(np.var(dims))
        # Incoherence contribution
        incoherence = 1.0 - self.coherence
        d2 = 0.5 * variance * 4 + 0.5 * incoherence  # scale variance to 0-1
        return float(np.clip(d2, 0.0, 1.0))

    def to_dict(self) -> Dict:
        return {
            'lcc': self.lcc,
            'gile_g': self.gile_g,
            'gile_i': self.gile_i,
            'gile_l': self.gile_l,
            'gile_e': self.gile_e,
            'gile_composite': self.gile_composite,
            'gile_truth_score': self.gile_truth_score,
            'coherence': self.coherence,
            'hem_d2_tralse': self.hem_d2,
        }


@dataclass
class BiometricState:
    """Current biometric measurements"""
    heart_rate: float = 70.0
    rmssd: float = 40.0
    sdnn: float = 50.0
    alpha_power: float = 0.5
    beta_power: float = 0.3
    theta_power: float = 0.4
    gamma_power: float = 0.2
    delta_power: float = 0.3

    @property
    def parasympathetic_dominance(self) -> float:
        return min(1.0, self.rmssd / 80.0)

    @property
    def eeg_coherence(self) -> float:
        return (self.alpha_power + self.gamma_power * 0.5) / (self.beta_power + 0.1)


@dataclass
class Supplement:
    """Supplement with pharmacological properties"""
    name: str
    dose_mg: float

    # Pharmacokinetics
    absorption_time_min: float = 30.0
    half_life_hours: float = 4.0
    bbb_penetration: float = 0.5

    # Safety
    epilepsy_risk: str = "LOW"          # LOW / MODERATE / HIGH / CONTRAINDICATED
    epilepsy_note: str = ""
    not_medical_advice: str = "NOT MEDICAL ADVICE — consult neurologist before use"

    # Mechanisms (0-1 strength)
    faah_inhibition: float = 0.0
    cb1_activation: float = 0.0
    cb2_activation: float = 0.0
    nape_pld_activation: float = 0.0
    anti_inflammatory: float = 0.0
    bdnf_upregulation: float = 0.0
    gaba_modulation: float = 0.0
    serotonin_modulation: float = 0.0
    dopamine_modulation: float = 0.0
    nmda_modulation: float = 0.0        # NEW: NMDA system
    acetylcholine_modulation: float = 0.0  # NEW: ACh system
    mitochondrial_support: float = 0.0  # NEW: energy metabolism

    # Consciousness effects (TI-specific)
    lcc_boost: float = 0.0
    love_boost: float = 0.0
    intuition_boost: float = 0.0
    goodness_boost: float = 0.0
    environment_boost: float = 0.0

    # Interaction flags
    interaction_group: str = ""         # e.g. "faah_inhibitor", "cb1_agonist", "dopamine_precursor"
    known_interactions: List[str] = field(default_factory=list)


# ============================================================
# SUPPLEMENT DATABASE
# ============================================================
SUPPLEMENT_DATABASE: Dict[str, Supplement] = {

    # --- Endocannabinoid System ---
    'curcubrain': Supplement(
        name='Curcubrain',
        dose_mg=400, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.85,
        faah_inhibition=0.65, anti_inflammatory=0.80, bdnf_upregulation=0.55,
        lcc_boost=0.03, love_boost=0.04, intuition_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Generally safe; anti-inflammatory may mildly reduce seizure threshold elevation. Monitor if starting new protocol.",
        interaction_group="faah_inhibitor"
    ),
    'macamides_5pct': Supplement(
        name='Nootropics Depot 5% Macamides',
        dose_mg=750, absorption_time_min=30, half_life_hours=4, bbb_penetration=0.70,
        cb1_activation=0.70, nape_pld_activation=0.60,
        dopamine_modulation=0.45, serotonin_modulation=0.35,
        lcc_boost=0.05, love_boost=0.06, intuition_boost=0.04, goodness_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Macamides have no reported pro-convulsant activity. CB1 partial activation may have mild anticonvulsant properties.",
        interaction_group="cb1_agonist"
    ),
    'pea_palmitoylethanolamide': Supplement(
        name='PEA (Palmitoylethanolamide)',
        dose_mg=1500, absorption_time_min=40, half_life_hours=5, bbb_penetration=0.60,
        nape_pld_activation=0.75, anti_inflammatory=0.70,
        lcc_boost=0.04, love_boost=0.05,
        epilepsy_risk="LOW",
        epilepsy_note="PEA has emerging anticonvulsant research via PPAR-alpha. Generally safe for epilepsy profiles. Consult neurologist.",
        interaction_group="faah_inhibitor"
    ),
    'cbd_oil': Supplement(
        name='CBD Oil',
        dose_mg=25, absorption_time_min=20, half_life_hours=3, bbb_penetration=0.75,
        faah_inhibition=0.50, cb1_activation=0.20, cb2_activation=0.40,
        anti_inflammatory=0.60, gaba_modulation=0.30,
        lcc_boost=0.02, love_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="CBD (Epidiolex) is FDA-approved for certain epilepsy types. At 25mg generally well-tolerated. May interact with AEDs — monitor drug levels if on valproate or clobazam.",
        interaction_group="faah_inhibitor",
        known_interactions=["Valproate — monitor drug levels", "Clobazam — increased clobazam exposure"]
    ),
    'kaempferol': Supplement(
        name='Kaempferol',
        dose_mg=50, absorption_time_min=35, half_life_hours=4, bbb_penetration=0.55,
        faah_inhibition=0.45, anti_inflammatory=0.50,
        lcc_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Kaempferol shows anticonvulsant activity in animal models. No clinical pro-convulsant data.",
        interaction_group="faah_inhibitor"
    ),
    'quercetin': Supplement(
        name='Quercetin',
        dose_mg=500, absorption_time_min=45, half_life_hours=5, bbb_penetration=0.50,
        faah_inhibition=0.40, anti_inflammatory=0.65,
        lcc_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="No pro-convulsant activity; some neuroprotective evidence.",
        interaction_group="faah_inhibitor"
    ),
    'luteolin': Supplement(
        name='Luteolin',
        dose_mg=100, absorption_time_min=35, half_life_hours=4, bbb_penetration=0.55,
        faah_inhibition=0.55, anti_inflammatory=0.50,
        lcc_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Neuroprotective; no pro-convulsant data.",
        interaction_group="faah_inhibitor"
    ),
    'black_seed_oil': Supplement(
        name='Black Seed Oil (Thymoquinone)',
        dose_mg=500, absorption_time_min=40, half_life_hours=5, bbb_penetration=0.45,
        faah_inhibition=0.35, anti_inflammatory=0.55,
        lcc_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Thymoquinone shows anticonvulsant properties in animal models."
    ),

    # --- Minerals & Foundational ---
    'magnesium_l_threonate': Supplement(
        name='Magnesium L-Threonate',
        dose_mg=144, absorption_time_min=60, half_life_hours=8, bbb_penetration=0.90,
        gaba_modulation=0.40, bdnf_upregulation=0.35, nmda_modulation=0.35,
        lcc_boost=0.01, intuition_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Magnesium is neuroprotective and may reduce seizure susceptibility. Well-tolerated.",
        interaction_group="nmda_modulator"
    ),
    'omega3_dha': Supplement(
        name='Omega-3 DHA',
        dose_mg=1000, absorption_time_min=90, half_life_hours=24, bbb_penetration=0.70,
        anti_inflammatory=0.60, bdnf_upregulation=0.30,
        lcc_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="DHA is neuroprotective. No seizure risk."
    ),
    'vitamin_b6_p5p': Supplement(
        name='Vitamin B6 (P5P)',
        dose_mg=50, absorption_time_min=30, half_life_hours=6, bbb_penetration=0.85,
        nape_pld_activation=0.25, serotonin_modulation=0.30,
        dopamine_modulation=0.25, gaba_modulation=0.20,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="B6 cofactor for GABA synthesis. Generally anticonvulsant. Very high doses (>500mg/day) can cause neuropathy."
    ),

    # --- Maca variants ---
    'maca_standard': Supplement(
        name='Maca Root (Standard)',
        dose_mg=1500, absorption_time_min=40, half_life_hours=5, bbb_penetration=0.40,
        nape_pld_activation=0.30, dopamine_modulation=0.25,
        lcc_boost=0.01,
        epilepsy_risk="LOW", epilepsy_note="No seizure risk reported."
    ),

    # --- Nootropics / Cognition ---
    'lions_mane': Supplement(
        name="Lion's Mane (Hericium erinaceus)",
        dose_mg=1000, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.55,
        bdnf_upregulation=0.70, anti_inflammatory=0.40,
        lcc_boost=0.025, intuition_boost=0.04, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Neuroprotective via NGF induction. No pro-convulsant data. Safe profile.",
        interaction_group="bdnf_booster"
    ),
    'bacopa_monnieri': Supplement(
        name='BaCognize (Bacopa monnieri)',
        dose_mg=500, absorption_time_min=60, half_life_hours=5, bbb_penetration=0.60,
        bdnf_upregulation=0.45, anti_inflammatory=0.30, serotonin_modulation=0.25,
        lcc_boost=0.015, intuition_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Bacosides are neuroprotective. No seizure risk; some evidence of anticonvulsant effects.",
        interaction_group="bdnf_booster"
    ),
    'alpha_gpc': Supplement(
        name='Alpha GPC',
        dose_mg=600, absorption_time_min=30, half_life_hours=4, bbb_penetration=0.85,
        acetylcholine_modulation=0.75, bdnf_upregulation=0.20,
        lcc_boost=0.02, intuition_boost=0.035,
        epilepsy_risk="LOW",
        epilepsy_note="ACh precursor; no pro-convulsant activity. High doses may lower seizure threshold theoretically — stay ≤600mg.",
        interaction_group="cholinergic"
    ),
    'phosphatidylserine': Supplement(
        name='Phosphatidylserine',
        dose_mg=300, absorption_time_min=40, half_life_hours=5, bbb_penetration=0.65,
        bdnf_upregulation=0.25, anti_inflammatory=0.20,
        lcc_boost=0.01, intuition_boost=0.02, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Cell membrane support; no seizure risk."
    ),

    # --- Dopamine / Monoamine Pathway ---
    'mucuna_pruriens': Supplement(
        name='Mucuna Pruriens (15% L-DOPA)',
        dose_mg=400, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.70,
        dopamine_modulation=0.75, serotonin_modulation=0.20,
        lcc_boost=0.03, intuition_boost=0.04, environment_boost=0.03,
        epilepsy_risk="MODERATE",
        epilepsy_note="L-DOPA can lower seizure threshold at high doses. Use cautiously with epilepsy; start low. Do NOT combine with MAOIs.",
        interaction_group="dopamine_precursor",
        known_interactions=["Do NOT combine with L-Tyrosine same day", "Do NOT combine with MAOIs"]
    ),
    'l_tyrosine': Supplement(
        name='L-Tyrosine',
        dose_mg=500, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.60,
        dopamine_modulation=0.45, serotonin_modulation=0.15,
        lcc_boost=0.015, intuition_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Gentle dopamine precursor. No significant seizure risk.",
        interaction_group="dopamine_precursor",
        known_interactions=["Do NOT combine with Mucuna same day"]
    ),

    # --- NMDA / Glutamate Pathway ---
    'nac': Supplement(
        name='NAC (N-Acetyl Cysteine)',
        dose_mg=1000, absorption_time_min=45, half_life_hours=5, bbb_penetration=0.60,
        anti_inflammatory=0.50, nmda_modulation=0.40,
        lcc_boost=0.02, goodness_boost=0.04,
        epilepsy_risk="LOW",
        epilepsy_note="Antioxidant and glutamate modulator. Some anticonvulsant properties. Well-tolerated.",
        interaction_group="nmda_modulator"
    ),
    'glycine': Supplement(
        name='Glycine',
        dose_mg=3000, absorption_time_min=20, half_life_hours=4, bbb_penetration=0.55,
        gaba_modulation=0.35, nmda_modulation=0.30, serotonin_modulation=0.10,
        lcc_boost=0.015, love_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Inhibitory neurotransmitter; supports sleep. No pro-convulsant activity.",
        interaction_group="nmda_modulator"
    ),

    # --- Mitochondrial / Energy ---
    'coq10': Supplement(
        name='CoQ10',
        dose_mg=200, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.30,
        mitochondrial_support=0.75, anti_inflammatory=0.25,
        lcc_boost=0.005, environment_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Mitochondrial support; antioxidant. No seizure risk. May benefit mitochondrial epilepsy variants."
    ),
    'creatine': Supplement(
        name='Creatine',
        dose_mg=5000, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.35,
        mitochondrial_support=0.60,
        lcc_boost=0.005, intuition_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Phosphocreatine buffer for brain energy. Neuroprotective; no seizure risk."
    ),

    # ── NEW SUPPLEMENTS (April 2026 full stack) ───────────────────────────

    'beta_caryophyllene': Supplement(
        name='Beta-Caryophyllene (sublingual, MCT)',
        dose_mg=90, absorption_time_min=15, half_life_hours=3, bbb_penetration=0.65,
        cb2_activation=0.75, anti_inflammatory=0.60, gaba_modulation=0.20,
        lcc_boost=0.025, love_boost=0.035, goodness_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Selective CB2 agonist (no psychoactivity). Anti-inflammatory; potential anticonvulsant via GABA-A. Very safe profile.",
        interaction_group="cb2_agonist"
    ),
    'saffron_extract': Supplement(
        name='Saffron Extract (2% safranal, 11% crocins)',
        dose_mg=60, absorption_time_min=30, half_life_hours=5, bbb_penetration=0.70,
        serotonin_modulation=0.55, dopamine_modulation=0.30, bdnf_upregulation=0.40,
        anti_inflammatory=0.35,
        lcc_boost=0.04, love_boost=0.05, intuition_boost=0.03, goodness_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Saffron has anticonvulsant properties in animal models. No pro-convulsant data. May reduce anxiety which is seizure-protective.",
        interaction_group="serotonin_modulator",
        known_interactions=["Caution with 5-HTP and SSRI — serotonin syndrome risk; separate by 12h"]
    ),
    'htp_5': Supplement(
        name='5-HTP (200 mg)',
        dose_mg=200, absorption_time_min=30, half_life_hours=4, bbb_penetration=0.80,
        serotonin_modulation=0.75, bdnf_upregulation=0.20,
        lcc_boost=0.04, love_boost=0.06, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="5-HTP generally well-tolerated. High serotonergic activity — do NOT combine with SSRIs, MAOIs, or Saffron without monitoring.",
        interaction_group="serotonin_precursor",
        known_interactions=["Do NOT combine with SSRIs or MAOIs — serotonin syndrome", "Caution with Saffron (separate by 12h)"]
    ),
    'mood_probiotic': Supplement(
        name='Mood Probiotic (L. helveticus R-52 + B. longum R-175)',
        dose_mg=357, absorption_time_min=120, half_life_hours=48, bbb_penetration=0.10,
        serotonin_modulation=0.30, gaba_modulation=0.25, anti_inflammatory=0.40,
        lcc_boost=0.03, love_boost=0.04, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Probiotics are safe for epilepsy profiles. Gut-brain axis modulation is neuroprotective. No seizure risk.",
        interaction_group="gut_brain"
    ),
    'pqq': Supplement(
        name='PQQ (Pyrroloquinoline Quinone, 20 mg)',
        dose_mg=20, absorption_time_min=30, half_life_hours=6, bbb_penetration=0.55,
        mitochondrial_support=0.80, bdnf_upregulation=0.50, anti_inflammatory=0.30,
        lcc_boost=0.02, intuition_boost=0.03, environment_boost=0.04,
        epilepsy_risk="LOW",
        epilepsy_note="PQQ stimulates mitochondrial biogenesis. Neuroprotective. No seizure risk."
    ),
    'beta_ecdysterone': Supplement(
        name='Beta-Ecdysterone (500 mg x2)',
        dose_mg=1000, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.45,
        mitochondrial_support=0.50, anti_inflammatory=0.35, bdnf_upregulation=0.30,
        lcc_boost=0.015, environment_boost=0.04, intuition_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Ecdysterone (ERβ agonist) is neuroprotective. No pro-convulsant data."
    ),
    'l_methylfolate': Supplement(
        name='L-Methylfolate (1700 DFE)',
        dose_mg=1.0, absorption_time_min=30, half_life_hours=4, bbb_penetration=0.90,
        serotonin_modulation=0.35, dopamine_modulation=0.30, bdnf_upregulation=0.35,
        lcc_boost=0.025, goodness_boost=0.04, intuition_boost=0.025,
        epilepsy_risk="LOW",
        epilepsy_note="L-methylfolate is neuroprotective. Supports neurotransmitter synthesis (BH4 cofactor). No seizure risk."
    ),
    'vitamin_d3': Supplement(
        name='Vitamin D3 (250 mcg / 10,000 IU)',
        dose_mg=0.25, absorption_time_min=60, half_life_hours=72, bbb_penetration=0.65,
        anti_inflammatory=0.40, bdnf_upregulation=0.45, serotonin_modulation=0.25,
        lcc_boost=0.015, goodness_boost=0.02, intuition_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Vitamin D deficiency is associated with increased seizure risk. Supplementation is neuroprotective. Very safe."
    ),
    'green_tea_egcg': Supplement(
        name='Green Tea Extract (98% polyphenols, 45% EGCG, 725 mg)',
        dose_mg=725, absorption_time_min=40, half_life_hours=5, bbb_penetration=0.65,
        faah_inhibition=0.40, anti_inflammatory=0.60, bdnf_upregulation=0.45,
        nape_pld_activation=0.20,
        lcc_boost=0.02, intuition_boost=0.025, goodness_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="EGCG is neuroprotective; mild anticonvulsant properties. No pro-convulsant data. Decaffeinated form removes caffeine seizure risk.",
        interaction_group="faah_inhibitor"
    ),
    'triacetyluridine': Supplement(
        name='Triacetyluridine (TAU, 250 mg)',
        dose_mg=250, absorption_time_min=30, half_life_hours=6, bbb_penetration=0.75,
        dopamine_modulation=0.40, acetylcholine_modulation=0.30, mitochondrial_support=0.25,
        lcc_boost=0.02, intuition_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="TAU (CDP-choline pathway) supports dopamine receptor density. No seizure risk."
    ),
    'moringa': Supplement(
        name='Moringa (1 gram)',
        dose_mg=1000, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.40,
        anti_inflammatory=0.45, bdnf_upregulation=0.35, serotonin_modulation=0.20,
        lcc_boost=0.015, goodness_boost=0.02, love_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Moringa has anticonvulsant properties in animal models. Neuroprotective. Safe profile."
    ),
    'tribulus_extract': Supplement(
        name='Tribulus Extract (95% saponins, 500 mg)',
        dose_mg=500, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.35,
        dopamine_modulation=0.30, serotonin_modulation=0.15,
        lcc_boost=0.01, environment_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Tribulus at standard doses: no seizure data. Mild dopaminergic; well-tolerated."
    ),
    'lactoferrin': Supplement(
        name='Lactoferrin (300 mg)',
        dose_mg=300, absorption_time_min=60, half_life_hours=8, bbb_penetration=0.30,
        anti_inflammatory=0.50, bdnf_upregulation=0.20,
        lcc_boost=0.01, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Lactoferrin is neuroprotective and iron-regulatory. No seizure risk.",
        interaction_group="gut_brain"
    ),
    'iberogast': Supplement(
        name='Iberogast (20 drops x2 daily)',
        dose_mg=30, absorption_time_min=20, half_life_hours=4, bbb_penetration=0.20,
        serotonin_modulation=0.35, gaba_modulation=0.20, anti_inflammatory=0.30,
        lcc_boost=0.015, love_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Iberogast (STW 5) is safe. Prokinetic; no CNS effects at standard doses.",
        interaction_group="gut_brain"
    ),
    'peppermint_oil_capsule': Supplement(
        name='Peppermint Essential Oil (enteric, 20 ml x3)',
        dose_mg=60, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.40,
        gaba_modulation=0.25, serotonin_modulation=0.15,
        lcc_boost=0.01, love_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Peppermint oil (menthol) modulates TRPM8 channels. Antispasmodic. No seizure risk."
    ),
    'ceylon_cinnamon': Supplement(
        name='Ceylon Cinnamon (1 teaspoon daily)',
        dose_mg=2500, absorption_time_min=40, half_life_hours=8, bbb_penetration=0.35,
        anti_inflammatory=0.40, serotonin_modulation=0.15,
        lcc_boost=0.01, environment_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Ceylon cinnamon (not cassia) is safe. Anticonvulsant properties in animal models."
    ),
    'ginger_extract': Supplement(
        name='Ginger (1 teaspoon daily)',
        dose_mg=2000, absorption_time_min=30, half_life_hours=5, bbb_penetration=0.30,
        anti_inflammatory=0.45, serotonin_modulation=0.25,
        lcc_boost=0.01, love_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Ginger is anti-inflammatory and has anticonvulsant properties. Very safe."
    ),
    'psyllium_husk': Supplement(
        name='Psyllium Husk (2 teaspoons daily)',
        dose_mg=8000, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.05,
        anti_inflammatory=0.20,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="Psyllium is gut fiber. No CNS effects; no seizure risk.",
        interaction_group="gut_brain"
    ),
    'sunfiber': Supplement(
        name='Sunfiber PHGG (7 grams daily)',
        dose_mg=7000, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.05,
        anti_inflammatory=0.20, serotonin_modulation=0.10,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="Partially hydrolyzed guar gum — prebiotic. No seizure risk.",
        interaction_group="gut_brain"
    ),
    'iron_b12_folate': Supplement(
        name='Iron + B12 + Folate Complex (28mg Fe + 60mg VitC + 667mcg DFE + 8mcg B12)',
        dose_mg=100, absorption_time_min=45, half_life_hours=8, bbb_penetration=0.50,
        serotonin_modulation=0.20, dopamine_modulation=0.20, mitochondrial_support=0.30,
        lcc_boost=0.01, intuition_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Iron + B12 + folate support heme-dependent neurotransmitter synthesis. Neuroprotective. No seizure risk."
    ),
    'bromelain_quercetin': Supplement(
        name='Quercetin 880mg + Bromelain 165mg',
        dose_mg=1045, absorption_time_min=35, half_life_hours=5, bbb_penetration=0.55,
        faah_inhibition=0.45, anti_inflammatory=0.70, bdnf_upregulation=0.20,
        lcc_boost=0.02, intuition_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Quercetin has anticonvulsant properties. Bromelain enhances quercetin absorption. Very safe.",
        interaction_group="faah_inhibitor"
    ),
    'omega3_high_epa': Supplement(
        name='Omega-3 Fish Oil (4g, 2.4:1 EPA:DHA)',
        dose_mg=4000, absorption_time_min=90, half_life_hours=24, bbb_penetration=0.75,
        anti_inflammatory=0.70, bdnf_upregulation=0.45, serotonin_modulation=0.25,
        lcc_boost=0.02, love_boost=0.02, intuition_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="High-dose Omega-3 (4g EPA+DHA) is anticonvulsant in some studies. EPA-dominant formulas show stronger mood effects."
    ),
    'transdermal_cbd': Supplement(
        name='Transdermal CBD (30-60 mg)',
        dose_mg=45, absorption_time_min=45, half_life_hours=6, bbb_penetration=0.60,
        faah_inhibition=0.45, cb1_activation=0.15, cb2_activation=0.35,
        anti_inflammatory=0.55, gaba_modulation=0.25,
        lcc_boost=0.02, love_boost=0.025,
        epilepsy_risk="LOW",
        epilepsy_note="Transdermal CBD has lower bioavailability than oral but avoids first-pass metabolism. FDA-approved CBD (Epidiolex) is anticonvulsant. Monitor if on valproate/clobazam.",
        interaction_group="faah_inhibitor",
        known_interactions=["Monitor if on valproate or clobazam — may increase drug levels"]
    ),

    # ── PRESCRIPTION MEDICATIONS ──────────────────────────────────────────

    'seroquel': Supplement(
        name='Seroquel (Quetiapine, 200 mg)',
        dose_mg=200, absorption_time_min=90, half_life_hours=7, bbb_penetration=0.85,
        gaba_modulation=0.30, serotonin_modulation=0.55, dopamine_modulation=0.50,
        lcc_boost=0.01, love_boost=0.02, goodness_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Quetiapine has a low seizure risk. H1 antagonism causes sedation. At very high doses (>1000mg) there is theoretical seizure risk — 200mg is safe.",
        interaction_group="antipsychotic",
        known_interactions=["Additive sedation with Olanzapine — monitor metabolic panel", "CYP3A4 substrate — avoid grapefruit"]
    ),
    'olanzapine': Supplement(
        name='Olanzapine (Zyprexa, 10 mg)',
        dose_mg=10, absorption_time_min=60, half_life_hours=30, bbb_penetration=0.90,
        serotonin_modulation=0.65, dopamine_modulation=0.60, gaba_modulation=0.20,
        lcc_boost=0.005, love_boost=0.01,
        epilepsy_risk="MODERATE",
        epilepsy_note="Olanzapine lowers seizure threshold more than Seroquel — MODERATE risk. Combined with Seroquel: monitor closely. Keppra co-prescription mitigates risk.",
        interaction_group="antipsychotic",
        known_interactions=["Additive metabolic risk with Seroquel — weight, glucose, lipids", "Additive sedation with all sleep aids"]
    ),
    'klonopin': Supplement(
        name='Klonopin (Clonazepam, 1 mg as needed)',
        dose_mg=1, absorption_time_min=30, half_life_hours=30, bbb_penetration=0.90,
        gaba_modulation=0.85, anti_inflammatory=0.15,
        lcc_boost=0.02, love_boost=0.04,
        epilepsy_risk="LOW",
        epilepsy_note="Clonazepam IS an anticonvulsant (first-line for some seizure types). Very safe for epilepsy. Risk: tolerance and dependence with regular use.",
        interaction_group="benzo_gaba",
        known_interactions=["Additive CNS depression with Lunesta, Belsomra, Seroquel, Olanzapine — use as-needed only"]
    ),
    'lunesta': Supplement(
        name='Lunesta (Eszopiclone, 3 mg as needed)',
        dose_mg=3, absorption_time_min=30, half_life_hours=6, bbb_penetration=0.90,
        gaba_modulation=0.75,
        lcc_boost=0.01, love_boost=0.015,
        epilepsy_risk="LOW",
        epilepsy_note="Eszopiclone (Z-drug, GABA-A agonist) is safe for epilepsy. May have mild anticonvulsant properties.",
        interaction_group="benzo_gaba",
        known_interactions=["Do not combine with Klonopin and Belsomra simultaneously — additive CNS depression"]
    ),
    'belsomra': Supplement(
        name='Belsomra (Suvorexant, 20 mg)',
        dose_mg=20, absorption_time_min=30, half_life_hours=12, bbb_penetration=0.85,
        serotonin_modulation=0.10,
        lcc_boost=0.015, love_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Suvorexant (orexin antagonist) has an excellent safety profile for epilepsy. No seizure risk; may actually reduce sleep-related seizures.",
        known_interactions=["Additive sedation with Klonopin, Lunesta if combined same night"]
    ),
    'clonidine': Supplement(
        name='Clonidine (0.3 mg)',
        dose_mg=0.3, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.85,
        serotonin_modulation=0.10, gaba_modulation=0.20,
        lcc_boost=0.01, love_boost=0.02, goodness_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Alpha-2 agonist. Some anticonvulsant properties; reduces NE (which can be proconvulsant). Safe."
    ),
    'desmopressin': Supplement(
        name='Desmopressin (DDAVP, 0.6 mg)',
        dose_mg=0.6, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.20,
        lcc_boost=0.005, intuition_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Desmopressin (ADH analog) is safe for epilepsy at standard doses. CAUTION: hyponatremia risk (low sodium) at high doses or with excess water intake — hyponatremia CAN trigger seizures. Monitor sodium.",
        known_interactions=["⚠️ Hyponatremia risk — do not over-hydrate; monitor sodium levels"]
    ),
    'ketamine_troche': Supplement(
        name='Ketamine Troche (200 mg sublingual, every other day)',
        dose_mg=200, absorption_time_min=15, half_life_hours=3, bbb_penetration=0.95,
        nmda_modulation=0.90, dopamine_modulation=0.40, serotonin_modulation=0.30,
        bdnf_upregulation=0.75,
        lcc_boost=0.08, love_boost=0.07, intuition_boost=0.08, goodness_boost=0.04,
        epilepsy_risk="MODERATE",
        epilepsy_note="Ketamine has a complex seizure profile: anticonvulsant at sub-anesthetic doses (used in refractory status epilepticus), potentially pro-convulsant at higher doses. 200mg sublingual troche is sub-anesthetic — likely safe with Keppra co-administration. Monitor closely.",
        interaction_group="nmda_modulator",
        known_interactions=["Synergy with Lithium (GSK-3β + AMPA potentiation)", "LDN may prevent tolerance (TLR4 mechanism)", "Additive CNS effects with Klonopin — coordinate with prescriber"]
    ),
    'focalin': Supplement(
        name='Focalin (Dexmethylphenidate, 10 mg x2)',
        dose_mg=20, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.90,
        dopamine_modulation=0.75, serotonin_modulation=0.20,
        lcc_boost=0.02, intuition_boost=0.04, environment_boost=0.03,
        epilepsy_risk="MODERATE",
        epilepsy_note="Stimulants can lower seizure threshold. Dexmethylphenidate at therapeutic doses (20mg total) has low but non-zero seizure risk. Keppra co-administration provides significant mitigation. Avoid dose escalation.",
        interaction_group="stimulant",
        known_interactions=["⚠️ May lower seizure threshold — mitigated by Keppra", "Additive cardiovascular effects with Qelbree"]
    ),
    'qelbree': Supplement(
        name='Qelbree (Viloxazine, 600 mg)',
        dose_mg=600, absorption_time_min=90, half_life_hours=7, bbb_penetration=0.85,
        serotonin_modulation=0.45, dopamine_modulation=0.35,
        lcc_boost=0.025, intuition_boost=0.04, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Viloxazine (NRI) has a low seizure risk profile — safer than stimulants. No significant pro-convulsant data at 600mg.",
        interaction_group="stimulant",
        known_interactions=["CYP1A2 inhibitor — may raise levels of caffeine, melatonin, clozapine"]
    ),
    'lithium': Supplement(
        name='Lithium Carbonate (300 mg)',
        dose_mg=300, absorption_time_min=60, half_life_hours=24, bbb_penetration=0.70,
        anti_inflammatory=0.40, bdnf_upregulation=0.55, nmda_modulation=0.30,
        lcc_boost=0.03, goodness_boost=0.05, environment_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Lithium at therapeutic levels (0.6–1.2 mEq/L) is neuroprotective. Toxic levels (>1.5) can cause seizures. 300mg is a low dose — safe. Monitor levels quarterly.",
        known_interactions=["⚠️ NSAIDs (Sulindac) raise lithium levels — monitor levels when adding/removing Sulindac", "Monitor with Prilosec (minimal interaction but track)"]
    ),
    'amantadine': Supplement(
        name='Amantadine (200 mg x2)',
        dose_mg=400, absorption_time_min=90, half_life_hours=16, bbb_penetration=0.85,
        nmda_modulation=0.55, dopamine_modulation=0.50,
        lcc_boost=0.025, intuition_boost=0.04, environment_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Amantadine has anticonvulsant properties via NMDA antagonism. Generally safe with Keppra. Low seizure risk.",
        interaction_group="nmda_modulator",
        known_interactions=["Synergy with Alpha GPC (dopamine + ACh cognitive enhancement)"]
    ),
    'ldn': Supplement(
        name='Low Dose Naltrexone (LDN, 4.5 mg)',
        dose_mg=4.5, absorption_time_min=60, half_life_hours=13, bbb_penetration=0.80,
        anti_inflammatory=0.65, bdnf_upregulation=0.40,
        lcc_boost=0.04, love_boost=0.05, goodness_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="LDN (TLR4 antagonist + OGF/OGFR modulator) is neuroprotective and anti-inflammatory. No seizure risk. May actually benefit seizure thresholds via neuroinflammation reduction.",
        known_interactions=["May prevent ketamine tolerance (TLR4 mechanism — therapeutic synergy)", "Do NOT use standard-dose naltrexone if on opioids"]
    ),
    'keppra': Supplement(
        name='Keppra (Levetiracetam, 500 mg x2)',
        dose_mg=1000, absorption_time_min=60, half_life_hours=8, bbb_penetration=0.85,
        anti_inflammatory=0.30, gaba_modulation=0.25,
        lcc_boost=0.01, goodness_boost=0.02,
        epilepsy_risk="LOW",
        epilepsy_note="Keppra IS an anticonvulsant (SV2A modulator). Protective. Note: Keppra rage/irritability in some patients — Vitamin B6 + Magnesium may mitigate this.",
        known_interactions=["Vitamin B6 (P5P) may reduce Keppra-associated mood side effects"]
    ),
    'taltz': Supplement(
        name='Taltz (Ixekizumab, 80 mg monthly)',
        dose_mg=80, absorption_time_min=3000, half_life_hours=312, bbb_penetration=0.05,
        anti_inflammatory=0.80,
        lcc_boost=0.02, goodness_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Biologic (IL-17A antibody). No CNS penetration at standard doses. Anti-inflammatory systemic effects are neuroprotective. No seizure risk."
    ),
    'sulindac': Supplement(
        name='Sulindac (200 mg)',
        dose_mg=200, absorption_time_min=60, half_life_hours=18, bbb_penetration=0.45,
        anti_inflammatory=0.60,
        lcc_boost=0.01,
        epilepsy_risk="LOW",
        epilepsy_note="Sulindac (NSAID, COX inhibitor). No direct seizure risk. Anti-inflammatory benefit.",
        known_interactions=["⚠️ CRITICAL: Sulindac raises lithium levels by ~25%. Monitor lithium every 2 weeks if Sulindac dose changes."]
    ),
    'tylenol_xr': Supplement(
        name='Acetaminophen XR (1300 mg)',
        dose_mg=1300, absorption_time_min=60, half_life_hours=4, bbb_penetration=0.50,
        anti_inflammatory=0.20,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="Acetaminophen is safe for epilepsy. Do not exceed 4g/day; avoid alcohol.",
        known_interactions=["Total daily Tylenol limit 4g/day — factor in all sources"]
    ),
    'prilosec': Supplement(
        name='Prilosec (Omeprazole, 20 mg)',
        dose_mg=20, absorption_time_min=60, half_life_hours=1, bbb_penetration=0.20,
        lcc_boost=0.0,
        epilepsy_risk="LOW",
        epilepsy_note="Omeprazole (PPI) is safe for epilepsy. May reduce magnesium absorption with long-term use — supplement Mg L-Threonate (already doing this).",
        known_interactions=["Long-term use may reduce magnesium absorption — already supplemented by Mg L-Threonate"]
    ),
    'linzess': Supplement(
        name='Linzess (Linaclotide, 145 mcg)',
        dose_mg=0.145, absorption_time_min=30, half_life_hours=3, bbb_penetration=0.02,
        serotonin_modulation=0.20,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="Linaclotide acts locally in the gut (GC-C agonist). Minimal systemic absorption. No seizure risk.",
        interaction_group="gut_brain"
    ),
    'flonase': Supplement(
        name='Flonase (Fluticasone, 2 sprays each nostril)',
        dose_mg=0.2, absorption_time_min=30, half_life_hours=8, bbb_penetration=0.05,
        anti_inflammatory=0.40,
        lcc_boost=0.005,
        epilepsy_risk="LOW",
        epilepsy_note="Intranasal fluticasone has minimal systemic absorption (<1%). No seizure risk."
    ),
    'mucinex': Supplement(
        name='Mucinex XR (Guaifenesin, 1200 mg)',
        dose_mg=1200, absorption_time_min=60, half_life_hours=7, bbb_penetration=0.10,
        lcc_boost=0.0,
        epilepsy_risk="LOW",
        epilepsy_note="Guaifenesin is an expectorant with no CNS effects at therapeutic doses. No seizure risk."
    ),

    'ubiquinone_coq10': Supplement(
        name='Ubiquinone CoQ10 (200 mg)',
        dose_mg=200, absorption_time_min=60, half_life_hours=12, bbb_penetration=0.30,
        mitochondrial_support=0.75, anti_inflammatory=0.25,
        lcc_boost=0.005, environment_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="CoQ10 is mitochondrially neuroprotective. No seizure risk. May benefit mitochondrial epilepsy."
    ),
    'saffron_macamides_mct': Supplement(
        name='Maca Macamides 5% + MCT Oil (800 mg)',
        dose_mg=800, absorption_time_min=25, half_life_hours=4, bbb_penetration=0.75,
        cb1_activation=0.70, nape_pld_activation=0.60,
        dopamine_modulation=0.45, serotonin_modulation=0.35,
        lcc_boost=0.05, love_boost=0.055, intuition_boost=0.04, goodness_boost=0.03,
        epilepsy_risk="LOW",
        epilepsy_note="Macamides via MCT oil have enhanced absorption. CB1 activation may be mildly anticonvulsant.",
        interaction_group="cb1_agonist"
    ),
}


# ============================================================
# INTERACTION DETECTION
# ============================================================

INTERACTION_CONFLICTS = {
    ("dopamine_precursor", "dopamine_precursor"): "⚠️ Two dopamine precursors in same stack — high depletion risk. Use on alternate days.",
    ("faah_inhibitor", "faah_inhibitor"): "ℹ️ Multiple FAAH inhibitors — diminishing returns (handled in simulation). Stack is safe.",
    ("cb1_agonist", "cb1_agonist"): "ℹ️ Multiple CB1 agonists — receptor saturation risk above 3 agents.",
    ("antipsychotic", "antipsychotic"): "⚠️ Two antipsychotics (Seroquel + Olanzapine) — additive metabolic risk (weight, glucose, lipids). Monitor metabolic panel quarterly.",
    ("benzo_gaba", "benzo_gaba"): "⚠️ Multiple GABA-A agents (e.g. Klonopin + Lunesta) — additive CNS depression. Use only one per night; as-needed only.",
    ("serotonin_modulator", "serotonin_precursor"): "⚠️ Saffron (SSRI-like) + 5-HTP (serotonin precursor) — serotonin syndrome risk. Separate by at least 12 hours.",
    ("stimulant", "stimulant"): "ℹ️ Focalin + Qelbree — coordinate with prescriber. Both affect NE/DA; additive cardiovascular effects.",
    ("nmda_modulator", "nmda_modulator"): "ℹ️ Multiple NMDA modulators (Ketamine + Amantadine + Magnesium + NAC + Glycine) — rich but complex NMDA environment. Generally synergistic; titrate carefully.",
    ("gut_brain", "gut_brain"): "ℹ️ Multiple gut-brain agents — generally synergistic (probiotics + prebiotics + prokinetics work in complementary layers).",
}


def detect_interactions(supp_objects: List[Supplement]) -> List[str]:
    """Detect pharmacological interactions between supplements."""
    warnings = []
    groups = [s.interaction_group for s in supp_objects if s.interaction_group]

    # Check group conflicts
    for i in range(len(groups)):
        for j in range(i + 1, len(groups)):
            key = tuple(sorted([groups[i], groups[j]]))
            if key in INTERACTION_CONFLICTS:
                msg = INTERACTION_CONFLICTS[key]
                if msg not in warnings:
                    warnings.append(msg)

    # Check known interaction notes
    for s in supp_objects:
        for note in s.known_interactions:
            if note not in warnings:
                warnings.append(f"💊 {s.name}: {note}")

    return warnings


# ============================================================
# PERMISSIBILITY DISTRIBUTION (PD — URB #615)
# ============================================================

def compute_pd(gile_truth: float, d2: float, lcc: float) -> Dict[str, float]:
    """
    Compute the 5-state PD (Permissibility Distribution) over {TT, TI, TF, DT, EV}.
    Based on URB #615 logic with D2 as the Tralse meter (URB #619).

    TT  = True-Tralse (high truth, some indeterminacy)
    TI  = Tralse-Indeterminate (mid-truth, high indeterminacy)
    TF  = Tralse-False (low truth, some indeterminacy)
    DT  = Double Tralse (total indeterminacy / absence of truth-content)
    EV  = EV-dominant (existence-driven, truth secondary)
    """
    # D2 drives indeterminacy allocation
    # gile_truth drives T-pole vs F-pole
    # lcc drives EV weight

    dt_weight = max(0.0, (d2 - 0.35) / 0.65) ** 1.5  # rises sharply above 0.35
    dt_weight = min(dt_weight, 0.70)

    remaining = 1.0 - dt_weight

    ev_weight = remaining * (1.0 - gile_truth) * 0.3 * (1.0 - lcc * 0.5)
    ev_weight = max(0.0, ev_weight)
    remaining -= ev_weight

    # Indeterminacy band (TI) peaks at d2=0.5
    ti_weight = remaining * (1.0 - abs(d2 - 0.5) * 2) * d2
    ti_weight = max(0.0, ti_weight)
    remaining -= ti_weight

    # Allocate TT vs TF by gile_truth
    tt_weight = remaining * gile_truth
    tf_weight = remaining * (1.0 - gile_truth)

    total = tt_weight + ti_weight + tf_weight + dt_weight + ev_weight
    if total <= 0:
        return {'TT': 0.2, 'TI': 0.2, 'TF': 0.2, 'DT': 0.2, 'EV': 0.2}

    return {
        'TT': round(tt_weight / total, 3),
        'TI': round(ti_weight / total, 3),
        'TF': round(tf_weight / total, 3),
        'DT': round(dt_weight / total, 3),
        'EV': round(ev_weight / total, 3),
    }


# ============================================================
# EXISTENCE VALUE (EV — URB #609)
# ============================================================

def compute_ev(gile_g: float, gile_i: float, gile_l: float, gile_e: float,
               lcc: float, coherence: float) -> Dict[str, float]:
    """
    Compute Holistic Existence Matrix (HEM) across HEM Dimensions.
    HEM-D1 = EF (physical causal presence); HEM-D2 = Moral; HEM-D3 = Meaning; HEM-D4 = Aesthetics.
    """
    fde1 = (gile_e * 0.6 + lcc * 0.4)                    # EF: physical/energetic
    fde2 = max(0.0, gile_g)                                # Moral Presence (no negatives — privation)
    fde3 = (gile_i * 0.55 + gile_l * 0.45)               # Conscious Meaning
    fde4 = (coherence * 0.5 + gile_l * 0.3 + gile_e * 0.2)  # Aesthetics / structural harmony

    ev_total = 0.35 * fde1 + 0.25 * fde2 + 0.25 * fde3 + 0.15 * fde4

    return {
        'fde1_ef': round(fde1, 3),
        'fde2_moral': round(fde2, 3),
        'fde3_meaning': round(fde3, 3),
        'fde4_aesthetics': round(fde4, 3),
        'ev_total': round(ev_total, 3),
    }


# ============================================================
# PREDICTION RESULT
# ============================================================

@dataclass
class PredictionResult:
    """Result of pharmacological simulation"""
    timestamp: datetime
    supplements: List[str]

    # Predicted changes
    lcc_change: float = 0.0
    gile_g_change: float = 0.0
    gile_i_change: float = 0.0
    gile_l_change: float = 0.0
    gile_e_change: float = 0.0
    coherence_change: float = 0.0
    true_tralseness_change: float = 0.0  # kept for DB compat

    # Predicted final state
    final_lcc: float = 0.0
    final_gile_composite: float = 0.0   # canonical weights
    final_gile_truth: float = 0.0       # gile_composite × coherence
    final_coherence: float = 0.0
    final_true_tralseness: float = 0.0  # kept for DB compat

    # HEM D2 (Tralse meter — URB #619)
    hem_d2_before: float = 0.0
    hem_d2_after: float = 0.0

    # EV (URB #609)
    ev_before: Dict = field(default_factory=dict)
    ev_after: Dict = field(default_factory=dict)

    # PD distribution (URB #615)
    pd_before: Dict = field(default_factory=dict)
    pd_after: Dict = field(default_factory=dict)

    # Biometric predictions
    heart_rate_change: float = 0.0
    rmssd_change: float = 0.0

    # Timeline
    time_to_onset_min: float = 30.0
    time_to_peak_min: float = 60.0
    duration_hours: float = 4.0

    # Anandamide
    anandamide_multiplier: float = 1.0

    # Safety
    epilepsy_flags: List[Dict] = field(default_factory=list)
    interaction_warnings: List[str] = field(default_factory=list)

    # Phenomology
    predicted_sensations: List[str] = field(default_factory=list)
    predicted_emotions: List[str] = field(default_factory=list)
    synchronicity_likelihood: float = 0.5
    confidence: float = 0.5


# ============================================================
# MAIN SIMULATOR CLASS
# ============================================================

class TIPharmacologicalSimulator:
    """
    Personalized pharmacological simulator using TI framework.
    Integrates URB #619 (HEM-EF Bridge) and URB #615 (PD/MR/EAR).
    """

    def __init__(self, user_id: str = 'brandon'):
        self.user_id = user_id
        self.genetic_profile = GeneticProfile()
        self.load_user_profile()

    def load_user_profile(self):
        if not DATABASE_URL:
            self._set_brandon_defaults()
            return

        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor(cursor_factory=RealDictCursor)
            cur.execute("""
                SELECT * FROM ti_genetic_profiles
                WHERE user_id = %s
                ORDER BY created_at DESC LIMIT 1
            """, (self.user_id,))
            row = cur.fetchone()
            if row:
                self.genetic_profile = GeneticProfile(
                    faah_activity=row.get('faah_activity', 1.0),
                    comt_activity=row.get('comt_activity', 1.0),
                    serotonin_sensitivity=row.get('serotonin_sensitivity', 1.0),
                    bdnf_expression=row.get('bdnf_expression', 1.0),
                    schizotypy_snp_count=row.get('schizotypy_snp_count', 0),
                    cb1_receptor_density=row.get('cb1_receptor_density', 1.0),
                    gaba_sensitivity=row.get('gaba_sensitivity', 1.0),
                    dopamine_sensitivity=row.get('dopamine_sensitivity', 1.0)
                )
            else:
                self._set_brandon_defaults()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Could not load profile from DB: {e}")
            self._set_brandon_defaults()

    def _set_brandon_defaults(self):
        self.genetic_profile = GeneticProfile(
            faah_activity=0.7,
            comt_activity=0.8,
            serotonin_sensitivity=1.3,
            bdnf_expression=1.1,
            schizotypy_snp_count=180,
            cb1_receptor_density=1.2,
            gaba_sensitivity=1.1,
            dopamine_sensitivity=1.2
        )

    def _resolve_supplements(self, supplements: List[str]) -> List[Supplement]:
        """Match supplement keys/names to database entries."""
        result = []
        seen = set()
        for name in supplements:
            key = name.lower().replace(' ', '_').replace('-', '_')
            if key in SUPPLEMENT_DATABASE and key not in seen:
                result.append(SUPPLEMENT_DATABASE[key])
                seen.add(key)
                continue
            if name.lower() in SUPPLEMENT_DATABASE and name.lower() not in seen:
                result.append(SUPPLEMENT_DATABASE[name.lower()])
                seen.add(name.lower())
                continue
            # Partial match
            for k, s in SUPPLEMENT_DATABASE.items():
                if k not in seen and (name.lower() in k or k in name.lower()):
                    result.append(s)
                    seen.add(k)
                    break
        return result

    def simulate(
        self,
        supplements: List[str],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState,
        session_type: str = 'standard'
    ) -> PredictionResult:
        """
        Simulate supplement stack effects through the TI framework.
        Integrates canonical GILE weights, EV, PD, HEM D2 (URB #619).
        """
        supp_objects = self._resolve_supplements(supplements)

        # --- Interaction detection ---
        interaction_warnings = detect_interactions(supp_objects)

        # --- Epilepsy flags ---
        epilepsy_flags = []
        for s in supp_objects:
            if s.epilepsy_risk in ("MODERATE", "HIGH", "CONTRAINDICATED"):
                epilepsy_flags.append({
                    'supplement': s.name,
                    'risk': s.epilepsy_risk,
                    'note': s.epilepsy_note
                })

        # --- Combine mechanisms (multiplicative for same-receptor effects) ---
        total_faah = 0.0
        total_cb1 = 0.0
        total_nape = 0.0
        total_anti_inflam = 0.0
        total_bdnf = 0.0
        total_dopamine = 0.0
        total_serotonin = 0.0
        total_gaba = 0.0
        total_nmda = 0.0
        total_ach = 0.0
        total_mito = 0.0

        total_lcc_boost = 0.0
        total_love = 0.0
        total_intuition = 0.0
        total_goodness = 0.0
        total_env = 0.0

        avg_absorption = 0.0
        avg_duration = 0.0

        for s in supp_objects:
            total_faah = 1 - (1 - total_faah) * (1 - s.faah_inhibition)
            total_cb1 = 1 - (1 - total_cb1) * (1 - s.cb1_activation)
            total_nape = 1 - (1 - total_nape) * (1 - s.nape_pld_activation)
            total_anti_inflam = 1 - (1 - total_anti_inflam) * (1 - s.anti_inflammatory)
            total_bdnf = 1 - (1 - total_bdnf) * (1 - s.bdnf_upregulation)
            total_dopamine = 1 - (1 - total_dopamine) * (1 - s.dopamine_modulation)
            total_serotonin = 1 - (1 - total_serotonin) * (1 - s.serotonin_modulation)
            total_gaba = 1 - (1 - total_gaba) * (1 - s.gaba_modulation)
            total_nmda = 1 - (1 - total_nmda) * (1 - s.nmda_modulation)
            total_ach = 1 - (1 - total_ach) * (1 - s.acetylcholine_modulation)
            total_mito = 1 - (1 - total_mito) * (1 - s.mitochondrial_support)

            total_lcc_boost += s.lcc_boost
            total_love += s.love_boost
            total_intuition += s.intuition_boost
            total_goodness += s.goodness_boost
            total_env += s.environment_boost

            avg_absorption += s.absorption_time_min
            avg_duration += s.half_life_hours

        n = len(supp_objects) if supp_objects else 1
        avg_absorption /= n
        avg_duration /= n

        # --- Genetic modifiers ---
        genetic_amp = self.genetic_profile.consciousness_amplification_factor()
        faah_eff = total_faah * (2.0 - self.genetic_profile.faah_activity)
        cb1_eff = total_cb1 * self.genetic_profile.cb1_receptor_density
        dopamine_eff = total_dopamine * self.genetic_profile.dopamine_sensitivity
        serotonin_eff = total_serotonin * self.genetic_profile.serotonin_sensitivity

        # --- Anandamide multiplier ---
        anandamide_mult = 1.0
        anandamide_mult *= (1 + faah_eff * 0.8)
        anandamide_mult *= (1 + total_nape * 0.6)
        anandamide_mult *= (1 + cb1_eff * 0.3)

        # --- Consciousness baseline amplification (non-linear: high LCC = better response) ---
        cons_mult = 1.0 + (current_consciousness.lcc - 0.5) * 0.5

        # --- GILE changes ---
        g_change = (total_goodness + total_anti_inflam * 0.02 + total_nmda * 0.01) * genetic_amp
        i_change = (total_intuition + total_ach * 0.03 + total_bdnf * 0.02
                    + dopamine_eff * 0.015) * genetic_amp * (1 + self.genetic_profile.schizotypy_snp_count / 200)
        l_change = (total_love + (anandamide_mult - 1) * 0.04 + serotonin_eff * 0.02) * genetic_amp
        e_change = (total_env + total_mito * 0.03 + total_anti_inflam * 0.01) * genetic_amp

        lcc_change = total_lcc_boost * genetic_amp * cons_mult
        coherence_change = (total_anti_inflam * 0.05 + total_gaba * 0.02 + total_nmda * 0.01) * cons_mult

        # --- Final states ---
        final_g = float(np.clip(current_consciousness.gile_g + g_change, 0, 1))
        final_i = float(np.clip(current_consciousness.gile_i + i_change, 0, 1))
        final_l = float(np.clip(current_consciousness.gile_l + l_change, 0, 1))
        final_e = float(np.clip(current_consciousness.gile_e + e_change, 0, 1))
        final_lcc = float(np.clip(current_consciousness.lcc + lcc_change, 0, 1))
        final_coherence = float(np.clip(current_consciousness.coherence + coherence_change, 0, 1))

        # Canonical GILE composite (URB #576)
        final_gile_composite = GILE_W_G * final_g + GILE_W_I * final_i + GILE_W_L * final_l + GILE_W_E * final_e
        final_gile_truth = final_gile_composite * final_coherence

        # HEM D2 before/after (URB #619)
        d2_before = current_consciousness.hem_d2
        dims_after = [final_g, final_i, final_l, final_e]
        d2_after = float(np.clip(
            0.5 * float(np.var(dims_after)) * 4 + 0.5 * (1.0 - final_coherence), 0, 1
        ))

        # EV before/after (URB #609)
        ev_before = compute_ev(current_consciousness.gile_g, current_consciousness.gile_i,
                               current_consciousness.gile_l, current_consciousness.gile_e,
                               current_consciousness.lcc, current_consciousness.coherence)
        ev_after = compute_ev(final_g, final_i, final_l, final_e, final_lcc, final_coherence)

        # PD before/after (URB #615)
        pd_before = compute_pd(current_consciousness.gile_truth_score, d2_before, current_consciousness.lcc)
        pd_after = compute_pd(final_gile_truth, d2_after, final_lcc)

        # Biometrics
        hr_change = -(anandamide_mult - 1) * 15 - total_gaba * 3
        rmssd_change = (anandamide_mult - 1) * 25 + total_gaba * 5

        # Sensations & emotions
        sensations, emotions = self._predict_phenomenology(
            anandamide_mult, cb1_eff, total_anti_inflam, total_bdnf,
            l_change, i_change, lcc_change, total_ach, total_dopamine, final_lcc
        )

        # Synchronicity: now includes D2 reduction as signal
        d2_reduction = max(0.0, d2_before - d2_after)
        synchronicity = min(0.95, final_lcc * 0.7 + (anandamide_mult - 1) * 0.1 + d2_reduction * 0.2)

        # Confidence
        confidence = 0.60
        if self.genetic_profile.schizotypy_snp_count > 0:
            confidence += 0.10
        if current_consciousness.lcc > 0.9:
            confidence += 0.08
        if len(supp_objects) >= 3:
            confidence += 0.05   # more data points
        confidence = min(0.95, confidence)

        # Legacy true_tralseness field
        final_tt = 0.4 * final_lcc + 0.3 * final_coherence + 0.3 * final_gile_composite

        return PredictionResult(
            timestamp=datetime.now(),
            supplements=[s.name for s in supp_objects],
            lcc_change=lcc_change,
            gile_g_change=g_change,
            gile_i_change=i_change,
            gile_l_change=l_change,
            gile_e_change=e_change,
            coherence_change=coherence_change,
            true_tralseness_change=final_tt - current_consciousness.true_tralseness,
            final_lcc=final_lcc,
            final_gile_composite=final_gile_composite,
            final_gile_truth=final_gile_truth,
            final_coherence=final_coherence,
            final_true_tralseness=final_tt,
            hem_d2_before=d2_before,
            hem_d2_after=d2_after,
            ev_before=ev_before,
            ev_after=ev_after,
            pd_before=pd_before,
            pd_after=pd_after,
            heart_rate_change=hr_change,
            rmssd_change=rmssd_change,
            time_to_onset_min=avg_absorption * 0.5,
            time_to_peak_min=avg_absorption,
            duration_hours=avg_duration * 2,
            anandamide_multiplier=anandamide_mult,
            epilepsy_flags=epilepsy_flags,
            interaction_warnings=interaction_warnings,
            predicted_sensations=sensations,
            predicted_emotions=emotions,
            synchronicity_likelihood=synchronicity,
            confidence=confidence,
        )

    def _predict_phenomenology(
        self, anandamide_mult, cb1_eff, anti_inflam, bdnf,
        l_change, i_change, lcc_change, ach, dopamine, final_lcc
    ) -> Tuple[List[str], List[str]]:
        sensations = []
        emotions = []

        if anandamide_mult > 1.5:
            sensations.append("Warmth spreading through body")
            sensations.append("Tingling in extremities")
        if anandamide_mult > 2.0:
            sensations.append("Feeling of lightness")
            sensations.append("Reduced physical tension")
        if anti_inflam > 0.5:
            sensations.append("Reduced inflammation / pain perception")
        if cb1_eff > 0.5:
            sensations.append("Mild euphoria")
        if ach > 0.4:
            sensations.append("Mental sharpness and clarity")
        if dopamine > 0.4:
            sensations.append("Motivated, energized")

        if l_change > 0.04:
            emotions.append("Deep sense of love and connection")
        if i_change > 0.03:
            emotions.append("Enhanced intuition and knowing")
        if lcc_change > 0.02:
            emotions.append("Expansion of consciousness awareness")
        if anti_inflam > 0.5:
            emotions.append("Peace and calmness")
        if bdnf > 0.4:
            emotions.append("Openness and neuroplasticity — good time to learn")
        if final_lcc > 0.95:
            emotions.append("Sense of future pulling forward")
            emotions.append("Synchronicities becoming obvious")

        return sensations, emotions

    def predict_time_series(
        self,
        supplements: List[str],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState,
        duration_hours: float = 6.0,
        interval_min: float = 15.0
    ) -> List[Dict]:
        peak = self.simulate(supplements, current_consciousness, current_biometrics)

        series = []
        t = 0.0
        while t <= duration_hours * 60:
            tf = self._time_factor(t, peak.time_to_onset_min, peak.time_to_peak_min,
                                   peak.duration_hours * 60)
            series.append({
                'time_min': t,
                'time_hours': t / 60,
                'lcc': current_consciousness.lcc + peak.lcc_change * tf,
                'gile_g': current_consciousness.gile_g + peak.gile_g_change * tf,
                'gile_l': current_consciousness.gile_l + peak.gile_l_change * tf,
                'gile_i': current_consciousness.gile_i + peak.gile_i_change * tf,
                'gile_e': current_consciousness.gile_e + peak.gile_e_change * tf,
                'coherence': current_consciousness.coherence + peak.coherence_change * tf,
                'heart_rate': current_biometrics.heart_rate + peak.heart_rate_change * tf,
                'rmssd': current_biometrics.rmssd + peak.rmssd_change * tf,
                'anandamide_multiplier': 1.0 + (peak.anandamide_multiplier - 1.0) * tf,
                'effect_intensity': tf,
            })
            t += interval_min
        return series

    def _time_factor(self, t, onset, peak_t, total) -> float:
        if t < onset:
            return (t / onset) ** 2 * 0.3 if onset > 0 else 0.0
        elif t < peak_t:
            p = (t - onset) / (peak_t - onset) if peak_t > onset else 1.0
            return 0.3 + 0.7 * p
        elif t < total:
            dp = (t - peak_t) / (total - peak_t) if total > peak_t else 1.0
            return float(np.exp(-dp * 2))
        return 0.1

    def compare_stacks(
        self,
        stack_options: List[List[str]],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState
    ) -> List[Tuple[List[str], PredictionResult]]:
        results = []
        for stack in stack_options:
            pred = self.simulate(stack, current_consciousness, current_biometrics)
            results.append((stack, pred))
        results.sort(key=lambda x: x[1].final_gile_truth, reverse=True)
        return results

    def save_prediction(self, prediction: PredictionResult):
        if not DATABASE_URL:
            return
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO ti_pharmacological_predictions (
                    user_id, timestamp, supplements,
                    predicted_lcc, predicted_gile_composite, predicted_coherence,
                    predicted_true_tralseness, predicted_anandamide_multiplier,
                    predicted_sensations, predicted_emotions, confidence
                ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING id
            """, (
                self.user_id, prediction.timestamp,
                json.dumps(prediction.supplements),
                prediction.final_lcc,
                prediction.final_gile_composite,
                prediction.final_coherence,
                prediction.final_true_tralseness,
                prediction.anandamide_multiplier,
                json.dumps(prediction.predicted_sensations),
                json.dumps(prediction.predicted_emotions),
                prediction.confidence
            ))
            pred_id = cur.fetchone()[0]
            conn.commit()
            cur.close()
            conn.close()
            return pred_id
        except Exception as e:
            print(f"Could not save prediction: {e}")
            return None

    def validate_prediction(
        self,
        prediction_id: int,
        actual_lcc: float,
        actual_gile_composite: float,
        actual_sensations: List[str],
        actual_emotions: List[str]
    ):
        if not DATABASE_URL:
            return
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor()
            cur.execute("""
                UPDATE ti_pharmacological_predictions
                SET actual_lcc = %s, actual_gile_composite = %s,
                    actual_sensations = %s, actual_emotions = %s,
                    validated_at = NOW()
                WHERE id = %s
            """, (actual_lcc, actual_gile_composite,
                  json.dumps(actual_sensations), json.dumps(actual_emotions),
                  prediction_id))
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Could not validate prediction: {e}")

    def get_prediction_history(self, limit: int = 20) -> List[Dict]:
        if not DATABASE_URL:
            return []
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor(cursor_factory=RealDictCursor)
            cur.execute("""
                SELECT id, timestamp, supplements, predicted_lcc, predicted_gile_composite,
                       predicted_anandamide_multiplier, confidence,
                       actual_lcc, actual_gile_composite, validated_at
                FROM ti_pharmacological_predictions
                WHERE user_id = %s
                ORDER BY timestamp DESC
                LIMIT %s
            """, (self.user_id, limit))
            rows = [dict(r) for r in cur.fetchall()]
            cur.close()
            conn.close()
            return rows
        except Exception as e:
            print(f"Could not load history: {e}")
            return []


# ============================================================
# DATABASE SETUP
# ============================================================

def create_database_tables():
    if not DATABASE_URL:
        print("No DATABASE_URL found")
        return
    try:
        conn = psycopg2.connect(DATABASE_URL)
        cur = conn.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS ti_genetic_profiles (
                id SERIAL PRIMARY KEY,
                user_id VARCHAR(100) NOT NULL,
                faah_activity REAL DEFAULT 1.0,
                comt_activity REAL DEFAULT 1.0,
                serotonin_sensitivity REAL DEFAULT 1.0,
                bdnf_expression REAL DEFAULT 1.0,
                schizotypy_snp_count INTEGER DEFAULT 0,
                cb1_receptor_density REAL DEFAULT 1.0,
                gaba_sensitivity REAL DEFAULT 1.0,
                dopamine_sensitivity REAL DEFAULT 1.0,
                raw_genetic_data JSONB,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS ti_pharmacological_predictions (
                id SERIAL PRIMARY KEY,
                user_id VARCHAR(100) NOT NULL,
                timestamp TIMESTAMP NOT NULL,
                supplements JSONB,
                predicted_lcc REAL,
                predicted_gile_composite REAL,
                predicted_coherence REAL,
                predicted_true_tralseness REAL,
                predicted_anandamide_multiplier REAL,
                predicted_sensations JSONB,
                predicted_emotions JSONB,
                confidence REAL,
                actual_lcc REAL,
                actual_gile_composite REAL,
                actual_sensations JSONB,
                actual_emotions JSONB,
                validated_at TIMESTAMP,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        conn.commit()
        cur.close()
        conn.close()
        print("Database tables ready.")
    except Exception as e:
        print(f"Error creating tables: {e}")


if __name__ == "__main__":
    create_database_tables()

    sim = TIPharmacologicalSimulator(user_id='brandon')
    cs = ConsciousnessState(lcc=0.99, gile_g=0.95, gile_i=0.90, gile_l=0.99, gile_e=0.95, coherence=0.99)
    bio = BiometricState(heart_rate=60, rmssd=80, alpha_power=0.85, gamma_power=0.40)

    stack = ['curcubrain', 'macamides_5pct', 'magnesium_l_threonate', 'omega3_dha', 'vitamin_b6_p5p']
    result = sim.simulate(stack, cs, bio)

    print(f"Anandamide: {result.anandamide_multiplier:.2f}x")
    print(f"Final LCC: {result.final_lcc:.1%}")
    print(f"GILE Truth: {result.final_gile_truth:.3f}")
    print(f"HEM D2 before/after: {result.hem_d2_before:.3f} → {result.hem_d2_after:.3f}")
    print(f"HEM total: {result.ev_before['ev_total']} → {result.ev_after['ev_total']}")
    print(f"PD before: {result.pd_before}")
    print(f"PD after:  {result.pd_after}")
