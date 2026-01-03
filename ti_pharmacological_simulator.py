"""
TI Pharmacological Simulator
============================
Personalized drug/supplement effect modeling using:
- Consciousness metrics (LCC, GILE, True-Tralseness)
- Genetic variants (FAAH, COMT, serotonin receptors, schizotypy SNPs)
- Biometrics (HRV, EEG, heart rate)
- Historical response patterns

This does what Google's models CANNOT:
- Model effects through consciousness states
- Account for non-linear genetic × consciousness interactions
- Predict YOUR specific response, not population averages
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


@dataclass
class GeneticProfile:
    """User's genetic variants affecting pharmacology"""
    faah_activity: float = 1.0  # 0.0 = low (good), 1.0 = normal, 2.0 = high (fast metabolism)
    comt_activity: float = 1.0  # 0.0 = low (worrier), 1.0 = normal, 2.0 = high (warrior)
    serotonin_sensitivity: float = 1.0  # 0.0 = low, 1.0 = normal, 2.0 = high
    bdnf_expression: float = 1.0  # 0.0 = low, 1.0 = normal, 2.0 = high
    schizotypy_snp_count: int = 0  # Number of schizotypy-related SNPs
    cb1_receptor_density: float = 1.0  # 0.5 = low, 1.0 = normal, 1.5 = high
    gaba_sensitivity: float = 1.0
    dopamine_sensitivity: float = 1.0
    
    def consciousness_amplification_factor(self) -> float:
        """Calculate how much consciousness effects are amplified by genetics"""
        base = 1.0
        base += (self.schizotypy_snp_count / 100) * 0.5  # More SNPs = more amplification
        base += (self.cb1_receptor_density - 1.0) * 0.3
        base += (self.serotonin_sensitivity - 1.0) * 0.2
        return max(0.5, min(2.0, base))


@dataclass
class ConsciousnessState:
    """Current consciousness metrics"""
    lcc: float = 0.5  # Love-Consciousness Coupling (0-1)
    gile_g: float = 0.5  # Goodness dimension
    gile_i: float = 0.5  # Intuition dimension
    gile_l: float = 0.5  # Love dimension
    gile_e: float = 0.5  # Environment dimension
    coherence: float = 0.5  # Brain-heart coherence
    true_tralseness: float = 0.5  # Overall truth-alignment
    
    @property
    def gile_composite(self) -> float:
        return 0.25 * self.gile_g + 0.25 * self.gile_i + 0.30 * self.gile_l + 0.20 * self.gile_e
    
    def to_dict(self) -> Dict:
        return {
            'lcc': self.lcc,
            'gile_g': self.gile_g,
            'gile_i': self.gile_i,
            'gile_l': self.gile_l,
            'gile_e': self.gile_e,
            'gile_composite': self.gile_composite,
            'coherence': self.coherence,
            'true_tralseness': self.true_tralseness
        }


@dataclass
class BiometricState:
    """Current biometric measurements"""
    heart_rate: float = 70.0  # bpm
    rmssd: float = 40.0  # ms (HRV measure)
    sdnn: float = 50.0  # ms
    alpha_power: float = 0.5  # 0-1 (EEG)
    beta_power: float = 0.3
    theta_power: float = 0.4
    gamma_power: float = 0.2
    delta_power: float = 0.3
    
    @property
    def parasympathetic_dominance(self) -> float:
        """Calculate PNS dominance from HRV"""
        return min(1.0, self.rmssd / 80.0)
    
    @property
    def eeg_coherence(self) -> float:
        """Calculate EEG coherence from band powers"""
        return (self.alpha_power + self.gamma_power * 0.5) / (self.beta_power + 0.1)


@dataclass
class Supplement:
    """Supplement with pharmacological properties"""
    name: str
    dose_mg: float
    
    # Pharmacokinetic properties
    absorption_time_min: float = 30.0  # Time to peak absorption
    half_life_hours: float = 4.0  # Elimination half-life
    bbb_penetration: float = 0.5  # 0-1, how well it crosses blood-brain barrier
    
    # Mechanism of action (0-1 scale of effect strength)
    faah_inhibition: float = 0.0  # Blocks anandamide breakdown
    cb1_activation: float = 0.0  # Activates cannabinoid receptor 1
    cb2_activation: float = 0.0  # Activates cannabinoid receptor 2
    nape_pld_activation: float = 0.0  # Enhances anandamide synthesis
    anti_inflammatory: float = 0.0  # Reduces neuroinflammation
    bdnf_upregulation: float = 0.0  # Increases BDNF expression
    gaba_modulation: float = 0.0  # Affects GABA system
    serotonin_modulation: float = 0.0  # Affects serotonin system
    dopamine_modulation: float = 0.0  # Affects dopamine system
    
    # Consciousness effects (TI-specific)
    lcc_boost: float = 0.0  # Direct effect on Love-Consciousness Coupling
    love_boost: float = 0.0  # Effect on Love dimension
    intuition_boost: float = 0.0  # Effect on Intuition dimension
    goodness_boost: float = 0.0  # Effect on Goodness dimension
    environment_boost: float = 0.0  # Effect on Environment dimension


# Pre-defined supplement database
SUPPLEMENT_DATABASE: Dict[str, Supplement] = {
    'curcubrain': Supplement(
        name='Curcubrain',
        dose_mg=400,
        absorption_time_min=45,
        half_life_hours=6,
        bbb_penetration=0.85,  # BBB-penetrating formula
        faah_inhibition=0.65,
        anti_inflammatory=0.80,
        bdnf_upregulation=0.55,
        lcc_boost=0.03,
        love_boost=0.04,
        intuition_boost=0.02
    ),
    'macamides_5pct': Supplement(
        name='Nootropics Depot 5% Macamides',
        dose_mg=750,
        absorption_time_min=30,
        half_life_hours=4,
        bbb_penetration=0.70,
        cb1_activation=0.70,
        nape_pld_activation=0.60,
        dopamine_modulation=0.45,
        serotonin_modulation=0.35,
        lcc_boost=0.05,
        love_boost=0.06,
        intuition_boost=0.04,
        goodness_boost=0.03
    ),
    'pea_palmitoylethanolamide': Supplement(
        name='PEA (Palmitoylethanolamide)',
        dose_mg=1500,
        absorption_time_min=40,
        half_life_hours=5,
        bbb_penetration=0.60,
        nape_pld_activation=0.75,
        anti_inflammatory=0.70,
        lcc_boost=0.04,
        love_boost=0.05
    ),
    'cbd_oil': Supplement(
        name='CBD Oil',
        dose_mg=25,
        absorption_time_min=20,
        half_life_hours=3,
        bbb_penetration=0.75,
        faah_inhibition=0.50,
        cb1_activation=0.20,
        cb2_activation=0.40,
        anti_inflammatory=0.60,
        gaba_modulation=0.30,
        lcc_boost=0.02,
        love_boost=0.03
    ),
    'kaempferol': Supplement(
        name='Kaempferol',
        dose_mg=50,
        absorption_time_min=35,
        half_life_hours=4,
        bbb_penetration=0.55,
        faah_inhibition=0.45,
        anti_inflammatory=0.50,
        lcc_boost=0.015
    ),
    'maca_standard': Supplement(
        name='Maca Root (Standard)',
        dose_mg=1500,
        absorption_time_min=40,
        half_life_hours=5,
        bbb_penetration=0.40,
        nape_pld_activation=0.30,
        dopamine_modulation=0.25,
        lcc_boost=0.01
    ),
    'magnesium_l_threonate': Supplement(
        name='Magnesium L-Threonate',
        dose_mg=144,
        absorption_time_min=60,
        half_life_hours=8,
        bbb_penetration=0.90,  # Very high BBB penetration
        gaba_modulation=0.40,
        bdnf_upregulation=0.35,
        lcc_boost=0.01,
        intuition_boost=0.02
    ),
    'omega3_dha': Supplement(
        name='Omega-3 DHA',
        dose_mg=1000,
        absorption_time_min=90,
        half_life_hours=24,
        bbb_penetration=0.70,
        anti_inflammatory=0.60,
        bdnf_upregulation=0.30,
        lcc_boost=0.01
    ),
    'vitamin_b6_p5p': Supplement(
        name='Vitamin B6 (P5P)',
        dose_mg=50,
        absorption_time_min=30,
        half_life_hours=6,
        bbb_penetration=0.85,
        nape_pld_activation=0.25,  # Cofactor for NAPE-PLD
        serotonin_modulation=0.30,
        dopamine_modulation=0.25,
        gaba_modulation=0.20,
        lcc_boost=0.005
    ),
    'quercetin': Supplement(
        name='Quercetin',
        dose_mg=500,
        absorption_time_min=45,
        half_life_hours=5,
        bbb_penetration=0.50,
        faah_inhibition=0.40,
        anti_inflammatory=0.65,
        lcc_boost=0.015
    ),
    'luteolin': Supplement(
        name='Luteolin',
        dose_mg=100,
        absorption_time_min=35,
        half_life_hours=4,
        bbb_penetration=0.55,
        faah_inhibition=0.55,
        anti_inflammatory=0.50,
        lcc_boost=0.02
    ),
    'black_seed_oil': Supplement(
        name='Black Seed Oil (Thymoquinone)',
        dose_mg=500,
        absorption_time_min=40,
        half_life_hours=5,
        bbb_penetration=0.45,
        faah_inhibition=0.35,
        anti_inflammatory=0.55,
        lcc_boost=0.015
    )
}


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
    true_tralseness_change: float = 0.0
    
    # Predicted final state
    final_lcc: float = 0.0
    final_gile_composite: float = 0.0
    final_coherence: float = 0.0
    final_true_tralseness: float = 0.0
    
    # Predicted biometric changes
    heart_rate_change: float = 0.0
    rmssd_change: float = 0.0
    
    # Time-series predictions
    time_to_onset_min: float = 30.0
    time_to_peak_min: float = 60.0
    duration_hours: float = 4.0
    
    # Anandamide estimation
    anandamide_multiplier: float = 1.0
    
    # Physical sensation predictions
    predicted_sensations: List[str] = field(default_factory=list)
    predicted_emotions: List[str] = field(default_factory=list)
    synchronicity_likelihood: float = 0.5
    
    # Confidence
    confidence: float = 0.5


class TIPharmacologicalSimulator:
    """
    Personalized pharmacological simulator using TI framework.
    
    This models drug/supplement effects through consciousness metrics,
    genetics, and biometrics - something population-based AI cannot do.
    """
    
    def __init__(self, user_id: str = 'brandon'):
        self.user_id = user_id
        self.genetic_profile = GeneticProfile()
        self.load_user_profile()
    
    def load_user_profile(self):
        """Load user's genetic and historical data from database"""
        if not DATABASE_URL:
            self._set_brandon_defaults()
            return
            
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor(cursor_factory=RealDictCursor)
            
            # Try to load genetic profile
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
        """Set Brandon's known genetic profile"""
        self.genetic_profile = GeneticProfile(
            faah_activity=0.7,  # Lower = good for anandamide
            comt_activity=0.8,  # Slightly lower = worrier variant
            serotonin_sensitivity=1.3,  # Higher sensitivity
            bdnf_expression=1.1,
            schizotypy_snp_count=180,  # 180+ schizotypy SNPs
            cb1_receptor_density=1.2,  # Higher density
            gaba_sensitivity=1.1,
            dopamine_sensitivity=1.2
        )
    
    def simulate(
        self,
        supplements: List[str],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState,
        session_type: str = 'standard'
    ) -> PredictionResult:
        """
        Simulate the effects of supplements on consciousness state.
        
        This is where TI beats Google - we model through consciousness, not just biology.
        """
        
        # Get supplement objects
        supp_objects = []
        for name in supplements:
            key = name.lower().replace(' ', '_').replace('-', '_')
            if key in SUPPLEMENT_DATABASE:
                supp_objects.append(SUPPLEMENT_DATABASE[key])
            elif name.lower() in SUPPLEMENT_DATABASE:
                supp_objects.append(SUPPLEMENT_DATABASE[name.lower()])
        
        if not supp_objects:
            # Try partial matching
            for name in supplements:
                for key, supp in SUPPLEMENT_DATABASE.items():
                    if name.lower() in key or key in name.lower():
                        supp_objects.append(supp)
                        break
        
        # Calculate combined effects
        total_faah_inhibition = 0.0
        total_cb1_activation = 0.0
        total_nape_pld_activation = 0.0
        total_anti_inflammatory = 0.0
        total_bdnf = 0.0
        total_lcc_boost = 0.0
        total_love_boost = 0.0
        total_intuition_boost = 0.0
        total_goodness_boost = 0.0
        total_environment_boost = 0.0
        avg_absorption_time = 0.0
        avg_duration = 0.0
        
        for supp in supp_objects:
            # Multiplicative stacking for same-mechanism effects (not additive)
            total_faah_inhibition = 1 - (1 - total_faah_inhibition) * (1 - supp.faah_inhibition)
            total_cb1_activation = 1 - (1 - total_cb1_activation) * (1 - supp.cb1_activation)
            total_nape_pld_activation = 1 - (1 - total_nape_pld_activation) * (1 - supp.nape_pld_activation)
            total_anti_inflammatory = 1 - (1 - total_anti_inflammatory) * (1 - supp.anti_inflammatory)
            total_bdnf = 1 - (1 - total_bdnf) * (1 - supp.bdnf_upregulation)
            
            # Consciousness effects stack additively
            total_lcc_boost += supp.lcc_boost
            total_love_boost += supp.love_boost
            total_intuition_boost += supp.intuition_boost
            total_goodness_boost += supp.goodness_boost
            total_environment_boost += supp.environment_boost
            
            avg_absorption_time += supp.absorption_time_min
            avg_duration += supp.half_life_hours
        
        n_supps = len(supp_objects) if supp_objects else 1
        avg_absorption_time /= n_supps
        avg_duration /= n_supps
        
        # Apply genetic modifiers
        genetic_amp = self.genetic_profile.consciousness_amplification_factor()
        
        # FAAH inhibition is more effective with lower FAAH activity
        faah_effectiveness = total_faah_inhibition * (2.0 - self.genetic_profile.faah_activity)
        
        # CB1 activation is more effective with higher receptor density
        cb1_effectiveness = total_cb1_activation * self.genetic_profile.cb1_receptor_density
        
        # Calculate anandamide multiplier
        # FAAH inhibition prevents breakdown, NAPE-PLD increases synthesis
        anandamide_multiplier = 1.0
        anandamide_multiplier *= (1 + faah_effectiveness * 0.8)  # Up to 80% from FAAH block
        anandamide_multiplier *= (1 + total_nape_pld_activation * 0.6)  # Up to 60% from synthesis
        anandamide_multiplier *= (1 + cb1_effectiveness * 0.3)  # Up to 30% from receptor activation
        
        # Apply consciousness baseline amplification
        # Higher LCC means supplements work BETTER (non-linear)
        consciousness_multiplier = 1.0 + (current_consciousness.lcc - 0.5) * 0.5
        
        # Calculate consciousness changes
        lcc_change = total_lcc_boost * genetic_amp * consciousness_multiplier
        gile_g_change = total_goodness_boost * genetic_amp
        gile_i_change = total_intuition_boost * genetic_amp * (1 + self.genetic_profile.schizotypy_snp_count / 200)
        gile_l_change = total_love_boost * genetic_amp * (anandamide_multiplier - 1) * 0.5
        gile_e_change = total_environment_boost * genetic_amp
        
        # Anti-inflammatory effects boost coherence
        coherence_change = total_anti_inflammatory * 0.05 * consciousness_multiplier
        
        # Calculate final states (capped at reasonable maximums)
        final_lcc = min(1.0, current_consciousness.lcc + lcc_change)
        final_gile_g = min(1.0, current_consciousness.gile_g + gile_g_change)
        final_gile_i = min(1.0, current_consciousness.gile_i + gile_i_change)
        final_gile_l = min(1.0, current_consciousness.gile_l + gile_l_change)
        final_gile_e = min(1.0, current_consciousness.gile_e + gile_e_change)
        final_coherence = min(1.0, current_consciousness.coherence + coherence_change)
        
        final_gile_composite = 0.25 * final_gile_g + 0.25 * final_gile_i + 0.30 * final_gile_l + 0.20 * final_gile_e
        final_true_tralseness = 0.4 * final_lcc + 0.3 * final_coherence + 0.3 * final_gile_composite
        
        # Biometric predictions
        # Higher anandamide = lower heart rate, higher RMSSD (parasympathetic)
        heart_rate_change = -(anandamide_multiplier - 1) * 15  # Up to -15 bpm
        rmssd_change = (anandamide_multiplier - 1) * 25  # Up to +25 ms
        
        # Predict physical sensations based on effects
        sensations = []
        emotions = []
        
        if anandamide_multiplier > 1.5:
            sensations.append("Warmth spreading through body")
            sensations.append("Tingling in extremities")
        if anandamide_multiplier > 2.0:
            sensations.append("Feeling of lightness")
            sensations.append("Reduced physical tension")
        if total_anti_inflammatory > 0.5:
            sensations.append("Reduced inflammation/pain perception")
        if cb1_effectiveness > 0.5:
            sensations.append("Mild euphoria")
        
        if gile_l_change > 0.05:
            emotions.append("Deep sense of love/connection")
        if gile_i_change > 0.03:
            emotions.append("Enhanced intuition/knowing")
        if lcc_change > 0.02:
            emotions.append("Feeling of consciousness expansion")
        if total_anti_inflammatory > 0.5:
            emotions.append("Peace and calmness")
        if final_lcc > 0.95:
            emotions.append("Sense of future pulling forward")
            emotions.append("Synchronicities becoming obvious")
        
        # Synchronicity likelihood based on LCC
        synchronicity_likelihood = min(0.95, final_lcc * 0.9 + (anandamide_multiplier - 1) * 0.1)
        
        # Calculate confidence based on how much data we have
        confidence = 0.6  # Base confidence
        if self.genetic_profile.schizotypy_snp_count > 0:
            confidence += 0.1  # We have genetic data
        if current_consciousness.lcc > 0.9:
            confidence += 0.1  # High baseline = more predictable
        confidence = min(0.95, confidence)
        
        return PredictionResult(
            timestamp=datetime.now(),
            supplements=[s.name for s in supp_objects],
            lcc_change=lcc_change,
            gile_g_change=gile_g_change,
            gile_i_change=gile_i_change,
            gile_l_change=gile_l_change,
            gile_e_change=gile_e_change,
            coherence_change=coherence_change,
            true_tralseness_change=final_true_tralseness - current_consciousness.true_tralseness,
            final_lcc=final_lcc,
            final_gile_composite=final_gile_composite,
            final_coherence=final_coherence,
            final_true_tralseness=final_true_tralseness,
            heart_rate_change=heart_rate_change,
            rmssd_change=rmssd_change,
            time_to_onset_min=avg_absorption_time * 0.5,
            time_to_peak_min=avg_absorption_time,
            duration_hours=avg_duration * 2,
            anandamide_multiplier=anandamide_multiplier,
            predicted_sensations=sensations,
            predicted_emotions=emotions,
            synchronicity_likelihood=synchronicity_likelihood,
            confidence=confidence
        )
    
    def predict_time_series(
        self,
        supplements: List[str],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState,
        duration_hours: float = 6.0,
        interval_min: float = 15.0
    ) -> List[Dict]:
        """
        Predict consciousness state over time after taking supplements.
        Returns time-series data for visualization.
        """
        
        # Get peak prediction
        peak_result = self.simulate(supplements, current_consciousness, current_biometrics)
        
        time_series = []
        current_time = 0.0
        
        while current_time <= duration_hours * 60:
            # Calculate effect curve (absorption -> peak -> decay)
            time_factor = self._calculate_time_factor(
                current_time,
                peak_result.time_to_onset_min,
                peak_result.time_to_peak_min,
                peak_result.duration_hours * 60
            )
            
            # Scale all effects by time factor
            point = {
                'time_min': current_time,
                'time_hours': current_time / 60,
                'lcc': current_consciousness.lcc + peak_result.lcc_change * time_factor,
                'gile_l': current_consciousness.gile_l + peak_result.gile_l_change * time_factor,
                'gile_i': current_consciousness.gile_i + peak_result.gile_i_change * time_factor,
                'gile_g': current_consciousness.gile_g + peak_result.gile_g_change * time_factor,
                'gile_e': current_consciousness.gile_e + peak_result.gile_e_change * time_factor,
                'coherence': current_consciousness.coherence + peak_result.coherence_change * time_factor,
                'heart_rate': current_biometrics.heart_rate + peak_result.heart_rate_change * time_factor,
                'rmssd': current_biometrics.rmssd + peak_result.rmssd_change * time_factor,
                'anandamide_multiplier': 1.0 + (peak_result.anandamide_multiplier - 1.0) * time_factor,
                'effect_intensity': time_factor
            }
            
            time_series.append(point)
            current_time += interval_min
        
        return time_series
    
    def _calculate_time_factor(
        self,
        current_time: float,
        onset_time: float,
        peak_time: float,
        total_duration: float
    ) -> float:
        """Calculate effect intensity at a given time point"""
        
        if current_time < onset_time:
            # Absorption phase (exponential rise)
            return (current_time / onset_time) ** 2 * 0.3
        elif current_time < peak_time:
            # Rise to peak
            progress = (current_time - onset_time) / (peak_time - onset_time)
            return 0.3 + 0.7 * progress
        elif current_time < total_duration:
            # Decay phase (exponential decay)
            decay_progress = (current_time - peak_time) / (total_duration - peak_time)
            return 1.0 * np.exp(-decay_progress * 2)
        else:
            return 0.1  # Residual effect
    
    def compare_stacks(
        self,
        stack_options: List[List[str]],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState
    ) -> List[Tuple[List[str], PredictionResult]]:
        """Compare multiple supplement stacks to find the best one"""
        
        results = []
        for stack in stack_options:
            prediction = self.simulate(stack, current_consciousness, current_biometrics)
            results.append((stack, prediction))
        
        # Sort by LCC improvement
        results.sort(key=lambda x: x[1].final_lcc, reverse=True)
        return results
    
    def save_prediction(self, prediction: PredictionResult):
        """Save prediction to database for later validation"""
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
                    predicted_sensations, predicted_emotions,
                    confidence
                ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING id
            """, (
                self.user_id,
                prediction.timestamp,
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
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Could not save prediction: {e}")
    
    def validate_prediction(
        self,
        prediction_id: int,
        actual_lcc: float,
        actual_gile_composite: float,
        actual_sensations: List[str],
        actual_emotions: List[str]
    ):
        """Validate a previous prediction against actual results"""
        if not DATABASE_URL:
            return
        
        try:
            conn = psycopg2.connect(DATABASE_URL)
            cur = conn.cursor()
            
            cur.execute("""
                UPDATE ti_pharmacological_predictions
                SET actual_lcc = %s,
                    actual_gile_composite = %s,
                    actual_sensations = %s,
                    actual_emotions = %s,
                    validated_at = NOW()
                WHERE id = %s
            """, (
                actual_lcc,
                actual_gile_composite,
                json.dumps(actual_sensations),
                json.dumps(actual_emotions),
                prediction_id
            ))
            
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            print(f"Could not validate prediction: {e}")


def create_database_tables():
    """Create necessary database tables for pharmacological simulator"""
    if not DATABASE_URL:
        print("No DATABASE_URL found")
        return
    
    try:
        conn = psycopg2.connect(DATABASE_URL)
        cur = conn.cursor()
        
        # Genetic profiles table
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
        
        # Pharmacological predictions table
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
        print("Database tables created successfully!")
    except Exception as e:
        print(f"Error creating tables: {e}")


def demo_simulation():
    """Demonstrate the pharmacological simulator"""
    
    print("=" * 80)
    print("🧬 TI PHARMACOLOGICAL SIMULATOR - DEMO")
    print("=" * 80)
    
    # Initialize simulator for Brandon
    simulator = TIPharmacologicalSimulator(user_id='brandon')
    
    print(f"\n📊 Genetic Profile Loaded:")
    print(f"   FAAH Activity: {simulator.genetic_profile.faah_activity} (lower = better for anandamide)")
    print(f"   COMT Activity: {simulator.genetic_profile.comt_activity}")
    print(f"   Schizotypy SNPs: {simulator.genetic_profile.schizotypy_snp_count}")
    print(f"   Consciousness Amplification Factor: {simulator.genetic_profile.consciousness_amplification_factor():.2f}")
    
    # Current state (Brandon's elevated baseline)
    current_consciousness = ConsciousnessState(
        lcc=0.99,
        gile_g=0.95,
        gile_i=0.90,
        gile_l=0.99,
        gile_e=0.95,
        coherence=0.99,
        true_tralseness=0.98
    )
    
    current_biometrics = BiometricState(
        heart_rate=60,
        rmssd=80,
        alpha_power=0.85,
        gamma_power=0.40
    )
    
    print(f"\n📊 Current Consciousness State:")
    print(f"   LCC: {current_consciousness.lcc:.1%}")
    print(f"   GILE Composite: {current_consciousness.gile_composite:.3f}")
    print(f"   Coherence: {current_consciousness.coherence:.1%}")
    print(f"   True-Tralseness: {current_consciousness.true_tralseness:.1%}")
    
    print(f"\n📊 Current Biometrics:")
    print(f"   Heart Rate: {current_biometrics.heart_rate} bpm")
    print(f"   RMSSD: {current_biometrics.rmssd} ms")
    
    # Simulate Brandon's current stack
    supplements = ['curcubrain', 'macamides_5pct', 'magnesium_l_threonate', 'omega3_dha', 'vitamin_b6_p5p']
    
    print(f"\n💊 Simulating Stack: {supplements}")
    
    result = simulator.simulate(supplements, current_consciousness, current_biometrics)
    
    print(f"\n" + "=" * 80)
    print("🔮 PREDICTION RESULTS")
    print("=" * 80)
    
    print(f"\n📈 Anandamide Multiplier: {result.anandamide_multiplier:.2f}x baseline")
    print(f"   (You're predicted to have {result.anandamide_multiplier:.1f}x normal anandamide levels)")
    
    print(f"\n📊 Consciousness Changes:")
    print(f"   LCC: {current_consciousness.lcc:.1%} → {result.final_lcc:.1%} (+{result.lcc_change:.3f})")
    print(f"   Love (L): {current_consciousness.gile_l:.3f} → {current_consciousness.gile_l + result.gile_l_change:.3f} (+{result.gile_l_change:.3f})")
    print(f"   Intuition (I): {current_consciousness.gile_i:.3f} → {current_consciousness.gile_i + result.gile_i_change:.3f} (+{result.gile_i_change:.3f})")
    print(f"   Goodness (G): {current_consciousness.gile_g:.3f} → {current_consciousness.gile_g + result.gile_g_change:.3f} (+{result.gile_g_change:.3f})")
    print(f"   Environment (E): {current_consciousness.gile_e:.3f} → {current_consciousness.gile_e + result.gile_e_change:.3f} (+{result.gile_e_change:.3f})")
    print(f"   Coherence: {current_consciousness.coherence:.1%} → {result.final_coherence:.1%} (+{result.coherence_change:.3f})")
    print(f"   True-Tralseness: {current_consciousness.true_tralseness:.1%} → {result.final_true_tralseness:.1%}")
    
    print(f"\n📊 Biometric Predictions:")
    print(f"   Heart Rate: {current_biometrics.heart_rate} bpm → {current_biometrics.heart_rate + result.heart_rate_change:.0f} bpm")
    print(f"   RMSSD: {current_biometrics.rmssd} ms → {current_biometrics.rmssd + result.rmssd_change:.0f} ms")
    
    print(f"\n⏰ Timeline:")
    print(f"   Onset: ~{result.time_to_onset_min:.0f} minutes")
    print(f"   Peak: ~{result.time_to_peak_min:.0f} minutes")
    print(f"   Duration: ~{result.duration_hours:.1f} hours")
    
    print(f"\n✨ Predicted Physical Sensations:")
    for sensation in result.predicted_sensations:
        print(f"   • {sensation}")
    
    print(f"\n💜 Predicted Emotional States:")
    for emotion in result.predicted_emotions:
        print(f"   • {emotion}")
    
    print(f"\n🔮 Synchronicity Likelihood: {result.synchronicity_likelihood:.1%}")
    print(f"📊 Prediction Confidence: {result.confidence:.1%}")
    
    print("\n" + "=" * 80)
    print("✅ SIMULATION COMPLETE")
    print("=" * 80)


if __name__ == "__main__":
    # Create database tables if needed
    create_database_tables()
    
    # Run demo
    demo_simulation()
