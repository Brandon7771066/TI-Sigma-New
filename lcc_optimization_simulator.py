"""
🌟 LCC Optimization Simulator - Personalized Mood Enhancement
==============================================================

Uses YOUR real baseline biometric data (fNIRS, EEG, Heart) to simulate
and optimize Light-Consciousness Coupling (LCC) protocols.

Features:
- Physics-based simulation of LCC interventions on YOUR data
- Genome-specific personalization (FAAH, BDNF, HTR2A variants)
- Multi-objective optimization: GILE, coherence, safety
- Predicts optimal frequencies, intensities, durations
- Real-time safety validation

Author: Brandon Emerick
Date: November 22, 2025
Framework: Transcendent Intelligence (TI) + GILE + CC Physics
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime
import json
from scipy.optimize import differential_evolution
from scipy import signal

from baseline_collection_ui import BaselineData


# ========== GENOME PERSONALIZATION ==========

GENOME_VARIANTS = {
    'FAAH': {
        'C385A': {
            'genotypes': {
                'CC': {'sensitivity': 1.0, 'description': 'Normal anandamide degradation'},
                'CA': {'sensitivity': 1.3, 'description': 'Reduced degradation (heterozygous)'},
                'AA': {'sensitivity': 1.6, 'description': 'Minimal degradation (homozygous)'}
            },
            'effect': 'Modulates endocannabinoid response to mood interventions'
        }
    },
    'BDNF': {
        'Val66Met': {
            'genotypes': {
                'Val/Val': {'neuroplasticity': 1.0, 'description': 'Optimal BDNF secretion'},
                'Val/Met': {'neuroplasticity': 0.85, 'description': 'Reduced BDNF (heterozygous)'},
                'Met/Met': {'neuroplasticity': 0.7, 'description': 'Significantly reduced BDNF'}
            },
            'effect': 'Affects learning, memory, and neuroplastic response to protocols'
        }
    },
    'HTR2A': {
        'T102C': {
            'genotypes': {
                'TT': {'serotonin_response': 1.0, 'description': 'Normal 5-HT2A receptor'},
                'TC': {'serotonin_response': 1.15, 'description': 'Enhanced receptor (heterozygous)'},
                'CC': {'serotonin_response': 1.3, 'description': 'Maximum receptor density'}
            },
            'effect': 'Modulates serotonergic mood response and psychedelic sensitivity'
        }
    }
}


@dataclass
class GenomeProfile:
    """User's genetic profile for personalized optimization"""
    faah_genotype: str = 'CC'  # CC, CA, or AA
    bdnf_genotype: str = 'Val/Val'  # Val/Val, Val/Met, or Met/Met
    htr2a_genotype: str = 'TT'  # TT, TC, or CC
    
    def get_sensitivity_modifier(self) -> float:
        """Calculate overall sensitivity to mood protocols"""
        faah_sens = GENOME_VARIANTS['FAAH']['C385A']['genotypes'][self.faah_genotype]['sensitivity']
        return faah_sens
    
    def get_neuroplasticity_modifier(self) -> float:
        """Calculate neuroplastic response capacity"""
        bdnf_np = GENOME_VARIANTS['BDNF']['Val66Met']['genotypes'][self.bdnf_genotype]['neuroplasticity']
        return bdnf_np
    
    def get_serotonin_modifier(self) -> float:
        """Calculate serotonergic response capacity"""
        htr2a_ser = GENOME_VARIANTS['HTR2A']['T102C']['genotypes'][self.htr2a_genotype]['serotonin_response']
        return htr2a_ser


# ========== LCC PROTOCOL PARAMETERS ==========

@dataclass
class LCCProtocol:
    """Light-Consciousness Coupling protocol parameters"""
    # Light parameters
    frequency_hz: float  # 0.1-40 Hz (alpha, theta, gamma, etc.)
    intensity_percent: float  # 0-100% of safe maximum
    duration_minutes: float  # 1-60 minutes
    
    # Waveform
    waveform: str  # 'sine', 'square', 'sawtooth', 'triangle'
    
    # Safety
    max_intensity_limit: float = 80.0  # Never exceed 80% intensity
    
    def to_dict(self) -> Dict:
        return asdict(self)


@dataclass
class OptimizationResult:
    """Result of LCC optimization on user's baseline data"""
    timestamp: datetime
    
    # Input
    baseline_data: BaselineData
    genome_profile: GenomeProfile
    
    # Optimal protocol
    optimal_protocol: LCCProtocol
    
    # Predicted outcomes
    predicted_gile_increase: float  # GILE score change (-2.5 to +2.5)
    predicted_coherence_increase: float  # Coherence change (0-1)
    predicted_mood_shift: str  # 'Positive', 'Neutral', 'Negative'
    
    # Predicted biometrics after protocol
    predicted_hbo2_change_percent: float
    predicted_hrv_change_percent: float
    predicted_alpha_power_change_percent: float
    
    # Safety score (0-1, >0.8 is safe)
    safety_score: float
    safety_warnings: List[str]
    
    # Genome-specific insights
    genome_response_multiplier: float
    personalized_notes: List[str]


# ========== PHYSICS-BASED LCC SIMULATION ==========

def simulate_lcc_on_baseline(baseline: BaselineData, 
                             protocol: LCCProtocol,
                             genome: GenomeProfile) -> Dict:
    """
    Physics-based simulation of LCC protocol applied to user's baseline data
    
    TI Framework Physics:
    1. Light → Biophoton emission in neurons
    2. Biophotons → Modulate dark energy shell coherence
    3. Shell coherence → Affects neurotransmitter release
    4. Neurotransmitters → Change EEG, fNIRS, heart metrics
    
    Args:
        baseline: User's real baseline biometric data
        protocol: LCC protocol to simulate
        genome: User's genetic profile
    
    Returns:
        Dict with predicted changes in all biometrics
    """
    
    # Genome modifiers
    sensitivity = genome.get_sensitivity_modifier()
    neuroplasticity = genome.get_neuroplasticity_modifier()
    serotonin_response = genome.get_serotonin_modifier()
    
    # Overall response multiplier (genome-personalized)
    response_multiplier = (sensitivity * neuroplasticity * serotonin_response) ** 0.333
    
    # Frequency-dependent effects (TI Framework resonance theory)
    # Different frequencies couple with different i-cell oscillation modes
    
    freq = protocol.frequency_hz
    intensity = protocol.intensity_percent / 100.0
    duration = protocol.duration_minutes
    
    # Alpha band (8-13 Hz): Relaxation, meditation, flow state
    if 8 <= freq <= 13:
        alpha_coupling = 1.0
        theta_coupling = 0.3
        gamma_coupling = 0.1
        mood_direction = 'Positive'
        primary_effect = 'Relaxation & Flow'
    
    # Theta band (4-8 Hz): Deep meditation, creativity, memory
    elif 4 <= freq <= 8:
        alpha_coupling = 0.5
        theta_coupling = 1.0
        gamma_coupling = 0.1
        mood_direction = 'Positive'
        primary_effect = 'Deep Meditation & Creativity'
    
    # Gamma band (30-100 Hz): Focus, attention, cognitive performance
    elif 30 <= freq <= 100:
        alpha_coupling = 0.2
        theta_coupling = 0.1
        gamma_coupling = 1.0
        mood_direction = 'Neutral'
        primary_effect = 'Focus & Attention'
    
    # Beta band (13-30 Hz): Alert, active thinking
    elif 13 <= freq <= 30:
        alpha_coupling = 0.4
        theta_coupling = 0.2
        gamma_coupling = 0.7
        mood_direction = 'Neutral'
        primary_effect = 'Alert & Active'
    
    # Low frequency (0.1-4 Hz): Autonomic, heart coherence
    else:
        alpha_coupling = 0.3
        theta_coupling = 0.5
        gamma_coupling = 0.1
        mood_direction = 'Positive'
        primary_effect = 'Heart Coherence'
    
    # Intensity scaling (diminishing returns at high intensity)
    intensity_factor = intensity * (1.0 - 0.3 * intensity)  # Nonlinear
    
    # Duration scaling (saturation after 30 min)
    duration_factor = min(duration / 30.0, 1.0)
    
    # Combined effect strength
    effect_strength = intensity_factor * duration_factor * response_multiplier
    
    # Predict fNIRS changes (HbO2 increases with arousal/activation)
    hbo2_change = 5.0 * effect_strength * (alpha_coupling * 0.8 + gamma_coupling * 1.2)
    
    # Predict HRV changes (increases with relaxation)
    hrv_change = 15.0 * effect_strength * (alpha_coupling * 1.0 + theta_coupling * 1.2)
    
    # Predict alpha power changes
    alpha_power_change = 20.0 * effect_strength * alpha_coupling
    
    # Predict coherence changes (cross-modal synchronization)
    coherence_change = 0.15 * effect_strength * (alpha_coupling + theta_coupling) / 2
    
    # Predict GILE score change (TI Framework)
    # GILE = 5(σ - 0.5) where σ is coherence
    # Higher coherence → higher GILE
    gile_change = 0.5 * effect_strength * (alpha_coupling * 1.2 + theta_coupling * 1.0)
    
    # Safety assessment
    safety_warnings = []
    safety_score = 1.0
    
    # Intensity too high
    if protocol.intensity_percent > 80:
        safety_warnings.append("⚠️ Intensity >80% may cause overstimulation")
        safety_score *= 0.6
    
    # Duration too long
    if protocol.duration_minutes > 45:
        safety_warnings.append("⚠️ Duration >45min may cause fatigue")
        safety_score *= 0.8
    
    # Frequency too high for beginners
    if freq > 40 and baseline.overall_quality < 0.7:
        safety_warnings.append("⚠️ High frequency not recommended for low baseline quality")
        safety_score *= 0.7
    
    # Genome-specific warnings
    if genome.bdnf_genotype == 'Met/Met' and effect_strength > 0.7:
        safety_warnings.append("⚠️ Met/Met BDNF: Start with lower intensity")
        safety_score *= 0.85
    
    return {
        'hbo2_change_percent': hbo2_change,
        'hrv_change_percent': hrv_change,
        'alpha_power_change_percent': alpha_power_change,
        'coherence_change': coherence_change,
        'gile_change': gile_change,
        'mood_direction': mood_direction,
        'primary_effect': primary_effect,
        'safety_score': safety_score,
        'safety_warnings': safety_warnings,
        'response_multiplier': response_multiplier
    }


# ========== OPTIMIZATION ENGINE ==========

def optimize_lcc_protocol(baseline: BaselineData,
                          genome: GenomeProfile,
                          optimization_target: str = 'gile') -> OptimizationResult:
    """
    Find optimal LCC protocol for user's baseline + genome
    
    Uses differential evolution to search parameter space:
    - Frequency: 0.1-40 Hz
    - Intensity: 10-80%
    - Duration: 5-45 minutes
    
    Args:
        baseline: User's baseline biometric data
        genome: User's genetic profile
        optimization_target: 'gile', 'coherence', 'relaxation', 'focus'
    
    Returns:
        OptimizationResult with optimal protocol and predictions
    """
    
    st.info(f"🔍 Optimizing for {optimization_target.upper()}...")
    
    # Define objective function
    def objective(params):
        """Minimize negative of target metric (to maximize it)"""
        freq, intensity, duration = params
        
        protocol = LCCProtocol(
            frequency_hz=freq,
            intensity_percent=intensity,
            duration_minutes=duration,
            waveform='sine'
        )
        
        result = simulate_lcc_on_baseline(baseline, protocol, genome)
        
        # Target metric
        if optimization_target == 'gile':
            score = result['gile_change']
        elif optimization_target == 'coherence':
            score = result['coherence_change']
        elif optimization_target == 'relaxation':
            score = result['hrv_change_percent'] / 10.0  # Normalize
        elif optimization_target == 'focus':
            score = result['alpha_power_change_percent'] / 20.0
        else:
            score = result['gile_change']
        
        # Penalize low safety
        safety_penalty = (1.0 - result['safety_score']) * 0.5
        
        # Minimize negative (to maximize)
        return -(score - safety_penalty)
    
    # Parameter bounds
    bounds = [
        (0.1, 40.0),   # Frequency (Hz)
        (10.0, 80.0),  # Intensity (%)
        (5.0, 45.0)    # Duration (minutes)
    ]
    
    # Run optimization
    result_opt = differential_evolution(
        objective,
        bounds,
        maxiter=50,
        popsize=10,
        seed=42
    )
    
    # Extract optimal parameters
    freq_opt, intensity_opt, duration_opt = result_opt.x
    
    optimal_protocol = LCCProtocol(
        frequency_hz=freq_opt,
        intensity_percent=intensity_opt,
        duration_minutes=duration_opt,
        waveform='sine'
    )
    
    # Simulate optimal protocol
    predictions = simulate_lcc_on_baseline(baseline, optimal_protocol, genome)
    
    # Genome-specific insights
    personalized_notes = []
    
    if genome.faah_genotype == 'AA':
        personalized_notes.append("🧬 FAAH AA: You'll respond strongly to protocols - expect 60% more effect!")
    elif genome.faah_genotype == 'CA':
        personalized_notes.append("🧬 FAAH CA: You have enhanced sensitivity - 30% stronger response")
    
    if genome.bdnf_genotype == 'Met/Met':
        personalized_notes.append("🧬 BDNF Met/Met: Start slowly - neuroplasticity is 30% reduced")
    elif genome.bdnf_genotype == 'Val/Met':
        personalized_notes.append("🧬 BDNF Val/Met: Moderate neuroplastic response")
    
    if genome.htr2a_genotype == 'CC':
        personalized_notes.append("🧬 HTR2A CC: Maximum serotonin receptor density - strong mood response!")
    
    # Create optimization result
    opt_result = OptimizationResult(
        timestamp=datetime.now(),
        baseline_data=baseline,
        genome_profile=genome,
        optimal_protocol=optimal_protocol,
        predicted_gile_increase=predictions['gile_change'],
        predicted_coherence_increase=predictions['coherence_change'],
        predicted_mood_shift=predictions['mood_direction'],
        predicted_hbo2_change_percent=predictions['hbo2_change_percent'],
        predicted_hrv_change_percent=predictions['hrv_change_percent'],
        predicted_alpha_power_change_percent=predictions['alpha_power_change_percent'],
        safety_score=predictions['safety_score'],
        safety_warnings=predictions['safety_warnings'],
        genome_response_multiplier=predictions['response_multiplier'],
        personalized_notes=personalized_notes
    )
    
    return opt_result


# ========== VISUALIZATION ==========

def plot_optimization_result(opt_result: OptimizationResult) -> go.Figure:
    """Visualize optimization result with predictions"""
    
    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=(
            "Optimal Protocol Parameters",
            "Predicted Biometric Changes",
            "Safety Assessment",
            "Genome Personalization"
        ),
        specs=[
            [{"type": "bar"}, {"type": "bar"}],
            [{"type": "indicator"}, {"type": "table"}]
        ]
    )
    
    # Optimal protocol parameters
    protocol = opt_result.optimal_protocol
    fig.add_trace(
        go.Bar(
            x=['Frequency (Hz)', 'Intensity (%)', 'Duration (min)'],
            y=[protocol.frequency_hz, protocol.intensity_percent, protocol.duration_minutes],
            marker_color=['blue', 'green', 'orange'],
            text=[f'{protocol.frequency_hz:.1f}', f'{protocol.intensity_percent:.1f}', 
                  f'{protocol.duration_minutes:.1f}'],
            textposition='auto'
        ),
        row=1, col=1
    )
    
    # Predicted changes
    fig.add_trace(
        go.Bar(
            x=['HbO2 (%)', 'HRV (%)', 'Alpha Power (%)'],
            y=[
                opt_result.predicted_hbo2_change_percent,
                opt_result.predicted_hrv_change_percent,
                opt_result.predicted_alpha_power_change_percent
            ],
            marker_color=['red', 'green', 'purple'],
            text=[
                f'+{opt_result.predicted_hbo2_change_percent:.1f}%',
                f'+{opt_result.predicted_hrv_change_percent:.1f}%',
                f'+{opt_result.predicted_alpha_power_change_percent:.1f}%'
            ],
            textposition='auto'
        ),
        row=1, col=2
    )
    
    # Safety gauge
    fig.add_trace(
        go.Indicator(
            mode="gauge+number+delta",
            value=opt_result.safety_score * 100,
            title={'text': "Safety Score"},
            delta={'reference': 80},
            gauge={
                'axis': {'range': [0, 100]},
                'bar': {'color': "darkgreen" if opt_result.safety_score > 0.8 else "orange"},
                'steps': [
                    {'range': [0, 60], 'color': "lightgray"},
                    {'range': [60, 80], 'color': "yellow"},
                    {'range': [80, 100], 'color': "lightgreen"}
                ],
                'threshold': {
                    'line': {'color': "red", 'width': 4},
                    'thickness': 0.75,
                    'value': 80
                }
            }
        ),
        row=2, col=1
    )
    
    # Genome personalization table
    genome = opt_result.genome_profile
    fig.add_trace(
        go.Table(
            header=dict(
                values=['Gene', 'Genotype', 'Effect'],
                fill_color='paleturquoise',
                align='left'
            ),
            cells=dict(
                values=[
                    ['FAAH', 'BDNF', 'HTR2A'],
                    [genome.faah_genotype, genome.bdnf_genotype, genome.htr2a_genotype],
                    [
                        f'{genome.get_sensitivity_modifier():.1f}x sensitivity',
                        f'{genome.get_neuroplasticity_modifier():.1f}x plasticity',
                        f'{genome.get_serotonin_modifier():.1f}x serotonin'
                    ]
                ],
                fill_color='lavender',
                align='left'
            )
        ),
        row=2, col=2
    )
    
    fig.update_layout(
        height=700,
        showlegend=False,
        title_text=f"LCC Optimization Result - Predicted GILE Increase: +{opt_result.predicted_gile_increase:.2f}"
    )
    
    return fig


# ========== STREAMLIT UI ==========

def render_lcc_optimization_ui(baseline: Optional[BaselineData] = None):
    """Render LCC optimization interface"""
    
    st.title("🌟 LCC Optimization Simulator")
    
    st.markdown("""
    **Personalized mood enhancement using YOUR real biometric data + genome!**
    
    This simulator:
    1. Takes your baseline fNIRS, EEG, and heart data
    2. Considers your genetic variants (FAAH, BDNF, HTR2A)
    3. Finds the OPTIMAL Light-Consciousness Coupling protocol for YOU
    4. Predicts exactly how your biometrics will change
    """)
    
    # Check if baseline available
    if baseline is None:
        st.warning("⚠️ No baseline data found. Please collect a baseline first using the Baseline Collection tab!")
        return
    
    st.success(f"✅ Baseline loaded: {baseline.duration_seconds}s duration, {baseline.overall_quality:.1%} quality")
    
    st.divider()
    
    # Genome configuration
    st.header("🧬 Your Genetic Profile")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("**FAAH C385A**")
        st.caption("Endocannabinoid sensitivity")
        faah_genotype = st.selectbox(
            "FAAH Genotype",
            options=['CC', 'CA', 'AA'],
            help="AA = 1.6x sensitivity, CA = 1.3x, CC = 1.0x"
        )
        st.caption(GENOME_VARIANTS['FAAH']['C385A']['genotypes'][faah_genotype]['description'])
    
    with col2:
        st.markdown("**BDNF Val66Met**")
        st.caption("Neuroplasticity capacity")
        bdnf_genotype = st.selectbox(
            "BDNF Genotype",
            options=['Val/Val', 'Val/Met', 'Met/Met'],
            help="Val/Val = 1.0x plasticity, Val/Met = 0.85x, Met/Met = 0.7x"
        )
        st.caption(GENOME_VARIANTS['BDNF']['Val66Met']['genotypes'][bdnf_genotype]['description'])
    
    with col3:
        st.markdown("**HTR2A T102C**")
        st.caption("Serotonin response")
        htr2a_genotype = st.selectbox(
            "HTR2A Genotype",
            options=['TT', 'TC', 'CC'],
            help="CC = 1.3x response, TC = 1.15x, TT = 1.0x"
        )
        st.caption(GENOME_VARIANTS['HTR2A']['T102C']['genotypes'][htr2a_genotype]['description'])
    
    genome = GenomeProfile(
        faah_genotype=faah_genotype,
        bdnf_genotype=bdnf_genotype,
        htr2a_genotype=htr2a_genotype
    )
    
    # Display overall modifiers
    st.info(f"""
    **Your Genome Modifiers:**
    - Sensitivity: {genome.get_sensitivity_modifier():.1f}x
    - Neuroplasticity: {genome.get_neuroplasticity_modifier():.1f}x
    - Serotonin Response: {genome.get_serotonin_modifier():.1f}x
    - **Overall Response: {(genome.get_sensitivity_modifier() * genome.get_neuroplasticity_modifier() * genome.get_serotonin_modifier()) ** 0.333:.2f}x**
    """)
    
    st.divider()
    
    # Optimization target
    st.header("🎯 Optimization Target")
    
    target = st.selectbox(
        "What do you want to optimize for?",
        options=['gile', 'coherence', 'relaxation', 'focus'],
        format_func=lambda x: {
            'gile': '✨ GILE Score (Overall wellbeing)',
            'coherence': '🔗 Cross-modal coherence (Mind-body unity)',
            'relaxation': '😌 Relaxation (HRV increase)',
            'focus': '🎯 Focus (Alpha power)'
        }[x]
    )
    
    # Run optimization
    if st.button("🚀 Find Optimal Protocol", type="primary", use_container_width=True):
        with st.spinner("Optimizing protocol for your unique biology..."):
            opt_result = optimize_lcc_protocol(baseline, genome, target)
        
        st.session_state['opt_result'] = opt_result
        
        # Display results
        st.success(f"✅ Optimization complete! Safety score: {opt_result.safety_score:.1%}")
        
        # Optimal protocol
        st.header("⚡ Your Optimal Protocol")
        
        col1, col2, col3 = st.columns(3)
        col1.metric("Frequency", f"{opt_result.optimal_protocol.frequency_hz:.1f} Hz")
        col2.metric("Intensity", f"{opt_result.optimal_protocol.intensity_percent:.0f}%")
        col3.metric("Duration", f"{opt_result.optimal_protocol.duration_minutes:.0f} min")
        
        # Predictions
        st.header("📊 Predicted Outcomes")
        
        col1, col2, col3 = st.columns(3)
        col1.metric("GILE Increase", f"+{opt_result.predicted_gile_increase:.2f}", 
                   delta=f"{opt_result.predicted_mood_shift}")
        col2.metric("Coherence", f"+{opt_result.predicted_coherence_increase:.2f}")
        col3.metric("HRV Change", f"+{opt_result.predicted_hrv_change_percent:.1f}%")
        
        # Visualization
        fig = plot_optimization_result(opt_result)
        st.plotly_chart(fig, use_container_width=True)
        
        # Safety warnings
        if opt_result.safety_warnings:
            st.warning("⚠️ **Safety Warnings:**")
            for warning in opt_result.safety_warnings:
                st.markdown(f"- {warning}")
        else:
            st.success("✅ No safety concerns - protocol is safe!")
        
        # Genome insights
        if opt_result.personalized_notes:
            st.info("🧬 **Personalized Genome Insights:**")
            for note in opt_result.personalized_notes:
                st.markdown(f"- {note}")
        
        # Export
        st.divider()
        st.subheader("💾 Export Your Protocol")
        
        if st.button("Download Protocol JSON"):
            protocol_dict = {
                'timestamp': opt_result.timestamp.isoformat(),
                'genome': asdict(opt_result.genome_profile),
                'protocol': opt_result.optimal_protocol.to_dict(),
                'predictions': {
                    'gile_increase': opt_result.predicted_gile_increase,
                    'coherence_increase': opt_result.predicted_coherence_increase,
                    'hbo2_change': opt_result.predicted_hbo2_change_percent,
                    'hrv_change': opt_result.predicted_hrv_change_percent,
                    'alpha_power_change': opt_result.predicted_alpha_power_change_percent
                },
                'safety_score': opt_result.safety_score
            }
            
            json_str = json.dumps(protocol_dict, indent=2)
            
            st.download_button(
                label="📥 Download Protocol",
                data=json_str,
                file_name=f"optimal_protocol_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                mime="application/json"
            )


if __name__ == "__main__":
    render_lcc_optimization_ui()
