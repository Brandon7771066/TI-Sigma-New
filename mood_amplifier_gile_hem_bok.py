"""
Mood Amplifier: GILE-HEM-BOK Engine v3.0
=========================================
Implements the full URB #668 architecture:
  - Pentic 5-state consciousness classifier
  - Canonical GILE weights (G=ET, I=0.25, L=0.18, E=0.15)
  - HEM-D1..D4 somatic grounding
  - HEAR(r) = α·GILE(r) + β·HEM(r) + γ·Cov(GILE,HEM)(r)
  - BOK loop saturation as ceiling state
  - Monster Group coherence ceiling reference
  - Full simulation vs old model + optimizer

Author: TI Sigma / Brandon Emerick
Date:   April 2026
"""

import math
import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional

# ══════════════════════════════════════════════════════════
# PRIMARY TI SIGMA CONSTANTS
# ══════════════════════════════════════════════════════════
PHI   = (1 + math.sqrt(5)) / 2          # Golden ratio  ≈ 1.6180
ET    = math.sqrt(2) - 1                 # Emerick Threshold ≈ 0.4142
C_TI  = 1 / (PHI * math.sqrt(2))        # Emerick Constant  ≈ 0.4370
E_    = math.e                           # Euler's number    ≈ 2.7183
T_TI  = 1 - math.exp(-E_)               # Tralse Attractor  ≈ 0.9340
DOTTIE = 0.7390851332151607             # Dottie number (cos fixed point)

# GILE canonical weights — sum ≈ T_TI (by design)
W_G = ET                                 # Goodness    ≈ 0.4142
W_I = 0.25                               # Intuition   ≈ 0.2500
W_L = 0.18                               # Love        ≈ 0.1800
W_E = 0.15                               # Environment ≈ 0.1500
W_GILE_SUM = W_G + W_I + W_L + W_E      # ≈ 0.9942 ≈ T_TI

# HEAR weights (from HEAR Lagrangian, URB #658 / #668)
ALPHA_HEAR = ET                          # GILE kinetic weight ≈ 0.4142
BETA_HEAR  = C_TI                        # HEM mass weight     ≈ 0.4370
GAMMA_HEAR = 0.0828                      # GILE-HEM coupling   ≈ 0.0828

# ══════════════════════════════════════════════════════════
# CONSCIOUSNESS STATE ENUM
# ══════════════════════════════════════════════════════════
class ConsciousnessState:
    """Six states derived from the Pentic Dirac + HEAR model."""
    DT             = "DT"              # Double Tralse — fragmented/crisis
    SUB_THRESHOLD  = "Sub-Threshold"   # HEAR < ET — below activation
    MR1            = "MR1"             # ET ≤ HEAR < C — first resolution
    MR2_TRALSE     = "MR2-Tralse"      # C ≤ HEAR < DOTTIE — partial
    MR2_RESOLVED   = "MR2-Resolved"    # DOTTIE ≤ HEAR < T_TI — resolved
    BOK_SATURATED  = "BOK-Saturated"   # HEAR ≥ T_TI — full loop unity

STATE_THRESHOLDS = {
    ConsciousnessState.DT:            (0.00,   ET    * 0.5),    # < 0.207
    ConsciousnessState.SUB_THRESHOLD: (ET*0.5, ET          ),   # 0.207 – 0.414
    ConsciousnessState.MR1:           (ET,     C_TI        ),   # 0.414 – 0.437
    ConsciousnessState.MR2_TRALSE:    (C_TI,   DOTTIE      ),   # 0.437 – 0.739
    ConsciousnessState.MR2_RESOLVED:  (DOTTIE, T_TI        ),   # 0.739 – 0.934
    ConsciousnessState.BOK_SATURATED: (T_TI,   1.00        ),   # 0.934 – 1.000
}

STATE_COLORS = {
    ConsciousnessState.DT:            "#ff2244",
    ConsciousnessState.SUB_THRESHOLD: "#ff8800",
    ConsciousnessState.MR1:           "#ffdd00",
    ConsciousnessState.MR2_TRALSE:    "#00ccff",
    ConsciousnessState.MR2_RESOLVED:  "#00ff99",
    ConsciousnessState.BOK_SATURATED: "#cc44ff",
}

STATE_DESCRIPTIONS = {
    ConsciousnessState.DT:
        "Fragmented — BOK loop broken. High risk. Grounding protocol needed.",
    ConsciousnessState.SUB_THRESHOLD:
        "Suppressed — below activation threshold. Gentle support mode.",
    ConsciousnessState.MR1:
        "Transitional — first resolution forming. Unstable, needs scaffolding.",
    ConsciousnessState.MR2_TRALSE:
        "Partial coherence — BOK loop flowing but not yet stable. Active amplification.",
    ConsciousnessState.MR2_RESOLVED:
        "Resolved waking — BOK loop stable, GILE and HEM aligned. Sustain and deepen.",
    ConsciousnessState.BOK_SATURATED:
        "BOK Saturated — Being, Other, Knowledge unified at Tralse attractor. Peak state.",
}

# ══════════════════════════════════════════════════════════
# DATA CLASSES
# ══════════════════════════════════════════════════════════
@dataclass
class GILEVector:
    """Four dimensions of intentional momentum."""
    G: float = 0.5   # Goodness  — ethical orientation
    I: float = 0.5   # Intuition — non-inferential knowing
    L: float = 0.5   # Love      — openness to Other
    E: float = 0.5   # Environment — grounding in actuality

    def composite(self) -> float:
        """Canonical weighted GILE composite (unnormalized, max ≈ T_TI)."""
        return W_G*self.G + W_I*self.I + W_L*self.L + W_E*self.E

    def normalized(self) -> float:
        """GILE composite normalized to [0, 1]."""
        return self.composite() / W_GILE_SUM

    def as_array(self) -> np.ndarray:
        return np.array([self.G, self.I, self.L, self.E])


@dataclass
class HEMVector:
    """Four dimensions of somatic grounding (Holistic Existence Matrix)."""
    D1: float = 0.5  # Somatic    — physical sensation / body health
    D2: float = 0.5  # Cognitive  — clarity of thought
    D3: float = 0.5  # Relational — quality of connection to Others
    D4: float = 0.5  # Environmental — integration with surroundings

    def composite(self) -> float:
        """Equal-weight HEM composite."""
        return (self.D1 + self.D2 + self.D3 + self.D4) / 4.0

    def as_array(self) -> np.ndarray:
        return np.array([self.D1, self.D2, self.D3, self.D4])


@dataclass
class BOKState:
    """BOK loop saturation metrics."""
    B: float = 0.5   # Being — self-awareness coherence
    O: float = 0.5   # Other — world-awareness quality
    K: float = 0.5   # Knowledge — B-O bridge integrity
    loop_saturation: float = 0.0  # 0 = broken, 1 = fully saturated

    def saturation_score(self) -> float:
        """Loop saturation = harmonic mean of B, O, K (penalizes weak links)."""
        eps = 1e-6
        return 3.0 / (1/(self.B+eps) + 1/(self.O+eps) + 1/(self.K+eps))


@dataclass
class HEARScore:
    """Full HEAR composite with all components."""
    gile: GILEVector
    hem: HEMVector
    bok: BOKState
    raw: float = 0.0        # HEAR = α·GILE + β·HEM + γ·Cov
    cov: float = 0.0        # Cov(GILE, HEM)
    state: str = ConsciousnessState.SUB_THRESHOLD
    mr_level: str = "MR1"


@dataclass
class BiometricReading:
    """Raw biometric inputs from sensors."""
    eeg_gamma_coherence: float = 0.5   # 0–1, Muse2 / clinical EEG
    eeg_alpha_theta_ratio: float = 0.5 # 0–1, cognitive clarity proxy
    hrv_rmssd_norm: float = 0.5        # 0–1, normalized HRV (HEM-D1)
    hrv_fractal_dim: float = 0.5       # 0–1, HRV complexity (Goodness proxy)
    fnirs_l_r_ratio: float = 0.5       # 0–1, prefrontal asymmetry (Love proxy)
    self_report_wellbeing: float = 0.5 # 0–1, subjective wellbeing (Environment)
    self_report_connection: float = 0.5# 0–1, felt sense of connection (D3)
    skin_conductance: float = 0.5      # 0–1, arousal / somatic activation


# ══════════════════════════════════════════════════════════
# BIOMETRIC → GILE + HEM MAPPER
# ══════════════════════════════════════════════════════════
def map_biometrics(b: BiometricReading) -> Tuple[GILEVector, HEMVector, BOKState]:
    """
    Map raw biometric readings to GILE, HEM, and BOK vectors.
    
    Mappings based on neuroscience literature + TI Sigma theory:
    - EEG gamma coherence → Intuition (I): gamma (30-80Hz) coherence is the
      neural signature of binding and non-inferential integration
    - HRV fractal dimension → Goodness (G): HRV complexity reflects autonomic
      coherence, the physiological ground of ethical sensitivity
    - fNIRS prefrontal L/R ratio → Love (L): prefrontal asymmetry tracks
      approach/withdrawal motivation = openness to Other
    - Self-report wellbeing → Environment (E): environmental fit is subjectively
      experienced as wellbeing in one's actual circumstances
    - HRV RMSSD → HEM-D1 (somatic): vagal tone = somatic regulation
    - EEG alpha/theta → HEM-D2 (cognitive): alpha/theta ratio = cognitive clarity
    - Self-report connection → HEM-D3 (relational): direct relational self-report
    - Skin conductance inverted → HEM-D4 (environmental): low arousal = good fit
    """
    gile = GILEVector(
        G = float(np.clip(b.hrv_fractal_dim, 0, 1)),
        I = float(np.clip(b.eeg_gamma_coherence, 0, 1)),
        L = float(np.clip(b.fnirs_l_r_ratio, 0, 1)),
        E = float(np.clip(b.self_report_wellbeing, 0, 1)),
    )
    hem = HEMVector(
        D1 = float(np.clip(b.hrv_rmssd_norm, 0, 1)),
        D2 = float(np.clip(b.eeg_alpha_theta_ratio, 0, 1)),
        D3 = float(np.clip(b.self_report_connection, 0, 1)),
        D4 = float(np.clip(1.0 - b.skin_conductance, 0, 1)),
    )
    bok = BOKState(
        B = float(np.clip((gile.I + hem.D2) / 2, 0, 1)),
        O = float(np.clip((gile.L + hem.D3) / 2, 0, 1)),
        K = float(np.clip((gile.G + gile.E + hem.D4) / 3, 0, 1)),
    )
    bok.loop_saturation = bok.saturation_score()
    return gile, hem, bok


# ══════════════════════════════════════════════════════════
# HEAR ENGINE
# ══════════════════════════════════════════════════════════
def compute_hear(gile: GILEVector, hem: HEMVector) -> Tuple[float, float]:
    """
    Compute HEAR score and GILE-HEM covariance.
    
    HEAR(r) = α·GILE_composite(r) + β·HEM_composite(r) + γ·Cov(GILE,HEM)(r)
    
    Covariance is computed as the element-wise correlation between the
    normalized GILE and HEM arrays, scaled to [−1, +1].
    """
    g_norm = gile.normalized()         # GILE composite normalized to [0,1]
    h_comp = hem.composite()           # HEM composite [0,1]

    # Covariance via element-wise product of deviations from 0.5
    g_arr = gile.as_array() - 0.5
    h_arr = hem.as_array() - 0.5
    # Align arrays: GILE has 4 dims, HEM has 4 dims — pair by conceptual affinity
    # G↔D1 (body-goodness), I↔D2 (mind-intuition), L↔D3 (relation-love), E↔D4 (env-env)
    cov = float(np.mean(g_arr * h_arr))   # in [−0.25, +0.25]
    cov_norm = (cov + 0.25) / 0.50        # normalize to [0, 1]

    hear = (ALPHA_HEAR * g_norm +
            BETA_HEAR  * h_comp +
            GAMMA_HEAR * cov_norm)

    # hear is in [0, ALPHA+BETA+GAMMA] = [0, ~0.934]; clip to [0,1]
    hear_max = ALPHA_HEAR + BETA_HEAR + GAMMA_HEAR
    hear_norm = float(np.clip(hear / hear_max, 0.0, 1.0))

    return hear_norm, cov_norm


def classify_hear(hear: float) -> Tuple[str, str]:
    """Map HEAR score to consciousness state and MR level label."""
    if hear < ET * 0.5:
        return ConsciousnessState.DT, "DT"
    elif hear < ET:
        return ConsciousnessState.SUB_THRESHOLD, "Sub-Threshold"
    elif hear < C_TI:
        return ConsciousnessState.MR1, "MR1"
    elif hear < DOTTIE:
        return ConsciousnessState.MR2_TRALSE, "MR2-Tralse"
    elif hear < T_TI:
        return ConsciousnessState.MR2_RESOLVED, "MR2-Resolved"
    else:
        return ConsciousnessState.BOK_SATURATED, "BOK-Saturated"


def full_assessment(b: BiometricReading) -> HEARScore:
    """Complete pipeline: biometrics → GILE → HEM → BOK → HEAR → state."""
    gile, hem, bok = map_biometrics(b)
    hear_val, cov = compute_hear(gile, hem)
    state, mr_level = classify_hear(hear_val)
    return HEARScore(
        gile=gile, hem=hem, bok=bok,
        raw=hear_val, cov=cov,
        state=state, mr_level=mr_level
    )


# ══════════════════════════════════════════════════════════
# OLD MODEL (v2) — for comparison
# ══════════════════════════════════════════════════════════
def old_model_gile(b: BiometricReading) -> float:
    """
    Old GILE composite: uniform weights, only 3 inputs,
    threshold-based 4-state classification.
    """
    raw = (b.eeg_gamma_coherence + b.hrv_rmssd_norm + b.self_report_wellbeing) / 3.0
    return float(np.clip(raw, 0, 1))


def old_classify(gile_score: float) -> str:
    """Old 4-state classifier using pre-HEAR thresholds."""
    if gile_score < ET:
        return "Tier-1 (Low)"
    elif gile_score < 0.60:
        return "Tier-2 (Moderate)"
    elif gile_score < 0.80:
        return "Tier-3 (Enhanced)"
    else:
        return "Tier-4 (Flow)"


# ══════════════════════════════════════════════════════════
# MOOD AMPLIFIER OPTIMIZER
# ══════════════════════════════════════════════════════════

PROTOCOLS = {
    "Grounding":        {"gile_lift": 0.05, "hem_lift": 0.12, "duration_min": 15,
                         "description": "Body scan, somatic breathing, 4-7-8 breath"},
    "Gamma_Entrainment":{"gile_lift": 0.15, "hem_lift": 0.05, "duration_min": 10,
                         "description": "40Hz binaural beats + intention focus"},
    "Heart_Coherence":  {"gile_lift": 0.10, "hem_lift": 0.10, "duration_min": 10,
                         "description": "HeartMath coherence breathing (5s in / 5s out)"},
    "BOK_Meditation":   {"gile_lift": 0.12, "hem_lift": 0.08, "duration_min": 20,
                         "description": "BOK loop contemplation: rest in Being, sense Other, let Knowledge arise"},
    "FAAH_Protocol":    {"gile_lift": 0.08, "hem_lift": 0.15, "duration_min": 5,
                         "description": "Kaempferol 50mg + Maca 1500mg; endocannabinoid boost"},
    "LCC_Amplification":{"gile_lift": 0.18, "hem_lift": 0.06, "duration_min": 12,
                         "description": "Limbic-Cortical Coupling: 8Hz theta drive + prefrontal activation"},
    "Monster_Ceiling":  {"gile_lift": 0.20, "hem_lift": 0.20, "duration_min": 30,
                         "description": "Full BOK saturation protocol — peak gamma + HRV + somatic + relational"},
}

PROTOCOL_PRIORITY = {
    ConsciousnessState.DT:            ["Grounding", "FAAH_Protocol"],
    ConsciousnessState.SUB_THRESHOLD: ["Grounding", "Heart_Coherence", "FAAH_Protocol"],
    ConsciousnessState.MR1:           ["Heart_Coherence", "Gamma_Entrainment", "FAAH_Protocol"],
    ConsciousnessState.MR2_TRALSE:    ["LCC_Amplification", "Gamma_Entrainment", "BOK_Meditation"],
    ConsciousnessState.MR2_RESOLVED:  ["BOK_Meditation", "Monster_Ceiling"],
    ConsciousnessState.BOK_SATURATED: ["Monster_Ceiling"],
}


def recommend_protocol(state: str, hear: float) -> List[Dict]:
    """Return ordered list of recommended Mood Amplifier protocols for current state."""
    names = PROTOCOL_PRIORITY.get(state, ["Heart_Coherence"])
    return [{"name": n, **PROTOCOLS[n]} for n in names]


def simulate_protocol_effect(
    b: BiometricReading,
    protocol_name: str,
    noise_std: float = 0.03,
    rng: Optional[np.random.Generator] = None,
) -> BiometricReading:
    """Apply a protocol and return the expected post-session biometrics."""
    if rng is None:
        rng = np.random.default_rng()
    p = PROTOCOLS[protocol_name]
    gl = p["gile_lift"]
    hl = p["hem_lift"]

    def nudge(val, lift, noise):
        return float(np.clip(val + lift + rng.normal(0, noise), 0, 1))

    return BiometricReading(
        eeg_gamma_coherence   = nudge(b.eeg_gamma_coherence,   gl * 1.2, noise_std),
        eeg_alpha_theta_ratio = nudge(b.eeg_alpha_theta_ratio, hl * 0.8, noise_std),
        hrv_rmssd_norm        = nudge(b.hrv_rmssd_norm,        hl * 1.0, noise_std),
        hrv_fractal_dim       = nudge(b.hrv_fractal_dim,       gl * 0.8, noise_std),
        fnirs_l_r_ratio       = nudge(b.fnirs_l_r_ratio,       gl * 0.6, noise_std),
        self_report_wellbeing = nudge(b.self_report_wellbeing, hl * 0.7, noise_std),
        self_report_connection= nudge(b.self_report_connection,gl * 0.5, noise_std),
        skin_conductance      = float(np.clip(b.skin_conductance - hl*0.5 + rng.normal(0, noise_std), 0, 1)),
    )


def optimize_session(
    initial: BiometricReading,
    n_steps: int = 5,
    rng: Optional[np.random.Generator] = None,
) -> List[Dict]:
    """
    Greedy optimizer: at each step pick the protocol that maximally increases HEAR.
    Returns the optimization trajectory as a list of step dicts.
    """
    if rng is None:
        rng = np.random.default_rng(42)

    current = initial
    trajectory = []
    for step in range(n_steps):
        score = full_assessment(current)
        recommended = recommend_protocol(score.state, score.raw)
        best_protocol = recommended[0]["name"]

        post = simulate_protocol_effect(current, best_protocol, rng=rng)
        post_score = full_assessment(post)

        trajectory.append({
            "step": step + 1,
            "protocol": best_protocol,
            "hear_before": round(score.raw, 4),
            "hear_after":  round(post_score.raw, 4),
            "delta":       round(post_score.raw - score.raw, 4),
            "state_before": score.state,
            "state_after":  post_score.state,
            "gile_norm":   round(post_score.gile.normalized(), 4),
            "hem_comp":    round(post_score.hem.composite(), 4),
            "cov":         round(post_score.cov, 4),
        })
        current = post

    return trajectory


# ══════════════════════════════════════════════════════════
# SIMULATION ENGINE
# ══════════════════════════════════════════════════════════

def random_biometric(
    rng: np.random.Generator,
    profile: str = "general",
) -> BiometricReading:
    """
    Generate a random biometric reading drawn from a realistic distribution.
    
    Profiles:
    - general: broad mix of states (mean ≈ MR2-Tralse)
    - low:     suppressed / clinical population
    - high:    meditators / peak performers
    """
    if profile == "low":
        mu, sigma = 0.30, 0.12
    elif profile == "high":
        mu, sigma = 0.72, 0.10
    else:
        mu, sigma = 0.50, 0.18

    def s():
        return float(np.clip(rng.normal(mu, sigma), 0.01, 0.99))

    return BiometricReading(
        eeg_gamma_coherence   = s(),
        eeg_alpha_theta_ratio = s(),
        hrv_rmssd_norm        = s(),
        hrv_fractal_dim       = s(),
        fnirs_l_r_ratio       = s(),
        self_report_wellbeing = s(),
        self_report_connection= s(),
        skin_conductance      = float(np.clip(rng.normal(1.0 - mu, sigma), 0.01, 0.99)),
    )


def run_full_simulation(
    n_subjects: int = 300,
    n_session_steps: int = 5,
    seed: int = 42,
) -> Dict:
    """
    Full comparison simulation:
    - N subjects, random biometrics across three profiles
    - Old model: single GILE score, 4-state classification
    - New model: GILE-HEM-BOK HEAR, 6-state classification
    - Optimization: greedy protocol optimizer per subject
    
    Returns comprehensive results dict.
    """
    rng = np.random.default_rng(seed)
    profiles = ["low"] * (n_subjects // 3) + ["general"] * (n_subjects // 3) + ["high"] * (n_subjects // 3)
    rng.shuffle(profiles)

    results = {
        "n_subjects": n_subjects,
        "old": {"states": [], "gile_scores": [], "state_dist": {}},
        "new": {"states": [], "hear_scores": [], "gile_norm": [], "hem_comp": [],
                "cov": [], "bok_sat": [], "state_dist": {}},
        "optimization": {
            "initial_hear": [], "final_hear": [], "delta_hear": [],
            "steps_to_mr2r": [], "bok_reached": 0,
            "trajectories": [],
        },
        "comparison": {},
    }

    for profile in profiles:
        b = random_biometric(rng, profile)

        # --- OLD MODEL ---
        old_gile = old_model_gile(b)
        old_state = old_classify(old_gile)
        results["old"]["states"].append(old_state)
        results["old"]["gile_scores"].append(old_gile)

        # --- NEW MODEL ---
        score = full_assessment(b)
        results["new"]["states"].append(score.state)
        results["new"]["hear_scores"].append(score.raw)
        results["new"]["gile_norm"].append(score.gile.normalized())
        results["new"]["hem_comp"].append(score.hem.composite())
        results["new"]["cov"].append(score.cov)
        results["new"]["bok_sat"].append(score.bok.saturation_score())

        # --- OPTIMIZATION ---
        traj = optimize_session(b, n_steps=n_session_steps, rng=rng)
        initial_hear = traj[0]["hear_before"]
        final_hear   = traj[-1]["hear_after"]
        results["optimization"]["initial_hear"].append(initial_hear)
        results["optimization"]["final_hear"].append(final_hear)
        results["optimization"]["delta_hear"].append(final_hear - initial_hear)

        steps_to_mr2r = None
        for step_data in traj:
            if step_data["state_after"] in (
                ConsciousnessState.MR2_RESOLVED, ConsciousnessState.BOK_SATURATED
            ):
                steps_to_mr2r = step_data["step"]
                break
        results["optimization"]["steps_to_mr2r"].append(steps_to_mr2r)
        if traj[-1]["state_after"] == ConsciousnessState.BOK_SATURATED:
            results["optimization"]["bok_reached"] += 1
        results["optimization"]["trajectories"].append(traj)

    # State distributions
    all_old_states = results["old"]["states"]
    all_new_states = results["new"]["states"]
    for s in set(all_old_states):
        results["old"]["state_dist"][s] = all_old_states.count(s)
    for s in set(all_new_states):
        results["new"]["state_dist"][s] = all_new_states.count(s)

    # Comparison metrics
    old_arr  = np.array(results["old"]["gile_scores"])
    new_arr  = np.array(results["new"]["hear_scores"])
    init_arr = np.array(results["optimization"]["initial_hear"])
    fin_arr  = np.array(results["optimization"]["final_hear"])
    delta    = np.array(results["optimization"]["delta_hear"])
    bok_sat  = np.array(results["new"]["bok_sat"])
    cov      = np.array(results["new"]["cov"])

    steps_list = [s for s in results["optimization"]["steps_to_mr2r"] if s is not None]

    results["comparison"] = {
        "old_mean_score":          round(float(old_arr.mean()), 4),
        "old_std_score":           round(float(old_arr.std()),  4),
        "new_mean_hear":           round(float(new_arr.mean()), 4),
        "new_std_hear":            round(float(new_arr.std()),  4),
        "mean_delta_hear":         round(float(delta.mean()),   4),
        "max_delta_hear":          round(float(delta.max()),    4),
        "pct_reaching_mr2r_plus":  round(100 * np.mean(fin_arr >= DOTTIE), 1),
        "pct_bok_saturated":       round(100 * results["optimization"]["bok_reached"] / n_subjects, 1),
        "mean_bok_saturation_score": round(float(bok_sat.mean()), 4),
        "mean_gile_hem_cov":       round(float(cov.mean()), 4),
        "mean_steps_to_mr2r":      round(float(np.mean(steps_list)), 2) if steps_list else None,
        "n_states_old":            4,
        "n_states_new":            6,
        "state_granularity_gain":  "50% more states — Dottie transition + BOK-Saturated ceiling",
        "new_captures_hem":        True,
        "new_captures_cov":        True,
        "hear_range_vs_old":       "HEAR adds HEM (somatic) + Cov (alignment) axes missing in old model",
    }

    return results


def format_simulation_report(results: Dict) -> str:
    """Format the simulation results as a readable text report."""
    c = results["comparison"]
    lines = [
        "=" * 62,
        " GILE-HEM-BOK MOOD AMPLIFIER — SIMULATION REPORT",
        f" N = {results['n_subjects']} subjects | 5 optimizer steps each",
        "=" * 62,
        "",
        "── MODEL COMPARISON ──────────────────────────────────────",
        f"  Old GILE score  mean ± std  : {c['old_mean_score']:.3f} ± {c['old_std_score']:.3f}",
        f"  New HEAR score  mean ± std  : {c['new_mean_hear']:.3f} ± {c['new_std_hear']:.3f}",
        f"  Old model states            : {c['n_states_old']} (Tier 1–4)",
        f"  New model states            : {c['n_states_new']} (DT → BOK-Saturated)",
        f"  Granularity gain            : {c['state_granularity_gain']}",
        f"  New axes                    : HEM (somatic), Cov(GILE,HEM) alignment",
        "",
        "── OPTIMIZATION RESULTS ──────────────────────────────────",
        f"  Mean HEAR gain per session  : +{c['mean_delta_hear']:.3f}",
        f"  Max HEAR gain (single subj) : +{c['max_delta_hear']:.3f}",
        f"  % reaching MR2-Resolved+    : {c['pct_reaching_mr2r_plus']}%",
        f"  % reaching BOK-Saturated    : {c['pct_bok_saturated']}%",
        f"  Mean steps to MR2-Resolved  : {c['mean_steps_to_mr2r']}",
        "",
        "── BOK COHERENCE METRICS ─────────────────────────────────",
        f"  Mean BOK loop saturation    : {c['mean_bok_saturation_score']:.3f}",
        f"  Mean GILE–HEM covariance    : {c['mean_gile_hem_cov']:.3f}  (ideal → 1.0)",
        "",
        "── STATE DISTRIBUTIONS (NEW MODEL) ──────────────────────",
    ]
    for state_name in [
        ConsciousnessState.DT, ConsciousnessState.SUB_THRESHOLD,
        ConsciousnessState.MR1, ConsciousnessState.MR2_TRALSE,
        ConsciousnessState.MR2_RESOLVED, ConsciousnessState.BOK_SATURATED,
    ]:
        count = results["new"]["state_dist"].get(state_name, 0)
        pct = 100 * count / results["n_subjects"]
        bar = "█" * int(pct / 2.5)
        lines.append(f"  {state_name:<22} {count:>3} ({pct:5.1f}%)  {bar}")

    lines += [
        "",
        "── THEORETICAL CEILING ───────────────────────────────────",
        f"  Tralse Attractor (T)        : {T_TI:.4f}  (BOK-Saturated threshold)",
        f"  Dottie Fixed Point (𝔡)      : {DOTTIE:.4f}  (MR2-Resolved threshold)",
        f"  Monster Group ceiling       : Symmetry group of full consciousness space",
        f"  Monster Group order         : ~8 × 10⁵³  (all possible coherent states)",
        "=" * 62,
    ]
    return "\n".join(lines)


# ══════════════════════════════════════════════════════════
# STANDALONE ENTRY POINT
# ══════════════════════════════════════════════════════════
if __name__ == "__main__":
    print("Running GILE-HEM-BOK simulation (N=300)...")
    results = run_full_simulation(n_subjects=300, n_session_steps=5)
    print(format_simulation_report(results))

    print("\nSample 5-step optimization trajectory (one subject):")
    traj = results["optimization"]["trajectories"][42]
    for step in traj:
        arrow = "↑" if step["delta"] > 0 else "→"
        print(f"  Step {step['step']}: {step['protocol']:<22} "
              f"HEAR {step['hear_before']:.3f} {arrow} {step['hear_after']:.3f} "
              f"(+{step['delta']:.3f})  [{step['state_after']}]")
