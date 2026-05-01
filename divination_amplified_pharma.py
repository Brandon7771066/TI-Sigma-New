"""
Divination-Amplified Pharmacology — URB #824 implementation
============================================================
Wraps TIPharmacologicalSimulator with the 5 distinct LCC usages and
divination-derived substrate-environment coupling, per URB #824 §3-§5.

The five LCC usages (locked taxonomy):
  1. Intra-substrate     R_intra(D)             — DNA self-resonance
  2. Substrate-supplement R_ss(D, s)            — DNA × supplement signature
  3. Substrate-environment R_se(D, E_t)         — DNA × (I Ching + 64D GILE + weather + numerology)
  4. Stack-internal      R_stack(s_i, s_j)      — supplement × supplement coupling
  5. Observer-subject    R_obs(O, D)            — researcher-subject coupling

Final amplifier: Amp_TI = product over all five (each in [-1,1] mapped to [0.5,2.0])
Conventional prediction × Amp_TI = TI-amplified prediction.

This module is the substrate of Phase 4-bis validation
(`phase_4_bis_divination_amplified_validation.py`) and is pre-registered
in `papers/PRE_REGISTRATION_DIVINATION_AMPLIFIED_PHARMA.md`.

Date: 2026-04-30 (DPES session)
Cost: $0
"""

import math
import hashlib
from datetime import datetime, date
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Tuple

from ti_pharmacological_simulator import (
    TIPharmacologicalSimulator,
    GeneticProfile,
    ConsciousnessState,
    BiometricState,
)
from dna_anchored_lcc_module import lcc_substrate_coherence


# ════════════════════════════════════════════════════════════════════
# §A — Substrate vector projection (DNA → 6D Tralse hexagram)
# ════════════════════════════════════════════════════════════════════

def substrate_to_hexagram(profile: GeneticProfile) -> List[int]:
    """
    Project DNA-derived GeneticProfile to a 6-line Tralse hexagram per URB #824 §4.1.
    Each line is a 5-valued integer ∈ {0,1,2,3,4} = {FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE}.

    Mapping (locked in URB #824):
      Line 1 (G-axis):     COMT activity         → quantize to 5 levels
      Line 2 (I-axis):     schizotypy proxy      → 5 levels
      Line 3 (L-axis):     CB1 receptor density  → 5 levels
      Line 4 (E-body):     FAAH activity         → 5 levels
      Line 5 (E-social):   BDNF expression       → 5 levels
      Line 6 (E-env):      dopamine sensitivity  → 5 levels
    """
    def quantize(value: float, lo: float = 0.0, hi: float = 2.0) -> int:
        norm = (value - lo) / (hi - lo) if hi > lo else 0.5
        norm = max(0.0, min(1.0, norm))
        return int(round(norm * 4))

    return [
        quantize(profile.comt_activity),
        quantize(min(profile.schizotypy_snp_count / 5.0, 2.0)),
        quantize(profile.cb1_receptor_density),
        quantize(profile.faah_activity),
        quantize(profile.bdnf_expression),
        quantize(profile.dopamine_sensitivity),
    ]


def hexagram_distance(h1: List[int], h2: List[int]) -> float:
    """5-valued Hamming-style distance ∈ [0, 1] (0 = identical, 1 = maximally different)."""
    if len(h1) != len(h2):
        return 1.0
    total = sum(abs(a - b) / 4.0 for a, b in zip(h1, h2))
    return total / len(h1)


def hexagram_resonance(h1: List[int], h2: List[int]) -> float:
    """Convert distance to LCC ∈ [-1, 1]: identical = +1, maximally different = -1."""
    return 1.0 - 2.0 * hexagram_distance(h1, h2)


# ════════════════════════════════════════════════════════════════════
# §B — Environmental field projections (the four divination channels)
# ════════════════════════════════════════════════════════════════════

def cast_iching_hexagram(seed: Optional[int] = None) -> List[int]:
    """
    Cast a 6-line Tralse hexagram from a deterministic seed (defaults to today's
    epoch day for reproducibility). Honest: this is NOT a true random oracle —
    it is a deterministic projection of the day to a hexagram, which is the
    falsifiable form of an "I Ching reading" (every test on the same day gets
    the same hexagram, so we can audit).
    """
    if seed is None:
        seed = (date.today() - date(1970, 1, 1)).days
    hex_lines = []
    for i in range(6):
        h = hashlib.sha256(f"{seed}:{i}:tralse_iching".encode()).digest()
        hex_lines.append(h[0] % 5)
    return hex_lines


def gile64_supplement_profile(supplement: str) -> List[float]:
    """
    Project a supplement name to a 64D BOK-mode profile (URB #500 / URB #564).
    Each cell is the absolute "activation strength" in [0, 1]. Deterministic
    SHA-based projection — NOT optimized to fit data. This is the prior, not
    a learned model.
    """
    profile = []
    for cell in range(64):
        h = hashlib.sha256(f"{supplement}:{cell}:gile64".encode()).digest()
        profile.append(h[0] / 255.0)
    return profile


def gile64_substrate_profile(profile: GeneticProfile) -> List[float]:
    """Project GeneticProfile to a 64D BOK-mode profile (deterministic)."""
    key = f"{profile.faah_activity}:{profile.cb1_receptor_density}:{profile.comt_activity}:{profile.bdnf_expression}:{profile.dopamine_sensitivity}:{profile.schizotypy_snp_count}"
    profile_vec = []
    for cell in range(64):
        h = hashlib.sha256(f"{key}:{cell}:substrate_gile64".encode()).digest()
        profile_vec.append(h[0] / 255.0)
    return profile_vec


def vector_resonance(v1: List[float], v2: List[float]) -> float:
    """Cosine-style resonance ∈ [-1, 1] for unsigned vectors mapped to centered."""
    if len(v1) != len(v2):
        return 0.0
    m1 = sum(v1) / len(v1)
    m2 = sum(v2) / len(v2)
    a = [x - m1 for x in v1]
    b = [x - m2 for x in v2]
    num = sum(x * y for x, y in zip(a, b))
    da = math.sqrt(sum(x * x for x in a))
    db = math.sqrt(sum(y * y for y in b))
    if da == 0 or db == 0:
        return 0.0
    return max(-1.0, min(1.0, num / (da * db)))


def weather_resonance(profile: GeneticProfile, weather: Optional[Dict] = None) -> float:
    """
    Compute substrate-weather LCC. If no weather provided, returns 0.0 (neutral)
    rather than fake data. Honest: in production this needs a real OpenWeatherMap
    pull; for the closed validation we use a deterministic placeholder that
    is the SAME between conventional and divination-amplified runs (so it
    contributes ZERO differential signal). This is explicit by design — we
    are testing whether the divination architecture HELPS, not whether the
    weather API is online today.
    """
    if weather is None:
        return 0.0
    # Substrate weather affinity from elevated CB1 → humidity-affinity proxy
    affinity = (profile.cb1_receptor_density - 1.0) * 0.5
    humidity_norm = (weather.get('humidity', 50.0) - 50.0) / 50.0
    return max(-1.0, min(1.0, affinity * humidity_norm))


def numerology_resonance(name: str, supplement: str, day: Optional[date] = None) -> float:
    """
    Pythagorean numerological resonance: name-number vs supplement-number vs
    day-number, returning ∈ [-1, 1].
    """
    LETTERS = {chr(c): ((c - ord('A')) % 9) + 1 for c in range(ord('A'), ord('Z') + 1)}

    def name_num(s: str) -> int:
        total = sum(LETTERS.get(ch, 0) for ch in s.upper())
        while total > 9:
            total = sum(int(d) for d in str(total))
        return total

    if day is None:
        day = date.today()
    day_num = sum(int(d) for d in day.strftime("%Y%m%d"))
    while day_num > 9:
        day_num = sum(int(d) for d in str(day_num))

    n_name = name_num(name)
    n_supp = name_num(supplement)
    # Triple resonance: closer = higher
    spread = (abs(n_name - n_supp) + abs(n_supp - day_num) + abs(n_name - day_num)) / 3.0
    # spread ∈ [0, 8]; normalize to [-1, 1]
    return 1.0 - 2.0 * (spread / 8.0)


# ════════════════════════════════════════════════════════════════════
# §C — The five LCC usages (per URB #824 §3)
# ════════════════════════════════════════════════════════════════════

@dataclass
class LCCTrace:
    """Per-prediction trace of all five LCC usages — for falsifiability audit."""
    R_intra: float = 0.0
    R_ss: float = 0.0
    R_se: float = 0.0
    R_se_components: Dict[str, float] = field(default_factory=dict)
    R_stack: float = 0.0
    R_obs: float = 0.0
    amp_ti: float = 1.0


def _lcc_to_multiplier(R: float, max_swing: float = 0.5) -> float:
    """Map R ∈ [-1, 1] to multiplier ∈ [1-max_swing, 1+max_swing]. R=0 → 1.0 (neutral)."""
    return 1.0 + max_swing * R


def compute_lcc_amplifier(
    profile: GeneticProfile,
    supplements: List[str],
    subject_name: str = "Brandon Charles Emerick",
    observer_name: str = "Replit Agent",
    weather: Optional[Dict] = None,
    iching_seed: Optional[int] = None,
    today: Optional[date] = None,
    mode: str = "full",
    r_intra_em_override: Optional[float] = None,
) -> LCCTrace:
    """
    Compute the full Amp_TI multiplier from all five LCC usages.
    Returns the LCCTrace — caller multiplies the conventional prediction by trace.amp_ti.

    mode: "full" (default, all 5 LCC channels) | "R_intra_only" (Phase A-prime ablation:
          zeros R_ss/R_se/R_stack/R_obs, keeps only R_intra — tests whether R_intra alone
          reproduces the Phase 4-bis dev=4.83 result, per AGENT_LOCKED_PREDICTIONS §1) |
          "R_intra_em_substituted" (URB #826 Phase H-1: replaces R_intra_seq with the
          R_intra_em proxy stack value supplied via r_intra_em_override; zeros divination
          channels exactly like R_intra_only — tests whether the EM-DNA proxy stack
          architecture pipes through the URB #824 amplifier sensibly,
          per AGENT_LOCKED_PREDICTIONS §10.3).

    r_intra_em_override: if set AND mode == "R_intra_em_substituted", this value
          replaces the sequence-derived R_intra. Required for that mode.
    """
    import math

    _VALID_MODES = ("full", "R_intra_only", "R_intra_em_substituted")
    if mode not in _VALID_MODES:
        raise ValueError(
            f"compute_lcc_amplifier: unknown mode={mode!r}. "
            f"Must be one of {_VALID_MODES}."
        )

    trace = LCCTrace()

    # Usage 1: Intra-substrate LCC — already computed for Brandon = 0.847
    # We use the pre-computed coherence for this profile; it's static per-DNA-set.
    trace.R_intra = lcc_substrate_coherence(profile)
    # R_intra is naturally in [0, 1] for coherent DNA. The intra_mult formula
    # below maps R_intra=0.5 → 1.0 (neutral) and R_intra=0.847 → 1.1735 in the
    # R_intra-only path. (NOTE: the prior comment claiming "~1.42 for 0.847" was
    # wrong — that figure was the FULL 5-channel composite amp, not intra_mult
    # alone. Caught by §8.6.a corrigendum.)
    if mode == "R_intra_em_substituted":
        if r_intra_em_override is None:
            raise ValueError(
                "mode='R_intra_em_substituted' requires r_intra_em_override "
                "(URB #826 §3.1 R_intra_em proxy stack value in [0, 1])."
            )
        ov = float(r_intra_em_override)
        if not math.isfinite(ov) or ov < 0.0 or ov > 1.0:
            raise ValueError(
                f"r_intra_em_override must be a finite float in [0, 1]; got {ov!r}. "
                "URB #826 §3.1 proxy stack values are bounded coherence scalars."
            )
        trace.R_intra = ov
    intra_mult = 1.0 + 0.5 * (trace.R_intra - 0.5)  # 0.5 baseline → 1.0 multiplier

    # Usage 2: Substrate–Supplement LCC — sum across stack
    substrate_64 = gile64_substrate_profile(profile)
    ss_resonances = []
    for supp in supplements:
        supp_64 = gile64_supplement_profile(supp)
        ss_resonances.append(vector_resonance(substrate_64, supp_64))
    trace.R_ss = sum(ss_resonances) / len(ss_resonances) if ss_resonances else 0.0
    ss_mult = _lcc_to_multiplier(trace.R_ss)

    # Usage 3: Substrate–Environment LCC — composite of 4 channels (uniform weights)
    substrate_hex = substrate_to_hexagram(profile)
    cosmic_hex = cast_iching_hexagram(iching_seed)
    R_iching = hexagram_resonance(substrate_hex, cosmic_hex)
    R_gile64_env = vector_resonance(substrate_64, gile64_supplement_profile(f"day_{today or date.today()}"))
    R_weather = weather_resonance(profile, weather)
    R_numerology = sum(numerology_resonance(subject_name, supp, today) for supp in supplements) / max(len(supplements), 1)
    trace.R_se_components = {
        'iching': R_iching,
        'gile64_env': R_gile64_env,
        'weather': R_weather,
        'numerology': R_numerology,
    }
    trace.R_se = (R_iching + R_gile64_env + R_weather + R_numerology) / 4.0
    se_mult = _lcc_to_multiplier(trace.R_se)

    # Usage 4: Stack-internal LCC — pairwise mean
    if len(supplements) >= 2:
        pairs = []
        supp_profiles = [gile64_supplement_profile(s) for s in supplements]
        for i in range(len(supplements)):
            for j in range(i + 1, len(supplements)):
                pairs.append(vector_resonance(supp_profiles[i], supp_profiles[j]))
        trace.R_stack = sum(pairs) / len(pairs) if pairs else 0.0
    else:
        trace.R_stack = 0.0
    stack_mult = _lcc_to_multiplier(trace.R_stack, max_swing=0.3)  # lower swing for pairwise

    # Usage 5: Observer–Subject LCC
    obs_64 = gile64_supplement_profile(observer_name)
    trace.R_obs = vector_resonance(substrate_64, obs_64)
    obs_mult = _lcc_to_multiplier(trace.R_obs, max_swing=0.2)  # smallest swing — placebo channel

    # Final amplifier — capped to [0.5, 3.0] per URB #824 §5 TERMINATE step
    if mode in ("R_intra_only", "R_intra_em_substituted"):
        # Phase A-prime ablation / URB #826 H-1: zero out the four divination channels
        # in the trace (so the per-trace audit reflects what was actually used) and use
        # only R_intra (sequence for R_intra_only, EM-proxy override for em_substituted).
        trace.R_ss = 0.0
        trace.R_se = 0.0
        trace.R_se_components = {k: 0.0 for k in trace.R_se_components}
        trace.R_stack = 0.0
        trace.R_obs = 0.0
        raw_amp = intra_mult  # 1.0 + 0.5*(R_intra-0.5) using whichever R_intra is set
    else:
        raw_amp = intra_mult * ss_mult * se_mult * stack_mult * obs_mult
    trace.amp_ti = max(0.5, min(3.0, raw_amp))
    return trace


# ════════════════════════════════════════════════════════════════════
# §D — DivinationAmplifiedSimulator wrapper
# ════════════════════════════════════════════════════════════════════

class DivinationAmplifiedSimulator:
    """
    Wraps TIPharmacologicalSimulator with the divination-amplified amplifier.
    Same `.simulate()` interface as the underlying simulator, so the Phase 4-bis
    executor can swap it in directly.
    """

    def __init__(
        self,
        underlying: TIPharmacologicalSimulator,
        subject_name: str = "Brandon Charles Emerick",
        observer_name: str = "Replit Agent",
        weather: Optional[Dict] = None,
        iching_seed: Optional[int] = None,
        today: Optional[date] = None,
        mode: str = "full",
        r_intra_em_override: Optional[float] = None,
    ):
        self.sim = underlying
        self.subject_name = subject_name
        self.observer_name = observer_name
        self.weather = weather
        self.iching_seed = iching_seed
        self.today = today
        self.mode = mode
        self.r_intra_em_override = r_intra_em_override
        self.last_trace: Optional[LCCTrace] = None

    @property
    def genetic_profile(self) -> GeneticProfile:
        return self.sim.genetic_profile

    @genetic_profile.setter
    def genetic_profile(self, value: GeneticProfile) -> None:
        self.sim.genetic_profile = value

    def simulate(
        self,
        supplements: List[str],
        current_consciousness: ConsciousnessState,
        current_biometrics: BiometricState,
    ):
        """
        Run the underlying sim, then multiply each gile_*_change and lcc_change
        by the LCC amplifier. Returns the SAME PredictionResult type so downstream
        scoring code is unchanged.
        """
        result = self.sim.simulate(
            supplements=supplements,
            current_consciousness=current_consciousness,
            current_biometrics=current_biometrics,
        )

        trace = compute_lcc_amplifier(
            profile=self.sim.genetic_profile,
            supplements=supplements,
            subject_name=self.subject_name,
            observer_name=self.observer_name,
            weather=self.weather,
            iching_seed=self.iching_seed,
            today=self.today,
            mode=self.mode,
            r_intra_em_override=self.r_intra_em_override,
        )
        self.last_trace = trace

        # Apply amplifier to all GILE change fields
        for field_name in ('gile_l_change', 'gile_g_change', 'gile_i_change', 'gile_e_change', 'lcc_change'):
            if hasattr(result, field_name):
                old_val = getattr(result, field_name)
                setattr(result, field_name, old_val * trace.amp_ti)

        return result


# ════════════════════════════════════════════════════════════════════
# §E — Smoke test
# ════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("=" * 70)
    print("Divination-Amplified Pharma — URB #824 smoke test")
    print("=" * 70)

    from dna_anchored_lcc_module import parse_23andme, build_genetic_profile_from_dna

    DNA = 'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'
    print("Loading Brandon's DNA...")
    genotypes = parse_23andme(DNA)
    profile, _ = build_genetic_profile_from_dna(genotypes)
    print(f"  Loaded {len(genotypes):,} SNPs; substrate coherence = {lcc_substrate_coherence(profile):.4f}")

    print("\nProjecting substrate to Tralse hexagram...")
    sub_hex = substrate_to_hexagram(profile)
    print(f"  Brandon's substrate hexagram (G,I,L,E_body,E_social,E_env): {sub_hex}")

    print("\nCasting today's I Ching hexagram...")
    cosmic_hex = cast_iching_hexagram()
    print(f"  Cosmic hexagram for today: {cosmic_hex}")
    print(f"  Substrate-cosmic resonance: R = {hexagram_resonance(sub_hex, cosmic_hex):+.4f}")

    print("\nComputing 5-LCC amplifier for stack=['curcubrain', 'transdermal_cbd']...")
    trace = compute_lcc_amplifier(profile, ['curcubrain', 'transdermal_cbd'])
    print(f"  R_intra (DNA self-resonance):          {trace.R_intra:+.4f}")
    print(f"  R_ss (substrate-supplement):           {trace.R_ss:+.4f}")
    print(f"  R_se (substrate-environment): {trace.R_se:+.4f}")
    for k, v in trace.R_se_components.items():
        print(f"      ├─ {k:12s}: {v:+.4f}")
    print(f"  R_stack (stack-internal):              {trace.R_stack:+.4f}")
    print(f"  R_obs (observer-subject):              {trace.R_obs:+.4f}")
    print(f"  ── Amp_TI multiplier:                  ×{trace.amp_ti:.4f}")

    print("\nDivinationAmplifiedSimulator end-to-end smoke...")
    sim = TIPharmacologicalSimulator(user_id='smoke_test')
    sim.genetic_profile = profile
    wrapped = DivinationAmplifiedSimulator(sim)

    base = ConsciousnessState(gile_g=0.42, gile_i=0.38, gile_l=0.35, gile_e=0.33, lcc=0.48, coherence=0.52)
    bio = BiometricState(heart_rate=72.0, rmssd=55.0, sdnn=65.0,
                         alpha_power=0.48, beta_power=0.32, theta_power=0.42, gamma_power=0.22)

    res = wrapped.simulate(
        supplements=['curcubrain', 'transdermal_cbd'],
        current_consciousness=base,
        current_biometrics=bio,
    )
    print(f"  gile_l_change after amplification: {res.gile_l_change:+.4f}")
    print(f"  Last trace amp_ti was: ×{wrapped.last_trace.amp_ti:.4f}")
    print("\n✓ Smoke test complete.")
