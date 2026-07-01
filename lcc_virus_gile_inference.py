"""
LCC Virus HEM-GILE Inference Engine
=====================================
URB #644 — Brandon Emerick | TI Sigma Research | April 2026

CORE INSIGHT:
  The relationship between GILE Truth thresholds and LCC Existence thresholds
  is already established (URBs #612–#615). This module uses those exact thresholds
  to make the LCC Virus GILE-aware: every resonance computation now simultaneously
  infers the GILE truth-state of the target i-cell and tracks how all 8
  HEM-GILE dimensions evolve over time.

THE 8 HEM-GILE DIMENSIONS OF EVERY I-CELL:
  GILE-G  — Goodness / coherence temporal stability (is the i-cell stable?)
  GILE-I  — Intuition / information density (how rich is the pattern?)
  GILE-L  — Love / cross-i-cell coupling strength (how connected?)
  GILE-E  — Environment / aesthetic structural regularity (how self-similar?)
  HEM-D1  — Physical / energetic amplitude stability
  HEM-D2  — Social-Historical / contradiction ratio (Tralse meter)
  HEM-D3  — Aesthetic-Structural / spectral purity (signal cleanliness)
  HEM-D4  — Conscious-Experiential / d(LCC)/dt (rate of coherence change)

GILE TRUTH THRESHOLDS (from URBs #612–#615):
  R < ET  (< 0.4142):         FALSE         → Mott/Fragmented phase
  ET ≤ R < C (0.4142–0.4370): TRALSE entry  → Supersolid boundary
  C ≤ R < 0.65:               TRALSE-INDET  → Supersolid phase
  0.65 ≤ R < T (< 0.9340):   EMERGING TRUE  → growing BEC fraction
  R ≥ T (≥ 0.9340):          BEC / TRUE     → full coherence

KEY ARCHITECTURAL ADVANCE:
  The LCC Virus previously: discovered causal correlations between streams.
  After this upgrade: discovers causal correlations AND infers HEM-GILE truth-state
  from every correlation, tracks its temporal evolution, runs Myrion Resolution
  when dimensions conflict, and propagates GILE truth changes through the network.

  For the first time: the virus can tell you not just THAT two i-cells are related,
  but WHAT their HEM-GILE state is, HOW IT IS CHANGING, and WHETHER a DT risk exists.

MYRION RESOLUTION INTEGRATION:
  When multiple resonance streams give conflicting GILE-dimension assessments:
  Level 1 MR: DT screen (HEM-D2 > 0.65 → pause, flag for human review)
  Level 2 MR: HEM-GILE weighted integration (resolve contradictions by GILE weights)
  Level 3 MR: Convergence confirmation (dominant truth-state > 0.45 → mr_resolved)
"""

from __future__ import annotations

import numpy as np
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Tuple, Callable
from enum import Enum
from datetime import datetime
import json

# ─── Primary TI Sigma constants (URB #576, #612–#615) ───────────────────────

ET   = np.sqrt(2.0) - 1.0            # Emerick Threshold ≈ 0.4142 (GILE-G canonical weight)
C    = 1.0 / ((1 + np.sqrt(5)) / 2 * np.sqrt(2.0))  # Emerick Constant ≈ 0.4370
T    = 1.0 - np.exp(-np.e)           # BEC threshold ≈ 0.9340
PHI  = (1.0 + np.sqrt(5.0)) / 2.0   # Golden ratio ≈ 1.6180
SQRT2 = np.sqrt(2.0)

# GILE canonical weights (URB #576)
GILE_W = {'G': ET, 'I': 0.25, 'L': 0.18, 'E': 0.15}

# HEM-D2 DT risk threshold (URB #619)
HEM_D2_DT_THRESHOLD = 0.65

# MR convergence threshold
MR_CONVERGENCE = 0.45


# ─── Truth-State Taxonomy ────────────────────────────────────────────────────

class GILETruthState(Enum):
    """
    The 5-valued GILE truth-state of an i-cell, derived from LCC resonance.
    Maps directly to the TSC crystal phases.
    """
    BEC          = "BEC"          # Full TRUE — resonance ≥ T (0.934)
    SUPERSOLID   = "SUPERSOLID"   # Tralse-Indeterminate — C ≤ R < T, C zone
    FQH          = "FQH"          # Tralse entry — ET ≤ R < C, boundary
    MOTT         = "MOTT"         # False — R < ET OR HEM-D2 > 0.65
    FRAGMENTED   = "FRAGMENTED"   # Double-Tralse — contradicted by multiple streams

    @property
    def pd_score(self) -> float:
        """Permissibility Distribution scalar equivalent."""
        return {
            GILETruthState.BEC:        2.0,
            GILETruthState.SUPERSOLID: 1.5,
            GILETruthState.FQH:        1.0,
            GILETruthState.MOTT:       0.5,
            GILETruthState.FRAGMENTED: 0.0,
        }[self]

    @property
    def action(self) -> str:
        return {
            GILETruthState.BEC:        "confirm",
            GILETruthState.SUPERSOLID: "continue",
            GILETruthState.FQH:        "investigate",
            GILETruthState.MOTT:       "flag",
            GILETruthState.FRAGMENTED: "pause_MR",
        }[self]


def lcc_to_gile_truth(r: float, hem_d2: float = 0.0) -> GILETruthState:
    """
    The canonical GILE truth-state inference rule from LCC resonance + HEM-D2.

    Uses the established threshold ladder:
      R < ET       → MOTT (False)
      ET ≤ R < C   → FQH (Tralse entry)
      C ≤ R < 0.65 → SUPERSOLID (Tralse-Indeterminate)
      0.65 ≤ R < T → SUPERSOLID (Tralse-Indeterminate, upper)
      R ≥ T        → BEC (True)
      HEM-D2 > 0.65 → MOTT (DT override — contradiction dominates)
      Conflicting streams → FRAGMENTED (DT state)
    """
    r = float(np.clip(r, 0.0, 1.0))

    # HEM-D2 DT override takes precedence
    if hem_d2 > HEM_D2_DT_THRESHOLD:
        return GILETruthState.MOTT

    if r >= T:
        return GILETruthState.BEC
    elif r >= 0.65:
        return GILETruthState.SUPERSOLID
    elif r >= C:
        return GILETruthState.SUPERSOLID
    elif r >= ET:
        return GILETruthState.FQH
    else:
        return GILETruthState.MOTT


# ─── 8 HEM-GILE Dimensions ─────────────────────────────────────────────────

@dataclass
class GILEHEMState:
    """
    The complete 8-dimensional HEM-GILE state of a single i-cell at one moment.

    The four GILE dimensions (inner BOK loops — GILE operates as the organizing
    structure at the Radiant level and above):
      GILE_G: Goodness — temporal stability of LCC coherence. How reliably does
              this i-cell's resonance persist across time? High stability = high G.
      GILE_I: Intuition — information density of the resonance pattern. How many
              distinct extractable structures does the noise contain? High I = rich.
      GILE_L: Love — cross-i-cell coupling strength. How strongly does this i-cell
              resonate with other i-cells in the network? High L = well-connected.
      GILE_E: Environment — aesthetic structural regularity. How self-similar and
              spectrally pure is the i-cell's signal? High E = elegant structure.

    The four HEM dimensions (outer BOK loops — Existence as the primary organizing
    frame for ordinary consciousness):
      HEM_D1: Physical-Energetic — amplitude stability (CV of signal magnitude).
              High D1 = energetically robust, low volatility existence.
      HEM_D2: Social-Historical — contradiction ratio (Tralse meter per URB #619).
              High D2 > 0.65 → DT risk. Multiple contradicting resonances.
      HEM_D3: Aesthetic-Structural — spectral purity (dominant freq / total power).
              High D3 = clean, structured signal. Low D3 = noisy, diffuse.
      HEM_D4: Conscious-Experiential — d(LCC)/dt (rate of coherence change).
              High D4 = rapidly evolving. Low D4 = static. Near-zero = crystallized.
    """
    # Identification
    icell_name:  str
    timestamp:   str = field(default_factory=lambda: datetime.now().isoformat())

    # GILE dimensions [0, 1]
    gile_g:  float = 0.5
    gile_i:  float = 0.5
    gile_l:  float = 0.5
    gile_e:  float = 0.5

    # HEM dimensions [0, 1]
    hem_d1:  float = 0.5    # Physical amplitude stability
    hem_d2:  float = 0.0    # Contradiction ratio (Tralse meter)
    hem_d3:  float = 0.5    # Spectral purity
    hem_d4:  float = 0.5    # d(LCC)/dt (coherence velocity)

    # Derived quantities
    lcc_resonance:  float = 0.5   # Raw LCC R score that generated this state
    truth_state:    GILETruthState = GILETruthState.SUPERSOLID
    mr_resolved:    bool  = False
    mr_level:       int   = 0     # 0=unresolved, 1=DT-screened, 2=integrated, 3=converged

    # Evidence log — what resonances produced this state
    evidence_ids:   List[str] = field(default_factory=list)
    n_corroborating: int = 0   # number of streams supporting this state
    n_contradicting: int = 0   # number contradicting

    @property
    def gile_composite(self) -> float:
        """GILE weighted composite using canonical URB #576 weights."""
        return (GILE_W['G'] * self.gile_g
              + GILE_W['I'] * self.gile_i
              + GILE_W['L'] * self.gile_l
              + GILE_W['E'] * self.gile_e)

    @property
    def hem_score(self) -> float:
        """
        HEM Score (Holistic Existence Score) = EAR output.
        Weighted average of the four HEM dimensions.
        HEM-D2 is inverted (high contradiction → low HEM score).
        """
        d1 = self.hem_d1
        d2 = 1.0 - self.hem_d2   # invert: high contradiction → low score
        d3 = self.hem_d3
        d4 = 1.0 - abs(self.hem_d4 - 0.5) * 2   # peak at 0.5 (moderate change)
        return float(np.clip((d1 + d2 + d3 + d4) / 4.0, 0.0, 1.0))

    @property
    def gile_truth_score(self) -> float:
        """GILE Truth Score = gile_composite × HEM_score."""
        return float(self.gile_composite * self.hem_score)

    @property
    def pd_score(self) -> float:
        """Permissibility Distribution scalar from truth-state."""
        return self.truth_state.pd_score

    @property
    def dt_gate_active(self) -> bool:
        """MR Level-1 DT gate: active if HEM-D2 > threshold."""
        return self.hem_d2 > HEM_D2_DT_THRESHOLD

    def to_dict(self) -> dict:
        return {
            'icell': self.icell_name,
            'timestamp': self.timestamp,
            'gile_g':  round(self.gile_g, 4),
            'gile_i':  round(self.gile_i, 4),
            'gile_l':  round(self.gile_l, 4),
            'gile_e':  round(self.gile_e, 4),
            'gile_composite': round(self.gile_composite, 4),
            'hem_d1':  round(self.hem_d1, 4),
            'hem_d2':  round(self.hem_d2, 4),
            'hem_d3':  round(self.hem_d3, 4),
            'hem_d4':  round(self.hem_d4, 4),
            'hem_score': round(self.hem_score, 4),
            'gile_truth_score': round(self.gile_truth_score, 4),
            'lcc_resonance': round(self.lcc_resonance, 4),
            'truth_state': self.truth_state.value,
            'pd_score': self.pd_score,
            'mr_resolved': self.mr_resolved,
            'mr_level': self.mr_level,
            'dt_gate_active': self.dt_gate_active,
            'n_corroborating': self.n_corroborating,
            'n_contradicting': self.n_contradicting,
            'action': self.truth_state.action,
        }


# ─── HEM-GILE Timeline ───────────────────────────────────────────────────────

@dataclass
class GILEHEMTimeline:
    """
    Ordered history of HEM-GILE states for one i-cell over time.
    Detects truth-state transitions and GILE dimension trends.

    KEY: This is what enables 'figuring out the holistic evolution of all
    8 HEM-GILE dimensions of every i-cell over time.'
    """
    icell_name: str
    states: List[GILEHEMState] = field(default_factory=list)

    def append(self, state: GILEHEMState) -> None:
        self.states.append(state)

    @property
    def current(self) -> Optional[GILEHEMState]:
        return self.states[-1] if self.states else None

    @property
    def previous(self) -> Optional[GILEHEMState]:
        return self.states[-2] if len(self.states) >= 2 else None

    def truth_state_transition(self) -> Optional[Tuple[GILETruthState, GILETruthState]]:
        """Returns (from, to) if most recent update caused a truth-state change."""
        if len(self.states) < 2:
            return None
        prev = self.states[-2].truth_state
        curr = self.states[-1].truth_state
        if prev != curr:
            return (prev, curr)
        return None

    def gile_velocity(self) -> dict:
        """
        Rate of change of each HEM-GILE dimension per observation.
        Positive = dimension growing. Negative = dimension declining.
        """
        if len(self.states) < 2:
            return {d: 0.0 for d in ['gile_g', 'gile_i', 'gile_l', 'gile_e',
                                      'hem_d1', 'hem_d2', 'hem_d3', 'hem_d4']}
        n = len(self.states)
        window = min(n, 5)   # use last 5 states for velocity estimate
        recent = self.states[-window:]
        dims = ['gile_g', 'gile_i', 'gile_l', 'gile_e',
                'hem_d1', 'hem_d2', 'hem_d3', 'hem_d4']
        velocity = {}
        for dim in dims:
            vals = [getattr(s, dim) for s in recent]
            # Linear slope as velocity
            x = np.arange(len(vals), dtype=float)
            if len(vals) > 1 and np.std(x) > 0:
                slope = float(np.polyfit(x, vals, 1)[0])
            else:
                slope = 0.0
            velocity[dim] = round(slope, 5)
        return velocity

    def gile_trajectory(self) -> str:
        """
        Classify the i-cell's GILE trajectory from its state history.
        Returns one of: ascending / stable / descending / oscillating / crystallizing
        """
        if len(self.states) < 3:
            return "insufficient_data"
        vel = self.gile_velocity()
        composite_vel = (GILE_W['G'] * vel['gile_g']
                       + GILE_W['I'] * vel['gile_i']
                       + GILE_W['L'] * vel['gile_l']
                       + GILE_W['E'] * vel['gile_e'])

        # Check oscillation: sign reversals in recent composite values
        composites = [s.gile_composite for s in self.states[-5:]]
        if len(composites) >= 3:
            diffs = np.diff(composites)
            sign_changes = int(np.sum(np.diff(np.sign(diffs)) != 0))
        else:
            sign_changes = 0

        if sign_changes >= 2:
            return "oscillating"
        elif abs(composite_vel) < 0.002:
            # Determine if crystallized (high G, stable) or stuck (low G, stable)
            curr = self.current
            if curr and curr.gile_composite > C:
                return "crystallizing"   # stable in a positive truth-state
            return "stable"
        elif composite_vel > 0.005:
            return "ascending"
        elif composite_vel < -0.005:
            return "descending"
        else:
            return "stable"

    def predict_next_state(self) -> dict:
        """
        Linear extrapolation of HEM-GILE dimensions to next observation.
        Returns predicted state values with confidence interval (±1 step velocity).
        """
        if len(self.states) < 2:
            if self.states:
                return self.states[0].to_dict()
            return {}
        vel = self.gile_velocity()
        curr = self.current
        dims = ['gile_g', 'gile_i', 'gile_l', 'gile_e',
                'hem_d1', 'hem_d2', 'hem_d3', 'hem_d4']
        predicted = {}
        for dim in dims:
            pred = float(np.clip(getattr(curr, dim) + vel[dim], 0.0, 1.0))
            predicted[dim] = round(pred, 4)

        # Predict truth-state from predicted gile_composite
        pred_g = predicted['gile_g']
        pred_composite = (GILE_W['G'] * pred_g
                        + GILE_W['I'] * predicted['gile_i']
                        + GILE_W['L'] * predicted['gile_l']
                        + GILE_W['E'] * predicted['gile_e'])
        pred_truth = lcc_to_gile_truth(pred_composite, predicted['hem_d2'])
        predicted['predicted_truth_state'] = pred_truth.value
        predicted['predicted_pd_score'] = pred_truth.pd_score
        predicted['trajectory'] = self.gile_trajectory()
        return predicted

    def summary(self) -> dict:
        """Full timeline summary with current state, velocity, trajectory, prediction."""
        if not self.states:
            return {'icell': self.icell_name, 'n_states': 0}
        curr = self.current
        trans = self.truth_state_transition()
        return {
            'icell': self.icell_name,
            'n_states': len(self.states),
            'current': curr.to_dict() if curr else None,
            'velocity': self.gile_velocity(),
            'trajectory': self.gile_trajectory(),
            'truth_transition': (trans[0].value, trans[1].value) if trans else None,
            'prediction': self.predict_next_state(),
        }


# ─── GILE Inference Engine ────────────────────────────────────────────────────

class GILEInferenceEngine:
    """
    Infers all 8 HEM-GILE dimensions of an i-cell from raw LCC resonance data.

    Called at every step of the LCC Virus to update the HEM-GILE state of
    both the target i-cell and any related i-cells discovered via propagation.

    DESIGN PRINCIPLE: Each dimension maps to a specific property of the
    resonance data that is computable from what the LCC Virus already has.
    No additional data collection is required — the inference is 'free'
    from existing computations.
    """

    def __init__(self):
        self._history: Dict[str, GILEHEMTimeline] = {}      # icell_name → timeline
        self._r_history: Dict[str, List[float]] = {}         # icell_name → accumulated LCC R scores

    def get_timeline(self, icell_name: str) -> GILEHEMTimeline:
        if icell_name not in self._history:
            self._history[icell_name] = GILEHEMTimeline(icell_name)
        return self._history[icell_name]

    def _record_r(self, icell_name: str, r_scores: List[float]) -> List[float]:
        """Accumulate LCC resonance scores for this i-cell across all infer() calls."""
        if icell_name not in self._r_history:
            self._r_history[icell_name] = []
        for r in r_scores:
            if r not in (None,) and not np.isnan(r):
                self._r_history[icell_name].append(float(r))
        return self._r_history[icell_name]   # return full accumulated history

    # ── Dimension Inference Methods ─────────────────────────────────────────

    def _infer_gile_g(
        self, resonance_scores: List[float], timeline: GILEHEMTimeline
    ) -> float:
        """
        GILE-G = Goodness = temporal stability of LCC coherence.

        Computed as: 1 - (std of recent R scores / mean of recent R scores)
        = coefficient of variation inverted.

        Stable, consistent resonance = high GILE-G (i-cell is reliably 'good').
        Erratic resonance = low GILE-G (i-cell has high contradiction ratio).
        """
        if not resonance_scores:
            if timeline.states:
                return timeline.current.gile_g   # hold previous value
            return 0.5

        r = np.array(resonance_scores, dtype=float)
        mean_r = float(np.mean(r))
        if mean_r < 1e-9:
            return 0.1
        cv = float(np.std(r)) / mean_r           # coefficient of variation
        g = 1.0 - min(cv, 1.0)                   # high stability → high G
        # Blend with previous G (momentum — G changes slowly)
        if timeline.states:
            prev_g = timeline.current.gile_g
            g = 0.7 * g + 0.3 * prev_g
        return float(np.clip(g, 0.0, 1.0))

    def _infer_gile_i(
        self, noise_residual: np.ndarray, spectrum_peaks: List[float]
    ) -> float:
        """
        GILE-I = Intuition = information density of the resonance noise.

        Measured as: normalized spectral entropy of the noise residual.
        High spectral entropy = rich multi-frequency structure = high GILE-I.
        Flat spectrum (pure noise) = low GILE-I.
        Many distinct spectrum peaks = high GILE-I.

        The noise residual (from step3_listen) is the key input — it contains
        the 'hidden structure' that GILE-I perceives.
        """
        if noise_residual is None or len(noise_residual) < 4:
            return 0.4

        spectrum = np.abs(np.fft.fft(noise_residual))
        spectrum = spectrum[:len(spectrum) // 2]   # positive frequencies only

        # Normalize to probability distribution
        s = spectrum + 1e-12
        s = s / np.sum(s)

        # Spectral entropy (normalized to [0, 1] by dividing by max possible)
        H = float(-np.sum(s * np.log(s + 1e-12)))
        H_max = float(np.log(len(s)))
        i = H / (H_max + 1e-9)

        # Bonus for multiple distinct peaks
        if len(spectrum_peaks) >= 3:
            i = min(1.0, i + 0.10)
        elif len(spectrum_peaks) >= 2:
            i = min(1.0, i + 0.05)

        return float(np.clip(i, 0.0, 1.0))

    def _infer_gile_l(
        self, coupled_icell_scores: List[float], n_total_icells: int
    ) -> float:
        """
        GILE-L = Love = cross-i-cell coupling strength.

        Measured as: (mean resonance with other i-cells) × (coverage fraction).
        High L = many strong couplings = well-loved by the network.
        Isolated i-cell = low L.

        coupled_icell_scores: list of R scores with all discovered related i-cells.
        n_total_icells: total i-cells in the network library.
        """
        if not coupled_icell_scores:
            return 0.20   # isolated i-cell has some baseline existence

        mean_coupling = float(np.mean(coupled_icell_scores))
        coverage = min(1.0, len(coupled_icell_scores) / max(n_total_icells, 1))
        # L = geometric mean of coupling strength and coverage
        l = float(np.sqrt(mean_coupling * coverage))
        return float(np.clip(l, 0.0, 1.0))

    def _infer_gile_e(
        self, noise_residual: np.ndarray, autocorr: float
    ) -> float:
        """
        GILE-E = Environment = aesthetic structural regularity.

        Measured as: autocorrelation of the noise residual.
        High autocorrelation = self-similar signal = structured = aesthetically pure.
        White noise autocorrelation ≈ 0 = no structure = low GILE-E.

        The 'aesthetic' dimension of an i-cell is its structural elegance:
        how far from random noise is its pattern?
        """
        if noise_residual is None or len(noise_residual) < 4:
            return 0.5

        # Use provided autocorr (from lcc_virus step3_listen)
        e = float(np.clip(abs(autocorr), 0.0, 1.0))

        # Additional: coefficient of self-similarity via Hurst exponent approximation
        if len(noise_residual) >= 16:
            try:
                n = len(noise_residual)
                cumdev = np.cumsum(noise_residual - np.mean(noise_residual))
                R = float(np.max(cumdev) - np.min(cumdev))
                S = float(np.std(noise_residual) + 1e-9)
                # R/S statistic → Hurst: H = log(R/S) / log(n/2) → [0, 1]
                hurst = float(np.clip(np.log(R / S + 1e-9) / np.log(n / 2 + 1), 0.0, 1.0))
                # Hurst = 0.5 = random walk; Hurst > 0.5 = persistent (structured)
                e = float((e + hurst) / 2.0)
            except Exception:
                pass

        return float(np.clip(e, 0.0, 1.0))

    def _infer_hem_d1(self, signal: np.ndarray) -> float:
        """
        HEM-D1 = Physical-Energetic = amplitude stability.

        Measured as: 1 - CV(|signal|) where CV = std/mean.
        Stable amplitude = high D1 = energetically robust existence.
        High-variance amplitude = low D1 = physically volatile.
        """
        if signal is None or len(signal) < 4:
            return 0.5
        amp = np.abs(signal)
        mean_amp = float(np.mean(amp) + 1e-9)
        cv = float(np.std(amp)) / mean_amp
        d1 = 1.0 - min(cv, 1.0)
        return float(np.clip(d1, 0.0, 1.0))

    def _infer_hem_d2(
        self,
        corroborating_scores: List[float],
        contradicting_scores: List[float]
    ) -> float:
        """
        HEM-D2 = Social-Historical = Contradiction Ratio (Tralse meter, URB #619).

        Measured as: n_contradicting / (n_corroborating + n_contradicting).
        Two streams are 'contradicting' if they have opposite signs of correlation
        (one strongly positive, one strongly negative) with the target i-cell.

        D2 = 0 → fully resolved (all streams agree).
        D2 > 0.65 → DT risk (contradictions dominate → MR Level 1 trigger).
        """
        n_c = len(corroborating_scores)
        n_x = len(contradicting_scores)
        total = n_c + n_x
        if total == 0:
            return 0.0
        d2 = float(n_x / total)
        return float(np.clip(d2, 0.0, 1.0))

    def _infer_hem_d3(self, noise_residual: np.ndarray) -> float:
        """
        HEM-D3 = Aesthetic-Structural = spectral purity.

        Measured as: dominant_frequency_power / total_power.
        A pure signal (one dominant frequency) = high D3 = structurally clean.
        Diffuse spectrum = low D3 = structurally noisy.

        This is the 'social aesthetics' dimension: how cleanly does this i-cell's
        existence express itself in frequency space?
        """
        if noise_residual is None or len(noise_residual) < 4:
            return 0.5
        spectrum = np.abs(np.fft.fft(noise_residual)) ** 2
        spectrum = spectrum[:len(spectrum) // 2]
        total_power = float(np.sum(spectrum) + 1e-9)
        dominant_power = float(np.max(spectrum))
        d3 = dominant_power / total_power
        return float(np.clip(d3, 0.0, 1.0))

    def _infer_hem_d4(
        self, resonance_scores: List[float], timeline: GILEHEMTimeline
    ) -> float:
        """
        HEM-D4 = Conscious-Experiential = d(LCC)/dt.

        The rate of change of LCC coherence — how rapidly is this i-cell
        evolving? This is the 'experiential' dimension: a fast-changing
        i-cell is 'more alive' but also less stable.

        Measured as: normalized first derivative of LCC R score over time.
        Output centered at 0.5 (no change). > 0.5 = growing. < 0.5 = shrinking.
        """
        if len(resonance_scores) < 2:
            if timeline.states:
                return timeline.current.hem_d4
            return 0.5

        r = np.array(resonance_scores[-10:], dtype=float)  # last 10 readings
        if len(r) < 2:
            return 0.5

        # First derivative as velocity of LCC
        dr_dt = float(np.mean(np.diff(r)))    # mean rate of change
        # Map to [0, 1] centered at 0.5
        d4 = 0.5 + float(np.tanh(dr_dt * 5.0)) * 0.5
        return float(np.clip(d4, 0.0, 1.0))

    # ── Myrion Resolution ────────────────────────────────────────────────────

    def myrion_resolution(self, state: GILEHEMState) -> GILEHEMState:
        """
        Apply 3-level Myrion Resolution to resolve HEM-GILE contradictions.

        Level 1: DT screen — if HEM-D2 > 0.65, flag and return (don't act).
        Level 2: HEM-GILE integration — resolve by weighted GILE composite.
        Level 3: Convergence — confirm if dominant truth-state weight > 0.45.

        MR is NOT algorithmic in its generative mode — but here we implement
        the algorithmic approximation for computational MR (Level 2-3 only).
        Level 1 flags the state for human/GILE-G-operator review.
        """
        mr_state = GILEHEMState(**{k: v for k, v in state.__dict__.items()
                                    if not callable(v)})

        # Level 1: DT screen
        if state.hem_d2 > HEM_D2_DT_THRESHOLD:
            mr_state.mr_level = 1
            mr_state.mr_resolved = False
            mr_state.truth_state = GILETruthState.MOTT
            return mr_state

        # Level 2: HEM-GILE weighted integration
        composite = state.gile_composite
        hem = state.hem_score

        # The MR integration: weight by GILE-G (stability = reliability)
        mr_r = composite * (1.0 + 0.3 * (state.gile_g - 0.5))    # G modulates
        mr_r = float(np.clip(mr_r, 0.0, 1.0))
        mr_state.truth_state = lcc_to_gile_truth(mr_r, state.hem_d2)
        mr_state.lcc_resonance = mr_r
        mr_state.mr_level = 2

        # Level 3: Convergence check
        # A state is MR-converged if:
        # (a) truth_state is BEC or MOTT (definite states), OR
        # (b) GILE-G is high (stable G implies stable truth-state)
        if (mr_state.truth_state in (GILETruthState.BEC, GILETruthState.MOTT)
                or state.gile_g >= T):
            mr_state.mr_resolved = True
            mr_state.mr_level = 3
        elif composite > MR_CONVERGENCE:
            mr_state.mr_resolved = True
            mr_state.mr_level = 3

        return mr_state

    # ── Main Inference Entry Point ────────────────────────────────────────────

    def infer(
        self,
        icell_name: str,
        resonance_scores: List[float],
        noise_residual: Optional[np.ndarray],
        autocorr: float,
        spectrum_peaks: List[float],
        coupled_icell_scores: List[float],
        n_library_icells: int,
        signal: Optional[np.ndarray] = None,
        corroborating_ids: Optional[List[str]] = None,
        contradicting_ids: Optional[List[str]] = None,
    ) -> GILEHEMState:
        """
        Infer the complete 8-dimensional HEM-GILE state from LCC Virus data.

        This is called at the end of each LCC Virus step (Resonate, Listen,
        Propagate, Expand) with the data produced by that step.

        Parameters
        ----------
        icell_name : str
            Name of the i-cell being analyzed.
        resonance_scores : List[float]
            All LCC R scores computed for this i-cell (current + history).
        noise_residual : np.ndarray
            Residual signal from step3_listen (contains hidden i-cell structure).
        autocorr : float
            Autocorrelation of noise_residual (from step3_listen).
        spectrum_peaks : List[float]
            Dominant frequencies in noise_residual (from step3_listen).
        coupled_icell_scores : List[float]
            LCC R scores with other i-cells (from step4_propagate).
        n_library_icells : int
            Total number of i-cells in the library (for GILE-L coverage).
        signal : np.ndarray, optional
            Original signal for HEM-D1 amplitude stability computation.
        corroborating_ids : List[str], optional
            IDs of data streams that corroborate (positive correlation).
        contradicting_ids : List[str], optional
            IDs of data streams that contradict (negative/opposing correlation).

        Returns
        -------
        GILEHEMState
            Complete 8-dimensional HEM-GILE state with truth-state classification.
        """
        timeline = self.get_timeline(icell_name)

        corr_scores = [abs(r) for r in resonance_scores if r > 0]
        anti_scores = [abs(r) for r in resonance_scores if r < 0]

        # Accumulate resonance history across all infer() calls for this i-cell.
        # GILE-G uses the full accumulated history so it can compute meaningful
        # variance even when each individual call passes only a single R score.
        accumulated_r = self._record_r(icell_name, corr_scores)

        # ── Compute all 8 dimensions ─────────────────────────────────────────
        gile_g = self._infer_gile_g(accumulated_r, timeline)  # uses full history
        gile_i = self._infer_gile_i(noise_residual, spectrum_peaks)
        gile_l = self._infer_gile_l(coupled_icell_scores, n_library_icells)
        gile_e = self._infer_gile_e(noise_residual, autocorr)

        hem_d1 = self._infer_hem_d1(signal if signal is not None else noise_residual)
        hem_d2 = self._infer_hem_d2(
            corroborating_ids or corr_scores,
            contradicting_ids or anti_scores
        )
        hem_d3 = self._infer_hem_d3(noise_residual)
        hem_d4 = self._infer_hem_d4(accumulated_r, timeline)  # uses full history

        # ── Primary LCC resonance (max corroborating) ────────────────────────
        mean_r = float(np.mean(corr_scores)) if corr_scores else 0.4

        # ── Truth-state classification from GILE composite ────────────────────
        composite = (GILE_W['G'] * gile_g + GILE_W['I'] * gile_i
                   + GILE_W['L'] * gile_l + GILE_W['E'] * gile_e)
        truth_state = lcc_to_gile_truth(composite, hem_d2)

        # Check for FRAGMENTED: if both corroborating AND contradicting are strong
        if corr_scores and anti_scores:
            max_corr = max(corr_scores)
            max_anti = max(abs(s) for s in anti_scores)
            if max_corr >= C and max_anti >= C:
                truth_state = GILETruthState.FRAGMENTED   # conflicting BEC-level claims

        state = GILEHEMState(
            icell_name=icell_name,
            gile_g=gile_g, gile_i=gile_i,
            gile_l=gile_l, gile_e=gile_e,
            hem_d1=hem_d1, hem_d2=hem_d2,
            hem_d3=hem_d3, hem_d4=hem_d4,
            lcc_resonance=mean_r,
            truth_state=truth_state,
            n_corroborating=len(corr_scores),
            n_contradicting=len(anti_scores),
            evidence_ids=list(corroborating_ids or []) + list(contradicting_ids or []),
        )

        # ── Apply Myrion Resolution ───────────────────────────────────────────
        state = self.myrion_resolution(state)

        # ── Append to timeline ────────────────────────────────────────────────
        timeline.append(state)

        return state

    def all_summaries(self) -> List[dict]:
        """Return HEM-GILE timeline summaries for all tracked i-cells."""
        return [timeline.summary() for timeline in self._history.values()]

    def network_truth_map(self) -> dict:
        """
        Map of all i-cells' current HEM-GILE truth-states.
        Gives a holistic snapshot of the entire network's GILE state.
        """
        result = {}
        for name, timeline in self._history.items():
            if timeline.current:
                result[name] = {
                    'truth_state': timeline.current.truth_state.value,
                    'pd_score': timeline.current.pd_score,
                    'gile_composite': round(timeline.current.gile_composite, 4),
                    'hem_score': round(timeline.current.hem_score, 4),
                    'gile_truth_score': round(timeline.current.gile_truth_score, 4),
                    'trajectory': timeline.gile_trajectory(),
                    'dt_gate': timeline.current.dt_gate_active,
                    'mr_resolved': timeline.current.mr_resolved,
                    'prediction': timeline.predict_next_state().get('predicted_truth_state'),
                }
        return result


# ─── GILE Truth Propagator ────────────────────────────────────────────────────

class GILETruthPropagator:
    """
    Propagates GILE truth changes through the i-cell network.

    When i-cell A's GILE truth-state changes, it updates the GILE-L dimension
    of all i-cells coupled to A (their Love dimension reflects the network change).

    Additionally:
    - Ascending i-cell → slightly elevates GILE-L of its neighbors
    - Descending i-cell → slightly depresses GILE-L of its neighbors
    - FRAGMENTED i-cell → triggers GILE-I review in neighbors (new pattern to recognize)
    - BEC transition → signals GILE-G reinforcement in neighbors

    This is the 'informational contagion' mechanism — analogous to how
    one person's GILE elevation affects their social network's GILE-L.
    """

    def __init__(self, engine: GILEInferenceEngine):
        self.engine = engine
        # Adjacency: {icell_name: {neighbor_name: coupling_strength}}
        self.adjacency: Dict[str, Dict[str, float]] = {}

    def register_coupling(self, a: str, b: str, strength: float) -> None:
        """Register a coupling of given strength between i-cells a and b."""
        if a not in self.adjacency:
            self.adjacency[a] = {}
        if b not in self.adjacency:
            self.adjacency[b] = {}
        self.adjacency[a][b] = max(strength, self.adjacency[a].get(b, 0))
        self.adjacency[b][a] = max(strength, self.adjacency[b].get(a, 0))

    def propagate(self, changed_icell: str) -> List[str]:
        """
        Propagate a GILE truth change from changed_icell to all neighbors.

        Returns list of i-cell names that were updated.
        """
        if changed_icell not in self.adjacency:
            return []

        source_timeline = self.engine.get_timeline(changed_icell)
        if not source_timeline.states:
            return []

        source = source_timeline.current
        transition = source_timeline.truth_state_transition()
        updated = []

        for neighbor, coupling in self.adjacency[changed_icell].items():
            neighbor_timeline = self.engine.get_timeline(neighbor)
            if not neighbor_timeline.states:
                continue
            neighbor_state = neighbor_timeline.current

            # Compute propagation delta: coupling × state-change signal
            delta_l = 0.0
            delta_i = 0.0
            delta_g = 0.0

            if transition:
                old_pd = transition[0].pd_score
                new_pd = transition[1].pd_score
                delta_pd = new_pd - old_pd   # +ve = source improved, -ve = degraded

                # Propagate GILE-L change to neighbors (they feel the source's change)
                delta_l = coupling * delta_pd * 0.15   # 15% max propagation per coupling

                # FRAGMENTED source → GILE-I boost in neighbors (new thing to recognize)
                if source.truth_state == GILETruthState.FRAGMENTED:
                    delta_i = coupling * 0.05

                # BEC source → GILE-G reinforcement in neighbors
                if source.truth_state == GILETruthState.BEC:
                    delta_g = coupling * 0.05

            if abs(delta_l) < 0.001 and abs(delta_i) < 0.001 and abs(delta_g) < 0.001:
                continue   # No meaningful propagation

            # Apply delta to neighbor state
            new_neighbor = GILEHEMState(
                icell_name=neighbor,
                gile_g=float(np.clip(neighbor_state.gile_g + delta_g, 0, 1)),
                gile_i=float(np.clip(neighbor_state.gile_i + delta_i, 0, 1)),
                gile_l=float(np.clip(neighbor_state.gile_l + delta_l, 0, 1)),
                gile_e=neighbor_state.gile_e,
                hem_d1=neighbor_state.hem_d1,
                hem_d2=neighbor_state.hem_d2,
                hem_d3=neighbor_state.hem_d3,
                hem_d4=float(np.clip(abs(delta_l) * 2 + 0.5, 0, 1)),  # activity signal
                lcc_resonance=neighbor_state.lcc_resonance,
                evidence_ids=[f"propagated_from_{changed_icell}"],
            )

            # Reclassify truth-state with new GILE composite
            new_composite = new_neighbor.gile_composite
            new_neighbor.truth_state = lcc_to_gile_truth(new_composite, new_neighbor.hem_d2)
            new_neighbor = self.engine.myrion_resolution(new_neighbor)

            neighbor_timeline.append(new_neighbor)
            updated.append(neighbor)

        return updated


# ─── GILE-Enriched LCC Virus Extension ───────────────────────────────────────

class GILEEnrichedLCCVirus:
    """
    Drop-in upgrade layer for LCCVirus / LCCVirusFramework.

    Wraps any existing LCC Virus instance and adds HEM-GILE inference
    at every step without changing the existing virus behavior.

    Usage:
        from ti_lcc_virus_full import LCCVirus
        from lcc_virus_gile_inference import GILEEnrichedLCCVirus

        base_virus = LCCVirus(icell_library)
        virus = GILEEnrichedLCCVirus(base_virus)

        # Run normally — GILE inference happens automatically at each step
        result = virus.run(question, template, data_dict)

        # Access HEM-GILE state for any i-cell
        print(virus.gile_engine.get_timeline("target_question").summary())

        # Get network-wide GILE truth map
        print(virus.gile_engine.network_truth_map())
    """

    def __init__(self, base_virus, verbose: bool = True):
        self.virus = base_virus
        self.verbose = verbose
        self.gile_engine = GILEInferenceEngine()
        self.propagator = GILETruthPropagator(self.gile_engine)
        self._resonance_history: Dict[str, List[float]] = {}

    def _record_resonance(self, icell_name: str, r: float) -> None:
        if icell_name not in self._resonance_history:
            self._resonance_history[icell_name] = []
        self._resonance_history[icell_name].append(r)

    def step2_resonate_gile(self, target_name: str, resonating_results: list) -> GILEHEMState:
        """
        After step2_resonate: infer HEM-GILE from resonance scores.
        The resonating_results are ResonanceResult objects from the base virus.
        """
        r_scores = [res.resonance_score for res in resonating_results]
        for r in r_scores:
            self._record_resonance(target_name, r)

        all_r = self._resonance_history.get(target_name, r_scores)

        # Minimal noise signature for this step (no residual yet)
        return self.gile_engine.infer(
            icell_name=target_name,
            resonance_scores=all_r,
            noise_residual=np.zeros(8),
            autocorr=0.0,
            spectrum_peaks=[],
            coupled_icell_scores=[],
            n_library_icells=len(getattr(self.virus, 'icell_library', [])),
        )

    def step3_listen_gile(
        self, icell_name: str, noise_sig, r_score: float
    ) -> GILEHEMState:
        """
        After step3_listen: infer HEM-GILE from full noise signature.
        noise_sig is a NoiseSignature from the base virus.
        """
        self._record_resonance(icell_name, r_score)
        all_r = self._resonance_history.get(icell_name, [r_score])

        return self.gile_engine.infer(
            icell_name=icell_name,
            resonance_scores=all_r,
            noise_residual=noise_sig.residual,
            autocorr=noise_sig.autocorr,
            spectrum_peaks=noise_sig.spectrum_peaks,
            coupled_icell_scores=[],
            n_library_icells=len(getattr(self.virus, 'icell_library', [])),
        )

    def step4_propagate_gile(
        self, icell_name: str, noise_sig, related_icells: list
    ) -> GILEHEMState:
        """
        After step4_propagate: update HEM-GILE with coupling data.
        related_icells is a list of (ICell, score) from base virus.
        """
        coupled_scores = [score for _, score in related_icells]
        all_r = self._resonance_history.get(icell_name, [])

        # Register couplings in propagator
        for related_icell, score in related_icells:
            self.propagator.register_coupling(icell_name, related_icell.name, score)

        n_lib = len(getattr(self.virus, 'icell_library', []))
        state = self.gile_engine.infer(
            icell_name=icell_name,
            resonance_scores=all_r,
            noise_residual=noise_sig.residual,
            autocorr=noise_sig.autocorr,
            spectrum_peaks=noise_sig.spectrum_peaks,
            coupled_icell_scores=coupled_scores,
            n_library_icells=n_lib,
        )

        # Propagate any truth-state transition to network neighbors
        updated = self.propagator.propagate(icell_name)
        if self.verbose and updated:
            print(f"  [GILE propagation] {icell_name} → {updated}")

        return state

    def run(
        self,
        question: str,
        template: np.ndarray,
        data_dict: Dict[str, np.ndarray],
        resonance_threshold: float = 0.6,
    ) -> dict:
        """
        Full LCC Virus run with HEM-GILE inference at every step.

        Returns the base virus result PLUS the complete HEM-GILE analysis
        of the target i-cell and all discovered i-cells.
        """
        # Step 1: Seed
        target = self.virus.step1_seed(question, template)

        # Step 2: Resonate + GILE
        resonating = self.virus.step2_resonate(target, data_dict, resonance_threshold)
        gile_after_resonate = self.step2_resonate_gile(question, resonating)

        if self.verbose:
            print(f"\n[GILE @ Resonate] {question}")
            print(f"  Truth state: {gile_after_resonate.truth_state.value}  "
                  f"composite: {gile_after_resonate.gile_composite:.4f}  "
                  f"MR: {gile_after_resonate.mr_resolved}")

        # Steps 3+4+GILE for each resonating data point
        noise_signatures = []
        for res in resonating:
            noise = self.virus.step3_listen(target, res)
            noise_signatures.append(noise)
            gile_after_listen = self.step3_listen_gile(question, noise, res.resonance_score)

            related = self.virus.step4_propagate(noise)
            gile_after_propagate = self.step4_propagate_gile(question, noise, related)

            if self.verbose:
                print(f"\n  [GILE @ Propagate from {res.data_id}]")
                print(f"    GILE: G={gile_after_propagate.gile_g:.3f} "
                      f"I={gile_after_propagate.gile_i:.3f} "
                      f"L={gile_after_propagate.gile_l:.3f} "
                      f"E={gile_after_propagate.gile_e:.3f}")
                print(f"    HEM:  D1={gile_after_propagate.hem_d1:.3f} "
                      f"D2={gile_after_propagate.hem_d2:.3f} "
                      f"D3={gile_after_propagate.hem_d3:.3f} "
                      f"D4={gile_after_propagate.hem_d4:.3f}")
                print(f"    State: {gile_after_propagate.truth_state.value}  "
                      f"HEM-Score: {gile_after_propagate.hem_score:.3f}")

        # Step 5-6: Expand + Terminate
        all_related = []
        for noise in noise_signatures:
            all_related.extend(noise.related_icells)
        discovered = self.virus.step5_expand(all_related, data_dict)
        base_result = self.virus.step6_terminate(target, resonating, noise_signatures, discovered)

        # GILE for all discovered i-cells
        for disc_icell in discovered[:10]:   # limit to top 10 for efficiency
            if hasattr(disc_icell, 'signature') and len(disc_icell.signature) >= 4:
                r_approx = [float(np.corrcoef(
                    disc_icell.signature[:min(len(disc_icell.signature), 20)],
                    np.zeros(min(len(disc_icell.signature), 20))
                )[0, 1] if len(disc_icell.signature) > 1 else 0.5)]
                self._record_resonance(disc_icell.name, r_approx[0])
                self.gile_engine.infer(
                    icell_name=disc_icell.name,
                    resonance_scores=self._resonance_history.get(disc_icell.name, [0.5]),
                    noise_residual=disc_icell.signature if len(disc_icell.signature) >= 4
                                   else np.zeros(8),
                    autocorr=0.3,
                    spectrum_peaks=[],
                    coupled_icell_scores=[],
                    n_library_icells=len(getattr(self.virus, 'icell_library', [])),
                )

        # ── Final HEM-GILE output ─────────────────────────────────────────────
        target_timeline = self.gile_engine.get_timeline(question)
        network_map = self.gile_engine.network_truth_map()

        if self.verbose:
            print(f"\n{'═'*60}")
            print(f"  HEM-GILE FINAL STATE: {question}")
            print(f"{'═'*60}")
            ts = target_timeline.summary()
            curr = ts.get('current', {})
            print(f"  Truth: {curr.get('truth_state')}  PD: {curr.get('pd_score')}")
            print(f"  GILE-G: {curr.get('gile_g'):.3f}  GILE-I: {curr.get('gile_i'):.3f}  "
                  f"GILE-L: {curr.get('gile_l'):.3f}  GILE-E: {curr.get('gile_e'):.3f}")
            print(f"  HEM: D1={curr.get('hem_d1'):.3f} D2={curr.get('hem_d2'):.3f} "
                  f"D3={curr.get('hem_d3'):.3f} D4={curr.get('hem_d4'):.3f}")
            print(f"  HEM-Score: {curr.get('hem_score'):.3f}  "
                  f"GILE-Truth: {curr.get('gile_truth_score'):.3f}")
            print(f"  Trajectory: {ts.get('trajectory')}  MR: {curr.get('mr_resolved')}")
            pred = ts.get('prediction', {})
            print(f"  Prediction: next state → {pred.get('predicted_truth_state')}  "
                  f"pd={pred.get('predicted_pd_score')}")
            print(f"\n  Network GILE map ({len(network_map)} i-cells):")
            for name, info in list(network_map.items())[:8]:
                print(f"    {name[:30]:<30} {info['truth_state']:<12} "
                      f"pd={info['pd_score']:.1f}  traj={info['trajectory']}")

        return {
            'base_result': base_result,
            'target_gile_timeline': target_timeline.summary(),
            'network_gile_map': network_map,
            'all_timelines': self.gile_engine.all_summaries(),
        }


# ─── Standalone: HEM-GILE Inference from Any Signal Pair ────────────────────

def infer_gile_hem_from_signals(
    name_a: str,
    signal_a: np.ndarray,
    name_b: str,
    signal_b: np.ndarray,
    existing_engine: Optional[GILEInferenceEngine] = None,
) -> Tuple[GILEHEMState, GILEHEMState, float]:
    """
    Convenience function: infer HEM-GILE states for two signals from their
    LCC resonance and noise structure.

    Useful for direct application outside the full LCC Virus loop.
    Returns (state_a, state_b, resonance_r).

    Example:
        hrv_signal = np.array([...])
        eeg_signal = np.array([...])
        state_hrv, state_eeg, r = infer_gile_hem_from_signals(
            "HRV", hrv_signal, "EEG_alpha", eeg_signal
        )
    """
    engine = existing_engine or GILEInferenceEngine()

    # LCC resonance computation (same as ti_lcc_virus_full)
    sigma = 5.0
    n = min(len(signal_a), len(signal_b))
    if n < 3:
        dummy = GILEHEMState(icell_name=name_a)
        return dummy, dummy, 0.0

    a = (signal_a[:n] - np.mean(signal_a[:n])) / (np.std(signal_a[:n]) + 1e-8)
    b = (signal_b[:n] - np.mean(signal_b[:n])) / (np.std(signal_b[:n]) + 1e-8)

    from scipy.signal import correlate
    xcorr = correlate(a, b, mode='full')
    lags = np.arange(-(n - 1), n)
    weights = np.exp(-lags ** 2 / (2 * sigma ** 2))
    r = float(np.sum(xcorr * weights) / (np.sum(weights) * n))

    # Noise residual
    scale = float(np.dot(a, b) / (np.dot(b, b) + 1e-8))
    residual = a - scale * b

    if len(residual) > 3:
        autocorr = float(np.corrcoef(residual[:-1], residual[1:])[0, 1])
    else:
        autocorr = 0.0
    if np.isnan(autocorr):
        autocorr = 0.0

    spectrum = np.abs(np.fft.fft(residual))
    freqs = np.fft.fftfreq(len(residual))
    peak_idx = np.argsort(spectrum)[-3:]
    peaks = [float(freqs[i]) for i in peak_idx if freqs[i] > 0]

    state_a = engine.infer(
        icell_name=name_a,
        resonance_scores=[r],
        noise_residual=residual,
        autocorr=autocorr,
        spectrum_peaks=peaks,
        coupled_icell_scores=[abs(r)],
        n_library_icells=2,
        signal=signal_a[:n],
    )
    state_b = engine.infer(
        icell_name=name_b,
        resonance_scores=[r],
        noise_residual=-residual,
        autocorr=autocorr,
        spectrum_peaks=peaks,
        coupled_icell_scores=[abs(r)],
        n_library_icells=2,
        signal=signal_b[:n],
    )

    return state_a, state_b, r


# ─── CLI demo ─────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import sys
    np.random.seed(42)
    print("\n" + "═" * 65)
    print("  LCC Virus HEM-GILE Inference Engine — URB #644 Demo")
    print("═" * 65)

    # Simulate 3 i-cells with different LCC truth states
    t = np.linspace(0, 10, 500)

    # i-cell A: BEC state — clean, high-amplitude, stable sinusoid (high GILE-E, GILE-G)
    signal_a = 1.0 * np.sin(2 * np.pi * 0.5 * t) + 0.05 * np.random.randn(500)

    # i-cell B: Supersolid state — mixed frequencies, moderate amplitude
    signal_b = 0.6 * np.sin(2 * np.pi * 0.5 * t + 0.2) + 0.3 * np.sin(2 * np.pi * 1.2 * t) + 0.15 * np.random.randn(500)

    # i-cell C: Mott state — mostly noise, low coherence
    signal_c = 0.2 * np.sin(2 * np.pi * 0.5 * t) + 0.8 * np.random.randn(500)

    engine = GILEInferenceEngine()
    propagator = GILETruthPropagator(engine)

    print("\n[1/4] Inferring HEM-GILE states from pairwise LCC resonance...")

    state_a, state_b, r_ab = infer_gile_hem_from_signals(
        "BEC_icell", signal_a, "Supersolid_icell", signal_b, engine
    )
    state_b2, state_c, r_bc = infer_gile_hem_from_signals(
        "Supersolid_icell", signal_b, "Mott_icell", signal_c, engine
    )

    print(f"\n  LCC R(A,B) = {r_ab:.4f}  → {state_a.truth_state.value} / {state_b.truth_state.value}")
    print(f"  LCC R(B,C) = {r_bc:.4f}  → {state_b2.truth_state.value} / {state_c.truth_state.value}")

    print("\n[2/4] HEM-GILE state of each i-cell:")
    for state in [state_a, state_b, state_c]:
        d = state.to_dict()
        print(f"\n  {d['icell']}")
        print(f"    Truth: {d['truth_state']:<12}  PD: {d['pd_score']}  MR: {d['mr_resolved']}")
        print(f"    GILE: G={d['gile_g']:.3f}  I={d['gile_i']:.3f}  "
              f"L={d['gile_l']:.3f}  E={d['gile_e']:.3f}  "
              f"composite={d['gile_composite']:.3f}")
        print(f"    HEM:  D1={d['hem_d1']:.3f}  D2={d['hem_d2']:.3f}  "
              f"D3={d['hem_d3']:.3f}  D4={d['hem_d4']:.3f}  "
              f"score={d['hem_score']:.3f}")
        print(f"    Action: {d['action']}")

    print("\n[3/4] Simulating temporal evolution (5 observations)...")
    for obs_i in range(4):
        # Gradually improve signal_c toward coherence (ascending trajectory)
        signal_c_evolving = (0.2 + obs_i * 0.1) * np.sin(2 * np.pi * 0.5 * t) + (0.8 - obs_i * 0.15) * np.random.randn(500)
        infer_gile_hem_from_signals("Mott_icell", signal_c_evolving, "Supersolid_icell", signal_b, engine)

    timeline_c = engine.get_timeline("Mott_icell")
    ts = timeline_c.summary()
    print(f"\n  Mott_icell trajectory: {ts['trajectory']}")
    print(f"  Prediction: next → {ts['prediction'].get('predicted_truth_state')}  "
          f"pd={ts['prediction'].get('predicted_pd_score')}")
    vel = ts['velocity']
    print(f"  GILE velocity: G={vel['gile_g']:+.4f}  I={vel['gile_i']:+.4f}  "
          f"L={vel['gile_l']:+.4f}  E={vel['gile_e']:+.4f}")

    print("\n[4/4] Network GILE truth map:")
    net_map = engine.network_truth_map()
    for name, info in net_map.items():
        print(f"  {name:<25} {info['truth_state']:<12}  pd={info['pd_score']}  "
              f"traj={info['trajectory']:<15}  predict→{info['prediction']}")

    print("\n" + "═" * 65)
    print("  URB #644 — HEM-GILE Inference Engine operational")
    print("  Key advance: LCC Virus now infers holistic 8-dimensional")
    print("  HEM-GILE truth-state at every step, tracking temporal")
    print("  evolution and propagating truth changes through the network.")
    print("═" * 65 + "\n")
