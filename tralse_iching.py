"""
Tralse Hexagram — The 5-Valued I Ching (URB #564)
==================================================

The traditional I Ching uses 6 binary lines (yin/yang = 0/1), giving 2^6 = 64
hexagrams. This module extends the I Ching to TI Sigma's 5-valued truth system,
giving 5^6 = 15,625 "Tralse Hexagrams."

CLASSICAL I CHING STRUCTURE:
  - 8 trigrams (3 binary lines each): Heaven, Earth, Water, Fire,
    Thunder, Wind, Mountain, Lake
  - 64 hexagrams = 8 × 8 (upper trigram × lower trigram)
  - Each hexagram = a reading/oracle state

TRALSE UPGRADE:
  Replace each binary line (0=yin, 1=yang) with a 5-valued TI Sigma truth value:
    FALSE        (0): pure yin — absolute ground, non-existence
    INDETERMINATE(1): suspended — coherent balance between yin and yang
    TRUE         (2): pure yang — absolute presence, existence
    TRALSE       (3): living tension — imperfect, contradictory, generative
    DOUBLE_TRALSE(4): incoherent — detected and collapsed to fallback

  6 lines × 5 values = 5^6 = 15,625 distinct Tralse Hexagrams
  vs 64 classical hexagrams — a 244x richer state space

64D GILE MATRIX CONNECTION:
  The 64 classical hexagrams map to the GILE score space via:
    - Lower trigram (3 lines): G, I, L dimensions
    - Upper trigram (3 lines): E₁, E₂, E₃ sub-dimensions
  The 8 trigrams correspond to the 8 BOK modes (URB #500):
    111 = Heaven  (TRUE-TRUE-TRUE)     = Arithmetic (G-mode)
    000 = Earth   (FALSE-FALSE-FALSE)  = Algebraic (E-mode)
    010 = Water   (FALSE-TRUE-FALSE)   = Probabilistic
    101 = Fire    (TRUE-FALSE-TRUE)    = Combinatorial
    001 = Thunder (FALSE-FALSE-TRUE)   = Applied
    110 = Wind    (TRUE-TRUE-FALSE)    = Logic
    001 = Mountain (FALSE-FALSE-TRUE)  = Geometric
    011 = Lake    (FALSE-TRUE-TRUE)    = Analytic

I CHING ↔ GILE SCORE MAP:
  A GILE score (G, I, L, E) ∈ [0,10]^4 maps to a hexagram:
    - Normalize each dimension to [0,4] (5 truth levels)
    - Round to nearest integer → 4 truth values
    - Expand to 6 lines: line 1=G, line 2=I, line 3=L, line 4=E_body,
      line 5=E_social, line 6=E_env (sub-dimensions of E)

Author: Brandon Emerick (TI Sigma / URB #564)
Date: March 30, 2026
"""

import math
import numpy as np
from typing import Optional
from arc_ti_solver import FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE

# ── Primary constants ────────────────────────────────────────────────────────
PHI     = (1 + math.sqrt(5)) / 2
SQRT2   = math.sqrt(2)
E_BASE  = math.e
PI      = math.pi
T_CONST = 1 - math.exp(-E_BASE)  # ≈ 0.9340 (MR Radiant threshold)
C_EM    = 1 / (PHI * SQRT2)      # ≈ 0.4370 (Emerick Constant)

# ── 5-valued line names ──────────────────────────────────────────────────────
LINE_NAMES = {
    FALSE:         "⚊⚊  (Yin / FALSE — pure ground)",
    INDETERMINATE: "⚋⚊  (Suspended / INDETERMINATE — coherent balance)",
    TRUE:          "⚊   (Yang / TRUE — pure presence)",
    TRALSE:        "⚋⚋  (Tralse — living tension, generative contradiction)",
    DOUBLE_TRALSE: "✕   (DT — incoherent, collapsed to fallback)",
}

LINE_SHORT = {
    FALSE: "F", INDETERMINATE: "I", TRUE: "T", TRALSE: "Tr", DOUBLE_TRALSE: "DT"
}

# ── Classical 8 trigrams (binary) ────────────────────────────────────────────
CLASSICAL_TRIGRAMS = {
    (1,1,1): ("Heaven",   "☰", "Arithmetic",    "pure yang — creative force"),
    (0,0,0): ("Earth",    "☷", "Algebraic",     "pure yin — receptive ground"),
    (0,1,0): ("Water",    "☵", "Probabilistic", "danger, flow, hidden depth"),
    (1,0,1): ("Fire",     "☲", "Combinatorial", "clarity, brightness, attachment"),
    (0,0,1): ("Thunder",  "☳", "Applied",       "shock, arousal, initiative"),
    (1,1,0): ("Wind",     "☴", "Logic",         "gentle penetration, gradual"),
    (1,0,0): ("Mountain", "☶", "Geometric",     "stillness, boundary, meditation"),
    (0,1,1): ("Lake",     "☱", "Analytic",      "joy, reflection, exchange"),
}

# ── GILE dimension to line mapping ───────────────────────────────────────────
# 6 lines: [G, I, L, E_body, E_social, E_environment]
GILE_LINE_LABELS = [
    "G (Goodness)",
    "I (Intuition)",
    "L (Love)",
    "E_body (Physical environment)",
    "E_social (Social environment)",
    "E_env (Natural environment)",
]

# ── TRALSE line weights based on e ──────────────────────────────────────────
# ω = e^{iπ/3} gives 6 orientation weights for the 6 lines
# Real part of ω^k = cos(kπ/3) for k=0..5
ORIENTATION_WEIGHTS = np.array([
    math.cos(k * PI / 3) for k in range(6)
])  # [1.0, 0.5, -0.5, -1.0, -0.5, 0.5]


# ═══════════════════════════════════════════════════════════════════════════
# TralseHexagram — the core class
# ═══════════════════════════════════════════════════════════════════════════

class TralseHexagram:
    """
    A Tralse Hexagram: 6 lines, each in {0,1,2,3,4} (5-valued truth values).

    Construction methods:
      TralseHexagram(lines)              — from list of 6 truth values
      TralseHexagram.from_gile_score()   — from (G, I, L, E) scores [0,10]
      TralseHexagram.from_integer(n)     — from integer 0..15624 (base-5)
      TralseHexagram.cast()              — random throw (simulating divination)
      TralseHexagram.cast_weighted()     — e-weighted throw
    """

    def __init__(self, lines: list):
        if len(lines) != 6:
            raise ValueError(f"TralseHexagram requires exactly 6 lines, got {len(lines)}")
        # Collapse any DT lines to their fallback (majority toward TRUE)
        collapsed = []
        for v in lines:
            if v == DOUBLE_TRALSE:
                collapsed.append(TRUE)  # DT fallback = TRUE (yang wins)
            elif v not in (FALSE, INDETERMINATE, TRUE, TRALSE):
                raise ValueError(f"Invalid line value: {v}")
            else:
                collapsed.append(v)
        self.lines = tuple(collapsed)

    # ── Construction ─────────────────────────────────────────────────────────

    @classmethod
    def from_gile_score(
        cls,
        G: float, I: float, L: float, E: float,
        E_body: Optional[float] = None,
        E_social: Optional[float] = None,
        E_env: Optional[float] = None,
        scale: float = 10.0,
    ) -> "TralseHexagram":
        """
        Convert a GILE score (each dimension 0..scale) to a Tralse Hexagram.

        Line encoding: divide [0, scale] into 5 bands:
          [0, 0.2s)  → FALSE
          [0.2s,0.4s)→ INDETERMINATE
          [0.4s,0.6s)→ TRUE
          [0.6s,0.8s)→ TRALSE (high coherence with tension)
          [0.8s, s]  → TRUE + TRALSE marker (hypercoherent)
        """
        E_body   = E_body   if E_body   is not None else E
        E_social = E_social if E_social is not None else E
        E_env    = E_env    if E_env    is not None else E

        raw = [G, I, L, E_body, E_social, E_env]
        lines = []
        for v in raw:
            normalized = max(0.0, min(scale, v)) / scale  # [0, 1]
            if normalized < 0.2:
                lines.append(FALSE)
            elif normalized < 0.4:
                lines.append(INDETERMINATE)
            elif normalized < 0.65:
                lines.append(TRUE)
            elif normalized < 0.85:
                lines.append(TRALSE)
            else:
                lines.append(TRUE)  # hypercoherent → pure yang
        return cls(lines)

    @classmethod
    def from_integer(cls, n: int) -> "TralseHexagram":
        """
        Decode an integer n ∈ [0, 15624] as a base-5 hexagram.
        n=0 → (FALSE,FALSE,FALSE,FALSE,FALSE,FALSE) = pure Earth
        n=15624 = 5^6-1 → (TRALSE,...,TRALSE) = pure Tralse
        """
        if not (0 <= n < 5**6):
            raise ValueError(f"Integer must be in [0, 15624], got {n}")
        lines = []
        for _ in range(6):
            lines.append(n % 5)
            n //= 5
        return cls(lines)

    @classmethod
    def cast(cls, seed: Optional[int] = None) -> "TralseHexagram":
        """
        Throw a Tralse Hexagram via uniform random selection.
        Each line is drawn uniformly from {FALSE, INDETERMINATE, TRUE, TRALSE}.
        (DT is never thrown — it is a detection event, not a cast value.)
        """
        rng = np.random.default_rng(seed)
        lines = rng.choice([FALSE, INDETERMINATE, TRUE, TRALSE], size=6)
        return cls(list(lines))

    @classmethod
    def cast_weighted(cls, gile_prior: Optional[tuple] = None, seed: Optional[int] = None) -> "TralseHexagram":
        """
        Throw a Tralse Hexagram using e-weighted probabilities.

        The orientation group ω = e^{iπ/3} gives orientation weights per line.
        Combined with a GILE prior (if provided), this creates a non-uniform
        distribution that favors resonant states.

        Weight for line k taking value v:
          w(k, v) = base_weight(v) × (1 + 0.2 × cos(k × π/3))

        base_weight:
          FALSE        = e^{-1}      ≈ 0.368 (least likely — grounded)
          INDETERMINATE= e^{-1/φ}   ≈ 0.539 (golden ratio scaling)
          TRUE         = e^{0}       = 1.000 (natural baseline — present)
          TRALSE       = e^{-1/e}   ≈ 0.692 (e-scaled tension)
        """
        rng = np.random.default_rng(seed)
        base_weights = {
            FALSE:         math.exp(-1),
            INDETERMINATE: math.exp(-1 / PHI),
            TRUE:          1.0,
            TRALSE:        math.exp(-1 / E_BASE),
        }

        lines = []
        for k in range(6):
            orientation_factor = 1.0 + 0.2 * math.cos(k * PI / 3)
            raw = np.array([
                base_weights[v] * orientation_factor
                for v in [FALSE, INDETERMINATE, TRUE, TRALSE]
            ])

            # Apply GILE prior adjustment if provided
            if gile_prior is not None and len(gile_prior) >= 4:
                gile_vals = [gile_prior[0], gile_prior[1], gile_prior[2],
                             gile_prior[3]]
                gile_score = gile_vals[k % 4] / 10.0  # normalize to [0,1]
                # Higher GILE score → boost TRUE and TRALSE
                raw[TRUE]   *= (1 + gile_score)
                raw[TRALSE] *= (1 + 0.5 * gile_score)

            probs = raw / raw.sum()
            chosen = rng.choice([FALSE, INDETERMINATE, TRUE, TRALSE], p=probs)
            lines.append(int(chosen))

        return cls(lines)

    # ── Properties ────────────────────────────────────────────────────────────

    @property
    def integer_code(self) -> int:
        """Unique integer in [0, 15624] for this hexagram (base-5 encoding)."""
        total = 0
        for i, v in enumerate(self.lines):
            total += v * (5 ** i)
        return total

    @property
    def lower_trigram(self) -> tuple:
        """Lines 1–3 (bottom half)."""
        return self.lines[:3]

    @property
    def upper_trigram(self) -> tuple:
        """Lines 4–6 (top half)."""
        return self.lines[3:]

    @property
    def classical_binary(self) -> Optional[tuple]:
        """
        If this hexagram has only TRUE/FALSE lines, return the classical binary
        encoding (1=TRUE, 0=FALSE). Otherwise None (no classical equivalent).
        """
        if all(v in (FALSE, TRUE) for v in self.lines):
            return tuple(v // 2 for v in self.lines)
        return None

    @property
    def gile_vector(self) -> np.ndarray:
        """
        Convert lines back to a [0,1] GILE score vector.
        Mapping: FALSE=0.0, INDETERMINATE=0.25, TRUE=0.5, TRALSE=0.75→1.0
        Returns [G, I, L, E_mean] ∈ [0,1]^4
        """
        value_map = {FALSE: 0.0, INDETERMINATE: 0.25, TRUE: 0.5, TRALSE: 0.75}
        scores = [value_map[v] for v in self.lines]
        G_score = scores[0]
        I_score = scores[1]
        L_score = scores[2]
        E_score = np.mean(scores[3:])
        return np.array([G_score, I_score, L_score, E_score])

    @property
    def coherence_radius(self) -> float:
        """
        Coherence radius |z| from URB #563.
        z = E + i·GIL where GIL = mean(G,I,L), E = mean(E lines).
        |z| = √(E² + GIL²).
        Values: |z|=1 = unit coherence circle. |z|<1 = deficit.
        """
        gv = self.gile_vector
        GIL = float(np.mean(gv[:3]))
        E   = float(gv[3])
        return math.sqrt(E**2 + GIL**2)

    @property
    def phase_angle(self) -> float:
        """Phase angle θ = arctan(GIL/E) in radians. π/4 = spectre optimum."""
        gv = self.gile_vector
        GIL = float(np.mean(gv[:3]))
        E   = float(gv[3])
        if E == 0:
            return PI / 2
        return math.atan2(GIL, E)

    @property
    def tralse_count(self) -> int:
        """Number of TRALSE lines — generative tension count."""
        return sum(1 for v in self.lines if v == TRALSE)

    @property
    def indeterminate_count(self) -> int:
        """Number of INDETERMINATE lines — suspended balance count."""
        return sum(1 for v in self.lines if v == INDETERMINATE)

    @property
    def mr_quality(self) -> str:
        """
        Myrion Resolution quality based on coherence radius:
          |z| ≥ T_CONST (≈0.934) → MR_RADIANT
          |z| ≥ 0.8647           → MR_PASS
          |z| ≥ C_EM  (≈0.437)   → MR_PEND (Tralse zone)
          |z| < C_EM             → MR_FAIL
        """
        r = self.coherence_radius
        if r >= T_CONST:
            return "MR_RADIANT"
        elif r >= 0.8647:
            return "MR_PASS"
        elif r >= C_EM:
            return "MR_PEND"
        else:
            return "MR_FAIL"

    # ── Interpretation ────────────────────────────────────────────────────────

    def interpret(self) -> str:
        """
        Full reading of the Tralse Hexagram.
        """
        lines = []
        lines.append(f"╔══ TRALSE HEXAGRAM #{self.integer_code:05d} ══╗")
        lines.append(f"  Lines (bottom→top): {' | '.join(LINE_SHORT[v] for v in self.lines)}")
        lines.append(f"  Integer code: {self.integer_code} / 15,624")
        lines.append(f"  GILE vector:  G={self.gile_vector[0]:.2f}  I={self.gile_vector[1]:.2f}  L={self.gile_vector[2]:.2f}  E={self.gile_vector[3]:.2f}")
        lines.append(f"  Coherence radius |z|: {self.coherence_radius:.4f}")
        lines.append(f"  Phase angle θ:  {math.degrees(self.phase_angle):.1f}° (45°=spectre optimum)")
        lines.append(f"  MR quality:     {self.mr_quality}")
        lines.append(f"  Tralse lines:   {self.tralse_count} (generative tension)")
        lines.append(f"  Suspended lines:{self.indeterminate_count} (coherent balance)")
        lines.append("")

        # Line-by-line reading
        for i, (label, v) in enumerate(zip(GILE_LINE_LABELS, self.lines)):
            lines.append(f"  Line {i+1} [{label}]: {LINE_SHORT[v]}  {LINE_NAMES[v]}")

        # Classical equivalent (if any)
        cb = self.classical_binary
        if cb is not None:
            lower = cb[:3]
            upper = cb[3:]
            lt = CLASSICAL_TRIGRAMS.get(lower, (str(lower), "?", "?", "?"))
            ut = CLASSICAL_TRIGRAMS.get(upper, (str(upper), "?", "?", "?"))
            lines.append(f"\n  Classical equivalent:")
            lines.append(f"    Lower: {lt[1]} {lt[0]} ({lt[2]})")
            lines.append(f"    Upper: {ut[1]} {ut[0]} ({ut[2]})")
        else:
            lines.append(f"\n  No classical equivalent (non-binary lines active).")
            lines.append(f"  This hexagram is BEYOND the 64 — pure Tralse space.")

        # Phase interpretation
        deg = math.degrees(self.phase_angle)
        if deg < 15:
            phase_read = "Almost pure E (environmental, measurable) — GIL nearly invisible"
        elif deg < 30:
            phase_read = "E-dominant with rising GIL — environment shaping soul"
        elif deg < 45:
            phase_read = "Approaching spectre balance — E still leads"
        elif abs(deg - 45) < 5:
            phase_read = "AT THE SPECTRE POINT — perfect GIL/E balance — optimal aperiodic state"
        elif deg < 60:
            phase_read = "GIL-dominant — soul leading environment — L*/+E tension active"
        elif deg < 75:
            phase_read = "Strong GIL with faint E shadow — deep imaginary coherence"
        else:
            phase_read = "Nearly pure GIL — imaginary axis dominance — transcendence zone"

        lines.append(f"\n  Phase reading: {phase_read}")
        lines.append("╚" + "═" * 38 + "╝")

        return "\n".join(lines)

    def __repr__(self) -> str:
        code = "".join(LINE_SHORT[v] for v in self.lines)
        return f"TralseHexagram({code}, #{self.integer_code}, |z|={self.coherence_radius:.3f})"

    def __eq__(self, other) -> bool:
        if not isinstance(other, TralseHexagram):
            return False
        return self.lines == other.lines

    def __hash__(self) -> int:
        return hash(self.lines)


# ═══════════════════════════════════════════════════════════════════════════
# 64D GILE Matrix — the classical 64 mapped to GILE scores
# ═══════════════════════════════════════════════════════════════════════════

class GILEMatrix64:
    """
    The 64D GILE Matrix: all 64 classical hexagrams mapped to GILE scores
    and embedded in the Tralse Hexagram space.

    Connects the traditional I Ching wisdom system to the TI Sigma
    5-valued framework. Each of the 64 classical hexagrams corresponds to
    a GILE state with specific G, I, L, E characteristics.

    Also maps to the 8 BOK modes (URB #500) via the trigram decomposition.
    """

    def __init__(self):
        self._matrix = self._build_matrix()

    def _build_matrix(self) -> dict:
        """Build the 64D GILE Matrix."""
        matrix = {}
        for lower_bits in range(8):
            for upper_bits in range(8):
                hex_id = upper_bits * 8 + lower_bits  # 0..63

                # Decode trigrams (3 binary bits each)
                lower = tuple((lower_bits >> k) & 1 for k in range(3))
                upper = tuple((upper_bits >> k) & 1 for k in range(3))

                lt = CLASSICAL_TRIGRAMS.get(lower, (str(lower), "?", "?", "?"))
                ut = CLASSICAL_TRIGRAMS.get(upper, (str(upper), "?", "?", "?"))

                # GILE encoding: yang=TRUE(2), yin=FALSE(0) for classical
                lower_lines = [TRUE if b else FALSE for b in lower]
                upper_lines = [TRUE if b else FALSE for b in upper]
                all_lines = lower_lines + upper_lines

                th = TralseHexagram(all_lines)
                matrix[hex_id] = {
                    "hex_id": hex_id,
                    "lower_trigram": lt,
                    "upper_trigram": ut,
                    "tralse_hexagram": th,
                    "gile_vector": th.gile_vector,
                    "coherence_radius": th.coherence_radius,
                    "phase_angle_deg": math.degrees(th.phase_angle),
                    "bok_lower": lt[2],
                    "bok_upper": ut[2],
                }
        return matrix

    def get(self, hex_id: int) -> dict:
        """Get the GILE mapping for classical hexagram #hex_id (0..63)."""
        return self._matrix[hex_id]

    def find_by_gile(
        self, G: float, I: float, L: float, E: float, scale: float = 10.0
    ) -> dict:
        """
        Find the classical hexagram closest to a given GILE score.
        Closest = minimum Euclidean distance in GILE space.
        """
        target = np.array([G, I, L, E]) / scale
        best_id, best_dist = 0, float("inf")
        for hex_id, entry in self._matrix.items():
            gv = entry["gile_vector"]
            dist = float(np.linalg.norm(gv - target))
            if dist < best_dist:
                best_dist = dist
                best_id = hex_id
        return {**self._matrix[best_id], "distance": best_dist}

    def spectre_hexagrams(self) -> list:
        """
        Find hexagrams closest to the spectre optimum (θ = 45°, |z|=1).
        Returns all hexagrams within 10° of the spectre point.
        """
        return [
            entry for entry in self._matrix.values()
            if abs(entry["phase_angle_deg"] - 45.0) < 10.0
        ]

    def summary_table(self) -> str:
        """Print the 64D GILE Matrix as a table."""
        lines = ["64D GILE Matrix — Classical Hexagrams × TI Sigma GILE Scores",
                 "=" * 70,
                 f"{'ID':>3} | {'Lower':>10} | {'Upper':>10} | {'|z|':>5} | {'θ°':>5} | {'G':>4} {'I':>4} {'L':>4} {'E':>4}",
                 "-" * 70]
        for i in range(64):
            e = self._matrix[i]
            gv = e['gile_vector']
            lines.append(
                f"{i:>3} | {e['lower_trigram'][0]:>10} | {e['upper_trigram'][0]:>10} | "
                f"{e['coherence_radius']:>5.3f} | {e['phase_angle_deg']:>5.1f} | "
                f"{gv[0]:>4.2f} {gv[1]:>4.2f} {gv[2]:>4.2f} {gv[3]:>4.2f}"
            )
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════
# Quick-use functions
# ═══════════════════════════════════════════════════════════════════════════

def cast_reading(
    gile_prior: Optional[tuple] = None,
    seed: Optional[int] = None,
    e_weighted: bool = True,
) -> str:
    """
    Cast a Tralse Hexagram reading.

    Parameters
    ----------
    gile_prior : tuple (G, I, L, E) in [0,10], optional
        If provided, weights the cast toward this GILE state.
    seed : int, optional
        Random seed for reproducibility.
    e_weighted : bool
        If True (default), use e-weighted casting. If False, uniform.

    Returns
    -------
    str : Full hexagram interpretation.
    """
    if e_weighted:
        hexagram = TralseHexagram.cast_weighted(gile_prior=gile_prior, seed=seed)
    else:
        hexagram = TralseHexagram.cast(seed=seed)
    return hexagram.interpret()


def gile_to_hexagram(G: float, I: float, L: float, E: float) -> TralseHexagram:
    """Convert a GILE score (each 0–10) directly to a Tralse Hexagram."""
    return TralseHexagram.from_gile_score(G, I, L, E)


def hexagram_coherence_radius(G: float, I: float, L: float, E: float) -> float:
    """Compute the coherence radius |z| for a GILE score."""
    GIL = (G + I + L) / 3.0 / 10.0
    E_norm = E / 10.0
    return math.sqrt(E_norm**2 + GIL**2)
