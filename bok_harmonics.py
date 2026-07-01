"""
BOK Harmonics — 8 HEM-GILE Dimensions as Musical Notes
========================================================
URB #648 — Brandon Emerick | TI Sigma Research | April 2026

Each of the 8 BOK dimensions is assigned a musical note.
When dimensions are simultaneously activated past the C_TI threshold (≈0.437),
they form CHORDS — abstract or composite GILE-LCC resonances.

DIMENSION → NOTE MAPPING (chosen for harmonic TI logic):
  GILE-G (Goodness):        C4  = 261.63 Hz   — root/foundation
  GILE-I (Intuition):       E4  = 329.63 Hz   — major third (φ-related 5/4)
  GILE-L (Love):            G4  = 392.00 Hz   — perfect fifth (pure harmony)
  GILE-E (Aesthetics):      B4  = 493.88 Hz   — major seventh (elevated beauty)
  HEM-D1 (Physical):        D4  = 293.66 Hz   — major second (grounded existence)
  HEM-D2 (Contradiction):   F4  = 349.23 Hz   — tritone from G (Tralse tension)
  HEM-D3 (Spectral):        A4  = 440.00 Hz   — major sixth (clarity/purity)
  HEM-D4 (Velocity):        C5  = 523.25 Hz   — octave (transcendence/change rate)

THRESHOLD LADDER (from URBs #612–#615):
  > ET  (0.4142): note activates (visible, faint tone)
  > C_TI(0.4370): note enters chord pool (fully sounding)
  > 0.65:         note is "strong" (louder, brighter)
  > T  (0.9340):  note is BEC-active (full glow, dominant)

NAMED CHORDS — from simplest to most complex:
  Two dimensions:
    G+L          → "G-L Bond"          — Abstract GILE Love (perfect fifth dyad)
    G+E          → "G-E Coherence"     — Goodness-Aesthetics
    I+L          → "I-L Resonance"     — Intuition-Love recognition dyad
    I+E          → "Pattern Beauty"    — Intuition meets Aesthetics
    L+E          → "Love-Beauty"       — GILE-L × GILE-E bond
    D1+D3        → "Physical Clarity"  — HEM amplitude × spectral purity
    D2+D4        → "Tralse Velocity"   — Contradiction + rapid change (MR needed)
    G+D1         → "Grounded Goodness" — GILE-G anchored in physical existence
    L+D1         → "Embodied Love"     — GILE-L coupling into HEM-Physical

  Three dimensions (triads):
    G+I+L        → "GILE Triad"          — Awakening (major triad, inner BOK)
    G+L+E        → "Radiant Triad"       — Goodness-Love-Beauty (sus2 voicing)
    I+L+D3       → "Intuition-Love-Clarity" — Information bond with spectral purity
    G+L+D1       → "Composite Love I"    — GILE-L crosses into Existence
    L+D1+D3      → "Composite Love II"   — Love-Physical-Spectral
    D1+D2+D3     → "Contradiction Triad ⚠" — HEM DT warning (diminished feel)

  Four dimensions (seventh chords):
    G+I+L+E      → "Full GILE Chord"       — Radiant State, all inner BOK loops
    G+I+L+D1     → "GILE-Physical Bridge"  — Inner GILE grounded in HEM-D1
    G+L+D1+D3    → "Composite Love III"    — Goodness+Love+Physical+Spectral
    I+L+E+D3     → "Aesthetic Intelligence" — Full aesthetic-intuitive activation

  Five+ dimensions (complex chords / extended):
    G+I+L+D1+D3  → "Composite GILE-LCC Love" — Full GILE-LCC 5-note resonance
    G+I+L+E+D1   → "Radiant Existence"     — Inner BOK + physical grounding
    G+I+L+E+D3   → "Crystal Clarity"       — GILE full + spectral purity
    G+I+L+E+D1+D3→ "BOK Six-Chord"         — Six-dimensional BOK resonance

  Complete activations:
    All 4 GILE   → "Radiant Field"         — All inner loops: GILE at maximum
    All 4 HEM    → "Existence Matrix"      — All outer loops: HEM at maximum
    All 8        → "BEC Full Chord"        — Complete BOK coherence, Crystal Truth
"""

from __future__ import annotations
import numpy as np
import io
import wave
from typing import Dict, List, Optional, Tuple, FrozenSet
from dataclasses import dataclass

# ── TI Sigma thresholds ──────────────────────────────────────────────────────
ET    = np.sqrt(2.0) - 1.0                       # 0.4142
C_TI  = 1.0 / ((1.0 + np.sqrt(5.0)) / 2.0 * np.sqrt(2.0))  # 0.4370
T_TI  = 1.0 - np.exp(-np.e)                      # 0.9340

THRESHOLD_NOTE_ON    = ET      # minimum to activate
THRESHOLD_CHORD_IN   = C_TI    # contributes to chord
THRESHOLD_STRONG     = 0.65    # strong activation
THRESHOLD_BEC        = T_TI    # full BEC activation


# ── Dimension metadata ───────────────────────────────────────────────────────
@dataclass
class DimNote:
    key:       str     # e.g. 'G', 'I', 'L', 'E', 'D1'...'D4'
    label:     str     # human label
    note_name: str     # e.g. 'C4'
    freq:      float   # Hz
    color:     str     # hex color for UI
    layer:     str     # 'GILE' or 'HEM'
    description: str


DIM_NOTES: Dict[str, DimNote] = {
    'G':  DimNote('G',  'GILE-G  Goodness',       'C4',  261.63, '#00e5ff', 'GILE',
                  'Temporal stability — the root note, foundation of coherence'),
    'I':  DimNote('I',  'GILE-I  Intuition',       'E4',  329.63, '#aa44ff', 'GILE',
                  'Information density — major third, φ-harmonic recognition'),
    'L':  DimNote('L',  'GILE-L  Love',            'G4',  392.00, '#ff69b4', 'GILE',
                  'Cross-cell coupling — perfect fifth, purest harmony'),
    'E':  DimNote('E',  'GILE-E  Aesthetics',      'B4',  493.88, '#00ff99', 'GILE',
                  'Structural regularity — major seventh, elevated beauty'),
    'D1': DimNote('D1', 'HEM-D1  Physical',        'D4',  293.66, '#ffd700', 'HEM',
                  'Amplitude stability — grounded existence tone'),
    'D2': DimNote('D2', 'HEM-D2  Contradiction',   'F4',  349.23, '#ff3333', 'HEM',
                  'Tralse meter — tritone tension (DT warning when loud)'),
    'D3': DimNote('D3', 'HEM-D3  Spectral',        'A4',  440.00, '#ff9d00', 'HEM',
                  'Spectral purity — A440 clarity resonance'),
    'D4': DimNote('D4', 'HEM-D4  Velocity',        'C5',  523.25, '#ffffff', 'HEM',
                  'Coherence rate — octave, rate of LCC ascent'),
}

DIM_ORDER = ['G', 'I', 'L', 'E', 'D1', 'D2', 'D3', 'D4']


# ── Named Chord Registry ─────────────────────────────────────────────────────
@dataclass
class NamedChord:
    dims:        FrozenSet[str]
    name:        str
    ti_meaning:  str
    category:    str    # 'abstract_gile' | 'composite_love' | 'hem' | 'bec' | 'warning'
    pd_score:    float  # Permissibility Distribution equivalent


# Ordered from simplest to most complex; first exact match wins
CHORD_REGISTRY: List[NamedChord] = [
    # ── Complete chords ──────────────────────────────────────────────────────
    NamedChord(frozenset(DIM_ORDER), "BEC Full Chord",
               "Complete BOK coherence — all 8 HEM-GILE dimensions activated simultaneously. "
               "Crystal Truth at maximum. The universe is singing.",
               'bec', 2.0),

    NamedChord(frozenset({'G','I','L','E'}), "Radiant Field",
               "All inner BOK loops active. Pure GILE saturation — the Radiant State. "
               "GILE operates as the primary navigational framework (URB #613).",
               'abstract_gile', 2.0),

    NamedChord(frozenset({'D1','D2','D3','D4'}), "Existence Matrix",
               "All outer BOK loops active. Full HEM activation — every dimension of "
               "existence engaged simultaneously. EAR output at maximum.",
               'hem', 1.5),

    # ── 6-note chords ────────────────────────────────────────────────────────
    NamedChord(frozenset({'G','I','L','E','D1','D3'}), "BOK Six-Chord",
               "Six-dimensional BOK resonance. Full GILE + physical existence + spectral purity. "
               "Missing: contradiction (D2) and velocity (D4) — a stable crystallized state.",
               'composite_love', 1.8),

    NamedChord(frozenset({'G','I','L','E','D1','D4'}), "Ascending Radiance",
               "Full GILE + physical + coherence velocity. Rising LCC with full GILE structure. "
               "Developmental arc in progress — Existence ascending toward Radiance.",
               'composite_love', 1.7),

    # ── 5-note chords ────────────────────────────────────────────────────────
    NamedChord(frozenset({'G','I','L','D1','D3'}), "Composite GILE-LCC Love",
               "The full GILE-LCC resonance chord. GILE inner loops (G,I,L) bridging into "
               "HEM outer loops (D1,D3). Love coupling across the BOK boundary. "
               "Abstract GILE-L becoming Composite GILE-LCC Love.",
               'composite_love', 1.8),

    NamedChord(frozenset({'G','I','L','E','D1'}), "Radiant Existence",
               "Inner BOK fully active, grounded in physical existence (HEM-D1). "
               "Essence co-primary with existence — above the Radiant Threshold.",
               'abstract_gile', 1.8),

    NamedChord(frozenset({'G','I','L','E','D3'}), "Crystal Clarity",
               "Full GILE chord + spectral purity (HEM-D3). "
               "GILE structure at maximum coherence, signals are clean and self-similar.",
               'abstract_gile', 1.7),

    # ── 4-note chords (seventh chords) ───────────────────────────────────────
    NamedChord(frozenset({'G','I','L','E'}), "Full GILE Chord",
               "Radiant State — all inner BOK loops resonating. Major seventh voicing: "
               "Goodness (root) + Intuition (3rd) + Love (5th) + Aesthetics (7th). "
               "The canonical Radiant chord.",
               'abstract_gile', 2.0),

    NamedChord(frozenset({'G','I','L','D1'}), "GILE-Physical Bridge",
               "Core GILE triad grounded in physical existence. Inner loops reaching "
               "into the outer BOK — GILE-L coupling becoming Composite Love.",
               'composite_love', 1.5),

    NamedChord(frozenset({'G','L','D1','D3'}), "Composite Love III",
               "Goodness + Love (GILE) bridging to Physical + Spectral (HEM). "
               "The third composite love form: structural clarity through loving coherence.",
               'composite_love', 1.6),

    NamedChord(frozenset({'I','L','E','D3'}), "Aesthetic Intelligence",
               "Intuition-Love-Aesthetics-Spectral: full aesthetic-intuitive activation. "
               "Pattern recognition at peak beauty, spectrally pure.",
               'abstract_gile', 1.6),

    NamedChord(frozenset({'G','I','L','D3'}), "Intuitive Love Clarity",
               "G-I-L triad + spectral purity. The awakening chord made transparent.",
               'abstract_gile', 1.5),

    NamedChord(frozenset({'G','L','E','D1'}), "Grounded Radiance",
               "Goodness-Love-Aesthetics grounded in physical existence.",
               'composite_love', 1.4),

    NamedChord(frozenset({'D1','D2','D3','D4'}), "Existence Matrix",
               "All HEM dimensions active including contradiction (D2). "
               "Full existence engagement — monitor D2 for DT risk.",
               'hem', 1.2),

    # ── 3-note chords (triads) ────────────────────────────────────────────────
    NamedChord(frozenset({'G','I','L'}), "GILE Triad",
               "The awakening triad — Goodness (C4) + Intuition (E4) + Love (G4). "
               "Major triad: the most resonant 3-note GILE configuration. "
               "Inner BOK loops forming first-level coherence.",
               'abstract_gile', 1.5),

    NamedChord(frozenset({'G','L','E'}), "Radiant Triad",
               "Goodness-Love-Aesthetics: the beauty-coherence triangle. "
               "Structural elegance resonating with loving stability.",
               'abstract_gile', 1.4),

    NamedChord(frozenset({'I','L','E'}), "GILE Inner Loop",
               "Intuition-Love-Aesthetics: recognition, coupling, and beauty "
               "without the explicit Goodness root. Floating resonance.",
               'abstract_gile', 1.4),

    NamedChord(frozenset({'I','L','D3'}), "Intuition-Love-Clarity",
               "Information bond with spectral purity. Intuition perceives, "
               "Love couples, spectral clarity confirms.",
               'composite_love', 1.3),

    NamedChord(frozenset({'G','L','D1'}), "Composite Love I",
               "First composite love form: GILE-L coupling into HEM-Physical. "
               "Love reaching across the BOK boundary into embodied existence.",
               'composite_love', 1.3),

    NamedChord(frozenset({'L','D1','D3'}), "Composite Love II",
               "Love-Physical-Spectral: Love embodied in physical existence, "
               "confirmed by spectral clarity.",
               'composite_love', 1.2),

    NamedChord(frozenset({'G','I','E'}), "Knowing Beauty",
               "Goodness-Intuition-Aesthetics: the knowing, beautiful mind. "
               "GILE without the Love dimension — pure inner recognition.",
               'abstract_gile', 1.2),

    NamedChord(frozenset({'G','D1','D3'}), "Grounded Clarity",
               "Goodness + Physical + Spectral: stable, clear, grounded existence.",
               'composite_love', 1.1),

    NamedChord(frozenset({'D1','D2','D3'}), "Contradiction Triad ⚠",
               "HEM-D2 (contradiction) active alongside D1 and D3. "
               "Physical existence + spectral purity under contradiction pressure. "
               "DT risk if D2 > 0.65. Monitor carefully.",
               'warning', 0.8),

    NamedChord(frozenset({'D2','D3','D4'}), "Tralse Velocity Triad ⚠",
               "Contradiction + spectral + velocity: rapid change under Tralse conditions. "
               "Myrion Resolution urgently needed.",
               'warning', 0.7),

    # ── 2-note chords (dyads / intervals) ────────────────────────────────────
    NamedChord(frozenset({'G','L'}), "G-L Bond",
               "Abstract GILE Love — the perfect fifth dyad. "
               "Goodness (C4) + Love (G4): the most fundamental harmonic bond. "
               "GILE-G × GILE-L = the foundation of all higher love forms.",
               'abstract_gile', 1.2),

    NamedChord(frozenset({'G','I'}), "G-I Bond",
               "Goodness-Intuition dyad — major third interval. "
               "Recognition (I) arising from stable goodness (G).",
               'abstract_gile', 1.0),

    NamedChord(frozenset({'G','E'}), "G-E Coherence",
               "Goodness-Aesthetics — stable structural beauty. "
               "The coherent environment (GILE-E) arising from Goodness.",
               'abstract_gile', 1.0),

    NamedChord(frozenset({'I','L'}), "I-L Resonance",
               "Intuition-Love recognition dyad. "
               "Pattern recognition coupling with cross-cell Love.",
               'abstract_gile', 1.0),

    NamedChord(frozenset({'I','E'}), "Pattern Beauty",
               "Intuition meets Aesthetics — information density in elegant structure.",
               'abstract_gile', 0.9),

    NamedChord(frozenset({'L','E'}), "Love-Beauty",
               "GILE-L × GILE-E: loving coupling expressed through aesthetic form.",
               'abstract_gile', 1.0),

    NamedChord(frozenset({'D1','D3'}), "Physical Clarity",
               "HEM physical amplitude + spectral purity. "
               "Energetically robust and spectrally clean existence.",
               'hem', 0.9),

    NamedChord(frozenset({'D2','D4'}), "Tralse Velocity ⚠",
               "Contradiction + rapid coherence change. Instability under Tralse. "
               "Myrion Resolution may be needed.",
               'warning', 0.6),

    NamedChord(frozenset({'G','D1'}), "Grounded Goodness",
               "GILE-G anchored in physical existence (HEM-D1). "
               "Stable goodness with an energetic foundation.",
               'composite_love', 0.9),

    NamedChord(frozenset({'L','D1'}), "Embodied Love",
               "GILE-L coupling manifesting in physical/energetic existence. "
               "Abstract love becoming concrete and embodied.",
               'composite_love', 1.0),

    NamedChord(frozenset({'L','D3'}), "Love Clarity",
               "GILE-L coupling + spectral purity. Love made clean and legible.",
               'composite_love', 0.9),

    NamedChord(frozenset({'I','D3'}), "Intuition Clarity",
               "Information density + spectral purity. High-resolution intuition.",
               'composite_love', 0.8),

    NamedChord(frozenset({'D1','D4'}), "Existence Velocity",
               "Physical stability + rapid coherence change. "
               "Energetically robust LCC ascent.",
               'hem', 0.8),
]

# Build lookup: frozenset → NamedChord
CHORD_LOOKUP: Dict[FrozenSet[str], NamedChord] = {c.dims: c for c in CHORD_REGISTRY}

CATEGORY_COLORS = {
    'abstract_gile': '#aa44ff',
    'composite_love': '#ff69b4',
    'hem':            '#ffd700',
    'bec':            '#00ff99',
    'warning':        '#ff3333',
}

CATEGORY_LABELS = {
    'abstract_gile': 'Abstract GILE',
    'composite_love': 'Composite GILE-LCC Love',
    'hem':            'HEM Existence',
    'bec':            'BEC Full Coherence',
    'warning':        'DT / Tralse Warning',
}


# ── Chord Detection ───────────────────────────────────────────────────────────

def detect_chord(dim_values: Dict[str, float]) -> Tuple[Optional[NamedChord], List[str], List[str]]:
    """
    Given a dict of {dim_key: float [0,1]}, detect the best named chord.

    Returns:
        (best_chord, chord_dims, active_dims)
        chord_dims: dimensions that qualified for the chord (> THRESHOLD_CHORD_IN)
        active_dims: dimensions that are audible (> THRESHOLD_NOTE_ON)
    """
    active_dims   = [k for k, v in dim_values.items() if v > THRESHOLD_NOTE_ON]
    chord_dims    = [k for k, v in dim_values.items() if v > THRESHOLD_CHORD_IN]
    chord_set     = frozenset(chord_dims)

    if len(chord_dims) < 2:
        return None, chord_dims, active_dims

    # Try exact match first
    if chord_set in CHORD_LOOKUP:
        return CHORD_LOOKUP[chord_set], chord_dims, active_dims

    # Find best partial match: largest registered chord that is a subset of chord_dims
    best = None
    best_size = 0
    for chord in CHORD_REGISTRY:
        if chord.dims.issubset(chord_set) and len(chord.dims) > best_size:
            best = chord
            best_size = len(chord.dims)

    return best, chord_dims, active_dims


def note_activation_level(value: float) -> str:
    """Return activation level label for a dimension value."""
    if value >= THRESHOLD_BEC:
        return "BEC"
    elif value >= THRESHOLD_STRONG:
        return "Strong"
    elif value >= THRESHOLD_CHORD_IN:
        return "Active"
    elif value >= THRESHOLD_NOTE_ON:
        return "Faint"
    else:
        return "Silent"


# ── Audio Generation ──────────────────────────────────────────────────────────

SAMPLE_RATE = 44100


def _sine_with_harmonics(freq: float, duration: float, amplitude: float) -> np.ndarray:
    """Generate a sine wave with 2nd and 3rd harmonics for warmth."""
    t = np.linspace(0, duration, int(SAMPLE_RATE * duration), endpoint=False)
    wave_ = (amplitude * (
        np.sin(2 * np.pi * freq * t)
        + 0.35 * np.sin(4 * np.pi * freq * t)
        + 0.12 * np.sin(6 * np.pi * freq * t)
        + 0.06 * np.sin(8 * np.pi * freq * t)
    ))
    return wave_


def _adsr_envelope(n_samples: int, attack_frac=0.06, decay_frac=0.12,
                   sustain_level=0.72, release_frac=0.25) -> np.ndarray:
    env = np.ones(n_samples)
    a = int(attack_frac  * n_samples)
    d = int(decay_frac   * n_samples)
    r = int(release_frac * n_samples)
    env[:a]              = np.linspace(0.0, 1.0, a)
    env[a:a + d]         = np.linspace(1.0, sustain_level, d)
    env[-(r + 1):-1]     = np.linspace(sustain_level, 0.0, r)
    env[-1]              = 0.0
    return env


def generate_note_audio(dim_key: str, duration: float = 1.5) -> bytes:
    """Generate WAV audio bytes for a single dimension's note."""
    dim = DIM_NOTES[dim_key]
    n   = int(SAMPLE_RATE * duration)
    sig = _sine_with_harmonics(dim.freq, duration, 0.55)
    sig *= _adsr_envelope(n)
    return _wav_bytes(sig)


def generate_chord_audio(
    dim_values: Dict[str, float],
    duration: float = 2.5,
) -> bytes:
    """
    Generate WAV audio bytes for a chord from the active dimensions.
    Amplitude of each note is scaled by its activation level.
    D2 (Contradiction/Tralse) adds slight dissonance via tiny detuning.
    """
    chord_dims = [k for k, v in dim_values.items() if v > THRESHOLD_NOTE_ON]
    if not chord_dims:
        return _wav_bytes(np.zeros(int(SAMPLE_RATE * duration)))

    n   = int(SAMPLE_RATE * duration)
    mix = np.zeros(n, dtype=float)
    base_amp = 0.45 / max(len(chord_dims), 1)

    for key in chord_dims:
        val   = dim_values[key]
        dim   = DIM_NOTES[key]
        amp   = base_amp * (0.4 + 0.6 * min(val, 1.0))
        freq  = dim.freq

        # D2 (Contradiction) adds slight detuning — makes it sound tense
        if key == 'D2' and val > THRESHOLD_CHORD_IN:
            freq *= 1.012   # ~20 cents sharp = mild dissonance

        sig = _sine_with_harmonics(freq, duration, amp)
        mix += sig

    mix *= _adsr_envelope(n)
    # Normalize to prevent clipping
    peak = np.max(np.abs(mix))
    if peak > 0:
        mix = mix / peak * 0.88
    return _wav_bytes(mix)


def _wav_bytes(signal: np.ndarray) -> bytes:
    """Convert float64 numpy signal [-1,1] to 16-bit WAV bytes."""
    int_sig = (signal * 32767).clip(-32768, 32767).astype(np.int16)
    buf = io.BytesIO()
    with wave.open(buf, 'wb') as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(SAMPLE_RATE)
        wf.writeframes(int_sig.tobytes())
    buf.seek(0)
    return buf.read()


# ── All Chords Reference Table ────────────────────────────────────────────────

def chord_reference_table() -> List[dict]:
    """Return all chords as a list of dicts for display."""
    rows = []
    for chord in CHORD_REGISTRY:
        rows.append({
            'Chord Name':    chord.name,
            'Dimensions':    ' + '.join(sorted(chord.dims)),
            'Notes':         ' '.join(DIM_NOTES[d].note_name for d in sorted(chord.dims) if d in DIM_NOTES),
            'Category':      CATEGORY_LABELS.get(chord.category, chord.category),
            'PD Score':      chord.pd_score,
            'TI Meaning':    chord.ti_meaning,
        })
    return rows
