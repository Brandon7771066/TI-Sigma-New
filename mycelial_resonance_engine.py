"""
Mycelial Resonance Engine (MRE) — closed-loop ambient brain entrainment.

Generates isochronic-tone tracks with a slow drift from the operator's current
EEG α-peak toward a target mood-attractor frequency, modulated by a 5.5-BPM
cardiac-coherence amplitude envelope.

v1 capabilities (this file):
  - Read latest Muse band-power state from esp32_biometric_data
  - Heuristic α-peak estimate from band-power dominance pattern
  - Generate mono isochronic tone (speaker-friendly) or stereo binaural (headphones)
  - Linear-drift instantaneous frequency from start_hz → target_hz over duration
  - 5.5-BPM cardiac envelope coupling
  - Smooth fade-in/fade-out
  - Pure stdlib + numpy. No API calls.

v2 (next session): closed-loop adaptation; v3: visual flicker overlay.

URB linkage: Mycelial GM-Node Architecture (replit.md), GILE-coherent harmonic
bed (URB #781 §B), 5.5-BPM cardiac coherence (HeartMath / Lehrer baroreflex).
"""

from __future__ import annotations

import os
import wave
from dataclasses import dataclass
from typing import Optional

import numpy as np
import psycopg2
from psycopg2.extras import RealDictCursor


# ---------------------------------------------------------------------------
# Mood attractors — target frequencies the drift ramps toward
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MoodAttractor:
    key: str
    target_hz: float
    overlay_hz: Optional[float]  # secondary frequency (e.g., 40 Hz gamma overlay)
    name: str
    description: str


MOOD_ATTRACTORS: dict[str, MoodAttractor] = {
    "CALM_FOCUS": MoodAttractor(
        "CALM_FOCUS", 10.5, None,
        "Calm Focus",
        "Peak α (10.5 Hz). Restful awareness with retained attention. The default lift.",
    ),
    "FLOW": MoodAttractor(
        "FLOW", 12.0, None,
        "Flow",
        "Low β (12 Hz). Engaged, smooth, productive. For sustained creative or analytic work.",
    ),
    "DEEP_REST": MoodAttractor(
        "DEEP_REST", 6.0, None,
        "Deep Rest",
        "θ (6 Hz). Recovery, hypnagogic, sleep-adjacent. Use lying down.",
    ),
    "EUPHORIC_ALERT": MoodAttractor(
        "EUPHORIC_ALERT", 14.0, 40.0,
        "Euphoric Alert",
        "β (14 Hz) with γ (40 Hz) overlay. Mood lift plus cross-cortical integration.",
    ),
    "CREATIVE_IDEATION": MoodAttractor(
        "CREATIVE_IDEATION", 8.0, None,
        "Creative Ideation",
        "θ/α border (8 Hz). Hypnagogic creativity; loose associative thinking.",
    ),
    "GILE_COHERENCE": MoodAttractor(
        "GILE_COHERENCE", 7.83, None,
        "GILE Coherence (Schumann)",
        "7.83 Hz Schumann resonance. Fractal-coupled, GILE-aligned per URB #781 §B.",
    ),
}


# ---------------------------------------------------------------------------
# State reading + α-peak heuristic
# ---------------------------------------------------------------------------

def read_current_state(session_id: Optional[str] = None) -> dict:
    """Read the latest Muse row from esp32_biometric_data."""
    where = "WHERE session_id = %s" if session_id else "WHERE muse_connected = TRUE"
    params = (session_id,) if session_id else ()
    with psycopg2.connect(os.environ["DATABASE_URL"]) as conn:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT alpha, beta, theta, gamma, delta, heart_rate, rmssd,
                       polar_connected, muse_connected, session_id, created_at
                FROM esp32_biometric_data
                {where}
                ORDER BY created_at DESC
                LIMIT 1
                """,
                params,
            )
            row = cur.fetchone()
    return dict(row) if row else {}


def estimate_alpha_peak(state: dict) -> float:
    """
    Heuristic α-peak frequency estimate from Mind-Monitor band-power summaries.

    Population mean α-peak ~ 10 Hz. Adjust within [8.5, 11.5] based on the
    relative dominance of α vs adjacent bands:
      - high α relative to θ → peak shifts up (toward 11)
      - high θ relative to α → peak shifts down (toward 9)
      - high β → suggests narrower / higher α peak
    """
    a = float(state.get("alpha") or 0.0)
    b = float(state.get("beta") or 0.0)
    t = float(state.get("theta") or 0.0)

    base = 10.0
    # α dominance shifts peak up; θ dominance shifts it down
    shift = 0.6 * (a - t) + 0.3 * (b - 0.0)
    return float(np.clip(base + shift, 8.5, 11.5))


# ---------------------------------------------------------------------------
# Audio synthesis
# ---------------------------------------------------------------------------

def _fade_envelope(n: int, sample_rate: int, fade_in_s: float, fade_out_s: float) -> np.ndarray:
    env = np.ones(n, dtype=np.float64)
    fi = int(fade_in_s * sample_rate)
    fo = int(fade_out_s * sample_rate)
    if fi > 0:
        env[:fi] = np.linspace(0.0, 1.0, fi)
    if fo > 0:
        env[-fo:] = np.linspace(1.0, 0.0, fo)
    return env


def _drift_phase(start_hz: float, target_hz: float, t: np.ndarray, T: float) -> np.ndarray:
    """Integrated phase for linear frequency drift from start_hz to target_hz over T."""
    a = float(start_hz)
    b = float(target_hz - start_hz)
    return 2.0 * np.pi * (a * t + b * t * t / (2.0 * T))


def generate_track(
    target_hz: float,
    duration_s: int = 300,
    *,
    start_hz: Optional[float] = None,
    carrier_hz: float = 200.0,
    sample_rate: int = 16000,
    mode: str = "isochronic",          # "isochronic" or "binaural"
    overlay_hz: Optional[float] = None, # secondary entrainment frequency, mixed in at lower amp
    cardiac_bpm: float = 5.5,
    amp: float = 0.30,
    fade_in_s: float = 4.0,
    fade_out_s: float = 6.0,
    output_path: str = "tracks/mre_track.wav",
) -> str:
    """
    Synthesize an entrainment WAV.

    isochronic: mono carrier sine at carrier_hz, amplitude-modulated by a
                smooth cosine pulse at the (drifting) target_hz. Speaker-safe.
    binaural:   stereo, left = carrier_hz, right = carrier_hz + target_hz(t).
                Headphones required.
    """
    if start_hz is None:
        start_hz = target_hz
    n = int(duration_s * sample_rate)
    t = np.arange(n, dtype=np.float64) / sample_rate
    fade = _fade_envelope(n, sample_rate, fade_in_s, fade_out_s)

    cardiac_hz = cardiac_bpm / 60.0
    cardiac_env = 0.80 + 0.20 * np.cos(2.0 * np.pi * cardiac_hz * t)

    os.makedirs(os.path.dirname(output_path) or ".", exist_ok=True)

    if mode == "isochronic":
        carrier = np.sin(2.0 * np.pi * carrier_hz * t)
        phi_iso = _drift_phase(start_hz, target_hz, t, duration_s)
        iso_env = 0.5 * (1.0 + np.cos(phi_iso - np.pi))
        sig = amp * carrier * iso_env * cardiac_env * fade

        if overlay_hz is not None:
            phi_ov = 2.0 * np.pi * overlay_hz * t
            ov_env = 0.5 * (1.0 + np.cos(phi_ov - np.pi))
            sig = sig + (0.4 * amp) * carrier * ov_env * cardiac_env * fade

        sig_int = np.clip(sig * 32767.0, -32767, 32767).astype(np.int16)

        with wave.open(output_path, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sample_rate)
            wf.writeframes(sig_int.tobytes())

    elif mode == "binaural":
        left_phase  = 2.0 * np.pi * carrier_hz * t
        right_freq_inst = start_hz + (target_hz - start_hz) * (t / duration_s)
        right_phase = 2.0 * np.pi * np.cumsum(carrier_hz + right_freq_inst) / sample_rate

        left  = amp * np.sin(left_phase)  * cardiac_env * fade
        right = amp * np.sin(right_phase) * cardiac_env * fade

        stereo = np.stack([left, right], axis=1)
        stereo_int = np.clip(stereo * 32767.0, -32767, 32767).astype(np.int16)

        with wave.open(output_path, "wb") as wf:
            wf.setnchannels(2)
            wf.setsampwidth(2)
            wf.setframerate(sample_rate)
            wf.writeframes(stereo_int.tobytes())
    else:
        raise ValueError(f"unknown mode: {mode}")

    return output_path


def generate_for_mood(
    mood_key: str,
    duration_s: int = 300,
    *,
    use_current_state: bool = True,
    session_id: Optional[str] = None,
    mode: str = "isochronic",
    output_path: Optional[str] = None,
) -> dict:
    """High-level: pick attractor, read state, drift from current α-peak to target."""
    if mood_key not in MOOD_ATTRACTORS:
        raise ValueError(f"unknown mood: {mood_key}; choose from {list(MOOD_ATTRACTORS)}")
    attractor = MOOD_ATTRACTORS[mood_key]

    state = read_current_state(session_id) if use_current_state else {}
    start_hz = estimate_alpha_peak(state) if state else attractor.target_hz

    if output_path is None:
        output_path = f"tracks/mre_{mood_key.lower()}_{int(start_hz*10)}_to_{int(attractor.target_hz*10)}.wav"

    path = generate_track(
        target_hz=attractor.target_hz,
        duration_s=duration_s,
        start_hz=start_hz,
        overlay_hz=attractor.overlay_hz,
        mode=mode,
        output_path=output_path,
    )
    return {
        "path": path,
        "mood_key": mood_key,
        "attractor_name": attractor.name,
        "start_hz": round(start_hz, 2),
        "target_hz": attractor.target_hz,
        "overlay_hz": attractor.overlay_hz,
        "duration_s": duration_s,
        "mode": mode,
        "state_used": {k: state.get(k) for k in ("alpha", "beta", "theta", "session_id", "created_at")} if state else None,
    }


if __name__ == "__main__":
    import json
    result = generate_for_mood("CALM_FOCUS", duration_s=300, mode="isochronic")
    print(json.dumps(result, indent=2, default=str))
