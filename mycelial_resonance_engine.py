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


def _gile_harmonic_bed(
    t: np.ndarray,
    duration_s: float,
    root_hz: float = 196.0,            # G3 — pleasant low root, ratio-friendly
    progression: Optional[list] = None, # list of (start_frac, ratios_tuple) chord events
    breath_bpm: float = 5.5,           # slow tremolo coupled to cardiac coherence
) -> np.ndarray:
    """
    GILE-coherent harmonic bed (URB #781 §B compliant).

    Replaces a bare carrier sine with a sparse just-intonation chord that
    moves through a +Δ-resolution progression (each change resolves upward
    or sustains; no exploitative dissonance, no tritones, no minor seconds).
    Default progression is I → IV → V → I in just intonation, with each
    chord built from root + perfect-fifth (3:2) + octave (2:1).
    A slow tremolo at the breath frequency couples bed amplitude to cardiac
    coherence so it never stands flat against the entrainment envelope.

    Returns a normalized waveform in [-1, 1] suitable for mixing as a carrier.
    """
    if progression is None:
        # I (1:1), IV (4:3), V (3:2), I (1:1) — Dirac-elegant root motion in JI.
        # Each chord = (start_frac_of_duration, root_ratio, fifth_ratio, octave_ratio)
        progression = [
            (0.00, 1.0,        3.0/2,      2.0),
            (0.30, 4.0/3,      (4.0/3)*(3.0/2), (4.0/3)*2.0),
            (0.60, 3.0/2,      (3.0/2)*(3.0/2)/2, (3.0/2)*2.0),  # V with fifth folded down to stay in tessitura
            (0.85, 1.0,        3.0/2,      2.0),
        ]

    n = t.shape[0]
    bed = np.zeros(n, dtype=np.float64)
    # Build per-segment crossfaded sums of three sines (root, fifth, octave)
    seg_starts = [int(seg[0] * n) for seg in progression] + [n]
    crossfade = int(0.025 * n)  # ~2.5% of total duration crossfade per chord change

    for i, seg in enumerate(progression):
        s0 = seg_starts[i]
        s1 = seg_starts[i + 1]
        r1, r2, r3 = seg[1] * root_hz, seg[2] * root_hz, seg[3] * root_hz
        seg_t = t[s0:s1]
        chord = (np.sin(2 * np.pi * r1 * seg_t)
                 + 0.65 * np.sin(2 * np.pi * r2 * seg_t)
                 + 0.45 * np.sin(2 * np.pi * r3 * seg_t)) / 2.10  # normalize peak
        # Apply local amplitude ramp at boundaries to crossfade smoothly
        ramp = np.ones_like(chord)
        if s0 > 0 and crossfade > 0:
            k = min(crossfade, ramp.shape[0])
            ramp[:k] = np.linspace(0.0, 1.0, k)
        if s1 < n and crossfade > 0:
            k = min(crossfade, ramp.shape[0])
            ramp[-k:] = np.linspace(1.0, 0.0, k)
        bed[s0:s1] += chord * ramp

    # Slow breath tremolo (proportional symmetry per URB #781 §B.6 test 2)
    breath_hz = breath_bpm / 60.0
    breath = 0.85 + 0.15 * np.sin(2.0 * np.pi * breath_hz * t)
    bed = bed * breath

    peak = float(np.max(np.abs(bed))) or 1.0
    return bed / peak


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
    harmonic_bed: bool = False,        # L4: GILE-coherent harmonic bed (URB #781 §B)
    harmonic_root_hz: float = 196.0,
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
        if harmonic_bed:
            carrier = _gile_harmonic_bed(t, duration_s, root_hz=harmonic_root_hz, breath_bpm=cardiac_bpm)
        else:
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
    harmonic_bed: bool = False,
    output_path: Optional[str] = None,
) -> dict:
    """High-level: pick attractor, read state, drift from current α-peak to target."""
    if mood_key not in MOOD_ATTRACTORS:
        raise ValueError(f"unknown mood: {mood_key}; choose from {list(MOOD_ATTRACTORS)}")
    attractor = MOOD_ATTRACTORS[mood_key]

    state = read_current_state(session_id) if use_current_state else {}
    start_hz = estimate_alpha_peak(state) if state else attractor.target_hz

    if output_path is None:
        bed_tag = "_bed" if harmonic_bed else ""
        output_path = f"tracks/mre_{mood_key.lower()}_{int(start_hz*10)}_to_{int(attractor.target_hz*10)}{bed_tag}.wav"

    path = generate_track(
        target_hz=attractor.target_hz,
        duration_s=duration_s,
        start_hz=start_hz,
        overlay_hz=attractor.overlay_hz,
        mode=mode,
        harmonic_bed=harmonic_bed,
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
        "harmonic_bed": harmonic_bed,
        "state_used": {k: state.get(k) for k in ("alpha", "beta", "theta", "session_id", "created_at")} if state else None,
    }


# ---------------------------------------------------------------------------
# v2: Adaptive session — anticipatory closed-loop using recent Muse history
# ---------------------------------------------------------------------------

def read_state_history(session_id: Optional[str] = None, limit: int = 30) -> list[dict]:
    """Read the most-recent N Muse rows (newest first) for trajectory estimation."""
    where = "WHERE session_id = %s" if session_id else "WHERE muse_connected = TRUE"
    params = (session_id, limit) if session_id else (limit,)
    with psycopg2.connect(os.environ["DATABASE_URL"]) as conn:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT alpha, beta, theta, gamma, delta, created_at
                FROM esp32_biometric_data
                {where}
                ORDER BY created_at DESC
                LIMIT %s
                """,
                params,
            )
            return [dict(r) for r in cur.fetchall()]


def _estimate_alpha_velocity(history: list[dict]) -> float:
    """
    Hz / second velocity estimate from the rolling alpha-peak series.

    Uses simple linear fit on estimate_alpha_peak() applied across history.
    Returns 0.0 if insufficient data or zero time-span.
    """
    if not history or len(history) < 3:
        return 0.0
    rows = list(reversed(history))  # oldest → newest
    ts = [r["created_at"] for r in rows]
    if not ts[0] or not ts[-1]:
        return 0.0
    span = (ts[-1] - ts[0]).total_seconds()
    if span <= 0:
        return 0.0
    peaks = np.array([estimate_alpha_peak(r) for r in rows])
    secs  = np.array([(r["created_at"] - ts[0]).total_seconds() for r in rows])
    # least-squares slope
    A = np.vstack([secs, np.ones_like(secs)]).T
    slope, _ = np.linalg.lstsq(A, peaks, rcond=None)[0]
    # Clamp to reasonable physiological velocity (|v| ≤ 0.05 Hz/s)
    return float(np.clip(slope, -0.05, 0.05))


def generate_adaptive_session(
    mood_key: str,
    duration_s: int = 600,
    *,
    segment_s: int = 30,
    session_id: Optional[str] = None,
    mode: str = "isochronic",
    harmonic_bed: bool = True,
    output_path: Optional[str] = None,
) -> dict:
    """
    v2 anticipatory adaptation: build a multi-segment WAV where each segment's
    drift parameters are computed from the rolling Muse trajectory.

    Reads the most-recent ~60s of state history, estimates current α-peak and
    α-velocity, then projects where the operator will be at the start of each
    segment under the assumption that entrainment progressively pulls the
    operator toward the attractor with each preceding segment. Each segment's
    instantaneous start_hz is the projection; its end_hz is a weighted average
    of (projection-following) and (attractor-target), so early segments meet
    the operator where they are and later segments commit harder to the goal.

    The whole track is rendered in one numpy pass with crossfaded segments,
    so it plays back as one continuous file — but the *internal* drift profile
    encodes anticipated state evolution. This is open-loop pre-adaptation;
    true on-line adaptation requires live audio, deferred to v3.
    """
    if mood_key not in MOOD_ATTRACTORS:
        raise ValueError(f"unknown mood: {mood_key}")
    attractor = MOOD_ATTRACTORS[mood_key]
    target_hz = attractor.target_hz

    history = read_state_history(session_id=session_id, limit=30)
    if history:
        current_peak = estimate_alpha_peak(history[0])
        velocity = _estimate_alpha_velocity(history)
    else:
        current_peak = target_hz
        velocity = 0.0

    n_segments = max(1, duration_s // segment_s)
    # Per-segment drift schedule
    segments = []
    for i in range(n_segments):
        seg_t0 = i * segment_s
        # Naive projection: where would natural drift put us?
        natural_proj = current_peak + velocity * seg_t0
        # Entrainment progressively pulls: weight from 0 (segment 0) → 1 (last segment)
        w = (i + 1) / n_segments
        seg_start = (1.0 - 0.5 * w) * natural_proj + (0.5 * w) * target_hz
        # End of segment commits harder toward target as we go
        seg_end = (1.0 - w) * seg_start + w * target_hz
        # Clamp into entrainable range
        seg_start = float(np.clip(seg_start, 4.0, 16.0))
        seg_end   = float(np.clip(seg_end,   4.0, 16.0))
        segments.append({"index": i, "start_hz": round(seg_start, 3), "end_hz": round(seg_end, 3),
                         "duration_s": segment_s})

    # Render: build continuous time, segment-by-segment instantaneous frequency
    sample_rate = 16000
    n = int(duration_s * sample_rate)
    t = np.arange(n, dtype=np.float64) / sample_rate
    inst_freq = np.zeros(n, dtype=np.float64)
    for seg in segments:
        i0 = int(seg["index"] * segment_s * sample_rate)
        i1 = int((seg["index"] + 1) * segment_s * sample_rate)
        i1 = min(i1, n)
        seg_n = i1 - i0
        if seg_n <= 0:
            continue
        inst_freq[i0:i1] = np.linspace(seg["start_hz"], seg["end_hz"], seg_n)

    # Integrate to phase
    phi_iso = 2.0 * np.pi * np.cumsum(inst_freq) / sample_rate

    # Carrier: GILE harmonic bed if requested, else plain sine
    if harmonic_bed:
        carrier = _gile_harmonic_bed(t, duration_s)
    else:
        carrier = np.sin(2.0 * np.pi * 200.0 * t)

    iso_env = 0.5 * (1.0 + np.cos(phi_iso - np.pi))
    cardiac_env = 0.80 + 0.20 * np.cos(2.0 * np.pi * (5.5 / 60.0) * t)
    fade = _fade_envelope(n, sample_rate, 4.0, 6.0)
    sig = 0.30 * carrier * iso_env * cardiac_env * fade

    if attractor.overlay_hz is not None:
        phi_ov = 2.0 * np.pi * attractor.overlay_hz * t
        ov_env = 0.5 * (1.0 + np.cos(phi_ov - np.pi))
        sig = sig + 0.12 * carrier * ov_env * cardiac_env * fade

    sig_int = np.clip(sig * 32767.0, -32767, 32767).astype(np.int16)

    if output_path is None:
        output_path = f"tracks/mre_adaptive_{mood_key.lower()}_{int(duration_s)}s.wav"
    os.makedirs(os.path.dirname(output_path) or ".", exist_ok=True)
    with wave.open(output_path, "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(sample_rate)
        wf.writeframes(sig_int.tobytes())

    return {
        "path": output_path,
        "mood_key": mood_key,
        "attractor_name": attractor.name,
        "target_hz": target_hz,
        "current_peak_hz": round(current_peak, 3),
        "alpha_velocity_hz_per_s": round(velocity, 5),
        "segments": segments,
        "duration_s": duration_s,
        "segment_s": segment_s,
        "n_segments": n_segments,
        "harmonic_bed": harmonic_bed,
        "history_rows_used": len(history),
        "mode": mode,
    }


# ---------------------------------------------------------------------------
# L5: SSVEP visual entrainment overlay (HTML component)
# ---------------------------------------------------------------------------

SSVEP_HTML_TEMPLATE = """\
<!doctype html>
<html><head><meta charset="utf-8"><title>MRE SSVEP overlay</title>
<style>
  html, body {{ margin: 0; padding: 0; height: 100%; background: #111; color: #eee;
                font-family: -apple-system, system-ui, sans-serif; }}
  #stage {{ position: fixed; inset: 0; transition: none;
            background: radial-gradient(circle at center, #2a1840, #0a0612 70%); }}
  #info  {{ position: fixed; bottom: 12px; left: 12px; right: 12px; opacity: 0.55;
            font-size: 12px; line-height: 1.4; pointer-events: none; }}
  #fix   {{ position: fixed; top: 50%; left: 50%; width: 8px; height: 8px;
            transform: translate(-50%, -50%); border-radius: 50%;
            background: rgba(255,255,255,0.4); pointer-events: none; }}
</style></head>
<body>
  <div id="stage"></div>
  <div id="fix"></div>
  <div id="info">
    SSVEP overlay — soft sinusoidal flicker at <b>{freq_hz:.2f} Hz</b>
    ({mood_name}). View in peripheral vision; do not stare. Stop after
    5–10 minutes or at any discomfort. Photosensitive-epilepsy warning applies.
  </div>
<script>
(function() {{
  var TARGET_HZ = {freq_hz};
  var BASE_R = 32, BASE_G = 18, BASE_B = 56;
  var PEAK_R = 168, PEAK_G = 110, PEAK_B = 240;
  var stage = document.getElementById("stage");
  var t0 = null;
  function tick(ts) {{
    if (t0 === null) t0 = ts;
    var t = (ts - t0) / 1000.0;
    var k = 0.5 + 0.5 * Math.sin(2 * Math.PI * TARGET_HZ * t);
    var r = Math.round(BASE_R + (PEAK_R - BASE_R) * k);
    var g = Math.round(BASE_G + (PEAK_G - BASE_G) * k);
    var b = Math.round(BASE_B + (PEAK_B - BASE_B) * k);
    stage.style.background = "rgb(" + r + "," + g + "," + b + ")";
    requestAnimationFrame(tick);
  }}
  requestAnimationFrame(tick);
}})();
</script>
</body></html>
"""


def ssvep_html(target_hz: float, mood_name: str = "Calm Focus") -> str:
    """Return a self-contained HTML page that flickers a soft purple field at target_hz.

    Uses requestAnimationFrame with timestamp-based phase (no setInterval drift),
    sinusoidal brightness modulation (gentler than square wave; lower seizure risk
    than high-contrast strobing), and a dim-by-default palette. Includes an
    on-page photosensitive-epilepsy warning. Intended for peripheral viewing only.
    """
    return SSVEP_HTML_TEMPLATE.format(freq_hz=float(target_hz), mood_name=mood_name)


if __name__ == "__main__":
    import json
    result = generate_for_mood("CALM_FOCUS", duration_s=300, mode="isochronic")
    print(json.dumps(result, indent=2, default=str))
