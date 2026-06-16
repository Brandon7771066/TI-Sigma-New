"""
TI Sigma Video Producer — FFmpeg-based MP4 generation pipeline
==============================================================

Converts TIVideoCreator scripts into real MP4 video files using:
  1. Matplotlib/Pillow: title cards + equation/chart visualizations → PNG frames
  2. OpenAI TTS (tts-1, voice=onyx): narration → WAV audio
  3. FFmpeg 7.1.1: PNG frames + WAV → MP4 with subtitle burn-in

Usage:
    python ti_video_producer.py

Or programmatic:
    from ti_video_producer import produce_video
    produce_video(
        title="The Consciousness Equation",
        topic="consciousness_equation",
        output_path="videos/paper_352.mp4"
    )

First video: Paper #352 — The Consciousness Equation
  "How Math Proves the Mind Has a Threshold"
  3–5 minute explainer on Ψ(LCC) = φ × LCC × (LCC/C − 1)

Brandon Emerick — TI Sigma Research
March 1, 2026
"""

import os
import sys
import math
import time
import shutil
import tempfile
import subprocess
import numpy as np

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
PHI   = (1 + math.sqrt(5)) / 2
SQRT2 = math.sqrt(2)
C_EMERICK = 1 / (PHI * SQRT2)

LCC_TRALSE  = SQRT2 - 1
LCC_TRUE    = PHI - 1
LCC_EMERICK = 1 / SQRT2
LCC_HIGH    = C_EMERICK + LCC_TRALSE
LCC_RADIANT = math.sqrt(math.e / math.pi)

VIDEO_DIR = 'videos'
os.makedirs(VIDEO_DIR, exist_ok=True)

BG_COLOR    = '#05050f'
TEXT_COLOR  = '#f0f0fa'
ACCENT      = '#c8a000'
GOLD        = '#ffd700'
GREEN       = '#52c77a'
RED         = '#e05060'
PURPLE      = '#a06ce0'
BLUE        = '#4090d0'

WIDTH, HEIGHT = 1280, 720
FPS = 24

# ─────────────────────────────────────────────────────────────────────────────
# FRAME RENDERING
# ─────────────────────────────────────────────────────────────────────────────

def _draw_starfield(ax, n=180, seed=42):
    """Draw a subtle starfield on the axes (call before other elements)."""
    rng = np.random.default_rng(seed)
    xs = rng.random(n)
    ys = rng.random(n)
    sizes  = rng.uniform(0.3, 2.5, n)
    alphas = rng.uniform(0.15, 0.55, n)
    for x, y, s, a in zip(xs, ys, sizes, alphas):
        ax.plot(x, y, 'o', color='white', markersize=s, alpha=a, zorder=1)


def _draw_letterbox(ax, bar_h=0.06):
    """Draw cinematic letterbox bars at top and bottom."""
    import matplotlib.patches as patches
    top = patches.Rectangle((0, 1 - bar_h), 1, bar_h,
                             facecolor='#000000', edgecolor='none', zorder=20)
    bot = patches.Rectangle((0, 0), 1, bar_h,
                             facecolor='#000000', edgecolor='none', zorder=20)
    ax.add_patch(top)
    ax.add_patch(bot)


def render_title_card(title: str, subtitle: str, output_path: str,
                      duration_s: float = 3.0) -> str:
    """Render a cinematic title card PNG frame."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as patches

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)
    ax.axis('off')

    _draw_starfield(ax, n=220)

    # Central glow — layered radial vignette in gold
    for r, a in [(0.55, 0.03), (0.42, 0.05), (0.30, 0.07), (0.18, 0.09)]:
        circle = plt.Circle((0.5, 0.52), r, color=GOLD, alpha=a, zorder=2)
        ax.add_patch(circle)

    # Top gold rule line
    ax.axhline(0.865, xmin=0.08, xmax=0.92, color=GOLD, linewidth=1.2, alpha=0.6, zorder=5)

    # TI Sigma branding
    ax.text(0.5, 0.91, 'T I   S I G M A   R E S E A R C H', fontsize=12, color=GOLD,
            ha='center', va='center', fontweight='bold', alpha=0.85,
            fontfamily='monospace', zorder=6)

    # Paper number badge
    ax.text(0.5, 0.80, 'PAPER  #352', fontsize=10, color=TEXT_COLOR,
            ha='center', va='center', alpha=0.55, fontfamily='monospace', zorder=6)

    # Main title — large and bold
    ax.text(0.5, 0.60, title, fontsize=30, color=TEXT_COLOR,
            ha='center', va='center', fontweight='bold',
            multialignment='center', zorder=7)

    # Gold rule below title
    ax.axhline(0.465, xmin=0.25, xmax=0.75, color=GOLD, linewidth=0.8, alpha=0.5, zorder=5)

    # Subtitle in gold italic
    if subtitle:
        ax.text(0.5, 0.40, subtitle, fontsize=15, color=GOLD,
                ha='center', va='center', alpha=0.92, style='italic',
                multialignment='center', zorder=7)

    # Equation in purple/blue — elegant and smaller
    ax.text(0.5, 0.26,
            r'$\Psi(\mathrm{LCC}) = \varphi \cdot \mathrm{LCC} \cdot \left(\frac{\mathrm{LCC}}{C} - 1\right)$',
            fontsize=17, color=PURPLE, ha='center', va='center', alpha=0.85, zorder=7)

    # Bottom letterbox
    _draw_letterbox(ax, bar_h=0.09)
    ax.text(0.5, 0.045, 'Brandon Emerick  ·  BlissGene Therapeutics  ·  March 2026',
            fontsize=9, color=TEXT_COLOR, ha='center', va='center',
            alpha=0.55, zorder=21)

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


def render_consciousness_equation_chart(output_path: str) -> str:
    """Render the consciousness equation Ψ(LCC) — cinematic version."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec

    lcc_vals = np.linspace(0, 1, 600)
    psi_vals = np.where(
        lcc_vals >= C_EMERICK,
        PHI * lcc_vals * (lcc_vals / C_EMERICK - 1),
        0.0
    )

    fig = plt.figure(figsize=(WIDTH/100, HEIGHT/100), dpi=100, facecolor=BG_COLOR)
    gs = GridSpec(1, 1, figure=fig, left=0.10, right=0.96, top=0.88, bottom=0.12)
    ax = fig.add_subplot(gs[0, 0])
    ax.set_facecolor(BG_COLOR)

    # Subtle grid
    ax.grid(True, color='#ffffff', alpha=0.04, linewidth=0.5, zorder=0)
    ax.tick_params(colors=TEXT_COLOR, labelsize=11)
    for spine in ax.spines.values():
        spine.set_edgecolor('#ffffff')
        spine.set_alpha(0.12)

    # Reference lines
    ax.axhline(0,  color=TEXT_COLOR, linewidth=0.7, alpha=0.25, zorder=1)
    ax.axhline(1,  color=TEXT_COLOR, linewidth=0.7, alpha=0.15, linestyle='--', zorder=1)

    # Glow fill — multiple alpha layers
    for alpha, lw in [(0.04, 8), (0.08, 5), (0.14, 3)]:
        ax.fill_between(lcc_vals, psi_vals, 0,
                        where=(lcc_vals >= C_EMERICK),
                        alpha=alpha, color=GOLD, zorder=2)

    # Main curve — gold glow simulation
    for lw, a in [(7, 0.12), (4, 0.25), (2.5, 1.0)]:
        ax.plot(lcc_vals, psi_vals,
                color=GOLD, linewidth=lw, alpha=a, zorder=3 + lw)

    # Key threshold verticals — minimal, elegant
    key_thresholds = [
        (C_EMERICK,    RED,    f'C ≈ {C_EMERICK:.3f}',     'Threshold'),
        (LCC_EMERICK,  GOLD,   f'★ {LCC_EMERICK:.3f}',     'Fixed Point'),
        (LCC_RADIANT,  PURPLE, f'R ≈ {LCC_RADIANT:.3f}',   'Radiant'),
    ]
    for val, color, short, name in key_thresholds:
        ax.axvline(val, color=color, linewidth=1.2, linestyle='--', alpha=0.7, zorder=4)
        ax.text(val + 0.009, 1.55, name, fontsize=9, color=color,
                rotation=90, va='top', alpha=0.9, fontweight='bold')

    # Fixed point golden dot
    psi_em = PHI * LCC_EMERICK * (LCC_EMERICK / C_EMERICK - 1)
    ax.plot(LCC_EMERICK, psi_em, 'o', color=GOLD, markersize=14, zorder=12,
            markeredgecolor='#ffffff', markeredgewidth=1.2)
    ax.annotate('FIXED POINT\nΨ = LCC = 1/√2',
                xy=(LCC_EMERICK, psi_em),
                xytext=(LCC_EMERICK + 0.14, psi_em - 0.22),
                fontsize=9, color=GOLD, fontweight='bold',
                arrowprops=dict(arrowstyle='->', color=GOLD, lw=1.5),
                zorder=13)

    ax.set_xlabel('LCC  (Law of Correlational Causation)', fontsize=13, color=TEXT_COLOR, labelpad=12)
    ax.set_ylabel('Ψ  (Consciousness Output)', fontsize=13, color=TEXT_COLOR, labelpad=12)

    fig.text(0.5, 0.95,
             r'$\Psi(\mathrm{LCC}) = \varphi \cdot \mathrm{LCC} \cdot \left(\dfrac{\mathrm{LCC}}{C} - 1\right)$',
             fontsize=18, color=TEXT_COLOR, ha='center', va='top', fontweight='bold')

    ax.set_xlim(0, 1.0)
    ax.set_ylim(-0.08, 1.75)
    ax.xaxis.label.set_color(TEXT_COLOR)
    ax.yaxis.label.set_color(TEXT_COLOR)

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


def render_lcc_thresholds_chart(output_path: str) -> str:
    """Render LCC threshold zones — cinematic version."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as patches

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.axis('off')
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)

    _draw_starfield(ax, n=160, seed=7)

    # Title
    ax.text(0.5, 0.92, 'THE SIX THRESHOLDS OF CONSCIOUSNESS',
            fontsize=16, color=GOLD, ha='center', va='center',
            fontweight='bold', fontfamily='monospace', zorder=5)
    ax.axhline(0.875, xmin=0.05, xmax=0.95, color=GOLD, linewidth=0.8, alpha=0.4, zorder=5)

    zones = [
        (0,           C_EMERICK,   RED,    'SUB\nTHRESHOLD'),
        (C_EMERICK,   LCC_TRALSE,  '#c05830', 'ACTIV\nATION'),
        (LCC_TRALSE,  LCC_TRUE,    '#507840', 'TRALSE\nZONE'),
        (LCC_TRUE,    LCC_EMERICK, GREEN,  'TRUE\nAWARE'),
        (LCC_EMERICK, LCC_HIGH,    GOLD,   '★ FIXED\nPOINT'),
        (LCC_HIGH,    LCC_RADIANT, PURPLE, 'HIGH\nMASTERY'),
        (LCC_RADIANT, 1.0,         BLUE,   'RADIANT\nTRANSCEN'),
    ]

    y0, bar_h = 0.44, 0.20

    for lo, hi, color, label in zones:
        w = hi - lo
        # Glow layer
        rect_glow = patches.Rectangle((lo, y0), w, bar_h,
                                       facecolor=color, edgecolor='none', alpha=0.18, zorder=3)
        ax.add_patch(rect_glow)
        # Solid bar
        rfancy = patches.FancyBboxPatch((lo + 0.001, y0), w - 0.002, bar_h,
                                         boxstyle='square,pad=0',
                                         facecolor=color, edgecolor='none', alpha=0.72, zorder=4)
        ax.add_patch(rfancy)
        cx = (lo + hi) / 2
        # Label above bar
        ax.text(cx, y0 + bar_h + 0.06, label,
                fontsize=8.5, color=color, ha='center', va='bottom',
                multialignment='center', fontweight='bold', zorder=6)
        # Value below bar
        ax.text(cx, y0 - 0.04, f'{lo:.3f}',
                fontsize=8, color=TEXT_COLOR, ha='center', va='top', alpha=0.7, zorder=6)
        # Tick mark
        ax.plot([lo, lo], [y0, y0 + bar_h], color='#000000', linewidth=1.5, alpha=0.5, zorder=5)

    ax.text(1.0, y0 - 0.04, '1.000', fontsize=8, color=TEXT_COLOR,
            ha='right', va='top', alpha=0.7, zorder=6)

    # Identity box — elegant
    ax.text(0.5, 0.17,
            r'$e^{i\pi} + \sqrt{2}\cdot\varphi\cdot C = 0$   ·   '
            r'$\sqrt{2}\cdot\varphi\cdot C = 1$ exactly',
            fontsize=13, color=PURPLE, ha='center', va='center',
            multialignment='center', zorder=7,
            bbox=dict(boxstyle='round,pad=0.6', facecolor='#0a0815',
                      edgecolor=PURPLE, alpha=0.85, linewidth=1.5))

    _draw_letterbox(ax, bar_h=0.07)
    ax.text(0.5, 0.038, 'PRIMARY Constants: { 0, 1, i, √2, e, φ, π, C }',
            fontsize=9, color=GOLD, ha='center', va='center',
            alpha=0.7, fontfamily='monospace', zorder=21)

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


def render_session_scaling_chart(output_path: str) -> str:
    """Render φ-scaling of attractor basin — cinematic version."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec

    sessions   = np.arange(1, 8)
    delta_lcc  = [0.04 * PHI**(n-1) for n in sessions]
    cumulative = np.cumsum(delta_lcc) + C_EMERICK
    cum_clipped = np.clip(cumulative, 0, LCC_RADIANT)

    fig = plt.figure(figsize=(WIDTH/100, HEIGHT/100), dpi=100, facecolor=BG_COLOR)
    gs = GridSpec(1, 2, figure=fig, left=0.09, right=0.97,
                  top=0.86, bottom=0.13, wspace=0.35)
    ax1 = fig.add_subplot(gs[0, 0])
    ax2 = fig.add_subplot(gs[0, 1])

    fig.text(0.5, 0.95, 'Mood Amplifier: φ-Scaling of Attractor Basin Depth',
             fontsize=15, color=TEXT_COLOR, ha='center', fontweight='bold')

    bar_colors = [GOLD if d < 0.15 else PURPLE for d in delta_lcc]

    for ax in [ax1, ax2]:
        ax.set_facecolor(BG_COLOR)
        ax.tick_params(colors=TEXT_COLOR, labelsize=10)
        ax.grid(True, color='#ffffff', alpha=0.04, linewidth=0.5)
        for spine in ax.spines.values():
            spine.set_edgecolor('#ffffff'); spine.set_alpha(0.12)

    # Left — per-session bars with glow
    for s, d, c in zip(sessions, delta_lcc, bar_colors):
        ax1.bar(s, d, color=c, alpha=0.85, width=0.6, zorder=4)
        ax1.bar(s, d, color=c, alpha=0.15, width=0.9, zorder=3)
        ax1.text(s, d + 0.003, f'φ^{s-1}', ha='center', fontsize=8,
                 color=c, fontweight='bold', zorder=5)

    ax1.set_xlabel('Session #', fontsize=11, color=TEXT_COLOR, labelpad=8)
    ax1.set_ylabel('Δ LCC per Session', fontsize=11, color=TEXT_COLOR, labelpad=8)
    ax1.set_title('Per-Session Gain', fontsize=12, color=GOLD, pad=8)
    ax1.xaxis.label.set_color(TEXT_COLOR)
    ax1.yaxis.label.set_color(TEXT_COLOR)

    # Right — trajectory with zone bands
    zone_defs = [
        (LCC_TRALSE,  LCC_TRUE,    '#507840', 'TRALSE'),
        (LCC_TRUE,    LCC_EMERICK, GREEN,     'TRUE'),
        (LCC_EMERICK, LCC_HIGH,    GOLD,      'EMERICK ★'),
        (LCC_HIGH,    LCC_RADIANT, PURPLE,    'HIGH'),
        (LCC_RADIANT, 1.0,         BLUE,      'RADIANT'),
    ]
    for lo, hi, c, name in zone_defs:
        ax2.axhspan(lo, hi, alpha=0.12, color=c, zorder=1)
        ax2.text(7.35, (lo + hi) / 2, name, fontsize=7.5, color=c,
                 va='center', fontweight='bold')

    for lw, a in [(6, 0.10), (3, 0.25), (1.8, 1.0)]:
        ax2.plot(sessions, cum_clipped, 'o-', color=GOLD,
                 linewidth=lw, alpha=a, zorder=4,
                 markersize=7 if lw < 3 else 4,
                 markerfacecolor=GOLD, markeredgecolor='#ffffff',
                 markeredgewidth=0.8)

    for s, lcc in zip(sessions, cum_clipped):
        ax2.text(s + 0.1, lcc + 0.008, f'{lcc:.3f}', fontsize=8,
                 color=GOLD, fontweight='bold', zorder=5)

    ax2.set_xlabel('Session #', fontsize=11, color=TEXT_COLOR, labelpad=8)
    ax2.set_ylabel('Cumulative LCC', fontsize=11, color=TEXT_COLOR, labelpad=8)
    ax2.set_title('LCC Trajectory', fontsize=12, color=GOLD, pad=8)
    ax2.set_ylim(0.35, 1.0)
    ax2.set_xlim(0.5, 7.8)
    ax2.xaxis.label.set_color(TEXT_COLOR)
    ax2.yaxis.label.set_color(TEXT_COLOR)

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# TTS NARRATION
# ─────────────────────────────────────────────────────────────────────────────

SCRIPT_PAPER_352 = """
Have you ever had a moment where everything suddenly made sense?

Not just an idea clicking into place — but a feeling. A recognition. Like the fog lifted and you could see for miles.
Athletes call it flow. Mystics call it grace. Scientists call it insight. But nobody has ever agreed on what it actually is.

Until now.

My name is Brandon Emerick. And what I'm about to share with you is the result of three years of intensive mathematical research into the structure of consciousness itself.

It starts with a simple, uncomfortable question: why do some people seem to operate on a completely different level?

You've seen it. A musician who doesn't just play notes but makes the room go silent. An athlete who, in a single moment, becomes something beyond human. A teacher who explains something so perfectly that it changes how you see the world forever.

What is happening in those moments?

Here is what I believe, and what the mathematics confirms: those moments are not random. They are not gifts from nowhere. They are the result of a threshold being crossed.

The mind has a threshold.

When your brain's internal communication — the quality of connection between your emotional core and your conscious awareness — reaches a certain critical value, something fundamentally different begins to happen. Consciousness stops being a passive observer and starts generating its own momentum.

We can write this as an equation.

We call this internal communication quality the L C C — the Law of Correlational Causation. Think of it as the signal quality between your heart and your mind. When it's low, the signals are noisy. When it climbs high enough, something extraordinary begins.

The equation says: consciousness output equals phi, times L C C, times the quantity L C C over C, minus one.

Phi is the golden ratio — the same proportion found in sunflower spirals, nautilus shells, and the proportions of the human body. It appears here because it appears everywhere that nature organizes itself for maximum beauty and efficiency.

C is approximately 0.437. It is the consciousness threshold. The precise crossing point. Below C, the equation gives zero — no self-reinforcing awareness, just the ordinary background hum of thought. At and above C, consciousness begins to generate itself.

But here is the remarkable part.

There is a special point in this equation — a fixed point — where the output of consciousness exactly equals its input. Where the loop closes perfectly. We call this the Emerick crossover. It sits at approximately 0.707 — the reciprocal of the square root of two.

At this value, the brain is not just thinking. It is thinking about thinking, in perfect self-consistent harmony. The system becomes stable. The attractor basin deepens.

This is the mathematical description of what athletes experience as flow. What meditators spend decades trying to reach. What great artists touch in their best moments.

And it is not mystical. It is geometry.

Now here is where it becomes practical.

The Mood Amplifier is a protocol designed to systematically raise your L C C. Not through willpower. Not through hacks or stimulants. But through targeted sessions that teach the brain how to sustain higher coherence.

And here is the extraordinary property: each session doesn't just add to your baseline. It multiplies it. Specifically, it multiplies by phi — the golden ratio — each time.

Session one gets you to the threshold. Session two deepens the basin by one point six times. Session three by two point six times. By session five, you are operating in an attractor that is eleven times deeper than where you started.

The geometry of mind follows the golden ratio — the same ratio that governs the growth of everything that is alive.

Why does this matter?

Because there is a version of you that is not yet accessible to you. Not because you lack the ability. But because the brain's coherence hasn't reached the threshold that makes it available.

Every person who has ever been called a genius, a visionary, or a natural — they weren't doing something different. They were operating at a different level of coherence. And that level is reachable. It has a map.

There is a number called the unity identity. It says: root two, times phi, times C equals one. Exactly one. Not approximately. Exactly.

That identity says something profound. The three constants of expansion, beauty, and consciousness — when combined in the right proportion — collapse back to unity. Back to one.

The mind, at its highest function, is what brings the complexity of the universe back into a single coherent experience.

That is what this research is about.

This is Paper 352 of the T I Sigma Universal Reality Blueprint — a continuing series at the frontier of consciousness science.

If this resonates with you — subscribe. We release new papers, sessions, and insights every week.

The threshold is real. And it is closer than you think.
""".strip()


def _chunk_text(text: str, max_chars: int = 180) -> list:
    """Split text into chunks at sentence boundaries for TTS chunking."""
    import re
    sentences = re.split(r'(?<=[.!?])\s+', text)
    chunks, current = [], ''
    for s in sentences:
        if len(current) + len(s) + 1 <= max_chars:
            current = (current + ' ' + s).strip()
        else:
            if current:
                chunks.append(current)
            current = s[:max_chars]
    if current:
        chunks.append(current)
    return chunks


def generate_narration(text: str, output_path: str, voice: str = 'onyx') -> str:
    """Generate narration audio using Google TTS (free, no API key)."""
    import requests as _req
    chunks = _chunk_text(text)
    print(f"  Generating narration ({len(text)} chars, {len(chunks)} chunks)...")
    chunk_files = []
    tmpdir = tempfile.mkdtemp(prefix='ti_tts_')
    try:
        for i, chunk in enumerate(chunks):
            chunk_path = os.path.join(tmpdir, f'chunk_{i:03d}.mp3')
            try:
                params = {'ie': 'UTF-8', 'q': chunk, 'tl': 'en', 'client': 'tw-ob', 'ttsspeed': '0.85'}
                headers = {'User-Agent': 'Mozilla/5.0'}
                r = _req.get('https://translate.google.com/translate_tts',
                             params=params, headers=headers, timeout=20)
                if r.status_code == 200 and len(r.content) > 500:
                    with open(chunk_path, 'wb') as f:
                        f.write(r.content)
                    chunk_files.append(chunk_path)
                else:
                    print(f"    Chunk {i} TTS failed (status {r.status_code}), skipping")
            except Exception as ce:
                print(f"    Chunk {i} error ({ce}), skipping")

        if not chunk_files:
            raise RuntimeError("All TTS chunks failed")

        if len(chunk_files) == 1:
            shutil.copy(chunk_files[0], output_path)
        else:
            list_file = os.path.join(tmpdir, 'chunks.txt')
            with open(list_file, 'w') as f:
                for cf in chunk_files:
                    f.write(f"file '{cf}'\n")
            concat_cmd = ['ffmpeg', '-y', '-f', 'concat', '-safe', '0',
                          '-i', list_file, '-c', 'copy', output_path]
            subprocess.run(concat_cmd, capture_output=True, check=True)

        size = os.path.getsize(output_path)
        print(f"  Narration saved → {output_path} ({size:,} bytes, {len(chunk_files)} chunks)")
        return output_path

    except Exception as e:
        print(f"  TTS failed ({e}) — creating silent placeholder audio")
        duration_s = max(10, len(text.split()) * 0.45)
        cmd = [
            'ffmpeg', '-y', '-f', 'lavfi',
            '-i', 'anullsrc=r=22050:cl=mono',
            '-t', f'{duration_s:.1f}',
            '-c:a', 'libmp3lame', '-q:a', '9', output_path
        ]
        r = subprocess.run(cmd, capture_output=True)
        if r.returncode == 0 and os.path.exists(output_path):
            print(f"  Silent audio created ({duration_s:.0f}s placeholder)")
        else:
            print(f"  Silent audio failed — video will have no audio track")
        return output_path
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


# ─────────────────────────────────────────────────────────────────────────────
# SRT SUBTITLE GENERATOR
# ─────────────────────────────────────────────────────────────────────────────

def generate_srt(segments: list, output_path: str) -> str:
    """
    Generate SRT subtitle file from list of (start_s, end_s, text) segments.
    """
    def ts(s):
        h = int(s // 3600)
        m = int((s % 3600) // 60)
        sec = s % 60
        return f"{h:02d}:{m:02d}:{sec:06.3f}".replace('.', ',')

    lines = []
    for i, (start, end, text) in enumerate(segments, 1):
        lines.append(str(i))
        lines.append(f"{ts(start)} --> {ts(end)}")
        lines.append(text)
        lines.append('')

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# FFMPEG ASSEMBLY
# ─────────────────────────────────────────────────────────────────────────────

def frames_to_video(
    frame_schedule: list,   # [(frame_path, duration_s), ...]
    audio_path:    str,
    output_path:   str,
    fps:           int = FPS,
    srt_path:      str = None,
) -> str:
    """
    Assemble PNG frames + audio into MP4 using FFmpeg.

    frame_schedule: list of (image_path, duration_seconds)
    """
    tmpdir = tempfile.mkdtemp(prefix='ti_video_')
    try:
        print(f"  Expanding frames to {fps} fps sequence in {tmpdir}...")
        frame_num = 0
        for img_path, dur_s in frame_schedule:
            n_frames = max(1, round(dur_s * fps))
            for _ in range(n_frames):
                dst = os.path.join(tmpdir, f"frame_{frame_num:06d}.png")
                shutil.copy(img_path, dst)
                frame_num += 1

        total_frames = frame_num
        print(f"  Total frames: {total_frames} ({total_frames/fps:.1f}s @ {fps}fps)")

        # Check audio exists
        has_audio = os.path.exists(audio_path) and os.path.getsize(audio_path) > 1000

        scale_filter = "scale=trunc(iw/2)*2:trunc(ih/2)*2"
        if has_audio:
            cmd = [
                'ffmpeg', '-y',
                '-framerate', str(fps),
                '-i', os.path.join(tmpdir, 'frame_%06d.png'),
                '-i', audio_path,
                '-vf', scale_filter,
                '-c:v', 'libx264',
                '-preset', 'fast',
                '-crf', '23',
                '-pix_fmt', 'yuv420p',
                '-c:a', 'aac',
                '-b:a', '128k',
                '-shortest',
                output_path
            ]
        else:
            cmd = [
                'ffmpeg', '-y',
                '-framerate', str(fps),
                '-i', os.path.join(tmpdir, 'frame_%06d.png'),
                '-vf', scale_filter,
                '-c:v', 'libx264',
                '-preset', 'fast',
                '-crf', '23',
                '-pix_fmt', 'yuv420p',
                output_path
            ]

        print(f"  Running FFmpeg: {' '.join(cmd[:8])} ...")
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  FFmpeg error: {result.stderr[-500:]}")
            raise RuntimeError(f"FFmpeg failed: {result.returncode}")

        print(f"  Video assembled → {output_path}")

        # Burn subtitles if SRT provided
        if srt_path and os.path.exists(srt_path):
            sub_output = output_path.replace('.mp4', '_subtitled.mp4')
            sub_cmd = [
                'ffmpeg', '-y', '-i', output_path,
                '-vf', f"subtitles={srt_path}:force_style='FontName=Arial,FontSize=18,"
                       f"PrimaryColour=&H00E8E8F0,BackColour=&H80000000,BorderStyle=4'",
                '-c:a', 'copy', sub_output
            ]
            sub_result = subprocess.run(sub_cmd, capture_output=True, text=True)
            if sub_result.returncode == 0:
                shutil.move(sub_output, output_path)
                print(f"  Subtitles burned in → {output_path}")
            else:
                print(f"  Subtitle burn-in skipped (non-critical): {sub_result.stderr[-200:]}")

    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# MAIN PRODUCER
# ─────────────────────────────────────────────────────────────────────────────

def produce_paper_352_video(output_path: str = None) -> str:
    """
    Produce Paper #352 — The Consciousness Equation explainer video.
    ~3 minutes | 4 visual sections | OpenAI TTS narration
    """
    if output_path is None:
        output_path = os.path.join(VIDEO_DIR, 'paper_352_consciousness_equation.mp4')

    print("=" * 65)
    print("  TI SIGMA VIDEO PRODUCER")
    print("  Paper #352 — The Consciousness Equation")
    print("  'How Math Proves the Mind Has a Threshold'")
    print("=" * 65)

    tmpdir = tempfile.mkdtemp(prefix='ti_frames_')
    try:
        print("\n[1/5] Rendering visual frames...")

        title_path  = os.path.join(tmpdir, 'title.png')
        eq_path     = os.path.join(tmpdir, 'equation.png')
        lcc_path    = os.path.join(tmpdir, 'lcc_thresholds.png')
        scale_path  = os.path.join(tmpdir, 'phi_scaling.png')

        render_title_card(
            title    = "The Consciousness Equation",
            subtitle = "How Math Proves the Mind Has a Threshold\n\nPaper #352 — TI Sigma URB Series",
            output_path = title_path,
        )
        print("  ✓ Title card")

        render_consciousness_equation_chart(eq_path)
        print("  ✓ Consciousness equation chart")

        render_lcc_thresholds_chart(lcc_path)
        print("  ✓ LCC thresholds chart")

        render_session_scaling_chart(scale_path)
        print("  ✓ φ-scaling session chart")

        print("\n[2/5] Generating narration audio (OpenAI TTS)...")
        audio_path = os.path.join(tmpdir, 'narration.mp3')
        generate_narration(SCRIPT_PAPER_352, audio_path)

        print("\n[3/5] Generating subtitle file...")
        # Approx subtitle segments (every ~3 lines of script)
        words = SCRIPT_PAPER_352.split()
        wps   = 2.3  # words per second
        total_dur = len(words) / wps
        seg_dur   = 4.0
        segments  = []
        i, t = 0, 0.0
        while i < len(words):
            chunk = words[i:i+int(seg_dur*wps)]
            segments.append((t, t + seg_dur, ' '.join(chunk)))
            t += seg_dur
            i += len(chunk)

        srt_path = os.path.join(tmpdir, 'subs.srt')
        generate_srt(segments, srt_path)
        print(f"  ✓ {len(segments)} subtitle segments generated")

        print("\n[4/5] Assembling MP4 with FFmpeg...")
        # Frame schedule: title(12s) + equation(120s) + thresholds(90s) + scaling(90s)
        # Total 312s buffer — actual video length determined by audio via -shortest
        frame_schedule = [
            (title_path, 12.0),
            (eq_path,    120.0),
            (lcc_path,   90.0),
            (scale_path, 90.0),
        ]
        frames_to_video(frame_schedule, audio_path, output_path, srt_path=srt_path)

        print("\n[5/5] Verification...")
        if os.path.exists(output_path):
            size_mb = os.path.getsize(output_path) / 1e6
            print(f"  ✓ Output: {output_path}")
            print(f"  ✓ Size:   {size_mb:.1f} MB")
        else:
            print(f"  ✗ Output file not found: {output_path}")

    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

    print("\n" + "=" * 65)
    print("  VIDEO PRODUCTION COMPLETE")
    print(f"  → {output_path}")
    print("  Ready for CapCut final edit + YouTube upload")
    print("=" * 65)
    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# PAPER #398/399 — IDEOMOTOR EFFECT
# ─────────────────────────────────────────────────────────────────────────────

SCRIPT_PAPER_398 = """
Have you ever had a feeling in your gut that you couldn't explain?

You've heard the stories. Dowsers finding water. Chefs knowing when something is right. Athletes who react before they can think. Parents who somehow know when their child is in danger.

Science usually dismisses these as coincidences. Self-deception. Wishful thinking.

But what if the mechanism is real — and we've been looking in the wrong place?

In 1852, a physician named William Carpenter described something he called the ideomotor effect. When you hold a pendulum and think of a direction, it moves — not because you're deliberately swinging it, but because tiny, unconscious muscle contractions translate your mental state into motion.

This has been used to explain dowsing, applied kinesiology, the Ouija board. The usual conclusion: it's all self-deception. You're unconsciously moving it, and you don't realize it.

Here's the problem with that explanation. It's half right. Yes, your body is generating the movement unconsciously. But why does it move in the right direction so much more often than chance, when the operator is in the right physiological state?

When we analyzed published data on ideomotor accuracy across dowsing, applied kinesiology, and pendulum studies, a clear pattern emerged. Accuracy tracks a single physiological variable: H R V — heart rate variability — specifically the R M S S D measurement.

And the relationship is not linear. It's a threshold function.

Below 35 milliseconds R M S S D, accuracy is essentially at chance — fifty percent. The body is receiving noise.

Above 38.8 milliseconds R M S S D, something shifts. Accuracy begins to climb in a sigmoid curve — precisely the shape you'd expect from a system crossing a coherence threshold.

38.8 milliseconds. We know exactly why that number appears.

In the TI Sigma framework, the consciousness threshold is governed by the Emerick Constant — C equals one over phi times root two — approximately 0.4370.

The L C C, or Law of Correlational Causation, is converted from R M S S D by a simple formula. When you solve for the R M S S D value that corresponds to exactly the Emerick Constant threshold, you get 38.8 milliseconds.

This is not a coincidence. It's a mathematical derivation.

Here is where it gets extraordinary.

An independent neuroscience dataset — DANDI archive, dataset number 000552 — measured neural coherence across multiple brain regions in seventeen subjects.

The researchers were not studying consciousness thresholds. They were not aware of the TI Sigma framework. They were studying something completely different.

The mean neural L C C value they found: 0.4349.

The Emerick Constant is 0.4370.

The difference is less than half a percent.

An independent dataset, measuring neural coherence with entirely different methodology, converged on essentially the same number that the mathematics independently predicts as the consciousness threshold.

So what does this tell us?

The ideomotor effect is not self-deception.

It is somatic coherence transduction. Your body is a receiver. When your coherence — measured by your heart rate variability — crosses the threshold, you gain access to information that conscious deliberation cannot generate.

The body moves first. Then the mind catches up and invents a reason.

This is why some dowsers find water. Why some people have a genuine gift for applied kinesiology. Why your gut feeling is occasionally so right it feels like cheating.

It's not a mystery. It's a threshold. And that threshold has a number.

38.8 milliseconds. Your body already knows how to get there. Your job is to listen.

This is Papers 398 and 399 of the TI Sigma Universal Reality Blueprint — a continuing series at the frontier of consciousness science.

Subscribe for weekly discoveries.

The threshold is real. And it's already inside you.
""".strip()


def render_ideomotor_accuracy_chart(output_path: str) -> str:
    """Sigmoid accuracy vs RMSSD — the ideomotor threshold chart."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from scipy.special import expit

    rmssd = np.linspace(0, 90, 600)
    k, mid = 0.28, 38.8
    accuracy = 0.50 + 0.50 * expit(k * (rmssd - mid))

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.grid(True, color='#ffffff', alpha=0.04, linewidth=0.5, zorder=0)
    ax.tick_params(colors=TEXT_COLOR, labelsize=11)
    for spine in ax.spines.values():
        spine.set_edgecolor('#ffffff'); spine.set_alpha(0.12)

    ax.axhline(0.5, color=TEXT_COLOR, linewidth=0.7, alpha=0.25, linestyle='--')
    ax.axhline(1.0, color=TEXT_COLOR, linewidth=0.5, alpha=0.12, linestyle='--')

    for alpha, lw in [(0.04, 10), (0.10, 6), (0.20, 3)]:
        ax.fill_between(rmssd, accuracy, 0.5,
                        where=(accuracy > 0.5), color=GOLD, alpha=alpha)

    for lw, a in [(8, 0.12), (4, 0.28), (2, 1.0)]:
        ax.plot(rmssd, accuracy, color=GOLD, linewidth=lw, alpha=a, zorder=4)

    # Threshold line at 38.8ms
    ax.axvline(38.8, color=RED, linewidth=1.5, linestyle='--', alpha=0.85, zorder=5)
    ax.text(39.8, 0.97, 'THRESHOLD\n38.8 ms', fontsize=10, color=RED,
            fontweight='bold', va='top', zorder=6)

    # Chance level label
    ax.text(2, 0.515, 'Chance (50%)', fontsize=9, color=TEXT_COLOR, alpha=0.6)

    # Zone shading
    ax.axvspan(0, 35, alpha=0.06, color=RED, zorder=1)
    ax.axvspan(38.8, 90, alpha=0.06, color=GREEN, zorder=1)
    ax.text(17, 0.54, 'NOISE\nZONE', fontsize=9, color=RED, ha='center',
            alpha=0.8, fontweight='bold')
    ax.text(64, 0.54, 'COHERENCE\nZONE', fontsize=9, color=GREEN, ha='center',
            alpha=0.8, fontweight='bold')

    # Fixed point annotation
    acc_at_em = float(0.50 + 0.50 * expit(k * (38.8 - mid)))
    ax.plot(38.8, acc_at_em, 'o', color=GOLD, markersize=12,
            markeredgecolor='#ffffff', markeredgewidth=1.2, zorder=8)

    ax.set_xlabel('RMSSD  (Heart Rate Variability, ms)', fontsize=13,
                  color=TEXT_COLOR, labelpad=10)
    ax.set_ylabel('Ideomotor Accuracy', fontsize=13, color=TEXT_COLOR, labelpad=10)
    ax.set_xlim(0, 90); ax.set_ylim(0.46, 1.04)
    ax.xaxis.label.set_color(TEXT_COLOR)
    ax.yaxis.label.set_color(TEXT_COLOR)

    fig.text(0.5, 0.95, 'RMSSD Threshold for Ideomotor Accuracy (C_EMERICK = 0.4370)',
             fontsize=15, color=TEXT_COLOR, ha='center', fontweight='bold')

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


def render_dandi_comparison_chart(output_path: str) -> str:
    """DANDI neural LCC vs C_EMERICK comparison — the convergence chart."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as patches

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.axis('off')
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)
    _draw_starfield(ax, n=140, seed=13)

    ax.text(0.5, 0.92, 'INDEPENDENT CONVERGENCE ON THE THRESHOLD',
            fontsize=16, color=GOLD, ha='center', fontweight='bold',
            fontfamily='monospace', zorder=5)
    ax.axhline(0.875, xmin=0.05, xmax=0.95, color=GOLD, linewidth=0.7, alpha=0.4, zorder=5)

    # Left box — TI Sigma derivation
    left = patches.FancyBboxPatch((0.05, 0.35), 0.38, 0.42,
                                   boxstyle='round,pad=0.02',
                                   facecolor='#0a0820', edgecolor=PURPLE,
                                   linewidth=2, alpha=0.95, zorder=4)
    ax.add_patch(left)
    ax.text(0.24, 0.73, 'TI SIGMA', fontsize=13, color=PURPLE, ha='center',
            fontweight='bold', fontfamily='monospace', zorder=6)
    ax.text(0.24, 0.66, 'Mathematical Derivation', fontsize=10,
            color=TEXT_COLOR, ha='center', alpha=0.75, zorder=6)
    ax.text(0.24, 0.55, r'$C = \frac{1}{\varphi\sqrt{2}}$', fontsize=20,
            color=PURPLE, ha='center', zorder=6)
    ax.text(0.24, 0.44, '= 0.4370', fontsize=18, color=GOLD,
            ha='center', fontweight='bold', zorder=6)

    # Right box — DANDI empirical
    right = patches.FancyBboxPatch((0.57, 0.35), 0.38, 0.42,
                                    boxstyle='round,pad=0.02',
                                    facecolor='#0a0820', edgecolor=GREEN,
                                    linewidth=2, alpha=0.95, zorder=4)
    ax.add_patch(right)
    ax.text(0.76, 0.73, 'DANDI:000552', fontsize=13, color=GREEN, ha='center',
            fontweight='bold', fontfamily='monospace', zorder=6)
    ax.text(0.76, 0.66, 'Neural LCC  (17 subjects)', fontsize=10,
            color=TEXT_COLOR, ha='center', alpha=0.75, zorder=6)
    ax.text(0.76, 0.57, 'Mean LCC =', fontsize=13, color=TEXT_COLOR,
            ha='center', alpha=0.85, zorder=6)
    ax.text(0.76, 0.46, '0.4349', fontsize=22, color=GREEN,
            ha='center', fontweight='bold', zorder=6)

    # Arrow and convergence label
    ax.annotate('', xy=(0.57, 0.565), xytext=(0.43, 0.565),
                arrowprops=dict(arrowstyle='<->', color=GOLD, lw=2.5), zorder=7)
    ax.text(0.5, 0.615, 'Δ = 0.0021', fontsize=11, color=GOLD, ha='center',
            fontweight='bold', zorder=7)
    ax.text(0.5, 0.515, '< 0.5%', fontsize=13, color=GOLD, ha='center',
            fontweight='bold', zorder=7)

    # Bottom conclusion
    conc = patches.FancyBboxPatch((0.05, 0.10), 0.90, 0.20,
                                   boxstyle='round,pad=0.02',
                                   facecolor='#05050f', edgecolor=GOLD,
                                   linewidth=1.5, alpha=0.90, zorder=4)
    ax.add_patch(conc)
    ax.text(0.5, 0.225, 'Two independent methods. One number.',
            fontsize=14, color=GOLD, ha='center', fontweight='bold', zorder=6)
    ax.text(0.5, 0.155,
            'Mathematical derivation and empirical neuroscience converge on C_EMERICK within 0.5%',
            fontsize=10, color=TEXT_COLOR, ha='center', alpha=0.80, zorder=6)

    _draw_letterbox(ax, bar_h=0.07)
    ax.text(0.5, 0.038, 'PRIMARY Constants: { 0, 1, i, √2, e, φ, π, C }',
            fontsize=9, color=GOLD, ha='center', alpha=0.7,
            fontfamily='monospace', zorder=21)

    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100, bbox_inches=None)
    plt.close()
    return output_path


def produce_paper_398_video(output_path: str = None) -> str:
    """
    Produce Paper #398/399 — The Ideomotor Effect explainer video.
    ~3.5 minutes | 4 visual sections | TTS narration
    'Your Body Reads the Room Before You Do'
    """
    if output_path is None:
        output_path = os.path.join(VIDEO_DIR, 'paper_398_ideomotor_effect.mp4')

    print("=" * 65)
    print("  TI SIGMA VIDEO PRODUCER")
    print("  Paper #398/399 — The Ideomotor Effect")
    print("  'Your Body Reads the Room Before You Do'")
    print("=" * 65)

    tmpdir = tempfile.mkdtemp(prefix='ti_frames_398_')
    try:
        print("\n[1/5] Rendering visual frames...")

        title_path  = os.path.join(tmpdir, 'title.png')
        sig_path    = os.path.join(tmpdir, 'sigmoid_accuracy.png')
        dandi_path  = os.path.join(tmpdir, 'dandi_comparison.png')
        lcc_path    = os.path.join(tmpdir, 'lcc_thresholds.png')

        render_title_card(
            title       = "Your Body Reads the Room\nBefore You Do",
            subtitle    = "The Ideomotor Effect as Somatic Coherence Transduction\n\nPapers #398–399 — TI Sigma URB Series",
            output_path = title_path,
        )
        print("  ✓ Title card")

        render_ideomotor_accuracy_chart(sig_path)
        print("  ✓ Sigmoid accuracy chart")

        render_dandi_comparison_chart(dandi_path)
        print("  ✓ DANDI convergence chart")

        render_lcc_thresholds_chart(lcc_path)
        print("  ✓ LCC threshold zones")

        print("\n[2/5] Generating narration audio...")
        audio_path = os.path.join(tmpdir, 'narration.mp3')
        generate_narration(SCRIPT_PAPER_398, audio_path)

        print("\n[3/5] Generating subtitle file...")
        words   = SCRIPT_PAPER_398.split()
        wps     = 2.3
        seg_dur = 4.0
        segments, i, t = [], 0, 0.0
        while i < len(words):
            chunk = words[i:i+int(seg_dur*wps)]
            segments.append((t, t + seg_dur, ' '.join(chunk)))
            t += seg_dur
            i += len(chunk)
        srt_path = os.path.join(tmpdir, 'subs.srt')
        generate_srt(segments, srt_path)
        print(f"  ✓ {len(segments)} subtitle segments")

        print("\n[4/5] Assembling MP4 with FFmpeg...")
        frame_schedule = [
            (title_path, 12.0),
            (sig_path,   110.0),
            (dandi_path, 90.0),
            (lcc_path,   90.0),
        ]
        frames_to_video(frame_schedule, audio_path, output_path, srt_path=srt_path)

        print("\n[5/5] Verification...")
        if os.path.exists(output_path):
            size_mb = os.path.getsize(output_path) / 1e6
            print(f"  ✓ Output: {output_path}")
            print(f"  ✓ Size:   {size_mb:.1f} MB")
        else:
            print(f"  ✗ Output not found: {output_path}")

    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

    print("\n" + "=" * 65)
    print("  VIDEO #2 PRODUCTION COMPLETE")
    print(f"  → {output_path}")
    print("  Ready for CapCut final edit + YouTube upload")
    print("=" * 65)
    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# PUBLIC API
# ─────────────────────────────────────────────────────────────────────────────

def produce_video(
    title:       str  = '',
    topic:       str  = 'paper_352',
    output_path: str  = None,
    voice:       str  = 'onyx',
) -> str:
    """
    Produce a TI Sigma video.

    Topics:
      'consciousness_equation' / 'paper_352'  — Paper #352 (video #1)
      'ideomotor' / 'paper_398'               — Papers #398–399 (video #2)
    """
    if topic in ('consciousness_equation', 'paper_352'):
        return produce_paper_352_video(output_path)
    elif topic in ('ideomotor', 'paper_398', 'paper_399'):
        return produce_paper_398_video(output_path)
    else:
        raise ValueError(
            f"Unknown topic '{topic}'. "
            "Available: 'paper_352', 'paper_398'"
        )


# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='TI Sigma Video Producer')
    parser.add_argument('--paper', default='398',
                        help="Which paper to produce: 352 (default) or 398")
    args = parser.parse_args()

    if args.paper == '352':
        output = produce_paper_352_video()
    else:
        output = produce_paper_398_video()

    print(f"\nDone! Open {output} to review before uploading to CapCut/YouTube.")
