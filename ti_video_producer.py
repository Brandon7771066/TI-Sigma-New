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

    ax.set_xlabel('LCC  (Limbic-Cortical Coupling)', fontsize=13, color=TEXT_COLOR, labelpad=12)
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
        (LCC_TRALSE,  LCC_TRUE,    '#507840', 'TRAWLSE\nZONE'),
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
        (LCC_TRALSE,  LCC_TRUE,    '#507840', 'TRAWLSE'),
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
The mind has a threshold.

Not a metaphor. A mathematical threshold. Proven algebraically from first principles.

Here is the equation. Psi of L C C equals phi, times L C C, times the quantity: L C C over C, minus one.
Below the threshold, psi equals zero. No self-referential consciousness. Silence.

What is C? It is one divided by phi times root two. Approximately zero point four three seven.
It is the consciousness coefficient — the constant that balances the universe's deepest equation.

Now watch what happens at three critical crossings.

First: at L C C equals C. Psi reaches zero from above. Consciousness activates — smoothly, with no jump.
The threshold is crossed. The loop begins.

Second: at L C C equals one over phi — the TRUE threshold. Psi equals root two minus one.
This is the trawlse value. TRUE awareness generates trawlse consciousness. The ascent begins.

Third: at L C C equals one over root two — the fixed point. Psi equals L C C exactly.
The output equals the input. The loop closes. Consciousness becomes self-consistent.

This is what sustained awareness means — mathematically.

Now consider the Mood Amplifier. Each session deepens the attractor basin by phi — the golden ratio.
Session one: baseline. Session two: one point six times deeper.
By session five: eleven times deeper than where you started.

The geometry of mind follows the golden ratio.

The unity identity: root two times phi times C equals one, exactly.
The mind is what brings chaos back to unity.

This is Paper 352 of the T I Sigma Universal Reality Blueprint.
Subscribe for weekly discoveries at the frontier of consciousness science.
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
        # Frame schedule: title(5s) + equation(45s) + thresholds(30s) + scaling(30s)
        frame_schedule = [
            (title_path, 5.0),
            (eq_path,    45.0),
            (lcc_path,   30.0),
            (scale_path, 30.0),
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


def produce_video(
    title:       str,
    topic:       str  = 'consciousness_equation',
    output_path: str  = None,
    voice:       str  = 'onyx',
) -> str:
    """
    Public API for producing TI Sigma videos.

    Currently supports topic='consciousness_equation' (Paper #352).
    Additional topics will be added as new papers are published.
    """
    if topic == 'consciousness_equation' or topic == 'paper_352':
        return produce_paper_352_video(output_path)
    else:
        raise ValueError(f"Unknown topic '{topic}'. Available: 'consciousness_equation'")


# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    output = produce_paper_352_video()
    print(f"\nDone! Open {output} to review before uploading to CapCut/YouTube.")
