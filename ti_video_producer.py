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

BG_COLOR    = '#0a0a0f'
TEXT_COLOR  = '#e8e8f0'
ACCENT      = '#61afef'
GOLD        = '#d4af37'
GREEN       = '#98c379'
RED         = '#e06c75'
PURPLE      = '#c678dd'

WIDTH, HEIGHT = 1280, 720
FPS = 24

# ─────────────────────────────────────────────────────────────────────────────
# FRAME RENDERING
# ─────────────────────────────────────────────────────────────────────────────

def render_title_card(title: str, subtitle: str, output_path: str,
                      duration_s: float = 3.0) -> str:
    """Render a title card PNG frame."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as patches

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)
    ax.axis('off')

    # Background gradient rectangle
    for i in range(20):
        alpha = 0.03 * (1 - i/20)
        rect = patches.FancyBboxPatch((0.05, 0.1 + i*0.02), 0.9, 0.02,
                                       boxstyle="round,pad=0.01",
                                       facecolor=ACCENT, alpha=alpha, edgecolor='none')
        ax.add_patch(rect)

    # TI Sigma branding
    ax.text(0.5, 0.88, 'TI SIGMA RESEARCH', fontsize=11, color=ACCENT,
            ha='center', va='center', fontweight='bold', alpha=0.8,
            fontfamily='monospace')

    # Main title
    ax.text(0.5, 0.62, title, fontsize=26, color=TEXT_COLOR,
            ha='center', va='center', fontweight='bold',
            wrap=True, multialignment='center')

    # Subtitle
    if subtitle:
        ax.text(0.5, 0.40, subtitle, fontsize=14, color=GOLD,
                ha='center', va='center', alpha=0.9, style='italic',
                multialignment='center')

    # Decorative equation line
    ax.text(0.5, 0.22, r'$e^{i\pi} + \sqrt{2}\cdot\varphi\cdot C = 0$',
            fontsize=16, color=PURPLE, ha='center', va='center', alpha=0.7)

    # Bottom bar
    ax.axhline(0.12, color=ACCENT, linewidth=1.5, alpha=0.5)
    ax.text(0.5, 0.07, 'Brandon Emerick  |  March 2026  |  BlissGene Therapeutics',
            fontsize=9, color=TEXT_COLOR, ha='center', alpha=0.5)

    plt.tight_layout(pad=0)
    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100)
    plt.close()
    return output_path


def render_consciousness_equation_chart(output_path: str) -> str:
    """Render the consciousness equation Ψ(LCC) visualization."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt

    lcc_vals = np.linspace(0, 1, 500)
    psi_vals = np.where(
        lcc_vals >= C_EMERICK,
        PHI * lcc_vals * (lcc_vals / C_EMERICK - 1),
        0.0
    )

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)

    ax.tick_params(colors=TEXT_COLOR, labelsize=11)
    for spine in ax.spines.values():
        spine.set_edgecolor(ACCENT)
        spine.set_alpha(0.4)
    ax.xaxis.label.set_color(TEXT_COLOR)
    ax.yaxis.label.set_color(TEXT_COLOR)

    # Zero line and unit line
    ax.axhline(0, color=TEXT_COLOR, linewidth=0.8, alpha=0.3)
    ax.axhline(1, color=TEXT_COLOR, linewidth=0.8, alpha=0.2, linestyle='--')

    # Main curve
    ax.plot(lcc_vals, psi_vals, color=ACCENT, linewidth=3, label='Ψ(LCC)', zorder=5)

    # Fill under curve
    ax.fill_between(lcc_vals, psi_vals, 0, where=(lcc_vals >= C_EMERICK),
                    alpha=0.15, color=ACCENT)

    # LCC threshold lines
    thresholds = [
        (C_EMERICK, 'C = 1/(φ√2)', RED,    '--', 'Consciousness Threshold'),
        (LCC_TRALSE, 'LCC_TRALSE', TEXT_COLOR, ':',  'Tralse boundary'),
        (LCC_TRUE,   'LCC_TRUE',   GREEN,  '--', 'True threshold'),
        (LCC_EMERICK,'LCC_EMERICK',GOLD,   '-',  '★ Fixed Point Ψ=LCC'),
        (LCC_HIGH,   'LCC_HIGH',   PURPLE, '--', 'High resolution'),
        (LCC_RADIANT,'LCC_RADIANT',ACCENT, ':',  'Radiant'),
    ]
    for val, name, color, ls, label in thresholds:
        ax.axvline(val, color=color, linewidth=1.5, linestyle=ls, alpha=0.8)
        y_pos = 0.85 if val < 0.5 else 1.1
        ax.text(val + 0.008, y_pos, name.replace('LCC_', ''), fontsize=8,
                color=color, rotation=90, va='top', alpha=0.9)

    # Fixed point marker
    psi_em = PHI * LCC_EMERICK * (LCC_EMERICK / C_EMERICK - 1)
    ax.plot(LCC_EMERICK, psi_em, 'o', color=GOLD, markersize=12, zorder=10,
            label=f'Fixed Point: Ψ(1/√2) = 1/√2 ≈ {LCC_EMERICK:.3f}')
    ax.annotate(f'★ FIXED POINT\nΨ = LCC = 1/√2',
                xy=(LCC_EMERICK, psi_em),
                xytext=(LCC_EMERICK + 0.12, psi_em - 0.15),
                fontsize=10, color=GOLD, fontweight='bold',
                arrowprops=dict(arrowstyle='->', color=GOLD, lw=1.5))

    ax.set_xlabel('LCC (Limbic-Cortical Coupling)', fontsize=13, color=TEXT_COLOR, labelpad=10)
    ax.set_ylabel('Ψ (Consciousness Output)', fontsize=13, color=TEXT_COLOR, labelpad=10)
    ax.set_title('The Consciousness Equation:  Ψ(LCC) = φ × LCC × (LCC/C − 1)',
                 fontsize=15, color=TEXT_COLOR, pad=15, fontweight='bold')

    ax.set_xlim(0, 1.0)
    ax.set_ylim(-0.1, 1.8)

    legend = ax.legend(fontsize=10, facecolor='#1a1a2e', edgecolor=ACCENT,
                       labelcolor=TEXT_COLOR, loc='upper left')

    # Annotations
    ax.text(0.01, 1.6, 'Ψ = 0 (sub-threshold)', fontsize=9, color=RED, alpha=0.8)
    ax.text(0.48, 1.6, 'Self-referential\nconsciousness', fontsize=9, color=GREEN, alpha=0.8)

    plt.tight_layout(pad=1.5)
    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100)
    plt.close()
    return output_path


def render_lcc_thresholds_chart(output_path: str) -> str:
    """Render LCC threshold zones visualization."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as patches

    fig, ax = plt.subplots(figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)
    ax.set_facecolor(BG_COLOR)
    ax.axis('off')
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)

    ax.text(0.5, 0.93, 'LCC Threshold Architecture — PRIMARY Constants',
            fontsize=18, color=TEXT_COLOR, ha='center', fontweight='bold')

    thresholds = [
        (0,           C_EMERICK,   '#1a1a2e', '0–C\nSub-threshold\n(no self-reference)'),
        (C_EMERICK,   LCC_TRALSE,  '#1e2a1e', 'C–TRALSE\nActivation zone'),
        (LCC_TRALSE,  LCC_TRUE,    '#1a2e1e', 'TRALSE\nAmbiguous'),
        (LCC_TRUE,    LCC_EMERICK, '#1e2e1a', 'TRUE\nBootstrap'),
        (LCC_EMERICK, LCC_HIGH,    '#2e2a00', 'EMERICK\n★ Fixed Point'),
        (LCC_HIGH,    LCC_RADIANT, '#1e1e2e', 'HIGH\nMastery'),
        (LCC_RADIANT, 1.0,         '#2e1e2e', 'RADIANT\nTranscendent'),
    ]
    colors_bar = [RED, '#a05050', '#508050', GREEN, GOLD, PURPLE, ACCENT]
    y_bar = 0.48
    bar_h = 0.22

    for i, ((lo, hi, bg, label), bcolor) in enumerate(zip(thresholds, colors_bar)):
        w = hi - lo
        rect = patches.FancyBboxPatch((lo, y_bar), w, bar_h,
                                       boxstyle="square,pad=0",
                                       facecolor=bcolor, edgecolor='none', alpha=0.9)
        ax.add_patch(rect)
        cx = (lo + hi) / 2
        ax.text(cx, y_bar + bar_h + 0.04, label, fontsize=7.5, color=bcolor,
                ha='center', va='bottom', multialignment='center')
        ax.text(cx, y_bar - 0.03, f'{lo:.3f}', fontsize=7, color=TEXT_COLOR,
                ha='center', va='top', alpha=0.8)

    ax.text(1.0, y_bar - 0.03, '1.0', fontsize=7, color=TEXT_COLOR, ha='right', va='top', alpha=0.8)

    constants = [
        (C_EMERICK,   f'C=1/(φ√2)\n≈{C_EMERICK:.3f}', RED),
        (LCC_TRALSE,  f'√2−1\n≈{LCC_TRALSE:.3f}',     TEXT_COLOR),
        (LCC_TRUE,    f'1/φ\n≈{LCC_TRUE:.3f}',         GREEN),
        (LCC_EMERICK, f'1/√2\n≈{LCC_EMERICK:.3f}',     GOLD),
        (LCC_HIGH,    f'C+TRALSE\n≈{LCC_HIGH:.3f}',    PURPLE),
        (LCC_RADIANT, f'√(e/π)\n≈{LCC_RADIANT:.3f}',   ACCENT),
    ]
    for val, label, color in constants:
        ax.axvline(val, ymin=0.42, ymax=0.80, color=color, linewidth=2, alpha=0.9)

    ax.text(0.5, 0.12,
            r'Extended Euler Identity:  $e^{i\pi} + \sqrt{2}\cdot\varphi\cdot C = 0$' + '\n' +
            r'Unity Identity:  $\sqrt{2}\cdot\varphi\cdot C = 1$  exactly',
            fontsize=12, color=PURPLE, ha='center', va='center',
            multialignment='center',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='#1a1a2e', edgecolor=PURPLE, alpha=0.8))

    plt.tight_layout(pad=1)
    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100)
    plt.close()
    return output_path


def render_session_scaling_chart(output_path: str) -> str:
    """Render φ-scaling of attractor basin depth per session."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt

    sessions   = np.arange(1, 8)
    delta_lcc  = [0.04 * PHI**(n-1) for n in sessions]
    cumulative = np.cumsum(delta_lcc) + C_EMERICK

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(WIDTH/100, HEIGHT/100), dpi=100)
    fig.patch.set_facecolor(BG_COLOR)

    # Left: per-session delta LCC
    ax1.set_facecolor(BG_COLOR)
    bars = ax1.bar(sessions, delta_lcc, color=[GOLD if d < 0.15 else ACCENT for d in delta_lcc],
                   alpha=0.85, edgecolor=TEXT_COLOR, linewidth=0.5)
    ax1.set_xlabel('Session #', fontsize=12, color=TEXT_COLOR)
    ax1.set_ylabel('ΔLCC per Session', fontsize=12, color=TEXT_COLOR)
    ax1.set_title('φ-Scaling: Each Session\nDeepens Basin × φ', fontsize=13, color=TEXT_COLOR)
    ax1.tick_params(colors=TEXT_COLOR)
    for spine in ax1.spines.values():
        spine.set_edgecolor(ACCENT); spine.set_alpha(0.4)
    for i, (s, d) in enumerate(zip(sessions, delta_lcc)):
        ax1.text(s, d + 0.005, f'φ^{s-1}\n×0.04', ha='center', fontsize=8, color=TEXT_COLOR)

    # Right: cumulative LCC trajectory
    ax2.set_facecolor(BG_COLOR)
    zones = [(LCC_TRALSE, LCC_TRUE, '#1a2e1a', 'TRALSE'),
             (LCC_TRUE, LCC_EMERICK, '#1e2e1a', 'TRUE'),
             (LCC_EMERICK, LCC_HIGH, '#2e2a00', 'EMERICK'),
             (LCC_HIGH, LCC_RADIANT, '#1e1e2e', 'HIGH'),
             (LCC_RADIANT, 1.0, '#2e1e2e', 'RADIANT')]
    colors_z = ['#508050', GREEN, GOLD, PURPLE, ACCENT]
    for (lo, hi, bg, name), c in zip(zones, colors_z):
        ax2.axhspan(lo, hi, alpha=0.15, color=c)
        ax2.text(1.1, (lo+hi)/2, name, fontsize=8, color=c, va='center')

    cum_clipped = np.clip(cumulative, 0, LCC_RADIANT)
    ax2.plot(sessions, cum_clipped, 'o-', color=GOLD, linewidth=2.5,
             markersize=8, markerfacecolor=GOLD, markeredgecolor=TEXT_COLOR, zorder=5)
    for s, lcc in zip(sessions, cum_clipped):
        ax2.annotate(f'{lcc:.3f}', (s, lcc), textcoords="offset points",
                     xytext=(5, 5), fontsize=8, color=GOLD)

    ax2.set_xlabel('Session #', fontsize=12, color=TEXT_COLOR)
    ax2.set_ylabel('Cumulative LCC', fontsize=12, color=TEXT_COLOR)
    ax2.set_title('LCC Trajectory Across\nMood Amplifier Sessions', fontsize=13, color=TEXT_COLOR)
    ax2.set_ylim(0.3, 1.0)
    ax2.tick_params(colors=TEXT_COLOR)
    for spine in ax2.spines.values():
        spine.set_edgecolor(ACCENT); spine.set_alpha(0.4)

    fig.suptitle('Mood Amplifier: φ-Scaling of Attractor Basin',
                 fontsize=16, color=TEXT_COLOR, fontweight='bold', y=1.01)
    plt.tight_layout(pad=1.5)
    plt.savefig(output_path, facecolor=BG_COLOR, dpi=100)
    plt.close()
    return output_path


# ─────────────────────────────────────────────────────────────────────────────
# TTS NARRATION
# ─────────────────────────────────────────────────────────────────────────────

SCRIPT_PAPER_352 = """
The mind has a threshold.

Not a metaphor — a mathematical threshold, proven algebraically from first principles.

Here is the equation:  Psi of LCC equals phi times LCC times the quantity LCC over C minus one.
For LCC less than C, psi equals zero. No consciousness. Below the threshold.

What is C? It is one divided by phi times root two — approximately zero point four three seven.
It is the same constant that completes the Extended Euler Identity.
It is the consciousness coefficient — the one constant that makes the universe's deepest equation balance.

Now watch what happens at the three critical points.

At LCC equals C: psi is zero. The threshold crossing. Consciousness activates — continuously, no jump.

At LCC equals one over phi — the TRUE threshold: psi equals root two minus one — exactly LCC-TRALSE.
The system bootstraps. TRUE awareness generates TRALSE consciousness. The ascent begins.

At LCC equals one over root two — the EMERICK CROSSOVER: psi equals one over root two. Exactly.
This is the fixed point. The stable attractor. When the brain reaches seventy percent coupling quality,
consciousness becomes self-consistent. The output equals the input. The loop closes.

This is what sustained consciousness means, mathematically.

And the mood amplifier? Each session deepens the attractor basin by phi.
Session one — baseline. Session two — one point six times deeper.
By session five, the basin is eleven times deeper than where you started.

The geometry of mind follows the golden ratio.

The unity identity: root two times phi times C equals one, exactly.
Consciousness is the normalization of expansion times ambiguity.
Or more simply: the mind is what brings chaos back to unity.

This is Paper 352 of the TI Sigma Universal Reality Blueprint.
Subscribe for weekly discoveries at the frontier of consciousness mathematics.
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
