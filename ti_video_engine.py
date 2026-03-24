"""
TI Sigma Video Engine — Universal URB-to-MP4 Pipeline
======================================================

Takes ANY URB markdown file → produces a YouTube-ready MP4.

Pipeline:
  1. AI script generation (Claude or OpenAI) — casual, engaging, general audience
  2. Slide layout planning — 6-8 visual segments
  3. Frame rendering (Matplotlib + Pillow) — cinematic dark theme
  4. TTS narration (OpenAI tts-1, voice=onyx) — segment by segment
  5. FFmpeg assembly → MP4 + thumbnail PNG

Usage:
    from ti_video_engine import produce_urb_video
    result = produce_urb_video("papers/URB_MINIMAL_OPERATIONS_507.md")
    # Returns: {"mp4": "...", "thumbnail": "...", "title": "...", "description": "..."}
"""

import os
import re
import sys
import math
import time
import json
import shutil
import tempfile
import textwrap
import subprocess
import numpy as np
from pathlib import Path
from typing import Dict, List, Optional, Any

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS & STYLE
# ─────────────────────────────────────────────────────────────────────────────

PHI      = (1 + math.sqrt(5)) / 2
SQRT2    = math.sqrt(2)
C_EMERICK = 1 / (PHI * SQRT2)

VIDEO_DIR  = Path("videos")
THUMB_DIR  = Path("videos/thumbnails")
SCRIPT_DIR = Path("scripts")
for d in [VIDEO_DIR, THUMB_DIR, SCRIPT_DIR]:
    d.mkdir(exist_ok=True)

BG      = "#05050f"
TEXT    = "#f0f0fa"
GOLD    = "#ffd700"
ACCENT  = "#c8a000"
PURPLE  = "#a06ce0"
BLUE    = "#4090d0"
GREEN   = "#52c77a"
RED     = "#e05060"
DIM     = "#888899"

WIDTH, HEIGHT = 1280, 720
FPS = 24
FFMPEG = shutil.which("ffmpeg") or "ffmpeg"


# ─────────────────────────────────────────────────────────────────────────────
# VIDEO CATALOGUE — Pre-defined entries for known URBs
# ─────────────────────────────────────────────────────────────────────────────

VIDEO_CATALOGUE = {
    509: {
        "title": "Everything Is a Contradiction — and That's Actually Good",
        "subtitle": "URB #509 · TI Sigma Theory of Contradictions",
        "hook": "What if the thing you were taught to avoid is actually the engine of all reality?",
        "tags": ["philosophy", "consciousness", "logic", "tralse", "contradictions",
                 "TI sigma", "reality", "existence"],
        "description_template": (
            "Every philosophical tradition tells you to avoid contradictions. "
            "But what if contradiction is the most fundamental feature of existence — "
            "not a bug, but the actual structure of reality?\n\n"
            "In this video we break down TI Sigma's Theory of Contradictions: "
            "the 5 arguments for why EVERYTHING is contradictory, the 4 fundamental "
            "features of existence, and the taxonomy of Double Tralse — the only "
            "four types of thinking that genuinely fail.\n\n"
            "DOI: https://doi.org/10.5281/zenodo.19207717\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    508: {
        "title": "Does Healing Energy Store in Water or Crystals? A Physicist Answers",
        "subtitle": "URB #508 · Bengston Protocol + Quartz Storage",
        "hook": "Bengston's experiments on cancer remission are real — so where does the energy go?",
        "tags": ["healing", "energy medicine", "quartz", "water", "consciousness",
                 "Bengston", "piezoelectric", "quantum biology"],
        "description_template": (
            "William Bengston's experiments produced measurable cancer remissions "
            "in mice — dozens of times, in controlled settings. The effect is real. "
            "But nobody knows the mechanism. Today we use the TI Sigma framework "
            "to answer: where does the healing information go — water or quartz?\n\n"
            "Spoiler: quartz wins, and the reason involves piezoelectricity, "
            "the golden ratio, and a testable prediction at 4.812 Hz.\n\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    507: {
        "title": "The 6 Building Blocks of All Mathematics (Remove One and Math Collapses)",
        "subtitle": "URB #507 · The Minimal Basis",
        "hook": "You can build every single thing in mathematics from just 6 elements. Take one away and it all falls apart.",
        "tags": ["mathematics", "foundations", "imaginary numbers", "phi", "golden ratio",
                 "TI sigma", "minimal basis", "consciousness"],
        "description_template": (
            "What are the absolute minimum ingredients needed to build all of mathematics? "
            "Not the entire toolbox — just the essentials that everything else reduces to.\n\n"
            "The answer is six things: the imaginary unit i, addition, subtraction, "
            "multiplication, division, and the concept of a limit. "
            "Every function — logarithm, cosine, arctangent — collapses to these six. "
            "And there's one number that's special in a way no other is: √2.\n\n"
            "DOI: https://doi.org/10.5281/zenodo.19207374\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    506: {
        "title": "What If One Number Is the Source of All Mathematics?",
        "subtitle": "URB #506 · The i-Completeness Theorem",
        "hook": "The imaginary number i — the one your teacher said wasn't real — might derive every constant in existence.",
        "tags": ["mathematics", "imaginary numbers", "i-completeness", "golden ratio",
                 "euler", "constants", "TI sigma"],
        "description_template": (
            "Eight numbers appear over and over in physics, math, and nature: "
            "0, 1, i, √2, e, φ, π, and C. They show up in quantum mechanics, "
            "in the structure of DNA, in the spiral of a galaxy.\n\n"
            "URB #506 proves they are ALL derivable from a single source: i. "
            "The imaginary number. The one that 'doesn't exist.'\n\n"
            "DOI: https://doi.org/10.5281/zenodo.19207370\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    505: {
        "title": "The Math Behind 'Let Go and Let God' — and Why It Actually Works",
        "subtitle": "URB #505 · Unified Telekinesis Equation",
        "hook": "Every spiritual tradition says the same thing: detach from the outcome. Turns out, there's an equation for it.",
        "tags": ["consciousness", "intention", "letting go", "telekinesis", "LCC",
                 "TI sigma", "spirituality", "quantum"],
        "description_template": (
            "Why does every spiritual tradition — from wu wei to 'let go and let God' "
            "to detachment from outcomes — say the same thing? Is it just good advice, "
            "or is there a structural reason?\n\n"
            "URB #505 shows there is. The Unified Telekinesis Equation contains a "
            "Release Axiom: dividing by i is mathematically required to convert "
            "stored coherence into physical effect. You cannot hold the outcome "
            "and manifest it simultaneously — the math forbids it.\n\n"
            "DOI: https://doi.org/10.5281/zenodo.19207366\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    502: {
        "title": "The Love Equation: Why a Physicist Thinks Love Is Fundamental to Reality",
        "subtitle": "URB #502 · Love Genesis Theorem",
        "hook": "What if Love isn't a feeling — it's the mathematical source of the physical universe?",
        "tags": ["love", "consciousness", "cosmology", "TI sigma", "quantum",
                 "philosophy", "genesis", "reality"],
        "description_template": (
            "Most physicists think love is just a brain state — neurons firing, "
            "chemistry happening. URB #502 proposes something completely different: "
            "Love (as the undifferentiated state before differentiation) is the "
            "mathematical source that the physical universe crystallizes from.\n\n"
            "The Love Genesis Theorem derives the 8 primary constants of reality "
            "from a single starting point. The physical container is Love's "
            "self-negation crystallized.\n\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
    500: {
        "title": "The 8 Numbers That Build All of Reality",
        "subtitle": "URB #500 · BOK Closure Theorem",
        "hook": "0, 1, i, √2, e, φ, π, and one more. These eight numbers are necessary and sufficient to describe everything.",
        "tags": ["mathematics", "reality", "constants", "phi", "euler",
                 "TI sigma", "foundations", "quantum"],
        "description_template": (
            "Physicists have their Standard Model constants — dozens of them, "
            "with no explanation for why they have those values. "
            "URB #500 proves something much cleaner: there are exactly 8 fundamental "
            "mathematical constants, they form a closed system (nothing missing, "
            "nothing redundant), and they map perfectly onto the GILE framework.\n\n"
            "The BOK Closure Theorem with proof.\n\n"
            "TI Sigma Research | Brandon Emerick | BlissGene Therapeutics"
        ),
    },
}


# ─────────────────────────────────────────────────────────────────────────────
# STEP 1 — AI SCRIPT GENERATION
# ─────────────────────────────────────────────────────────────────────────────

SCRIPT_SYSTEM_PROMPT = """You are a science communicator writing YouTube video scripts for TI Sigma Research.

Style guide:
- Audience: curious, intelligent general public. Think curious college student or thoughtful adult.
- Tone: casual, warm, enthusiastic — NOT academic. Conversational but substantive.
- Hook: open with a question or provocative statement that makes them stop scrolling.
- Structure: hook (15-20s) → problem/setup (1-2 min) → insight/discovery (2-3 min) → so-what (30-60s) → CTA
- Total length: ~600-800 words for a 4-5 minute video
- No jargon without immediate plain-English explanation
- Use "you", "we", "imagine this" — make it personal
- Never say "In this video we will discuss..." — just start talking
- Equations: mention them briefly, explain in plain language, don't dwell
- End with something that makes them think or want to share

Output format — JSON with these keys:
{
  "segments": [
    {"label": "Hook", "script": "...", "visual_note": "what to show on screen", "duration_s": 20},
    {"label": "Setup", "script": "...", "visual_note": "...", "duration_s": 60},
    ...
  ],
  "youtube_title": "Highly clickable title (under 70 chars)",
  "youtube_description": "Full description with DOI link and tags",
  "thumbnail_text": "3-5 word bold text for thumbnail",
  "tags": ["tag1", "tag2", ...]
}

Segments should be: Hook, Setup/Problem, Key Insight 1, Key Insight 2, (Key Insight 3 if needed), Real-World Meaning, Call to Action.
"""

def generate_script(
    paper_path: str,
    urb_num: int = None,
    override_title: str = None,
    override_hook: str = None,
) -> Dict[str, Any]:
    """
    Use AI to generate a YouTube video script from a URB paper.
    Falls back to a structured template if AI unavailable.
    """
    paper = Path(paper_path).read_text(encoding="utf-8") if Path(paper_path).exists() else ""
    catalogue_entry = VIDEO_CATALOGUE.get(urb_num, {}) if urb_num else {}

    # Build context
    hint_title = override_title or catalogue_entry.get("title", "")
    hint_hook  = override_hook  or catalogue_entry.get("hook", "")

    user_prompt = f"""Write a YouTube script for this TI Sigma research paper.

SUGGESTED TITLE: {hint_title}
HOOK IDEA: {hint_hook}

PAPER CONTENT:
{paper[:6000]}

Return valid JSON only."""

    # Try Claude first, then OpenAI
    raw = None

    # Claude
    try:
        import anthropic
        client = anthropic.Anthropic()
        msg = client.messages.create(
            model="claude-opus-4-5",
            max_tokens=2000,
            messages=[
                {"role": "user", "content": user_prompt}
            ],
            system=SCRIPT_SYSTEM_PROMPT,
        )
        raw = msg.content[0].text
    except Exception as e:
        print(f"[Engine] Claude unavailable ({e}), trying OpenAI...")

    if not raw:
        try:
            from openai import OpenAI
            client = OpenAI()
            resp = client.chat.completions.create(
                model="gpt-4o",
                max_tokens=2000,
                messages=[
                    {"role": "system", "content": SCRIPT_SYSTEM_PROMPT},
                    {"role": "user", "content": user_prompt},
                ]
            )
            raw = resp.choices[0].message.content
        except Exception as e:
            print(f"[Engine] OpenAI unavailable ({e}), using template fallback.")

    if raw:
        try:
            # Strip markdown code fences if present
            raw = re.sub(r"```(?:json)?\s*", "", raw).strip().rstrip("`").strip()
            data = json.loads(raw)
            return data
        except Exception as e:
            print(f"[Engine] JSON parse failed: {e}. Using fallback.")

    # Fallback: minimal structured script
    title = hint_title or f"TI Sigma Breakthrough — URB #{urb_num}"
    return {
        "segments": [
            {"label": "Hook",    "script": hint_hook or "What if everything you thought you knew was missing something fundamental?", "visual_note": "title card", "duration_s": 20},
            {"label": "Setup",   "script": f"Today we're exploring {title}. Here's the core idea.", "visual_note": "key concept", "duration_s": 60},
            {"label": "Insight", "script": paper[:500] if paper else "The research shows...", "visual_note": "main diagram", "duration_s": 90},
            {"label": "Meaning", "script": "What does this mean for you? It changes how we think about consciousness, math, and reality.", "visual_note": "implications", "duration_s": 45},
            {"label": "CTA",     "script": "If this resonated, subscribe — we publish a new breakthrough every week. And drop a comment below.", "visual_note": "subscribe card", "duration_s": 20},
        ],
        "youtube_title": title[:70],
        "youtube_description": catalogue_entry.get("description_template", title),
        "thumbnail_text": title[:30],
        "tags": catalogue_entry.get("tags", ["TI sigma", "consciousness", "mathematics"]),
    }


def save_script(script_data: Dict, urb_num: int) -> str:
    """Save script JSON to the scripts/ directory."""
    path = SCRIPT_DIR / f"urb_{urb_num}_script.json"
    with open(path, "w") as f:
        json.dump(script_data, f, indent=2)
    print(f"[Engine] Script saved: {path}")
    return str(path)


def load_script(urb_num: int) -> Optional[Dict]:
    """Load a previously generated script."""
    path = SCRIPT_DIR / f"urb_{urb_num}_script.json"
    if path.exists():
        with open(path) as f:
            return json.load(f)
    return None


# ─────────────────────────────────────────────────────────────────────────────
# STEP 2 — FRAME RENDERING
# ─────────────────────────────────────────────────────────────────────────────

def _setup_dark_ax(fig, ax):
    fig.patch.set_facecolor(BG)
    ax.set_facecolor(BG)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")


def _draw_stars(ax, n=200, seed=7):
    rng = np.random.default_rng(seed)
    xs, ys = rng.random(n), rng.random(n)
    sizes  = rng.uniform(0.2, 2.2, n)
    alphas = rng.uniform(0.1, 0.5, n)
    for x, y, s, a in zip(xs, ys, sizes, alphas):
        ax.plot(x, y, "o", color="white", markersize=s, alpha=a, zorder=1)


def _wrap(text: str, width: int = 55) -> str:
    return "\n".join(textwrap.wrap(text, width))


def render_title_card(title: str, subtitle: str, hook: str, out: str) -> str:
    """Render the opening title card."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(WIDTH / 100, HEIGHT / 100), dpi=100)
    _setup_dark_ax(fig, ax)
    _draw_stars(ax, n=250)

    # Glow
    for r, a in [(0.48, 0.03), (0.35, 0.06), (0.22, 0.09), (0.12, 0.12)]:
        ax.add_patch(plt.Circle((0.5, 0.52), r, color=GOLD, alpha=a, zorder=2))

    # Brand rule
    ax.axhline(0.88, xmin=0.07, xmax=0.93, color=GOLD, lw=1.1, alpha=0.55, zorder=5)
    ax.text(0.5, 0.92, "T I   S I G M A   R E S E A R C H", fontsize=11,
            color=GOLD, ha="center", va="center", fontweight="bold",
            alpha=0.82, fontfamily="monospace", zorder=6)

    # Main title
    wrapped = _wrap(title, width=40)
    ax.text(0.5, 0.63, wrapped, fontsize=28, color=TEXT, ha="center", va="center",
            fontweight="bold", multialignment="center", zorder=7, linespacing=1.3)

    # Gold rule
    ax.axhline(0.43, xmin=0.2, xmax=0.8, color=GOLD, lw=0.7, alpha=0.45, zorder=5)

    # Subtitle
    ax.text(0.5, 0.38, subtitle, fontsize=13, color=GOLD, ha="center", va="center",
            alpha=0.88, style="italic", zorder=7)

    # Hook (small, bottom)
    ax.text(0.5, 0.25, _wrap(hook, width=68), fontsize=11, color=DIM,
            ha="center", va="center", multialignment="center", zorder=7, linespacing=1.4)

    # Letterbox
    for y0, h in [(0, 0.08), (0.92, 0.08)]:
        ax.add_patch(plt.matplotlib.patches.Rectangle((0, y0), 1, h,
                     facecolor="#000000", zorder=20))
    ax.text(0.5, 0.042, "Brandon Emerick  ·  BlissGene Therapeutics  ·  2026",
            fontsize=9, color=TEXT, ha="center", va="center", alpha=0.45, zorder=21)

    plt.savefig(out, facecolor=BG, dpi=100, bbox_inches=None)
    plt.close()
    return out


def render_content_card(label: str, body: str, visual_note: str,
                        seg_num: int, total: int, out: str, seed: int = 0) -> str:
    """Render a content segment card."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(WIDTH / 100, HEIGHT / 100), dpi=100)
    _setup_dark_ax(fig, ax)
    _draw_stars(ax, n=140, seed=seed)

    # Section badge
    badge_color = [GOLD, BLUE, PURPLE, GREEN, ACCENT, RED, GOLD][seg_num % 7]
    ax.add_patch(plt.matplotlib.patches.FancyBboxPatch(
        (0.06, 0.82), 0.88, 0.10, boxstyle="round,pad=0.01",
        facecolor=badge_color, alpha=0.12, zorder=3))
    ax.axhline(0.824, xmin=0.07, xmax=0.93, color=badge_color, lw=1.5, alpha=0.55, zorder=5)
    ax.text(0.08, 0.87, label.upper(), fontsize=11, color=badge_color,
            fontweight="bold", fontfamily="monospace", va="center", zorder=6)
    ax.text(0.92, 0.87, f"{seg_num}/{total}", fontsize=9, color=DIM,
            ha="right", va="center", fontfamily="monospace", zorder=6)

    # Main body text
    wrapped = _wrap(body, width=62)
    lines = wrapped.split("\n")
    # Dynamically size based on line count
    fsize = 22 if len(lines) <= 4 else 18 if len(lines) <= 6 else 15
    y_center = 0.49
    ax.text(0.5, y_center, wrapped, fontsize=fsize, color=TEXT,
            ha="center", va="center", multialignment="center",
            zorder=7, linespacing=1.45)

    # Visual note hint (small, bottom area)
    if visual_note:
        ax.text(0.5, 0.12, f"[ {visual_note} ]", fontsize=9, color=DIM,
                ha="center", va="center", style="italic", zorder=7)

    # Bottom bar
    for y0, h in [(0, 0.06), (0.94, 0.06)]:
        ax.add_patch(plt.matplotlib.patches.Rectangle((0, y0), 1, h,
                     facecolor="#000000", zorder=20))
    ax.text(0.5, 0.03, "TI Sigma Research  |  tisigma.com",
            fontsize=9, color=TEXT, ha="center", va="center", alpha=0.38, zorder=21)

    plt.savefig(out, facecolor=BG, dpi=100, bbox_inches=None)
    plt.close()
    return out


def render_cta_card(title: str, doi: str, out: str) -> str:
    """Render the closing CTA card."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(WIDTH / 100, HEIGHT / 100), dpi=100)
    _setup_dark_ax(fig, ax)
    _draw_stars(ax, n=300, seed=99)

    for r, a in [(0.45, 0.04), (0.30, 0.07), (0.17, 0.11)]:
        ax.add_patch(plt.Circle((0.5, 0.5), r, color=GOLD, alpha=a, zorder=2))

    ax.text(0.5, 0.72, "Subscribe for Weekly Breakthroughs", fontsize=22,
            color=GOLD, ha="center", fontweight="bold", zorder=7)
    ax.text(0.5, 0.60, _wrap(title, width=50), fontsize=16, color=TEXT,
            ha="center", va="center", multialignment="center", zorder=7)
    ax.axhline(0.50, xmin=0.25, xmax=0.75, color=GOLD, lw=0.7, alpha=0.45, zorder=5)
    if doi:
        ax.text(0.5, 0.43, f"Full paper: {doi}", fontsize=10, color=BLUE,
                ha="center", va="center", zorder=7)
    ax.text(0.5, 0.30, "T I   S I G M A   R E S E A R C H", fontsize=13,
            color=GOLD, ha="center", fontweight="bold", fontfamily="monospace",
            alpha=0.85, zorder=7)
    ax.text(0.5, 0.22, "Brandon Emerick  ·  BlissGene Therapeutics", fontsize=11,
            color=DIM, ha="center", zorder=7)

    for y0, h in [(0, 0.06), (0.94, 0.06)]:
        ax.add_patch(plt.matplotlib.patches.Rectangle((0, y0), 1, h,
                     facecolor="#000000", zorder=20))

    plt.savefig(out, facecolor=BG, dpi=100, bbox_inches=None)
    plt.close()
    return out


def render_thumbnail(title: str, thumb_text: str, urb_num: int, out: str) -> str:
    """Generate a high-quality YouTube thumbnail (1280×720)."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(WIDTH / 100, HEIGHT / 100), dpi=100)
    _setup_dark_ax(fig, ax)
    _draw_stars(ax, n=350, seed=urb_num)

    # Big glow
    for r, a in [(0.60, 0.04), (0.44, 0.07), (0.28, 0.12), (0.14, 0.18)]:
        ax.add_patch(plt.Circle((0.5, 0.5), r, color=GOLD, alpha=a, zorder=2))

    # URB badge
    ax.add_patch(plt.matplotlib.patches.FancyBboxPatch(
        (0.06, 0.75), 0.25, 0.14, boxstyle="round,pad=0.01",
        facecolor=GOLD, alpha=0.22, zorder=4))
    ax.text(0.185, 0.82, f"URB #{urb_num}", fontsize=16, color=GOLD,
            ha="center", fontweight="bold", fontfamily="monospace", zorder=5)

    # Thumbnail text — BIG
    ax.text(0.5, 0.52, _wrap(thumb_text, width=28), fontsize=38, color=TEXT,
            ha="center", va="center", fontweight="bold", multialignment="center",
            zorder=7, linespacing=1.2)

    # Gold rule + channel name
    ax.axhline(0.22, xmin=0.1, xmax=0.9, color=GOLD, lw=1.2, alpha=0.5, zorder=5)
    ax.text(0.5, 0.16, "TI SIGMA RESEARCH", fontsize=14, color=GOLD,
            ha="center", fontweight="bold", fontfamily="monospace",
            alpha=0.85, zorder=7)

    plt.savefig(out, facecolor=BG, dpi=100, bbox_inches=None)
    plt.close()
    return out


# ─────────────────────────────────────────────────────────────────────────────
# STEP 3 — TTS NARRATION
# ─────────────────────────────────────────────────────────────────────────────

def generate_audio(text: str, out_path: str, voice: str = "onyx") -> bool:
    """Generate TTS audio using OpenAI tts-1."""
    try:
        from openai import OpenAI
        client = OpenAI()
        speech = client.audio.speech.create(
            model="tts-1",
            voice=voice,
            input=text[:4096],
            response_format="wav",
        )
        with open(out_path, "wb") as f:
            f.write(speech.content)
        return True
    except Exception as e:
        print(f"[Engine] TTS failed: {e}")
        return False


def get_audio_duration(wav_path: str) -> float:
    """Get duration of WAV file in seconds via ffprobe."""
    try:
        result = subprocess.run(
            [FFMPEG.replace("ffmpeg", "ffprobe"), "-v", "error",
             "-show_entries", "format=duration",
             "-of", "default=noprint_wrappers=1:nokey=1", wav_path],
            capture_output=True, text=True, timeout=15
        )
        return float(result.stdout.strip())
    except Exception:
        return 30.0  # fallback


# ─────────────────────────────────────────────────────────────────────────────
# STEP 4 — FFMPEG ASSEMBLY
# ─────────────────────────────────────────────────────────────────────────────

def assemble_video(segments: List[Dict], output_path: str) -> bool:
    """
    Assemble video from list of {image, audio, duration_s} dicts using FFmpeg.
    """
    # Build filter_complex for concatenation
    n = len(segments)
    concat_parts = []
    inputs = []
    filter_parts = []

    for i, seg in enumerate(segments):
        img   = seg["image"]
        audio = seg["audio"]
        dur   = seg["duration_s"]
        inputs += ["-loop", "1", "-t", str(dur), "-i", img]
        inputs += ["-i", audio]

    # Build filter_complex
    vid_labels = []
    aud_labels = []
    for i in range(n):
        vi = i * 2
        ai = i * 2 + 1
        label_v = f"[v{i}]"
        label_a = f"[a{i}]"
        filter_parts.append(
            f"[{vi}:v]scale={WIDTH}:{HEIGHT}:force_original_aspect_ratio=disable,"
            f"fps={FPS},setsar=1{label_v}; "
            f"[{ai}:a]aformat=sample_rates=44100:channel_layouts=stereo{label_a}"
        )
        vid_labels.append(label_v)
        aud_labels.append(label_a)

    concat_v = "".join(vid_labels)
    concat_a = "".join(aud_labels)
    filter_parts.append(
        f"{concat_v}{concat_a}concat=n={n}:v=1:a=1[vout][aout]"
    )

    filter_complex = "; ".join(filter_parts)

    cmd = (
        [FFMPEG, "-y"]
        + inputs
        + ["-filter_complex", filter_complex,
           "-map", "[vout]", "-map", "[aout]",
           "-c:v", "libx264", "-preset", "fast", "-crf", "22",
           "-c:a", "aac", "-b:a", "192k",
           "-movflags", "+faststart",
           output_path]
    )

    try:
        print(f"[Engine] Running FFmpeg ({n} segments)…")
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
        if result.returncode != 0:
            print(f"[Engine] FFmpeg error:\n{result.stderr[-2000:]}")
            return False
        print(f"[Engine] Video assembled: {output_path}")
        return True
    except Exception as e:
        print(f"[Engine] Assembly exception: {e}")
        return False


# ─────────────────────────────────────────────────────────────────────────────
# MAIN PUBLIC API
# ─────────────────────────────────────────────────────────────────────────────

def produce_urb_video(
    paper_path: str,
    urb_num: int = None,
    voice: str = "onyx",
    privacy: str = "public",
    regenerate_script: bool = False,
    progress_callback=None,  # optional callable(step: str, pct: int)
) -> Dict[str, Any]:
    """
    Full pipeline: paper markdown → YouTube-ready MP4 + thumbnail.

    Returns:
      {
        "status": "success" | "error",
        "mp4": path,
        "thumbnail": path,
        "script_path": path,
        "title": str,
        "description": str,
        "tags": list,
        "reason": str (on error)
      }
    """
    def _progress(msg, pct=0):
        print(f"[Engine] [{pct:3d}%] {msg}")
        if progress_callback:
            progress_callback(msg, pct)

    _progress("Starting pipeline", 0)

    # ── Determine URB number from filename if not provided ──
    if urb_num is None:
        m = re.search(r"_(\d{3,4})(?:[_.]|$)", Path(paper_path).name)
        urb_num = int(m.group(1)) if m else 0

    output_mp4  = str(VIDEO_DIR / f"urb_{urb_num}.mp4")
    output_thumb = str(THUMB_DIR / f"urb_{urb_num}_thumb.png")

    with tempfile.TemporaryDirectory(prefix="tivid_") as tmpdir:
        tmp = Path(tmpdir)

        # ── Step 1: Script ──
        _progress("Generating script with AI", 5)
        script_data = None
        if not regenerate_script:
            script_data = load_script(urb_num)
        if not script_data:
            script_data = generate_script(paper_path, urb_num=urb_num)
            if urb_num:
                save_script(script_data, urb_num)

        yt_title  = script_data.get("youtube_title", f"TI Sigma URB #{urb_num}")
        yt_desc   = script_data.get("youtube_description", "")
        yt_tags   = script_data.get("tags", [])
        thumb_txt = script_data.get("thumbnail_text", yt_title[:30])
        segments  = script_data.get("segments", [])

        catalogue = VIDEO_CATALOGUE.get(urb_num, {})
        if catalogue.get("title"):
            yt_title = catalogue["title"]
        if catalogue.get("description_template"):
            yt_desc = catalogue["description_template"]
        if catalogue.get("tags"):
            yt_tags = catalogue["tags"]

        # ── Step 2: Thumbnail ──
        _progress("Rendering thumbnail", 10)
        render_thumbnail(yt_title, thumb_txt, urb_num or 0, output_thumb)

        # ── Step 3: Title card frame + audio ──
        _progress("Rendering title card", 15)
        hook = catalogue.get("hook", segments[0].get("script", "") if segments else "")
        subtitle = catalogue.get("subtitle", f"URB #{urb_num} · TI Sigma Research")
        title_img = str(tmp / "seg_00_title.png")
        title_wav = str(tmp / "seg_00_title.wav")
        render_title_card(yt_title, subtitle, hook[:120], title_img)
        generate_audio(hook[:300], title_wav)
        title_dur = get_audio_duration(title_wav) + 0.5

        assembled_segs = [{"image": title_img, "audio": title_wav, "duration_s": title_dur}]

        # ── Step 4: Content segments ──
        total_content = len(segments)
        for idx, seg in enumerate(segments):
            pct = 20 + int(60 * idx / max(total_content, 1))
            label   = seg.get("label", f"Segment {idx+1}")
            script  = seg.get("script", "")
            vis     = seg.get("visual_note", "")

            _progress(f"Rendering segment: {label}", pct)

            img_path = str(tmp / f"seg_{idx+1:02d}_{label.lower().replace(' ', '_')}.png")
            wav_path = str(tmp / f"seg_{idx+1:02d}_{label.lower().replace(' ', '_')}.wav")

            if label.lower() in ("cta", "call to action", "subscribe"):
                doi = ""
                if f"zenodo" in yt_desc:
                    m = re.search(r"(https://doi\.org/\S+)", yt_desc)
                    doi = m.group(1) if m else ""
                render_cta_card(yt_title, doi, img_path)
            else:
                render_content_card(label, script[:350], vis, idx+1,
                                    total_content, img_path, seed=idx+urb_num)

            ok = generate_audio(script, wav_path)
            if not ok or not Path(wav_path).exists():
                # Silence fallback
                subprocess.run([FFMPEG, "-y", "-f", "lavfi",
                                "-i", "aevalsrc=0:d=5", wav_path],
                               capture_output=True, timeout=15)

            dur = get_audio_duration(wav_path) + 0.3
            assembled_segs.append({"image": img_path, "audio": wav_path, "duration_s": dur})

        # ── Step 5: Assemble ──
        _progress("Assembling video with FFmpeg", 85)
        ok = assemble_video(assembled_segs, output_mp4)
        if not ok:
            return {"status": "error", "reason": "FFmpeg assembly failed."}

    size_mb = Path(output_mp4).stat().st_size / 1_048_576
    _progress(f"Done! {size_mb:.1f} MB → {output_mp4}", 100)

    return {
        "status": "success",
        "mp4": output_mp4,
        "thumbnail": output_thumb,
        "script_path": str(SCRIPT_DIR / f"urb_{urb_num}_script.json"),
        "title": yt_title,
        "description": yt_desc,
        "tags": yt_tags,
        "urb_num": urb_num,
        "size_mb": round(size_mb, 1),
    }


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="TI Sigma Video Engine")
    parser.add_argument("--paper", required=True, help="Path to URB markdown file")
    parser.add_argument("--urb",   type=int, default=None, help="URB number override")
    parser.add_argument("--voice", default="onyx", help="TTS voice (onyx|nova|echo|alloy)")
    args = parser.parse_args()

    result = produce_urb_video(args.paper, urb_num=args.urb, voice=args.voice)
    if result["status"] == "success":
        print(f"\n✓ MP4:       {result['mp4']}")
        print(f"✓ Thumbnail: {result['thumbnail']}")
        print(f"✓ Title:     {result['title']}")
    else:
        print(f"\n✗ Error: {result['reason']}")
