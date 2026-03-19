"""
Custom PDF generator for URBs #450-455 with distinct cover designs per paper.
Each paper gets a unique visual treatment appropriate to its subject matter.
"""

import markdown
import os
from weasyprint import HTML


PAPERS = [
    {
        "md": "papers/URB_TELEKINESIS_GENERAL_PSI_450.md",
        "pdf": "papers/URB_450_TELEKINESIS_GENERAL_PSI.pdf",
        "urb": "#450",
        "subtitle": "Telekinesis as the General Case of PSI",
        "tagline": "S → [i-channel] → O",
        "theme": "psi_physics",
    },
    {
        "md": "papers/URB_COSMIC_TELEKINESIS_CREATIONISM_451.md",
        "pdf": "papers/URB_451_COSMIC_TELEKINESIS_CREATIONISM.pdf",
        "urb": "#451",
        "subtitle": "Cosmic Telekinesis and the Scientific Framework for Creationism",
        "tagline": "CCC as Architect of the Probability Landscape",
        "theme": "cosmology",
    },
    {
        "md": "papers/URB_SHAMANIC_PLANT_CONSCIOUSNESS_452.md",
        "pdf": "papers/URB_452_SHAMANIC_PLANT_CONSCIOUSNESS.pdf",
        "urb": "#452",
        "subtitle": "Shamanic Expert Testimony and Plant-Fungal Consciousness",
        "tagline": "Prima Facie • LCC of Life • i-Channel Opening",
        "theme": "plant_life",
    },
    {
        "md": "papers/URB_CCC_CHOSEN_CONSTRAINTS_THEODICY_453.md",
        "pdf": "papers/URB_453_CCC_CHOSEN_CONSTRAINTS_THEODICY.pdf",
        "urb": "#453",
        "subtitle": "CCC's Chosen Constraints and the New Theodicy",
        "tagline": "Most Perfect Possible · Imaginary ≠ Instantiable · Autonomy Principle",
        "theme": "theodicy",
    },
    {
        "md": "papers/URB_GM_NODE_SOTERIOLOGY_THREE_TIERS_454.md",
        "pdf": "papers/URB_454_GM_NODE_SOTERIOLOGY_THREE_TIERS.pdf",
        "urb": "#454",
        "subtitle": "GM-Node Soteriology: Three Tiers of BT Existence",
        "tagline": "Existence · Permissibility · Greatness · Doctrine of Grace",
        "theme": "soteriology",
    },
    {
        "md": "papers/URB_SIN_NATURE_DOCTRINE_455.md",
        "pdf": "papers/URB_455_SIN_NATURE_DOCTRINE.pdf",
        "urb": "#455",
        "subtitle": "The Sin-Nature Doctrine",
        "tagline": "Terrible or Permissible Alone · Greatness Requires GM Support",
        "theme": "sin_nature",
    },
]


COVER_STYLES = {
    "psi_physics": {
        "bg": "linear-gradient(135deg, #0a0a2e 0%, #1a1a5e 40%, #0d3b6e 100%)",
        "accent": "#00d4ff",
        "accent2": "#7b2fff",
        "text": "#e8f4fd",
        "badge_bg": "rgba(0, 212, 255, 0.15)",
        "badge_border": "#00d4ff",
        "label": "PSI PHYSICS · LCC THEORY · METACAUSAL NETWORKS",
        "symbol": "∿",
        "symbol_color": "#00d4ff",
        "orb_color": "rgba(0, 212, 255, 0.12)",
        "orb2_color": "rgba(123, 47, 255, 0.10)",
    },
    "cosmology": {
        "bg": "linear-gradient(135deg, #0c0518 0%, #1a0b3d 35%, #0a1628 70%, #001428 100%)",
        "accent": "#ffd700",
        "accent2": "#ff6b35",
        "text": "#f0e8ff",
        "badge_bg": "rgba(255, 215, 0, 0.12)",
        "badge_border": "#ffd700",
        "label": "COSMOLOGY · CREATIONISM · CCC-BASED EVOLUTION",
        "symbol": "✦",
        "symbol_color": "#ffd700",
        "orb_color": "rgba(255, 215, 0, 0.08)",
        "orb2_color": "rgba(255, 107, 53, 0.08)",
    },
    "plant_life": {
        "bg": "linear-gradient(135deg, #071a0e 0%, #0d2b14 35%, #142b1a 70%, #0a1f10 100%)",
        "accent": "#4ade80",
        "accent2": "#a78bfa",
        "text": "#ecfdf5",
        "badge_bg": "rgba(74, 222, 128, 0.12)",
        "badge_border": "#4ade80",
        "label": "ETHNOBOTANY · PLANT CONSCIOUSNESS · PRIMA FACIE",
        "symbol": "❧",
        "symbol_color": "#4ade80",
        "orb_color": "rgba(74, 222, 128, 0.10)",
        "orb2_color": "rgba(167, 139, 250, 0.08)",
    },
    "theodicy": {
        "bg": "linear-gradient(135deg, #1a0a00 0%, #2d1500 35%, #3d1a0a 70%, #1a0c00 100%)",
        "accent": "#f59e0b",
        "accent2": "#ef4444",
        "text": "#fef3c7",
        "badge_bg": "rgba(245, 158, 11, 0.12)",
        "badge_border": "#f59e0b",
        "label": "THEODICY · AUTONOMY PRINCIPLE · GILE THEOLOGY",
        "symbol": "⚖",
        "symbol_color": "#f59e0b",
        "orb_color": "rgba(245, 158, 11, 0.10)",
        "orb2_color": "rgba(239, 68, 68, 0.08)",
    },
    "soteriology": {
        "bg": "linear-gradient(135deg, #0f0f1e 0%, #1a1535 40%, #0f1e30 100%)",
        "accent": "#c084fc",
        "accent2": "#38bdf8",
        "text": "#f5f3ff",
        "badge_bg": "rgba(192, 132, 252, 0.12)",
        "badge_border": "#c084fc",
        "label": "SOTERIOLOGY · GM-NODE ARCHITECTURE · DOCTRINE OF GRACE",
        "symbol": "⬡",
        "symbol_color": "#c084fc",
        "orb_color": "rgba(192, 132, 252, 0.10)",
        "orb2_color": "rgba(56, 189, 248, 0.08)",
    },
    "sin_nature": {
        "bg": "linear-gradient(135deg, #0e0e0e 0%, #1c1c1c 40%, #0a0a1a 100%)",
        "accent": "#f87171",
        "accent2": "#34d399",
        "text": "#f9fafb",
        "badge_bg": "rgba(248, 113, 113, 0.12)",
        "badge_border": "#f87171",
        "label": "MORAL PHILOSOPHY · SIN-NATURE · GRACE TRADITIONS",
        "symbol": "⊖",
        "symbol_color": "#f87171",
        "orb_color": "rgba(248, 113, 113, 0.08)",
        "orb2_color": "rgba(52, 211, 153, 0.08)",
    },
}


BODY_CSS = """
@page {
    size: A4;
    margin: 2.5cm 2cm;
    @top-center {
        content: string(doctitle);
        font-size: 9pt;
        color: #888;
        font-family: 'Georgia', serif;
    }
    @bottom-center {
        content: "Page " counter(page) " of " counter(pages) " · TI Sigma URB Series · Brandon Emerick · 2026";
        font-size: 9pt;
        color: #888;
        font-family: 'Georgia', serif;
    }
}
@page :first {
    @top-center { content: ""; }
    @bottom-center { content: ""; }
    margin: 0;
}
body {
    font-family: 'Georgia', 'Times New Roman', serif;
    line-height: 1.7;
    color: #2c2c2c;
    font-size: 11pt;
}
h1 {
    string-set: doctitle content();
    color: #1a1a1a;
    border-bottom: 3px solid #4CAF50;
    padding-bottom: 10px;
    margin-top: 30px;
    margin-bottom: 20px;
    font-size: 18pt;
    line-height: 1.3;
}
h2 {
    color: #2d2d2d;
    border-left: 4px solid #4CAF50;
    padding-left: 12px;
    margin-top: 28px;
    margin-bottom: 14px;
    font-size: 14pt;
}
h3 {
    color: #3a3a3a;
    margin-top: 22px;
    margin-bottom: 10px;
    font-size: 12pt;
    font-style: italic;
}
p {
    margin-bottom: 12px;
    text-align: justify;
}
table {
    width: 100%;
    border-collapse: collapse;
    margin: 18px 0;
    font-size: 10pt;
}
th {
    background-color: #2d5a27;
    color: white;
    padding: 8px 10px;
    text-align: left;
    font-weight: bold;
}
td {
    padding: 7px 10px;
    border-bottom: 1px solid #ddd;
    vertical-align: top;
}
tr:nth-child(even) td {
    background-color: #f5f5f5;
}
blockquote {
    border-left: 4px solid #4CAF50;
    margin: 18px 0;
    padding: 12px 16px;
    background-color: #f9fdf9;
    font-style: italic;
    color: #444;
}
code {
    background-color: #f4f4f4;
    padding: 2px 6px;
    border-radius: 3px;
    font-family: monospace;
    font-size: 10pt;
}
ul, ol {
    margin-bottom: 14px;
    padding-left: 28px;
}
li {
    margin-bottom: 5px;
}
strong {
    color: #1a1a1a;
}
hr {
    border: none;
    border-top: 2px solid #e0e0e0;
    margin: 24px 0;
}
.cover-page {
    page-break-after: always;
    width: 100%;
    min-height: 297mm;
    box-sizing: border-box;
}
"""


def make_cover_html(paper, style):
    s = COVER_STYLES[style]
    return f"""
<div class="cover-page" style="
    background: {s['bg']};
    display: flex;
    flex-direction: column;
    justify-content: center;
    align-items: center;
    padding: 60px 50px;
    min-height: 297mm;
    position: relative;
    overflow: hidden;
">
  <!-- Decorative orbs -->
  <div style="
    position: absolute; top: -80px; right: -80px;
    width: 360px; height: 360px;
    border-radius: 50%;
    background: {s['orb_color']};
    border: 1px solid {s['badge_border']}22;
  "></div>
  <div style="
    position: absolute; bottom: -100px; left: -60px;
    width: 280px; height: 280px;
    border-radius: 50%;
    background: {s['orb2_color']};
  "></div>

  <!-- TI Sigma brand line -->
  <div style="
    font-family: monospace;
    font-size: 10pt;
    letter-spacing: 4px;
    color: {s['accent']};
    text-transform: uppercase;
    margin-bottom: 18px;
    text-align: center;
    opacity: 0.85;
  ">TI SIGMA RESEARCH · BRANDON EMERICK · MARCH 19, 2026</div>

  <!-- Large decorative symbol -->
  <div style="
    font-size: 80pt;
    color: {s['symbol_color']};
    opacity: 0.35;
    margin-bottom: 10px;
    text-align: center;
    line-height: 1;
  ">{s['symbol']}</div>

  <!-- URB number badge -->
  <div style="
    display: inline-block;
    background: {s['badge_bg']};
    border: 1.5px solid {s['badge_border']};
    border-radius: 6px;
    padding: 6px 20px;
    margin-bottom: 28px;
    font-family: monospace;
    font-size: 13pt;
    letter-spacing: 3px;
    color: {s['accent']};
    font-weight: bold;
  ">URB {paper['urb']}</div>

  <!-- Main title -->
  <h1 style="
    color: {s['text']};
    font-family: 'Georgia', serif;
    font-size: 22pt;
    font-weight: bold;
    text-align: center;
    line-height: 1.35;
    margin: 0 0 20px 0;
    padding: 0;
    border: none;
    max-width: 480px;
  ">{paper['subtitle']}</h1>

  <!-- Tagline -->
  <div style="
    color: {s['accent']};
    font-size: 11pt;
    font-style: italic;
    text-align: center;
    max-width: 420px;
    margin-bottom: 40px;
    opacity: 0.9;
    line-height: 1.6;
  ">{paper['tagline']}</div>

  <!-- Horizontal rule -->
  <div style="
    width: 160px;
    height: 2px;
    background: linear-gradient(to right, transparent, {s['accent']}, transparent);
    margin-bottom: 32px;
  "></div>

  <!-- Label strip -->
  <div style="
    font-family: monospace;
    font-size: 8pt;
    letter-spacing: 2.5px;
    color: {s['accent']};
    text-align: center;
    opacity: 0.7;
    margin-bottom: 40px;
  ">{s['label']}</div>

  <!-- Author/metadata block -->
  <div style="
    text-align: center;
    color: {s['text']};
    opacity: 0.75;
    font-size: 10pt;
    line-height: 1.8;
  ">
    <div style="font-weight: bold; font-size: 11pt; margin-bottom: 4px;">Brandon Emerick</div>
    <div>TI Sigma Unified Research Bulletin Series</div>
    <div>Total URBs: 109 · March 19, 2026</div>
    <div style="font-style: italic; margin-top: 8px; font-size: 9pt; opacity: 0.7;">
      GILE Framework · GM-Node Architecture · LCC Theory · PRIMARY CONSTANTS &#123;0,1,i,√2,e,φ,π,C&#125;
    </div>
  </div>
</div>
"""


def generate_paper_pdf(paper):
    md_path = paper["md"]
    pdf_path = paper["pdf"]
    style = paper["theme"]

    with open(md_path, "r", encoding="utf-8") as f:
        md_content = f.read()

    # Convert markdown to HTML body
    html_body = markdown.markdown(
        md_content,
        extensions=["extra", "tables", "toc"],
    )

    cover = make_cover_html(paper, style)

    full_html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<style>
{BODY_CSS}
</style>
</head>
<body>
{cover}
<div style="padding: 0;">
{html_body}
</div>
</body>
</html>"""

    HTML(string=full_html, base_url=".").write_pdf(pdf_path)
    size = os.path.getsize(pdf_path)
    print(f"OK: {pdf_path} ({size:,} bytes) [{style}]")


if __name__ == "__main__":
    for paper in PAPERS:
        generate_paper_pdf(paper)
    print("All 6 URB PDFs generated with distinct cover designs.")
