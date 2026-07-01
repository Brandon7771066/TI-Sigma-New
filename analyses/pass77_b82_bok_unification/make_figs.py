"""
Pass-77 B82 — BOK unification diagrams (plain-language).
Two illustrative diagrams (no data; structural maps) for the updated BOK_MASTER_REFERENCE.md:
  fig1: the BOK EQUATION EVOLUTION — original ChatGPT 3-variable limit -> +Love (4 vars) + finite calculus
        -> 8-fold (Butterfly 4 + Octopus 4 / 8 tralsebits) -> HEM-GILE coupling + E8/Leech/Monster ladder.
  fig2: the FOUR GILE<->HEM COMPLEMENT COUPLES (G<->Existence Footprint highlighted; EF = amplitude x frequency).
Budget $0, local matplotlib.
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

OUT = "analyses/pass77_b82_bok_unification"

# ---------------- fig1: equation evolution ----------------
fig, ax = plt.subplots(figsize=(12.5, 6.2))
ax.axis("off")
ax.set_xlim(0, 100); ax.set_ylim(0, 100)

stages = [
    (8, "1 · ORIGIN (ChatGPT)\n\nlim f(u, v, t)\nas interaction → ∞\n\nu = polarity (T/F)\nv = Tralse phase\nt = time (Jeff Time)\n\n3 variables", "#e9c46a"),
    (32, "2 · COMPLETION (Dec 2025)\n\nf(u, v, w, t)\nfinite: f^(N), N large\n\n+ w = Love /\nentanglement\n(the missing\nGILE dimension)\n\n4 variables", "#f4a261"),
    (56, "3 · EIGHTFOLD\n\n4 GILE dims × 2\npolarities = 8\n\nButterfly (4 primary)\n+ Octopus (4 arms)\n= 8 tralsebits\n(i-cell, B58)\n\nE₈ in ℝ⁸", "#2a9d8f"),
    (80, "4 · GILE↔HEM\nCOMPLETION\n\neach GILE (abstract)\ncoupled to its HEM\n(physical) complement\n\nG↔EF, I↔precision,\nL↔entanglement,\nE↔symmetry (B63)\n\nE₈ ×3(time) → Leech₂₄\n→ Monster (GM net)", "#577590"),
]
for x, txt, col in stages:
    box = FancyBboxPatch((x, 28), 18, 50, boxstyle="round,pad=0.6,rounding_size=2",
                         fc=col, ec="black", lw=1.2, alpha=0.92)
    ax.add_patch(box)
    ax.text(x + 9, 53, txt, ha="center", va="center", fontsize=8.4, wrap=True)
for x0 in [26, 50, 74]:
    ax.add_patch(FancyArrowPatch((x0, 53), (x0 + 6, 53), arrowstyle="-|>", mutation_scale=20, lw=2, color="#333"))
ax.text(50, 92, "The BOK Equation, United: from the original 3-variable limit to the HEM–GILE blueprint",
        ha="center", fontsize=13, weight="bold")
ax.text(50, 86, "Butterfly–Octopus Knot (BOK) — same object at four levels of completion; nothing discarded, each stage contains the last",
        ha="center", fontsize=9, style="italic", color="#444")
ax.text(50, 16, "Plain language: the first equation had 3 dials. We found a 4th (Love), made the math finite (infinite steps don't exist),\n"
                "saw the 4 dials double into 8 (the i-cell's 8 tralsebits = E₈), then paired each abstract GILE dial with a measurable\n"
                "physical partner (HEM). G's physical partner is the Existence Footprint — how loudly something exists.",
        ha="center", fontsize=8.6, color="#222")
plt.tight_layout()
plt.savefig(f"{OUT}/fig1_bok_equation_evolution.png", dpi=115); plt.close()

# ---------------- fig2: the four GILE<->HEM couples ----------------
fig, ax = plt.subplots(figsize=(11.5, 6.4))
ax.axis("off")
ax.set_xlim(0, 100); ax.set_ylim(0, 100)
ax.text(50, 95, "The Four HEM–GILE Couples — abstract truth paired with physical footprint",
        ha="center", fontsize=13, weight="bold")
ax.text(50, 89, "GILE truth is incomplete without its HEM complement (and vice-versa). Each couple = one Dirac γ-matrix (B63).",
        ha="center", fontsize=9, style="italic", color="#444")

couples = [
    ("G — Goodness", "result of the Four C's\n(Continuity, Coherence,\nConcreteness, Consistency)\n— ABSTRACT existence", "EF — Existence Footprint",
     "amplitude × frequency\n(how strongly it exists;\nDirac density V⁰)", "γ⁰", "#e76f51", True),
    ("I — Intuition", "accuracy + certainty\n(2-dimensional)", "Precision sector", "⟨O⟩ accuracy,\n1/(1+Var) certainty", "γ¹", "#2a9d8f", False),
    ("L — Love", "relational positive valence\n(networks of MI particles)", "Entanglement", "concurrence\n(correlation/binding)", "γ²", "#577590", False),
    ("E — Environment", "aesthetics\n(physical or abstract)", "Symmetry", "⟨SWAP⟩\n(structural order)", "γ³", "#9c6644", False),
]
y = 76
for gname, gdesc, hname, hdesc, gamma, col, hl in couples:
    lw = 2.4 if hl else 1.0
    ec = "#b5179e" if hl else "black"
    gbox = FancyBboxPatch((6, y - 8), 32, 13, boxstyle="round,pad=0.4,rounding_size=1.5",
                          fc=col, ec=ec, lw=lw, alpha=0.85)
    ax.add_patch(gbox)
    ax.text(22, y + 2.5, gname, ha="center", fontsize=9.5, weight="bold", color="white")
    ax.text(22, y - 3.2, gdesc, ha="center", fontsize=7.3, color="white")
    ax.add_patch(FancyArrowPatch((39, y - 1.5), (60, y - 1.5), arrowstyle="<|-|>",
                                 mutation_scale=16, lw=lw, color=ec))
    ax.text(49.5, y + 2.2, f"{gamma}  couple", ha="center", fontsize=7.6, color=ec, weight="bold")
    hbox = FancyBboxPatch((61, y - 8), 33, 13, boxstyle="round,pad=0.4,rounding_size=1.5",
                          fc="#e9ecef", ec=ec, lw=lw)
    ax.add_patch(hbox)
    ax.text(77.5, y + 2.5, hname, ha="center", fontsize=9.5, weight="bold", color="#222")
    ax.text(77.5, y - 3.2, hdesc, ha="center", fontsize=7.3, color="#333")
    y -= 18
ax.text(22, 4.5, "GILE  (abstract / phase)", ha="center", fontsize=9, weight="bold", color="#3a0ca3")
ax.text(77.5, 4.5, "HEM  (physical / modulus)", ha="center", fontsize=9, weight="bold", color="#3a0ca3")
ax.text(50, 0.8, "Highlighted: GILE-G ↔ Existence Footprint (Brandon's clarification). CCC i-cell GILE:HEM magnitude ratio = 2:1.",
        ha="center", fontsize=8, color="#b5179e")
plt.tight_layout()
plt.savefig(f"{OUT}/fig2_gile_hem_couples.png", dpi=115); plt.close()

print("wrote fig1_bok_equation_evolution.png, fig2_gile_hem_couples.png")
