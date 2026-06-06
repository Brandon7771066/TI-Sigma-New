import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ---------- Fig 1: Proposition-Type x Clair-channel bandwidth matrix ----------
pts = ["Amodal /\nlogical", "Visual-\ngeometric", "Visual-\naesthetic", "Auditory-\nmusical\n(GILE-E)", "Somatic-\naffective"]
chans = ["Clair-\ncognizance", "Clair-\nvoyance", "Clair-\naudience", "Clair-\nsentience"]
# bandwidth 0-3 : payload-reach for claircognizance is broad; native-sense qualia peak elsewhere
B = np.array([
    [3, 1, 1, 1],   # amodal/logical  -> knowing peaks
    [2, 3, 0, 0],   # visual-geometric -> sight peaks; knowing gets payload (2)
    [2, 3, 0, 0],   # visual-aesthetic
    [2, 0, 3, 0],   # auditory-musical -> hearing peaks
    [2, 0, 0, 3],   # somatic-affective -> sentience peaks
])
fig, ax = plt.subplots(figsize=(8.4, 6.2))
im = ax.imshow(B, cmap="YlGn", vmin=0, vmax=3, aspect="auto")
ax.set_xticks(range(len(chans))); ax.set_xticklabels(chans, fontsize=9)
ax.set_yticks(range(len(pts))); ax.set_yticklabels(pts, fontsize=9)
labels = {0: "—", 1: "low", 2: "payload\nonly", 3: "PEAK\nqualia"}
for i in range(B.shape[0]):
    for j in range(B.shape[1]):
        ax.text(j, i, labels[B[i, j]], ha="center", va="center",
                fontsize=8, fontweight="bold",
                color="#333" if B[i, j] < 3 else "#0a3d20")
ax.set_title("B93 Fig 1 — Proposition Types \u00d7 clair-channel BANDWIDTH\n"
             "claircognizance reaches every PT's PAYLOAD (col 1, never blank);\n"
             "native senses hold PEAK qualia on their own PT",
             fontsize=10.5, fontweight="bold")
ax.text(0.5, -0.30,
        "CGP-1 supremacy RE-GROUNDED (refinement #1): NOT bandwidth-dominance, but\n"
        "FUNCTIONAL COMPLETENESS (reaches every payload)  +  EGO-SAFETY (routine\n"
        "knowing doesn't fracture the ego the way vivid sensory experience can).",
        transform=ax.transAxes, ha="center", fontsize=8.6, color="#1e5e40", fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b93_proposition_types/fig1_proposition_type_bandwidth.png", dpi=130,
            bbox_inches="tight")
print("wrote fig1")

# ---------- Fig 2: Brandon lifetime hallucination ledger by channel (corrected B94) ----------
# (channel, label, state, counted)
events = [
    ("Clairaudient", "Fan/pillow music (~monthly)", "hypnagogic", "borderline"),
    ("Clairaudient", "Heavy-metal (THC, 2022)", "substance", "substance"),
    ("Clairvoyant", "Mimi apparition (~2mo ago)", "WAKING", "yes"),
    ("Clairvoyant", "Ceiling-tile dilation (ketamine 2-3 / ~200 \u2248 1-1.5%)", "substance", "substance"),
    ("Somatic /\nwillful", "Kundalini / metta (waking)", "willful", "willful"),
    ("Liminal\n(not counted)", "OBEs (dozen+)", "hypnagogic", "no"),
    ("Liminal\n(not counted)", "Chanting + kundalini (hypnagogic)", "hypnagogic", "no"),
    ("Claircognitive", "False knowings", "waking incl. ketamine", "clean"),
]
state_color = {"hypnagogic": "#9ec6e0", "substance": "#e0b66e", "WAKING": "#d98b8b",
               "willful": "#c9b6e0", "waking incl. ketamine": "#bcd9c4"}
fig, ax = plt.subplots(figsize=(11.4, 6.9))
ax.axis("off"); ax.set_xlim(0, 10); ax.set_ylim(0, 10)
ax.text(5, 9.62, "B93 Fig 2 (corrected B94) — Brandon's WHOLE-LIFE anomalous-perception ledger",
        ha="center", fontsize=12, fontweight="bold")
ax.text(5, 9.08, "#69 finding: anomalies cluster in the SENSORY clair-channels; the KNOWING channel stays clean",
        ha="center", fontsize=9.2, color="#444", style="italic")
y = 8.55
for chan, lab, state, counted in events:
    fc = state_color.get(state, "#dddddd")
    ax.add_patch(plt.Rectangle((0.4, y-0.40), 9.2, 0.82, fc=fc, ec="k", lw=0.8, alpha=0.85))
    ax.text(0.7, y+0.02, f"{chan}", fontsize=9, fontweight="bold", va="center")
    ax.text(3.3, y+0.02, lab, fontsize=8.8, va="center")
    tag = {"yes": "WAKING HALLUCINATION", "no": "liminal (not counted)",
           "borderline": "hypnagogic (borderline)", "substance": "substance-occasioned",
           "willful": "WILLFUL \u2014 meditation/mania (induced)",
           "clean": "\u2248 0  (channel clean)"}[counted]
    tc = ("#7a1d12" if counted == "yes" else "#1e5e40" if counted == "clean"
          else "#5b3a8a" if counted == "willful" else "#555")
    ax.text(9.4, y+0.02, tag, fontsize=8.0, ha="right", va="center", color=tc, fontweight="bold")
    y -= 1.0
ax.add_patch(plt.Rectangle((0.4, 0.05), 9.2, 0.86, fc="#e8eef5", ec="#2E7D5B", lw=1.6))
ax.text(5, 0.48,
        "CORRECTED (B94): ketamine perceptual events 2-3 / ~200 sessions \u2248 1-1.5% \u2014 near-absence STANDS;\n"
        "claircognitive false-knowings \u2248 0. Kundalini/metta waking = WILLFUL (practice/mania), not spontaneous hallucination.",
        ha="center", fontsize=8.3, fontweight="bold", color="#1e5e40")
fig.tight_layout()
fig.savefig("analyses/pass77_b93_proposition_types/fig2_hallucination_ledger.png", dpi=130,
            bbox_inches="tight")
print("wrote fig2"); print("B93 figures done.")
