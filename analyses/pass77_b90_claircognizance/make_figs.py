import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

# ---- Fig 1: payload vs wrapper flow ----
fig, ax = plt.subplots(figsize=(11.0, 6.4))
ax.axis("off"); ax.set_xlim(0,12); ax.set_ylim(0,8)
def box(x,y,w,h,txt,fc,tc="black",fs=9):
    ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle="round,pad=0.08",fc=fc,ec="k",lw=1.1,alpha=0.92))
    ax.text(x+w/2,y+h/2,txt,ha="center",va="center",fontsize=fs,color=tc,fontweight="bold")
def arrow(x1,y1,x2,y2,c="#333"):
    ax.add_patch(FancyArrowPatch((x1,y1),(x2,y2),arrowstyle="-|>",mutation_scale=16,lw=1.6,color=c))
# payload
box(0.3,5.6,2.6,1.4,"I-axis SIGNAL\n(intuited content)","#dfe7f3")
# claircognizance path (top, direct)
box(4.0,6.0,3.0,1.0,"CLAIRCOGNIZANCE\n(content = content)","#cfe6d6")
arrow(2.9,6.4,4.0,6.5)
box(8.4,5.6,3.2,1.4,"INTEGRATE into\ncoherent belief web\n\u2192 doubtable belief","#cfe6d6")
arrow(7.0,6.5,8.4,6.4)
ax.text(6.0,7.25,"direct path: no decode, preserves fallibility (#69)",ha="center",fontsize=8.4,color="#1e5e40")
# wrapped path (bottom)
box(3.6,3.0,2.4,1.1,"SENSORY WRAPPER\nvision / feeling / voice","#f3e2cf")
arrow(1.6,5.6,3.9,4.1)
box(6.6,3.0,2.2,1.1,"DECODE step\n(+error)","#f0d2c0")
arrow(6.0,3.55,6.6,3.55,"#8c2018")
box(9.4,3.0,2.4,1.1,"INTEGRATE\n(if corrigible)","#f3e2cf")
arrow(8.8,3.55,9.4,3.55)
# incorrigible branch
box(6.0,0.7,5.0,1.2,"INCORRIGIBLE outer voice \u2192 cannot doubt \u2192\nremoves error-correction + fragments ego  (\u2193 GILE-G Goodness)","#e7c4bd","#5a1410",8.4)
arrow(7.7,3.0,8.5,1.9,"#8c2018")
ax.text(6.0,4.4,"wrapped path: +decode error, +incorrigibility risk, +cross-modal conflict",ha="center",fontsize=8.4,color="#8c2018")
ax.set_title("B90 Fig 1: the WRAPPER is not the PAYLOAD \u2014 epistemic value = correctness \u00d7 coherent integration\n"
             "claircognizance adds nothing between content and integration; sensory modalities add decode + incorrigibility + conflict",
             fontsize=10.8, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b90_claircognizance/fig1_payload_vs_wrapper.png", dpi=130)
print("wrote fig1")

# ---- Fig 2: advantage flat, risk rising ----
import numpy as np
mod = ["Claircognizance\n(clear knowing)","Clairsentience\n(feeling)","Clairvoyance\n(inner image)","Clairaudience\n(inner voice)","Incorrigible\nouter voice"]
advantage = [0.06,0.09,0.11,0.08,0.04]      # net epistemic advantage ~ flat near 0
risk      = [0.05,0.20,0.36,0.55,0.92]      # fragmentation / incorrigibility risk rising
x = np.arange(len(mod)); w=0.38
fig, ax = plt.subplots(figsize=(11.0,6.2))
b1=ax.bar(x-w/2, advantage, w, label="net epistemic ADVANTAGE (I-axis)", color="#2E7D5B", edgecolor="k", lw=0.5)
b2=ax.bar(x+w/2, risk, w, label="ego-fragmentation / incorrigibility RISK (G-axis cost)", color="#b23a2e", edgecolor="k", lw=0.5)
ax.axhline(0.10, color="#2E7D5B", ls=":", lw=1.3)
ax.text(4.45,0.115,"advantage \u2248 flat, near zero",color="#1e5e40",fontsize=8.6,ha="right",fontweight="bold")
ax.set_xticks(x); ax.set_xticklabels(mod, fontsize=8.6)
ax.set_ylabel("relative magnitude (0\u20131, illustrative)", fontsize=10)
ax.set_ylim(0,1.0); ax.legend(loc="upper left", fontsize=9)
for sp in ["top","right"]: ax.spines[sp].set_visible(False)
ax.text(2.0,-0.235,"no decisive epistemic advantage from added senses; risk rises with externalization/incorrigibility  \u2192  claircognizance is RISK-DOMINANT",
        ha="center", fontsize=8.8, color="#444", transform=ax.transData)
ax.set_title("B90 Fig 2: sensory richness cannot trump coherence \u2014 advantage flat, risk rising\n"
             "(CGP-1 candidate: claircognizance supreme by RISK, not by knowing more; preserves #69 fallibility)",
             fontsize=10.8, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b90_claircognizance/fig2_advantage_flat_risk_rising.png", dpi=130)
print("wrote fig2"); print("B90 figures done.")
