"""
Pass-77 B79 — Cognitive ERROR is NOT a hallucination (EHD-1). The separator is CERTAINTY under HEM-GILE.

Brandon insight (2026-05-28): "a cognitive error is not the same as a hallucination. The latter is
strongly believed (high certainty, low accuracy with HEM-GILE), while the former is not."

OPERATIONAL MODEL. Each output has accuracy a in [0,1] (P correct, HEM-GILE ground truth) and the
agent's CERTAINTY q in [0,1]. Both ERROR and HALLUCINATION are low-accuracy; what separates them is
certainty:
  - KNOWLEDGE         : high a, high q       (calibrated correct)
  - HALLUCINATION     : low  a, HIGH q       (strongly-believed wrong -> dangerous; == hyper-imagining, B78)
  - COGNITIVE ERROR   : low  a, LOW/MID q    (wrong but NOT strongly believed -> self-correctable, cheap)
  - underconfident    : high a, low q        (correct but not asserted)
HEM-GILE calibration = q tracking a (diagonal). Overconfidence gap g = q - a. Hallucination = large
positive g AT low a. Cognitive error = small g at low a. The HARM of a wrong output scales with how
strongly it is believed: harm = q * (1 - a). -> at the SAME inaccuracy, certainty is the harm multiplier.

#69 HONESTY: by-construction model; shapes/qualitative claims are the deliverable, magnitudes
illustrative. Empirical upgrade: calibration datasets (confidence vs correctness) + a self-correction
probe (does the agent revise when challenged?) to operationalize "strongly believed / incorrigible".

Budget $0, local numpy/matplotlib.
"""
import numpy as np, json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = "analyses/pass77_b79_error_vs_hallucination"
rng = np.random.default_rng(79)
N = 9000
LO, HI = 0.4, 0.6        # accuracy / certainty band splits

a = rng.uniform(0, 1, N)                       # accuracy
q = np.clip(a + rng.normal(0, 0.22, N), 0, 1)  # certainty loosely tracks accuracy + miscalibration

def quadrant(a, q):
    out = np.empty(len(a), dtype=object)
    out[(a >= HI) & (q >= HI)] = "knowledge"
    out[(a <  LO) & (q >= HI)] = "hallucination"
    out[(a <  LO) & (q <  LO)] = "cognitive_error"
    out[(a >= HI) & (q <  LO)] = "underconfident"
    out[out == None] = "ambiguous_midband"
    return out

quad = quadrant(a, q)
counts = {k: int(np.sum(quad == k)) for k in
          ["knowledge", "hallucination", "cognitive_error", "underconfident", "ambiguous_midband"]}

harm = q * (1 - a)                              # how damaging a wrong output is = certainty x inaccuracy
mask_err = quad == "cognitive_error"
mask_hal = quad == "hallucination"
harm_err = float(np.mean(harm[mask_err])) if mask_err.any() else 0.0
harm_hal = float(np.mean(harm[mask_hal])) if mask_hal.any() else 0.0

# same-inaccuracy comparison: among LOW-accuracy items (a<LO), harm as a function of certainty
low = a < LO
cbins = np.linspace(0, 1, 11)
idx = np.digitize(q[low], cbins) - 1
harm_by_cert = [float(np.mean(harm[low][idx == b])) if np.any(idx == b) else np.nan for b in range(10)]

# ---- fig1: accuracy x certainty plane with the four labelled quadrants ----
plt.figure(figsize=(7.8, 6.2))
cmap = {"knowledge": "#2a9d8f", "hallucination": "#e63946", "cognitive_error": "#457b9d",
        "underconfident": "#e9c46a", "ambiguous_midband": "#cccccc"}
for k, c in cmap.items():
    m = quad == k
    plt.scatter(a[m][:1400], q[m][:1400], s=7, c=c, alpha=.55,
                label=f"{k} (n={counts[k]})")
xs = np.linspace(0, 1, 50)
plt.plot(xs, xs, "k--", lw=1.2, label="HEM-GILE calibration (q=a)")
plt.axvspan(0, LO, color="red", alpha=0.04)
plt.text(0.02, 0.96, "HALLUCINATION\nlow accuracy + HIGH certainty\n(strongly-believed wrong)",
         fontsize=7.5, va="top", color="#9d0208")
plt.text(0.02, 0.18, "COGNITIVE ERROR\nlow accuracy + LOW certainty\n(not strongly believed)",
         fontsize=7.5, va="top", color="#1d3557")
plt.xlabel("accuracy a  (HEM-GILE ground truth)")
plt.ylabel("agent certainty q")
plt.title("Cognitive ERROR ≠ HALLUCINATION (EHD-1): both are low-accuracy;\nCERTAINTY is the separator (HEM-GILE diagonal = calibration)")
plt.legend(fontsize=7, loc="lower right"); plt.tight_layout()
plt.savefig(f"{OUT}/fig1_error_vs_hallucination_plane.png", dpi=110); plt.close()

# ---- fig2: at the SAME (low) accuracy, harm rises with certainty -> error vs hallucination ----
plt.figure(figsize=(7.8, 5))
centers = (cbins[:-1] + cbins[1:]) / 2
plt.plot(centers, harm_by_cert, "o-", color="#6a040f")
plt.axvspan(0, LO, color="#457b9d", alpha=0.12)
plt.axvspan(HI, 1, color="#e63946", alpha=0.12)
plt.text(0.04, max(np.nanmax(harm_by_cert)*0.9, 0.05), "cognitive-error zone\n(low certainty)", fontsize=8, color="#1d3557")
plt.text(0.62, max(np.nanmax(harm_by_cert)*0.5, 0.03), "hallucination zone\n(high certainty)", fontsize=8, color="#9d0208")
plt.xlabel("agent certainty q   (among LOW-accuracy outputs, a<0.4)")
plt.ylabel("harm = certainty × inaccuracy")
plt.title("Same inaccuracy, different certainty: harm scales with belief-strength\n→ hallucination is the high-certainty tail of being wrong, error the low")
plt.tight_layout()
plt.savefig(f"{OUT}/fig2_harm_scales_with_certainty.png", dpi=110); plt.close()

out = dict(
  insight="cognitive error != hallucination; both low-accuracy; certainty (strength of belief) is the "
          "separator; harm = certainty x inaccuracy; HEM-GILE diagonal = calibration reference",
  model_is_illustrative_69=("by-construction; shapes are the deliverable. Empirical upgrade: calibration "
     "datasets (confidence vs correctness) + self-correction/challenge probe to operationalize "
     "'strongly believed / incorrigible' vs revisable error."),
  bands=dict(low_below=LO, high_above=HI),
  quadrant_counts=counts,
  mean_harm=dict(cognitive_error=round(harm_err, 4), hallucination=round(harm_hal, 4),
                 ratio_hall_over_err=round(harm_hal / harm_err, 2) if harm_err else None),
  harm_by_certainty_among_low_accuracy=[None if np.isnan(x) else round(x, 4) for x in harm_by_cert],
  findings=dict(
    separator_is_certainty="hallucination (low a, high q) and cognitive error (low a, low q) share low "
       "accuracy; only certainty distinguishes them -> certainty is the EHD-1 separator, exactly as "
       "Brandon states.",
    harm_multiplier=f"mean harm hallucination {harm_hal:.3f} vs cognitive error {harm_err:.3f} "
       f"(~{(harm_hal/harm_err):.1f}x) -> at comparable inaccuracy, strongly-believed wrongness is far "
       f"more damaging; certainty is the harm multiplier.",
    ties_to_HAH1="hallucination here = the high-certainty/low-evidence hyper-imagining of B78 (HAH-1); "
       "EHD-1 supplies the certainty criterion that operationally separates HAH-1's 'hyper-imagining' "
       "from ordinary ERR.",
    calibration="HEM-GILE calibration (q=a diagonal) is the reference; hallucination is the largest "
       "DANGEROUS overconfidence gap (q>>a at low a), error a small/benign gap."),
  principles_status="EHD-1 (Error-Hallucination Distinction) introduced CANDIDATE canonical, operational "
     "refinement/twin of HAH-1 (B78). VPP-1 EXTENDED (caps/bold/italics emphasis = intonation channel, "
     "VPP-1c) - no new count. Ratification = Brandon choice. Canonical count unchanged 74.")

with open(f"{OUT}/results.json", "w") as f:
    json.dump(out, f, indent=2)

print("=== B79 error vs hallucination ===")
print("quadrant counts:", counts)
print(f"mean harm: hallucination {harm_hal:.3f} vs cognitive error {harm_err:.3f} "
      f"({(harm_hal/harm_err):.1f}x)" if harm_err else "")
print("figs: fig1_error_vs_hallucination_plane, fig2_harm_scales_with_certainty")
