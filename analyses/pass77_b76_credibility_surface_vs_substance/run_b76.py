"""
Pass-77 B76 — Credibility evaluation: SUBSTANCE vs SURFACE markers (typos/grammar/citation-count).

Brandon morning insight (2026-05-28): surface markers (typos, grammar, citation validity/count) are
WRONGLY glorified as credibility checkers; dogmatic appeal-to-authority is a fallacy; sufficient
demonstration needs no more references; aesthetics IS constitutive of truth (so typos do cost aesthetic
value) BUT the UOP caps the aesthetic GILE trait per-field AND AI can repair aesthetic surface ->
human typos/grammar should be heavily discounted. SUBSTANCE of ACTUAL CONTENT matters most.

#69 HONESTY: this is an ILLUSTRATIVE generative model. I set the data-generating process (how surface
couples to substance), so the qualitative result is by-construction, NOT an empirical measurement. Its
job is to make the logic precise and STEELMAN the surface-marker view (it is a valid proxy WHEN surface
tracks substance; it fails exactly when they decouple -- which is the case that matters). Empirical
upgrade: human-labeled corpus of articles with independent substance ratings vs surface-quality scores.

Budget $0, local numpy/scipy/matplotlib.
"""
import numpy as np, json
from scipy.stats import spearmanr
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

rng = np.random.default_rng(76)
N = 4000
OUT = "analyses/pass77_b76_credibility_surface_vs_substance"

def make_items(coupling):
    """true substance s ~ U(0,1); surface aesthetics a and citation-signal c are PROXIES that track s
    with strength `coupling` and otherwise are independent noise (incl. polished-but-empty &
    typo-ridden-but-right cases at low coupling)."""
    s = rng.uniform(0, 1, N)
    a = coupling*s + (1-coupling)*rng.uniform(0, 1, N)      # aesthetic / grammar quality
    c = coupling*s + (1-coupling)*rng.uniform(0, 1, N)      # citation count/validity signal
    return s, np.clip(a, 0, 1), np.clip(c, 0, 1)

# Evaluator = weights over (substance-read, aesthetics, citations) + a substance-reading NOISE.
# A WMI-1 "wise/metacognitive" evaluator invests effort to READ substance well (low noise, high w_s).
# A surface-heavy evaluator leans on cheap surface markers and reads substance poorly.
EVALS = {
  "surface-heavy":   dict(w_s=0.20, w_a=0.45, w_c=0.35, read_noise=0.35),
  "balanced":        dict(w_s=0.50, w_a=0.25, w_c=0.25, read_noise=0.20),
  "substance-heavy (WMI-1)": dict(w_s=0.80, w_a=0.10, w_c=0.10, read_noise=0.08),
}

def accuracy(ev, s, a, c, ai_clean=False):
    if ai_clean:                     # AI repairs aesthetic surface -> a saturates, loses its variance
        a = np.clip(0.9 + 0.05*rng.standard_normal(N), 0, 1)
    s_obs = np.clip(s + ev["read_noise"]*rng.standard_normal(N), 0, 1)
    score = ev["w_s"]*s_obs + ev["w_a"]*a + ev["w_c"]*c
    return float(spearmanr(score, s).correlation)   # vs TRUE substance

# ---- Sweep coupling (surface-substance decoupling) ----
cps = np.linspace(0.0, 1.0, 21)
curves = {name: [accuracy(ev, *make_items(cp)) for cp in cps] for name, ev in EVALS.items()}

# ---- AI-cleanup effect at a representative MODERATE coupling 0.5 ----
s, a, c = make_items(0.5)
before = {name: accuracy(ev, s, a, c, ai_clean=False) for name, ev in EVALS.items()}
after  = {name: accuracy(ev, s, a, c, ai_clean=True)  for name, ev in EVALS.items()}

# ---- Figures ----
plt.figure(figsize=(8, 5))
for name, ys in curves.items():
    plt.plot(cps, ys, marker="o", ms=3, label=name)
plt.axvspan(0.0, 0.4, color="#f4a261", alpha=0.18, label="decoupled zone (cases that matter)")
plt.xlabel("surface↔substance coupling  (1 = typos track quality, 0 = polished-but-wrong / typo-but-right)")
plt.ylabel("evaluator accuracy  (Spearman vs TRUE substance)")
plt.title("Surface markers are proxies that FAIL when decoupled from substance\n(#69 steelman: surface-heavy is fine at high coupling, collapses at low)")
plt.legend(fontsize=8); plt.tight_layout()
plt.savefig(f"{OUT}/fig1_accuracy_vs_coupling.png", dpi=110); plt.close()

plt.figure(figsize=(8, 5))
x = np.arange(len(EVALS)); w = 0.36
plt.bar(x-w/2, [before[n] for n in EVALS], w, label="before AI cleanup", color="#264653")
plt.bar(x+w/2, [after[n]  for n in EVALS], w, label="after AI cleanup (aesthetics repaired)", color="#2a9d8f")
plt.xticks(x, [n.replace(" ", "\n") for n in EVALS], fontsize=8)
plt.ylabel("accuracy (Spearman vs substance)")
plt.title("AI cleanup removes aesthetic signal -> penalizing human typos becomes LESS defensible\n(surface-heavy evaluator loses its already-weak edge; substance-heavy unaffected)")
plt.legend(fontsize=8); plt.tight_layout()
plt.savefig(f"{OUT}/fig2_ai_cleanup_effect.png", dpi=110); plt.close()

out = dict(
  insight="surface markers (typos/grammar/citation-count) are weak credibility signals; substance is primary",
  model_is_illustrative_69=("generative data-generating process is agent-set; qualitative result is "
     "by-construction. Job: make logic precise + steelman surface view. Empirical upgrade: labeled "
     "article corpus with independent substance vs surface ratings."),
  accuracy_vs_coupling={name: [round(v,4) for v in ys] for name, ys in curves.items()},
  coupling_grid=[round(x,3) for x in cps],
  ai_cleanup={"before": {k: round(v,4) for k,v in before.items()},
              "after":  {k: round(v,4) for k,v in after.items()}},
  findings=dict(
    f1_steelman="surface-heavy evaluator is COMPETITIVE only at high coupling; its accuracy COLLAPSES "
       "as coupling->0 (polished-but-wrong / typo-but-right) -- exactly the cases where credibility "
       "judgement actually matters. Surface markers aren't useless; they're proxies that fail when needed.",
    f2_substance_robust="substance-heavy (WMI-1) evaluator stays accurate across ALL coupling levels -- "
       "reading the actual content is the only coupling-robust strategy.",
    f3_ai_cleanup="when AI repairs aesthetics, surface aesthetic signal loses variance; the surface-heavy "
       "evaluator's already-weak edge erodes further while substance-heavy is unaffected -> penalizing "
       "human typos/grammar is increasingly indefensible.",
    f4_sufficiency="(not simulated; argued) once substance is demonstrated, extra citations add ~0 "
       "epistemic weight -- a parsimony/sufficiency gate symmetric with WMI-1's pragmatic info-seeking gate."),
  principle_status="CEC-1 + WMI-1 introduced as CANDIDATE canonical (ratification = Brandon choice). "
     "Canonical count unchanged 74.")

with open(f"{OUT}/results.json", "w") as f:
    json.dump(out, f, indent=2)

print("=== B76 surface-vs-substance credibility sim ===")
print("coupling grid:", [round(x,2) for x in cps][::4], "...")
for name, ys in curves.items():
    print(f"{name:26s} acc@coupling0.0={ys[0]:.3f}  @0.5={ys[10]:.3f}  @1.0={ys[-1]:.3f}")
print("\nAI-cleanup (coupling 0.5):")
for n in EVALS:
    print(f"  {n:26s} before={before[n]:.3f} -> after={after[n]:.3f}  (delta {after[n]-before[n]:+.3f})")
print("\nfigs: fig1_accuracy_vs_coupling, fig2_ai_cleanup_effect")
