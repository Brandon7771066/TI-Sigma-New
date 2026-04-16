"""
CRI Pilot v2 — Collective HEM-GILE Ratio Invariance Empirical Test
==================================================================

Expanded sample + domain-anchored scoring methodology.

Changes from v1:
  - Expanded from ~27 practitioners to ~54 across 9 domains
  - Domain-anchored scoring: scores span the full 0-10 range relative to
    all human endeavor (an athlete's G is not scored against a philosopher's
    G baseline — both use the universal 0-10 spread)
  - More aggressive extremes at low-GILE and low-HEM ends to remove the
    central-tendency compression seen in v1
  - Reports rank-order correlation against predictions (not just range hits)

Proxy definitions (URB #694 §4):
  HEM loops: body, material, environment, relational embodiment
  GILE loops: G (goodness), I (insight), L (love-depth), E (environment-sense)

Companion papers:
  papers/urb_694_collective_hem_gile_ratio_invariance.md
  papers/urb_695_first_mover_genuine_new_mr_initiation.md (free will refinement)
"""

from __future__ import annotations
from dataclasses import dataclass
from statistics import mean, stdev
from typing import Dict, List


@dataclass
class Practitioner:
    name: str
    domain: str
    body: float
    material: float
    environment_hem: float
    relational_embodiment: float
    G_goodness: float
    I_insight: float
    L_love: float
    E_env_sense: float
    justification: str = ""

    @property
    def hem_total(self) -> float:
        return self.body + self.material + self.environment_hem + self.relational_embodiment

    @property
    def gile_total(self) -> float:
        return self.G_goodness + self.I_insight + self.L_love + self.E_env_sense

    @property
    def R(self) -> float:
        return self.gile_total / self.hem_total if self.hem_total > 0 else float("inf")


# ---------------------------------------------------------------------------
# Scoring anchors (0-10 spans human endeavor as a whole):
#   body=1: bedridden mystic; body=10: elite athlete at peak
#   material=1: pure abstract thinker; material=10: master craftsman/prolific maker
#   environment_hem=1: isolated cell; environment_hem=10: naturalist in wild, Darwin
#   relational_embodiment=1: near-hermit; rel=10: deeply embedded in community+family
#   G=1: ethically indifferent; G=10: Weil, Gandhi-class moral commitment
#   I=1: rote follower; I=10: once-a-generation insight
#   L=1: transactional only; L=10: Teresa of Avila, deep sustained love
#   E=1: context-blind; E=10: Darwin, McClintock system-sensing
# ---------------------------------------------------------------------------

PRACTITIONERS: List[Practitioner] = [

    # --- Pure Mathematics (predicted 3:1+) ------------------------------
    Practitioner("Kurt Gödel", "pure_math",
        body=1, material=1, environment_hem=2, relational_embodiment=2,
        G_goodness=6, I_insight=10, L_love=6, E_env_sense=3,
        justification="Incompleteness; paranoid starvation death; minimal HEM."),
    Practitioner("Alexander Grothendieck", "pure_math",
        body=2, material=1, environment_hem=2, relational_embodiment=2,
        G_goodness=9, I_insight=10, L_love=6, E_env_sense=4,
        justification="EGA/SGA; Pyrenean hermitage; ethical radicalism."),
    Practitioner("Emmy Noether", "pure_math",
        body=2, material=2, environment_hem=2, relational_embodiment=5,
        G_goodness=9, I_insight=10, L_love=7, E_env_sense=4,
        justification="Noether's theorem; Noether boys mentorship; refugee."),
    Practitioner("Srinivasa Ramanujan", "pure_math",
        body=2, material=1, environment_hem=2, relational_embodiment=3,
        G_goodness=7, I_insight=10, L_love=7, E_env_sense=3,
        justification="5000+ theorems; notebooks; early death; near-pure GILE."),
    Practitioner("Alan Turing", "pure_math",
        body=5, material=3, environment_hem=3, relational_embodiment=4,
        G_goodness=9, I_insight=10, L_love=6, E_env_sense=6,
        justification="Computability; Enigma; marathon running; persecution."),
    Practitioner("Terence Tao", "pure_math",
        body=4, material=2, environment_hem=3, relational_embodiment=5,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=6,
        justification="Fields medalist; blog; broad collaborative output."),

    # --- Theoretical Physics (predicted 2:1–3:1) ----------------------
    Practitioner("Albert Einstein", "theor_physics",
        body=3, material=3, environment_hem=4, relational_embodiment=5,
        G_goodness=9, I_insight=10, L_love=7, E_env_sense=7,
        justification="Relativity; pacifism; violin; moral voice."),
    Practitioner("Richard Feynman", "theor_physics",
        body=6, material=4, environment_hem=5, relational_embodiment=7,
        G_goodness=7, I_insight=10, L_love=8, E_env_sense=7,
        justification="QED; bongos; safecracking; taught widely."),
    Practitioner("Paul Dirac", "theor_physics",
        body=2, material=1, environment_hem=2, relational_embodiment=2,
        G_goodness=7, I_insight=10, L_love=4, E_env_sense=4,
        justification="Dirac equation; legendary austerity."),
    Practitioner("Werner Heisenberg", "theor_physics",
        body=4, material=4, environment_hem=4, relational_embodiment=5,
        G_goodness=5, I_insight=10, L_love=6, E_env_sense=6,
        justification="Uncertainty principle; moral ambiguity in WWII."),
    Practitioner("Edward Witten", "theor_physics",
        body=3, material=2, environment_hem=3, relational_embodiment=4,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=7,
        justification="M-theory; Fields medalist in math; near-pure abstraction."),
    Practitioner("Lise Meitner", "theor_physics",
        body=4, material=5, environment_hem=5, relational_embodiment=5,
        G_goodness=10, I_insight=10, L_love=8, E_env_sense=8,
        justification="Fission interpretation; refused bomb work; refugee."),

    # --- Philosophy (predicted 2:1–2.5:1) -----------------------------
    Practitioner("Ludwig Wittgenstein", "philosophy",
        body=5, material=3, environment_hem=5, relational_embodiment=4,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=7,
        justification="Tractatus+PI; WWI; Norway hut; teacher/gardener."),
    Practitioner("Immanuel Kant", "philosophy",
        body=2, material=2, environment_hem=3, relational_embodiment=4,
        G_goodness=10, I_insight=9, L_love=5, E_env_sense=6,
        justification="Three Critiques; Königsberg walks; moral law."),
    Practitioner("Simone Weil", "philosophy",
        body=5, material=3, environment_hem=6, relational_embodiment=5,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=8,
        justification="Factory work; Spain; starvation; max embodied ethics."),
    Practitioner("Hannah Arendt", "philosophy",
        body=4, material=3, environment_hem=6, relational_embodiment=7,
        G_goodness=10, I_insight=10, L_love=7, E_env_sense=9,
        justification="Banality of evil; refugee; deep historical-political attunement."),
    Practitioner("Baruch Spinoza", "philosophy",
        body=3, material=4, environment_hem=3, relational_embodiment=4,
        G_goodness=10, I_insight=10, L_love=8, E_env_sense=6,
        justification="Ethics; lens-grinder; excommunicated; austere ethics."),
    Practitioner("Confucius", "philosophy",
        body=5, material=4, environment_hem=7, relational_embodiment=8,
        G_goodness=10, I_insight=9, L_love=9, E_env_sense=9,
        justification="Analects; wandering teacher; ren+li; maximal relational ethics."),

    # --- Engineering / Applied (predicted ~1:1) -----------------------
    Practitioner("Nikola Tesla", "engineering",
        body=6, material=10, environment_hem=7, relational_embodiment=3,
        G_goodness=8, I_insight=10, L_love=6, E_env_sense=7,
        justification="AC; induction motor; hands-on lab; visionary."),
    Practitioner("Thomas Edison", "engineering",
        body=7, material=10, environment_hem=8, relational_embodiment=7,
        G_goodness=5, I_insight=8, L_love=5, E_env_sense=7,
        justification="Menlo Park; 1000+ patents; mixed ethics."),
    Practitioner("Hedy Lamarr", "engineering",
        body=7, material=7, environment_hem=7, relational_embodiment=7,
        G_goodness=8, I_insight=9, L_love=7, E_env_sense=7,
        justification="Frequency hopping; dual-career; applied inventor."),
    Practitioner("Leonardo da Vinci", "engineering",
        body=7, material=9, environment_hem=8, relational_embodiment=6,
        G_goodness=7, I_insight=10, L_love=7, E_env_sense=9,
        justification="Notebooks; machines; anatomical dissection; polymathic."),
    Practitioner("Grace Hopper", "engineering",
        body=6, material=8, environment_hem=7, relational_embodiment=8,
        G_goodness=9, I_insight=9, L_love=7, E_env_sense=8,
        justification="COBOL; Navy Admiral; compiler pioneer; mentorship."),
    Practitioner("Claude Shannon", "engineering",
        body=5, material=8, environment_hem=5, relational_embodiment=5,
        G_goodness=7, I_insight=10, L_love=6, E_env_sense=7,
        justification="Information theory; juggling robots; playful inventor."),

    # --- Experimental Science (predicted ~1:1) -----------------------
    Practitioner("Marie Curie", "exp_science",
        body=8, material=10, environment_hem=7, relational_embodiment=6,
        G_goodness=10, I_insight=9, L_love=8, E_env_sense=7,
        justification="Radium; WWI X-rays; died of exposure; maximum lab HEM."),
    Practitioner("Charles Darwin", "exp_science",
        body=7, material=8, environment_hem=10, relational_embodiment=7,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=10,
        justification="Beagle; barnacles; Down House; decades of observation."),
    Practitioner("Barbara McClintock", "exp_science",
        body=7, material=8, environment_hem=10, relational_embodiment=5,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=10,
        justification="Maize transposons; patient lab decades."),
    Practitioner("Louis Pasteur", "exp_science",
        body=7, material=9, environment_hem=7, relational_embodiment=7,
        G_goodness=9, I_insight=10, L_love=7, E_env_sense=8,
        justification="Germ theory; vaccination; hands-on lab+public health."),
    Practitioner("Rosalind Franklin", "exp_science",
        body=7, material=9, environment_hem=7, relational_embodiment=5,
        G_goodness=9, I_insight=10, L_love=7, E_env_sense=8,
        justification="Photo 51; X-ray crystallography; died young from exposure."),
    Practitioner("Alexander von Humboldt", "exp_science",
        body=8, material=8, environment_hem=10, relational_embodiment=7,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=10,
        justification="Expeditions; Kosmos; integrative naturalism."),

    # --- Art / Aesthetics (predicted 1:2) -----------------------------
    Practitioner("Vincent van Gogh", "art",
        body=8, material=10, environment_hem=9, relational_embodiment=3,
        G_goodness=8, I_insight=8, L_love=10, E_env_sense=7,
        justification="900 paintings/10 years; suffering; Theo letters."),
    Practitioner("Frida Kahlo", "art",
        body=10, material=9, environment_hem=8, relational_embodiment=7,
        G_goodness=8, I_insight=8, L_love=10, E_env_sense=7,
        justification="Body-as-medium; self-portraits; suffering central."),
    Practitioner("Pablo Picasso", "art",
        body=8, material=10, environment_hem=8, relational_embodiment=8,
        G_goodness=4, I_insight=9, L_love=7, E_env_sense=7,
        justification="50000 works; prolific; ethically mixed."),
    Practitioner("Michelangelo", "art",
        body=9, material=10, environment_hem=8, relational_embodiment=5,
        G_goodness=7, I_insight=9, L_love=7, E_env_sense=7,
        justification="Sistine; David; decades of physical stone/paint labor."),
    Practitioner("Georgia O'Keeffe", "art",
        body=7, material=9, environment_hem=10, relational_embodiment=5,
        G_goodness=7, I_insight=9, L_love=8, E_env_sense=9,
        justification="New Mexico decades; deep landscape attunement."),
    Practitioner("J.S. Bach", "art",
        body=7, material=8, environment_hem=7, relational_embodiment=9,
        G_goodness=9, I_insight=10, L_love=9, E_env_sense=7,
        justification="Massive output; 20 children; profound structural invention."),

    # --- Trades / Craft (predicted 1:3) ------------------------------
    Practitioner("Sam Maloof", "trades",
        body=9, material=10, environment_hem=7, relational_embodiment=6,
        G_goodness=8, I_insight=6, L_love=8, E_env_sense=6,
        justification="Chair maker; 60+ years; hand craftsmanship."),
    Practitioner("Jiro Ono", "trades",
        body=9, material=10, environment_hem=7, relational_embodiment=6,
        G_goodness=7, I_insight=6, L_love=7, E_env_sense=7,
        justification="70+ years sushi; embodied skill."),
    Practitioner("James Krenov", "trades",
        body=9, material=10, environment_hem=7, relational_embodiment=5,
        G_goodness=7, I_insight=6, L_love=7, E_env_sense=6,
        justification="Cabinetmaker-philosopher; wood-first aesthetic."),
    Practitioner("George Nakashima", "trades",
        body=9, material=10, environment_hem=9, relational_embodiment=6,
        G_goodness=8, I_insight=6, L_love=8, E_env_sense=8,
        justification="Woodworker; respect for tree's soul; decades of practice."),
    Practitioner("Dario Cecchini (butcher)", "trades",
        body=9, material=10, environment_hem=7, relational_embodiment=7,
        G_goodness=7, I_insight=5, L_love=7, E_env_sense=6,
        justification="8th-gen butcher; Panzano; lifelong physical craft."),
    Practitioner("Dale Chihuly", "trades",
        body=8, material=10, environment_hem=7, relational_embodiment=7,
        G_goodness=6, I_insight=7, L_love=7, E_env_sense=6,
        justification="Glassblower; large studios; physical mastery."),

    # --- Athletics (predicted 1:4+) -----------------------------------
    Practitioner("Michael Jordan", "athletics",
        body=10, material=5, environment_hem=8, relational_embodiment=8,
        G_goodness=4, I_insight=7, L_love=5, E_env_sense=7,
        justification="6 NBA titles; extreme physical; ultra-competitive."),
    Practitioner("Serena Williams", "athletics",
        body=10, material=4, environment_hem=7, relational_embodiment=7,
        G_goodness=7, I_insight=7, L_love=7, E_env_sense=7,
        justification="23 slams; long dominance; balanced later life."),
    Practitioner("Lionel Messi", "athletics",
        body=10, material=4, environment_hem=7, relational_embodiment=7,
        G_goodness=7, I_insight=8, L_love=7, E_env_sense=8,
        justification="World Cup; legendary pitch awareness."),
    Practitioner("Usain Bolt", "athletics",
        body=10, material=3, environment_hem=6, relational_embodiment=6,
        G_goodness=6, I_insight=6, L_love=6, E_env_sense=5,
        justification="Fastest human; charisma; pure physical expression."),
    Practitioner("Simone Biles", "athletics",
        body=10, material=4, environment_hem=6, relational_embodiment=7,
        G_goodness=9, I_insight=7, L_love=7, E_env_sense=7,
        justification="Gymnast; mental health advocacy; physical maximum."),
    Practitioner("Roger Federer", "athletics",
        body=10, material=4, environment_hem=7, relational_embodiment=7,
        G_goodness=8, I_insight=7, L_love=7, E_env_sense=8,
        justification="20 slams; balletic awareness; sportsmanship."),

    # --- Contemplative Practice (predicted 2:1–4:1) -----------------
    Practitioner("Thich Nhat Hanh", "contemplative",
        body=4, material=2, environment_hem=4, relational_embodiment=6,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=9,
        justification="Engaged Buddhism; Plum Village; decades of teaching."),
    Practitioner("Ramana Maharshi", "contemplative",
        body=2, material=1, environment_hem=3, relational_embodiment=4,
        G_goodness=10, I_insight=10, L_love=9, E_env_sense=6,
        justification="Self-inquiry; Arunachala decades; near-pure GILE."),
    Practitioner("Teresa of Ávila", "contemplative",
        body=4, material=4, environment_hem=5, relational_embodiment=6,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=7,
        justification="Interior Castle; Carmelite reforms; mystic+institutional."),
    Practitioner("Rumi", "contemplative",
        body=4, material=3, environment_hem=5, relational_embodiment=7,
        G_goodness=10, I_insight=10, L_love=10, E_env_sense=8,
        justification="Masnavi; whirling; love-centric; Shams encounter."),
    Practitioner("Meister Eckhart", "contemplative",
        body=3, material=2, environment_hem=4, relational_embodiment=5,
        G_goodness=10, I_insight=10, L_love=9, E_env_sense=7,
        justification="Dominican mystic; detachment; ground of soul."),
    Practitioner("Tenzin Gyatso (Dalai Lama)", "contemplative",
        body=5, material=3, environment_hem=6, relational_embodiment=8,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=9,
        justification="Tibetan Buddhism; exile; global compassion teaching."),
]


DOMAIN_LABELS = {
    "pure_math": "Pure Mathematics",
    "theor_physics": "Theoretical Physics",
    "philosophy": "Philosophy",
    "engineering": "Engineering / Applied",
    "exp_science": "Experimental Science",
    "art": "Art / Aesthetics",
    "trades": "Trades / Craft",
    "athletics": "Athletics",
    "contemplative": "Contemplative Practice",
}

PREDICTED = {
    "pure_math": (3.0, 10.0),
    "theor_physics": (2.0, 3.5),
    "philosophy": (1.8, 2.8),
    "engineering": (0.9, 1.4),
    "exp_science": (0.9, 1.4),
    "art": (0.4, 0.9),
    "trades": (0.3, 0.6),
    "athletics": (0.2, 0.5),
    "contemplative": (2.0, 4.5),
}

# Predicted rank order (GILE:HEM low → high)
PREDICTED_RANK = [
    "athletics", "trades", "art",
    "engineering", "exp_science",
    "philosophy", "theor_physics", "contemplative", "pure_math",
]


def spearman_rank(observed: List[str], predicted: List[str]) -> float:
    """Simple Spearman-style rank correlation for two domain orderings."""
    n = len(observed)
    obs_rank = {d: i for i, d in enumerate(observed)}
    pred_rank = {d: i for i, d in enumerate(predicted)}
    d2 = sum((obs_rank[d] - pred_rank[d]) ** 2 for d in observed)
    return 1 - (6 * d2) / (n * (n ** 2 - 1))


def run_cri_analysis() -> None:
    print("=" * 78)
    print("CRI Pilot v2 — Collective HEM-GILE Ratio Invariance")
    print("Expanded sample + domain-anchored scoring")
    print("=" * 78)

    by_domain: Dict[str, List[Practitioner]] = {}
    for p in PRACTITIONERS:
        by_domain.setdefault(p.domain, []).append(p)

    domain_means: Dict[str, float] = {}
    within_stds: Dict[str, float] = {}

    print(f"\nTotal practitioners: {len(PRACTITIONERS)}")
    print(f"Domains: {len(by_domain)}")

    for domain, people in by_domain.items():
        Rs = [p.R for p in people]
        m = mean(Rs)
        s = stdev(Rs) if len(Rs) > 1 else 0.0
        domain_means[domain] = m
        within_stds[domain] = s

        print(f"\n--- {DOMAIN_LABELS[domain]} (n={len(people)}) ---")
        lo, hi = PREDICTED[domain]
        print(f"Predicted GILE:HEM range: {lo} – {hi}")
        for p in people:
            in_range = lo <= p.R <= hi
            marker = "✓" if in_range else "·"
            print(f"  {marker} {p.name:30s} HEM={p.hem_total:5.1f}  "
                  f"GILE={p.gile_total:5.1f}  R={p.R:.3f}")
        print(f"  Mean R = {m:.3f} | within-domain sd = {s:.3f}")

    all_Rs = [p.R for p in PRACTITIONERS]
    overall_mean = mean(all_Rs)
    overall_sd = stdev(all_Rs)

    between_var = mean((m - overall_mean) ** 2 for m in domain_means.values())
    within_var = mean(s ** 2 for s in within_stds.values())

    print("\n" + "=" * 78)
    print("Variance Decomposition")
    print("=" * 78)
    print(f"Overall mean R:                        {overall_mean:.3f}")
    print(f"Overall sd R:                          {overall_sd:.3f}")
    print(f"Between-domain variance (signal):      {between_var:.4f}")
    print(f"Mean within-domain variance (noise):   {within_var:.4f}")
    f_ratio = between_var / within_var if within_var > 0 else float("inf")
    print(f"Signal/Noise F-ratio:                  {f_ratio:.2f}")

    # Observed ranking
    observed_rank = [d for d, _ in sorted(domain_means.items(), key=lambda x: x[1])]
    rho = spearman_rank(observed_rank, PREDICTED_RANK)
    print(f"Spearman rank correlation (observed vs predicted order): {rho:.3f}")

    print("\nDomain-ordered means (ascending):")
    hits = 0
    for d, m in sorted(domain_means.items(), key=lambda x: x[1]):
        lo, hi = PREDICTED[d]
        in_range = lo <= m <= hi
        if in_range:
            hits += 1
        marker = "✓" if in_range else "✗"
        pred_rank_pos = PREDICTED_RANK.index(d) + 1
        obs_rank_pos = observed_rank.index(d) + 1
        rank_drift = pred_rank_pos - obs_rank_pos
        drift_str = f"(rank drift {rank_drift:+d})" if rank_drift else "(rank ✓)"
        print(f"  {marker} {DOMAIN_LABELS[d]:25s}  R = {m:.3f}  "
              f"predicted {lo}–{hi}  {drift_str}")

    print(f"\nPredicted-range hits: {hits} / {len(domain_means)} domains")

    cri_pass_signal = f_ratio > 3.0
    cri_pass_rank = rho > 0.80
    cri_pass_hits = hits >= len(domain_means) * 0.6

    print("\nPass criteria:")
    print(f"  F-ratio > 3.0:              {'PASS' if cri_pass_signal else 'FAIL'} "
          f"({f_ratio:.2f})")
    print(f"  Spearman rho > 0.80:        {'PASS' if cri_pass_rank else 'FAIL'} "
          f"({rho:.3f})")
    print(f"  ≥60% range hits:            {'PASS' if cri_pass_hits else 'FAIL'} "
          f"({hits}/{len(domain_means)})")

    overall = sum([cri_pass_signal, cri_pass_rank, cri_pass_hits])
    verdict = ["FAIL", "WEAK", "STRONG", "COMPLETE"][overall]
    print(f"\nCRI pilot verdict: {verdict} ({overall}/3 criteria met)")
    print("=" * 78)


if __name__ == "__main__":
    run_cri_analysis()
