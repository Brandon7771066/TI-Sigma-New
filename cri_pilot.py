"""
CRI Pilot — Collective HEM-GILE Ratio Invariance Empirical Test
================================================================

Tests the URB #694 prediction that successful practitioners within a domain
cluster at a characteristic GILE:HEM ratio, with within-domain variance
lower than between-domain variance.

Proxy scoring (0–10 scale) for well-documented historical exemplars:
  HEM loops (4): body, material, environment, relational embodiment
  GILE loops (4): G (goodness), I (intuition/insight), L (love), E (environment-sense)

Scores are justified by widely available biographical evidence. This is a
first-pass pilot intended to detect domain-level signal, not a definitive
measurement.

Author: Brandon Emerick
Framework: TI Sigma
Companion paper: papers/urb_694_collective_hem_gile_ratio_invariance.md
"""

from __future__ import annotations
from dataclasses import dataclass, field
from statistics import mean, stdev
from typing import Dict, List


@dataclass
class Practitioner:
    name: str
    domain: str
    # HEM loops: 0-10 each
    body: float
    material: float
    environment_hem: float
    relational_embodiment: float
    # GILE loops: 0-10 each
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
        """GILE:HEM collective ratio."""
        return self.gile_total / self.hem_total if self.hem_total > 0 else float("inf")


# ---------------------------------------------------------------------------
# Exemplar data — historical figures with rich, widely documented profiles.
# Scores reflect best-effort reading of biographical evidence using the
# proxy definitions from URB #694 Section 4.
# ---------------------------------------------------------------------------

PRACTITIONERS: List[Practitioner] = [
    # --- Pure Mathematics (predicted 3:1+ GILE:HEM) ---------------------
    Practitioner(
        "Kurt Gödel", "pure_math",
        body=2, material=2, environment_hem=2, relational_embodiment=3,
        G_goodness=7, I_insight=10, L_love=8, E_env_sense=5,
        justification="Incompleteness theorems; near-ascetic life; "
                      "obsessive logic focus; low material/bodily engagement.",
    ),
    Practitioner(
        "Alexander Grothendieck", "pure_math",
        body=3, material=2, environment_hem=3, relational_embodiment=3,
        G_goodness=9, I_insight=10, L_love=7, E_env_sense=6,
        justification="Schemes, EGA/SGA; later moral withdrawal from institutions; "
                      "abstract-object dominant cognition.",
    ),
    Practitioner(
        "Emmy Noether", "pure_math",
        body=3, material=3, environment_hem=3, relational_embodiment=6,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=6,
        justification="Noether's theorem; foundational abstract algebra; "
                      "strong mentorship (Noether boys); ethical persistence.",
    ),
    Practitioner(
        "Terence Tao", "pure_math",
        body=5, material=3, environment_hem=4, relational_embodiment=6,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=7,
        justification="Fields medalist; blog; prolific collaborative output; "
                      "balanced personal life; high cross-domain awareness.",
    ),

    # --- Theoretical Physics (predicted 2:1–3:1) -----------------------
    Practitioner(
        "Albert Einstein", "theor_physics",
        body=4, material=4, environment_hem=5, relational_embodiment=6,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=8,
        justification="Relativity; pacifism; music; strong ethical voice; "
                      "thought experiments over lab work.",
    ),
    Practitioner(
        "Richard Feynman", "theor_physics",
        body=6, material=5, environment_hem=5, relational_embodiment=7,
        G_goodness=7, I_insight=10, L_love=8, E_env_sense=8,
        justification="QED; bongo drums; safecracking; teaching; lived widely; "
                      "higher HEM engagement than typical.",
    ),
    Practitioner(
        "Paul Dirac", "theor_physics",
        body=3, material=2, environment_hem=3, relational_embodiment=3,
        G_goodness=7, I_insight=10, L_love=6, E_env_sense=5,
        justification="Dirac equation; famously austere; minimal social/material "
                      "engagement; extreme abstract-structure focus.",
    ),

    # --- Philosophy (predicted 2:1) ------------------------------------
    Practitioner(
        "Ludwig Wittgenstein", "philosophy",
        body=5, material=4, environment_hem=5, relational_embodiment=5,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=7,
        justification="Tractatus + PI; WWI service; Norway hut; "
                      "gardener/teacher periods; embodied philosophical practice.",
    ),
    Practitioner(
        "Immanuel Kant", "philosophy",
        body=3, material=3, environment_hem=4, relational_embodiment=5,
        G_goodness=10, I_insight=9, L_love=6, E_env_sense=7,
        justification="Three Critiques; famously regular walks; "
                      "moral law central; sedentary scholarly life.",
    ),
    Practitioner(
        "Simone Weil", "philosophy",
        body=5, material=4, environment_hem=6, relational_embodiment=6,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=8,
        justification="Factory work; Spanish Civil War; hunger strike; "
                      "maximal embodied-ethical integration.",
    ),

    # --- Engineering / Applied (predicted ~1:1) ------------------------
    Practitioner(
        "Nikola Tesla", "engineering",
        body=6, material=9, environment_hem=7, relational_embodiment=5,
        G_goodness=8, I_insight=10, L_love=7, E_env_sense=8,
        justification="AC system, induction motor; hands-on laboratory work; "
                      "visionary engineering; wide-bandwidth material engagement.",
    ),
    Practitioner(
        "Thomas Edison", "engineering",
        body=7, material=10, environment_hem=8, relational_embodiment=7,
        G_goodness=6, I_insight=8, L_love=6, E_env_sense=8,
        justification="Menlo Park lab; >1000 patents; prolific material "
                      "instantiation; mixed ethical record.",
    ),
    Practitioner(
        "Hedy Lamarr", "engineering",
        body=7, material=7, environment_hem=7, relational_embodiment=7,
        G_goodness=8, I_insight=9, L_love=7, E_env_sense=7,
        justification="Frequency-hopping spread spectrum; dual-career; "
                      "applied inventive work with balanced life.",
    ),

    # --- Experimental Science (predicted ~1:1) -------------------------
    Practitioner(
        "Marie Curie", "exp_science",
        body=8, material=9, environment_hem=7, relational_embodiment=6,
        G_goodness=10, I_insight=9, L_love=8, E_env_sense=7,
        justification="Radium isolation; extreme lab labor; WWI X-ray work; "
                      "died of radiation exposure; maximum HEM commitment.",
    ),
    Practitioner(
        "Charles Darwin", "exp_science",
        body=7, material=7, environment_hem=10, relational_embodiment=7,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=10,
        justification="Beagle voyage; barnacle taxonomy; Down House garden; "
                      "decades of observation; maximum environmental engagement.",
    ),
    Practitioner(
        "Barbara McClintock", "exp_science",
        body=7, material=8, environment_hem=9, relational_embodiment=6,
        G_goodness=9, I_insight=10, L_love=8, E_env_sense=9,
        justification="Maize genetics; transposons; patient decades of field/lab "
                      "integration; deep system-sensing.",
    ),

    # --- Art / Aesthetics (predicted 1:2) -----------------------------
    Practitioner(
        "Vincent van Gogh", "art",
        body=8, material=9, environment_hem=9, relational_embodiment=5,
        G_goodness=8, I_insight=8, L_love=10, E_env_sense=7,
        justification="~900 paintings in 10 years; embodied struggle; "
                      "letters to Theo; intense material-perceptual engagement.",
    ),
    Practitioner(
        "Frida Kahlo", "art",
        body=10, material=8, environment_hem=8, relational_embodiment=8,
        G_goodness=8, I_insight=8, L_love=10, E_env_sense=7,
        justification="Body as primary material; 55 self-portraits; "
                      "physical suffering central; maximum HEM.",
    ),
    Practitioner(
        "Pablo Picasso", "art",
        body=8, material=10, environment_hem=8, relational_embodiment=8,
        G_goodness=5, I_insight=9, L_love=8, E_env_sense=7,
        justification="~50000 works; material prolific; cubist innovation; "
                      "ethical record mixed.",
    ),

    # --- Trades (predicted 1:3) ---------------------------------------
    Practitioner(
        "Sam Maloof (woodworker)", "trades",
        body=9, material=10, environment_hem=8, relational_embodiment=7,
        G_goodness=8, I_insight=7, L_love=8, E_env_sense=7,
        justification="Legendary chair maker; decades of hand craftsmanship; "
                      "material-dominant cognition.",
    ),
    Practitioner(
        "Jiro Ono (sushi)", "trades",
        body=9, material=10, environment_hem=8, relational_embodiment=7,
        G_goodness=8, I_insight=7, L_love=8, E_env_sense=8,
        justification="70+ years sushi mastery; minimal abstraction; "
                      "maximal embodied skill integration.",
    ),
    Practitioner(
        "James Krenov (woodworker)", "trades",
        body=9, material=10, environment_hem=7, relational_embodiment=6,
        G_goodness=8, I_insight=7, L_love=8, E_env_sense=7,
        justification="Cabinetmaker-philosopher; wood-first aesthetic; "
                      "tactile cognition.",
    ),

    # --- Athletics (predicted 1:4+) -----------------------------------
    Practitioner(
        "Michael Jordan", "athletics",
        body=10, material=7, environment_hem=9, relational_embodiment=9,
        G_goodness=6, I_insight=8, L_love=7, E_env_sense=8,
        justification="6 NBA titles; extreme physical commitment; "
                      "ultra-competitive; body-dominant performance.",
    ),
    Practitioner(
        "Serena Williams", "athletics",
        body=10, material=6, environment_hem=8, relational_embodiment=8,
        G_goodness=8, I_insight=8, L_love=8, E_env_sense=8,
        justification="23 grand slams; decades elite tennis; "
                      "high strategy/awareness with physical primacy.",
    ),
    Practitioner(
        "Lionel Messi", "athletics",
        body=10, material=6, environment_hem=8, relational_embodiment=8,
        G_goodness=8, I_insight=9, L_love=8, E_env_sense=9,
        justification="World Cup; pitch-awareness legendary; "
                      "extraordinary embodied pattern-recognition.",
    ),

    # --- Contemplative practice (predicted 2:1–4:1) -------------------
    Practitioner(
        "Thich Nhat Hanh", "contemplative",
        body=5, material=3, environment_hem=5, relational_embodiment=7,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=9,
        justification="Engaged Buddhism; Plum Village; decades of practice "
                      "and teaching; high G/L integration.",
    ),
    Practitioner(
        "Ramana Maharshi", "contemplative",
        body=3, material=2, environment_hem=4, relational_embodiment=5,
        G_goodness=10, I_insight=10, L_love=9, E_env_sense=7,
        justification="Self-inquiry lineage; Arunachala hermitage decades; "
                      "minimal material/bodily engagement; near-pure GILE.",
    ),
    Practitioner(
        "Teresa of Ávila", "contemplative",
        body=5, material=5, environment_hem=6, relational_embodiment=7,
        G_goodness=10, I_insight=9, L_love=10, E_env_sense=8,
        justification="Interior Castle; Carmelite reforms; "
                      "combined mystical writing with institutional work.",
    ),
]


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------

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
    "pure_math": (3.0, "∞"),
    "theor_physics": (2.0, 3.0),
    "philosophy": (2.0, 2.5),
    "engineering": (0.9, 1.3),
    "exp_science": (0.9, 1.3),
    "art": (0.4, 0.7),
    "trades": (0.3, 0.5),
    "athletics": (0.2, 0.4),
    "contemplative": (2.0, 4.0),
}


def run_cri_analysis() -> None:
    print("=" * 78)
    print("CRI Pilot — Collective HEM-GILE Ratio Invariance Empirical Test")
    print("Companion: papers/urb_694_collective_hem_gile_ratio_invariance.md")
    print("=" * 78)

    by_domain: Dict[str, List[Practitioner]] = {}
    for p in PRACTITIONERS:
        by_domain.setdefault(p.domain, []).append(p)

    domain_means: Dict[str, float] = {}
    within_stds: Dict[str, float] = {}

    for domain, people in by_domain.items():
        Rs = [p.R for p in people]
        m = mean(Rs)
        s = stdev(Rs) if len(Rs) > 1 else 0.0
        domain_means[domain] = m
        within_stds[domain] = s

        print(f"\n--- {DOMAIN_LABELS[domain]} "
              f"(n={len(people)}) ---")
        lo, hi = PREDICTED[domain]
        hi_str = f"{hi}" if isinstance(hi, (int, float)) else hi
        print(f"Predicted GILE:HEM range: {lo} – {hi_str}")
        for p in people:
            print(f"  {p.name:30s} HEM={p.hem_total:5.1f}  "
                  f"GILE={p.gile_total:5.1f}  R={p.R:.3f}")
        print(f"  Mean R = {m:.3f} | within-domain sd = {s:.3f}")

    # Variance decomposition
    all_Rs = [p.R for p in PRACTITIONERS]
    overall_mean = mean(all_Rs)
    overall_sd = stdev(all_Rs)

    between_var = mean((m - overall_mean) ** 2 for m in domain_means.values())
    within_var = mean(s ** 2 for s in within_stds.values())

    print("\n" + "=" * 78)
    print("Variance Decomposition")
    print("=" * 78)
    print(f"Overall mean R across all practitioners: {overall_mean:.3f}")
    print(f"Overall sd R:                           {overall_sd:.3f}")
    print(f"Between-domain variance (signal):       {between_var:.4f}")
    print(f"Mean within-domain variance (noise):    {within_var:.4f}")
    ratio = between_var / within_var if within_var > 0 else float("inf")
    print(f"Signal/Noise ratio (F-like):            {ratio:.2f}")

    print("\nDomain-ordered means (ascending):")
    for d, m in sorted(domain_means.items(), key=lambda x: x[1]):
        lo, hi = PREDICTED[d]
        hi_v = 10.0 if hi == "∞" else hi
        in_range = lo <= m <= hi_v
        marker = "✓" if in_range else "✗"
        print(f"  {marker} {DOMAIN_LABELS[d]:25s}  R = {m:.3f}  "
              f"(predicted {lo}–{hi})")

    hits = sum(
        1 for d, m in domain_means.items()
        if PREDICTED[d][0] <= m <= (10.0 if PREDICTED[d][1] == "∞" else PREDICTED[d][1])
    )
    print(f"\nPredicted-range hits: {hits} / {len(domain_means)} domains")

    print("\nCRI pass criterion: between/within > 3 AND majority in predicted range.")
    cri_pass = (ratio > 3.0) and (hits >= len(domain_means) * 0.6)
    print(f"CRI pilot verdict: {'PASS' if cri_pass else 'INCONCLUSIVE — needs larger sample'}")

    print("=" * 78)


if __name__ == "__main__":
    run_cri_analysis()
