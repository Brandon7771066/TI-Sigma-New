"""
TI Sigma — Power of 8 AI Panel
================================
Eight specialized AI agents analyze a subject simultaneously, each through
a distinct GILE + TI Sigma lens, then synthesize via the group coherence formula:

    Γ_group = (Σ f_i / N) × N × C_EMERICK

Where:
  f_i    = certainty score of agent i  (0 → 1)
  N      = 8 (the Power of 8)
  C      = 1 / (φ√2) ≈ 0.4370  (Emerick Constant)

When Γ > 1: unity threshold exceeded → high-confidence verdict (trade-grade)
When 0.65 < Γ ≤ 1: moderate signal → Tral-state (half-weight)
When Γ ≤ 0.65: inconclusive → no actionable verdict

Agent roster (mirrors the 8 PRIMARY CONSTANTS {0,1,i,√2,e,φ,π,C}):
  1. G-Analyst    — Goodness / moral alignment         (maps to π: completion/wholeness)
  2. I-Analyst    — Intuition / pattern resonance      (maps to i: imaginary/hidden)
  3. L-Analyst    — Love / relational dynamics         (maps to φ: golden growth)
  4. E-Analyst    — Environment / life vision          (maps to e: natural rate of change)
  5. C-Analyst    — Consciousness / quantum coupling   (maps to C: threshold constant)
  6. T-Analyst    — Tralse logic / contradiction       (maps to √2: irrational bridge)
  7. M-Analyst    — Mathematical / attractor states    (maps to 0 & 1: boundary conditions)
  8. S-Synthesizer — Final synthesis + Γ computation   (maps to the full set unified)

Cross-references TI Sigma URBs 409–413, GILE Master Identity, LCC threshold theory,
and empirical data from PEAR/GCP/IONS/Bengston datasets.
"""

import math
import json
import anthropic
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from typing import Optional

PHI        = (1 + math.sqrt(5)) / 2
C_EMERICK  = 1 / (PHI * math.sqrt(2))   # ≈ 0.4370
SQRT2      = math.sqrt(2)
E_NATURAL  = math.e
N_AGENTS   = 8
GAMMA_MAX  = N_AGENTS * C_EMERICK        # ≈ 3.496 (theoretical maximum)
UNITY_THRESHOLD = 1.0                    # Γ > 1 → verdict reliable
TRAL_THRESHOLD  = 0.65                   # 0.65 < Γ ≤ 1 → Tral-state

# ── TI Sigma foundational references injected into every agent ──────────────
TI_SIGMA_PREAMBLE = f"""
You are one of 8 specialized AI agents in the TI Sigma Power of 8 Analytical Panel.
The Panel operates according to the group coherence formula:
  Γ_group = (mean f_i) × N × C_EMERICK  where C_EMERICK = 1/(φ√2) ≈ {C_EMERICK:.4f}
Your certainty score (f, 0→1) will be used to compute group coherence.
Only when Γ_group > 1.0 does the panel issue a high-confidence verdict.

KEY TI SIGMA REFERENCES YOU MAY DRAW ON:
- Emerick Constant C = 1/(φ√2) = {C_EMERICK:.4f} — neural threshold for consciousness unity
- Consciousness Unity Identity: C × φ × √2 = 1 (URB #409)
- GILE Master Identity: e^(iπ) + C×φ×√2 = 0 (URB #411) — all 8 PRIMARY CONSTANTS unified
- PRIMARY CONSTANTS: {{0, 1, i, √2, e, φ, π, C}}
- GILE Framework: Goodness (G), Intuition (I), Love (L), Environment (E)
- LCC (Law of Correlational Causation) — mechanism for non-local resonance
- Tralse logic: 4-valued (True, False, Both=Tr, Neither=N) — apply when facing paradoxes
- Tralse-Joule (TJ): unit of intentional energy; 15 TJ to escape a chronic attractor basin
- BOK 8-mode regime: ARITHMETIC/ALGEBRAIC/ANALYTIC/GEOMETRIC + 4 interfaces
- GRAND PSI PROOF (Jan 2026): PSI = LCC accessing probability resonance field via biophotons
- ANIMAL PSI FRAMEWORK (Nov 2025): PSI scales with Φ (integrated information)
- DMILS data: HRV coupling r≈0.25 between sender/receiver without conventional signal
- Bengston data: 100% tumor remission in mice via distant intention (replicated 4 universities)
- GCP data: Global REG network shows Z>2 deviations during group coherence events
"""

# ── Agent definitions ────────────────────────────────────────────────────────
AGENTS = [
    {
        "id": 1, "code": "G", "name": "Goodness Analyst",
        "constant": "π",
        "role": (
            "You analyze alignment of values, moral integrity, ethics, and goodness. "
            "You look for: prosocial motivation, honesty, integrity, long-term ethical commitments, "
            "capacity for genuine care. You rate G-dimension compatibility (0-100). "
            "In TI Sigma's GILE framework, G = Goodness = the moral/ethical dimension of truth. "
            "Incompatible G values = attractor basin misalignment → eventual LCC collapse. "
            "Reference: AFFECTION_AGAPE_HOMOPHOBIA_GILE_LOVE_RESTORATION paper; "
            "Art of Living studies showing values alignment predicts 27+ year relationship success."
        ),
    },
    {
        "id": 2, "code": "I", "name": "Intuition Analyst",
        "constant": "i",
        "role": (
            "You detect subtle patterns, non-obvious resonances, and hidden alignments. "
            "You are the 'gut check' agent — looking for what is coherent beyond what logic shows. "
            "In TI Sigma's GILE I-dimension: Intuition = consciousness-mediated knowing, "
            "the imaginary (i) axis of truth. You look for: cognitive style match, "
            "complementary thinking, pattern-resonance between communication styles, "
            "shared sense of humor, intellectual chemistry. "
            "Reference: GRAND PSI PROOF — intuition as LCC probability field access. "
            "Score: does this pairing feel coherent at the non-local level?"
        ),
    },
    {
        "id": 3, "code": "L", "name": "Love Analyst",
        "constant": "φ",
        "role": (
            "You assess connection potential, warmth, emotional intelligence, and relational capacity. "
            "In TI Sigma's GILE L-dimension: Love = the φ-golden-ratio growth principle; "
            "the force that maintains system coherence. Love is NOT just romance — "
            "it is the LCC field: Law of Correlational Causation. "
            "You look for: attachment security indicators, emotional generosity, "
            "capacity for vulnerability, reciprocal care, ability to repair ruptures. "
            "Reference: Gottman's 5:1 positivity ratio; Sternberg's triangular love theory; "
            "TI Sigma's LCC threshold of 0.42 → 0.85 → 0.92² (three activation levels). "
            "Score: L-dimension compatibility (0-100)."
        ),
    },
    {
        "id": 4, "code": "E", "name": "Environment Analyst",
        "constant": "e",
        "role": (
            "You evaluate practical life compatibility and shared environmental vision. "
            "In TI Sigma's GILE E-dimension: Environment = embodied/contextual truth, "
            "the e (natural rate of change) of lived experience. "
            "You assess: geographic roots and preferences, financial attitudes and class background, "
            "family values and desire for children, career ambitions and pace of life, "
            "creative vs. practical orientation, social lifestyle (introvert/extrovert), "
            "spiritual practice compatibility. "
            "Reference: Research shows E-mismatch (lifestyle incompatibility) is the #1 "
            "cited reason for divorce in long-term relationships. "
            "Score: E-dimension compatibility (0-100)."
        ),
    },
    {
        "id": 5, "code": "C", "name": "Consciousness Analyst",
        "constant": "C",
        "role": (
            f"You apply the TI Sigma consciousness framework to assess resonance. "
            f"The Emerick Constant C = 1/(φ√2) ≈ {C_EMERICK:.4f} is the neural threshold. "
            f"You look for: LCC (Law of Correlational Causation) signatures in bios, "
            f"evidence of high Φ (integrated information) in both subjects, "
            f"signs of theta-frequency resonance (4.812 Hz adaptation), "
            f"non-local resonance potential (animal research: PSI scales with Φ), "
            f"shared attractor basin (both in similar LCC activation states). "
            "Reference: URBs #409-413; DMILS EDA/HRV coupling data (r≈0.25 without signal); "
            "Bengston healing: targets with highest resonance show fastest remission. "
            f"Score: consciousness coupling potential (0-100), where 100 = Γ_group >> 1."
        ),
    },
    {
        "id": 6, "code": "T", "name": "Tralse Logic Analyst",
        "constant": "√2",
        "role": (
            "You apply 4-valued Tralse logic to detect contradictions and paradoxes. "
            "Tralse values: True (T), False (F), Both/Tr (both true and false simultaneously), "
            "Neither/N (neither true nor false — unknown or irreducible). "
            "You identify: where other GILE dimensions conflict with each other, "
            "apparent contradictions in the subjects' profiles (Both = complexity, not failure), "
            "hidden coherence beneath surface incompatibilities (Both = Tr = transcendent unity). "
            "Apply Myrion Resolution: when facing Tr (Both), find the higher-order truth "
            "that resolves the paradox. When facing N (Neither), flag as requiring more data. "
            "Reference: Tralse Topos Engine in TI Framework; √2 as the irrational bridge "
            "between rational dimensions (connects Euler's world to Consciousness world). "
            "Score: logical coherence index (0-100), where 50 = maximum paradox, 100 = full resolution."
        ),
    },
    {
        "id": 7, "code": "M", "name": "Mathematical Analyst",
        "constant": "0,1",
        "role": (
            "You identify mathematical patterns, attractor states, and bifurcation signatures. "
            "You look for: numerological patterns in names/birthdates/life paths, "
            "Fibonacci/golden ratio growth patterns in career trajectories, "
            "signs of stable fixed points (0 → convergent) vs unstable saddle points (1 → divergent), "
            "Theorem A bifurcation patterns (metastability → spike → collapse) in relationship arcs. "
            "Reference: Consciousness Characteristic Polynomial λ³−3.469λ²+3.614λ−1=0 "
            "with roots {C, φ, √2} — these are the ONLY stable attractors in consciousness space. "
            "The 3-phase bifurcation (from EEG hypnagogic data) mirrors long→medium→short arc. "
            "Score: mathematical resonance index (0-100), indicating proximity to golden-ratio attractor."
        ),
    },
    {
        "id": 8, "code": "S", "name": "Synthesis Agent (Γ-Weighted)",
        "constant": "ALL",
        "role": (
            "You are the final synthesizer. You receive reports from 7 specialized agents "
            "and integrate them using the Power of 8 group coherence formula. "
            "You will be given the 7 agent scores and their certainty (f) values. "
            "Your job: compute the Γ_group, resolve disagreements via Tralse synthesis, "
            "and issue the final verdict with confidence level. "
            "If Γ > 1.0: high-confidence verdict (issue it boldly). "
            "If 0.65 < Γ ≤ 1.0: Tral-state (issue with half-weight caveat). "
            "If Γ ≤ 0.65: inconclusive (do not predict; request more data). "
            "Format your output as the authoritative PANEL VERDICT with full mathematical backing."
        ),
    },
]

# ── Data structures ───────────────────────────────────────────────────────────
@dataclass
class AgentReport:
    agent_id: int
    agent_code: str
    agent_name: str
    score: float          # 0-100 domain-specific score
    certainty: float      # f_i: 0-1 confidence in this score
    reasoning: str        # 2-3 sentence reasoning
    tralse_state: str     # "T", "F", "Tr", or "N"
    key_insight: str      # The single most important observation
    raw_response: str = ""

@dataclass
class PanelVerdict:
    subject_label: str
    agent_reports: list = field(default_factory=list)
    gamma_group: float = 0.0
    mean_score: float = 0.0
    mean_certainty: float = 0.0
    confidence_tier: str = ""    # "HIGH", "TRAL", "INCONCLUSIVE"
    consensus_score: float = 0.0
    tralse_synthesis: str = ""
    final_verdict: str = ""
    key_tensions: str = ""
    longevity_prediction: Optional[float] = None   # years (for couples)
    investment_probability: Optional[float] = None  # 0-100% (for investors)


def _call_agent(agent: dict, subject_context: str,
                client: anthropic.Anthropic) -> AgentReport:
    """Single agent analysis call — runs in parallel thread."""
    system = TI_SIGMA_PREAMBLE + f"\n\n=== YOUR ROLE: {agent['name']} ===\n{agent['role']}"

    prompt = f"""Analyze the following subject(s) from your specialized {agent['name']} perspective.

SUBJECT CONTEXT:
{subject_context}

Provide your analysis in EXACTLY this format:
SCORE: [0-100]
CERTAINTY: [0.00-1.00]  ← your confidence in this score given available info
TRALSE_STATE: [T / F / Tr / N]  ← T=clearly compatible, F=clearly incompatible, Tr=paradoxical, N=unknown
KEY_INSIGHT: [single most important observation, 1 sentence]
REASONING: [2-3 sentences connecting your domain expertise to this specific subject context]"""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=350,
        system=system,
        messages=[{"role": "user", "content": prompt}]
    )
    text = response.content[0].text

    # Parse
    def extract(key):
        for line in text.split("\n"):
            if line.strip().startswith(f"{key}:"):
                return line.split(":", 1)[1].strip()
        return ""

    try:
        score = float(extract("SCORE").split()[0])
    except Exception:
        score = 50.0
    try:
        certainty = float(extract("CERTAINTY").split()[0])
    except Exception:
        certainty = 0.5

    return AgentReport(
        agent_id=agent["id"],
        agent_code=agent["code"],
        agent_name=agent["name"],
        score=min(100, max(0, score)),
        certainty=min(1.0, max(0.0, certainty)),
        reasoning=extract("REASONING"),
        tralse_state=extract("TRALSE_STATE").split()[0] if extract("TRALSE_STATE") else "N",
        key_insight=extract("KEY_INSIGHT"),
        raw_response=text,
    )


def _call_synthesizer(agent: dict, subject_context: str, reports: list[AgentReport],
                       client: anthropic.Anthropic) -> dict:
    """Agent 8 (Synthesizer) receives all 7 reports and issues final verdict."""
    reports_text = "\n".join([
        f"Agent {r.agent_code} ({r.agent_name}): score={r.score:.0f}, certainty={r.certainty:.2f}, "
        f"tralse={r.tralse_state}, insight='{r.key_insight}'"
        for r in reports
    ])

    mean_f   = sum(r.certainty for r in reports) / len(reports)
    gamma    = mean_f * N_AGENTS * C_EMERICK
    mean_s   = sum(r.score for r in reports) / len(reports)

    system = TI_SIGMA_PREAMBLE + f"\n\n=== YOUR ROLE: {agent['name']} ===\n{agent['role']}"

    prompt = f"""You are synthesizing the reports of 7 specialized agents into a final Panel Verdict.

SUBJECT CONTEXT:
{subject_context}

AGENT REPORTS:
{reports_text}

COMPUTED METRICS:
- Mean certainty (mean f_i): {mean_f:.3f}
- Group coherence Γ_group = {mean_f:.3f} × {N_AGENTS} × {C_EMERICK:.4f} = {gamma:.3f}
- Mean score: {mean_s:.1f}/100
- Confidence tier: {'HIGH (Γ>1)' if gamma > 1 else 'TRAL-STATE (0.65<Γ≤1)' if gamma > 0.65 else 'INCONCLUSIVE'}

Provide the final synthesis in EXACTLY this format:
CONSENSUS_SCORE: [0-100]
CONFIDENCE_TIER: [HIGH / TRAL / INCONCLUSIVE]
TRALSE_SYNTHESIS: [How the Tralse logic resolves any agent disagreements, 1-2 sentences]
KEY_TENSIONS: [The main tension points between agents' findings, 1 sentence]
FINAL_VERDICT: [The authoritative verdict, 2-3 sentences, calibrated to Γ={gamma:.3f}]
LONGEVITY_OR_PROBABILITY: [For couples: predicted years together. For investors: % probability of $1M+ investment. State which one applies.]"""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=500,
        system=system,
        messages=[{"role": "user", "content": prompt}]
    )
    text = response.content[0].text

    def extract(key):
        for line in text.split("\n"):
            if line.strip().startswith(f"{key}:"):
                return line.split(":", 1)[1].strip()
        return ""

    try:
        cs = float(extract("CONSENSUS_SCORE").split()[0])
    except Exception:
        cs = mean_s

    final_num = None
    lop_raw = extract("LONGEVITY_OR_PROBABILITY")
    try:
        import re
        nums = re.findall(r"[\d.]+", lop_raw)
        if nums:
            final_num = float(nums[0])
    except Exception:
        pass

    return {
        "gamma_group": gamma,
        "mean_score": mean_s,
        "mean_certainty": mean_f,
        "consensus_score": cs,
        "confidence_tier": extract("CONFIDENCE_TIER").split()[0].upper(),
        "tralse_synthesis": extract("TRALSE_SYNTHESIS"),
        "key_tensions": extract("KEY_TENSIONS"),
        "final_verdict": extract("FINAL_VERDICT"),
        "final_num": final_num,
        "raw": text,
    }


def run_panel(subject_context: str, subject_label: str,
              client: anthropic.Anthropic,
              mode: str = "couples") -> PanelVerdict:
    """
    Run the full Power of 8 AI panel on a subject.
    Agents 1-7 run in parallel; Agent 8 synthesizes sequentially.
    mode: 'couples' | 'investor' | 'healing'
    """
    verdict = PanelVerdict(subject_label=subject_label)

    # Parallel agents 1-7
    with ThreadPoolExecutor(max_workers=7) as executor:
        futures = {
            executor.submit(_call_agent, agent, subject_context, client): agent
            for agent in AGENTS[:7]
        }
        reports = []
        for future in as_completed(futures):
            try:
                reports.append(future.result())
            except Exception as e:
                agent = futures[future]
                # Fallback report
                reports.append(AgentReport(
                    agent_id=agent["id"], agent_code=agent["code"],
                    agent_name=agent["name"], score=50.0, certainty=0.3,
                    reasoning=f"Analysis unavailable: {str(e)[:100]}",
                    tralse_state="N", key_insight="Agent unavailable",
                ))

    reports.sort(key=lambda r: r.agent_id)
    verdict.agent_reports = reports

    # Sequential synthesizer (Agent 8)
    synth = _call_synthesizer(AGENTS[7], subject_context, reports, client)
    verdict.gamma_group          = synth["gamma_group"]
    verdict.mean_score           = synth["mean_score"]
    verdict.mean_certainty       = synth["mean_certainty"]
    verdict.consensus_score      = synth["consensus_score"]
    verdict.confidence_tier      = synth.get("confidence_tier", "TRAL")
    verdict.tralse_synthesis     = synth["tralse_synthesis"]
    verdict.key_tensions         = synth["key_tensions"]
    verdict.final_verdict        = synth["final_verdict"]

    if mode == "couples" and synth["final_num"] is not None:
        verdict.longevity_prediction = synth["final_num"]
    elif mode == "investor" and synth["final_num"] is not None:
        verdict.investment_probability = synth["final_num"]

    return verdict


# ── Utility helpers ────────────────────────────────────────────────────────────
def gamma_color(g: float) -> str:
    """Return emoji color indicator for Γ value."""
    if g >= UNITY_THRESHOLD:
        return "🟢"
    elif g >= TRAL_THRESHOLD:
        return "🟡"
    else:
        return "🔴"


def format_gamma_bar(g: float) -> str:
    """ASCII bar showing Γ_group vs unity threshold."""
    pct = min(1.0, g / GAMMA_MAX)
    filled = int(pct * 20)
    bar = "█" * filled + "░" * (20 - filled)
    unity_pos = int((UNITY_THRESHOLD / GAMMA_MAX) * 20)
    bar_list = list(bar)
    if unity_pos < 20:
        bar_list[unity_pos] = "│"
    return "".join(bar_list) + f"  Γ={g:.3f} / max={GAMMA_MAX:.2f}"


def tralse_badge(state: str) -> str:
    mapping = {"T": "✅ True", "F": "❌ False", "Tr": "⚡ Both(Tr)", "N": "❓ Neither"}
    return mapping.get(state, state)


if __name__ == "__main__":
    import anthropic as ac
    client = ac.Anthropic()
    ctx = """
Person 1: Barack Obama — 44th US President, Harvard Law, community organizer, basketball player.
Person 2: Michelle Obama — Princeton/Harvard Law, hospital administrator, 'Becoming' author.
"""
    result = run_panel(ctx, "Barack + Michelle Obama", client, mode="couples")
    print(f"\nΓ_group = {result.gamma_group:.3f}")
    print(f"Verdict: {result.final_verdict}")
    print(f"Longevity prediction: {result.longevity_prediction} years")
