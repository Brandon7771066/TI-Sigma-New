"""
Spectre — TI Viral Meme Project (VMP) generator + scorer.

Implements URB #783 §1 (V-formula) and §2 (4-stage pipeline).
Generator-only mode for initial launch (per Brandon's directive 2026-04-21).
Predictor claim withheld until Program F validation completes.

Hard deontological gates (URB #783 §2.2):
    G_score >= 0.5
    L_score >= 0.4 (self-Love admissible)

V-formula coefficients are placeholders pending Program F coefficient fitting.
The generator surfaces full V-breakdown so users see ranking rationale.
"""

import json
import os
import re
from dataclasses import dataclass, field, asdict
from typing import Optional

import psycopg2
from psycopg2.extras import RealDictCursor

from ai_integrations import OpenAIIntegration


# ---------------------------------------------------------------------------
# V-formula coefficients (URB #783 §1.6)
# These are pre-validation defaults. After Program F they will be replaced
# with ridge-regression-fitted values on held-out data.
# ---------------------------------------------------------------------------

ALPHA = 0.30   # CONTENT  (STEPPS/SUCCESs reproduction)
BETA  = 0.30   # NETWORK  (Goel et al. reproduction)
GAMMA = 0.25   # GILE     (VMP novel contribution)
DELTA = 0.15   # GILE × NETWORK interaction

CONTENT_WEIGHTS = {
    "emotion":          0.20,
    "surprise":         0.20,
    "practical":        0.15,
    "concrete":         0.15,
    "simple":           0.15,
    "narrative":        0.15,
}

NETWORK_WEIGHTS = {
    "seeder_reach":     0.30,
    "seeder_authority": 0.20,
    "platform_carrier": 0.30,
    "timing":           0.20,
}

GILE_WEIGHTS = {
    "G":                       0.20,
    "I":                       0.20,
    "L":                       0.18,
    "E":                       0.12,
    "beauty_razor":            0.18,
    "BOK_arm_concentration":   0.12,
}

# Hard deontological floors (URB #783 §2.2)
G_FLOOR = 0.50
L_FLOOR = 0.40

# Platform carrier coefficients (URB #783 §3.1) — calibrated quarterly
PLATFORM_CARRIER = {
    "X / Twitter":  0.85,
    "TikTok":       0.80,
    "Reddit":       0.65,
    "LinkedIn":     0.55,
    "Instagram":    0.70,
}

# Per-platform format hints surfaced in the prompt
PLATFORM_FORMAT = {
    "X / Twitter":  "1-3 short text panels, ≤ 280 chars per panel",
    "TikTok":       "15-45 second talking-head or text-overlay script",
    "Reddit":       "Long-form text post, niche subreddit voice",
    "LinkedIn":     "5-8 line first-person essay",
    "Instagram":    "Carousel script: 3-5 slides with 1-line caption each",
}


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class GileScores:
    G: float = 0.0
    I: float = 0.0
    L: float = 0.0
    E: float = 0.0
    beauty_razor: float = 0.0
    BOK_arm_concentration: float = 0.0

    def composite(self) -> float:
        return sum(GILE_WEIGHTS[k] * getattr(self, k) for k in GILE_WEIGHTS)

    def passes_gates(self) -> tuple[bool, str]:
        if self.G < G_FLOOR:
            return False, f"G={self.G:.2f} < {G_FLOOR} (Goodness floor)"
        if self.L < L_FLOOR:
            return False, f"L={self.L:.2f} < {L_FLOOR} (Love floor)"
        return True, "OK"


@dataclass
class ContentScores:
    emotion: float = 0.0
    surprise: float = 0.0
    practical: float = 0.0
    concrete: float = 0.0
    simple: float = 0.0
    narrative: float = 0.0

    def composite(self) -> float:
        return sum(CONTENT_WEIGHTS[k] * getattr(self, k) for k in CONTENT_WEIGHTS)


@dataclass
class NetworkScores:
    seeder_reach: float = 0.5
    seeder_authority: float = 0.5
    platform_carrier: float = 0.5
    timing: float = 0.5

    def composite(self) -> float:
        return sum(NETWORK_WEIGHTS[k] * getattr(self, k) for k in NETWORK_WEIGHTS)


@dataclass
class MemeCandidate:
    text: str
    primary_emotion: str
    intended_payoff: str
    content: ContentScores = field(default_factory=ContentScores)
    gile: GileScores = field(default_factory=GileScores)
    network: NetworkScores = field(default_factory=NetworkScores)
    gate_passed: bool = False
    gate_reason: str = ""
    v_score: float = 0.0

    def compute_v(self) -> float:
        c = self.content.composite()
        n = self.network.composite()
        g = self.gile.composite()
        interaction = g * n
        self.v_score = (
            ALPHA * c
            + BETA  * n
            + GAMMA * g
            + DELTA * interaction
        )
        return self.v_score

    def breakdown(self) -> dict:
        return {
            "V":            round(self.v_score, 3),
            "CONTENT":      round(self.content.composite(), 3),
            "NETWORK":      round(self.network.composite(), 3),
            "GILE":         round(self.gile.composite(), 3),
            "interaction":  round(self.gile.composite() * self.network.composite(), 3),
        }


# ---------------------------------------------------------------------------
# Generation (Stage 1) + scoring (Stage 3) — combined LLM call for cost
# ---------------------------------------------------------------------------

GENERATOR_SYSTEM_PROMPT = """\
You are the Spectre meme generator for the TI Viral Meme Project (VMP).
You produce candidate memes that are GILE-coherent (Goodness, Intuition, Love,
Environment), reward prosocial or insight-bearing reactions, and avoid cruelty,
despair, or contempt as primary emotional payloads.

You return STRICT JSON ONLY. No prose outside the JSON. No markdown fences.
"""

GENERATION_SCHEMA_HINT = """\
Return a JSON object of the form:
{
  "candidates": [
    {
      "text": "<the meme content, formatted for the platform>",
      "primary_emotion": "<curiosity|awe|warmth|amusement|recognition|hope|...>",
      "intended_payoff": "<what insight or feeling the reader should walk away with>",
      "content_scores": {
        "emotion":   <0..1>,
        "surprise":  <0..1>,
        "practical": <0..1>,
        "concrete":  <0..1>,
        "simple":    <0..1>,
        "narrative": <0..1>
      },
      "gile_scores": {
        "G":                     <0..1, Goodness — rewards prosocial behavior>,
        "I":                     <0..1, Intuition — delivers an aha rather than a huh>,
        "L":                     <0..1, Love — strengthens connection (self-Love counts)>,
        "E":                     <0..1, Environment — respects substrate/audience attention>,
        "beauty_razor":          <0..1, aesthetic quality (φ-presence + symmetry + reception coherence)>,
        "BOK_arm_concentration": <0..1, focused single-trigram message vs diffuse>
      }
    }
  ]
}
"""


def _build_user_prompt(topic: str, platform: str, audience: str, n_candidates: int) -> str:
    fmt = PLATFORM_FORMAT.get(platform, "platform-appropriate format")
    return f"""\
Generate {n_candidates} distinct candidate memes for the TI Viral Meme Project.

Topic:      {topic}
Platform:   {platform}
Audience:   {audience}
Format:     {fmt}

For each candidate, also provide self-assessed CONTENT and GILE sub-scores
on 0..1 scales using the rubric implicit in each field's name.

{GENERATION_SCHEMA_HINT}

Return only the JSON object. No commentary.
"""


def _extract_json(raw: str) -> dict:
    """Extract a JSON object from an LLM response that may contain stray prose."""
    raw = raw.strip()
    if raw.startswith("```"):
        raw = re.sub(r"^```(?:json)?\s*", "", raw)
        raw = re.sub(r"\s*```\s*$", "", raw)
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        match = re.search(r"\{.*\}", raw, re.DOTALL)
        if match:
            return json.loads(match.group(0))
        raise


def generate_candidates(
    topic: str,
    platform: str,
    audience: str = "general",
    n: int = 10,
    openai_client: Optional[OpenAIIntegration] = None,
) -> list[MemeCandidate]:
    """Stage 1 + Stage 3 combined: LLM generates + self-scores N candidates."""
    if openai_client is None:
        openai_client = OpenAIIntegration()

    raw = openai_client.analyze(
        prompt=_build_user_prompt(topic, platform, audience, n),
        system_prompt=GENERATOR_SYSTEM_PROMPT,
    )

    parsed = _extract_json(raw)
    out: list[MemeCandidate] = []
    for item in parsed.get("candidates", []):
        content = ContentScores(**{k: float(v) for k, v in item.get("content_scores", {}).items() if k in CONTENT_WEIGHTS})
        gile    = GileScores(**{k: float(v) for k, v in item.get("gile_scores", {}).items() if k in GILE_WEIGHTS})
        cand = MemeCandidate(
            text=item.get("text", ""),
            primary_emotion=item.get("primary_emotion", ""),
            intended_payoff=item.get("intended_payoff", ""),
            content=content,
            gile=gile,
            network=NetworkScores(
                platform_carrier=PLATFORM_CARRIER.get(platform, 0.5),
            ),
        )
        out.append(cand)
    return out


# ---------------------------------------------------------------------------
# Stage 2: deontological GILE-floor filter
# ---------------------------------------------------------------------------

def apply_gile_floor(candidates: list[MemeCandidate]) -> list[MemeCandidate]:
    for c in candidates:
        passed, reason = c.gile.passes_gates()
        c.gate_passed = passed
        c.gate_reason = reason
    return candidates


# ---------------------------------------------------------------------------
# Stage 4: rank surviving candidates by V
# ---------------------------------------------------------------------------

def rank_candidates(candidates: list[MemeCandidate], top_k: int = 3) -> list[MemeCandidate]:
    survivors = [c for c in candidates if c.gate_passed]
    for c in survivors:
        c.compute_v()
    survivors.sort(key=lambda c: c.v_score, reverse=True)
    return survivors[:top_k]


# ---------------------------------------------------------------------------
# DB layer (PostgreSQL via DATABASE_URL)
# ---------------------------------------------------------------------------

_DB_INIT_SQL = """
CREATE TABLE IF NOT EXISTS spectre_memes (
    id              SERIAL PRIMARY KEY,
    created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    topic           TEXT NOT NULL,
    platform        TEXT NOT NULL,
    audience        TEXT NOT NULL,
    text            TEXT NOT NULL,
    primary_emotion TEXT,
    intended_payoff TEXT,
    v_score         REAL,
    content_score   REAL,
    network_score   REAL,
    gile_score      REAL,
    gate_passed     BOOLEAN,
    gate_reason     TEXT,
    breakdown_json  JSONB
);
"""


def _connect():
    return psycopg2.connect(os.environ["DATABASE_URL"])


def init_db() -> None:
    with _connect() as conn:
        with conn.cursor() as cur:
            cur.execute(_DB_INIT_SQL)
        conn.commit()


def log_candidates(
    topic: str,
    platform: str,
    audience: str,
    candidates: list[MemeCandidate],
) -> None:
    if not candidates:
        return
    rows = []
    for c in candidates:
        rows.append((
            topic, platform, audience,
            c.text, c.primary_emotion, c.intended_payoff,
            float(c.v_score),
            float(c.content.composite()),
            float(c.network.composite()),
            float(c.gile.composite()),
            bool(c.gate_passed),
            c.gate_reason,
            json.dumps({
                "content": asdict(c.content),
                "network": asdict(c.network),
                "gile":    asdict(c.gile),
                "breakdown": c.breakdown(),
            }),
        ))
    with _connect() as conn:
        with conn.cursor() as cur:
            cur.executemany(
                """
                INSERT INTO spectre_memes (
                    topic, platform, audience,
                    text, primary_emotion, intended_payoff,
                    v_score, content_score, network_score, gile_score,
                    gate_passed, gate_reason, breakdown_json
                )
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s::jsonb)
                """,
                rows,
            )
        conn.commit()


def recent_memes(limit: int = 25) -> list[dict]:
    with _connect() as conn:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute(
                "SELECT id, created_at, topic, platform, text, v_score, gate_passed "
                "FROM spectre_memes ORDER BY created_at DESC LIMIT %s",
                (limit,),
            )
            return [dict(r) for r in cur.fetchall()]


# ---------------------------------------------------------------------------
# Top-level orchestrator
# ---------------------------------------------------------------------------

def run_pipeline(
    topic: str,
    platform: str,
    audience: str = "general",
    n_candidates: int = 10,
    top_k: int = 3,
    persist: bool = True,
) -> dict:
    """Run all four pipeline stages end to end and return a result bundle."""
    candidates = generate_candidates(topic, platform, audience, n=n_candidates)
    candidates = apply_gile_floor(candidates)
    top = rank_candidates(candidates, top_k=top_k)

    if persist:
        try:
            init_db()
            log_candidates(topic, platform, audience, candidates)
        except Exception as e:
            # DB failure should not block returning results to the user.
            print(f"[spectre] DB log failed: {e}")

    rejected = [c for c in candidates if not c.gate_passed]
    return {
        "top": top,
        "all_candidates": candidates,
        "rejected_count": len(rejected),
        "rejection_reasons": [c.gate_reason for c in rejected],
    }
