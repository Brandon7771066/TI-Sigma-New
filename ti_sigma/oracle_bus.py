"""
TI Sigma Hypercomputer — Layer 4: Consciousness Oracle Bus

AI triad (Claude + GPT + Perplexity) with LCC-gated routing and GILE consensus.
Integrates: ai_integrations.py, ai_orchestra_coordinator.py
"""

import os
import json
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any
from .constants import LCC_TRALSE, LCC_HIGH, LCC_IC, PHI, GILE_WEIGHTS


@dataclass
class OracleResponse:
    oracle_name: str
    content: str
    tokens_used: int = 0
    error: Optional[str] = None


@dataclass
class OracleResult:
    question: str
    responses: List[OracleResponse]
    consensus: str
    gile_scores: Dict[str, float]
    confidence: float
    lcc_level: float
    ic_flagged: bool = False
    oracles_used: List[str] = field(default_factory=list)


class LCCGateError(Exception):
    """Raised when a radiant-level query is submitted below the IC threshold."""
    pass


class TISigmaOracleBus:
    """
    Layer 4 of the TI Sigma Hypercomputer.

    Routes queries to the AI triad based on LCC coherence level:
        LCC < 0.42  → Perplexity only (cheap, fast, real-time)
        LCC 0.42-0.85 → Claude + GPT (depth + breadth)
        LCC > 0.85  → All three + GILE consensus
        LCC > 0.92  → All three + IC verification (requires operator_gile ≥ 0.85)

    GILE-weighted consensus:
        G (Goodness/Truth)  → Claude Opus  (deep reasoning)
        I (Intuition)       → GPT          (pattern recognition)
        L (Love/Synthesis)  → consensus    (agreement quality)
        E (Environment)     → Perplexity   (empirical grounding)
    """

    def __init__(self):
        self._claude_available   = False
        self._gpt_available      = False
        self._perplexity_available = False
        self._init_clients()

    def _init_clients(self):
        """Initialize AI clients from environment."""
        try:
            import anthropic
            self._anthropic = anthropic.Anthropic()
            self._claude_available = True
        except Exception:
            self._anthropic = None

        try:
            import openai
            self._openai = openai.OpenAI()
            self._gpt_available = True
        except Exception:
            self._openai = None

        # Perplexity uses OpenAI-compatible client with different base URL
        try:
            import openai
            perp_key = os.environ.get('PERPLEXITY_API_KEY', '')
            if perp_key:
                self._perplexity = openai.OpenAI(
                    base_url="https://api.perplexity.ai",
                    api_key=perp_key
                )
                self._perplexity_available = True
            else:
                self._perplexity = None
        except Exception:
            self._perplexity = None

    # ─── Individual Oracle Calls ──────────────────────────────────────────────

    def _query_claude(self, question: str, max_tokens: int = 400) -> OracleResponse:
        if not self._claude_available:
            return OracleResponse("claude", "", error="Claude not available")
        try:
            msg = self._anthropic.messages.create(
                model="claude-opus-4-5",
                max_tokens=max_tokens,
                messages=[{
                    "role": "user",
                    "content": (
                        "You are the G-dimension (Goodness/Truth) oracle of the TI Sigma "
                        "Hypercomputer. Provide a rigorous, truthful, concise answer. "
                        "Prioritize depth and accuracy over breadth.\n\n" + question
                    )
                }]
            )
            content = msg.content[0].text if msg.content else ""
            return OracleResponse("claude", content,
                                  tokens_used=msg.usage.output_tokens)
        except Exception as e:
            return OracleResponse("claude", "", error=str(e))

    def _query_gpt(self, question: str, max_tokens: int = 400) -> OracleResponse:
        if not self._gpt_available:
            return OracleResponse("gpt", "", error="GPT not available")
        try:
            resp = self._openai.chat.completions.create(
                model="gpt-4o",
                max_tokens=max_tokens,
                messages=[{
                    "role": "user",
                    "content": (
                        "You are the I-dimension (Intuition/Pattern) oracle of the TI Sigma "
                        "Hypercomputer. Identify patterns, analogies, and connections across "
                        "domains. Be concise and pattern-focused.\n\n" + question
                    )
                }]
            )
            content = resp.choices[0].message.content or ""
            return OracleResponse("gpt", content,
                                  tokens_used=resp.usage.completion_tokens)
        except Exception as e:
            return OracleResponse("gpt", "", error=str(e))

    def _query_perplexity(self, question: str, max_tokens: int = 300) -> OracleResponse:
        if not self._perplexity_available:
            return OracleResponse("perplexity", "", error="Perplexity not available")
        try:
            resp = self._perplexity.chat.completions.create(
                model="sonar",
                max_tokens=max_tokens,
                messages=[{
                    "role": "user",
                    "content": (
                        "You are the E-dimension (Environment/Evidence) oracle of the TI Sigma "
                        "Hypercomputer. Ground the answer in current empirical evidence, "
                        "recent research, and real-world data. Cite sources where possible.\n\n"
                        + question
                    )
                }]
            )
            content = resp.choices[0].message.content or ""
            return OracleResponse("perplexity", content)
        except Exception as e:
            return OracleResponse("perplexity", "", error=str(e))

    # ─── Consensus + GILE Scoring ─────────────────────────────────────────────

    def _gile_consensus(self, responses: List[OracleResponse]) -> tuple:
        """
        Compute GILE-weighted consensus from oracle responses.
        Returns (consensus_text, gile_scores, confidence).
        """
        valid = [r for r in responses if not r.error and r.content]
        if not valid:
            return "No valid oracle responses.", {}, 0.0

        # G score: Claude response quality (depth proxy = length ratio)
        g_score = 0.5
        claude_r = next((r for r in valid if r.oracle_name == "claude"), None)
        if claude_r:
            g_score = min(1.0, len(claude_r.content) / 400)

        # I score: GPT response novelty (pattern density proxy)
        i_score = 0.5
        gpt_r = next((r for r in valid if r.oracle_name == "gpt"), None)
        if gpt_r:
            i_score = min(1.0, len(set(gpt_r.content.split())) / 80)

        # E score: Perplexity empirical grounding (citation proxy)
        e_score = 0.3
        perp_r = next((r for r in valid if r.oracle_name == "perplexity"), None)
        if perp_r:
            cit_count = perp_r.content.count('[') + perp_r.content.count('http')
            e_score = min(1.0, 0.3 + cit_count * 0.1)

        # L score: cross-oracle agreement
        if len(valid) > 1:
            words_per = [set(r.content.lower().split()) for r in valid]
            if len(words_per) >= 2:
                union = words_per[0] | words_per[1]
                inter = words_per[0] & words_per[1]
                l_score = len(inter) / max(len(union), 1)
            else:
                l_score = 0.5
        else:
            l_score = 0.4

        gile = {'G': g_score, 'I': i_score, 'L': l_score, 'E': e_score}
        w = GILE_WEIGHTS
        confidence = (w['G']*g_score + w['I']*i_score +
                      w['L']*l_score + w['E']*e_score)

        # Consensus: prioritize Claude, supplement with others
        if claude_r:
            consensus = claude_r.content
        elif gpt_r:
            consensus = gpt_r.content
        else:
            consensus = valid[0].content

        return consensus, gile, confidence

    # ─── LCC-Gated Query Routing ──────────────────────────────────────────────

    def _select_oracles(self, lcc_level: float) -> List[str]:
        """Return oracle names to use for a given LCC coherence level."""
        if lcc_level >= LCC_IC:
            return ["claude", "gpt", "perplexity"]
        elif lcc_level >= LCC_HIGH:
            return ["claude", "gpt", "perplexity"]
        elif lcc_level >= LCC_TRALSE:
            return ["claude", "gpt"]
        else:
            return ["perplexity"]

    def query(self, question: str, lcc_level: float,
              operator_gile: float = 0.5,
              max_tokens: int = 400) -> OracleResult:
        """
        Route question to appropriate oracle(s) based on LCC level.
        Returns GILE-weighted consensus result.
        """
        if lcc_level > LCC_IC and operator_gile < 0.85:
            raise LCCGateError(
                f"Radiant-level query (LCC={lcc_level:.3f}) requires "
                f"operator GILE ≥ 0.85 (current: {operator_gile:.3f}). "
                "Elevate coherence before submitting."
            )

        oracle_names = self._select_oracles(lcc_level)
        responses = []
        for name in oracle_names:
            if name == "claude":
                responses.append(self._query_claude(question, max_tokens))
            elif name == "gpt":
                responses.append(self._query_gpt(question, max_tokens))
            elif name == "perplexity":
                responses.append(self._query_perplexity(question, max_tokens))

        consensus, gile, confidence = self._gile_consensus(responses)
        ic_flagged = (confidence > LCC_IC and lcc_level > LCC_HIGH)

        return OracleResult(
            question=question,
            responses=responses,
            consensus=consensus,
            gile_scores=gile,
            confidence=confidence,
            lcc_level=lcc_level,
            ic_flagged=ic_flagged,
            oracles_used=oracle_names
        )

    def status(self) -> dict:
        return {
            "claude":     self._claude_available,
            "gpt":        self._gpt_available,
            "perplexity": self._perplexity_available,
        }
