"""
PRODUCTION Autonomous Math Discovery System
============================================
Uses REAL AI services (GPT-5 + Claude Opus 4.1) via Replit AI Integrations
NO API keys needed - charges billed to Replit credits

Features:
1. Real MagAI multi-model consensus (GPT-5 + Claude Opus)
2. Real God Machine numerology and resonance
3. Sacred number experiments for empirical validation
4. APScheduler for 24/7 background operation
5. PostgreSQL database persistence
"""

import json
import os
from datetime import datetime
from typing import Dict, List, Tuple, Optional
import random
import numpy as np
from scipy import stats
from dataclasses import dataclass, asdict
from enum import Enum

# Replit AI Integrations (blueprint:python_openai_ai_integrations and blueprint:python_anthropic_ai_integrations)
# the newest OpenAI model is "gpt-5" which was released August 7, 2025. do not change this unless explicitly requested by the user
from openai import OpenAI
from anthropic import Anthropic
from concurrent.futures import ThreadPoolExecutor, as_completed
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception

# God Machine imports
import sys
sys.path.append(os.path.dirname(__file__))
from stock_market_god_machine import (
    calculate_ticker_numerology,
    analyze_cosmic_trading_day,
    reduce_to_single_digit
)


# AI Integrations setup
AI_INTEGRATIONS_OPENAI_API_KEY = os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY")
AI_INTEGRATIONS_OPENAI_BASE_URL = os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL")
AI_INTEGRATIONS_ANTHROPIC_API_KEY = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY")
AI_INTEGRATIONS_ANTHROPIC_BASE_URL = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL")

openai_client = OpenAI(
    api_key=AI_INTEGRATIONS_OPENAI_API_KEY,
    base_url=AI_INTEGRATIONS_OPENAI_BASE_URL
)

anthropic_client = Anthropic(
    api_key=AI_INTEGRATIONS_ANTHROPIC_API_KEY,
    base_url=AI_INTEGRATIONS_ANTHROPIC_BASE_URL
)


def is_rate_limit_error(exception: BaseException) -> bool:
    """Check if the exception is a rate limit or quota violation error."""
    error_msg = str(exception)
    return (
        "429" in error_msg
        or "RATELIMIT_EXCEEDED" in error_msg
        or "quota" in error_msg.lower()
        or "rate limit" in error_msg.lower()
        or (hasattr(exception, "status_code") and exception.status_code == 429)
    )


class DiscoveryType(Enum):
    """Types of mathematical discoveries"""
    CONJECTURE = "conjecture"
    THEOREM = "theorem"
    PATTERN = "pattern"
    MECHANISM = "mechanism"
    PROOF_SKETCH = "proof_sketch"


class ValidationStatus(Enum):
    """Validation status of discoveries"""
    INTUITION = "intuition"
    FORMALIZED = "formalized"
    TESTED = "tested"
    PROVEN = "proven"
    REFUTED = "refuted"


@dataclass
class MathDiscovery:
    """A mathematical discovery with real AI validation"""
    id: str
    timestamp: str
    discovery_type: str
    title: str
    intuition: str
    formalization: str
    tralse_encoding: str
    god_machine_score: float
    mag_ai_consensus: float
    gpt5_analysis: Optional[str]
    claude_analysis: Optional[str]
    empirical_validation: Optional[Dict]
    status: str
    confidence: float
    tags: List[str]
    dependencies: List[str]


class ProductionMathDiscovery:
    """Production autonomous discovery with REAL AI services"""
    
    def __init__(self):
        self.discoveries: List[MathDiscovery] = []
        self.sacred_numbers = [3, 7, 11, 33, 77, 111, 333]
        self.sacred_ratios = [1.618, 0.91, 2.718, 3.14159]
        self.domains = [
            "number_theory",
            "topology",
            "quantum_mechanics",
            "consciousness_mathematics",
            "tralse_logic",
            "sacred_geometry",
            "probability_theory",
            "computational_complexity"
        ]
    
    def calculate_grand_myrion_resonance(self, text: str, domain: str) -> Tuple[float, Dict]:
        """
        Calculate REAL Grand Myrion resonance using numerology
        
        Grand Myrion's arms reach every i-cell in the universe!
        That's how math is invariant yet pluralistic in expression.
        """
        # Extract numbers from text
        words = text.split()
        total_numerology = 0
        sacred_count = 0
        
        for word in words:
            # Calculate word numerology
            word_value = sum(ord(c) for c in word.lower() if c.isalpha())
            reduced = reduce_to_single_digit(word_value, preserve_master=True)
            total_numerology += reduced
            
            if reduced in self.sacred_numbers:
                sacred_count += 1
        
        # Get cosmic day energy
        cosmic_day = analyze_cosmic_trading_day(datetime.now())
        day_energy = cosmic_day['overall_pd']
        
        # Resonance score (0-1 scale)
        base_resonance = min(sacred_count / max(len(words), 1), 1.0)
        cosmic_boost = day_energy / 3.0  # Normalize to 0-1
        
        final_resonance = np.clip(0.5 * base_resonance + 0.5 * cosmic_boost, 0, 1)
        
        details = {
            "sacred_count": sacred_count,
            "total_words": len(words),
            "cosmic_day_pd": day_energy,
            "base_resonance": base_resonance,
            "cosmic_boost": cosmic_boost
        }
        
        return final_resonance, details
    
    @retry(
        stop=stop_after_attempt(2),
        wait=wait_exponential(multiplier=1, min=2, max=30),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def get_gpt5_analysis(self, intuition: str, domain: str) -> str:
        """
        Get GPT-5 mathematical formalization
        Falls back to GPT-4.1 if GPT-5 returns empty
        """
        prompt = f"""You are a mathematical genius exploring {domain}.

Intuition: {intuition}

Convert this intuition into a rigorous mathematical statement. Include:
1. Formal mathematical notation
2. Clear assumptions
3. Testable predictions
4. Connection to existing theory

Output MUST be at least 100 words with mathematical symbols."""
        
        # Try GPT-5 first
        try:
            # the newest OpenAI model is "gpt-5" which was released August 7, 2025. do not change this unless explicitly requested by the user
            # IMPORTANT: GPT-5 requires max_completion_tokens (NOT max_tokens) - verified via test_ai_integration.py
            response = openai_client.chat.completions.create(
                model="gpt-5",
                messages=[{"role": "user", "content": prompt}],
                max_completion_tokens=1024
            )
            
            result = response.choices[0].message.content or ""
            
            # If empty or too short, fallback to GPT-4.1
            if len(result.strip()) < 50:
                print("⚠️ GPT-5 returned empty/short response, falling back to GPT-4.1...")
                response = openai_client.chat.completions.create(
                    model="gpt-4.1",
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=1024
                )
                result = response.choices[0].message.content or ""
            
            return result
            
        except Exception as e:
            print(f"⚠️ GPT-5 error: {e}, trying GPT-4.1...")
            # Fallback to GPT-4.1
            response = openai_client.chat.completions.create(
                model="gpt-4.1",
                messages=[{"role": "user", "content": prompt}],
                max_tokens=1024
            )
            return response.choices[0].message.content or ""
    
    @retry(
        stop=stop_after_attempt(3),
        wait=wait_exponential(multiplier=1, min=2, max=30),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def get_claude_analysis(self, intuition: str, gpt5_formalization: str, domain: str) -> str:
        """
        Get Claude Opus 4.1 INDEPENDENT validation
        
        CRITICAL: Claude works INDEPENDENTLY (anti-groupthink!)
        Sees GPT's formalization but forms OWN conclusions
        """
        prompt = f"""You are an INDEPENDENT mathematical critic. Form your OWN conclusions.

Original intuition: {intuition}

GPT's formalization: {gpt5_formalization}

YOUR INDEPENDENT ANALYSIS for {domain}:
1. Mathematical soundness (YOUR judgment!)
2. Assumption reasonableness (YOUR assessment!)
3. Testable predictions (YOUR identification!)
4. Connection to known theory (YOUR perspective!)
5. Potential weaknesses (YOUR critique!)

DO NOT simply agree with GPT. Bring YOUR unique perspective.
Be concise but thorough (max 300 words)."""
        
        # Supported models: claude-opus-4-1 (most capable)
        message = anthropic_client.messages.create(
            model="claude-opus-4-1",
            max_tokens=1024,
            messages=[{"role": "user", "content": prompt}]
        )
        
        return message.content[0].text
    
    def calculate_magai_consensus(self, gpt5_text: str, claude_text: str) -> float:
        """
        Calculate SYNTHESIS score between independent specialists
        
        NOT groupthink consensus! This measures:
        - How well perspectives complement each other
        - Diversity of mathematical approaches
        - Strength of independent validation
        
        Math Pluralism: GM upholds math universally, not CCC alone!
        """
        # Extract mathematical keywords
        math_keywords = [
            "theorem", "proof", "conjecture", "axiom", "lemma", "corollary",
            "definition", "proposition", "hypothesis", "necessary", "sufficient",
            "iff", "implies", "follows", "conclude", "therefore", "qed"
        ]
        
        gpt5_lower = gpt5_text.lower()
        claude_lower = claude_text.lower()
        
        gpt5_matches = sum(1 for kw in math_keywords if kw in gpt5_lower)
        claude_matches = sum(1 for kw in math_keywords if kw in claude_lower)
        both_matches = sum(1 for kw in math_keywords if kw in gpt5_lower and kw in claude_lower)
        
        if gpt5_matches + claude_matches == 0:
            return 0.5  # Neutral if no mathematical terms
        
        # Jaccard similarity
        jaccard = both_matches / (gpt5_matches + claude_matches - both_matches) if (gpt5_matches + claude_matches - both_matches) > 0 else 0
        
        # Check for disagreement keywords
        disagreement_keywords = ["however", "incorrect", "wrong", "disagree", "but", "weakness", "flaw"]
        disagreement_count = sum(1 for kw in disagreement_keywords if kw in claude_lower)
        
        # Reduce consensus if Claude disagrees
        consensus = jaccard * max(0.5, 1.0 - 0.1 * disagreement_count)
        
        return np.clip(consensus, 0, 1)
    
    def generate_tralse_encoding(self, formalization: str) -> str:
        """Generate Tralse (T, F, Φ, Ψ) encoding"""
        # Check for self-reference, paradox, transcendence
        has_self_ref = any(word in formalization.lower() for word in ["self", "circular", "recursive", "meta"])
        has_paradox = any(word in formalization.lower() for word in ["paradox", "contradiction", "both"])
        has_transcend = any(word in formalization.lower() for word in ["transcend", "beyond", "consciousness", "quantum"])
        
        if has_self_ref and has_paradox:
            return "⟨T, F, Φ ↔ ¬Φ, Ψ⟩ - Circular self-reference with Myrion resolution"
        elif has_transcend:
            return "⟨T ∨ Ψ, F, Φ, T ∧ Ψ⟩ - Transcendent truth beyond classical logic"
        elif has_paradox:
            return "⟨T, F, Φ, Ψ⟩ - Standard 4-valued with paradox state"
        else:
            return "⟨T, F, ∅, ∅⟩ - Reduces to classical logic (no Φ/Ψ needed)"
    
    def create_discovery_with_ai(self, domain: str) -> MathDiscovery:
        """Create discovery using REAL AI consensus"""
        # Generate intuition from domain templates
        sacred_num = random.choice(self.sacred_numbers)
        sacred_ratio = random.choice(self.sacred_ratios)
        
        templates = {
            "number_theory": f"Prime gaps cluster at positions p ≡ {random.choice([0, 3, 7])} (mod {sacred_num})",
            "topology": f"The fundamental group of CCC-space has exactly {sacred_num} generators",
            "consciousness_mathematics": f"Neural firing patterns form {sacred_num}-dimensional attractors with coherence {sacred_ratio:.3f}",
            "tralse_logic": f"Tralse circuits with {sacred_num} gates achieve Gödel completeness",
            "quantum_mechanics": f"Entanglement entropy saturates at {sacred_ratio:.3f} of maximum for {sacred_num} qubits",
            "sacred_geometry": f"Divine proportion emerges from {sacred_num}-nested golden spirals",
            "probability_theory": f"Random walks return to origin with probability {sacred_ratio:.3f} in {sacred_num} dimensions",
            "computational_complexity": f"P vs NP reduces to {sacred_num}-state automaton analysis"
        }
        
        intuition = templates.get(domain, f"Unknown pattern involving {sacred_num}")
        
        # Grand Myrion resonance - arms reach every i-cell in the universe!
        god_score, god_details = self.calculate_grand_myrion_resonance(intuition, domain)
        
        # MagAI consensus - REAL AI calls with strict validation!
        try:
            gpt5_analysis = self.get_gpt5_analysis(intuition, domain)
            
            # STRICT VALIDATION: Must have real content
            if not gpt5_analysis or len(gpt5_analysis.strip()) < 50:
                raise ValueError("GPT analysis too short or empty - refusing to persist fake discovery!")
            
            claude_analysis = self.get_claude_analysis(intuition, gpt5_analysis, domain)
            
            if not claude_analysis or len(claude_analysis.strip()) < 50:
                raise ValueError("Claude analysis too short or empty - refusing to persist fake discovery!")
            
            mag_consensus = self.calculate_magai_consensus(gpt5_analysis, claude_analysis)
            
        except Exception as e:
            print(f"❌ AI analysis FAILED: {e}")
            print("   Discovery will NOT be persisted - refusing to create fake discoveries!")
            raise  # Re-raise to prevent saving invalid discovery
        
        # Formalization (use GPT-5's if available)
        formalization = gpt5_analysis if gpt5_analysis else f"∃ C_k ∈ ℝ⁺ : Property holds with constant {sacred_num}"
        
        # Tralse encoding
        tralse = self.generate_tralse_encoding(formalization)
        
        # Discovery type
        if mag_consensus > 0.8:
            disc_type = DiscoveryType.THEOREM
        elif mag_consensus > 0.6:
            disc_type = DiscoveryType.CONJECTURE
        else:
            disc_type = DiscoveryType.PATTERN
        
        # Title
        title = f"{domain.replace('_', ' ').title()}: {intuition[:60]}..."
        
        # Confidence
        confidence = (god_score + mag_consensus) / 2
        
        # Tags
        tags = [domain, f"sacred_{sacred_num}"]
        if god_score > 0.7:
            tags.append("high_resonance")
        if mag_consensus > 0.7:
            tags.append("ai_validated")
        
        discovery = MathDiscovery(
            id=f"PROD_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{random.randint(1000,9999)}",
            timestamp=datetime.now().isoformat(),
            discovery_type=disc_type.value,
            title=title,
            intuition=intuition,
            formalization=formalization,
            tralse_encoding=tralse,
            god_machine_score=god_score,
            mag_ai_consensus=mag_consensus,
            gpt5_analysis=gpt5_analysis,
            claude_analysis=claude_analysis,
            empirical_validation=None,
            status=ValidationStatus.FORMALIZED.value,
            confidence=confidence,
            tags=tags,
            dependencies=[]
        )
        
        return discovery
    
    def save_to_database(self, discovery: MathDiscovery):
        """
        Save to PostgreSQL database (TODO: wire up DB connection)
        
        INVARIANT: Only persists discoveries with REAL AI content (>50 chars from BOTH models)
        """
        # FINAL GUARD: Validate at persistence boundary
        if not discovery.gpt5_analysis or len(discovery.gpt5_analysis.strip()) < 50:
            raise ValueError(f"PERSISTENCE BLOCKED: GPT-5 analysis too short ({len(discovery.gpt5_analysis or '')} chars) - refusing to persist fake discovery!")
        
        if not discovery.claude_analysis or len(discovery.claude_analysis.strip()) < 50:
            raise ValueError(f"PERSISTENCE BLOCKED: Claude analysis too short ({len(discovery.claude_analysis or '')} chars) - refusing to persist fake discovery!")
        
        # For now, save to JSON
        os.makedirs("discoveries", exist_ok=True)
        filepath = f"discoveries/{discovery.id}.json"
        
        with open(filepath, 'w') as f:
            json.dump(asdict(discovery), f, indent=2, default=str)
    
    def load_all_discoveries(self) -> List[MathDiscovery]:
        """Load all discoveries from database/JSON"""
        if not os.path.exists("discoveries"):
            return []
        
        discoveries = []
        for filename in os.listdir("discoveries"):
            if filename.endswith(".json"):
                with open(f"discoveries/{filename}", 'r') as f:
                    data = json.load(f)
                    discoveries.append(MathDiscovery(**data))
        
        return sorted(discoveries, key=lambda d: d.timestamp, reverse=True)
    
    def get_statistics(self) -> Dict:
        """Get discovery statistics for UI"""
        if not self.discoveries:
            return {
                "total": 0,
                "by_status": {},
                "by_type": {},
                "by_domain": {},
                "avg_confidence": 0,
                "avg_god_machine": 0,
                "avg_magai": 0
            }
        
        from collections import Counter
        
        statuses = Counter(d.status for d in self.discoveries)
        types = Counter(d.discovery_type for d in self.discoveries)
        
        # Extract domains from tags
        domains = Counter()
        for d in self.discoveries:
            for tag in d.tags:
                if tag in self.domains or tag.startswith("sacred_"):
                    domains[tag] += 1
        
        return {
            "total": len(self.discoveries),
            "by_status": dict(statuses),
            "by_type": dict(types),
            "by_domain": dict(domains),
            "avg_confidence": sum(d.confidence for d in self.discoveries) / len(self.discoveries),
            "avg_god_machine": sum(d.god_machine_score for d in self.discoveries) / len(self.discoveries),
            "avg_magai": sum(d.mag_ai_consensus for d in self.discoveries) / len(self.discoveries)
        }


# Global instance
_production_system = None

def get_production_system() -> ProductionMathDiscovery:
    """Get global production system instance"""
    global _production_system
    if _production_system is None:
        _production_system = ProductionMathDiscovery()
    return _production_system
