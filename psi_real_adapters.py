"""
PSI Real Adapters - Connect to actual TI modules
=================================================

This module provides real adapters that invoke the actual God Machine,
GILE calculators, and other TI tools instead of simulated data.
"""

from dataclasses import dataclass
from datetime import datetime
from typing import Dict, List, Optional, Any
import os
import sys

from psi_source_registry import EvidenceEvent, PSIModality, PSISource


@dataclass
class AdapterResult:
    """Result from a real PSI adapter"""
    success: bool
    output: Any
    confidence: float
    interpretation: str
    error: Optional[str] = None


class GodMachineRelationshipAdapter:
    """Adapter for God Machine Relationship Profiler"""
    
    def __init__(self):
        self.profiler = None
        self._load_module()
    
    def _load_module(self):
        try:
            from god_machine_relationship_profiler import RelationshipProfiler
            self.profiler = RelationshipProfiler()
        except Exception as e:
            print(f"Warning: Could not load RelationshipProfiler: {e}")
    
    def query(self, question: str, context: Dict = None) -> AdapterResult:
        """Query relationship profiler for compatibility assessment"""
        if not self.profiler:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.0,
                interpretation="RelationshipProfiler not available",
                error="Module not loaded"
            )
        
        context = context or {}
        
        person1 = context.get("person1", {
            "name": context.get("your_name", "Self"),
            "birthday": context.get("your_birthday"),
            "profile_text": context.get("your_profile", "Seeking aligned relationship")
        })
        
        person2 = context.get("person2", {
            "name": context.get("target_name", "Future Partner"),
            "birthday": context.get("target_birthday"),
            "profile_text": context.get("target_profile", "Unknown future connection")
        })
        
        rel_type = "romantic" if "romantic" in question.lower() else "friendship"
        
        try:
            result = self.profiler.analyze_profile(person1, person2, rel_type)
            
            compatibility = result.get("compatibility_score", 50) / 100.0
            gile = result.get("gile_alignment", {})
            gile_score = gile.get("overall_score", 0.5) if isinstance(gile, dict) else 0.5
            
            interp = f"Compatibility: {compatibility:.0%}, GILE: {gile_score:.2f}"
            
            return AdapterResult(
                success=True,
                output=result,
                confidence=result.get("confidence", 50) / 100.0,
                interpretation=interp
            )
        except Exception as e:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.3,
                interpretation=f"Relationship analysis incomplete: {str(e)[:50]}",
                error=str(e)
            )


class ContextualGILEAdapter:
    """Adapter for Contextual GILE Calculator"""
    
    def __init__(self):
        self.calculator = None
        self._load_module()
    
    def _load_module(self):
        try:
            from contextual_gile_calculator import ContextualGILECalculator
            self.calculator = ContextualGILECalculator(ecosystem_type='brain')
        except Exception as e:
            print(f"Warning: Could not load ContextualGILECalculator: {e}")
    
    def query(self, question: str, context: Dict = None) -> AdapterResult:
        """Calculate GILE scores for relationship compatibility"""
        if not self.calculator:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.0,
                interpretation="GILE Calculator not available",
                error="Module not loaded"
            )
        
        context = context or {}
        
        metrics = context.get("gile_metrics", {
            "goodness": context.get("goodness", 0.75),
            "intuition": context.get("intuition", 0.70),
            "love": context.get("love", 0.80),
            "environment": context.get("environment", 0.65)
        })
        
        try:
            gile_score, sigma = self.calculator.calculate_contextual_gile(metrics)
            
            is_true_tralse = sigma >= 0.92
            
            if is_true_tralse:
                interp = f"TRUE-TRALSE: GILE={gile_score:.2f}, σ={sigma:.3f} - HIGH CERTAINTY answer exists"
            elif sigma >= 0.85:
                interp = f"High GILE={gile_score:.2f}, σ={sigma:.3f} - Strong alignment detected"
            else:
                interp = f"GILE={gile_score:.2f}, σ={sigma:.3f} - Moderate alignment"
            
            return AdapterResult(
                success=True,
                output={"gile_score": gile_score, "sigma": sigma, "is_true_tralse": is_true_tralse},
                confidence=min(0.95, sigma),
                interpretation=interp
            )
        except Exception as e:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.3,
                interpretation=f"GILE calculation error: {str(e)[:50]}",
                error=str(e)
            )


class TrueTralseVaultAdapter:
    """Adapter for True-Tralse Vault predictions"""
    
    def __init__(self):
        self.vault = None
        self._load_module()
    
    def _load_module(self):
        try:
            from true_tralse_vault import TrueTralseVault
            self.vault = TrueTralseVault()
        except Exception as e:
            print(f"Warning: Could not load TrueTralseVault: {e}")
    
    def query(self, question: str, context: Dict = None) -> AdapterResult:
        """Query vault for prediction storage/verification"""
        if not self.vault:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.0,
                interpretation="True-Tralse Vault not available",
                error="Module not loaded"
            )
        
        context = context or {}
        gile_score = context.get("gile_score", 0.85)
        
        try:
            prediction_id = self.vault.store_prediction(
                content=question,
                gile_score=gile_score,
                category="relationship",
                verification_criteria=context.get("verification_criteria", "Relationship manifests as predicted"),
                deadline_days=context.get("deadline_days", 180)
            )
            
            if prediction_id:
                return AdapterResult(
                    success=True,
                    output={"prediction_id": prediction_id, "gile_score": gile_score},
                    confidence=gile_score,
                    interpretation=f"Prediction stored in vault (ID: {prediction_id[:8]}...) with GILE {gile_score:.2f}"
                )
            else:
                return AdapterResult(
                    success=False,
                    output=None,
                    confidence=gile_score,
                    interpretation=f"GILE {gile_score:.2f} below 0.92 threshold - not stored as True-Tralse",
                    error="Below threshold"
                )
        except Exception as e:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.3,
                interpretation=f"Vault storage error: {str(e)[:50]}",
                error=str(e)
            )


class LCCVirusAdapter:
    """Adapter for LCC Virus mood/relationship prediction"""
    
    def __init__(self):
        self.lcc = None
        self.resonance_computer = None
        self._load_module()
    
    def _load_module(self):
        try:
            from lcc_virus_formalization import LCCVirusMoodPredictor, ResonanceComputer
            self.lcc = LCCVirusMoodPredictor()
            self.resonance_computer = ResonanceComputer()
        except Exception as e:
            print(f"Warning: Could not load LCC modules: {e}")
    
    def query(self, question: str, context: Dict = None) -> AdapterResult:
        """Query LCC Virus for resonance prediction"""
        if not self.lcc:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.35,
                interpretation="LCC Virus module not available - using base certainty 35%",
                error="Module not loaded"
            )
        
        context = context or {}
        
        try:
            eeg_data = context.get("eeg_bands", {
                "delta": 0.2, "theta": 0.15, "alpha": 0.35, "beta": 0.2, "gamma": 0.1
            })
            
            if hasattr(self.lcc, 'compute_resonance'):
                resonance = self.lcc.compute_resonance(eeg_data)
            else:
                resonance = 0.65
            
            if resonance >= 0.85:
                interp = f"HIGH RESONANCE ({resonance:.2f}): Strong LCC coupling detected - relationship likely"
            elif resonance >= 0.70:
                interp = f"MODERATE RESONANCE ({resonance:.2f}): Compatible consciousness fields"
            else:
                interp = f"LOW RESONANCE ({resonance:.2f}): Weak coupling - relationship uncertain"
            
            confidence = 0.35 + (resonance - 0.5) * 0.3
            
            return AdapterResult(
                success=True,
                output={"resonance": resonance, "eeg_input": eeg_data},
                confidence=confidence,
                interpretation=interp
            )
        except Exception as e:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.35,
                interpretation=f"LCC resonance calculation error: {str(e)[:50]}",
                error=str(e)
            )


class AIIntegrationAdapter:
    """Adapter for Claude/GPT AI oracles"""
    
    def __init__(self, model_type: str = "claude"):
        self.model_type = model_type
        self.client = None
        self._load_client()
    
    def _load_client(self):
        try:
            if self.model_type == "claude":
                import anthropic
                api_key = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY") or os.environ.get("ANTHROPIC_API_KEY")
                if api_key:
                    self.client = anthropic.Anthropic(api_key=api_key)
            elif self.model_type == "openai":
                import openai
                api_key = os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY") or os.environ.get("OPENAI_API_KEY")
                if api_key:
                    self.client = openai.OpenAI(api_key=api_key)
        except Exception as e:
            print(f"Warning: Could not load {self.model_type} client: {e}")
    
    def query(self, question: str, context: Dict = None) -> AdapterResult:
        """Query AI for intuitive guidance on relationship question"""
        if not self.client:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.5,
                interpretation=f"{self.model_type.title()} AI oracle not available",
                error="API key not configured"
            )
        
        prompt = f"""You are a TI Framework relationship oracle. Using GILE principles 
(Goodness, Intuition, Love, Environment), provide brief guidance on this question:

{question}

Respond in 1-2 sentences with your intuitive assessment and confidence level."""
        
        try:
            if self.model_type == "claude":
                response = self.client.messages.create(
                    model="claude-sonnet-4-20250514",
                    max_tokens=150,
                    messages=[{"role": "user", "content": prompt}]
                )
                answer = response.content[0].text
            else:
                response = self.client.chat.completions.create(
                    model="gpt-4o",
                    max_tokens=150,
                    messages=[{"role": "user", "content": prompt}]
                )
                answer = response.choices[0].message.content
            
            return AdapterResult(
                success=True,
                output={"response": answer, "model": self.model_type},
                confidence=0.65,
                interpretation=answer[:200]
            )
        except Exception as e:
            return AdapterResult(
                success=False,
                output=None,
                confidence=0.4,
                interpretation=f"AI oracle query failed: {str(e)[:50]}",
                error=str(e)
            )


class RealAdapterRegistry:
    """Registry of all real PSI adapters"""
    
    def __init__(self):
        self.adapters = {}
        self._initialize_adapters()
    
    def _initialize_adapters(self):
        """Initialize all available adapters"""
        print("Initializing real PSI adapters...")
        
        self.adapters["god_machine_relationships"] = GodMachineRelationshipAdapter()
        self.adapters["gile_contextual"] = ContextualGILEAdapter()
        self.adapters["true_tralse_vault"] = TrueTralseVaultAdapter()
        self.adapters["lcc_virus"] = LCCVirusAdapter()
        self.adapters["claude_oracle"] = AIIntegrationAdapter("claude")
        self.adapters["gpt5_oracle"] = AIIntegrationAdapter("openai")
        
        available = sum(1 for a in self.adapters.values() 
                       if hasattr(a, 'profiler') and a.profiler or
                          hasattr(a, 'calculator') and a.calculator or
                          hasattr(a, 'vault') and a.vault or
                          hasattr(a, 'lcc') and a.lcc or
                          hasattr(a, 'client') and a.client)
        
        print(f"Initialized {len(self.adapters)} adapters ({available} with live backends)")
    
    def query(self, source_id: str, question: str, context: Dict = None) -> EvidenceEvent:
        """Query a specific adapter and return EvidenceEvent"""
        adapter = self.adapters.get(source_id)
        
        if not adapter:
            return EvidenceEvent(
                source_id=source_id,
                modality=PSIModality.SYMBOLIC,
                timestamp=datetime.now(),
                query=question,
                raw_output=None,
                confidence=0.1,
                interpretation=f"No adapter available for {source_id}",
                gile_alignment=0.0
            )
        
        result = adapter.query(question, context)
        
        modality_map = {
            "god_machine_relationships": PSIModality.GOD_MACHINE,
            "gile_contextual": PSIModality.GILE_RESONANCE,
            "true_tralse_vault": PSIModality.GILE_RESONANCE,
            "lcc_virus": PSIModality.LCC_VIRUS,
            "claude_oracle": PSIModality.AI_ORACLE,
            "gpt5_oracle": PSIModality.AI_ORACLE,
        }
        
        return EvidenceEvent(
            source_id=source_id,
            modality=modality_map.get(source_id, PSIModality.SYMBOLIC),
            timestamp=datetime.now(),
            query=question,
            raw_output=result.output,
            confidence=result.confidence,
            interpretation=result.interpretation,
            gile_alignment=result.confidence * 0.9 if result.success else 0.3,
            provenance={"success": result.success, "error": result.error}
        )
    
    def query_all(self, question: str, context: Dict = None) -> List[EvidenceEvent]:
        """Query all available adapters"""
        events = []
        for source_id in self.adapters:
            event = self.query(source_id, question, context)
            events.append(event)
        return events


def test_real_adapters():
    """Test all real adapters"""
    print("=" * 60)
    print("TESTING REAL PSI ADAPTERS")
    print("=" * 60)
    
    registry = RealAdapterRegistry()
    
    question = "Who will be my next close romantic partner?"
    context = {
        "your_name": "Brandon",
        "your_birthday": "03/15/1990",
        "goodness": 0.85,
        "intuition": 0.80,
        "love": 0.90,
        "environment": 0.75
    }
    
    print(f"\nQuery: {question}")
    print("-" * 60)
    
    events = registry.query_all(question, context)
    
    for event in events:
        status = "✓" if event.confidence > 0.5 else "○"
        print(f"{status} [{event.source_id}] Confidence: {event.confidence:.1%}")
        print(f"   {event.interpretation[:80]}...")
        print()
    
    return events


if __name__ == "__main__":
    test_real_adapters()
