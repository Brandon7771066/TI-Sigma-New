from typing import Dict, List, Any
import json


class SafetyAnalyzer:
    """Analyzes Mood Amplifier project for safety aspects using multiple AI models."""
    
    SAFETY_ANALYSIS_PROMPTS = {
        "animal_studies": """
You are a neuroscience research expert. Analyze the following Mood Amplifier project documentation 
for evidence of animal studies and preclinical testing.

Specifically evaluate:
1. Are there any references to animal studies (rodent, primate, or other models)?
2. What specific studies are mentioned (provide citations if available)?
3. What were the key findings from animal research?
4. Were there any safety concerns identified in animal studies?
5. What is the quality and credibility of the cited animal research?

Project Documentation:
{content}

Provide a detailed analysis in JSON format with these fields:
- studies_found: boolean
- study_details: list of study descriptions with citations
- safety_concerns: list of concerns identified
- credibility_assessment: rating from 1-10 with explanation
- recommendation: your expert opinion on the adequacy of animal research
""",
        
        "physical_mechanisms": """
You are a neurobiology and neurochemistry expert. Analyze the following Mood Amplifier project 
documentation for physical mechanisms and how they affect the brain.

Specifically evaluate:
1. What are the proposed physical mechanisms of action?
2. How does this intervention physically alter brain function?
3. What neurotransmitter systems are affected?
4. What brain regions or circuits are targeted?
5. Is the proposed mechanism scientifically plausible based on current neuroscience?
6. Are there any gaps or unsupported claims in the mechanism explanation?

Project Documentation:
{content}

Provide a detailed analysis in JSON format with these fields:
- mechanisms_described: boolean
- mechanism_details: description of proposed mechanisms
- affected_systems: list of neurotransmitter systems and brain regions
- scientific_plausibility: rating from 1-10 with explanation
- evidence_quality: assessment of supporting evidence
- gaps_and_concerns: list of unsupported claims or missing information
""",
        
        "tolerance_addiction": """
You are an addiction medicine and pharmacology expert. Analyze the following Mood Amplifier 
project documentation for risks of tolerance and addiction development.

Specifically evaluate:
1. Does the documentation address tolerance development over time?
2. What is the addiction potential based on the mechanism of action?
3. Are there withdrawal symptoms mentioned or expected?
4. What evidence is provided about long-term safety?
5. Are there strategies mentioned to prevent or manage tolerance/addiction?
6. How does this compare to known addictive interventions?

Project Documentation:
{content}

Provide a detailed analysis in JSON format with these fields:
- tolerance_addressed: boolean
- addiction_risk_level: rating from 1-10 (10 = highest risk)
- withdrawal_concerns: description of potential withdrawal effects
- prevention_strategies: list of strategies mentioned to manage these risks
- long_term_safety_data: assessment of long-term safety evidence
- comparison_to_known_substances: comparison with similar interventions
- overall_risk_assessment: your expert opinion on addiction/tolerance risk
""",
        
        "brain_damage": """
You are a neurotoxicology and brain safety expert. Analyze the following Mood Amplifier 
project documentation for risks of brain damage or other negative neurological effects.

Specifically evaluate:
1. What is the probability of causing brain damage or neuronal death?
2. Are there any neurotoxicity studies mentioned?
3. What are the potential negative side effects on cognition, memory, or other functions?
4. Are there any long-term neurological risks identified?
5. What safety measures or limits are proposed to prevent damage?
6. How reversible are the brain changes induced?

Project Documentation:
{content}

Provide a detailed analysis in JSON format with these fields:
- neurotoxicity_studies: boolean indicating if studies were mentioned
- brain_damage_probability: rating from 1-10 (10 = highest risk)
- potential_side_effects: list of identified negative effects
- long_term_risks: description of long-term neurological risks
- safety_measures: list of proposed safety protocols
- reversibility: assessment of whether changes are reversible
- overall_safety_rating: rating from 1-10 (10 = safest)
- expert_recommendation: your expert opinion on neurological safety
"""
    }
    
    def __init__(self, openai_client, anthropic_client, perplexity_client, magai_client=None):
        self.openai = openai_client
        self.anthropic = anthropic_client
        self.perplexity = perplexity_client
        self.magai = magai_client
    
    def analyze_safety_aspect(self, content: str, aspect: str, ai_model: str) -> Dict[str, Any]:
        """Analyze a specific safety aspect using a specific AI model."""
        if aspect not in self.SAFETY_ANALYSIS_PROMPTS:
            return {"error": f"Unknown safety aspect: {aspect}"}
        
        prompt = self.SAFETY_ANALYSIS_PROMPTS[aspect].format(content=content)
        system_prompt = "You are an expert scientific reviewer. Provide thorough, evidence-based analysis in valid JSON format."
        
        try:
            if ai_model == "gpt-5":
                response = self.openai.analyze(prompt, system_prompt)
            elif ai_model == "claude-opus":
                response = self.anthropic.analyze(prompt, system_prompt)
            elif ai_model == "perplexity":
                result = self.perplexity.analyze(prompt, system_prompt)
                response = result["content"]
            else:
                return {"error": f"Unknown AI model: {ai_model}"}
            
            try:
                parsed_response = self._extract_json(response)
                return {
                    "model": ai_model,
                    "aspect": aspect,
                    "analysis": parsed_response,
                    "raw_response": response
                }
            except:
                return {
                    "model": ai_model,
                    "aspect": aspect,
                    "analysis": None,
                    "raw_response": response
                }
                
        except Exception as e:
            return {
                "model": ai_model,
                "aspect": aspect,
                "error": str(e)
            }
    
    def comprehensive_safety_analysis(self, content: str) -> Dict[str, Any]:
        """Run comprehensive safety analysis across all aspects and all AI models."""
        results = {
            "animal_studies": {},
            "physical_mechanisms": {},
            "tolerance_addiction": {},
            "brain_damage": {}
        }
        
        ai_models = ["gpt-5", "claude-opus", "perplexity"]
        
        for aspect in results.keys():
            for model in ai_models:
                results[aspect][model] = self.analyze_safety_aspect(content, aspect, model)
        
        if self.magai and hasattr(self.magai, 'email') and self.magai.email:
            try:
                magai_results = self._analyze_with_magai(content)
                results["magai_analysis"] = magai_results
            except:
                results["magai_analysis"] = {"error": "MagAI analysis failed or not configured"}
        
        consensus_results = self._identify_consensus(results)
        disagreement_list = self._identify_disagreements(results)
        safety_rating = self._calculate_overall_safety(results)
        
        results["consensus"] = consensus_results
        results["disagreements"] = disagreement_list
        results["overall_safety_rating"] = safety_rating
        
        return results
    
    def _analyze_with_magai(self, content: str) -> Dict[str, Any]:
        """Analyze using MagAI platform."""
        if not self.magai:
            return {"error": "MagAI client not initialized"}
            
        prompt = f"""
Analyze this Mood Amplifier project for safety concerns. Focus on:
1. Animal studies evidence
2. Physical brain mechanisms
3. Tolerance and addiction risks
4. Brain damage probability

Project Documentation:
{content}

Provide a comprehensive safety analysis.
"""
        return self.magai.analyze_with_multiple_models(prompt)
    
    def _extract_json(self, text: str) -> Dict:
        """Extract JSON from AI response."""
        text = text.strip()
        
        if text.startswith("```json"):
            text = text[7:]
        if text.startswith("```"):
            text = text[3:]
        if text.endswith("```"):
            text = text[:-3]
        
        text = text.strip()
        
        start = text.find("{")
        end = text.rfind("}")
        
        if start != -1 and end != -1:
            text = text[start:end+1]
        
        return json.loads(text)
    
    def _identify_consensus(self, results: Dict) -> Dict[str, Any]:
        """Identify areas of consensus across AI models."""
        consensus = {}
        
        for aspect, model_results in results.items():
            if aspect in ["magai_analysis", "consensus", "disagreements", "overall_safety_rating"]:
                continue
            
            aspect_consensus = {
                "agreements": [],
                "key_findings": [],
                "confidence": "unknown",
                "model_count": 0
            }
            
            model_analyses = {}
            for model, result in model_results.items():
                if "analysis" in result and result["analysis"] and not "error" in result:
                    model_analyses[model] = result["analysis"]
                    aspect_consensus["model_count"] += 1
            
            if aspect == "animal_studies":
                studies_found = []
                safety_concerns = []
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict):
                        if analysis.get("studies_found"):
                            studies_found.append(model)
                        if analysis.get("safety_concerns"):
                            safety_concerns.extend(analysis.get("safety_concerns", []))
                
                if len(studies_found) >= 2:
                    aspect_consensus["agreements"].append(f"{len(studies_found)} models confirmed animal studies exist")
                    aspect_consensus["confidence"] = "high"
                elif len(studies_found) == 1:
                    aspect_consensus["agreements"].append("Only 1 model found animal studies - requires verification")
                    aspect_consensus["confidence"] = "low"
                else:
                    aspect_consensus["agreements"].append("No animal studies found by any model")
                    aspect_consensus["confidence"] = "high"
                
                if safety_concerns:
                    unique_concerns = list(set(safety_concerns))
                    aspect_consensus["key_findings"] = unique_concerns[:5]
            
            elif aspect == "physical_mechanisms":
                mechanisms_found = []
                plausibility_scores = []
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict):
                        if analysis.get("mechanisms_described"):
                            mechanisms_found.append(model)
                        if analysis.get("scientific_plausibility"):
                            try:
                                score = int(analysis.get("scientific_plausibility", 0))
                                plausibility_scores.append(score)
                            except:
                                pass
                
                if plausibility_scores:
                    avg_plausibility = sum(plausibility_scores) / len(plausibility_scores)
                    aspect_consensus["agreements"].append(f"Average plausibility rating: {avg_plausibility:.1f}/10")
                    aspect_consensus["key_findings"].append(f"Scientific plausibility: {avg_plausibility:.1f}/10")
                    
                    if avg_plausibility >= 7:
                        aspect_consensus["confidence"] = "high"
                    elif avg_plausibility >= 4:
                        aspect_consensus["confidence"] = "moderate"
                    else:
                        aspect_consensus["confidence"] = "low"
            
            elif aspect == "tolerance_addiction":
                addiction_risks = []
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict):
                        if analysis.get("addiction_risk_level"):
                            try:
                                risk = int(analysis.get("addiction_risk_level", 0))
                                addiction_risks.append(risk)
                            except:
                                pass
                
                if addiction_risks:
                    avg_risk = sum(addiction_risks) / len(addiction_risks)
                    aspect_consensus["agreements"].append(f"Average addiction risk: {avg_risk:.1f}/10")
                    aspect_consensus["key_findings"].append(f"Addiction risk level: {avg_risk:.1f}/10")
                    
                    if avg_risk >= 7:
                        aspect_consensus["confidence"] = "high"
                        aspect_consensus["key_findings"].append("⚠️ HIGH ADDICTION RISK - Use extreme caution")
                    elif avg_risk >= 4:
                        aspect_consensus["confidence"] = "moderate"
                        aspect_consensus["key_findings"].append("Moderate addiction risk - Monitor usage")
                    else:
                        aspect_consensus["confidence"] = "high"
                        aspect_consensus["key_findings"].append("Low addiction risk based on AI analysis")
            
            elif aspect == "brain_damage":
                damage_probabilities = []
                safety_ratings = []
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict):
                        if analysis.get("brain_damage_probability"):
                            try:
                                prob = int(analysis.get("brain_damage_probability", 0))
                                damage_probabilities.append(prob)
                            except:
                                pass
                        if analysis.get("overall_safety_rating"):
                            try:
                                rating = int(analysis.get("overall_safety_rating", 0))
                                safety_ratings.append(rating)
                            except:
                                pass
                
                if damage_probabilities:
                    avg_damage_prob = sum(damage_probabilities) / len(damage_probabilities)
                    aspect_consensus["agreements"].append(f"Average brain damage risk: {avg_damage_prob:.1f}/10")
                    aspect_consensus["key_findings"].append(f"Brain damage probability: {avg_damage_prob:.1f}/10")
                    
                    if avg_damage_prob >= 7:
                        aspect_consensus["confidence"] = "high"
                        aspect_consensus["key_findings"].append("⚠️ HIGH NEUROTOXICITY RISK - Do not proceed")
                    elif avg_damage_prob >= 4:
                        aspect_consensus["confidence"] = "moderate"
                        aspect_consensus["key_findings"].append("Moderate neurotoxicity concern - Requires expert review")
                    else:
                        aspect_consensus["confidence"] = "high"
                
                if safety_ratings:
                    avg_safety = sum(safety_ratings) / len(safety_ratings)
                    aspect_consensus["agreements"].append(f"Average overall safety: {avg_safety:.1f}/10")
            
            if aspect_consensus["model_count"] == 0:
                aspect_consensus["confidence"] = "none"
                aspect_consensus["agreements"].append("No successful analyses from any model")
            
            consensus[aspect] = aspect_consensus
        
        return consensus
    
    def _identify_disagreements(self, results: Dict) -> List[str]:
        """Identify areas where AI models disagree."""
        disagreements = []
        
        for aspect, model_results in results.items():
            if aspect in ["magai_analysis", "consensus", "disagreements", "overall_safety_rating"]:
                continue
            
            model_analyses = {}
            for model, result in model_results.items():
                if "analysis" in result and result["analysis"] and not "error" in result:
                    model_analyses[model] = result["analysis"]
            
            if aspect == "animal_studies":
                studies_found_by = []
                not_found_by = []
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict):
                        if analysis.get("studies_found"):
                            studies_found_by.append(model)
                        else:
                            not_found_by.append(model)
                
                if studies_found_by and not_found_by:
                    disagreements.append(
                        f"Animal Studies: {', '.join(studies_found_by)} found evidence, "
                        f"but {', '.join(not_found_by)} did not"
                    )
            
            elif aspect == "physical_mechanisms":
                plausibility_scores = {}
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict) and analysis.get("scientific_plausibility"):
                        try:
                            plausibility_scores[model] = int(analysis.get("scientific_plausibility", 0))
                        except:
                            pass
                
                if len(plausibility_scores) >= 2:
                    scores = list(plausibility_scores.values())
                    if max(scores) - min(scores) >= 4:
                        high_models = [m for m, s in plausibility_scores.items() if s >= 7]
                        low_models = [m for m, s in plausibility_scores.items() if s < 4]
                        if high_models and low_models:
                            disagreements.append(
                                f"Physical Mechanisms Plausibility: Major disagreement - "
                                f"{', '.join(high_models)} rated high, {', '.join(low_models)} rated low"
                            )
            
            elif aspect == "tolerance_addiction":
                risk_scores = {}
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict) and analysis.get("addiction_risk_level"):
                        try:
                            risk_scores[model] = int(analysis.get("addiction_risk_level", 0))
                        except:
                            pass
                
                if len(risk_scores) >= 2:
                    scores = list(risk_scores.values())
                    if max(scores) - min(scores) >= 4:
                        high_models = [m for m, s in risk_scores.items() if s >= 7]
                        low_models = [m for m, s in risk_scores.items() if s < 4]
                        if high_models and low_models:
                            disagreements.append(
                                f"Addiction Risk: Significant disagreement - "
                                f"{', '.join(high_models)} see high risk, {', '.join(low_models)} see low risk"
                            )
            
            elif aspect == "brain_damage":
                damage_scores = {}
                for model, analysis in model_analyses.items():
                    if isinstance(analysis, dict) and analysis.get("brain_damage_probability"):
                        try:
                            damage_scores[model] = int(analysis.get("brain_damage_probability", 0))
                        except:
                            pass
                
                if len(damage_scores) >= 2:
                    scores = list(damage_scores.values())
                    if max(scores) - min(scores) >= 4:
                        high_models = [m for m, s in damage_scores.items() if s >= 7]
                        low_models = [m for m, s in damage_scores.items() if s < 4]
                        if high_models and low_models:
                            disagreements.append(
                                f"Brain Damage Risk: Critical disagreement - "
                                f"{', '.join(high_models)} see high danger, {', '.join(low_models)} see low danger"
                            )
        
        return disagreements
    
    def _calculate_overall_safety(self, results: Dict) -> Dict[str, Any]:
        """Calculate overall safety rating based on all analyses."""
        return {
            "rating": "Requires expert review",
            "recommendation": "Consult with medical professionals before use",
            "critical_concerns": [
                "Verify all animal study claims",
                "Confirm mechanism of action with neuroscience literature",
                "Assess addiction potential carefully",
                "Evaluate long-term neurological safety"
            ]
        }
