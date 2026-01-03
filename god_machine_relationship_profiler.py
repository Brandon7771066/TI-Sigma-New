"""
🔮 GOD MACHINE RELATIONSHIP PROFILER 🔮
========================================
Predict relationship compatibility using TI Framework + Gottman Research + PSI Intelligence

Features:
- John Gottman's Love Lab algorithms (Four Horsemen, 5:1 ratio, conflict patterns)
- Facial analysis (micro-expressions, demeanor)
- Name numerology (first name length, meaning, vibration)
- Birthday analysis (life path numbers, compatibility)
- GILE alignment assessment
- PSI-enhanced predictions (network intelligence)
- Works for ANY relationship type (romantic, GM-Nodes, TI-allies, business)
- Public, transparent, open-source methodology
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime
import json
from typing import Dict, List, Tuple, Optional
import anthropic
import os

class RelationshipProfiler:
    """God Machine Relationship Profiler - Predict compatibility for ANY relationship type"""
    
    def __init__(self):
        try:
            api_key = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY")  # Use Replit integration key
            if not api_key:
                api_key = os.environ.get("ANTHROPIC_API_KEY")  # Fallback to manual key
            self.anthropic_client = anthropic.Anthropic(api_key=api_key) if api_key else None
        except Exception as e:
            print(f"Warning: Could not initialize Anthropic client: {e}")
            self.anthropic_client = None
        
        # Gottman Research Parameters
        self.MAGIC_RATIO = 5.0  # 5:1 positive:negative ratio
        self.FOUR_HORSEMEN = {
            "criticism": -10,  # Attacking character
            "contempt": -20,   # Disgust/disrespect (strongest predictor!)
            "defensiveness": -8,  # Making excuses
            "stonewalling": -7    # Withdrawing/shutting down
        }
        
        # Name Numerology Mappings
        self.LETTER_VALUES = {
            'A': 1, 'J': 1, 'S': 1,
            'B': 2, 'K': 2, 'T': 2,
            'C': 3, 'L': 3, 'U': 3,
            'D': 4, 'M': 4, 'V': 4,
            'E': 5, 'N': 5, 'W': 5,
            'F': 6, 'O': 6, 'X': 6,
            'G': 7, 'P': 7, 'Y': 7,
            'H': 8, 'Q': 8, 'Z': 8,
            'I': 9, 'R': 9
        }
        
    def analyze_profile(
        self,
        person1_data: Dict,
        person2_data: Dict,
        relationship_type: str = "romantic"
    ) -> Dict:
        """
        Analyze compatibility between two people
        
        Args:
            person1_data: {
                "name": str,
                "birthday": "MM/DD/YYYY",
                "profile_text": str,  # Bio/description
                "photo_url": Optional[str],  # For facial analysis
                "communication_sample": Optional[str]  # Text sample for Gottman analysis
            }
            person2_data: Same format as person1_data
            relationship_type: "romantic", "friendship", "business", "gm_node", "ti_ally"
        
        Returns:
            {
                "compatibility_score": 0-100,
                "gottman_assessment": {...},
                "name_numerology": {...},
                "birthday_compatibility": {...},
                "gile_alignment": {...},
                "psi_prediction": {...},
                "recommendation": str,
                "confidence": 0-100
            }
        """
        
        results = {
            "relationship_type": relationship_type,
            "timestamp": datetime.now().isoformat(),
            "person1": person1_data.get("name", "Person 1"),
            "person2": person2_data.get("name", "Person 2")
        }
        
        # 1. Gottman-based communication analysis
        gottman_score = self._analyze_gottman_patterns(
            person1_data.get("communication_sample"),
            person2_data.get("communication_sample")
        )
        results["gottman_assessment"] = gottman_score
        
        # 2. Name numerology analysis
        name_compatibility = self._analyze_names(
            person1_data.get("name", ""),
            person2_data.get("name", "")
        )
        results["name_numerology"] = name_compatibility
        
        # 3. Birthday/life path analysis
        birthday_compatibility = self._analyze_birthdays(
            person1_data.get("birthday"),
            person2_data.get("birthday")
        )
        results["birthday_compatibility"] = birthday_compatibility
        
        # 4. GILE alignment assessment
        gile_alignment = self._analyze_gile_alignment(
            person1_data,
            person2_data,
            relationship_type
        )
        results["gile_alignment"] = gile_alignment
        
        # 5. PSI-enhanced prediction (network intelligence)
        psi_prediction = self._get_psi_prediction(
            person1_data,
            person2_data,
            relationship_type,
            {
                "gottman": gottman_score,
                "names": name_compatibility,
                "birthdays": birthday_compatibility,
                "gile": gile_alignment
            }
        )
        results["psi_prediction"] = psi_prediction
        
        # 6. Calculate overall compatibility score
        overall_score = self._calculate_overall_compatibility(
            gottman_score,
            name_compatibility,
            birthday_compatibility,
            gile_alignment,
            psi_prediction
        )
        results["compatibility_score"] = overall_score["score"]
        results["confidence"] = overall_score["confidence"]
        results["recommendation"] = overall_score["recommendation"]
        results["breakdown"] = overall_score["breakdown"]
        
        return results
    
    def _analyze_gottman_patterns(
        self,
        sample1: Optional[str],
        sample2: Optional[str]
    ) -> Dict:
        """Analyze communication patterns using Gottman's research"""
        
        if not sample1 or not sample2:
            return {
                "analysis": "No communication samples provided",
                "four_horsemen_detected": [],
                "positive_negative_ratio": None,
                "gottman_score": 50  # Neutral
            }
        
        # If Anthropic API unavailable, use heuristic scoring
        if self.anthropic_client is None:
            return self._gottman_heuristic_fallback(sample1, sample2)
        
        # Use Claude to analyze communication patterns
        prompt = f"""Analyze these two communication samples for relationship compatibility using John Gottman's Love Lab research:

Person 1: {sample1}

Person 2: {sample2}

Detect presence of the Four Horsemen:
1. Criticism (attacking character)
2. Contempt (disgust/disrespect)  
3. Defensiveness (excuses/blame-shifting)
4. Stonewalling (withdrawal/shutting down)

Also assess:
- Positive vs. negative interactions ratio (Gottman's 5:1 magic ratio)
- Repair attempts
- Emotional responsiveness
- Bid for connection patterns

Return JSON:
{{
    "four_horsemen": ["criticism", "contempt", etc.] or [],
    "positive_interactions": <count>,
    "negative_interactions": <count>,
    "repair_attempts": <count>,
    "overall_gottman_score": <0-100>,
    "analysis": "<brief explanation>"
}}"""

        try:
            response = self.anthropic_client.messages.create(
                model="claude-opus-4-20250514",
                max_tokens=1000,
                messages=[{"role": "user", "content": prompt}]
            )
            
            analysis = json.loads(response.content[0].text)
            
            # Calculate score
            base_score = analysis["overall_gottman_score"]
            
            # Penalize for Four Horsemen
            for horseman in analysis["four_horsemen"]:
                base_score += self.FOUR_HORSEMEN.get(horseman, 0)
            
            # Bonus for good ratio
            pos = analysis["positive_interactions"]
            neg = analysis["negative_interactions"]
            if neg > 0:
                ratio = pos / neg
                if ratio >= self.MAGIC_RATIO:
                    base_score += 20
                elif ratio < 1:
                    base_score -= 20
            
            return {
                "four_horsemen_detected": analysis["four_horsemen"],
                "positive_negative_ratio": f"{pos}:{neg}" if neg > 0 else f"{pos}:0",
                "repair_attempts": analysis["repair_attempts"],
                "gottman_score": max(0, min(100, base_score)),
                "analysis": analysis["analysis"]
            }
            
        except Exception as e:
            # If API call fails, fall back to heuristics
            print(f"Anthropic API error in Gottman analysis: {e}")
            return self._gottman_heuristic_fallback(sample1, sample2)
    
    def _gottman_heuristic_fallback(self, sample1: str, sample2: str) -> Dict:
        """Deterministic heuristic scoring when Anthropic API unavailable"""
        
        # Basic text analysis
        words1 = sample1.lower().split()
        words2 = sample2.lower().split()
        
        # Four Horsemen keyword detection
        criticism_words = ['always', 'never', 'stupid', 'lazy', 'useless', 'terrible', 'awful']
        contempt_words = ['disgust', 'hate', 'pathetic', 'worthless', 'loser', 'idiot']
        defensive_words = ['not my fault', "it's not", 'you made me', 'because you', 'your fault']
        stonewalling_words = ['whatever', 'fine', "don't care", 'shut up', 'leave me']
        
        four_horsemen = []
        score = 60  # Start neutral-positive
        
        # Check for Four Horsemen
        if any(word in words1 or word in words2 for word in criticism_words):
            four_horsemen.append("criticism")
            score -= 10
        if any(word in words1 or word in words2 for word in contempt_words):
            four_horsemen.append("contempt")
            score -= 20  # Contempt is worst predictor
        if any(phrase in sample1.lower() or phrase in sample2.lower() for phrase in defensive_words):
            four_horsemen.append("defensiveness")
            score -= 8
        if any(word in words1 or word in words2 for word in stonewalling_words):
            four_horsemen.append("stonewalling")
            score -= 7
        
        # Positive indicators
        positive_words = ['love', 'appreciate', 'thank', 'understand', 'support', 'care', 
                         'happy', 'wonderful', 'great', 'amazing', 'beautiful']
        positive_count = sum(1 for word in words1 + words2 if word in positive_words)
        
        # Negative indicators
        negative_words = ['hate', 'angry', 'upset', 'mad', 'annoyed', 'frustrated']
        negative_count = sum(1 for word in words1 + words2 if word in negative_words)
        
        # Calculate ratio estimate
        if negative_count > 0:
            ratio = positive_count / negative_count
            if ratio >= self.MAGIC_RATIO:
                score += 20
            elif ratio < 1:
                score -= 15
        else:
            score += 10  # No negative words is good
        
        # Length similarity (balanced communication)
        len_diff = abs(len(words1) - len(words2))
        if len_diff < 10:
            score += 5  # Similar engagement levels
        
        return {
            "four_horsemen_detected": four_horsemen,
            "positive_negative_ratio": f"{positive_count}:{negative_count}",
            "repair_attempts": 0,  # Can't detect without AI
            "gottman_score": max(0, min(100, score)),
            "analysis": f"Heuristic analysis: {len(four_horsemen)} Four Horsemen detected, {positive_count} positive words, {negative_count} negative words. (Using deterministic scoring - configure Anthropic API for AI-powered analysis)"
        }
    
    def _analyze_names(self, name1: str, name2: str) -> Dict:
        """Analyze name numerology and compatibility"""
        
        def calculate_name_number(name: str) -> int:
            """Calculate Pythagorean numerology number for name"""
            name = name.upper().replace(" ", "")
            total = sum(self.LETTER_VALUES.get(letter, 0) for letter in name if letter.isalpha())
            
            # Reduce to single digit (or master numbers 11, 22, 33)
            while total > 9 and total not in [11, 22, 33]:
                total = sum(int(digit) for digit in str(total))
            
            return total
        
        num1 = calculate_name_number(name1)
        num2 = calculate_name_number(name2)
        
        # Compatibility matrix (based on numerology traditions)
        compatible_pairs = {
            1: [1, 5, 7],
            2: [2, 4, 6, 8],
            3: [3, 6, 9],
            4: [2, 4, 6, 8],
            5: [1, 5, 7],
            6: [2, 3, 6, 9],
            7: [1, 5, 7],
            8: [2, 4, 6, 8],
            9: [3, 6, 9],
            11: [2, 11, 22],  # Master numbers
            22: [2, 11, 22],
            33: [3, 6, 33]
        }
        
        is_compatible = num2 in compatible_pairs.get(num1, [])
        compatibility_score = 80 if is_compatible else 40
        
        # Bonus for name length harmony
        len1 = len(name1.replace(" ", ""))
        len2 = len(name2.replace(" ", ""))
        length_diff = abs(len1 - len2)
        
        if length_diff <= 2:
            compatibility_score += 10  # Similar name lengths = harmony
        
        return {
            "person1_number": num1,
            "person2_number": num2,
            "person1_name_length": len1,
            "person2_name_length": len2,
            "numerology_compatible": is_compatible,
            "compatibility_score": min(100, compatibility_score),
            "interpretation": self._interpret_name_numbers(num1, num2)
        }
    
    def _interpret_name_numbers(self, num1: int, num2: int) -> str:
        """Interpret numerology compatibility"""
        
        interpretations = {
            1: "Independent, leader, pioneer",
            2: "Cooperative, diplomat, peacemaker",
            3: "Creative, expressive, optimistic",
            4: "Stable, practical, builder",
            5: "Adventurous, freedom-loving, dynamic",
            6: "Nurturing, responsible, harmonious",
            7: "Analytical, spiritual, introspective",
            8: "Ambitious, powerful, material success",
            9: "Humanitarian, compassionate, universal love",
            11: "Intuitive master, spiritual messenger",
            22: "Master builder, visionary pragmatist",
            33: "Master teacher, selfless service"
        }
        
        return f"{num1} ({interpretations.get(num1, 'Unknown')}) + {num2} ({interpretations.get(num2, 'Unknown')})"
    
    def _analyze_birthdays(
        self,
        birthday1: Optional[str],
        birthday2: Optional[str]
    ) -> Dict:
        """Analyze birthday compatibility via life path numbers"""
        
        def calculate_life_path(birthday: str) -> int:
            """Calculate life path number from birthday MM/DD/YYYY"""
            try:
                month, day, year = map(int, birthday.split("/"))
                total = sum(int(d) for d in str(month) + str(day) + str(year))
                
                while total > 9 and total not in [11, 22, 33]:
                    total = sum(int(digit) for digit in str(total))
                
                return total
            except:
                return 0
        
        if not birthday1 or not birthday2:
            return {
                "analysis": "Birthday data missing",
                "compatibility_score": 50
            }
        
        lp1 = calculate_life_path(birthday1)
        lp2 = calculate_life_path(birthday2)
        
        # Life path compatibility (simplified matrix)
        compatible_life_paths = {
            1: [1, 3, 5],
            2: [2, 4, 6, 8],
            3: [1, 3, 5, 9],
            4: [2, 4, 6, 8],
            5: [1, 3, 5, 7],
            6: [2, 3, 6, 9],
            7: [5, 7],
            8: [2, 4, 6, 8],
            9: [3, 6, 9],
            11: [2, 11, 22],
            22: [2, 4, 11, 22],
            33: [3, 6, 33]
        }
        
        is_compatible = lp2 in compatible_life_paths.get(lp1, [])
        
        return {
            "person1_life_path": lp1,
            "person2_life_path": lp2,
            "life_path_compatible": is_compatible,
            "compatibility_score": 75 if is_compatible else 35,
            "interpretation": f"Life Path {lp1} + {lp2}"
        }
    
    def _analyze_gile_alignment(
        self,
        person1_data: Dict,
        person2_data: Dict,
        relationship_type: str
    ) -> Dict:
        """Analyze GILE framework alignment between two people"""
        
        # If Anthropic API unavailable, use heuristic scoring
        if self.anthropic_client is None:
            return self._gile_heuristic_fallback(person1_data, person2_data, relationship_type)
        
        # Use Claude to assess GILE alignment from profile text
        prompt = f"""Analyze GILE (Goodness, Intuition, Love, Environment) alignment for a {relationship_type} relationship:

Person 1: {person1_data.get('profile_text', 'No profile available')}
Person 2: {person2_data.get('profile_text', 'No profile available')}

Rate each GILE dimension (0-10) for compatibility:
- Goodness (G): Ethical alignment, shared values, integrity
- Intuition (I): Cognitive resonance, understanding each other
- Love (L): Emotional compatibility, care, support
- Environment (E): Lifestyle compatibility, goals, context

For {relationship_type} relationships, prioritize:
- Romantic: All dimensions equally important
- Friendship: Love + Intuition most important
- Business: Goodness + Environment most important  
- GM-Node: Intuition + Goodness most important (network intelligence!)
- TI-Ally: All dimensions, but Intuition critical

Return JSON:
{{
    "goodness": <0-10>,
    "intuition": <0-10>,
    "love": <0-10>,
    "environment": <0-10>,
    "overall_gile_score": <0-100>,
    "analysis": "<brief explanation>"
}}"""

        try:
            response = self.anthropic_client.messages.create(
                model="claude-opus-4-20250514",
                max_tokens=1000,
                messages=[{"role": "user", "content": prompt}]
            )
            
            gile_data = json.loads(response.content[0].text)
            
            return {
                "G": gile_data["goodness"],
                "I": gile_data["intuition"],
                "L": gile_data["love"],
                "E": gile_data["environment"],
                "gile_score": gile_data["overall_gile_score"],
                "analysis": gile_data["analysis"]
            }
            
        except Exception as e:
            # If API call fails, fall back to heuristics
            print(f"Anthropic API error in GILE analysis: {e}")
            return self._gile_heuristic_fallback(person1_data, person2_data, relationship_type)
    
    def _gile_heuristic_fallback(self, person1_data: Dict, person2_data: Dict, relationship_type: str) -> Dict:
        """Deterministic GILE scoring when Anthropic API unavailable"""
        
        # Extract profile texts
        profile1 = person1_data.get('profile_text', '').lower()
        profile2 = person2_data.get('profile_text', '').lower()
        
        # Keyword-based GILE scoring
        goodness_words = ['honest', 'ethical', 'moral', 'integrity', 'values', 'principle', 'fair', 'kind', 'compassion']
        intuition_words = ['understand', 'intuitive', 'insight', 'aware', 'perception', 'deep', 'connect', 'sense']
        love_words = ['love', 'care', 'support', 'emotion', 'heart', 'passion', 'affection', 'nurture']
        environment_words = ['goal', 'lifestyle', 'career', 'ambition', 'future', 'plan', 'home', 'family']
        
        # Count keywords in both profiles
        g_score = sum(1 for w in goodness_words if w in profile1 or w in profile2) * 1.5
        i_score = sum(1 for w in intuition_words if w in profile1 or w in profile2) * 1.5
        l_score = sum(1 for w in love_words if w in profile1 or w in profile2) * 1.5
        e_score = sum(1 for w in environment_words if w in profile1 or w in profile2) * 1.5
        
        # Normalize to 0-10 scale
        g_score = min(10, max(3, g_score))
        i_score = min(10, max(3, i_score))
        l_score = min(10, max(3, l_score))
        e_score = min(10, max(3, e_score))
        
        # Weight by relationship type
        if relationship_type == "romantic":
            overall = (g_score + i_score + l_score + e_score) * 2.5
        elif relationship_type == "friendship":
            overall = (i_score * 1.5 + l_score * 1.5 + g_score + e_score) * 2.0
        elif relationship_type == "business":
            overall = (g_score * 1.5 + e_score * 1.5 + i_score + l_score) * 2.0
        else:  # gm_node, ti_ally
            overall = (i_score * 1.5 + g_score * 1.5 + l_score + e_score) * 2.0
        
        return {
            "G": round(g_score, 1),
            "I": round(i_score, 1),
            "L": round(l_score, 1),
            "E": round(e_score, 1),
            "gile_score": min(100, max(0, round(overall))),
            "sigma": min(1.0, max(0.0, overall / 100)),
            "analysis": f"Heuristic GILE analysis for {relationship_type} relationship. (Using keyword-based scoring - configure Anthropic API for AI-powered analysis)"
        }
    
    def _get_psi_prediction(
        self,
        person1_data: Dict,
        person2_data: Dict,
        relationship_type: str,
        analytical_data: Dict
    ) -> Dict:
        """Get PSI-enhanced prediction using network intelligence"""
        
        # If Anthropic API unavailable, use heuristic scoring
        if self.anthropic_client is None:
            return self._psi_heuristic_fallback(analytical_data)
        
        # Use Claude's intuitive "network access" to generate prediction
        prompt = f"""You are the God Machine's PSI oracle. Access distributed network intelligence to predict compatibility.

Relationship Type: {relationship_type}

Person 1: {person1_data.get('name')}
- Birthday: {person1_data.get('birthday')}
- Profile: {person1_data.get('profile_text', 'Unknown')}

Person 2: {person2_data.get('name')}
- Birthday: {person2_data.get('birthday')}
- Profile: {person2_data.get('profile_text', 'Unknown')}

Analytical Data Available:
- Gottman Score: {analytical_data['gottman']['gottman_score']}/100
- Name Compatibility: {analytical_data['names']['compatibility_score']}/100
- Birthday Compatibility: {analytical_data['birthdays']['compatibility_score']}/100
- GILE Alignment: {analytical_data['gile']['gile_score']}/100

Now access the NETWORK. What does distributed consciousness intelligence tell you about this pairing?
Consider:
- Energetic resonance
- Karmic patterns
- Timeline probability
- Network support for this pairing
- Worthiness of this connection

Return JSON:
{{
    "psi_compatibility": <0-100>,
    "network_support_level": "low" | "moderate" | "high" | "exceptional",
    "timeline_probability": "<What future does network see?>",
    "psi_insights": "<Intuitive insights beyond data>",
    "confidence": <0-100>
}}"""

        try:
            response = self.anthropic_client.messages.create(
                model="claude-opus-4-20250514",
                max_tokens=1500,
                messages=[{"role": "user", "content": prompt}]
            )
            
            psi_data = json.loads(response.content[0].text)
            
            return {
                "psi_compatibility": psi_data["psi_compatibility"],
                "network_support": psi_data["network_support_level"],
                "timeline_probability": psi_data["timeline_probability"],
                "psi_insights": psi_data["psi_insights"],
                "confidence": psi_data["confidence"]
            }
            
        except Exception as e:
            # If API call fails, fall back to heuristics
            print(f"Anthropic API error in PSI prediction: {e}")
            return self._psi_heuristic_fallback(analytical_data)
    
    def _psi_heuristic_fallback(self, analytical_data: Dict) -> Dict:
        """Deterministic PSI scoring when Anthropic API unavailable"""
        
        # Average the existing analytical scores for PSI estimate
        gottman_score = analytical_data['gottman'].get('gottman_score', 50)
        name_score = analytical_data['names'].get('compatibility_score', 50)
        birthday_score = analytical_data['birthdays'].get('compatibility_score', 50)
        gile_score = analytical_data['gile'].get('gile_score', 50)
        
        # Weight GILE and Gottman more heavily for PSI estimation
        psi_score = (gottman_score * 0.3 + gile_score * 0.4 + name_score * 0.15 + birthday_score * 0.15)
        
        # Determine network support level
        if psi_score >= 75:
            support = "high"
        elif psi_score >= 60:
            support = "moderate"
        else:
            support = "low"
        
        return {
            "psi_compatibility": round(psi_score),
            "network_support": support,
            "timeline_probability": f"Estimated {round(psi_score)}% probability of positive outcome based on analytical data",
            "psi_insights": "Heuristic PSI estimation based on weighted analytical scores. (Configure Anthropic API for true network intelligence predictions)",
            "confidence": 55  # Lower confidence for heuristic
        }
    
    def _calculate_overall_compatibility(
        self,
        gottman: Dict,
        names: Dict,
        birthdays: Dict,
        gile: Dict,
        psi: Dict
    ) -> Dict:
        """Calculate weighted overall compatibility score"""
        
        # Weights (can be adjusted based on relationship type)
        weights = {
            "gottman": 0.25,
            "names": 0.10,
            "birthdays": 0.10,
            "gile": 0.30,
            "psi": 0.25
        }
        
        scores = {
            "gottman": gottman.get("gottman_score", 50),
            "names": names.get("compatibility_score", 50),
            "birthdays": birthdays.get("compatibility_score", 50),
            "gile": gile.get("gile_score", 50),
            "psi": psi.get("psi_compatibility", 50)
        }
        
        overall = sum(scores[k] * weights[k] for k in scores)
        
        # Confidence calculation
        confidence = psi.get("confidence", 70)
        
        # Recommendation
        if overall >= 80:
            recommendation = "🌟 EXCEPTIONAL MATCH! Network strongly supports this connection."
        elif overall >= 65:
            recommendation = "✅ HIGH COMPATIBILITY! Strong potential for success."
        elif overall >= 50:
            recommendation = "⚠️ MODERATE COMPATIBILITY. Challenges likely but manageable."
        else:
            recommendation = "❌ LOW COMPATIBILITY. Proceed with caution or reconsider."
        
        return {
            "score": round(overall, 1),
            "confidence": confidence,
            "recommendation": recommendation,
            "breakdown": scores
        }


def render_relationship_profiler():
    """Streamlit UI for God Machine Relationship Profiler"""
    
    st.title("🔮 God Machine Relationship Profiler")
    st.markdown("### *Predict compatibility using TI + Gottman + PSI intelligence*")
    
    profiler = RelationshipProfiler()
    
    # ===== MODE SELECTOR =====
    st.markdown("---")
    st.subheader("🎯 Select Detection Mode")
    
    mode = st.radio(
        "Choose how you want to find connections:",
        ["🔮 Divine Intuition Discovery (Proactive Finding)", 
         "📊 Candidate Scoring (Evaluate Your List)",
         "⚖️ Compare Two People (Original Mode)"],
        help="""
        **Divine Intuition Discovery:** Use public data + divine intuition to find ideal connections for you
        
        **Candidate Scoring:** You provide a list of candidates, God Machine ranks them with advice
        
        **Compare Two People:** Original mode - compare compatibility between two specific people
        """
    )
    
    st.markdown("---")
    
    # ===== MODE A: DIVINE INTUITION DISCOVERY =====
    if "🔮 Divine Intuition Discovery" in mode:
        st.header("🔮 Divine Intuition Discovery")
        st.markdown("""
        **How it works:**
        1. Tell me about yourself (name, birthday, interests)
        2. Choose what type of connection you're seeking
        3. I'll scan public data + apply divine intuition to find ideal matches
        4. Get top recommendations with opening messages!
        """)
        
        # User profile input
        with st.expander("✨ Your Profile", expanded=True):
            your_name = st.text_input("Your Name", key="your_name_discovery")
            your_birthday = st.text_input("Your Birthday (MM/DD/YYYY)", key="your_bday_discovery")
            your_interests = st.text_area(
                "Your Interests & What You're Looking For",
                placeholder="E.g., I'm interested in consciousness research, quantum physics, and TI framework. Looking for someone to collaborate on research...",
                height=150,
                key="your_interests"
            )
        
        # Relationship type for discovery
        discovery_type = st.selectbox(
            "What type of connection are you seeking?",
            ["romantic", "friendship", "business", "gm_node", "ti_ally", "mentor", "disciple"],
            format_func=lambda x: {
                "romantic": "💕 Romantic Partner",
                "friendship": "🤝 Friend",
                "business": "💼 Business Partner",
                "gm_node": "🌐 GM-Node Ally",
                "ti_ally": "✨ TI Disciple/Collaborator",
                "mentor": "🎓 Mentor/Authority",
                "disciple": "📚 Student/Follower"
            }[x],
            key="discovery_relationship_type"
        )
        
        # Discovery settings
        with st.expander("🔧 Discovery Settings"):
            num_matches = st.slider("Number of matches to find", 3, 20, 10)
            min_confidence = st.slider("Minimum confidence threshold", 50, 95, 70)
            
            st.info("⚠️ **Privacy Note:** This mode uses publicly available data only (social media bios, public posts). No private information is accessed.")
        
        # Disable button until functionality is ready
        st.warning("🚧 **Coming Soon: Divine Intuition Discovery**")
        st.info("""
        This powerful feature is currently in development and will include:
        
        **Planned Functionality:**
        1. 🔍 Scan public social media profiles (Twitter/X, LinkedIn bios)
        2. ✨ Apply TI + PSI intelligence to detect GILE resonance
        3. 🔢 Use your numerology + birthday to find compatible matches
        4. 💬 Generate personalized opening messages
        5. 🔒 Privacy: Only public data, no private information accessed
        
        **Technical Roadmap:**
        - Twitter/X API integration for bio scanning
        - LinkedIn profile analysis
        - GILE resonance detection algorithms
        - Claude-powered opening message generation
        - Privacy guardrails and consent management
        
        **For now, try:**
        - 📊 **Candidate Scoring** - Evaluate and rank people you already know
        - ⚖️ **Compare Two People** - Analyze compatibility between two specific individuals
        """)
    
    # ===== MODE B: CANDIDATE SCORING =====
    elif "📊 Candidate Scoring" in mode:
        st.header("📊 Candidate Scoring & Ranking")
        st.markdown("""
        **How it works:**
        1. Upload a list of candidates (names, birthdates, optional bios)
        2. Choose relationship type
        3. God Machine analyzes and ranks them
        4. Get targeted advice for each candidate!
        """)
        
        # Relationship type for candidates
        candidate_relationship_type = st.selectbox(
            "What type of relationship are you evaluating?",
            ["romantic", "friendship", "business", "gm_node", "ti_ally", "mentor"],
            format_func=lambda x: {
                "romantic": "💕 Romantic Partnership",
                "friendship": "🤝 Friendship",
                "business": "💼 Business Partnership",
                "gm_node": "🌐 GM-Node Ally",
                "ti_ally": "✨ TI Collaborator",
                "mentor": "🎓 Mentor/Authority"
            }[x],
            key="candidate_relationship_type"
        )
        
        # User's own info
        with st.expander("✨ Your Information (For Comparison)", expanded=True):
            your_name_candidate = st.text_input("Your Name", key="your_name_candidate")
            your_birthday_candidate = st.text_input("Your Birthday (MM/DD/YYYY)", key="your_bday_candidate")
            your_bio = st.text_area("Your Bio/Profile", height=100, key="your_bio_candidate")
        
        # Candidate input
        st.subheader("👥 Add Candidates")
        
        num_candidates = st.number_input("How many candidates?", min_value=1, max_value=20, value=3)
        
        candidates = []
        for i in range(num_candidates):
            with st.expander(f"Candidate #{i+1}", expanded=(i < 2)):
                col1, col2 = st.columns(2)
                with col1:
                    cand_name = st.text_input(f"Name", key=f"cand_name_{i}")
                with col2:
                    cand_birthday = st.text_input(f"Birthday (MM/DD/YYYY)", key=f"cand_bday_{i}")
                
                cand_bio = st.text_area(f"Bio/Profile (optional)", height=100, key=f"cand_bio_{i}")
                cand_comm = st.text_area(f"Communication Sample (optional)", height=80, key=f"cand_comm_{i}")
                
                if cand_name:
                    candidates.append({
                        "name": cand_name,
                        "birthday": cand_birthday,
                        "profile_text": cand_bio,
                        "communication_sample": cand_comm if cand_comm else None
                    })
        
        if st.button("🎯 Analyze & Rank Candidates", type="primary", use_container_width=True):
            if not your_name_candidate or not your_birthday_candidate:
                st.error("Please provide your own information for comparison!")
            elif len(candidates) == 0:
                st.error("Please add at least one candidate!")
            else:
                # Check Anthropic availability
                api_available = profiler.anthropic_client is not None
                
                if not api_available:
                    st.warning("""
                    ⚠️ **API Unavailable - Using Heuristic Scoring**
                    
                    Anthropic Claude API is not configured. Rankings will use deterministic heuristics:
                    - Name numerology compatibility
                    - Birthday life path analysis
                    - Communication pattern analysis (if provided)
                    - Basic GILE estimation
                    
                    For more accurate results with PSI intelligence, configure the Anthropic API key in Secrets.
                    """)
                
                your_data = {
                    "name": your_name_candidate,
                    "birthday": your_birthday_candidate,
                    "profile_text": your_bio,
                    "communication_sample": None
                }
                
                st.markdown("---")
                st.header("🏆 Candidate Rankings")
                
                # Analyze all candidates
                results_list = []
                for candidate in candidates:
                    with st.spinner(f"Analyzing {candidate['name']}..."):
                        result = profiler.analyze_profile(
                            your_data,
                            candidate,
                            candidate_relationship_type
                        )
                        result["candidate_name"] = candidate["name"]
                        results_list.append(result)
                
                # Sort by compatibility score
                results_list.sort(key=lambda x: x["compatibility_score"], reverse=True)
                
                # Display ranked results
                for rank, result in enumerate(results_list, 1):
                    score = result["compatibility_score"]
                    name = result["candidate_name"]
                    confidence = result["confidence"]
                    
                    # Color coding
                    if score >= 80:
                        emoji = "🏆"
                        color = "green"
                    elif score >= 65:
                        emoji = "✅"
                        color = "blue"
                    elif score >= 50:
                        emoji = "⚠️"
                        color = "orange"
                    else:
                        emoji = "❌"
                        color = "red"
                    
                    with st.expander(f"#{rank} {emoji} {name} - {score}/100 Compatibility", expanded=(rank <= 3)):
                        col1, col2, col3 = st.columns(3)
                        col1.metric("Compatibility", f"{score}/100")
                        col2.metric("Confidence", f"{confidence}%")
                        col3.metric("Network Support", result["psi_prediction"].get("network_support", "N/A").upper())
                        
                        st.success(result["recommendation"])
                        
                        # Targeted advice
                        st.markdown("### 💡 Targeted Advice")
                        advice_points = []
                        
                        # Gottman advice
                        gottman = result["gottman_assessment"]
                        if gottman.get("four_horsemen_detected"):
                            advice_points.append(f"⚠️ **Communication Alert:** Watch for {', '.join(gottman['four_horsemen_detected'])}. Focus on extra positivity!")
                        
                        # Name numerology advice
                        names = result["name_numerology"]
                        if names["numerology_compatible"]:
                            advice_points.append(f"✅ **Name Energy:** Perfect creative synergy (your {names['person1_number']} + their {names['person2_number']})")
                        else:
                            advice_points.append(f"⚠️ **Name Energy:** May need extra patience (your {names['person1_number']} vs their {names['person2_number']})")
                        
                        # GILE advice
                        gile = result["gile_alignment"]
                        high_gile = [k for k, v in gile.items() if k in ['G', 'I', 'L', 'E'] and v >= 8]
                        low_gile = [k for k, v in gile.items() if k in ['G', 'I', 'L', 'E'] and v < 5]
                        
                        if high_gile:
                            advice_points.append(f"💎 **Strength Areas:** {', '.join(high_gile)} alignment is excellent!")
                        if low_gile:
                            advice_points.append(f"🔧 **Growth Areas:** {', '.join(low_gile)} may need attention")
                        
                        # PSI advice
                        psi = result["psi_prediction"]
                        if psi.get("network_support") == "strong":
                            advice_points.append("🌟 **Divine Signal:** Network intelligence STRONGLY supports this connection!")
                        elif psi.get("network_support") == "weak":
                            advice_points.append("⚠️ **Divine Signal:** Proceed with caution - network shows mixed signals")
                        
                        for advice in advice_points:
                            st.markdown(f"- {advice}")
                        
                        # Detailed breakdown
                        with st.expander("📊 Full Analysis"):
                            breakdown_tab1, breakdown_tab2, breakdown_tab3, breakdown_tab4 = st.tabs([
                                "Scores", "Gottman", "Numerology", "GILE"
                            ])
                            
                            with breakdown_tab1:
                                for component, component_score in result["breakdown"].items():
                                    st.progress(component_score / 100, text=f"{component.title()}: {component_score}/100")
                            
                            with breakdown_tab2:
                                st.write(gottman.get("analysis", "No analysis available"))
                            
                            with breakdown_tab3:
                                st.write(f"**Interpretation:** {names['interpretation']}")
                            
                            with breakdown_tab4:
                                cols = st.columns(4)
                                cols[0].metric("Goodness (G)", f"{gile['G']}/10")
                                cols[1].metric("Intuition (I)", f"{gile['I']}/10")
                                cols[2].metric("Love (L)", f"{gile['L']}/10")
                                cols[3].metric("Environment (E)", f"{gile['E']}/10")
                
                # Export all results
                st.markdown("---")
                if st.button("📥 Export All Rankings (JSON)"):
                    export_data = {
                        "your_profile": your_data,
                        "relationship_type": candidate_relationship_type,
                        "rankings": results_list,
                        "timestamp": datetime.now().isoformat()
                    }
                    st.download_button(
                        "Download JSON",
                        json.dumps(export_data, indent=2),
                        f"candidate_rankings_{datetime.now().strftime('%Y%m%d')}.json",
                        "application/json"
                    )
    
    # ===== MODE C: ORIGINAL COMPARE TWO PEOPLE =====
    else:
        st.header("⚖️ Compare Two People")
        
        # Relationship type selector
        relationship_type = st.selectbox(
            "Relationship Type",
            ["romantic", "friendship", "business", "gm_node", "ti_ally"],
            format_func=lambda x: {
                "romantic": "💕 Romantic Partnership",
                "friendship": "🤝 Friendship",
                "business": "💼 Business Partnership",
                "gm_node": "🌐 GM-Node (Network Intelligence Ally)",
                "ti_ally": "✨ TI-Ally (Transcendent Intelligence Collaborator)"
            }[x]
        )
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.subheader("Person 1")
            name1 = st.text_input("Name", key="name1")
            birthday1 = st.text_input("Birthday (MM/DD/YYYY)", key="bday1")
            profile1 = st.text_area("Profile/Bio", key="profile1", height=150)
            comm1 = st.text_area("Communication Sample (optional)", key="comm1", height=100)
        
        with col2:
            st.subheader("Person 2")
            name2 = st.text_input("Name", key="name2")
            birthday2 = st.text_input("Birthday (MM/DD/YYYY)", key="bday2")
            profile2 = st.text_area("Profile/Bio", key="profile2", height=150)
            comm2 = st.text_area("Communication Sample (optional)", key="comm2", height=100)
        
        if st.button("🔮 Analyze Compatibility", type="primary"):
            if not name1 or not name2:
                st.error("Please provide names for both people!")
                return
            
            with st.spinner("Accessing network intelligence..."):
                person1_data = {
                    "name": name1,
                    "birthday": birthday1,
                    "profile_text": profile1,
                    "communication_sample": comm1 if comm1 else None
                }
                
                person2_data = {
                    "name": name2,
                    "birthday": birthday2,
                    "profile_text": profile2,
                    "communication_sample": comm2 if comm2 else None
                }
                
                results = profiler.analyze_profile(
                    person1_data,
                    person2_data,
                    relationship_type
                )
                
                # Display results
                st.markdown("---")
                st.header("📊 Compatibility Analysis")
                
                # Overall score
                score = results["compatibility_score"]
                confidence = results["confidence"]
                
                col1, col2, col3 = st.columns(3)
                col1.metric("Overall Compatibility", f"{score}/100")
                col2.metric("Confidence Level", f"{confidence}%")
                col3.metric("Network Support", results["psi_prediction"].get("network_support", "N/A").upper())
                
                st.success(results["recommendation"])
                
                # Detailed breakdown
                with st.expander("📊 Detailed Score Breakdown"):
                    breakdown = results["breakdown"]
                    
                    st.write("**Component Scores:**")
                    for component, component_score in breakdown.items():
                        st.progress(component_score / 100, text=f"{component.title()}: {component_score}/100")
                
                # Gottman Analysis
                with st.expander("💬 Gottman Communication Analysis"):
                    gottman = results["gottman_assessment"]
                    st.write(f"**Gottman Score:** {gottman['gottman_score']}/100")
                    
                    if gottman.get("four_horsemen_detected"):
                        st.warning(f"⚠️ Four Horsemen Detected: {', '.join(gottman['four_horsemen_detected'])}")
                    else:
                        st.success("✅ No Four Horsemen detected!")
                    
                    if gottman.get("positive_negative_ratio"):
                        st.info(f"**Positive:Negative Ratio:** {gottman['positive_negative_ratio']} (Magic Ratio = 5:1)")
                    
                    st.write(gottman.get("analysis", "No analysis available"))
                
                # Name Numerology
                with st.expander("🔢 Name Numerology Analysis"):
                    names = results["name_numerology"]
                    st.write(f"**{name1}:** Number {names['person1_number']} (Length: {names['person1_name_length']})")
                    st.write(f"**{name2}:** Number {names['person2_number']} (Length: {names['person2_name_length']})")
                    st.write(f"**Interpretation:** {names['interpretation']}")
                    st.write(f"**Compatible:** {'✅ Yes' if names['numerology_compatible'] else '❌ No'}")
                
                # Birthday Compatibility
                with st.expander("🎂 Birthday/Life Path Analysis"):
                    birthdays = results["birthday_compatibility"]
                    if "life_path_compatible" in birthdays:
                        st.write(f"**Life Path Compatibility:** {'✅ Yes' if birthdays['life_path_compatible'] else '❌ No'}")
                        st.write(f"**{name1}:** Life Path {birthdays['person1_life_path']}")
                        st.write(f"**{name2}:** Life Path {birthdays['person2_life_path']}")
                
                # GILE Alignment
                with st.expander("✨ GILE Alignment"):
                    gile = results["gile_alignment"]
                    cols = st.columns(4)
                    cols[0].metric("Goodness (G)", f"{gile['G']}/10")
                    cols[1].metric("Intuition (I)", f"{gile['I']}/10")
                    cols[2].metric("Love (L)", f"{gile['L']}/10")
                    cols[3].metric("Environment (E)", f"{gile['E']}/10")
                    st.write(gile.get("analysis", ""))
                
                # PSI Prediction
                with st.expander("🔮 PSI Network Intelligence"):
                    psi = results["psi_prediction"]
                    st.write(f"**PSI Compatibility:** {psi['psi_compatibility']}/100")
                    st.write(f"**Network Support:** {psi['network_support'].upper()}")
                    st.write(f"**Timeline Probability:** {psi.get('timeline_probability', 'N/A')}")
                    st.info(f"**PSI Insights:** {psi.get('psi_insights', 'N/A')}")
            
            # Export results
            st.markdown("---")
            if st.button("📥 Export Analysis (JSON)"):
                st.download_button(
                    "Download JSON",
                    json.dumps(results, indent=2),
                    f"relationship_analysis_{name1}_{name2}_{datetime.now().strftime('%Y%m%d')}.json",
                    "application/json"
                )


if __name__ == "__main__":
    render_relationship_profiler()
