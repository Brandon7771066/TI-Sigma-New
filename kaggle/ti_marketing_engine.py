"""
TI Marketing Intelligence Engine
=================================

Marketing applications where TI provides unique competitive advantage:
1. Campaign Performance Prediction
2. Creative Resonance Scoring
3. Audience Connection Analysis
4. Viral Potential Detection
5. GILE-Optimized Content Strategy

Academic framing:
- "Multi-dimensional resonance scoring"
- "Connection intensity metrics"
- "Engagement coherence analysis"
- "Viral cascade prediction"

Internal: This is GILE optimization for marketing.

Applications:
- Social media campaign optimization
- Ad creative A/B testing prediction
- Content calendar optimization
- Influencer partnership scoring
- Product launch timing
"""

import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime, timedelta
import re

@dataclass
class ContentAnalysis:
    """Analysis result for a piece of content."""
    resonance_score: float  # GILE-based connection strength
    clarity_score: float    # Message clarity
    authenticity_score: float  # Perceived genuineness
    energy_score: float     # Activation potential
    viral_potential: float  # Probability of spreading
    optimal_timing: str     # Best time to post
    recommendations: List[str]

@dataclass 
class CampaignPrediction:
    """Prediction for campaign performance."""
    expected_engagement_rate: float
    expected_conversion_rate: float
    expected_roi: float
    confidence: float
    risk_factors: List[str]
    optimization_suggestions: List[str]

class MarketingGILEEngine:
    """
    GILE-based marketing optimization engine.
    
    Maps GILE dimensions to marketing metrics:
    - G (Goodness) → Brand authenticity, trust signals
    - I (Intuition) → Message clarity, emotional resonance
    - L (Love) → Audience connection, community strength
    - E (Environment) → Market timing, competitive landscape
    
    Academic: "Multi-dimensional engagement optimization"
    Internal: GILE optimization for marketing
    """
    
    # Engagement patterns by hour (based on research)
    OPTIMAL_HOURS = {
        'B2B': [9, 10, 11, 14, 15],  # Business hours
        'B2C': [12, 13, 19, 20, 21],  # Lunch + evening
        'Gen_Z': [15, 16, 21, 22, 23],  # After school + late
        'Professionals': [7, 8, 12, 18, 19],  # Commute + lunch
    }
    
    # Emotional trigger words with resonance scores
    RESONANCE_TRIGGERS = {
        # High positive resonance
        'free': 0.9, 'new': 0.8, 'exclusive': 0.85, 'limited': 0.8,
        'you': 0.7, 'your': 0.7, 'discover': 0.75, 'transform': 0.8,
        'secret': 0.85, 'proven': 0.7, 'guaranteed': 0.75,
        
        # Connection triggers (L dimension)
        'together': 0.8, 'community': 0.75, 'join': 0.7, 'share': 0.7,
        'we': 0.6, 'us': 0.6, 'family': 0.8, 'friends': 0.75,
        
        # Authenticity triggers (G dimension)
        'honest': 0.8, 'real': 0.75, 'genuine': 0.8, 'truth': 0.75,
        'transparent': 0.7, 'authentic': 0.85, 'natural': 0.7,
        
        # Clarity triggers (I dimension)
        'simple': 0.7, 'easy': 0.75, 'clear': 0.7, 'step-by-step': 0.8,
        'quick': 0.7, 'instant': 0.75, 'now': 0.7,
        
        # Negative resonance (reduce score)
        'buy': -0.1, 'purchase': -0.1, 'expensive': -0.3, 'cost': -0.2,
        'complicated': -0.3, 'difficult': -0.2, 'problem': -0.1,
    }
    
    def __init__(self):
        self.history: List[Dict] = []
    
    def analyze_content(self, text: str, 
                        content_type: str = 'social',
                        target_audience: str = 'B2C') -> ContentAnalysis:
        """
        Analyze content for GILE optimization.
        
        Args:
            text: The content to analyze
            content_type: 'social', 'email', 'ad', 'blog'
            target_audience: 'B2B', 'B2C', 'Gen_Z', 'Professionals'
        
        Returns:
            ContentAnalysis with scores and recommendations
        """
        
        # G - Goodness/Authenticity
        authenticity = self._score_authenticity(text)
        
        # I - Intuition/Clarity
        clarity = self._score_clarity(text)
        
        # L - Love/Connection
        connection = self._score_connection(text)
        
        # E - Environment/Energy
        energy = self._score_energy(text)
        
        # Combined GILE resonance
        resonance = self._compute_resonance(authenticity, clarity, connection, energy)
        
        # Viral potential (non-linear - needs all factors high)
        viral = self._compute_viral_potential(resonance, energy, connection)
        
        # Optimal timing
        timing = self._get_optimal_timing(target_audience)
        
        # Generate recommendations
        recommendations = self._generate_recommendations(
            authenticity, clarity, connection, energy, text
        )
        
        return ContentAnalysis(
            resonance_score=resonance,
            clarity_score=clarity,
            authenticity_score=authenticity,
            energy_score=energy,
            viral_potential=viral,
            optimal_timing=timing,
            recommendations=recommendations
        )
    
    def _score_authenticity(self, text: str) -> float:
        """
        Score content for authenticity (G dimension).
        
        Factors:
        - Personal pronouns (we, I) vs corporate speak
        - Authenticity trigger words
        - Absence of hyperbole
        - Story elements
        """
        text_lower = text.lower()
        words = text_lower.split()
        
        score = 0.5  # Baseline
        
        # Personal pronouns boost authenticity
        personal = sum(1 for w in words if w in ['i', 'we', 'my', 'our', 'me', 'us'])
        score += min(personal / len(words) * 5, 0.2)
        
        # Authenticity triggers
        for word, value in self.RESONANCE_TRIGGERS.items():
            if word in text_lower and value > 0.7:
                if word in ['honest', 'real', 'genuine', 'authentic', 'truth', 'natural']:
                    score += 0.05
        
        # Penalize corporate buzzwords
        buzzwords = ['synergy', 'leverage', 'optimize', 'disrupting', 'paradigm']
        for buzz in buzzwords:
            if buzz in text_lower:
                score -= 0.1
        
        # Story indicators boost authenticity
        story_words = ['when', 'then', 'because', 'realized', 'discovered', 'learned']
        story_count = sum(1 for w in story_words if w in text_lower)
        score += min(story_count * 0.05, 0.15)
        
        return float(np.clip(score, 0.0, 1.0))
    
    def _score_clarity(self, text: str) -> float:
        """
        Score content for clarity (I dimension).
        
        Factors:
        - Sentence length
        - Word complexity
        - Clear call to action
        - Structure
        """
        words = text.split()
        sentences = text.replace('!', '.').replace('?', '.').split('.')
        sentences = [s.strip() for s in sentences if s.strip()]
        
        score = 0.5
        
        # Optimal sentence length (10-20 words)
        if sentences:
            avg_sentence_len = len(words) / len(sentences)
            if 10 <= avg_sentence_len <= 20:
                score += 0.15
            elif avg_sentence_len > 30:
                score -= 0.2
        
        # Simple words (shorter = clearer)
        avg_word_len = np.mean([len(w) for w in words]) if words else 5
        if avg_word_len < 5:
            score += 0.1
        elif avg_word_len > 7:
            score -= 0.1
        
        # Clear CTA presence
        cta_words = ['click', 'sign up', 'get', 'start', 'try', 'join', 'download', 'learn']
        text_lower = text.lower()
        has_cta = any(cta in text_lower for cta in cta_words)
        if has_cta:
            score += 0.15
        
        # Numbers add clarity
        has_numbers = bool(re.search(r'\d+', text))
        if has_numbers:
            score += 0.1
        
        return float(np.clip(score, 0.0, 1.0))
    
    def _score_connection(self, text: str) -> float:
        """
        Score content for connection (L dimension).
        
        Factors:
        - Second person (you/your)
        - Community language
        - Emotional triggers
        - Question engagement
        """
        text_lower = text.lower()
        words = text_lower.split()
        
        score = 0.5
        
        # "You" focus is critical
        you_count = sum(1 for w in words if w in ['you', 'your', "you're", "you'll"])
        you_ratio = you_count / len(words) if words else 0
        score += min(you_ratio * 10, 0.25)
        
        # Community language
        community_words = ['together', 'community', 'join', 'share', 'we', 'us', 'our']
        community_count = sum(1 for w in words if w in community_words)
        score += min(community_count * 0.05, 0.15)
        
        # Questions drive engagement
        question_count = text.count('?')
        score += min(question_count * 0.05, 0.1)
        
        # Emotional resonance triggers
        for word, value in self.RESONANCE_TRIGGERS.items():
            if word in text_lower and value > 0:
                score += value * 0.02
        
        return float(np.clip(score, 0.0, 1.0))
    
    def _score_energy(self, text: str) -> float:
        """
        Score content for energy/activation (E dimension).
        
        Factors:
        - Action verbs
        - Urgency signals
        - Exclamation energy
        - Power words
        """
        text_lower = text.lower()
        
        score = 0.5
        
        # Action verbs
        action_words = ['get', 'start', 'discover', 'unlock', 'transform', 'boost', 
                        'create', 'build', 'achieve', 'launch', 'grow']
        action_count = sum(1 for w in action_words if w in text_lower)
        score += min(action_count * 0.05, 0.2)
        
        # Urgency signals
        urgency_words = ['now', 'today', 'limited', 'exclusive', 'last chance', 
                         'don\'t miss', 'hurry', 'ending soon']
        urgency_count = sum(1 for w in urgency_words if w in text_lower)
        score += min(urgency_count * 0.08, 0.2)
        
        # Exclamation energy (but not too many)
        exclamation_count = text.count('!')
        if exclamation_count == 1:
            score += 0.1
        elif exclamation_count == 2:
            score += 0.05
        elif exclamation_count > 3:
            score -= 0.1  # Too aggressive
        
        # Emoji energy (moderate boost)
        emoji_pattern = re.compile("["
            u"\U0001F600-\U0001F64F"  # emoticons
            u"\U0001F300-\U0001F5FF"  # symbols
            u"\U0001F680-\U0001F6FF"  # transport
            u"\U0001F1E0-\U0001F1FF"  # flags
            "]+", flags=re.UNICODE)
        emoji_count = len(emoji_pattern.findall(text))
        if 1 <= emoji_count <= 3:
            score += 0.1
        elif emoji_count > 5:
            score -= 0.05
        
        return float(np.clip(score, 0.0, 1.0))
    
    def _compute_resonance(self, g: float, i: float, l: float, e: float) -> float:
        """
        Compute overall GILE resonance score.
        
        Uses geometric mean (same as trading intensity formula).
        """
        product = g * i * l * e
        resonance = float(np.power(max(product, 0.0), 0.25))
        return float(np.clip(resonance, 0.0, 1.0))
    
    def _compute_viral_potential(self, resonance: float, 
                                  energy: float, 
                                  connection: float) -> float:
        """
        Compute viral potential.
        
        Viral content requires:
        - High base resonance (all GILE factors aligned)
        - High energy (drives sharing)
        - High connection (creates community spread)
        
        Non-linear: all three must be present.
        """
        # Threshold effect - need all three above baseline
        if resonance < 0.6 or energy < 0.5 or connection < 0.5:
            return resonance * 0.3  # Low viral potential
        
        # Viral multiplier when all factors align
        viral = resonance * (1 + (energy - 0.5) * 0.5 + (connection - 0.5) * 0.5)
        
        return float(np.clip(viral, 0.0, 1.0))
    
    def _get_optimal_timing(self, target_audience: str) -> str:
        """Get optimal posting time for audience."""
        hours = self.OPTIMAL_HOURS.get(target_audience, self.OPTIMAL_HOURS['B2C'])
        
        # Format as recommendation
        am_hours = [h for h in hours if h < 12]
        pm_hours = [h for h in hours if h >= 12]
        
        timing = []
        if am_hours:
            timing.append(f"{am_hours[0]}:00 AM")
        if pm_hours:
            timing.append(f"{pm_hours[0]-12 if pm_hours[0] > 12 else 12}:00 PM")
        
        return " or ".join(timing)
    
    def _generate_recommendations(self, g: float, i: float, l: float, e: float, 
                                   text: str) -> List[str]:
        """Generate specific improvement recommendations."""
        recommendations = []
        
        # Authenticity (G)
        if g < 0.6:
            recommendations.append("Add personal story or specific example to increase authenticity")
        if g < 0.5:
            recommendations.append("Remove corporate buzzwords - use conversational language")
        
        # Clarity (I)
        if i < 0.6:
            recommendations.append("Shorten sentences - aim for 15-20 words per sentence")
        if 'you' not in text.lower():
            recommendations.append("Add a clear call-to-action (what should they do next?)")
        if i < 0.5:
            recommendations.append("Add specific numbers or data points for credibility")
        
        # Connection (L)
        if l < 0.6:
            recommendations.append("Use more 'you' and 'your' - make it about the reader")
        if l < 0.5:
            recommendations.append("Ask a question to drive engagement")
        if '?' not in text:
            recommendations.append("Consider ending with a question to spark discussion")
        
        # Energy (E)
        if e < 0.6:
            recommendations.append("Add urgency - why should they act NOW?")
        if e < 0.5:
            recommendations.append("Use stronger action verbs (discover, transform, unlock)")
        
        # If all scores are good, provide optimization tips
        if g >= 0.7 and i >= 0.7 and l >= 0.7 and e >= 0.7:
            recommendations.append("Content is well-optimized! Consider A/B testing variations")
        
        return recommendations[:5]  # Max 5 recommendations
    
    def predict_campaign_performance(self, 
                                      content_list: List[str],
                                      budget: float,
                                      duration_days: int,
                                      platform: str = 'mixed') -> CampaignPrediction:
        """
        Predict campaign performance based on content analysis.
        
        Args:
            content_list: List of ad/content variations
            budget: Campaign budget in $
            duration_days: Campaign duration
            platform: 'facebook', 'instagram', 'linkedin', 'mixed'
        
        Returns:
            CampaignPrediction with expected metrics
        """
        # Analyze all content
        analyses = [self.analyze_content(c) for c in content_list]
        
        # Average resonance across all content
        avg_resonance = np.mean([a.resonance_score for a in analyses])
        max_resonance = max(a.resonance_score for a in analyses)
        
        # Platform multipliers
        platform_multipliers = {
            'facebook': 1.0,
            'instagram': 1.2,  # Higher engagement rates
            'linkedin': 0.8,   # Lower engagement, higher quality
            'twitter': 0.9,
            'tiktok': 1.5,     # Highest viral potential
            'mixed': 1.0
        }
        platform_mult = platform_multipliers.get(platform, 1.0)
        
        # Base rates (industry averages)
        base_engagement = 0.02  # 2%
        base_conversion = 0.01  # 1%
        
        # GILE-adjusted rates
        engagement_rate = base_engagement * (1 + (avg_resonance - 0.5) * 2) * platform_mult
        conversion_rate = base_conversion * (1 + (max_resonance - 0.5) * 3)
        
        # Estimate impressions from budget (rough: $5 CPM average)
        estimated_impressions = (budget / 5) * 1000
        
        # Expected outcomes
        expected_clicks = estimated_impressions * engagement_rate
        expected_conversions = expected_clicks * conversion_rate
        
        # ROI calculation (assuming $50 value per conversion)
        expected_revenue = expected_conversions * 50
        expected_roi = (expected_revenue - budget) / budget * 100 if budget > 0 else 0
        
        # Confidence based on content consistency
        resonance_std = np.std([a.resonance_score for a in analyses])
        confidence = 0.8 - min(resonance_std * 2, 0.4)  # Lower std = higher confidence
        
        # Risk factors
        risk_factors = []
        if avg_resonance < 0.5:
            risk_factors.append("Low average content resonance - consider rewriting")
        if resonance_std > 0.2:
            risk_factors.append("High variation in content quality - standardize approach")
        if duration_days < 7:
            risk_factors.append("Short duration may not allow algorithm optimization")
        if budget < 100:
            risk_factors.append("Low budget limits statistical significance")
        
        # Optimization suggestions
        suggestions = []
        if avg_resonance < 0.6:
            suggestions.append("Improve content GILE scores before launching")
        if len(content_list) < 3:
            suggestions.append("Add more content variations for better A/B testing")
        suggestions.append(f"Best performing content: #{analyses.index(max(analyses, key=lambda x: x.resonance_score)) + 1}")
        
        return CampaignPrediction(
            expected_engagement_rate=engagement_rate,
            expected_conversion_rate=conversion_rate,
            expected_roi=expected_roi,
            confidence=confidence,
            risk_factors=risk_factors,
            optimization_suggestions=suggestions
        )
    
    def optimize_headline(self, headline: str, 
                          variations: int = 5) -> List[Tuple[str, float]]:
        """
        Generate optimized headline variations.
        
        Returns list of (headline, predicted_score) tuples.
        """
        base_analysis = self.analyze_content(headline)
        base_score = base_analysis.resonance_score
        
        variations_list = [(headline, base_score)]
        
        # Power word substitutions
        power_words = {
            'good': ['amazing', 'incredible', 'powerful'],
            'get': ['unlock', 'discover', 'claim'],
            'learn': ['master', 'discover', 'unlock'],
            'improve': ['transform', 'revolutionize', 'supercharge'],
            'save': ['slash', 'cut', 'eliminate'],
            'buy': ['get', 'claim', 'secure'],
        }
        
        # Generate variations
        headline_lower = headline.lower()
        for old, replacements in power_words.items():
            if old in headline_lower:
                for new in replacements[:2]:  # Max 2 per word
                    new_headline = re.sub(old, new, headline, flags=re.IGNORECASE)
                    analysis = self.analyze_content(new_headline)
                    variations_list.append((new_headline, analysis.resonance_score))
        
        # Add urgency variation
        if 'now' not in headline_lower and 'today' not in headline_lower:
            urgent_headline = headline.rstrip('.!') + ' — Starting Today!'
            analysis = self.analyze_content(urgent_headline)
            variations_list.append((urgent_headline, analysis.resonance_score))
        
        # Add question variation
        if '?' not in headline:
            q_headline = "Ready to " + headline[0].lower() + headline[1:].rstrip('.!') + "?"
            analysis = self.analyze_content(q_headline)
            variations_list.append((q_headline, analysis.resonance_score))
        
        # Sort by score and return top N
        variations_list.sort(key=lambda x: x[1], reverse=True)
        return variations_list[:variations]


def demo_marketing_engine():
    """Demonstrate the marketing GILE engine."""
    
    print("=" * 70)
    print("TI Marketing Intelligence Engine - Demo")
    print("=" * 70)
    
    engine = MarketingGILEEngine()
    
    # Test content samples
    samples = [
        "Buy our product now! It's the best on the market. Limited time offer!",
        "We discovered something that changed everything. Here's what we learned...",
        "Ready to transform your morning routine? Join 50,000+ who wake up energized.",
        "HUGE SALE!!! BUY NOW!!! DON'T MISS OUT!!! BEST PRICES EVER!!!",
    ]
    
    print("\nContent Analysis Results:\n")
    
    for i, content in enumerate(samples, 1):
        print(f"Sample {i}: \"{content[:60]}...\"" if len(content) > 60 else f"Sample {i}: \"{content}\"")
        
        analysis = engine.analyze_content(content)
        
        print(f"  Resonance Score:   {analysis.resonance_score:.2f}")
        print(f"  Authenticity (G):  {analysis.authenticity_score:.2f}")
        print(f"  Clarity (I):       {analysis.clarity_score:.2f}")
        print(f"  Connection (L):    {analysis.energy_score:.2f}")
        print(f"  Energy (E):        {analysis.energy_score:.2f}")
        print(f"  Viral Potential:   {analysis.viral_potential:.2f}")
        print(f"  Best Time:         {analysis.optimal_timing}")
        print(f"  Recommendations:")
        for rec in analysis.recommendations[:3]:
            print(f"    • {rec}")
        print()
    
    # Campaign prediction
    print("-" * 70)
    print("Campaign Performance Prediction")
    print("-" * 70)
    
    campaign_content = [
        "Transform your productivity with our proven system",
        "Join 10,000+ professionals who doubled their output",
        "Get started free today - no credit card required"
    ]
    
    prediction = engine.predict_campaign_performance(
        content_list=campaign_content,
        budget=1000,
        duration_days=14,
        platform='instagram'
    )
    
    print(f"\nCampaign: $1,000 budget, 14 days, Instagram")
    print(f"  Expected Engagement Rate: {prediction.expected_engagement_rate:.2%}")
    print(f"  Expected Conversion Rate: {prediction.expected_conversion_rate:.2%}")
    print(f"  Expected ROI:             {prediction.expected_roi:.1f}%")
    print(f"  Confidence:               {prediction.confidence:.1%}")
    
    if prediction.risk_factors:
        print(f"  Risk Factors:")
        for rf in prediction.risk_factors:
            print(f"    ⚠️ {rf}")
    
    print(f"  Suggestions:")
    for sug in prediction.optimization_suggestions:
        print(f"    → {sug}")
    
    # Headline optimization
    print("\n" + "-" * 70)
    print("Headline Optimization")
    print("-" * 70)
    
    original = "Learn how to improve your marketing"
    variations = engine.optimize_headline(original)
    
    print(f"\nOriginal: \"{original}\"")
    print(f"\nOptimized Variations:")
    for headline, score in variations:
        marker = "⭐" if score == max(v[1] for v in variations) else "  "
        print(f"  {marker} [{score:.2f}] {headline}")
    
    print("\n" + "=" * 70)
    print("Engine ready for marketing optimization!")
    print("=" * 70)


if __name__ == "__main__":
    demo_marketing_engine()
