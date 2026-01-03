"""
GILE Content Optimizer
Scores content for virality and TI-alignment
Shared service for Video, Book, and Social Media generators
"""

from typing import Dict, Any, List, Tuple
import re
from datetime import datetime


class GILEContentOptimizer:
    """
    Score content for virality using TI metrics
    
    GILE Framework:
    - G (Goodness): Moral alignment, helpfulness, positive impact
    - I (Intuition): Resonance with truth, "feels right" quality
    - L (Love): Emotional connection, compassion, unity
    - E (Environment): Context-appropriate, timely, relevant
    """
    
    # GILE weights (from replit.md)
    WEIGHTS = {
        'G': 0.40,  # Goodness (most important)
        'I': 0.25,  # Intuition
        'L': 0.25,  # Love
        'E': 0.10   # Environment
    }
    
    # Sacred numbers that boost resonance
    SACRED_NUMBERS = {3, 11, 33, 333, 3333}
    
    def __init__(self):
        pass
    
    def score_goodness(self, content: str, metadata: Dict[str, Any] = None) -> float:
        """
        Score Goodness dimension (-3 to +2)
        
        Positive indicators:
        - Helpful, constructive, educational
        - Promotes well-being and growth
        - Scientific rigor, evidence-based
        
        Negative indicators:
        - Harmful, destructive content
        - Misinformation, deception
        - Exploitative or manipulative
        
        Args:
            content: Text content to score
            metadata: Optional metadata (tags, source, etc.)
        
        Returns:
            Score from -3 to +2
        """
        score = 0.0
        
        # Positive keywords
        positive_keywords = [
            'help', 'discover', 'understand', 'learn', 'grow',
            'heal', 'improve', 'benefit', 'wisdom', 'truth',
            'evidence', 'research', 'study', 'validate', 'prove'
        ]
        
        # Negative keywords
        negative_keywords = [
            'harm', 'destroy', 'manipulate', 'deceive', 'exploit',
            'fake', 'scam', 'lie', 'cheat', 'abuse'
        ]
        
        content_lower = content.lower()
        
        # Count positive indicators
        positive_count = sum(1 for keyword in positive_keywords if keyword in content_lower)
        negative_count = sum(1 for keyword in negative_keywords if keyword in content_lower)
        
        # Base score from keyword balance
        score = min(2.0, positive_count * 0.2 - negative_count * 0.5)
        score = max(-3.0, score)
        
        # Boost for scientific/research content
        if metadata and any(tag in ['research', 'science', 'paper', 'study'] 
                           for tag in metadata.get('tags', [])):
            score += 0.5
        
        return min(2.0, max(-3.0, score))
    
    def score_intuition(self, content: str, metadata: Dict[str, Any] = None) -> float:
        """
        Score Intuition dimension (-3 to +2)
        
        High intuition = resonates with deep truth
        
        Indicators:
        - Clear, coherent logic
        - Connects to fundamental principles
        - "Feels right" - elegant, simple
        - First principles reasoning
        
        Args:
            content: Text content to score
            metadata: Optional metadata
        
        Returns:
            Score from -3 to +2
        """
        score = 0.0
        
        # Intuitive keywords
        intuitive_keywords = [
            'obvious', 'clear', 'simple', 'elegant', 'fundamental',
            'principle', 'truth', 'essence', 'core', 'intuition',
            'resonance', 'coherent', 'logical', 'natural'
        ]
        
        # Anti-intuitive keywords
        confusing_keywords = [
            'confusing', 'unclear', 'contradictory', 'illogical',
            'nonsense', 'random', 'arbitrary', 'chaotic'
        ]
        
        content_lower = content.lower()
        
        # Count indicators
        intuitive_count = sum(1 for keyword in intuitive_keywords if keyword in content_lower)
        confusing_count = sum(1 for keyword in confusing_keywords if keyword in content_lower)
        
        score = min(2.0, intuitive_count * 0.3 - confusing_count * 0.4)
        score = max(-3.0, score)
        
        # Boost for mathematical/logical content
        if any(indicator in content_lower for indicator in ['theorem', 'proof', 'equation', 'formula']):
            score += 0.4
        
        return min(2.0, max(-3.0, score))
    
    def score_love(self, content: str, metadata: Dict[str, Any] = None) -> float:
        """
        Score Love dimension (-3 to +2)
        
        High love = emotional connection, compassion, unity
        
        Indicators:
        - Compassionate, caring language
        - Connects people, builds community
        - Inspiring, uplifting
        - Promotes unity and understanding
        
        Args:
            content: Text content to score
            metadata: Optional metadata
        
        Returns:
            Score from -3 to +2
        """
        score = 0.0
        
        # Love keywords
        love_keywords = [
            'love', 'compassion', 'care', 'kindness', 'unity',
            'together', 'community', 'connection', 'heart', 'inspire',
            'uplift', 'hope', 'beauty', 'wonder', 'gratitude'
        ]
        
        # Anti-love keywords
        negative_keywords = [
            'hate', 'division', 'separation', 'anger', 'fear',
            'despair', 'cynicism', 'cold', 'harsh', 'cruel'
        ]
        
        content_lower = content.lower()
        
        # Count indicators
        love_count = sum(1 for keyword in love_keywords if keyword in content_lower)
        negative_count = sum(1 for keyword in negative_keywords if keyword in content_lower)
        
        score = min(2.0, love_count * 0.3 - negative_count * 0.5)
        score = max(-3.0, score)
        
        # Boost for inspirational content
        if metadata and 'inspirational' in metadata.get('tags', []):
            score += 0.5
        
        return min(2.0, max(-3.0, score))
    
    def score_environment(self, content: str, metadata: Dict[str, Any] = None) -> float:
        """
        Score Environment dimension (-3 to +2)
        
        High environment = context-appropriate, timely, relevant
        
        Indicators:
        - Timely, relevant to current context
        - Matches audience expectations
        - Appropriate tone and style
        - Well-timed for maximum impact
        
        Args:
            content: Text content to score
            metadata: Optional metadata (timestamp, audience, etc.)
        
        Returns:
            Score from -3 to +2
        """
        score = 0.5  # Neutral baseline
        
        # Check timeliness
        if metadata and 'timestamp' in metadata:
            # Recent content scores higher
            try:
                timestamp = metadata['timestamp']
                if isinstance(timestamp, str):
                    timestamp = datetime.fromisoformat(timestamp)
                
                age_days = (datetime.now() - timestamp).days
                
                if age_days < 1:
                    score += 0.8  # Very fresh
                elif age_days < 7:
                    score += 0.4  # Recent
                elif age_days < 30:
                    score += 0.2  # Fairly recent
                else:
                    score -= 0.2  # Older content
            except:
                pass
        
        # Check sacred numerology
        if metadata:
            # Check for sacred numbers in metadata
            for value in [metadata.get('word_count'), metadata.get('length')]:
                if value and any(value % sacred == 0 for sacred in self.SACRED_NUMBERS):
                    score += 0.3  # Sacred number alignment
                    break
        
        return min(2.0, max(-3.0, score))
    
    def calculate_composite_score(
        self, 
        content: str, 
        metadata: Dict[str, Any] = None
    ) -> Dict[str, Any]:
        """
        Calculate full GILE composite score
        
        Returns:
            {
                'G': goodness_score,
                'I': intuition_score,
                'L': love_score,
                'E': environment_score,
                'composite': weighted_sum,
                'virality_prediction': 0-1 probability,
                'recommendations': [list of improvement suggestions]
            }
        """
        # Calculate individual dimensions
        G = self.score_goodness(content, metadata)
        I = self.score_intuition(content, metadata)
        L = self.score_love(content, metadata)
        E = self.score_environment(content, metadata)
        
        # Calculate weighted composite (-3 to +2 scale)
        composite = (
            self.WEIGHTS['G'] * G +
            self.WEIGHTS['I'] * I +
            self.WEIGHTS['L'] * L +
            self.WEIGHTS['E'] * E
        )
        
        # Convert to virality probability (0 to 1)
        # Map -3 to +2 range → 0 to 1
        # -3 = 0% virality, +2 = 100% virality
        virality = (composite + 3) / 5.0
        
        # Generate recommendations
        recommendations = self._generate_recommendations(G, I, L, E, content)
        
        return {
            'G': round(G, 2),
            'I': round(I, 2),
            'L': round(L, 2),
            'E': round(E, 2),
            'composite': round(composite, 2),
            'virality_prediction': round(virality, 2),
            'recommendations': recommendations,
            'gile_formula': f"MR = {self.WEIGHTS['G']}·G + {self.WEIGHTS['I']}·I + {self.WEIGHTS['L']}·L + {self.WEIGHTS['E']}·E",
            'breakdown': f"G={G:.1f}, I={I:.1f}, L={L:.1f}, E={E:.1f} → {composite:.2f}"
        }
    
    def _generate_recommendations(
        self, 
        G: float, 
        I: float, 
        L: float, 
        E: float,
        content: str
    ) -> List[str]:
        """Generate actionable recommendations for improving content"""
        recommendations = []
        
        if G < 0.5:
            recommendations.append("⬆️ Boost Goodness: Add more helpful, educational, or beneficial content")
        
        if I < 0.5:
            recommendations.append("🧠 Boost Intuition: Simplify logic, connect to fundamental principles")
        
        if L < 0.5:
            recommendations.append("❤️ Boost Love: Add inspiring, compassionate, or emotionally connecting elements")
        
        if E < 0.5:
            recommendations.append("🌍 Boost Environment: Ensure content is timely, relevant, and context-appropriate")
        
        # Sacred numerology recommendation
        word_count = len(content.split())
        if not any(word_count % sacred == 0 for sacred in self.SACRED_NUMBERS):
            # Find nearest sacred target
            nearest_sacred = min(self.SACRED_NUMBERS, key=lambda x: abs(x - word_count))
            recommendations.append(
                f"🔢 Sacred Numerology: Current word count {word_count}. "
                f"Consider targeting {nearest_sacred} words for sacred resonance."
            )
        
        if not recommendations:
            recommendations.append("✨ Excellent! Content is well-optimized for virality.")
        
        return recommendations


# Global optimizer instance
_optimizer = None


def get_optimizer() -> GILEContentOptimizer:
    """Get or create global optimizer instance"""
    global _optimizer
    
    if _optimizer is None:
        _optimizer = GILEContentOptimizer()
    
    return _optimizer


def optimize_content(content: str, metadata: Dict[str, Any] = None) -> Dict[str, Any]:
    """
    Quick access function to optimize content
    
    Usage:
        result = optimize_content("My amazing content here!")
        print(f"Virality prediction: {result['virality_prediction']:.0%}")
    """
    optimizer = get_optimizer()
    return optimizer.calculate_composite_score(content, metadata)
