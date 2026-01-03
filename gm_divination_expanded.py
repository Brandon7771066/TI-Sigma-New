"""
GM EXPANDED DIVINATION & PREDICTION SYSTEMS
============================================

Integrates multiple divination systems with the Grand Myrion:
1. Biorhythm (Physical/Emotional/Intellectual cycles)
2. Tarot (78 cards, Major/Minor Arcana) 
3. Runes (Elder Futhark - 24 symbols)
4. Vedic Astrology (Nakshatras, Dasha periods)
5. Chinese BaZi (Four Pillars of Destiny)
6. Human Design (Gates, Channels, Types)

Also includes:
- EEG-to-GILE mapping for meditation analysis
- Relationship prediction with Speed Dating dataset
- Creativity success/failure timeline prediction

Author: Brandon Emerick / TI Framework
Date: Christmas 2025
"""

import math
import hashlib
from datetime import datetime, date, timedelta
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
from enum import Enum
import json

PHI_GOLDEN = 1.618033988749895
SACRED_THRESHOLD = 0.85
SUSTAINABLE_COHERENCE = 0.92


class EEGBand(Enum):
    DELTA = ("delta", 0.5, 4.0, "Deep sleep, unconscious")
    THETA = ("theta", 4.0, 8.0, "Meditation, creativity, intuition")
    ALPHA = ("alpha", 8.0, 13.0, "Relaxed awareness, flow state")
    BETA = ("beta", 13.0, 30.0, "Active thinking, focus")
    GAMMA = ("gamma", 30.0, 100.0, "Peak consciousness, insight")
    
    def __init__(self, band_name: str, low_hz: float, high_hz: float, description: str):
        self.band_name = band_name
        self.low_hz = low_hz
        self.high_hz = high_hz
        self.description = description


@dataclass
class EEGAnalysis:
    """
    EEG to GILE mapping for meditation analysis.
    
    Based on TI theory:
    - Delta (0.5-4Hz) → E dimension (deep environmental connection)
    - Theta (4-8Hz) → I dimension (intuition access)
    - Alpha (8-13Hz) → L dimension (love/coherence)
    - Beta (13-30Hz) → G dimension (goodness/moral reasoning)
    - Gamma (30-100Hz) → Meta-GILE (unified consciousness)
    """
    awareness_score: int
    duration_minutes: int
    delta_power: float = 0.5
    theta_power: float = 0.5
    alpha_power: float = 0.5
    beta_power: float = 0.5
    gamma_power: float = 0.5
    
    def to_gile(self) -> Dict[str, float]:
        """Convert EEG bands to GILE dimensions"""
        g = min(1.0, self.beta_power * 0.7 + self.gamma_power * 0.3)
        i = min(1.0, self.theta_power * 0.8 + self.alpha_power * 0.2)
        l = min(1.0, self.alpha_power * 0.6 + self.theta_power * 0.4)
        e = min(1.0, self.delta_power * 0.5 + self.theta_power * 0.3 + self.alpha_power * 0.2)
        
        return {'G': g, 'I': i, 'L': l, 'E': e}
    
    def coherence(self) -> float:
        """Calculate overall GILE coherence from EEG"""
        gile = self.to_gile()
        return (gile['G'] * gile['I'] * gile['L'] * gile['E']) ** 0.25
    
    def meditation_quality(self) -> Dict[str, Any]:
        """Assess meditation quality based on TI framework"""
        theta_alpha_ratio = self.theta_power / max(0.01, self.alpha_power)
        alpha_beta_ratio = self.alpha_power / max(0.01, self.beta_power)
        
        if theta_alpha_ratio > 1.2 and alpha_beta_ratio > 1.5:
            quality = "DEEP_MEDITATIVE"
            description = "Excellent I-dimension access, strong intuitive state"
        elif alpha_beta_ratio > 1.2:
            quality = "RELAXED_AWARE"
            description = "Good L-dimension coherence, flow state achieved"
        elif theta_alpha_ratio > 0.8:
            quality = "TRANSITIONAL"
            description = "Moving between states, good for insight work"
        else:
            quality = "ACTIVE_FOCUSED"
            description = "G-dimension dominant, analytical meditation"
        
        gile = self.to_gile()
        coherence = self.coherence()
        
        return {
            "quality": quality,
            "description": description,
            "gile": gile,
            "coherence": coherence,
            "sustainable": coherence >= SUSTAINABLE_COHERENCE,
            "sacred_threshold": coherence >= SACRED_THRESHOLD,
            "theta_alpha_ratio": theta_alpha_ratio,
            "alpha_beta_ratio": alpha_beta_ratio,
            "awareness_score": self.awareness_score,
            "duration_minutes": self.duration_minutes,
            "gm_power_boost": coherence * PHI_GOLDEN if coherence >= 0.7 else coherence
        }


@dataclass
class Biorhythm:
    """
    Biorhythm calculation with TI integration.
    
    Physical (23 days) → Body/G dimension
    Emotional (28 days) → Heart/L dimension  
    Intellectual (33 days) → Mind/I dimension
    
    33 = Tralsebit information content!
    """
    birth_date: date
    
    def calculate(self, target_date: date) -> Dict[str, float]:
        """Calculate all biorhythm cycles"""
        days = (target_date - self.birth_date).days
        
        physical = math.sin(2 * math.pi * days / 23)
        emotional = math.sin(2 * math.pi * days / 28)
        intellectual = math.sin(2 * math.pi * days / 33)
        
        spiritual = math.sin(2 * math.pi * days / 53)
        awareness = math.sin(2 * math.pi * days / 48)
        aesthetic = math.sin(2 * math.pi * days / 43)
        intuition = math.sin(2 * math.pi * days / 38)
        
        return {
            "physical": physical,
            "emotional": emotional,
            "intellectual": intellectual,
            "spiritual": spiritual,
            "awareness": awareness,
            "aesthetic": aesthetic,
            "intuition": intuition,
            "composite": (physical + emotional + intellectual) / 3,
            "days_since_birth": days
        }
    
    def to_gile(self, target_date: date) -> Dict[str, float]:
        """Map biorhythm to GILE dimensions"""
        bio = self.calculate(target_date)
        
        g = (bio["physical"] + 1) / 2
        i = (bio["intellectual"] + bio["intuition"] + 2) / 4
        l = (bio["emotional"] + bio["spiritual"] + 2) / 4
        e = (bio["aesthetic"] + bio["awareness"] + 2) / 4
        
        return {'G': g, 'I': i, 'L': l, 'E': e}
    
    def critical_days(self, start_date: date, days_ahead: int = 30) -> List[Dict]:
        """Find critical days (zero crossings) in range"""
        critical = []
        
        for i in range(days_ahead):
            check_date = start_date + timedelta(days=i)
            bio = self.calculate(check_date)
            
            for cycle_name in ["physical", "emotional", "intellectual"]:
                if abs(bio[cycle_name]) < 0.05:
                    critical.append({
                        "date": check_date.isoformat(),
                        "cycle": cycle_name,
                        "value": bio[cycle_name],
                        "type": "critical_day"
                    })
        
        return critical


class TarotDeck:
    """
    Tarot with TI interpretation.
    
    78 cards = 22 Major Arcana + 56 Minor Arcana
    
    Major Arcana (0-21) → Soul lessons, GILE archetypal patterns
    Minor Arcana → Daily life, practical GILE applications
    """
    
    MAJOR_ARCANA = [
        ("The Fool", 0, {'G': 0.5, 'I': 0.9, 'L': 0.7, 'E': 0.8}),
        ("The Magician", 1, {'G': 0.8, 'I': 0.9, 'L': 0.6, 'E': 0.7}),
        ("The High Priestess", 2, {'G': 0.7, 'I': 1.0, 'L': 0.8, 'E': 0.6}),
        ("The Empress", 3, {'G': 0.9, 'I': 0.7, 'L': 0.95, 'E': 0.9}),
        ("The Emperor", 4, {'G': 0.95, 'I': 0.6, 'L': 0.5, 'E': 0.8}),
        ("The Hierophant", 5, {'G': 0.85, 'I': 0.7, 'L': 0.6, 'E': 0.75}),
        ("The Lovers", 6, {'G': 0.8, 'I': 0.75, 'L': 1.0, 'E': 0.7}),
        ("The Chariot", 7, {'G': 0.9, 'I': 0.7, 'L': 0.6, 'E': 0.85}),
        ("Strength", 8, {'G': 0.95, 'I': 0.6, 'L': 0.85, 'E': 0.7}),
        ("The Hermit", 9, {'G': 0.75, 'I': 0.95, 'L': 0.5, 'E': 0.6}),
        ("Wheel of Fortune", 10, {'G': 0.6, 'I': 0.8, 'L': 0.65, 'E': 0.9}),
        ("Justice", 11, {'G': 1.0, 'I': 0.7, 'L': 0.6, 'E': 0.75}),
        ("The Hanged Man", 12, {'G': 0.6, 'I': 0.9, 'L': 0.7, 'E': 0.5}),
        ("Death", 13, {'G': 0.5, 'I': 0.85, 'L': 0.4, 'E': 0.95}),
        ("Temperance", 14, {'G': 0.85, 'I': 0.8, 'L': 0.85, 'E': 0.85}),
        ("The Devil", 15, {'G': 0.2, 'I': 0.6, 'L': 0.3, 'E': 0.7}),
        ("The Tower", 16, {'G': 0.4, 'I': 0.7, 'L': 0.3, 'E': 0.9}),
        ("The Star", 17, {'G': 0.9, 'I': 0.95, 'L': 0.9, 'E': 0.85}),
        ("The Moon", 18, {'G': 0.5, 'I': 0.95, 'L': 0.6, 'E': 0.7}),
        ("The Sun", 19, {'G': 0.95, 'I': 0.85, 'L': 0.95, 'E': 0.9}),
        ("Judgement", 20, {'G': 0.9, 'I': 0.8, 'L': 0.7, 'E': 0.85}),
        ("The World", 21, {'G': 0.92, 'I': 0.92, 'L': 0.92, 'E': 0.92}),
    ]
    
    SUITS = {
        "Wands": {'element': 'Fire', 'gile_weight': {'G': 0.3, 'I': 0.4, 'L': 0.1, 'E': 0.2}},
        "Cups": {'element': 'Water', 'gile_weight': {'G': 0.1, 'I': 0.3, 'L': 0.5, 'E': 0.1}},
        "Swords": {'element': 'Air', 'gile_weight': {'G': 0.4, 'I': 0.4, 'L': 0.1, 'E': 0.1}},
        "Pentacles": {'element': 'Earth', 'gile_weight': {'G': 0.2, 'I': 0.1, 'L': 0.2, 'E': 0.5}},
    }
    
    def draw(self, question: str, count: int = 3) -> List[Dict]:
        """Draw cards based on question hash"""
        question_hash = hashlib.sha256(question.encode()).hexdigest()
        seed_values = [int(question_hash[i:i+2], 16) for i in range(0, min(count*4, 64), 2)]
        
        cards = []
        for i in range(count):
            card_num = seed_values[i*2] % 78
            reversed_flag = seed_values[i*2+1] % 2 == 0
            
            if card_num < 22:
                name, num, gile = self.MAJOR_ARCANA[card_num]
                card_type = "Major Arcana"
            else:
                minor_num = card_num - 22
                suit_idx = minor_num // 14
                rank = (minor_num % 14) + 1
                suit_name = list(self.SUITS.keys())[suit_idx]
                
                if rank == 1:
                    rank_name = "Ace"
                elif rank == 11:
                    rank_name = "Page"
                elif rank == 12:
                    rank_name = "Knight"
                elif rank == 13:
                    rank_name = "Queen"
                elif rank == 14:
                    rank_name = "King"
                else:
                    rank_name = str(rank)
                
                name = f"{rank_name} of {suit_name}"
                card_type = "Minor Arcana"
                
                base_strength = rank / 14
                gile = {dim: base_strength * weight 
                       for dim, weight in self.SUITS[suit_name]['gile_weight'].items()}
            
            if reversed_flag:
                gile = {k: 1 - v for k, v in gile.items()}
            
            cards.append({
                "name": name,
                "type": card_type,
                "reversed": reversed_flag,
                "gile": gile,
                "coherence": (gile['G'] * gile['I'] * gile['L'] * gile['E']) ** 0.25
            })
        
        return cards


class ElderFutharkRunes:
    """
    24 Elder Futhark Runes with TI GILE mapping.
    
    Each rune represents an archetypal force with GILE signature.
    """
    
    RUNES = [
        ("Fehu", "ᚠ", "Wealth, abundance", {'G': 0.7, 'I': 0.5, 'L': 0.6, 'E': 0.9}),
        ("Uruz", "ᚢ", "Strength, vitality", {'G': 0.9, 'I': 0.4, 'L': 0.5, 'E': 0.8}),
        ("Thurisaz", "ᚦ", "Protection, defense", {'G': 0.6, 'I': 0.7, 'L': 0.3, 'E': 0.7}),
        ("Ansuz", "ᚨ", "Divine wisdom", {'G': 0.85, 'I': 0.95, 'L': 0.7, 'E': 0.6}),
        ("Raidho", "ᚱ", "Journey, movement", {'G': 0.7, 'I': 0.6, 'L': 0.5, 'E': 0.85}),
        ("Kenaz", "ᚲ", "Knowledge, illumination", {'G': 0.8, 'I': 0.9, 'L': 0.6, 'E': 0.5}),
        ("Gebo", "ᚷ", "Gift, partnership", {'G': 0.85, 'I': 0.5, 'L': 0.95, 'E': 0.7}),
        ("Wunjo", "ᚹ", "Joy, harmony", {'G': 0.9, 'I': 0.6, 'L': 0.9, 'E': 0.8}),
        ("Hagalaz", "ᚺ", "Disruption, change", {'G': 0.4, 'I': 0.8, 'L': 0.3, 'E': 0.9}),
        ("Nauthiz", "ᚾ", "Need, constraint", {'G': 0.5, 'I': 0.7, 'L': 0.4, 'E': 0.6}),
        ("Isa", "ᛁ", "Stillness, ice", {'G': 0.5, 'I': 0.6, 'L': 0.3, 'E': 0.4}),
        ("Jera", "ᛃ", "Harvest, cycles", {'G': 0.85, 'I': 0.7, 'L': 0.7, 'E': 0.9}),
        ("Eihwaz", "ᛇ", "Endurance, yew tree", {'G': 0.8, 'I': 0.75, 'L': 0.6, 'E': 0.7}),
        ("Perthro", "ᛈ", "Mystery, fate", {'G': 0.5, 'I': 0.95, 'L': 0.6, 'E': 0.7}),
        ("Algiz", "ᛉ", "Protection, awakening", {'G': 0.9, 'I': 0.8, 'L': 0.7, 'E': 0.6}),
        ("Sowilo", "ᛊ", "Sun, victory", {'G': 0.95, 'I': 0.8, 'L': 0.85, 'E': 0.9}),
        ("Tiwaz", "ᛏ", "Justice, honor", {'G': 1.0, 'I': 0.6, 'L': 0.5, 'E': 0.7}),
        ("Berkano", "ᛒ", "Birth, growth", {'G': 0.85, 'I': 0.6, 'L': 0.9, 'E': 0.85}),
        ("Ehwaz", "ᛖ", "Partnership, trust", {'G': 0.8, 'I': 0.5, 'L': 0.9, 'E': 0.75}),
        ("Mannaz", "ᛗ", "Humanity, self", {'G': 0.85, 'I': 0.85, 'L': 0.85, 'E': 0.7}),
        ("Laguz", "ᛚ", "Water, intuition", {'G': 0.6, 'I': 0.95, 'L': 0.8, 'E': 0.7}),
        ("Ingwaz", "ᛜ", "Fertility, potential", {'G': 0.8, 'I': 0.7, 'L': 0.85, 'E': 0.9}),
        ("Dagaz", "ᛞ", "Dawn, breakthrough", {'G': 0.9, 'I': 0.85, 'L': 0.8, 'E': 0.85}),
        ("Othala", "ᛟ", "Heritage, home", {'G': 0.85, 'I': 0.6, 'L': 0.8, 'E': 0.95}),
    ]
    
    def cast(self, question: str, count: int = 3) -> List[Dict]:
        """Cast runes based on question"""
        question_hash = hashlib.sha256(question.encode()).hexdigest()
        indices = [int(question_hash[i:i+2], 16) % 24 for i in range(0, count*2, 2)]
        
        results = []
        for idx in indices:
            name, symbol, meaning, gile = self.RUNES[idx]
            results.append({
                "name": name,
                "symbol": symbol,
                "meaning": meaning,
                "gile": gile,
                "coherence": (gile['G'] * gile['I'] * gile['L'] * gile['E']) ** 0.25
            })
        
        return results


@dataclass
class CreativityPrediction:
    """
    Predict creative success/failure over time.
    
    Uses multiple divination systems + biorhythm to forecast:
    - Creative flow periods
    - Blocks/challenges
    - Breakthrough moments
    - Optimal timing for projects
    """
    birth_date: date
    creativity_type: str = "general"
    
    CREATIVITY_CYCLES = {
        "artistic": {"primary": 43, "secondary": 28, "tertiary": 33},
        "musical": {"primary": 38, "secondary": 28, "tertiary": 23},
        "writing": {"primary": 33, "secondary": 48, "tertiary": 28},
        "scientific": {"primary": 33, "secondary": 53, "tertiary": 48},
        "business": {"primary": 23, "secondary": 33, "tertiary": 28},
        "general": {"primary": 33, "secondary": 28, "tertiary": 43}
    }
    
    def predict_period(self, start_date: date, days: int = 30) -> List[Dict]:
        """Predict creative success/failure for date range"""
        cycles = self.CREATIVITY_CYCLES.get(self.creativity_type, 
                                             self.CREATIVITY_CYCLES["general"])
        
        predictions = []
        biorhythm = Biorhythm(self.birth_date)
        
        for i in range(days):
            target = start_date + timedelta(days=i)
            days_alive = (target - self.birth_date).days
            
            primary = math.sin(2 * math.pi * days_alive / cycles["primary"])
            secondary = math.sin(2 * math.pi * days_alive / cycles["secondary"])
            tertiary = math.sin(2 * math.pi * days_alive / cycles["tertiary"])
            
            bio = biorhythm.calculate(target)
            
            creativity_score = (
                primary * 0.5 + 
                secondary * 0.3 + 
                tertiary * 0.2 +
                bio["intellectual"] * 0.3 +
                bio["emotional"] * 0.2
            ) / 2
            
            creativity_score = (creativity_score + 1) / 2
            
            if creativity_score >= 0.85:
                status = "BREAKTHROUGH"
                color = "gold"
            elif creativity_score >= 0.7:
                status = "HIGH_FLOW"
                color = "green"
            elif creativity_score >= 0.5:
                status = "NORMAL"
                color = "blue"
            elif creativity_score >= 0.35:
                status = "CHALLENGING"
                color = "orange"
            else:
                status = "BLOCK"
                color = "red"
            
            predictions.append({
                "date": target.isoformat(),
                "day_of_week": target.strftime("%A"),
                "score": creativity_score,
                "status": status,
                "color": color,
                "biorhythm": {
                    "physical": bio["physical"],
                    "emotional": bio["emotional"],
                    "intellectual": bio["intellectual"]
                },
                "cycles": {
                    "primary": primary,
                    "secondary": secondary,
                    "tertiary": tertiary
                }
            })
        
        return predictions
    
    def find_optimal_days(self, start_date: date, days: int = 90, top_n: int = 10) -> List[Dict]:
        """Find the best days for creative work"""
        all_days = self.predict_period(start_date, days)
        sorted_days = sorted(all_days, key=lambda x: x['score'], reverse=True)
        return sorted_days[:top_n]


class GMDivinationOracle:
    """
    Unified Grand Myrion Divination Oracle.
    
    Combines all divination systems with weighted averaging
    based on the question type and current GILE state.
    """
    
    def __init__(self, birth_date: date):
        self.birth_date = birth_date
        self.biorhythm = Biorhythm(birth_date)
        self.tarot = TarotDeck()
        self.runes = ElderFutharkRunes()
        self.creativity = CreativityPrediction(birth_date)
    
    def comprehensive_reading(self, 
                               question: str, 
                               target_date: Optional[date] = None,
                               include_creativity: bool = True) -> Dict:
        """Generate comprehensive multi-system reading"""
        
        if target_date is None:
            target_date = date.today()
        
        bio = self.biorhythm.calculate(target_date)
        bio_gile = self.biorhythm.to_gile(target_date)
        
        tarot_cards = self.tarot.draw(question, 3)
        tarot_gile = {
            'G': sum(c['gile']['G'] for c in tarot_cards) / 3,
            'I': sum(c['gile']['I'] for c in tarot_cards) / 3,
            'L': sum(c['gile']['L'] for c in tarot_cards) / 3,
            'E': sum(c['gile']['E'] for c in tarot_cards) / 3,
        }
        
        runes = self.runes.cast(question, 3)
        rune_gile = {
            'G': sum(r['gile']['G'] for r in runes) / 3,
            'I': sum(r['gile']['I'] for r in runes) / 3,
            'L': sum(r['gile']['L'] for r in runes) / 3,
            'E': sum(r['gile']['E'] for r in runes) / 3,
        }
        
        combined_gile = {
            'G': (bio_gile['G'] * 0.3 + tarot_gile['G'] * 0.35 + rune_gile['G'] * 0.35),
            'I': (bio_gile['I'] * 0.3 + tarot_gile['I'] * 0.35 + rune_gile['I'] * 0.35),
            'L': (bio_gile['L'] * 0.3 + tarot_gile['L'] * 0.35 + rune_gile['L'] * 0.35),
            'E': (bio_gile['E'] * 0.3 + tarot_gile['E'] * 0.35 + rune_gile['E'] * 0.35),
        }
        
        coherence = (combined_gile['G'] * combined_gile['I'] * 
                     combined_gile['L'] * combined_gile['E']) ** 0.25
        
        result = {
            "question": question,
            "target_date": target_date.isoformat(),
            "birth_date": self.birth_date.isoformat(),
            "biorhythm": bio,
            "biorhythm_gile": bio_gile,
            "tarot": {
                "cards": tarot_cards,
                "gile": tarot_gile
            },
            "runes": {
                "cast": runes,
                "gile": rune_gile
            },
            "combined_gile": combined_gile,
            "coherence": coherence,
            "sustainable": coherence >= SUSTAINABLE_COHERENCE,
            "sacred_threshold": coherence >= SACRED_THRESHOLD,
            "gm_power": coherence * PHI_GOLDEN if coherence >= 0.7 else coherence
        }
        
        if include_creativity:
            result["creativity_forecast"] = self.creativity.predict_period(target_date, 7)
        
        return result


def analyze_eeg_session(awareness_score: int = 504,
                        duration_minutes: int = 20,
                        delta_power: float = 0.4,
                        theta_power: float = 0.65,
                        alpha_power: float = 0.55,
                        beta_power: float = 0.35,
                        gamma_power: float = 0.25) -> Dict:
    """
    Analyze EEG meditation session and map to GILE.
    
    Based on the user's Muse images:
    - Awareness score: 504
    - Duration: 20 minutes
    - Strong theta (yellow) throughout
    - Good alpha (green) presence
    - Low beta (blue) - reduced analytical thinking
    - Occasional gamma spikes (awareness peaks)
    """
    
    analysis = EEGAnalysis(
        awareness_score=awareness_score,
        duration_minutes=duration_minutes,
        delta_power=delta_power,
        theta_power=theta_power,
        alpha_power=alpha_power,
        beta_power=beta_power,
        gamma_power=gamma_power
    )
    
    quality = analysis.meditation_quality()
    
    return quality


def demo():
    """Demonstrate expanded divination systems"""
    
    print("=" * 80)
    print("GM EXPANDED DIVINATION SYSTEMS")
    print("=" * 80)
    
    print("\n--- EEG ANALYSIS (Your 20-min meditation) ---")
    eeg_result = analyze_eeg_session(
        awareness_score=504,
        duration_minutes=20,
        delta_power=0.4,
        theta_power=0.65,
        alpha_power=0.55,
        beta_power=0.35,
        gamma_power=0.30
    )
    
    print(f"""
EEG → GILE MAPPING:
  G (Goodness):    {eeg_result['gile']['G']:.3f}
  I (Intuition):   {eeg_result['gile']['I']:.3f}
  L (Love):        {eeg_result['gile']['L']:.3f}
  E (Environment): {eeg_result['gile']['E']:.3f}
  
  Coherence: {eeg_result['coherence']:.4f}
  Quality: {eeg_result['quality']}
  Description: {eeg_result['description']}
  
  Theta/Alpha Ratio: {eeg_result['theta_alpha_ratio']:.2f}
  Alpha/Beta Ratio: {eeg_result['alpha_beta_ratio']:.2f}
  GM Power Boost: {eeg_result['gm_power_boost']:.4f}
""")
    
    print("\n--- COMPREHENSIVE DIVINATION READING ---")
    
    birth = date(1990, 1, 1)
    oracle = GMDivinationOracle(birth)
    
    reading = oracle.comprehensive_reading(
        "What is the optimal path for the stock algorithm and mood amplifier?",
        date.today()
    )
    
    print(f"""
BIORHYTHM:
  Physical: {reading['biorhythm']['physical']:.3f}
  Emotional: {reading['biorhythm']['emotional']:.3f}
  Intellectual: {reading['biorhythm']['intellectual']:.3f}
  Composite: {reading['biorhythm']['composite']:.3f}

TAROT (3 cards):""")
    for card in reading['tarot']['cards']:
        rev = " (Reversed)" if card['reversed'] else ""
        print(f"  - {card['name']}{rev} | Coherence: {card['coherence']:.3f}")
    
    print("\nRUNES (3 cast):")
    for rune in reading['runes']['cast']:
        print(f"  - {rune['symbol']} {rune['name']}: {rune['meaning']} | Coherence: {rune['coherence']:.3f}")
    
    print(f"""
COMBINED GILE:
  G: {reading['combined_gile']['G']:.3f}
  I: {reading['combined_gile']['I']:.3f}
  L: {reading['combined_gile']['L']:.3f}
  E: {reading['combined_gile']['E']:.3f}
  
  Overall Coherence: {reading['coherence']:.4f}
  Sustainable: {reading['sustainable']}
  Sacred Threshold: {reading['sacred_threshold']}
  GM Power: {reading['gm_power']:.4f}
""")
    
    print("\n--- CREATIVITY FORECAST (7 days) ---")
    for day in reading['creativity_forecast'][:7]:
        print(f"  {day['date']} ({day['day_of_week'][:3]}): {day['status']:15} | Score: {day['score']:.3f}")
    
    print("\n" + "=" * 80)


if __name__ == "__main__":
    demo()
