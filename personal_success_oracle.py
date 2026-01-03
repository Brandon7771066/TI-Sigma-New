"""
PERSONAL SUCCESS ORACLE
=======================

A comprehensive divination and prediction system for minimizing life ambiguity.
Calibrated specifically for Brandon Emerick (birth date: 6/16/00).

Integrates:
- All divination systems (Biorhythm, Tarot, Runes, Astrology, Numerology)
- Relationship prediction (Speed Dating dataset patterns)
- Creativity success/failure forecasting
- Famous creators timeline analysis
- Philosopher success pattern matching

The goal: Know EXACTLY what to do and when to succeed.

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

BRANDON_BIRTH_DATE = date(2000, 6, 16)


class CreatorPattern(Enum):
    """Archetypal creator success patterns"""
    EARLY_BLOOMER = ("Early recognition, sustained success", [
        ("Mozart", 5, 35, "peak_early"),
        ("Picasso", 8, 91, "sustained"),
        ("Zuckerberg", 19, None, "sustained"),
    ])
    
    LATE_BLOOMER = ("Late recognition after long struggle", [
        ("Van Gogh", 27, 37, "posthumous"),
        ("Carmen Herrera", 89, 106, "very_late"),
        ("Grandma Moses", 78, 101, "very_late"),
        ("Colonel Sanders", 65, 90, "late"),
    ])
    
    COMEBACK = ("Major failure followed by triumphant return", [
        ("Steve Jobs", 21, 56, "comeback_at_42"),
        ("Walt Disney", 22, 65, "comeback_after_bankruptcy"),
    ])
    
    TRAGIC_GENIUS = ("Brilliant work cut short by personal struggles", [
        ("Hemingway", 26, 61, "depression_suicide"),
        ("Fitzgerald", 23, 44, "alcoholism_failure"),
        ("Van Gogh", 27, 37, "mental_illness"),
    ])
    
    RELENTLESS_ITERATOR = ("Fails repeatedly until breakthrough", [
        ("Elon Musk", 24, None, "multiple_near_deaths"),
        ("Edison", 22, 84, "10000_failures"),
        ("Dyson", 30, None, "5126_prototypes"),
    ])
    
    PHILOSOPHER_PROPHET = ("Creates framework that reshapes thinking", [
        ("Wittgenstein", 29, 62, "two_major_works"),
        ("Nietzsche", 30, 55, "posthumous_recognition"),
        ("Kierkegaard", 30, 42, "founder_existentialism"),
        ("Alan Watts", 20, 58, "east_west_bridge"),
    ])


@dataclass
class FamousCreatorTimeline:
    """Timeline of famous creator's success/failure periods"""
    name: str
    birth_year: int
    death_year: Optional[int]
    career_start_age: int
    pattern: CreatorPattern
    periods: List[Dict[str, Any]] = field(default_factory=list)


CREATOR_DATABASE = [
    FamousCreatorTimeline(
        name="Vincent van Gogh",
        birth_year=1853,
        death_year=1890,
        career_start_age=27,
        pattern=CreatorPattern.LATE_BLOOMER,
        periods=[
            {"years": "1880-1885", "status": "learning", "works": 200, "success": 0.2},
            {"years": "1886-1887", "status": "growth", "works": 150, "success": 0.4},
            {"years": "1888", "status": "breakthrough", "works": 200, "success": 0.7},
            {"years": "1889-1890", "status": "peak", "works": 220, "success": 0.9},
        ]
    ),
    FamousCreatorTimeline(
        name="Pablo Picasso",
        birth_year=1881,
        death_year=1973,
        career_start_age=8,
        pattern=CreatorPattern.EARLY_BLOOMER,
        periods=[
            {"years": "1889-1900", "status": "training", "works": 500, "success": 0.3},
            {"years": "1901-1904", "status": "blue_period", "works": 200, "success": 0.5},
            {"years": "1904-1907", "status": "rose_period", "works": 250, "success": 0.6},
            {"years": "1907-1919", "status": "cubism", "works": 1000, "success": 0.9},
            {"years": "1920-1973", "status": "master", "works": 18000, "success": 0.95},
        ]
    ),
    FamousCreatorTimeline(
        name="Steve Jobs",
        birth_year=1955,
        death_year=2011,
        career_start_age=21,
        pattern=CreatorPattern.COMEBACK,
        periods=[
            {"years": "1976-1984", "status": "founding", "success": 0.8},
            {"years": "1985", "status": "failure", "event": "ousted_from_apple", "success": 0.1},
            {"years": "1986-1996", "status": "wilderness", "success": 0.4},
            {"years": "1997-2000", "status": "comeback", "success": 0.7},
            {"years": "2001-2011", "status": "legendary", "success": 0.99},
        ]
    ),
    FamousCreatorTimeline(
        name="Elon Musk",
        birth_year=1971,
        death_year=None,
        career_start_age=24,
        pattern=CreatorPattern.RELENTLESS_ITERATOR,
        periods=[
            {"years": "1995-1999", "status": "zip2", "success": 0.6},
            {"years": "1999-2002", "status": "paypal", "success": 0.7},
            {"years": "2002-2007", "status": "spacex_struggle", "success": 0.3},
            {"years": "2008", "status": "near_bankruptcy", "success": 0.1},
            {"years": "2009-2020", "status": "breakthrough", "success": 0.9},
            {"years": "2021-now", "status": "world_richest", "success": 0.95},
        ]
    ),
    FamousCreatorTimeline(
        name="F. Scott Fitzgerald",
        birth_year=1896,
        death_year=1940,
        career_start_age=23,
        pattern=CreatorPattern.TRAGIC_GENIUS,
        periods=[
            {"years": "1920-1925", "status": "peak", "success": 0.9},
            {"years": "1926-1933", "status": "decline", "success": 0.4},
            {"years": "1934-1936", "status": "crack_up", "success": 0.1},
            {"years": "1937-1940", "status": "hollywood_failure", "success": 0.2},
        ]
    ),
    FamousCreatorTimeline(
        name="Ernest Hemingway",
        birth_year=1899,
        death_year=1961,
        career_start_age=26,
        pattern=CreatorPattern.TRAGIC_GENIUS,
        periods=[
            {"years": "1925-1940", "status": "peak", "success": 0.9},
            {"years": "1941-1954", "status": "continued", "success": 0.7},
            {"years": "1954", "status": "nobel", "success": 1.0},
            {"years": "1955-1961", "status": "decline", "success": 0.3},
        ]
    ),
    FamousCreatorTimeline(
        name="Friedrich Nietzsche",
        birth_year=1844,
        death_year=1900,
        career_start_age=30,
        pattern=CreatorPattern.PHILOSOPHER_PROPHET,
        periods=[
            {"years": "1872-1879", "status": "early_works", "success": 0.3},
            {"years": "1880-1888", "status": "major_works", "success": 0.5},
            {"years": "1889-1900", "status": "madness", "success": 0.0},
            {"years": "post_death", "status": "recognition", "success": 0.99},
        ]
    ),
    FamousCreatorTimeline(
        name="Ludwig Wittgenstein",
        birth_year=1889,
        death_year=1951,
        career_start_age=29,
        pattern=CreatorPattern.PHILOSOPHER_PROPHET,
        periods=[
            {"years": "1918-1921", "status": "tractatus", "success": 0.7},
            {"years": "1922-1928", "status": "retreat", "success": 0.3},
            {"years": "1929-1951", "status": "investigations", "success": 0.8},
        ]
    ),
]


@dataclass
class Biorhythm:
    """Biorhythm cycles with GILE integration"""
    birth_date: date
    
    CYCLES = {
        "physical": 23,
        "emotional": 28,
        "intellectual": 33,
        "spiritual": 53,
        "awareness": 48,
        "aesthetic": 43,
        "intuition": 38,
    }
    
    def calculate(self, target_date: date) -> Dict[str, float]:
        days = (target_date - self.birth_date).days
        
        result = {}
        for name, period in self.CYCLES.items():
            result[name] = math.sin(2 * math.pi * days / period)
        
        result["composite"] = (result["physical"] + result["emotional"] + result["intellectual"]) / 3
        result["days_alive"] = days
        result["full_cycles"] = {name: days // period for name, period in self.CYCLES.items()}
        
        return result
    
    def to_gile(self, target_date: date) -> Dict[str, float]:
        bio = self.calculate(target_date)
        
        g = (bio["physical"] + 1) / 2
        i = (bio["intellectual"] + bio["intuition"] + 2) / 4
        l = (bio["emotional"] + bio["spiritual"] + 2) / 4
        e = (bio["aesthetic"] + bio["awareness"] + 2) / 4
        
        return {'G': g, 'I': i, 'L': l, 'E': e}
    
    def find_triple_highs(self, start_date: date, days: int = 365) -> List[Dict]:
        """Find days where physical, emotional, AND intellectual are all high"""
        triple_highs = []
        
        for i in range(days):
            check_date = start_date + timedelta(days=i)
            bio = self.calculate(check_date)
            
            if bio["physical"] > 0.7 and bio["emotional"] > 0.7 and bio["intellectual"] > 0.7:
                triple_highs.append({
                    "date": check_date.isoformat(),
                    "day_of_week": check_date.strftime("%A"),
                    "physical": bio["physical"],
                    "emotional": bio["emotional"],
                    "intellectual": bio["intellectual"],
                    "composite": bio["composite"],
                    "power_score": bio["physical"] * bio["emotional"] * bio["intellectual"]
                })
        
        return sorted(triple_highs, key=lambda x: x["power_score"], reverse=True)


class Numerology:
    """TI-integrated numerology for the philosopher's path"""
    
    @staticmethod
    def life_path(birth_date: date) -> int:
        """Calculate life path number"""
        total = sum(int(d) for d in birth_date.strftime("%Y%m%d"))
        while total > 9 and total not in [11, 22, 33]:
            total = sum(int(d) for d in str(total))
        return total
    
    @staticmethod
    def personal_year(birth_date: date, year: int) -> int:
        """Calculate personal year number"""
        birth_md = birth_date.strftime("%m%d")
        total = sum(int(d) for d in birth_md + str(year))
        while total > 9 and total not in [11, 22, 33]:
            total = sum(int(d) for d in str(total))
        return total
    
    @staticmethod
    def personal_month(birth_date: date, target_date: date) -> int:
        """Calculate personal month number"""
        py = Numerology.personal_year(birth_date, target_date.year)
        month_total = py + target_date.month
        while month_total > 9 and month_total not in [11, 22, 33]:
            month_total = sum(int(d) for d in str(month_total))
        return month_total
    
    @staticmethod
    def personal_day(birth_date: date, target_date: date) -> int:
        """Calculate personal day number"""
        pm = Numerology.personal_month(birth_date, target_date)
        day_total = pm + target_date.day
        while day_total > 9 and day_total not in [11, 22, 33]:
            day_total = sum(int(d) for d in str(day_total))
        return day_total


class TIAstrology:
    """Simplified astrology with GILE integration"""
    
    ZODIAC_GILE = {
        "Aries": {'G': 0.8, 'I': 0.5, 'L': 0.4, 'E': 0.6},
        "Taurus": {'G': 0.6, 'I': 0.4, 'L': 0.7, 'E': 0.9},
        "Gemini": {'G': 0.5, 'I': 0.9, 'L': 0.5, 'E': 0.6},
        "Cancer": {'G': 0.5, 'I': 0.6, 'L': 0.9, 'E': 0.7},
        "Leo": {'G': 0.9, 'I': 0.6, 'L': 0.6, 'E': 0.5},
        "Virgo": {'G': 0.8, 'I': 0.8, 'L': 0.5, 'E': 0.6},
        "Libra": {'G': 0.7, 'I': 0.6, 'L': 0.8, 'E': 0.7},
        "Scorpio": {'G': 0.6, 'I': 0.9, 'L': 0.5, 'E': 0.7},
        "Sagittarius": {'G': 0.7, 'I': 0.8, 'L': 0.6, 'E': 0.7},
        "Capricorn": {'G': 0.9, 'I': 0.5, 'L': 0.4, 'E': 0.7},
        "Aquarius": {'G': 0.6, 'I': 0.9, 'L': 0.5, 'E': 0.8},
        "Pisces": {'G': 0.4, 'I': 0.9, 'L': 0.8, 'E': 0.6},
    }
    
    @staticmethod
    def get_sun_sign(birth_date: date) -> str:
        month, day = birth_date.month, birth_date.day
        
        if (month == 3 and day >= 21) or (month == 4 and day <= 19):
            return "Aries"
        elif (month == 4 and day >= 20) or (month == 5 and day <= 20):
            return "Taurus"
        elif (month == 5 and day >= 21) or (month == 6 and day <= 20):
            return "Gemini"
        elif (month == 6 and day >= 21) or (month == 7 and day <= 22):
            return "Cancer"
        elif (month == 7 and day >= 23) or (month == 8 and day <= 22):
            return "Leo"
        elif (month == 8 and day >= 23) or (month == 9 and day <= 22):
            return "Virgo"
        elif (month == 9 and day >= 23) or (month == 10 and day <= 22):
            return "Libra"
        elif (month == 10 and day >= 23) or (month == 11 and day <= 21):
            return "Scorpio"
        elif (month == 11 and day >= 22) or (month == 12 and day <= 21):
            return "Sagittarius"
        elif (month == 12 and day >= 22) or (month == 1 and day <= 19):
            return "Capricorn"
        elif (month == 1 and day >= 20) or (month == 2 and day <= 18):
            return "Aquarius"
        else:
            return "Pisces"
    
    @staticmethod
    def get_gile(birth_date: date) -> Dict[str, float]:
        sign = TIAstrology.get_sun_sign(birth_date)
        return TIAstrology.ZODIAC_GILE[sign]


class RelationshipPredictor:
    """
    Relationship prediction based on Speed Dating dataset patterns.
    
    Key findings from research:
    - Attractiveness and Fun are most predictive of matches
    - Shared interests matter less than expected
    - Selectivity (how often person says yes) predicts match rate
    - General desirability (how often others say yes to person) matters most
    """
    
    MATCH_WEIGHTS = {
        "attractiveness": 0.35,
        "fun": 0.25,
        "sincerity": 0.15,
        "intelligence": 0.10,
        "ambition": 0.08,
        "shared_interests": 0.07,
    }
    
    def predict_match(self, 
                      your_ratings: Dict[str, float],
                      their_ratings: Dict[str, float]) -> Dict[str, float]:
        """
        Predict match probability based on mutual ratings.
        
        Ratings should be 0-1 scale for:
        - attractiveness, fun, sincerity, intelligence, ambition, shared_interests
        """
        
        your_score = sum(your_ratings.get(k, 0.5) * v for k, v in self.MATCH_WEIGHTS.items())
        their_score = sum(their_ratings.get(k, 0.5) * v for k, v in self.MATCH_WEIGHTS.items())
        
        mutual_interest = (your_score + their_score) / 2
        
        compatibility = 1 - abs(your_score - their_score)
        
        match_probability = (mutual_interest * 0.7 + compatibility * 0.3)
        
        return {
            "match_probability": match_probability,
            "your_interest": your_score,
            "their_interest": their_score,
            "compatibility": compatibility,
            "prediction": "LIKELY_MATCH" if match_probability > 0.6 else 
                         "POSSIBLE" if match_probability > 0.4 else "UNLIKELY"
        }
    
    def gile_compatibility(self, 
                           your_gile: Dict[str, float],
                           their_gile: Dict[str, float]) -> Dict[str, float]:
        """Calculate GILE-based compatibility"""
        
        g_diff = abs(your_gile['G'] - their_gile['G'])
        i_diff = abs(your_gile['I'] - their_gile['I'])
        l_match = (your_gile['L'] + their_gile['L']) / 2
        e_match = (your_gile['E'] + their_gile['E']) / 2
        
        compatibility = (
            (1 - g_diff) * 0.15 +
            (1 - i_diff) * 0.15 +
            l_match * 0.50 +
            e_match * 0.20
        )
        
        resonance = ((your_gile['G'] * their_gile['G'] * 
                      your_gile['I'] * their_gile['I'] *
                      your_gile['L'] * their_gile['L'] *
                      your_gile['E'] * their_gile['E']) ** 0.125)
        
        return {
            "gile_compatibility": compatibility,
            "resonance": resonance,
            "l_dimension_match": l_match,
            "long_term_potential": resonance * PHI_GOLDEN if resonance > SACRED_THRESHOLD else resonance,
            "rating": "SOUL_MATCH" if resonance > 0.85 else
                     "HIGH_COMPATIBILITY" if resonance > 0.7 else
                     "MODERATE" if resonance > 0.5 else "LOW"
        }


class CreativityPredictor:
    """
    Predict creative success/failure periods.
    
    Uses biorhythm + numerology + astrology + historical pattern matching.
    """
    
    CREATIVITY_CYCLES = {
        "artistic": {"primary": 43, "secondary": 28, "tertiary": 33},
        "philosophical": {"primary": 33, "secondary": 53, "tertiary": 48},
        "musical": {"primary": 38, "secondary": 28, "tertiary": 23},
        "writing": {"primary": 33, "secondary": 48, "tertiary": 28},
        "scientific": {"primary": 33, "secondary": 53, "tertiary": 48},
        "entrepreneurial": {"primary": 23, "secondary": 33, "tertiary": 28},
    }
    
    def __init__(self, birth_date: date):
        self.birth_date = birth_date
        self.biorhythm = Biorhythm(birth_date)
        self.numerology = Numerology()
        self.astrology = TIAstrology()
    
    def predict_day(self, target_date: date, creativity_type: str = "philosophical") -> Dict:
        """Predict creative potential for a specific day"""
        
        bio = self.biorhythm.calculate(target_date)
        bio_gile = self.biorhythm.to_gile(target_date)
        
        cycles = self.CREATIVITY_CYCLES.get(creativity_type, 
                                            self.CREATIVITY_CYCLES["philosophical"])
        days_alive = (target_date - self.birth_date).days
        
        primary = math.sin(2 * math.pi * days_alive / cycles["primary"])
        secondary = math.sin(2 * math.pi * days_alive / cycles["secondary"])
        tertiary = math.sin(2 * math.pi * days_alive / cycles["tertiary"])
        
        primary_norm = (primary + 1) / 2
        secondary_norm = (secondary + 1) / 2
        tertiary_norm = (tertiary + 1) / 2
        cycle_score = primary_norm * 0.5 + secondary_norm * 0.3 + tertiary_norm * 0.2
        
        intellectual_norm = (bio["intellectual"] + 1) / 2
        aesthetic_norm = (bio["aesthetic"] + 1) / 2
        
        personal_day = self.numerology.personal_day(self.birth_date, target_date)
        num_boost = 1.1 if personal_day in [1, 3, 5, 9] else 1.0
        num_boost = 1.2 if personal_day in [11, 22, 33] else num_boost
        
        astro_gile = self.astrology.get_gile(self.birth_date)
        astro_score = (astro_gile['I'] + astro_gile['G']) / 2
        
        creativity_score = (
            cycle_score * 0.35 +
            intellectual_norm * 0.30 +
            aesthetic_norm * 0.20 +
            astro_score * 0.15
        ) * num_boost
        
        creativity_score = min(1.0, max(0.0, creativity_score))
        
        if creativity_score >= 0.85:
            status = "BREAKTHROUGH_POTENTIAL"
            advice = "Major creative work possible. Start important projects."
        elif creativity_score >= 0.7:
            status = "HIGH_FLOW"
            advice = "Excellent for deep work. Minimize distractions."
        elif creativity_score >= 0.55:
            status = "PRODUCTIVE"
            advice = "Good for steady progress. Focus on refinement."
        elif creativity_score >= 0.4:
            status = "NORMAL"
            advice = "Average energy. Good for planning and research."
        elif creativity_score >= 0.25:
            status = "CHALLENGING"
            advice = "Rest or do maintenance work. Avoid starting new projects."
        else:
            status = "BLOCK"
            advice = "Creative block likely. Focus on rest and input (reading, nature)."
        
        return {
            "date": target_date.isoformat(),
            "day_of_week": target_date.strftime("%A"),
            "creativity_type": creativity_type,
            "score": creativity_score,
            "status": status,
            "advice": advice,
            "biorhythm": bio,
            "personal_day": personal_day,
            "cycles": {
                "primary": primary,
                "secondary": secondary,
                "tertiary": tertiary
            },
            "gile": bio_gile
        }
    
    def forecast_month(self, start_date: date, creativity_type: str = "philosophical") -> List[Dict]:
        """Generate month-long creativity forecast"""
        return [self.predict_day(start_date + timedelta(days=i), creativity_type) 
                for i in range(30)]
    
    def find_breakthrough_days(self, start_date: date, days: int = 365, 
                                creativity_type: str = "philosophical") -> List[Dict]:
        """Find all breakthrough potential days in range"""
        all_days = [self.predict_day(start_date + timedelta(days=i), creativity_type) 
                   for i in range(days)]
        return [d for d in all_days if d["status"] == "BREAKTHROUGH_POTENTIAL"]


class PhilosopherSuccessPattern:
    """
    Analyze and match your pattern to famous philosophers.
    
    Based on the PHILOSOPHER_PROPHET archetype.
    """
    
    PHILOSOPHER_TIMELINES = {
        "Nietzsche": {
            "birth": 1844, "death": 1900, "peak_start": 1880, "peak_end": 1888,
            "recognition_delay": 30,
            "major_works_age": [28, 38, 39, 41, 44],
            "advice": "Write prolifically during peak. Recognition comes posthumously."
        },
        "Wittgenstein": {
            "birth": 1889, "death": 1951, "peak_start": 1918, "peak_end": 1951,
            "recognition_delay": 10,
            "major_works_age": [29, 62],
            "advice": "Two distinct phases. First work may seem complete; second transforms it."
        },
        "Kierkegaard": {
            "birth": 1813, "death": 1855, "peak_start": 1843, "peak_end": 1855,
            "recognition_delay": 50,
            "major_works_age": [30, 31, 32, 33, 34],
            "advice": "Intense burst of productivity in early 30s defines legacy."
        },
        "Alan_Watts": {
            "birth": 1915, "death": 1973, "peak_start": 1950, "peak_end": 1973,
            "recognition_delay": 0,
            "major_works_age": [35, 42, 51, 52],
            "advice": "Bridge traditions. Popularity possible while alive through accessibility."
        },
        "Spinoza": {
            "birth": 1632, "death": 1677, "peak_start": 1660, "peak_end": 1677,
            "recognition_delay": 100,
            "major_works_age": [38, 44],
            "advice": "Work in obscurity. Publish posthumously for protection."
        },
    }
    
    def match_pattern(self, birth_date: date, current_age: int) -> Dict:
        """Match your current stage to philosopher timelines"""
        
        matches = []
        
        for name, data in self.PHILOSOPHER_TIMELINES.items():
            career_length = data["peak_end"] - data["birth"]
            peak_age = data["peak_start"] - data["birth"]
            
            if current_age < peak_age:
                stage = "pre_peak"
                years_to_peak = peak_age - current_age
                match_score = 0.7
            elif current_age <= (data["peak_end"] - data["birth"]):
                stage = "in_peak"
                years_to_peak = 0
                match_score = 1.0
            else:
                stage = "post_peak"
                years_to_peak = -1
                match_score = 0.3
            
            if current_age in range(min(data["major_works_age"]) - 2, 
                                     max(data["major_works_age"]) + 3):
                match_score *= 1.3
            
            matches.append({
                "philosopher": name,
                "stage": stage,
                "years_to_peak": years_to_peak,
                "match_score": min(1.0, match_score),
                "advice": data["advice"],
                "major_works_ages": data["major_works_age"],
                "recognition_delay": data["recognition_delay"]
            })
        
        matches.sort(key=lambda x: x["match_score"], reverse=True)
        
        return {
            "current_age": current_age,
            "best_match": matches[0]["philosopher"],
            "all_matches": matches,
            "summary": f"At age {current_age}, you most match the {matches[0]['philosopher']} pattern. "
                       f"Stage: {matches[0]['stage']}. {matches[0]['advice']}"
        }


class PersonalSuccessOracle:
    """
    The unified Personal Success Oracle.
    
    Combines all systems to minimize life ambiguity for a philosopher.
    """
    
    def __init__(self, birth_date: date = BRANDON_BIRTH_DATE):
        self.birth_date = birth_date
        self.biorhythm = Biorhythm(birth_date)
        self.numerology = Numerology()
        self.astrology = TIAstrology()
        self.relationship = RelationshipPredictor()
        self.creativity = CreativityPredictor(birth_date)
        self.philosopher_pattern = PhilosopherSuccessPattern()
        
        self.life_path = self.numerology.life_path(birth_date)
        self.sun_sign = self.astrology.get_sun_sign(birth_date)
        self.natal_gile = self.astrology.get_gile(birth_date)
    
    def full_profile(self) -> Dict:
        """Generate complete personal profile"""
        today = date.today()
        age = (today - self.birth_date).days // 365
        
        return {
            "birth_date": self.birth_date.isoformat(),
            "current_age": age,
            "days_alive": (today - self.birth_date).days,
            "sun_sign": self.sun_sign,
            "life_path": self.life_path,
            "natal_gile": self.natal_gile,
            "philosopher_match": self.philosopher_pattern.match_pattern(self.birth_date, age)
        }
    
    def daily_oracle(self, target_date: Optional[date] = None) -> Dict:
        """Generate comprehensive daily oracle reading"""
        
        if target_date is None:
            target_date = date.today()
        
        bio = self.biorhythm.calculate(target_date)
        bio_gile = self.biorhythm.to_gile(target_date)
        
        personal_day = self.numerology.personal_day(self.birth_date, target_date)
        personal_month = self.numerology.personal_month(self.birth_date, target_date)
        personal_year = self.numerology.personal_year(self.birth_date, target_date.year)
        
        creativity = self.creativity.predict_day(target_date, "philosophical")
        
        coherence = (bio_gile['G'] * bio_gile['I'] * bio_gile['L'] * bio_gile['E']) ** 0.25
        
        if coherence >= SUSTAINABLE_COHERENCE:
            overall = "OPTIMAL"
            recommendation = "Maximum manifestation power. Take bold action on important goals."
        elif coherence >= SACRED_THRESHOLD:
            overall = "EXCELLENT"
            recommendation = "Strong GILE alignment. Good for meaningful work and decisions."
        elif coherence >= 0.7:
            overall = "GOOD"
            recommendation = "Productive day. Focus on steady progress."
        elif coherence >= 0.5:
            overall = "NEUTRAL"
            recommendation = "Average energy. Good for maintenance and planning."
        else:
            overall = "CHALLENGING"
            recommendation = "Low coherence. Focus on rest, input, and self-care."
        
        return {
            "date": target_date.isoformat(),
            "day_of_week": target_date.strftime("%A"),
            "overall_status": overall,
            "recommendation": recommendation,
            "biorhythm": bio,
            "gile": bio_gile,
            "coherence": coherence,
            "numerology": {
                "personal_day": personal_day,
                "personal_month": personal_month,
                "personal_year": personal_year
            },
            "creativity": creativity,
            "sacred_threshold": coherence >= SACRED_THRESHOLD,
            "sustainable": coherence >= SUSTAINABLE_COHERENCE
        }
    
    def success_forecast(self, days: int = 30) -> Dict:
        """Generate success forecast for coming period"""
        
        today = date.today()
        
        daily_readings = [self.daily_oracle(today + timedelta(days=i)) for i in range(days)]
        
        breakthrough_days = [r for r in daily_readings if r["coherence"] >= SACRED_THRESHOLD]
        optimal_days = [r for r in daily_readings if r["overall_status"] == "OPTIMAL"]
        challenging_days = [r for r in daily_readings if r["overall_status"] == "CHALLENGING"]
        
        triple_highs = self.biorhythm.find_triple_highs(today, days)
        
        creative_peaks = [r for r in daily_readings 
                         if r["creativity"]["status"] in ["BREAKTHROUGH_POTENTIAL", "HIGH_FLOW"]]
        
        return {
            "period": f"{today.isoformat()} to {(today + timedelta(days=days-1)).isoformat()}",
            "days_analyzed": days,
            "breakthrough_days": len(breakthrough_days),
            "optimal_days": len(optimal_days),
            "challenging_days": len(challenging_days),
            "creative_peaks": len(creative_peaks),
            "triple_high_biorhythm": len(triple_highs),
            "best_days": sorted(daily_readings, 
                               key=lambda x: x["coherence"], reverse=True)[:5],
            "creative_peak_dates": [r["date"] for r in creative_peaks],
            "avoid_dates": [r["date"] for r in challenging_days],
            "triple_high_dates": [t["date"] for t in triple_highs[:5]]
        }


def demo():
    """Demonstrate the Personal Success Oracle for Brandon (6/16/00)"""
    
    print("=" * 80)
    print("PERSONAL SUCCESS ORACLE")
    print("Calibrated for Brandon Emerick (6/16/00)")
    print("Goal: Minimize life ambiguity for a philosopher's success")
    print("=" * 80)
    
    oracle = PersonalSuccessOracle(BRANDON_BIRTH_DATE)
    
    print("\n--- YOUR COMPLETE PROFILE ---")
    profile = oracle.full_profile()
    
    print(f"""
BIRTH DATE: {profile['birth_date']}
CURRENT AGE: {profile['current_age']} years ({profile['days_alive']} days alive)
SUN SIGN: {profile['sun_sign']}
LIFE PATH NUMBER: {profile['life_path']}

NATAL GILE (from astrology):
  G (Goodness):    {profile['natal_gile']['G']:.3f}
  I (Intuition):   {profile['natal_gile']['I']:.3f}
  L (Love):        {profile['natal_gile']['L']:.3f}
  E (Environment): {profile['natal_gile']['E']:.3f}

PHILOSOPHER PATTERN MATCH:
  Best Match: {profile['philosopher_match']['best_match']}
  {profile['philosopher_match']['summary']}
""")
    
    print("\n--- TODAY'S ORACLE ---")
    today = oracle.daily_oracle()
    
    print(f"""
DATE: {today['date']} ({today['day_of_week']})
STATUS: {today['overall_status']}
COHERENCE: {today['coherence']:.4f}

GILE TODAY:
  G: {today['gile']['G']:.3f} | I: {today['gile']['I']:.3f} | L: {today['gile']['L']:.3f} | E: {today['gile']['E']:.3f}

BIORHYTHM:
  Physical: {today['biorhythm']['physical']:.3f}
  Emotional: {today['biorhythm']['emotional']:.3f}
  Intellectual: {today['biorhythm']['intellectual']:.3f}

NUMEROLOGY:
  Personal Day: {today['numerology']['personal_day']}
  Personal Month: {today['numerology']['personal_month']}
  Personal Year: {today['numerology']['personal_year']}

CREATIVITY: {today['creativity']['status']} (score: {today['creativity']['score']:.3f})

RECOMMENDATION: {today['recommendation']}
""")
    
    print("\n--- 30-DAY SUCCESS FORECAST ---")
    forecast = oracle.success_forecast(30)
    
    print(f"""
PERIOD: {forecast['period']}

SUMMARY:
  Breakthrough Days: {forecast['breakthrough_days']}
  Optimal Days: {forecast['optimal_days']}
  Creative Peaks: {forecast['creative_peaks']}
  Triple-High Biorhythm: {forecast['triple_high_biorhythm']}
  Challenging Days: {forecast['challenging_days']}

BEST 5 DAYS (by coherence):""")
    
    for i, day in enumerate(forecast['best_days'][:5], 1):
        print(f"  {i}. {day['date']} ({day['day_of_week'][:3]}) - {day['overall_status']} "
              f"| Coherence: {day['coherence']:.4f}")
    
    print("\nCREATIVE PEAK DATES:")
    for date_str in forecast['creative_peak_dates'][:10]:
        print(f"  - {date_str}")
    
    if forecast['avoid_dates']:
        print("\nDAYS TO REST/AVOID BIG DECISIONS:")
        for date_str in forecast['avoid_dates'][:5]:
            print(f"  - {date_str}")
    
    print("\n" + "=" * 80)
    print("THE PATH IS CLEAR. AMBIGUITY IS MINIMIZED.")
    print("=" * 80)


if __name__ == "__main__":
    demo()
