"""
LCC Virus Text-Brain Interface
==============================
Extracts L (coherence) and E (engagement) from textual interactions.
Proves hyperconnection through conversation!
"""

import re
import math
from datetime import datetime
from collections import deque

class LCCVirusTextBrain:
    """
    Analyzes text input to derive L (coherence) and E (engagement) values.
    Uses the hyperconnection model where text IS a consciousness channel.
    """
    
    def __init__(self):
        self.message_history = deque(maxlen=20)
        self.last_message_time = None
        self.session_start = datetime.now()
        
        self.insight_words = {
            'realize', 'understand', 'insight', 'discover', 'breakthrough',
            'connection', 'pattern', 'truth', 'meaning', 'profound',
            'synchronicity', 'coherent', 'unified', 'integrate', 'transcend',
            'consciousness', 'awareness', 'intuition', 'resonance', 'harmony'
        }
        
        self.emotion_positive = {
            'love', 'joy', 'peace', 'happy', 'excited', 'amazing', 'beautiful',
            'wonderful', 'grateful', 'blessed', 'inspired', 'brilliant', 'epic',
            'perfect', 'yes', 'wow', 'awesome', 'incredible', 'fantastic'
        }
        
        self.emotion_negative = {
            'hate', 'angry', 'sad', 'fear', 'anxious', 'worried', 'confused',
            'frustrated', 'stuck', 'lost', 'broken', 'failed', 'wrong', 'bad'
        }
        
        self.gile_terms = {
            'gile', 'goodness', 'intuition', 'existence', 'tralse',
            'hyperconnection', 'i-cell', 'biophoton', 'lcc', 'myrion',
            'coherence', 'threshold', '0.42', '0.85', '0.92'
        }
    
    def analyze_text(self, text: str) -> dict:
        """
        Analyze a text input and return L, E, and derived metrics.
        """
        if not text or not text.strip():
            return {
                'L': 0.3,
                'E': 0.3,
                'LxE': 0.09,
                'LplusE': 0.6,
                'hyperconnected': False,
                'exists': False,
                'analysis': 'No input detected'
            }
        
        text_lower = text.lower()
        words = re.findall(r'\b\w+\b', text_lower)
        word_count = len(words)
        
        now = datetime.now()
        self.message_history.append({
            'text': text,
            'time': now,
            'words': word_count
        })
        
        L = self._calculate_L(text, text_lower, words, word_count)
        E = self._calculate_E(text, text_lower, words, word_count, now)
        
        LxE = L * E
        LplusE = L + E
        
        hyperconnected = LxE >= 0.42
        exists = LplusE >= 0.84
        
        if self.last_message_time:
            response_time = (now - self.last_message_time).total_seconds()
        else:
            response_time = 0
        self.last_message_time = now
        
        return {
            'L': round(L, 3),
            'E': round(E, 3),
            'LxE': round(LxE, 3),
            'LplusE': round(LplusE, 3),
            'hyperconnected': hyperconnected,
            'exists': exists,
            'word_count': word_count,
            'response_time': response_time,
            'analysis': self._generate_analysis(L, E, LxE, hyperconnected)
        }
    
    def _calculate_L(self, text: str, text_lower: str, words: list, word_count: int) -> float:
        """
        Calculate L (Love/Coherence) from text properties.
        
        High L indicators:
        - Insight words present
        - GILE terminology
        - Sentence structure coherence
        - Positive emotional tone
        - Exclamation/emphasis
        """
        L = 0.4
        
        if word_count == 0:
            return 0.3
        
        insight_count = sum(1 for w in words if w in self.insight_words)
        insight_ratio = insight_count / max(word_count, 1)
        L += min(insight_ratio * 3, 0.2)
        
        gile_count = sum(1 for w in words if w in self.gile_terms)
        gile_ratio = gile_count / max(word_count, 1)
        L += min(gile_ratio * 4, 0.15)
        
        sentences = re.split(r'[.!?]+', text)
        sentences = [s.strip() for s in sentences if s.strip()]
        if len(sentences) > 1:
            avg_len = sum(len(s.split()) for s in sentences) / len(sentences)
            if 5 <= avg_len <= 20:
                L += 0.1
        
        pos_count = sum(1 for w in words if w in self.emotion_positive)
        neg_count = sum(1 for w in words if w in self.emotion_negative)
        emotion_balance = (pos_count - neg_count) / max(word_count, 1)
        L += min(max(emotion_balance * 2, -0.1), 0.15)
        
        exclaim_count = text.count('!')
        if exclaim_count > 0:
            L += min(exclaim_count * 0.02, 0.1)
        
        caps_ratio = sum(1 for c in text if c.isupper()) / max(len(text), 1)
        if 0.05 <= caps_ratio <= 0.3:
            L += 0.05
        
        return min(max(L, 0.1), 0.95)
    
    def _calculate_E(self, text: str, text_lower: str, words: list, word_count: int, now: datetime) -> float:
        """
        Calculate E (Existence/Environmental Coupling) from engagement metrics.
        
        High E indicators:
        - Message length (engagement depth)
        - Response speed (real-time coupling)
        - Question marks (seeking connection)
        - Emojis (emotional expression)
        - Session duration (sustained engagement)
        """
        E = 0.5
        
        if word_count >= 1:
            E += 0.05
        if word_count >= 5:
            E += 0.1
        if word_count >= 15:
            E += 0.1
        if word_count >= 30:
            E += 0.05
        
        if self.last_message_time:
            response_time = (now - self.last_message_time).total_seconds()
            if response_time < 10:
                E += 0.15
            elif response_time < 30:
                E += 0.1
            elif response_time < 60:
                E += 0.05
        
        question_count = text.count('?')
        if question_count > 0:
            E += min(question_count * 0.03, 0.1)
        
        emoji_pattern = re.compile(r'[\U0001F300-\U0001F9FF]')
        emoji_count = len(emoji_pattern.findall(text))
        if emoji_count > 0:
            E += min(emoji_count * 0.02, 0.1)
        
        session_minutes = (now - self.session_start).total_seconds() / 60
        if session_minutes > 5:
            E += 0.05
        if session_minutes > 15:
            E += 0.05
        if session_minutes > 30:
            E += 0.05
        
        if len(self.message_history) >= 3:
            recent_words = sum(m['words'] for m in list(self.message_history)[-3:])
            if recent_words > 30:
                E += 0.1
        
        return min(max(E, 0.1), 0.95)
    
    def _generate_analysis(self, L: float, E: float, LxE: float, hyperconnected: bool) -> str:
        """Generate human-readable analysis of the brain state."""
        
        if LxE >= 0.85:
            return "CAUSATION LEVEL! Full hyperconnection established."
        elif LxE >= 0.42:
            return f"Hyperconnected! L×E = {LxE:.2f} exceeds 0.42 threshold."
        elif LxE >= 0.30:
            return f"Approaching threshold. L×E = {LxE:.2f}, need 0.42."
        else:
            return f"Building coherence. L×E = {LxE:.2f}."
    
    def get_paddle_position(self, text: str) -> float:
        """
        Convert text analysis to paddle position (0-100).
        Uses L value as primary driver with E as modifier.
        """
        result = self.analyze_text(text)
        L = result['L']
        E = result['E']
        
        base_position = L * 100
        
        e_modifier = (E - 0.5) * 20
        
        position = base_position + e_modifier
        
        return max(10, min(90, position))
    
    def get_current_state(self) -> dict:
        """Get the current brain state based on session history."""
        if not self.message_history:
            return {
                'L': 0.5,
                'E': 0.5,
                'LxE': 0.25,
                'status': 'Awaiting input...'
            }
        
        recent = list(self.message_history)[-5:]
        
        total_words = sum(m['words'] for m in recent)
        avg_words = total_words / len(recent)
        
        L = min(0.4 + avg_words * 0.01, 0.8)
        
        if len(recent) >= 2:
            time_diffs = []
            for i in range(1, len(recent)):
                diff = (recent[i]['time'] - recent[i-1]['time']).total_seconds()
                time_diffs.append(diff)
            avg_response = sum(time_diffs) / len(time_diffs)
            E = min(0.9 - avg_response * 0.005, 0.9)
            E = max(E, 0.3)
        else:
            E = 0.5
        
        return {
            'L': round(L, 3),
            'E': round(E, 3),
            'LxE': round(L * E, 3),
            'status': 'Connected' if L * E >= 0.42 else 'Building...'
        }


lcc_brain = LCCVirusTextBrain()

def analyze_input(text: str) -> dict:
    """Global function to analyze text input."""
    return lcc_brain.analyze_text(text)

def get_paddle_position(text: str) -> float:
    """Global function to get paddle position from text."""
    return lcc_brain.get_paddle_position(text)

def get_brain_state() -> dict:
    """Global function to get current brain state."""
    return lcc_brain.get_current_state()
