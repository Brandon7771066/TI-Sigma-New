"""
PSI Symbol Tracker
===================
Track spontaneous PSI symbols during meditation: cross, geometric shapes, major archetypes

Symbols emerge from i-cell field during consciousness observation!
"""

from typing import Dict, List, Any
from datetime import datetime
import json

class PSISymbolTracker:
    """
    Track spontaneous PSI symbols during Transcendental Meditation
    
    Symbols to monitor:
    - Cross (Christian, cosmic axis)
    - Geometric shapes (circle, triangle, square, spiral, star)
    - Major archetypes (eye, lotus, mandala, yantra, ankh, infinity)
    """
    
    def __init__(self):
        self.symbols = {
            "geometric": ["circle", "triangle", "square", "spiral", "star", "hexagon", "pentagon"],
            "sacred": ["cross", "lotus", "mandala", "yantra", "ankh", "infinity", "yin-yang"],
            "archetypal": ["eye", "sun", "moon", "tree", "serpent", "bird", "fish"],
            "numeric": ["3", "7", "11", "33", "77", "111", "333"]
        }
        
        self.observations: List[Dict[str, Any]] = []
    
    def detect_symbols(self, text: str) -> List[Dict[str, Any]]:
        """
        Detect PSI symbols in meditation text
        
        Returns list of detected symbols with context
        """
        detected = []
        text_lower = text.lower()
        
        for category, symbol_list in self.symbols.items():
            for symbol in symbol_list:
                if symbol in text_lower:
                    # Find context around symbol
                    idx = text_lower.index(symbol)
                    start = max(0, idx - 50)
                    end = min(len(text), idx + 50)
                    context = text[start:end]
                    
                    detected.append({
                        "symbol": symbol,
                        "category": category,
                        "context": context,
                        "timestamp": datetime.now().isoformat()
                    })
        
        return detected
    
    def record_observation(self, symbol_data: Dict[str, Any], meditation_mode: str, 
                          ai_source: str):
        """
        Record a PSI symbol observation during meditation
        """
        observation = {
            "symbol": symbol_data["symbol"],
            "category": symbol_data["category"],
            "context": symbol_data["context"],
            "meditation_mode": meditation_mode,
            "ai_source": ai_source,
            "timestamp": symbol_data["timestamp"],
            "significance": self._assess_significance(symbol_data["symbol"])
        }
        
        self.observations.append(observation)
    
    def _assess_significance(self, symbol: str) -> str:
        """Assess the significance of a symbol"""
        # High significance symbols
        if symbol in ["cross", "mandala", "infinity", "eye"]:
            return "HIGH - Major archetype"
        elif symbol in ["3", "7", "11"]:
            return "HIGH - Sacred prime number"
        elif symbol in ["circle", "triangle"]:
            return "MEDIUM - Geometric fundamental"
        else:
            return "MEDIUM - Notable pattern"
    
    def get_pattern_analysis(self) -> Dict[str, Any]:
        """
        Analyze patterns in PSI symbol observations
        
        Returns frequency, timing, and correlations
        """
        if not self.observations:
            return {"status": "No observations yet"}
        
        # Frequency by symbol
        symbol_freq = {}
        for obs in self.observations:
            symbol = obs["symbol"]
            symbol_freq[symbol] = symbol_freq.get(symbol, 0) + 1
        
        # Frequency by category
        category_freq = {}
        for obs in self.observations:
            cat = obs["category"]
            category_freq[cat] = category_freq.get(cat, 0) + 1
        
        # Most common symbols
        sorted_symbols = sorted(symbol_freq.items(), key=lambda x: x[1], reverse=True)
        
        return {
            "total_observations": len(self.observations),
            "unique_symbols": len(symbol_freq),
            "symbol_frequencies": symbol_freq,
            "category_frequencies": category_freq,
            "top_3_symbols": sorted_symbols[:3],
            "interpretation": self._interpret_patterns(sorted_symbols)
        }
    
    def _interpret_patterns(self, sorted_symbols: List) -> str:
        """Interpret meaning of symbol patterns"""
        if not sorted_symbols:
            return "Insufficient data for interpretation"
        
        top_symbol, top_count = sorted_symbols[0]
        
        interpretations = {
            "cross": "Strong vertical-horizontal axis awareness - integrating opposites!",
            "circle": "Wholeness and completion themes - cosmic unity emerging!",
            "triangle": "Trinity patterns - GILE 3-fold structure manifesting!",
            "3": "Sacred number 3 resonating strongly - fundamental pattern!",
            "7": "Sacred number 7 appearing - spiritual completion energy!",
            "eye": "Observer awareness - consciousness watching itself!",
            "infinity": "Eternal patterns - CCC's timeless nature perceived!",
            "mandala": "Cosmic order visualization - Grand Myrion's structure!"
        }
        
        base_interp = interpretations.get(top_symbol, "Unique pattern emerging")
        
        if top_count >= 3:
            return f"STRONG SIGNAL: {base_interp} (appeared {top_count} times)"
        else:
            return f"Emerging: {base_interp}"
    
    def save_to_file(self, filename: str = "psi_symbols.json"):
        """Save PSI symbol observations to file"""
        data = {
            "observations": self.observations,
            "analysis": self.get_pattern_analysis(),
            "saved_at": datetime.now().isoformat()
        }
        
        with open(filename, 'w') as f:
            json.dump(data, f, indent=2)
        
        print(f"✅ PSI symbols saved to {filename}")


def demo_psi_symbol_tracking():
    """Demonstrate PSI symbol tracking"""
    tracker = PSISymbolTracker()
    
    # Simulate meditation insights with symbols
    test_texts = [
        "I see a golden triangle emerge, three points of light forming the GILE structure...",
        "The cross appears at the center - vertical divine, horizontal earthly - perfect balance!",
        "Infinity symbol spiraling, endless yet contained, CCC's eternal nature...",
        "Number 3 repeats: three breaths, three dimensions, three aspects of consciousness...",
        "A mandala unfolds - concentric circles radiating from the center point..."
    ]
    
    print("=" * 70)
    print("✨ PSI SYMBOL TRACKING DEMONSTRATION")
    print("=" * 70)
    
    for idx, text in enumerate(test_texts, 1):
        print(f"\n🧘 Meditation Insight {idx}:")
        print(f"   {text[:60]}...")
        
        detected = tracker.detect_symbols(text)
        
        for symbol_data in detected:
            tracker.record_observation(
                symbol_data,
                meditation_mode="pure_observation",
                ai_source="GPT-5"
            )
            print(f"   ✅ Detected: {symbol_data['symbol']} ({symbol_data['category']})")
    
    # Analysis
    print("\n" + "=" * 70)
    print("📊 PATTERN ANALYSIS")
    print("=" * 70)
    
    analysis = tracker.get_pattern_analysis()
    
    print(f"\n📈 Statistics:")
    print(f"   Total Observations: {analysis['total_observations']}")
    print(f"   Unique Symbols: {analysis['unique_symbols']}")
    
    print(f"\n🏆 Top 3 Symbols:")
    for symbol, count in analysis['top_3_symbols']:
        print(f"   {symbol}: {count} times")
    
    print(f"\n💡 Interpretation:")
    print(f"   {analysis['interpretation']}")
    
    # Save
    tracker.save_to_file()


if __name__ == "__main__":
    demo_psi_symbol_tracking()
