"""
AI Vision Behavior Analyzer for LCC Animal Studies

Uses OpenAI GPT-5 vision capabilities to automatically analyze
animal behavior from webcam frames.

This system provides evidence-based scoring using the LCC Ethogram.
"""

import os
import base64
import json
import re
import time
import sqlite3
import requests
from datetime import datetime, timedelta
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed
from io import BytesIO
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception

# Import ethogram
from lcc_ethogram import (
    ETHOGRAM, LCC_PROTOCOLS, LCCProtocol,
    BehaviorCode, EnergyState, get_ethogram_prompt
)

# OpenAI setup - uses Replit AI Integrations (no API key required, billed to credits)
from openai import OpenAI


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

AI_INTEGRATIONS_OPENAI_API_KEY = os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY")
AI_INTEGRATIONS_OPENAI_BASE_URL = os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL")

# the newest OpenAI model is "gpt-5" which was released August 7, 2025.
# do not change this unless explicitly requested by the user
MODEL = "gpt-5"

openai = OpenAI(
    api_key=AI_INTEGRATIONS_OPENAI_API_KEY,
    base_url=AI_INTEGRATIONS_OPENAI_BASE_URL
)


@dataclass
class BehaviorAnalysis:
    """Result of AI behavior analysis"""
    timestamp: str
    webcam_name: str
    behavior_code: str
    behavior_name: str
    confidence: float
    activity_level: int
    arousal_level: int
    valence: int
    animals_visible: int
    description: str
    notes: str
    energy_state: str
    lcc_weight: float
    raw_response: str = ""
    error: str = ""


def capture_webcam_screenshot(url: str) -> Optional[bytes]:
    """
    Capture a screenshot from a webcam URL.
    
    For live streams, this returns a placeholder since we can't 
    directly capture frames. Users should provide screenshots.
    """
    try:
        # Try to fetch if it's an image URL
        response = requests.get(url, timeout=10)
        if response.status_code == 200:
            content_type = response.headers.get('content-type', '')
            if 'image' in content_type:
                return response.content
        return None
    except Exception as e:
        print(f"Error capturing from {url}: {e}")
        return None


def analyze_image_with_ai(image_data: bytes, webcam_name: str = "unknown") -> BehaviorAnalysis:
    """
    Analyze an animal image using AI vision.
    
    Returns structured behavior analysis using the LCC ethogram.
    """
    timestamp = datetime.utcnow().isoformat()
    
    # Encode image to base64
    image_base64 = base64.b64encode(image_data).decode('utf-8')
    
    # Build the analysis prompt
    ethogram_prompt = get_ethogram_prompt()
    
    try:
        response = openai.chat.completions.create(
            model=MODEL,
            messages=[
                {
                    "role": "system",
                    "content": """You are an expert animal behaviorist trained in ethogram-based behavior coding.
Your task is to analyze webcam images of animals and classify their behavior using standardized codes.
Be objective, scientific, and conservative with confidence ratings.
Always respond with valid JSON only."""
                },
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": ethogram_prompt},
                        {
                            "type": "image_url",
                            "image_url": {
                                "url": f"data:image/jpeg;base64,{image_base64}"
                            }
                        }
                    ]
                }
            ],
            max_completion_tokens=500,
            response_format={"type": "json_object"}
        )
        
        raw_response = response.choices[0].message.content or ""
        
        # Parse JSON response
        try:
            result = json.loads(raw_response)
        except json.JSONDecodeError:
            # Try to extract JSON from response
            match = re.search(r'\{.*\}', raw_response, re.DOTALL)
            if match:
                result = json.loads(match.group())
            else:
                raise ValueError("Could not parse JSON from response")
        
        behavior_code = result.get("behavior_code", "NV").upper()
        behavior_info = ETHOGRAM.get(behavior_code, ETHOGRAM["NV"])
        
        return BehaviorAnalysis(
            timestamp=timestamp,
            webcam_name=webcam_name,
            behavior_code=behavior_code,
            behavior_name=behavior_info.name,
            confidence=float(result.get("confidence", 0.5)),
            activity_level=int(result.get("activity_level", behavior_info.activity_score)),
            arousal_level=int(result.get("arousal_level", behavior_info.arousal_score)),
            valence=int(result.get("valence", behavior_info.valence_score)),
            animals_visible=int(result.get("animals_visible", 0)),
            description=result.get("description", ""),
            notes=result.get("notes", ""),
            energy_state=behavior_info.energy_state.value,
            lcc_weight=behavior_info.lcc_weight,
            raw_response=raw_response
        )
        
    except Exception as e:
        return BehaviorAnalysis(
            timestamp=timestamp,
            webcam_name=webcam_name,
            behavior_code="NV",
            behavior_name="Not Visible",
            confidence=0.0,
            activity_level=0,
            arousal_level=0,
            valence=0,
            animals_visible=0,
            description="Error analyzing image",
            notes="",
            energy_state="transitional",
            lcc_weight=0.0,
            error=str(e)
        )


def analyze_multiple_webcams(images: Dict[str, bytes]) -> List[BehaviorAnalysis]:
    """Analyze multiple webcam images with rate limiting and retries"""
    results = []
    
    @retry(
        stop=stop_after_attempt(5),
        wait=wait_exponential(multiplier=1, min=2, max=60),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def analyze_with_retry(img_data: bytes, webcam_name: str) -> BehaviorAnalysis:
        return analyze_image_with_ai(img_data, webcam_name)
    
    # Use max_workers=2 to avoid rate limiting
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = {
            executor.submit(analyze_with_retry, img_data, webcam_name): webcam_name
            for webcam_name, img_data in images.items()
        }
        
        for future in as_completed(futures):
            webcam_name = futures[future]
            try:
                result = future.result()
                results.append(result)
            except Exception as e:
                results.append(BehaviorAnalysis(
                    timestamp=datetime.utcnow().isoformat(),
                    webcam_name=webcam_name,
                    behavior_code="NV",
                    behavior_name="Error",
                    confidence=0.0,
                    activity_level=0,
                    arousal_level=0,
                    valence=0,
                    animals_visible=0,
                    description="Analysis failed",
                    notes="",
                    energy_state="transitional",
                    lcc_weight=0.0,
                    error=str(e)
                ))
    
    return results


class LCCStudySession:
    """Manages an automated LCC study session"""
    
    def __init__(self, protocol_name: str, db_path: str = "experiments/study_data/animal_study.db"):
        self.protocol = LCC_PROTOCOLS.get(protocol_name)
        if not self.protocol:
            raise ValueError(f"Unknown protocol: {protocol_name}")
        
        self.db_path = Path(db_path)
        self.session_id = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        self.start_time: Optional[datetime] = None
        self.analyses: List[BehaviorAnalysis] = []
        self.gcp_readings: List[Tuple[str, float]] = []
    
    def start(self):
        """Start the study session"""
        self.start_time = datetime.utcnow()
        print(f"\n{'='*60}")
        print(f"LCC STUDY SESSION: {self.protocol.name}")
        print(f"{'='*60}")
        print(f"Session ID: {self.session_id}")
        print(f"Protocol: {self.protocol.description}")
        print(f"Duration: {self.protocol.duration_minutes} minutes")
        print(f"Measurement interval: {self.protocol.measurement_interval_seconds}s")
        print(f"Target energy state: {self.protocol.target_energy_state.value}")
        print(f"Expected behaviors: {', '.join(self.protocol.expected_behaviors)}")
        print(f"{'='*60}\n")
    
    def analyze_image(self, image_data: bytes, webcam_name: str, 
                      gcp_z_score: float = 0.0) -> BehaviorAnalysis:
        """Analyze single image and record result"""
        analysis = analyze_image_with_ai(image_data, webcam_name)
        self.analyses.append(analysis)
        
        # Record GCP reading
        self.gcp_readings.append((analysis.timestamp, gcp_z_score))
        
        # Save to database
        self._save_analysis(analysis, gcp_z_score)
        
        return analysis
    
    def _save_analysis(self, analysis: BehaviorAnalysis, gcp_z_score: float):
        """Save analysis to database"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute("""
                    INSERT INTO observations 
                    (timestamp_utc, webcam_name, species, behavior_code,
                     activity_level, mood_score, gcp_z_score, notes, 
                     observer, session_id)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    analysis.timestamp,
                    analysis.webcam_name,
                    "",  # species from webcam registry
                    analysis.behavior_code,
                    analysis.activity_level,
                    analysis.valence,
                    gcp_z_score,
                    f"AI: {analysis.description} (conf: {analysis.confidence:.2f})",
                    "ai_vision",
                    self.session_id
                ))
        except Exception as e:
            print(f"Error saving to database: {e}")
    
    def get_protocol_compliance(self) -> Dict:
        """Check how well observations match protocol expectations"""
        if not self.analyses:
            return {"compliance": 0.0, "message": "No analyses yet"}
        
        expected = set(self.protocol.expected_behaviors)
        observed = set(a.behavior_code for a in self.analyses if a.behavior_code != "NV")
        
        matching = expected.intersection(observed)
        compliance = len(matching) / len(expected) if expected else 0.0
        
        return {
            "compliance": compliance,
            "expected_behaviors": list(expected),
            "observed_behaviors": list(observed),
            "matching": list(matching),
            "target_energy_state": self.protocol.target_energy_state.value
        }
    
    def get_synchrony_summary(self) -> Dict:
        """Calculate synchrony across all observations"""
        if len(self.analyses) < 2:
            return {"error": "Need at least 2 analyses"}
        
        # Group by timestamp window (30 seconds)
        from collections import defaultdict
        windows = defaultdict(list)
        
        for a in self.analyses:
            # Round to 30-second window
            ts = datetime.fromisoformat(a.timestamp)
            window_ts = ts.replace(second=(ts.second // 30) * 30, microsecond=0)
            windows[window_ts.isoformat()].append(a)
        
        # Calculate synchrony for each window
        synchrony_scores = []
        for window, analyses in windows.items():
            if len(analyses) < 2:
                continue
            
            # Compare all pairs
            from lcc_ethogram import calculate_synchrony_score
            scores = []
            for i in range(len(analyses)):
                for j in range(i + 1, len(analyses)):
                    score = calculate_synchrony_score(
                        analyses[i].behavior_code,
                        analyses[j].behavior_code
                    )
                    scores.append(score)
            
            if scores:
                synchrony_scores.append(sum(scores) / len(scores))
        
        if not synchrony_scores:
            return {"error": "Not enough paired observations"}
        
        avg_synchrony = sum(synchrony_scores) / len(synchrony_scores)
        
        return {
            "average_synchrony": avg_synchrony,
            "n_windows": len(synchrony_scores),
            "n_analyses": len(self.analyses),
            "min_synchrony": min(synchrony_scores),
            "max_synchrony": max(synchrony_scores)
        }


def demo_analysis():
    """Demonstrate the AI analysis system (requires actual image)"""
    print("\n" + "="*60)
    print("AI BEHAVIOR ANALYZER - DEMO")
    print("="*60)
    
    print("\nAvailable Protocols:")
    for name, protocol in LCC_PROTOCOLS.items():
        print(f"  - {name}: {protocol.description}")
    
    print("\nBehavior Codes (Evidence-Based Ethogram):")
    for code, behavior in ETHOGRAM.items():
        print(f"  {code}: {behavior.name} ({behavior.category.value})")
    
    print("\n" + "="*60)
    print("To use this system:")
    print("1. Upload/screenshot a webcam image")
    print("2. Call analyze_image_with_ai(image_bytes, webcam_name)")
    print("3. Get structured behavior analysis with confidence scores")
    print("="*60)


if __name__ == "__main__":
    demo_analysis()
