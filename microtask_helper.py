"""
Microtask Evaluation Helper
Helps you decide which Toloka/Clickworker tasks to take and how to approach them.
"""

import re
from dataclasses import dataclass
from typing import List, Tuple

@dataclass
class TaskEvaluation:
    verdict: str  # "DO IT", "SKIP", "MAYBE"
    estimated_pay_per_hour: str
    time_estimate: str
    approach: str
    warnings: List[str]
    
HIGH_VALUE_KEYWORDS = [
    "evaluate response", "rate relevance", "choose better", "compare answers",
    "fact-check", "check correctness", "search relevance", "ai response quality",
    "side-by-side", "result usefulness", "judge quality", "rating task",
    "preference", "which is better", "rank", "accuracy check"
]

MEDIUM_VALUE_KEYWORDS = [
    "categorize", "classify", "label", "tag", "select category",
    "image classification", "sentiment", "identify"
]

LOW_VALUE_KEYWORDS = [
    "transcription", "audio", "survey", "long form", "essay", "write",
    "bounding box", "draw", "annotation", "segmentation"
]

SKIP_KEYWORDS = [
    "training", "qualification", "onboarding", "tutorial", "test",
    "verify account", "phone number", "selfie", "id verification"
]

def evaluate_task(task_description: str, pay_amount: float | None = None, 
                  estimated_minutes: float | None = None) -> TaskEvaluation:
    """
    Evaluate a microtask and provide recommendation.
    
    Args:
        task_description: Full text of task instructions
        pay_amount: Pay in dollars (optional)
        estimated_minutes: Estimated time (optional)
    
    Returns:
        TaskEvaluation with verdict and approach
    """
    text_lower = task_description.lower()
    warnings = []
    
    # Check for skip keywords first
    for keyword in SKIP_KEYWORDS:
        if keyword in text_lower:
            return TaskEvaluation(
                verdict="SKIP",
                estimated_pay_per_hour="$0 (no pay for training)",
                time_estimate="Unknown",
                approach="Skip this - training/qualification tasks don't pay",
                warnings=["This appears to be unpaid training or verification"]
            )
    
    # Score the task
    high_matches = sum(1 for k in HIGH_VALUE_KEYWORDS if k in text_lower)
    medium_matches = sum(1 for k in MEDIUM_VALUE_KEYWORDS if k in text_lower)
    low_matches = sum(1 for k in LOW_VALUE_KEYWORDS if k in text_lower)
    
    # Calculate pay per hour if we have data
    pay_per_hour = None
    if pay_amount and estimated_minutes:
        pay_per_hour = (pay_amount / estimated_minutes) * 60
    
    # Determine verdict
    if high_matches >= 1 and low_matches == 0:
        verdict = "DO IT"
        approach = generate_high_value_approach(task_description)
        time_est = "30-90 seconds per task"
        pay_est = "$10-20/hr potential" if not pay_per_hour else f"${pay_per_hour:.2f}/hr"
    elif medium_matches >= 1 and low_matches == 0:
        verdict = "MAYBE"
        approach = generate_medium_value_approach(task_description)
        time_est = "1-2 minutes per task"
        pay_est = "$6-12/hr potential" if not pay_per_hour else f"${pay_per_hour:.2f}/hr"
    elif low_matches >= 1:
        verdict = "SKIP"
        approach = "Skip for now - these tasks take too long for the pay"
        time_est = "3-10+ minutes per task"
        pay_est = "$3-8/hr typical"
        warnings.append("Time-intensive task type")
    else:
        verdict = "MAYBE"
        approach = "Read instructions carefully, try 2-3 before committing"
        time_est = "Unknown"
        pay_est = "Unknown"
        warnings.append("Unfamiliar task type - proceed cautiously")
    
    # Add warnings
    if "bonus" in text_lower:
        warnings.append("Has bonus potential - accuracy matters extra")
    if "reject" in text_lower or "ban" in text_lower:
        warnings.append("Mentions rejection/ban - follow rules exactly")
    if len(task_description) > 2000:
        warnings.append("Long instructions - may be complex")
    
    return TaskEvaluation(
        verdict=verdict,
        estimated_pay_per_hour=pay_est,
        time_estimate=time_est,
        approach=approach,
        warnings=warnings
    )

def generate_high_value_approach(task_description: str) -> str:
    """Generate specific approach for high-value tasks."""
    text_lower = task_description.lower()
    
    if "compare" in text_lower or "better" in text_lower or "side-by-side" in text_lower:
        return """COMPARISON TASK APPROACH:
1. Read BOTH responses fully (don't skim)
2. Check: Which is more FACTUALLY CORRECT?
3. Check: Which ACTUALLY ANSWERS the question?
4. Check: Which is CLEARER and more relevant?
5. Pick the one that's more direct and accurate
6. When tied, pick the shorter/simpler one
DO NOT add creativity - reward boring correctness!"""
    
    elif "rate" in text_lower or "relevance" in text_lower or "evaluate" in text_lower:
        return """RATING TASK APPROACH:
1. Read the question/query first
2. Read the response/result
3. Ask: Does this DIRECTLY answer what was asked?
4. Ask: Is it FACTUALLY ACCURATE?
5. Ask: Would a normal person find this helpful?
6. Rate strictly based on the rubric given
Use middle ratings when genuinely unsure"""
    
    elif "fact" in text_lower or "correct" in text_lower or "accuracy" in text_lower:
        return """FACT-CHECK APPROACH:
1. Identify the specific claim being made
2. Is it verifiable or opinion?
3. Does it contradict common knowledge?
4. Look for obvious errors (dates, names, numbers)
5. When unsure, mark as "cannot verify"
Don't overthink - obvious errors are what they want"""
    
    else:
        return """GENERAL EVALUATION APPROACH:
1. Is it factually correct?
2. Does it actually answer the question?
3. Is it clear and relevant?
4. Any obvious safety/nonsense issues?
Choose the more direct, accurate, simpler option"""

def generate_medium_value_approach(task_description: str) -> str:
    """Generate approach for medium-value tasks."""
    return """CLASSIFICATION APPROACH:
1. Read the categories available first
2. Look at the item to classify
3. Pick the MOST OBVIOUS match
4. When ambiguous, pick the broader category
5. Work fast - speed matters for these
Don't overthink categories"""

def format_evaluation(eval: TaskEvaluation) -> str:
    """Format evaluation for display."""
    emoji = {"DO IT": "✅", "SKIP": "❌", "MAYBE": "⚠️"}
    
    output = f"""
{'='*60}
{emoji.get(eval.verdict, '?')} VERDICT: {eval.verdict}
{'='*60}

💰 Estimated Pay: {eval.estimated_pay_per_hour}
⏱️ Time per Task: {eval.time_estimate}

📋 APPROACH:
{eval.approach}
"""
    
    if eval.warnings:
        output += f"\n⚠️ WARNINGS:\n"
        for w in eval.warnings:
            output += f"  • {w}\n"
    
    return output

def quick_eval(task_text: str) -> str:
    """Quick evaluation - just paste task text and get answer."""
    eval = evaluate_task(task_text)
    return format_evaluation(eval)

# Example usage
if __name__ == "__main__":
    # Test with a sample task
    sample_task = """
    Evaluate AI Response Quality
    
    You will be shown a question and two AI-generated responses.
    Your task is to choose which response is better based on:
    - Accuracy
    - Helpfulness
    - Clarity
    
    Pay: $0.05 per comparison
    Estimated time: 30-60 seconds
    """
    
    print(quick_eval(sample_task))
