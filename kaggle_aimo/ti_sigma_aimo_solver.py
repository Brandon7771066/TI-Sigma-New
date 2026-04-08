"""
TI Sigma AIMO PP3 Solver
========================
AI Mathematical Olympiad – Progress Prize 3
Solver using Tralse chain-of-thought + PRIMARY CONSTANT proximity + MR collapse.

Architecture:
  Layer 0: Problem Classification (geometry / number_theory / algebra / combinatorics)
  Layer 1: PRIMARY CONSTANT Proximity Check (pre-answer filter)
  Layer 2: Tralse Chain-of-Thought Prompting (Claude / Anthropic)
  Layer 3: Answer Extraction + Validation
  Layer 4: MR Collapse (confidence aggregation over N passes)

Brandon Emerick | TI Sigma | April 2026
"""

import re
import math
import json
import os
import time
from typing import Optional

# ─────────────────────────────────────────────
# PRIMARY CONSTANTS (TI Sigma – URB #529)
# ─────────────────────────────────────────────
PHI   = (1 + math.sqrt(5)) / 2          # Golden ratio  ≈ 1.6180
SQRT2 = math.sqrt(2)                    # ≈ 1.4142
SQRT3 = math.sqrt(3)                    # ≈ 1.7321
SQRT5 = math.sqrt(5)                    # ≈ 2.2361
E     = math.e                          # ≈ 2.7183
PI    = math.pi                         # ≈ 3.1416
C     = 1 / (PHI * SQRT2)              # Emerick constant ≈ 0.4370
T     = 1 - math.exp(-E)               # TI threshold   ≈ 0.9340
ET    = SQRT2 - 1                       # Emerick threshold ≈ 0.4142

PRIMARY_CONSTANTS = {
    'sqrt2':  SQRT2,
    'phi':    PHI,
    'e':      E,
    'pi':     PI,
    'C':      C,
    'phi2':   PHI**2,
    'sqrt3':  SQRT3,
    'sqrt5':  SQRT5,
    '4_3':    4/3,
    '3_2':    3/2,
    '2_3':    2/3,
    'pi_4':   PI/4,
    'pi_2':   PI/2,
    '2pi':    2*PI,
    'e_2':    E/2,
    'ln2':    math.log(2),
    'T':      T,
    'ET':     ET,
}

FIBONACCI = [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,
             1597,2584,4181,6765,10946,17711,28657,46368,75025]
LUCAS     = [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,
             1364,2207,3571,5778,9349,15127,24476,39603,64079]
CATALAN   = [1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900]
BELL      = [1,1,2,5,15,52,203,877,4140,21147,115975,678570]
TRIANGULAR= [n*(n+1)//2 for n in range(200)]
PERFECT_SQ= [n*n for n in range(1, 1001)]


def primary_constant_proximity(x: float, threshold: float = 0.01) -> tuple[bool, Optional[str]]:
    """
    Check if x is suspiciously close to a PRIMARY CONSTANT or its simple multiples/fractions.
    Returns (is_close, description_or_None).
    """
    if not isinstance(x, (int, float)) or math.isnan(x) or math.isinf(x):
        return False, None
    for name, val in PRIMARY_CONSTANTS.items():
        for mult in [0.5, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 24, 36, 60, 100, 360]:
            target = val * mult
            if target == 0:
                continue
            if abs(x - target) / target < threshold:
                return True, f"{x:.6g} ≈ {mult}×{name} = {target:.6g}"
    return False, None


def check_special_number(x: float) -> Optional[str]:
    """Check if x is a combinatorially special number."""
    xi = int(round(x))
    if abs(x - xi) > 0.001:
        return None
    if xi in FIBONACCI:  return f"Fibonacci({FIBONACCI.index(xi)})"
    if xi in LUCAS:      return f"Lucas({LUCAS.index(xi)})"
    if xi in CATALAN:    return f"Catalan({CATALAN.index(xi)})"
    if xi in BELL:       return f"Bell({BELL.index(xi)})"
    if xi in TRIANGULAR: return f"Triangular({TRIANGULAR.index(xi)})"
    if xi in PERFECT_SQ: return f"PerfectSquare({int(math.sqrt(xi))}^2)"
    # Power of 2
    if xi > 0 and (xi & (xi-1)) == 0:
        return f"PowerOf2(2^{int(math.log2(xi))})"
    # Power of 3
    n = xi
    while n > 1:
        if n % 3 != 0: break
        n //= 3
    if n == 1: return f"PowerOf3(3^{int(round(math.log(xi,3)))})"
    return None


def classify_problem(text: str) -> str:
    """Classify problem type from text keywords."""
    text_l = text.lower()
    if any(w in text_l for w in ['circle', 'triangle', 'polygon', 'angle', 'radius', 'area', 'perimeter', 'chord', 'tangent']):
        return 'geometry'
    if any(w in text_l for w in ['prime', 'divisor', 'gcd', 'lcm', 'remainder', 'modulo', 'integer', 'digit', 'factor']):
        return 'number_theory'
    if any(w in text_l for w in ['sequence', 'series', 'sum', 'count', 'ways', 'arrange', 'choose', 'subset', 'permutation', 'combination', 'probability']):
        return 'combinatorics'
    if any(w in text_l for w in ['function', 'polynomial', 'root', 'equation', 'system', 'maximum', 'minimum', 'inequality', 'real number']):
        return 'algebra'
    return 'algebra'


def extract_answer_from_text(text: str) -> Optional[int]:
    """
    Extract a final integer answer from model output.
    Priority: boxed answer > "the answer is X" > last standalone integer.
    """
    # LaTeX boxed
    m = re.search(r'\\boxed\{(\-?\d+(?:\.\d+)?)\}', text)
    if m:
        return int(round(float(m.group(1))))

    # "answer is X", "= X", "result is X"
    patterns = [
        r'(?:the\s+)?answer\s+is\s+(\-?\d+)',
        r'(?:final\s+)?answer\s*[:=]\s*(\-?\d+)',
        r'(?:result|solution)\s+is\s+(\-?\d+)',
        r'=\s*(\-?\d+)\s*$',
        r'\*\*(\-?\d+)\*\*',
    ]
    for p in patterns:
        m = re.search(p, text, re.IGNORECASE | re.MULTILINE)
        if m:
            return int(m.group(1))

    # Last integer on its own line
    integers = re.findall(r'(?<!\d)(\-?\d+)(?!\d)', text)
    if integers:
        return int(integers[-1])

    return None


def validate_answer(answer: int, problem_type: str) -> dict:
    """Run TI Sigma validation layers on a candidate answer."""
    result = {
        'answer': answer,
        'in_aime_range': 0 <= answer <= 999,
        'primary_constant': primary_constant_proximity(answer),
        'special_number': check_special_number(answer),
        'problem_type': problem_type,
    }
    # Confidence heuristic
    conf = 0.4  # base
    if result['primary_constant'][0]:   conf += 0.25
    if result['special_number']:        conf += 0.15
    if result['in_aime_range']:         conf += 0.10
    result['confidence'] = min(conf, 1.0)
    return result


# ─────────────────────────────────────────────
# TRALSE CHAIN-OF-THOUGHT PROMPT
# ─────────────────────────────────────────────
TRALSE_COT_SYSTEM = """You are a world-class mathematical olympiad solver.
Solve the problem using this exact structure:

1. TRUE POLE: State the most direct interpretation of the problem.
2. FALSE POLE: Identify the hidden constraint, edge case, or trick that beginners miss.
3. MYRION SYNTHESIS: Combine both poles to find the correct formulation.
4. CALCULATION: Work through the mathematics carefully and precisely.
5. PRIMARY CHECK: Is the answer near √2≈1.414, φ≈1.618, e≈2.718, π≈3.14159, or a Fibonacci/Catalan number?
6. FINAL ANSWER: State the final integer answer in a \\boxed{} environment.

Be methodical. Check your arithmetic. The answer is a non-negative integer."""


def build_tralse_prompt(problem: str, problem_type: str, attempt: int = 1) -> str:
    """Build the Tralse chain-of-thought prompt for a given problem."""
    type_hints = {
        'geometry':      "This is a GEOMETRY problem. Key tools: similarity ratios, power of a point, trigonometric identities, area formulas. Answers often involve π or √2 multiplied by an integer.",
        'number_theory': "This is a NUMBER THEORY problem. Key tools: modular arithmetic, prime factorization, Euler's theorem, Chinese Remainder Theorem. Check if the answer is a Fibonacci or Bell number.",
        'combinatorics': "This is a COMBINATORICS problem. Key tools: inclusion-exclusion, generating functions, bijections. Answers are frequently Catalan or Fibonacci numbers.",
        'algebra':       "This is an ALGEBRA problem. Key tools: AM-GM, Cauchy-Schwarz, substitution, completing the square. Answers often emerge from elegant factorizations.",
    }
    hint = type_hints.get(problem_type, "")

    retry_note = ""
    if attempt == 2:
        retry_note = "\n\nNOTE: This is attempt 2. Double-check each arithmetic step and verify the answer satisfies ALL conditions in the problem."
    elif attempt >= 3:
        retry_note = "\n\nNOTE: This is attempt 3. Try a completely different approach from scratch. Consider whether inclusion-exclusion, complementary counting, or a generating function gives a cleaner path."

    return f"""{hint}{retry_note}

Problem: {problem}

Work through this carefully using the TRUE POLE / FALSE POLE / MYRION SYNTHESIS structure."""


# ─────────────────────────────────────────────
# LLM BACKENDS
# ─────────────────────────────────────────────

def call_anthropic(system: str, user: str, max_tokens: int = 2048, model: str = "claude-opus-4-5") -> str:
    """Call Anthropic Claude API."""
    try:
        import anthropic
        client = anthropic.Anthropic()
        message = client.messages.create(
            model=model,
            max_tokens=max_tokens,
            system=system,
            messages=[{"role": "user", "content": user}]
        )
        return message.content[0].text
    except Exception as ex:
        return f"[ERROR: {ex}]"


def call_openai(system: str, user: str, max_tokens: int = 2048, model: str = "gpt-4o") -> str:
    """Call OpenAI API."""
    try:
        from openai import OpenAI
        client = OpenAI()
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": system},
                {"role": "user", "content": user},
            ],
            max_tokens=max_tokens,
            temperature=0.2,
        )
        return response.choices[0].message.content
    except Exception as ex:
        return f"[ERROR: {ex}]"


def call_llm(system: str, user: str, max_tokens: int = 2048, backend: str = "anthropic") -> str:
    """Route to preferred LLM backend."""
    if backend == "anthropic":
        return call_anthropic(system, user, max_tokens)
    elif backend == "openai":
        return call_openai(system, user, max_tokens)
    return "[ERROR: unknown backend]"


# ─────────────────────────────────────────────
# MR COLLAPSE  (Multi-pass answer aggregation)
# ─────────────────────────────────────────────

def mr_collapse(answers: list[Optional[int]], confidences: list[float]) -> tuple[Optional[int], float, str]:
    """
    Myrion Resolution collapse over N answer candidates.
    Stage 1 — DT Screen: remove None answers and wildly inconsistent outliers.
    Stage 2 — GILE Integration: weight by confidence + PRIMARY CONSTANT boost.
    Stage 3 — Quality Check: return majority vote, weighted confidence, and MR level.
    """
    # Stage 1 — DT Screen
    valid = [(a, c) for a, c in zip(answers, confidences) if a is not None]
    if not valid:
        return None, 0.0, "DT"

    # Stage 2 — Weighted voting
    from collections import Counter
    vote_weight: dict[int, float] = {}
    for a, c in valid:
        vote_weight[a] = vote_weight.get(a, 0) + c
        # PRIMARY CONSTANT boost
        is_pc, _ = primary_constant_proximity(a)
        if is_pc:
            vote_weight[a] += 0.15
        if check_special_number(a):
            vote_weight[a] += 0.10

    best_answer = max(vote_weight, key=vote_weight.get)
    total_weight = sum(vote_weight.values())
    best_weight  = vote_weight[best_answer]
    confidence   = best_weight / total_weight if total_weight > 0 else 0.0

    # Stage 3 — MR level
    if len(valid) == 1:
        mr_level = "MR1"
    elif confidence >= 0.7:
        mr_level = "MR2-Resolved"
    elif confidence >= 0.4:
        mr_level = "MR2-Tralse"
    else:
        mr_level = "MR3-Indeterminate"

    return best_answer, confidence, mr_level


# ─────────────────────────────────────────────
# MAIN SOLVER
# ─────────────────────────────────────────────

class TISigmaSolver:
    """
    Full TI Sigma AIMO solver pipeline.
    
    Parameters
    ----------
    n_passes : int
        Number of independent LLM calls per problem (MR collapse across passes).
    backend : str
        'anthropic' (Claude) or 'openai' (GPT-4o).
    fallback_backend : str
        Second backend to use if primary fails.
    verbose : bool
        Print detailed logs.
    """

    def __init__(
        self,
        n_passes: int = 3,
        backend: str = "anthropic",
        fallback_backend: str = "openai",
        verbose: bool = True,
    ):
        self.n_passes = n_passes
        self.backend  = backend
        self.fallback_backend = fallback_backend
        self.verbose  = verbose

    def _log(self, *args):
        if self.verbose:
            print(*args)

    def solve(self, problem: str, problem_id: Optional[str] = None) -> dict:
        """
        Solve one problem.
        
        Returns dict with keys:
          answer, confidence, mr_level, problem_type,
          raw_answers, validation, reasoning_traces
        """
        pid = problem_id or "?"
        problem_type = classify_problem(problem)
        self._log(f"\n{'='*60}")
        self._log(f"Problem {pid} | Type: {problem_type}")
        self._log(problem[:120], "..." if len(problem) > 120 else "")

        answers: list[Optional[int]] = []
        confidences: list[float]     = []
        traces: list[str]            = []

        for attempt in range(1, self.n_passes + 1):
            self._log(f"  → Pass {attempt}/{self.n_passes}")
            user_prompt = build_tralse_prompt(problem, problem_type, attempt)

            # Primary backend
            response = call_llm(TRALSE_COT_SYSTEM, user_prompt, max_tokens=2048, backend=self.backend)
            if response.startswith("[ERROR"):
                self._log(f"    Primary backend error: {response} — trying fallback")
                response = call_llm(TRALSE_COT_SYSTEM, user_prompt, max_tokens=2048, backend=self.fallback_backend)

            traces.append(response)
            answer = extract_answer_from_text(response)

            if answer is not None:
                validation = validate_answer(answer, problem_type)
                conf       = validation['confidence']
                self._log(f"    Answer: {answer}  |  Confidence: {conf:.2f}  |  {validation['primary_constant'][1] or ''}")
            else:
                conf = 0.0
                self._log(f"    Could not extract answer from response")

            answers.append(answer)
            confidences.append(conf)

            # Small delay to avoid rate limits
            if attempt < self.n_passes:
                time.sleep(1.5)

        # MR Collapse
        final_answer, final_conf, mr_level = mr_collapse(answers, confidences)
        self._log(f"  MR Collapse → Answer: {final_answer}  |  Confidence: {final_conf:.2f}  |  Level: {mr_level}")

        # Final validation
        validation = validate_answer(final_answer, problem_type) if final_answer is not None else {}

        return {
            'problem_id':   pid,
            'problem_type': problem_type,
            'answer':       final_answer if final_answer is not None else 0,
            'confidence':   final_conf,
            'mr_level':     mr_level,
            'raw_answers':  answers,
            'validation':   validation,
            'reasoning_traces': traces,
        }

    def solve_batch(self, problems: list[dict], id_col: str = 'id', text_col: str = 'problem') -> list[dict]:
        """
        Solve a batch of problems.
        Each item in problems must have at least {id_col, text_col} keys.
        Returns list of result dicts.
        """
        results = []
        for i, row in enumerate(problems):
            pid     = row.get(id_col, str(i))
            problem = row.get(text_col, '')
            result  = self.solve(problem, problem_id=pid)
            results.append(result)
        return results


# ─────────────────────────────────────────────
# DEMO (run locally)
# ─────────────────────────────────────────────

DEMO_PROBLEMS = [
    {
        'id': 'DEMO-1',
        'problem': "Find the number of positive integers n ≤ 100 such that n² + n + 41 is prime.",
    },
    {
        'id': 'DEMO-2',
        'problem': "A triangle has sides 3, 4, 5. A second triangle is formed by connecting the midpoints of the sides of the first triangle. What is the area of the second triangle?",
    },
    {
        'id': 'DEMO-3',
        'problem': "How many integers from 1 to 1000 are divisible by 3 but not by 9?",
    },
]


if __name__ == "__main__":
    print("TI Sigma AIMO Solver — Demo Mode")
    print("=" * 60)

    solver = TISigmaSolver(n_passes=1, verbose=True)

    for prob in DEMO_PROBLEMS:
        result = solver.solve(prob['problem'], prob['id'])
        print(f"\n  FINAL: Problem {result['problem_id']} → Answer = {result['answer']}")
        val = result['validation']
        if val.get('primary_constant', (False,))[0]:
            print(f"  PRIMARY CONSTANT HIT: {val['primary_constant'][1]}")
        if val.get('special_number'):
            print(f"  SPECIAL NUMBER: {val['special_number']}")
        print(f"  MR Level: {result['mr_level']} | Confidence: {result['confidence']:.2f}")
