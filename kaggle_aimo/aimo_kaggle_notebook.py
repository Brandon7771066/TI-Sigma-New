"""
AIMO PP3 — TI Sigma Kaggle Submission Notebook
================================================
To run on Kaggle:
  1. Upload this file as a dataset or paste into notebook cells
  2. Add ANTHROPIC_API_KEY (or OPENAI_API_KEY) via Kaggle Secrets
  3. Set KAGGLE_MODE = True
  4. Run all cells

Competition: ai-mathematical-olympiad-progress-prize-3
Submission:  submission.csv with columns [id, answer]

Brandon Emerick | TI Sigma Framework | April 2026
"""

# ─────────────────────────────────────────────
# CONFIGURATION
# ─────────────────────────────────────────────
KAGGLE_MODE     = False          # True on Kaggle, False locally
N_PASSES        = 3              # MR collapse passes per problem (3 recommended)
BACKEND         = "anthropic"    # "anthropic" | "openai"
FALLBACK        = "openai"
MAX_PROBLEMS    = None           # None = all; integer = limit (for testing)
VERBOSE         = True

# Kaggle data paths
KAGGLE_DATA_DIR = "/kaggle/input/ai-mathematical-olympiad-progress-prize-3"
LOCAL_DATA_DIR  = "kaggle_aimo/data"

# ─────────────────────────────────────────────
# CELL 1: IMPORTS AND DEPENDENCIES
# ─────────────────────────────────────────────
import os
import sys
import json
import math
import re
import time
import pandas as pd
from pathlib import Path
from typing import Optional
from collections import Counter

# Add solver to path
solver_path = "/kaggle/working" if KAGGLE_MODE else os.path.dirname(os.path.dirname(__file__))
if solver_path not in sys.path:
    sys.path.insert(0, solver_path)

# Install dependencies if in Kaggle
if KAGGLE_MODE:
    os.system("pip install anthropic -q")

print("TI Sigma AIMO Solver — Initializing")
print(f"Mode: {'Kaggle' if KAGGLE_MODE else 'Local'}")
print(f"Backend: {BACKEND} | Passes: {N_PASSES}")


# ─────────────────────────────────────────────
# CELL 2: TI SIGMA SOLVER (INLINE COPY)
# ─────────────────────────────────────────────
# Self-contained solver (no external file dependency)

PHI   = (1 + math.sqrt(5)) / 2
SQRT2 = math.sqrt(2)
SQRT3 = math.sqrt(3)
SQRT5 = math.sqrt(5)
E_    = math.e
PI    = math.pi
C_    = 1 / (PHI * SQRT2)
T_    = 1 - math.exp(-E_)
ET_   = SQRT2 - 1

PRIMARY_CONSTANTS = {
    'sqrt2':  SQRT2,   'phi':  PHI,    'e': E_,     'pi': PI,
    'C':      C_,      'phi2': PHI**2, 'sqrt3': SQRT3, 'sqrt5': SQRT5,
    '4_3':    4/3,     '3_2':  3/2,    '2_3': 2/3,
    'pi_4':   PI/4,    'pi_2': PI/2,   '2pi': 2*PI,
    'ln2':    math.log(2), 'T': T_,    'ET': ET_,
}

FIBONACCI  = [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765,10946]
CATALAN    = [1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900]
LUCAS      = [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207,3571,5778]
BELL       = [1,1,2,5,15,52,203,877,4140,21147,115975]
TRIANGULAR = [n*(n+1)//2 for n in range(200)]


def pc_check(x: float) -> tuple[bool, Optional[str]]:
    if not isinstance(x, (int, float)) or math.isnan(x) or math.isinf(x):
        return False, None
    for name, val in PRIMARY_CONSTANTS.items():
        for mult in [0.5, 1, 2, 3, 4, 5, 6, 8, 10, 12, 24, 60, 100, 360]:
            target = val * mult
            if target == 0: continue
            if abs(x - target) / target < 0.01:
                return True, f"{x:.5g} ≈ {mult}×{name}={target:.5g}"
    return False, None


def special_check(x: float) -> Optional[str]:
    xi = int(round(x))
    if abs(x - xi) > 0.001: return None
    if xi in FIBONACCI:  return f"Fibonacci"
    if xi in CATALAN:    return f"Catalan"
    if xi in LUCAS:      return f"Lucas"
    if xi in BELL:       return f"Bell"
    if xi in TRIANGULAR: return f"Triangular"
    if xi > 0 and (xi & (xi-1)) == 0: return f"PowerOf2"
    return None


def classify(problem: str) -> str:
    t = problem.lower()
    if any(w in t for w in ['circle','triangle','polygon','angle','radius','area','chord','tangent']): return 'geometry'
    if any(w in t for w in ['prime','divisor','gcd','lcm','remainder','modulo','digit','factor']): return 'number_theory'
    if any(w in t for w in ['sequence','series','count','ways','arrange','choose','subset','permutation','combination','probability']): return 'combinatorics'
    return 'algebra'


def extract_int(text: str) -> Optional[int]:
    m = re.search(r'\\boxed\{(\-?\d+(?:\.\d+)?)\}', text)
    if m: return int(round(float(m.group(1))))
    for p in [r'(?:the\s+)?answer\s+is\s+(\-?\d+)', r'(?:final\s+)?answer\s*[:=]\s*(\-?\d+)',
              r'=\s*(\-?\d+)\s*$', r'\*\*(\-?\d+)\*\*']:
        m = re.search(p, text, re.IGNORECASE | re.MULTILINE)
        if m: return int(m.group(1))
    nums = re.findall(r'(?<!\d)(\-?\d+)(?!\d)', text)
    return int(nums[-1]) if nums else None


def confidence(answer: int, ptype: str) -> float:
    c = 0.4
    is_pc, _ = pc_check(answer)
    if is_pc: c += 0.25
    if special_check(answer): c += 0.15
    if 0 <= answer <= 999: c += 0.10
    return min(c, 1.0)


TRALSE_SYSTEM = """You are a world-class mathematical olympiad solver.
Use this exact structure:
1. TRUE POLE: Direct interpretation.
2. FALSE POLE: Hidden constraint or edge case.
3. MYRION SYNTHESIS: Combine both to find the correct formulation.
4. CALCULATION: Step-by-step arithmetic.
5. PRIMARY CHECK: Is the answer near √2, φ, e, π, or a Fibonacci/Catalan number?
6. FINAL ANSWER: \\boxed{integer_answer}

The final answer must be a non-negative integer."""


def build_prompt(problem: str, ptype: str, attempt: int) -> str:
    hints = {
        'geometry':      "GEOMETRY: Use similarity, power of a point, trig. Answers near π or √2×integer.",
        'number_theory': "NUMBER THEORY: Use mod arithmetic, CRT, Euler theorem. Check Fibonacci/Bell.",
        'combinatorics': "COMBINATORICS: Use inclusion-exclusion, bijection. Answers often Catalan/Fibonacci.",
        'algebra':       "ALGEBRA: Use AM-GM, Cauchy-Schwarz, substitution. Look for elegant factorizations.",
    }
    note = ""
    if attempt == 2: note = "\nNOTE: Attempt 2 — double-check arithmetic and verify all constraints."
    if attempt >= 3: note = "\nNOTE: Attempt 3 — try a completely different approach from scratch."
    return f"{hints.get(ptype, '')}{note}\n\nProblem: {problem}"


def call_anthropic_api(system: str, user: str) -> str:
    try:
        import anthropic
        client = anthropic.Anthropic()
        msg = client.messages.create(
            model="claude-opus-4-5",
            max_tokens=2048,
            system=system,
            messages=[{"role": "user", "content": user}]
        )
        return msg.content[0].text
    except Exception as ex:
        return f"[ERROR:{ex}]"


def call_openai_api(system: str, user: str) -> str:
    try:
        from openai import OpenAI
        client = OpenAI()
        r = client.chat.completions.create(
            model="gpt-4o",
            messages=[{"role": "system", "content": system}, {"role": "user", "content": user}],
            max_tokens=2048, temperature=0.2,
        )
        return r.choices[0].message.content
    except Exception as ex:
        return f"[ERROR:{ex}]"


def call_api(system: str, user: str, backend: str = "anthropic") -> str:
    if backend == "anthropic":
        r = call_anthropic_api(system, user)
        if r.startswith("[ERROR"): r = call_openai_api(system, user)
        return r
    return call_openai_api(system, user)


def mr_collapse(answers: list, confs: list) -> tuple:
    valid = [(a, c) for a, c in zip(answers, confs) if a is not None]
    if not valid: return 0, 0.0, "DT"
    weights: dict = {}
    for a, c in valid:
        weights[a] = weights.get(a, 0) + c
        if pc_check(a)[0]:       weights[a] += 0.15
        if special_check(a):     weights[a] += 0.10
    best = max(weights, key=weights.get)
    total = sum(weights.values())
    conf  = weights[best] / total if total else 0.0
    level = "MR2-Resolved" if conf >= 0.7 else "MR2-Tralse" if conf >= 0.4 else "MR3-Indeterminate"
    return best, conf, level


def solve_problem(problem: str, pid: str = "?", n_passes: int = 3, backend: str = "anthropic") -> dict:
    ptype = classify(problem)
    if VERBOSE: print(f"\n[{pid}] type={ptype}")
    answers, confs = [], []
    for attempt in range(1, n_passes + 1):
        prompt = build_prompt(problem, ptype, attempt)
        response = call_api(TRALSE_SYSTEM, prompt, backend)
        a = extract_int(response)
        c = confidence(a, ptype) if a is not None else 0.0
        answers.append(a)
        confs.append(c)
        if VERBOSE: print(f"  Pass {attempt}: answer={a}, conf={c:.2f}")
        if attempt < n_passes: time.sleep(1.0)
    final, conf, level = mr_collapse(answers, confs)
    if VERBOSE:
        is_pc, pc_str = pc_check(final) if final else (False, None)
        sn = special_check(final) if final else None
        print(f"  → FINAL: {final} | {level} | conf={conf:.2f}{' | '+pc_str if is_pc else ''}{' | '+sn if sn else ''}")
    return {'id': pid, 'answer': final, 'confidence': conf, 'mr_level': level, 'problem_type': ptype}


# ─────────────────────────────────────────────
# CELL 3: LOAD DATA
# ─────────────────────────────────────────────

def load_problems() -> pd.DataFrame:
    """Load competition problems from CSV."""
    # Kaggle environment
    if KAGGLE_MODE:
        data_dir = KAGGLE_DATA_DIR
    else:
        data_dir = LOCAL_DATA_DIR

    # Try multiple file name patterns used across AIMO editions
    for fname in ['train.csv', 'test.csv', 'sample_submission.csv', 'problems.csv']:
        fpath = Path(data_dir) / fname
        if fpath.exists():
            df = pd.read_csv(fpath)
            print(f"Loaded {len(df)} rows from {fpath}")
            print(f"Columns: {list(df.columns)}")
            return df

    # Demo fallback
    print("WARNING: No data file found. Running with demo problems.")
    demo = [
        {'id': 'DEMO-1', 'problem': "Find the number of positive integers n ≤ 100 where n²+n+41 is prime."},
        {'id': 'DEMO-2', 'problem': "A triangle has sides 3, 4, 5. What is the area of the medial triangle?"},
        {'id': 'DEMO-3', 'problem': "How many integers from 1 to 1000 are divisible by 3 but not by 9?"},
    ]
    return pd.DataFrame(demo)


# ─────────────────────────────────────────────
# CELL 4: DETECT COLUMN NAMES
# ─────────────────────────────────────────────

def detect_columns(df: pd.DataFrame) -> tuple[str, str]:
    """Detect id and problem text column names."""
    id_col   = next((c for c in df.columns if c.lower() in ['id', 'problem_id', 'idx']), df.columns[0])
    text_col = next((c for c in df.columns if c.lower() in ['problem', 'question', 'text', 'prompt']), df.columns[1])
    return id_col, text_col


# ─────────────────────────────────────────────
# CELL 5: RUN SOLVER
# ─────────────────────────────────────────────

def run_full_pipeline():
    df = load_problems()
    id_col, text_col = detect_columns(df)

    if MAX_PROBLEMS:
        df = df.head(MAX_PROBLEMS)

    print(f"\nSolving {len(df)} problems | id_col='{id_col}' | text_col='{text_col}'")
    print("=" * 60)

    results = []
    for _, row in df.iterrows():
        pid     = str(row[id_col])
        problem = str(row[text_col])
        result  = solve_problem(problem, pid=pid, n_passes=N_PASSES, backend=BACKEND)
        results.append(result)

    return pd.DataFrame(results)


# ─────────────────────────────────────────────
# CELL 6: BUILD SUBMISSION
# ─────────────────────────────────────────────

def build_submission(results_df: pd.DataFrame) -> pd.DataFrame:
    """Build the submission.csv in Kaggle format."""
    submission = results_df[['id', 'answer']].copy()
    submission['answer'] = submission['answer'].fillna(0).astype(int)
    return submission


# ─────────────────────────────────────────────
# CELL 7: MAIN ENTRY POINT
# ─────────────────────────────────────────────

if __name__ == "__main__":
    print("\n" + "=" * 60)
    print("TI Sigma AIMO PP3 Solver")
    print("Five-Valued Tralse Logic + Myrion Resolution")
    print("=" * 60)

    # Validate API
    test_resp = call_api("Say OK.", "Just say OK.", BACKEND)
    if test_resp.startswith("[ERROR"):
        print(f"WARNING: Primary backend ({BACKEND}) failed: {test_resp}")
        print(f"Falling back to {FALLBACK}")
        BACKEND = FALLBACK

    # Run
    results_df  = run_full_pipeline()
    submission  = build_submission(results_df)

    # Save
    out_path = "/kaggle/working/submission.csv" if KAGGLE_MODE else "kaggle_aimo/submission_aimo_pp3.csv"
    submission.to_csv(out_path, index=False)
    print(f"\nSubmission saved → {out_path}")
    print(submission.head(20).to_string())

    # Summary stats
    print("\n" + "=" * 60)
    print("MR COLLAPSE SUMMARY")
    print(f"  Resolved  (≥0.7 conf): {len(results_df[results_df['confidence'] >= 0.7])}")
    print(f"  Tralse    (0.4–0.7):   {len(results_df[(results_df['confidence'] >= 0.4) & (results_df['confidence'] < 0.7)])}")
    print(f"  Indeter.  (<0.4):      {len(results_df[results_df['confidence'] < 0.4])}")
    print(f"  DT (None answers):     {(submission['answer'] == 0).sum()} (defaulted to 0)")

    type_counts = results_df['problem_type'].value_counts()
    print(f"\nProblem types: {type_counts.to_dict()}")
