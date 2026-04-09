
"""
AIMO PP3 — TI Sigma Kaggle Submission Notebook
================================================
PASTE THIS ENTIRE FILE INTO A SINGLE KAGGLE CELL. Then click Run All.

Prerequisites (all done in the Kaggle UI before running):
  1. Add-ons → Secrets → Add secret named "Anthropic_Api_Key" (your Anthropic key)
  2. Enable "Attach to notebook" toggle for the secret
  3. Competition data attached as input dataset (or run in demo mode)

Competition: ai-mathematical-olympiad-progress-prize-3
Output:      /kaggle/working/submission.csv  [id, answer]

Brandon Emerick | TI Sigma Framework | April 2026
"""

# ══════════════════════════════════════════════════════════
# STEP 1 — INSTALL DEPENDENCIES
# ══════════════════════════════════════════════════════════
print("=" * 60)
print("TI SIGMA AIMO SOLVER — STARTING")
print("=" * 60)

import subprocess, sys
print("\n[1/6] Installing anthropic...")
subprocess.run([sys.executable, "-m", "pip", "install", "anthropic", "--quiet"], check=False)
print("      Done.")

# ══════════════════════════════════════════════════════════
# STEP 2 — LOAD KAGGLE SECRET → SET ENV VAR
# ══════════════════════════════════════════════════════════
import os

print("\n[2/6] Loading API key from Kaggle Secrets...")

# Kaggle Secrets require explicit loading via UserSecretsClient.
# The secret name must match EXACTLY what you typed in Add-ons → Secrets.
# We try several common spellings so it works regardless of how you named it.

ANTHROPIC_KEY = None

# --- Primary: Kaggle environment ---
try:
    from kaggle_secrets import UserSecretsClient
    client = UserSecretsClient()
    for name in ["Anthropic_Api_Key", "ANTHROPIC_API_KEY", "anthropic_api_key",
                 "AnthropicApiKey", "anthropic", "ANTHROPIC_KEY"]:
        try:
            ANTHROPIC_KEY = client.get_secret(name)
            if ANTHROPIC_KEY:
                print(f"      ✓ Found Anthropic key under secret name '{name}'")
                break
        except Exception:
            pass
except ImportError:
    print("      (Not in Kaggle environment — looking for local env var)")

# --- Fallback: local environment variable ---
if not ANTHROPIC_KEY:
    ANTHROPIC_KEY = os.environ.get("ANTHROPIC_API_KEY", "")

if ANTHROPIC_KEY:
    os.environ["ANTHROPIC_API_KEY"] = ANTHROPIC_KEY
    masked = ANTHROPIC_KEY[:8] + "..." + ANTHROPIC_KEY[-4:]
    print(f"      ✓ ANTHROPIC_API_KEY set ({masked})")
else:
    print("      ✗ WARNING: No Anthropic API key found!")
    print("        → Make sure your secret name is 'Anthropic_Api_Key' in Kaggle Secrets")
    print("        → Make sure 'Attach to notebook' is toggled ON for the secret")
    print("        → The notebook will continue in DEMO mode (no real API calls)")

# ══════════════════════════════════════════════════════════
# STEP 3 — CORE IMPORTS
# ══════════════════════════════════════════════════════════
print("\n[3/6] Importing libraries...")
import math, re, time, json
from pathlib import Path
from typing import Optional
import pandas as pd
print("      ✓ All imports OK")

# ══════════════════════════════════════════════════════════
# STEP 4 — TI SIGMA MATH ENGINE
# ══════════════════════════════════════════════════════════
print("\n[4/6] Building TI Sigma math engine...")

# --- PRIMARY CONSTANTS ---
PHI   = (1 + math.sqrt(5)) / 2
SQRT2 = math.sqrt(2)
SQRT3 = math.sqrt(3)
SQRT5 = math.sqrt(5)
E_    = math.e
PI    = math.pi
C_    = 1 / (PHI * SQRT2)

PRIMARY_CONSTANTS = {
    'sqrt2': SQRT2, 'phi': PHI,    'e': E_,   'pi': PI,
    'C':     C_,    'phi2': PHI**2, 'sqrt3': SQRT3,
    '4_3':   4/3,   '3_2': 3/2,    'pi_2': PI/2,
    '2pi':   2*PI,  'ln2': math.log(2),
}

FIBONACCI  = [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765]
CATALAN    = [1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012]
LUCAS      = [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207,3571]
BELL       = [1,1,2,5,15,52,203,877,4140,21147,115975]
TRIANGULAR = [n*(n+1)//2 for n in range(200)]

def pc_check(x):
    """Check if x is near a PRIMARY CONSTANT × simple multiplier."""
    if not isinstance(x, (int, float)) or math.isnan(x) or math.isinf(x): return False, None
    for name, val in PRIMARY_CONSTANTS.items():
        for mult in [0.5, 1, 2, 3, 4, 5, 6, 8, 10, 12, 24, 60, 100, 360]:
            t = val * mult
            if t > 0 and abs(x - t) / t < 0.01:
                return True, f"{x} ≈ {mult}×{name}={t:.5g}"
    return False, None

def special_check(x):
    """Check if x is a combinatorially special number."""
    xi = int(round(x))
    if abs(x - xi) > 0.001: return None
    if xi in FIBONACCI:  return "Fibonacci"
    if xi in CATALAN:    return "Catalan"
    if xi in LUCAS:      return "Lucas"
    if xi in BELL:       return "Bell"
    if xi in TRIANGULAR: return "Triangular"
    if xi > 1 and (xi & (xi-1)) == 0: return "PowerOf2"
    return None

def classify(problem):
    """Classify problem domain from keywords."""
    t = problem.lower()
    if any(w in t for w in ['circle','triangle','polygon','angle','radius','area','chord','tangent','square','rectangle']): return 'geometry'
    if any(w in t for w in ['prime','divisor','gcd','lcm','remainder','modulo','digit','factor','integer','divisible']): return 'number_theory'
    if any(w in t for w in ['sequence','count','ways','arrange','choose','subset','permutation','combination','probability','choose']): return 'combinatorics'
    return 'algebra'

def extract_int(text):
    """Extract the final integer answer from LLM output."""
    # LaTeX boxed answer (highest priority)
    m = re.search(r'\\boxed\{(\-?\d+(?:\.\d+)?)\}', text)
    if m: return int(round(float(m.group(1))))
    # Common answer phrases
    for p in [r'(?:the\s+)?answer\s+is\s+(\-?\d+)',
              r'(?:final\s+)?answer\s*[:=]\s*(\-?\d+)',
              r'(?:result|value)\s+is\s+(\-?\d+)',
              r'\*\*(\d+)\*\*']:
        m = re.search(p, text, re.IGNORECASE)
        if m: return int(m.group(1))
    # Last standalone integer in the response
    nums = re.findall(r'(?<!\d)(\-?\d+)(?!\d)', text)
    return int(nums[-1]) if nums else None

def answer_confidence(a, ptype):
    """Score confidence of a candidate answer using TI Sigma heuristics."""
    if a is None: return 0.0
    c = 0.4
    if pc_check(a)[0]: c += 0.25
    if special_check(a): c += 0.15
    if 0 <= a <= 999: c += 0.10
    return min(c, 1.0)

def mr_collapse(answers, confs):
    """Myrion Resolution: weighted majority vote over N candidate answers."""
    valid = [(a, c) for a, c in zip(answers, confs) if a is not None]
    if not valid: return 0, 0.0, "DT"
    weights = {}
    for a, c in valid:
        weights[a] = weights.get(a, 0) + c
        if pc_check(a)[0]:    weights[a] += 0.15
        if special_check(a):  weights[a] += 0.10
    best  = max(weights, key=weights.get)
    total = sum(weights.values())
    conf  = weights[best] / total
    level = "MR2-Resolved" if conf >= 0.7 else "MR2-Tralse" if conf >= 0.4 else "MR3-Indeterminate"
    return best, conf, level

print("      ✓ Math engine ready")

# ══════════════════════════════════════════════════════════
# STEP 5 — LLM INTERFACE
# ══════════════════════════════════════════════════════════
print("\n[5/6] Setting up LLM interface...")

SYSTEM_PROMPT = """You are a world-class mathematical olympiad solver.

Solve the problem using this EXACT structure:
1. TRUE POLE: The most direct interpretation of the problem.
2. FALSE POLE: The hidden constraint, edge case, or trick beginners miss.
3. MYRION SYNTHESIS: Combine both poles to find the correct formulation.
4. CALCULATION: Careful, step-by-step arithmetic.
5. VERIFY: Check the answer satisfies ALL stated conditions.
6. FINAL ANSWER: State the integer answer as \\boxed{N}

The final answer must be a non-negative integer."""

TYPE_HINTS = {
    'geometry':     "GEOMETRY problem — use similarity, power of a point, area formulas.",
    'number_theory':"NUMBER THEORY — use modular arithmetic, prime factorization, CRT.",
    'combinatorics':"COMBINATORICS — use inclusion-exclusion, bijections, generating functions.",
    'algebra':      "ALGEBRA — use AM-GM, Cauchy-Schwarz, substitution.",
}

def call_claude(problem, ptype, attempt=1):
    """Call Claude claude-opus-4-5 with Tralse chain-of-thought prompt."""
    try:
        import anthropic
        aclient = anthropic.Anthropic()  # reads ANTHROPIC_API_KEY from os.environ

        note = ""
        if attempt == 2: note = "\nNOTE — Attempt 2: double-check every arithmetic step."
        if attempt >= 3: note = "\nNOTE — Attempt 3: try a completely different approach."

        user = f"{TYPE_HINTS.get(ptype, '')}{note}\n\nProblem: {problem}"

        msg = aclient.messages.create(
            model="claude-opus-4-5",
            max_tokens=2048,
            system=SYSTEM_PROMPT,
            messages=[{"role": "user", "content": user}]
        )
        return msg.content[0].text
    except Exception as ex:
        return f"[CLAUDE_ERROR: {ex}]"

def demo_solve(problem):
    """Fallback solver when no API key is available — heuristic only."""
    # Simple pattern matching for demo purposes
    nums = re.findall(r'\d+', problem)
    if nums:
        n = int(nums[0])
        # Very basic: triangular number, Fibonacci, etc.
        return str(n % 1000)
    return "0"

def solve_one(problem, pid, n_passes=3):
    """Solve a single problem with MR collapse over N passes."""
    ptype = classify(problem)
    print(f"  [{pid}] {ptype} — {problem[:70]}{'...' if len(problem)>70 else ''}")

    if not ANTHROPIC_KEY:
        # Demo mode
        ans = 0
        print(f"       → DEMO MODE (no API key): answer = {ans}")
        return {'id': pid, 'answer': ans, 'confidence': 0.0, 'mr_level': 'DT', 'problem_type': ptype}

    answers, confs = [], []
    for attempt in range(1, n_passes + 1):
        response = call_claude(problem, ptype, attempt)
        if response.startswith("[CLAUDE_ERROR"):
            print(f"       Pass {attempt}: ERROR — {response}")
            answers.append(None); confs.append(0.0)
        else:
            a = extract_int(response)
            c = answer_confidence(a, ptype)
            answers.append(a); confs.append(c)
            pc_hit = pc_check(a)[1] if a is not None else None
            sn_hit = special_check(a) if a is not None else None
            print(f"       Pass {attempt}: {a}  conf={c:.2f}"
                  + (f"  [{pc_hit}]" if pc_hit else "")
                  + (f"  [{sn_hit}]" if sn_hit else ""))
        if attempt < n_passes: time.sleep(1.0)

    final, conf, level = mr_collapse(answers, confs)
    print(f"       → MR COLLAPSE: {final}  ({level}, conf={conf:.2f})")
    return {'id': pid, 'answer': final, 'confidence': conf, 'mr_level': level, 'problem_type': ptype}

print("      ✓ LLM interface ready")

# ══════════════════════════════════════════════════════════
# STEP 6 — LOAD DATA + RUN + SAVE SUBMISSION
# ══════════════════════════════════════════════════════════
print("\n[6/6] Loading competition data...")

# ── DIAGNOSTIC: show everything under /kaggle/input/ ──────
import os
kaggle_input = Path("/kaggle/input")
all_files = []
if kaggle_input.exists():
    for root, dirs, files in os.walk(kaggle_input):
        for f in files:
            all_files.append(Path(root) / f)
    if all_files:
        print(f"      Files found under /kaggle/input/ ({len(all_files)} total):")
        for f in sorted(all_files)[:40]:          # show up to 40
            print(f"        {f}")
        if len(all_files) > 40:
            print(f"        ... and {len(all_files)-40} more")
    else:
        print("      /kaggle/input/ exists but is EMPTY — dataset not attached yet")
else:
    print("      /kaggle/input/ does not exist (not in Kaggle environment?)")

# ── Find any CSV that could contain problems ──────────────
# Priority order: files with 'test'/'problem'/'question' in name first,
# then any CSV, regardless of folder depth.
DATA_FILE = None
csv_files = sorted([f for f in all_files if f.suffix.lower() == '.csv'])

PRIORITY_NAMES = ['test', 'problem', 'question', 'reference', 'train', 'sample']
for priority in PRIORITY_NAMES:
    for f in csv_files:
        if priority in f.name.lower():
            DATA_FILE = f
            break
    if DATA_FILE:
        break

# Last resort: just take the first CSV found
if not DATA_FILE and csv_files:
    DATA_FILE = csv_files[0]

if DATA_FILE:
    df = pd.read_csv(DATA_FILE)
    print(f"\n      ✓ Loaded {len(df)} rows from: {DATA_FILE}")
    print(f"        Columns: {list(df.columns)}")
    print(df.head(3).to_string())
else:
    print("\n      ! No CSV data found — running DEMO problems")
    print("        To attach competition data:")
    print("        1. Click the folder icon (Data) in the left sidebar")
    print("        2. Click 'Add Data' → 'Competition Datasets'")
    print("        3. Find 'AI Mathematical Olympiad - Progress Prize 3' → click +")
    print("        4. Run All again\n")
    df = pd.DataFrame([
        {'id': 'demo_1', 'problem': "How many positive integers n ≤ 100 satisfy: n² + n + 41 is prime?"},
        {'id': 'demo_2', 'problem': "A triangle has sides 3, 4, 5. What is the area of the triangle formed by connecting the midpoints of its sides?"},
        {'id': 'demo_3', 'problem': "How many integers from 1 to 1000 are divisible by 3 but not by 9?"},
        {'id': 'demo_4', 'problem': "Find the sum of all positive divisors of 120."},
        {'id': 'demo_5', 'problem': "In how many ways can 5 people be arranged in a row?"},
    ])

# Detect column names
id_col   = next((c for c in df.columns if c.lower() in ['id','problem_id','idx']), df.columns[0])
text_col = next((c for c in df.columns if c.lower() in ['problem','question','text','prompt']), df.columns[-1])
print(f"      id column: '{id_col}' | text column: '{text_col}'")

# How many to solve (set MAX_PROBLEMS = N to test with just N problems first)
MAX_PROBLEMS = None   # ← change to e.g. 5 to do a quick test run
N_PASSES     = 3      # ← number of Claude calls per problem (1 is fastest, 3 is most reliable)

solve_df = df.head(MAX_PROBLEMS) if MAX_PROBLEMS else df
print(f"\nSolving {len(solve_df)} problem(s) with {N_PASSES} passes each...")
print("=" * 60)

results = []
for _, row in solve_df.iterrows():
    pid     = str(row[id_col])
    problem = str(row[text_col])
    result  = solve_one(problem, pid, n_passes=N_PASSES)
    results.append(result)

# Build submission
results_df = pd.DataFrame(results)
submission = results_df[['id', 'answer']].copy()
submission['answer'] = submission['answer'].fillna(0).astype(int)

# Save
out = "/kaggle/working/submission.csv"
submission.to_csv(out, index=False)

print("\n" + "=" * 60)
print(f"DONE — submission saved to {out}")
print("=" * 60)
print(submission.to_string())

# Summary
print(f"\nMR LEVEL BREAKDOWN:")
for level, count in results_df['mr_level'].value_counts().items():
    print(f"  {level}: {count}")
print(f"\nTYPE BREAKDOWN:")
for ptype, count in results_df['problem_type'].value_counts().items():
    print(f"  {ptype}: {count}")
print(f"\nMean confidence: {results_df['confidence'].mean():.2f}")
print("\n✓ Submit submission.csv via the 'Submit' button in the top-right corner.")
