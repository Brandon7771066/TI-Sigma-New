
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
# STEP 6 — RUN: GATEWAY MODE (real submission) or CSV FALLBACK
# ══════════════════════════════════════════════════════════
#
# HOW AIMO3 WORKS:
#   The competition does NOT score your submission.csv directly.
#   Instead, Kaggle runs a local evaluation server that streams real
#   problems to your notebook one at a time via the AIMO3Gateway client.
#   Your predict() function is called for each problem; Kaggle records
#   every answer in real time.
#
#   test.csv contains only 3 trivial warm-up problems (1-1, 0×10, x=0).
#   Those are correct — they are literally placeholders to verify your
#   notebook runs. The actual olympiad problems come through the gateway.
#
# EXECUTION MODES (auto-detected):
#   A) GATEWAY MODE  — kaggle_evaluation package is importable (real run)
#                      → predict() called per problem, scored live
#   B) REFERENCE CSV — gateway unavailable, reference.csv has real problems
#                      → useful for offline tuning against known answers
#   C) DEMO MODE     — nothing else available → 5 built-in hard problems

print("\n[6/6] Running solver...")

import os, sys

# ── Diagnostic: list all available files ──────────────────
kaggle_input = Path("/kaggle/input")
all_files = []
if kaggle_input.exists():
    for root, dirs, files in os.walk(kaggle_input):
        for f in files:
            all_files.append(Path(root) / f)
    print(f"      Files under /kaggle/input/ ({len(all_files)} total):")
    for f in sorted(all_files)[:40]:
        print(f"        {f}")
    if len(all_files) > 40:
        print(f"        ... and {len(all_files)-40} more")

# ── Configuration ─────────────────────────────────────────
N_PASSES     = 3      # Claude calls per problem (3 = most reliable)
MAX_PROBLEMS = None   # None = all; set e.g. 5 for a quick local test

# ── The predict function: called by gateway OR the fallback loop ──
_results_log = []   # accumulated for summary at end

def predict(id_: str, problem: str) -> int:
    """Solve one problem. Returns integer answer. Called by AIMO3Gateway."""
    result = solve_one(str(problem), str(id_), n_passes=N_PASSES)
    _results_log.append(result)
    return int(result['answer'])

# ══════════════════════════════════════════════════════════
# MODE A — GATEWAY (live competition evaluation)
# ══════════════════════════════════════════════════════════
GATEWAY_AVAILABLE = False
try:
    # Add the competition's kaggle_evaluation package to the path
    for search_root in ["/kaggle/input/competitions", "/kaggle/input/datasets"]:
        for root, dirs, files in os.walk(search_root):
            if "aimo_3_gateway.py" in files:
                pkg_parent = str(Path(root).parent)
                if pkg_parent not in sys.path:
                    sys.path.insert(0, pkg_parent)
                break

    from kaggle_evaluation.aimo_3_gateway import AIMO3Gateway
    GATEWAY_AVAILABLE = True
except ImportError:
    pass

if GATEWAY_AVAILABLE:
    print("\n      ✓ GATEWAY MODE — Kaggle evaluation server detected")
    print("        Real olympiad problems will be streamed to predict().")
    print("        Submitting via gateway now...\n")
    print("=" * 60)

    gateway = AIMO3Gateway(predict)
    gateway.run()   # blocks until all problems are answered; Kaggle scores live

    print("\n" + "=" * 60)
    print("GATEWAY RUN COMPLETE")
    print("=" * 60)

# ══════════════════════════════════════════════════════════
# MODE B — REFERENCE CSV (offline tuning)
# ══════════════════════════════════════════════════════════
else:
    print("\n      Gateway not available — falling back to CSV mode.")

    # Find reference.csv (has real problems + answers for offline validation)
    ref_candidates = [
        f for f in all_files
        if f.suffix.lower() == '.csv' and 'reference' in f.name.lower()
    ]
    demo_candidates = [
        f for f in all_files
        if f.suffix.lower() == '.csv'
        and 'sample_submission' not in f.name.lower()
        and 'reference' not in f.name.lower()
        and 'test' not in f.name.lower()
    ]

    CSV_FILE = None
    if ref_candidates:
        # Prefer the competition's own reference over dataset copies
        comp_refs = [f for f in ref_candidates if 'competitions' in str(f)]
        CSV_FILE = comp_refs[0] if comp_refs else ref_candidates[0]
        print(f"      ✓ Using reference CSV: {CSV_FILE.name}")
        print("        (Contains real problems with known answers — good for tuning)")
    elif demo_candidates:
        CSV_FILE = demo_candidates[0]
        print(f"      ✓ Using CSV: {CSV_FILE.name}")

    if CSV_FILE:
        df = pd.read_csv(CSV_FILE)
        print(f"        Columns: {list(df.columns)} | Rows: {len(df)}")
        # Show a snippet so we can confirm problem content
        id_col   = next((c for c in df.columns if c.lower() in ['id','problem_id']), df.columns[0])
        text_col = next((c for c in df.columns if c.lower() in ['problem','question','text','prompt']), None)
        if text_col is None:
            # Pick longest-average-text column that isn't id/answer/solution
            skip = {'id','answer','label','target','solution','answer_value'}
            text_col = max(
                (c for c in df.columns if c.lower() not in skip),
                key=lambda c: df[c].dropna().astype(str).str.len().mean(),
                default=df.columns[-1]
            )
        print(f"        id='{id_col}' | problem='{text_col}'")
        print(f"        Sample: {str(df[text_col].iloc[0])[:120]}")

        solve_df = df.head(MAX_PROBLEMS) if MAX_PROBLEMS else df
        print(f"\nSolving {len(solve_df)} problem(s) with {N_PASSES} passes each...")
        print("=" * 60)

        for _, row in solve_df.iterrows():
            predict(str(row[id_col]), str(row[text_col]))

    else:
        # ── MODE C: DEMO ──────────────────────────────────────
        print("\n      ! No CSV found — running 5 built-in demo problems")
        DEMO_PROBLEMS = [
            ("demo_1", "How many positive integers n ≤ 100 satisfy φ(n) < n/2, where φ is Euler's totient function?"),
            ("demo_2", "Find the number of ordered pairs (a,b) of positive integers with a+b=100 and gcd(a,b)=4."),
            ("demo_3", "A circle of radius 3 is inscribed in a right triangle. If one leg has length 12, find the hypotenuse."),
            ("demo_4", "How many 6-digit integers contain exactly three distinct digits?"),
            ("demo_5", "Find the sum of all integers n such that n²+20n+26 is a perfect square."),
        ]
        print("=" * 60)
        for pid, problem in DEMO_PROBLEMS:
            predict(pid, problem)

    # ── Save submission CSV (fallback modes only) ─────────
    if _results_log:
        results_df = pd.DataFrame(_results_log)
        submission = results_df[['id', 'answer']].copy()
        submission['answer'] = submission['answer'].fillna(0).astype(int)
        out = "/kaggle/working/submission.csv"
        submission.to_csv(out, index=False)
        print("\n" + "=" * 60)
        print(f"DONE — submission saved to {out}")
        print("=" * 60)
        print(submission.to_string())

# ── Summary (all modes) ───────────────────────────────────
if _results_log:
    results_df = pd.DataFrame(_results_log)
    print(f"\nMR LEVEL BREAKDOWN:")
    for level, count in results_df['mr_level'].value_counts().items():
        print(f"  {level}: {count}")
    print(f"\nTYPE BREAKDOWN:")
    for ptype, count in results_df['problem_type'].value_counts().items():
        print(f"  {ptype}: {count}")
    print(f"\nMean confidence: {results_df['confidence'].mean():.2f}")

print("\n" + "=" * 60)
print("NOTE: In GATEWAY MODE, Kaggle scores answers live — no CSV submit needed.")
print("      In CSV/DEMO MODE, click 'Submit' top-right to submit submission.csv.")
print("=" * 60)
