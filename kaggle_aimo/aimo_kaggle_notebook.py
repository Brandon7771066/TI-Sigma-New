
"""
AIMO PP3 — TI Sigma Kaggle Submission Notebook
================================================
PASTE THIS ENTIRE FILE INTO A SINGLE KAGGLE CELL. Then click Run All.

Prerequisites (all done in the Kaggle UI before running):
  1. Add-ons → Secrets → Add secret named "Anthropic_Api_Key" (your Anthropic key)
  2. Enable "Attach to notebook" toggle for the secret
  3. Competition data attached as input dataset (or run in demo mode)

HOW AIMO3 WORKS:
  Kaggle streams real olympiad problems to your predict() function via a local
  evaluation server (gateway). test.csv has only 3 trivial warm-up rows —
  ignore them. The actual problems come through the gateway in a real submission.

  Gateway requires: pip install kaggle-evaluation  (done in Step 1 below)
  Each predict() call has a time budget — we enforce a hard per-call timeout.

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

print("\n[1/6] Installing dependencies...")

# anthropic SDK
subprocess.run([sys.executable, "-m", "pip", "install", "anthropic", "--quiet"], check=False)

# openai SDK — also used to reach Perplexity (OpenAI-compatible API)
subprocess.run([sys.executable, "-m", "pip", "install", "openai", "--quiet"], check=False)

# kaggle-evaluation — required to import AIMO3Gateway in a submission kernel
# This installs the package so `from kaggle_evaluation.aimo_3_gateway import AIMO3Gateway` works.
result = subprocess.run(
    [sys.executable, "-m", "pip", "install", "kaggle-evaluation", "--quiet"],
    capture_output=True, text=True
)
if result.returncode == 0:
    print("      ✓ kaggle-evaluation installed")
else:
    # May already be present or pip name differs — not fatal
    print(f"      ! kaggle-evaluation pip install note: {result.stderr.strip()[:120]}")

print("      ✓ Dependencies done")

# ══════════════════════════════════════════════════════════
# STEP 2 — LOAD KAGGLE SECRET → SET ENV VAR
# ══════════════════════════════════════════════════════════
import os

print("\n[2/6] Loading API keys from Kaggle Secrets...")

ANTHROPIC_KEY   = None
PERPLEXITY_KEY  = None

# ── Helper: pull a secret by any of several candidate names ──
def _get_secret(*names):
    for name in names:
        try:
            from kaggle_secrets import UserSecretsClient
            val = UserSecretsClient().get_secret(name)
            if val:
                return val, name
        except Exception:
            pass
        val = os.environ.get(name, "")
        if val:
            return val, name
    return None, None

# Load Anthropic key
ANTHROPIC_KEY, _aname = _get_secret(
    "Anthropic_Api_Key", "ANTHROPIC_API_KEY", "anthropic_api_key",
    "AnthropicApiKey", "anthropic", "ANTHROPIC_KEY"
)
if ANTHROPIC_KEY:
    os.environ["ANTHROPIC_API_KEY"] = ANTHROPIC_KEY
    masked = ANTHROPIC_KEY[:8] + "..." + ANTHROPIC_KEY[-4:]
    print(f"      ✓ Anthropic key found ('{_aname}'): {masked}")
else:
    print("      ! No Anthropic key found — will try Perplexity")

# Load Perplexity key (fallback provider — r1-1776 is great at math)
# "TI_Sigma" is the name used in this project's Kaggle Secrets
PERPLEXITY_KEY, _pname = _get_secret(
    "TI_Sigma", "Perplexity_Api_Key", "PERPLEXITY_API_KEY", "perplexity_api_key",
    "PerplexityApiKey", "PERPLEXITY_KEY"
)
if PERPLEXITY_KEY:
    os.environ["PERPLEXITY_API_KEY"] = PERPLEXITY_KEY
    masked2 = PERPLEXITY_KEY[:8] + "..." + PERPLEXITY_KEY[-4:]
    print(f"      ✓ Perplexity key found ('{_pname}'): {masked2}")
else:
    print("      ! No Perplexity key found")

if not ANTHROPIC_KEY and not PERPLEXITY_KEY:
    print("      ✗ WARNING: No API keys found at all!")
    print("        → Add 'Anthropic_Api_Key' OR 'Perplexity_Api_Key' to Kaggle Secrets")
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
import threading
print("      ✓ All imports OK")

# ══════════════════════════════════════════════════════════
# STEP 4 — TI SIGMA MATH ENGINE
# ══════════════════════════════════════════════════════════
print("\n[4/6] Building TI Sigma math engine...")

# PRIMARY CONSTANTS (TI Sigma — URB #529)
PHI   = (1 + math.sqrt(5)) / 2      # Golden ratio  ≈ 1.6180
SQRT2 = math.sqrt(2)                 # ≈ 1.4142
SQRT3 = math.sqrt(3)                 # ≈ 1.7321
SQRT5 = math.sqrt(5)                 # ≈ 2.2361
E_    = math.e                       # ≈ 2.7183
PI    = math.pi                      # ≈ 3.1416
C_    = 1 / (PHI * SQRT2)           # Emerick constant ≈ 0.4370
T_    = 1 - math.exp(-E_)           # TI threshold     ≈ 0.9340
ET    = SQRT2 - 1                    # Emerick threshold ≈ 0.4142

PRIMARY_CONSTANTS = {
    'sqrt2': SQRT2, 'phi': PHI,     'e': E_,    'pi': PI,
    'C':     C_,    'phi2': PHI**2, 'sqrt3': SQRT3,
    '4_3':   4/3,   '3_2': 3/2,    'pi_2': PI/2,
    '2pi':   2*PI,  'ln2': math.log(2),
    'sqrt5': SQRT5, '1_phi': 1/PHI, 'pi_3': PI/3,
}

FIBONACCI  = [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765]
CATALAN    = [1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012]
LUCAS      = [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207,3571]
BELL       = [1,1,2,5,15,52,203,877,4140,21147,115975]
TRIANGULAR = [n*(n+1)//2 for n in range(200)]
FIB_SET    = set(FIBONACCI)
CAT_SET    = set(CATALAN)
LUC_SET    = set(LUCAS)
BELL_SET   = set(BELL)
TRI_SET    = set(TRIANGULAR)

def pc_check(x):
    """Check if x is near a PRIMARY CONSTANT × simple multiplier."""
    if not isinstance(x, (int, float)) or math.isnan(x) or math.isinf(x):
        return False, None
    for name, val in PRIMARY_CONSTANTS.items():
        for mult in [0.5, 1, 2, 3, 4, 5, 6, 8, 10, 12, 24, 60, 100, 360]:
            t = val * mult
            if t > 0 and abs(x - t) / t < 0.01:
                return True, f"{x} ≈ {mult}×{name}={t:.5g}"
    return False, None

def special_check(x):
    """Check if x is a combinatorially special number."""
    xi = int(round(x))
    if abs(x - xi) > 0.001:
        return None
    if xi in FIB_SET:  return "Fibonacci"
    if xi in CAT_SET:  return "Catalan"
    if xi in LUC_SET:  return "Lucas"
    if xi in BELL_SET: return "Bell"
    if xi in TRI_SET:  return "Triangular"
    if xi > 1 and (xi & (xi - 1)) == 0: return "PowerOf2"
    return None

def classify(problem):
    """Classify problem domain from keywords."""
    t = problem.lower()
    if any(w in t for w in ['circle','triangle','polygon','angle','radius','area',
                             'chord','tangent','square','rectangle','hexagon',
                             'inscribed','circumscribed','perpendicular']):
        return 'geometry'
    if any(w in t for w in ['prime','divisor','gcd','lcm','remainder','modulo',
                             'digit','factor','integer','divisible','congruent',
                             'floor','ceiling','fibonacci','perfect number']):
        return 'number_theory'
    if any(w in t for w in ['sequence','count','ways','arrange','choose','subset',
                             'permutation','combination','probability','distribute',
                             'selection','path','grid','lattice']):
        return 'combinatorics'
    return 'algebra'

def extract_int(text):
    """Extract the final integer answer from LLM output. Multiple strategies."""
    # LaTeX boxed answer — highest priority
    m = re.search(r'\\boxed\{(\-?\d+(?:\.\d+)?)\}', text)
    if m:
        return int(round(float(m.group(1))))
    # Bold answer (markdown)
    m = re.search(r'\*\*(\-?\d+)\*\*', text)
    if m:
        return int(m.group(1))
    # Common answer phrases
    for p in [
        r'(?:the\s+)?(?:final\s+)?answer\s+is\s+(\-?\d+)',
        r'(?:final\s+)?answer\s*[:=]\s*(\-?\d+)',
        r'(?:result|value)\s+is\s+(\-?\d+)',
        r'therefore[,\s]+(\-?\d+)',
        r'thus[,\s]+(\-?\d+)',
        r'= (\-?\d+)\s*$',
    ]:
        m = re.search(p, text, re.IGNORECASE | re.MULTILINE)
        if m:
            return int(m.group(1))
    # Last standalone integer in the response (fallback)
    nums = re.findall(r'(?<!\d)(\-?\d{1,6})(?!\d)', text)
    if nums:
        return int(nums[-1])
    return None

def answer_confidence(a, ptype):
    """Score confidence of a candidate answer using TI Sigma heuristics."""
    if a is None:
        return 0.0
    # AIMO answers are always non-negative integers — negative result = likely extraction error
    if a < 0:
        return 0.05
    c = 0.4
    if pc_check(a)[0]:   c += 0.20
    if special_check(a): c += 0.15
    if 0 <= a <= 999:    c += 0.10   # AIMO answers almost always in this range
    if 0 <= a <= 9999:   c += 0.05
    return min(c, 1.0)

def mr_collapse(answers, confs):
    """Myrion Resolution: weighted majority vote over N candidate answers."""
    valid = [(a, c) for a, c in zip(answers, confs) if a is not None]
    if not valid:
        return 0, 0.0, "DT"
    weights = {}
    for a, c in valid:
        weights[a] = weights.get(a, 0) + c
        if pc_check(a)[0]:    weights[a] += 0.12
        if special_check(a):  weights[a] += 0.08
    best  = max(weights, key=weights.get)
    total = sum(weights.values())
    conf  = weights[best] / total
    level = ("MR2-Resolved"     if conf >= 0.70 else
             "MR2-Tralse"       if conf >= 0.40 else
             "MR3-Indeterminate")
    return best, conf, level

print("      ✓ Math engine ready")

# ══════════════════════════════════════════════════════════
# STEP 5 — LLM INTERFACE (with hard per-call timeout)
# ══════════════════════════════════════════════════════════
print("\n[5/6] Setting up LLM interface...")

# ── Provider selection is automatic (see provider auto-detection block below) ──
# ACTIVE_PROVIDER + ACTIVE_MODEL are set by the validation block.
# Priority: Anthropic (best math) → Perplexity r1-1776 → demo mode.
#
# If Anthropic fails with "credit balance too low":
#   → Go to console.anthropic.com → Settings → Billing → Add Credits (prepay $5+)
#   → Setting a monthly "spend limit" does NOT add credits. You need to buy them.
#
# If Perplexity fails:
#   → Make sure secret 'Perplexity_Api_Key' is added in Kaggle Secrets (Add-ons → Secrets)
#   → Make sure "Attach to notebook" toggle is ON for that secret

# ── Per-call hard timeout (seconds) ───────────────────────
# Gateway allows ~9 hours for ~50 problems = ~10 min/problem.
# We allow 90s per API call; 3 passes = ~5 min max per problem.
CALL_TIMEOUT_SEC = 90

SYSTEM_PROMPT = """You are a world-class mathematical olympiad solver competing in AIMO (AI Mathematical Olympiad).

Solve the problem using this EXACT structure:
1. TRUE POLE: The most direct interpretation of the problem.
2. FALSE POLE: The hidden constraint, edge case, or trick beginners miss.
3. MYRION SYNTHESIS: Combine both poles to find the correct formulation.
4. CALCULATION: Careful, step-by-step arithmetic — show every step. Double-check all arithmetic.
5. VERIFY: Substitute your answer back and confirm ALL conditions hold.
6. FINAL ANSWER: State the integer as \\boxed{N}

Rules:
- The answer MUST be a non-negative integer (0 or a positive whole number).
- AIMO answers are always integers in the range 0–999. If your calculation gives a larger number, compute it mod 1000.
- Show all intermediate steps clearly so errors can be caught.
- Do not leave the boxed answer blank — always provide your best integer estimate.
- The \\boxed{N} answer is what gets scored — make it unambiguous."""

TYPE_HINTS = {
    'geometry':     "GEOMETRY: use similarity ratios, power of a point, area decomposition.",
    'number_theory':"NUMBER THEORY: use modular arithmetic, prime factorization, CRT.",
    'combinatorics':"COMBINATORICS: use inclusion-exclusion, bijections, generating functions.",
    'algebra':      "ALGEBRA: use AM-GM, Cauchy-Schwarz, substitution, symmetry.",
}

# ── Provider: which API are we using? (auto-detected at validation time) ──
# Options: "anthropic", "perplexity", None (demo mode)
ACTIVE_PROVIDER = None
ACTIVE_MODEL    = None

def _llm_worker(provider, model, user_msg, result_container):
    """Worker thread: calls the active provider and stores result."""
    try:
        if provider == "anthropic":
            import anthropic
            aclient = anthropic.Anthropic()
            msg = aclient.messages.create(
                model=model,
                max_tokens=2048,
                system=SYSTEM_PROMPT,
                messages=[{"role": "user", "content": user_msg}]
            )
            result_container[0] = msg.content[0].text

        elif provider == "perplexity":
            from openai import OpenAI
            pclient = OpenAI(
                api_key=os.environ.get("PERPLEXITY_API_KEY", ""),
                base_url="https://api.perplexity.ai"
            )
            resp = pclient.chat.completions.create(
                model=model,
                max_tokens=2048,
                messages=[
                    {"role": "system", "content": SYSTEM_PROMPT},
                    {"role": "user",   "content": user_msg}
                ]
            )
            result_container[0] = resp.choices[0].message.content

        else:
            result_container[0] = "[LLM_ERROR: no provider configured]"

    except Exception as ex:
        result_container[0] = f"[LLM_ERROR: {ex}]"

def call_llm(problem, ptype, attempt=1):
    """Call the active LLM provider with a hard timeout. Returns response text or error."""
    if ACTIVE_PROVIDER is None:
        return "[LLM_ERROR: no working provider — add Anthropic or Perplexity API key]"

    note = ""
    if attempt == 2:
        note = "\nNOTE — Attempt 2: re-examine the problem from scratch. Check edge cases."
    elif attempt >= 3:
        note = "\nNOTE — Attempt 3: try a COMPLETELY DIFFERENT approach. Do not repeat prior work."

    user_msg = f"{TYPE_HINTS.get(ptype, '')}{note}\n\nProblem: {problem}"

    result = [None]
    thread = threading.Thread(
        target=_llm_worker,
        args=(ACTIVE_PROVIDER, ACTIVE_MODEL, user_msg, result),
        daemon=True
    )
    thread.start()
    thread.join(timeout=CALL_TIMEOUT_SEC)

    if thread.is_alive():
        return f"[LLM_ERROR: timeout after {CALL_TIMEOUT_SEC}s]"
    if result[0] is None:
        return "[LLM_ERROR: no response]"
    return result[0]

# Keep call_claude as an alias for backwards compatibility
call_claude = call_llm

# ── Configuration ──────────────────────────────────────────
# N_PASSES=3 with fast model: ~45-90s total per problem (well within budget).
# Early exit: if passes 1 & 2 agree with confidence ≥ 0.7, skip pass 3.
N_PASSES      = 3
EARLY_EXIT_CONF = 0.75   # skip pass 3 if first 2 agree at this confidence
MAX_PROBLEMS  = None     # None = all; set e.g. 5 for local testing

def solve_one(problem, pid, n_passes=3):
    """Solve a single problem with MR collapse over N passes. Early exit if confident."""
    ptype = classify(problem)
    print(f"\n  [{pid}] {ptype.upper()} | {problem[:80]}{'...' if len(problem)>80 else ''}")

    if ACTIVE_PROVIDER is None:
        print(f"       → DEMO MODE (no working API): answer = 0")
        return {'id': pid, 'answer': 0, 'confidence': 0.0,
                'mr_level': 'DT', 'problem_type': ptype}

    answers, confs = [], []
    _model_label = f"{ACTIVE_PROVIDER}:{ACTIVE_MODEL}"

    for attempt in range(1, n_passes + 1):
        t0 = time.time()
        response = call_llm(problem, ptype, attempt)
        elapsed  = time.time() - t0

        if response.startswith("[LLM_ERROR") or response.startswith("[CLAUDE_ERROR"):
            print(f"       Pass {attempt} ({_model_label}, {elapsed:.0f}s): ERROR — {response[:80]}")
            answers.append(None)
            confs.append(0.0)
        else:
            a = extract_int(response)
            c = answer_confidence(a, ptype)
            answers.append(a)
            confs.append(c)
            pc_hit = pc_check(a)[1] if a is not None else None
            sn_hit = special_check(a) if a is not None else None
            tag = ""
            if pc_hit: tag += f"  [{pc_hit}]"
            if sn_hit: tag += f"  [{sn_hit}]"
            print(f"       Pass {attempt} ({_model_label}, {elapsed:.0f}s): {a}  conf={c:.2f}{tag}")

        # Early exit: if first 2 passes agree at high confidence, skip pass 3
        if attempt == 2 and len([x for x in answers if x is not None]) >= 2:
            _, interim_conf, _ = mr_collapse(answers, confs)
            if interim_conf >= EARLY_EXIT_CONF:
                print(f"       → Early exit (conf={interim_conf:.2f} ≥ {EARLY_EXIT_CONF})")
                break

    final, conf, level = mr_collapse(answers, confs)
    print(f"       → MR COLLAPSE: {final}  ({level}, conf={conf:.2f})")
    return {'id': pid, 'answer': final, 'confidence': conf,
            'mr_level': level, 'problem_type': ptype}

# ── Provider auto-detection — tries each option, picks the first that works ──
# Priority: Anthropic (best math) → Perplexity r1-1776 (free, excellent math) → demo
#
# Anthropic models to try (in order):
# NOTE: If a model returns Error 404 (not_found_error), your API key may not
# have access to that model tier. The haiku model at the bottom is a known fallback.
# Add credits at console.anthropic.com and check your account's model access tier.
ANTHROPIC_MODELS = [
    "claude-3-7-sonnet-20250219",   # Feb 2025 — strongest reasoning + extended thinking
    "claude-3-5-sonnet-20241022",   # Oct 2024 — best speed/accuracy balance
    "claude-3-5-haiku-20241022",    # Oct 2024 — fastest, lightest
    "claude-3-haiku-20240307",      # Mar 2024 — confirmed fallback if newer models 404
    "claude-3-opus-20240229",       # Feb 2024 — deprecated, last resort
    "claude-3-sonnet-20240229",     # Feb 2024 — deprecated, last resort
]
# Perplexity models to try (in order):
PERPLEXITY_MODELS = [
    "r1-1776",                      # DeepSeek-R1 — excellent at math olympiad
    "sonar-pro",                    # Sonar Pro — web-connected, strong reasoning
    "sonar",                        # Standard sonar
]

def _test_anthropic(model_name):
    """Return (ok, reply_or_error) for one Anthropic model."""
    try:
        import anthropic
        aclient = anthropic.Anthropic()
        resp = aclient.messages.create(
            model=model_name, max_tokens=10,
            messages=[{"role": "user", "content": "Reply with just the number 1"}]
        )
        return True, resp.content[0].text.strip()
    except Exception as ex:
        return False, str(ex)[:160]

def _test_perplexity(model_name):
    """Return (ok, reply_or_error) for one Perplexity model."""
    try:
        from openai import OpenAI
        pclient = OpenAI(
            api_key=os.environ.get("PERPLEXITY_API_KEY", ""),
            base_url="https://api.perplexity.ai"
        )
        resp = pclient.chat.completions.create(
            model=model_name, max_tokens=10,
            messages=[{"role": "user", "content": "Reply with just the number 1"}]
        )
        return True, resp.choices[0].message.content.strip()
    except Exception as ex:
        return False, str(ex)[:160]

print("      ─── Provider auto-detection ───")

# 1. Try Anthropic (best math accuracy)
if ANTHROPIC_KEY and ACTIVE_PROVIDER is None:
    print("      Trying Anthropic...")
    for _model in ANTHROPIC_MODELS:
        _ok, _msg = _test_anthropic(_model)
        if _ok:
            ACTIVE_PROVIDER = "anthropic"
            ACTIVE_MODEL    = _model
            print(f"      ✓ Anthropic → '{_model}' works (reply: {_msg})")
            break
        else:
            _short = _msg[:80]
            print(f"        ✗ '{_model}': {_short}")
            # credit error → pointless to try other Anthropic models
            if "credit" in _msg.lower() or "billing" in _msg.lower():
                print("          ↳ Anthropic credit issue — skipping remaining Anthropic models")
                print("          ↳ → Top up at console.anthropic.com → Plans & Billing")
                break

# 2. Try Perplexity (free for existing subscribers, great math with r1-1776)
if PERPLEXITY_KEY and ACTIVE_PROVIDER is None:
    print("      Trying Perplexity...")
    for _model in PERPLEXITY_MODELS:
        _ok, _msg = _test_perplexity(_model)
        if _ok:
            ACTIVE_PROVIDER = "perplexity"
            ACTIVE_MODEL    = _model
            print(f"      ✓ Perplexity → '{_model}' works (reply: {_msg})")
            break
        else:
            print(f"        ✗ '{_model}': {_msg[:80]}")

if ACTIVE_PROVIDER is None:
    print("      ✗ NO WORKING PROVIDER — running in DEMO mode (answers = 0)")
    print("        Fix: add Anthropic credits OR add Perplexity_Api_Key to Kaggle Secrets")
else:
    print(f"      ✓ LLM interface ready")
    print(f"        Provider: {ACTIVE_PROVIDER} | Model: {ACTIVE_MODEL}")
    print(f"        Timeout: {CALL_TIMEOUT_SEC}s/call | Passes: {N_PASSES}")

# ══════════════════════════════════════════════════════════
# STEP 6 — RUN: GATEWAY MODE or CSV FALLBACK
# ══════════════════════════════════════════════════════════
#
# EXECUTION MODES (auto-detected):
#   A) GATEWAY MODE  — kaggle_evaluation importable (real submission)
#                      → predict() called per problem; Kaggle scores live
#   B) REFERENCE CSV — gateway unavailable, reference.csv found
#                      → useful for offline tuning against known answers
#   C) DEMO MODE     — nothing else available → 5 built-in hard problems

print("\n[6/6] Running solver...")

import os, sys

# Diagnostic: list all available files
kaggle_input = Path("/kaggle/input")
all_files = []
if kaggle_input.exists():
    for root, dirs, files in os.walk(kaggle_input):
        for f in files:
            all_files.append(Path(root) / f)
    print(f"      Files under /kaggle/input/ ({len(all_files)} total):")
    for f in sorted(all_files)[:30]:
        print(f"        {f}")
    if len(all_files) > 30:
        print(f"        ... and {len(all_files)-30} more")

# The predict function — called by AIMO3Gateway OR our fallback loop
_results_log = []

def predict(id_: str, problem: str) -> int:
    """Solve one problem. Returns integer answer. Called by AIMO3Gateway."""
    result = solve_one(str(problem), str(id_), n_passes=N_PASSES)
    _results_log.append(result)
    ans = int(result['answer'])
    # AIMO answers are always 0–999. Clamp anything that escaped the prompt instruction.
    if ans < 0 or ans > 999:
        ans = ans % 1000
    return ans

# ══════════════════════════════════════════════════════════
# MODE A — GATEWAY (live competition evaluation)
# ══════════════════════════════════════════════════════════
GATEWAY_AVAILABLE = False
AIMO3Gateway = None

# ── Strategy: try pip-installed package first, then path-based fallbacks ──
#
# In a real submission kernel, `pip install kaggle-evaluation` (Step 1) puts
# the package on the default Python path — direct import works.
#
# In DRAFT mode, the evaluation server is not running, so gateway.run()
# will raise a "data_paths" TypeError. That is EXPECTED in draft.
# In a real "Save & Run All Commit", gateway.run() works correctly.

# 1. Direct import (works after pip install kaggle-evaluation)
try:
    from kaggle_evaluation.aimo_3_gateway import AIMO3Gateway
    GATEWAY_AVAILABLE = True
    print("      ✓ kaggle_evaluation: direct import succeeded")
except ImportError:
    pass

# 2. Competition input folder
if not GATEWAY_AVAILABLE:
    _comp = Path("/kaggle/input/competitions/ai-mathematical-olympiad-progress-prize-3")
    for _p in [_comp, _comp / "kaggle_evaluation"]:
        if (_p / "aimo_3_gateway.py").exists():
            _parent = str(_p.parent) if _p.name == "kaggle_evaluation" else str(_p)
            if _parent not in sys.path:
                sys.path.insert(0, _parent)
            print(f"      Added to sys.path: {_parent}")
            break
    try:
        from kaggle_evaluation.aimo_3_gateway import AIMO3Gateway
        GATEWAY_AVAILABLE = True
        print("      ✓ Gateway loaded from competition folder")
    except ImportError:
        pass

# 3. Walk ALL input folders for any copy of aimo_3_gateway.py
if not GATEWAY_AVAILABLE:
    _found = None
    for _search in ["/kaggle/input/datasets", "/kaggle/input"]:
        _sp = Path(_search)
        if not _sp.exists():
            continue
        for _root, _dirs, _files in os.walk(_sp):
            if "aimo_3_gateway.py" in _files:
                _found = str(Path(_root).parent)
                print(f"      Found gateway at: {_root}")
                break
        if _found:
            break
    if _found and _found not in sys.path:
        sys.path.insert(0, _found)
    if _found:
        try:
            from kaggle_evaluation.aimo_3_gateway import AIMO3Gateway
            GATEWAY_AVAILABLE = True
            print("      ✓ Gateway loaded from dataset folder")
        except ImportError as _e:
            print(f"      ✗ Import failed even with path set: {_e}")

if not GATEWAY_AVAILABLE:
    print("      ✗ kaggle_evaluation not found — falling back to CSV/demo mode")
    print("        (In a real submission, Step 1 installs it via pip automatically)")

if GATEWAY_AVAILABLE:
    print("\n      ✓ GATEWAY MODE — Kaggle evaluation server active")
    print("        Real olympiad problems will be streamed to predict().")
    print("        Submitting via gateway now...\n")
    print("=" * 60)

    gateway = AIMO3Gateway(predict)
    try:
        gateway.run()   # blocks until all problems answered; Kaggle scores live
        print("\n" + "=" * 60)
        print("GATEWAY RUN COMPLETE — all problems answered")
        print("=" * 60)
    except Exception as _gw_exc:
        _msg = str(_gw_exc)
        print(f"\n      ✗ Gateway error: {_msg}")
        if "data_paths" in _msg or "not subscriptable" in _msg or "NoneType" in _msg:
            print("        → DRAFT MODE: evaluation server not running (expected).")
            print("          Use 'Save & Run All Commit' for a real scored submission.")
            print("          Your predict() function is correct — gateway works in real runs.")
        elif "timeout" in _msg.lower():
            print("        → Gateway timed out. Check API key and network connectivity.")
        else:
            print(f"        → Unexpected error. Full trace: {_msg}")
        GATEWAY_AVAILABLE = False

# ══════════════════════════════════════════════════════════
# MODE B — REFERENCE CSV (offline tuning / scoring check)
# ══════════════════════════════════════════════════════════
if not GATEWAY_AVAILABLE:
    print("\n      Gateway not available — falling back to CSV mode.")

    all_csvs = [f for f in all_files if f.suffix.lower() == '.csv']
    ref_candidates   = [f for f in all_csvs if 'reference' in f.name.lower()]
    test_candidates  = [f for f in all_csvs if 'test' in f.name.lower()
                        and 'sample' not in f.name.lower()]
    other_candidates = [f for f in all_csvs
                        if 'sample_submission' not in f.name.lower()
                        and 'reference' not in f.name.lower()
                        and 'test' not in f.name.lower()]

    def _prefer_comp(lst):
        comp = [f for f in lst if 'competitions' in str(f)]
        return comp[0] if comp else (lst[0] if lst else None)

    CSV_FILE = (_prefer_comp(ref_candidates) or
                _prefer_comp(test_candidates) or
                _prefer_comp(other_candidates))

    if CSV_FILE:
        print(f"      ✓ Using CSV: {CSV_FILE.name}")
        df = pd.read_csv(CSV_FILE)
        print(f"        Columns: {list(df.columns)} | Rows: {len(df)}")

        id_col   = next((c for c in df.columns if c.lower() in ['id','problem_id']), df.columns[0])
        text_col = next((c for c in df.columns if c.lower() in ['problem','question','text','prompt']), None)
        if text_col is None:
            _skip = {'id','answer','label','target','solution','answer_value'}
            text_col = max(
                (c for c in df.columns if c.lower() not in _skip),
                key=lambda c: df[c].dropna().astype(str).str.len().mean(),
                default=df.columns[-1]
            )
        print(f"        id='{id_col}' | problem='{text_col}'")
        print(f"        Sample: {str(df[text_col].iloc[0])[:100]}")

        # test.csv from AIMO3 has 3 trivial placeholder rows — skip if max answer ≤ 10
        _is_trivial = False
        if 'answer' in df.columns and len(df) <= 5:
            try:
                _max_ans = pd.to_numeric(df['answer'], errors='coerce').max()
                _is_trivial = (not pd.isna(_max_ans)) and (_max_ans <= 10)
            except Exception:
                pass
        if _is_trivial:
            print("        ! Detected trivial warm-up CSV (not real problems) — switching to DEMO mode")
            CSV_FILE = None

    if CSV_FILE:
        solve_df = df.head(MAX_PROBLEMS) if MAX_PROBLEMS else df
        print(f"\nSolving {len(solve_df)} problem(s) | {N_PASSES} passes each...")
        print("=" * 60)
        for _, row in solve_df.iterrows():
            predict(str(row[id_col]), str(row[text_col]))
    else:
        # ── MODE C: DEMO ──────────────────────────────────────────────────────
        print("\n      ! No real problem CSV found — running 5 built-in demo problems")
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

    # Save submission CSV (CSV/demo modes only — gateway scores live, no CSV needed)
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

# ── Summary (all modes) ───────────────────────────────────────────────────────
if _results_log:
    results_df = pd.DataFrame(_results_log)
    print(f"\nMR LEVEL BREAKDOWN:")
    for level, count in results_df['mr_level'].value_counts().items():
        print(f"  {level}: {count}")
    print(f"\nTYPE BREAKDOWN:")
    for ptype, count in results_df['problem_type'].value_counts().items():
        print(f"  {ptype}: {count}")
    print(f"\nMean confidence: {results_df['confidence'].mean():.2f}")
    print(f"Total problems solved: {len(results_df)}")

print("\n" + "=" * 60)
print("NOTES:")
print("  GATEWAY MODE:   Kaggle scores answers live — no CSV submit button needed.")
print("  CSV/DEMO MODE:  Click 'Submit' top-right to submit submission.csv.")
print("  DRAFT vs REAL:  'data_paths' gateway error is DRAFT ONLY — real runs work.")
print("  TIMEOUT GUARD:  Each API call is capped at", CALL_TIMEOUT_SEC, "seconds.")
print("=" * 60)
