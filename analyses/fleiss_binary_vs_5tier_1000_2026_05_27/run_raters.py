"""
Pass-77-B25 binary-vs-5-tier rater study.
1000 statements x 3 raters x 2 systems = 6000 API calls total.
Rating modes: binary {T,F} OR 5tier {T,F,I,MI,NA}.
Checkpoint after each call; safe to re-run for resume.
Usage:  MODE=binary python run_raters.py
        MODE=5tier  python run_raters.py
"""
import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from openai import OpenAI
from anthropic import Anthropic

MODE = os.environ.get("MODE", "5tier").lower()

PROMPTS = {
    "binary": """You are a logical/epistemic rater operating under classical bivalent logic. Classify the following sentence into EXACTLY ONE of these 2 categories:

T = TRUE: the sentence asserts something that is true.
F = FALSE: the sentence asserts something that is false.

This is the standard 0/1 binary classification used in classical logic and most computing systems. You MUST pick exactly one of T or F, even if the sentence is ambiguous, unverifiable, paradoxical, or a category mistake. Use your best judgment.

Sentence: {prop}

Respond with ONLY the single letter (T or F) and nothing else.""",

    "5tier": """You are a logical/epistemic rater. Classify the following sentence into EXACTLY ONE of these 5 categories:

T  = TRUE: the sentence is well-established as true given common knowledge.
F  = FALSE: the sentence is well-established as false given common knowledge.
I  = INDETERMINATE: the sentence has a determinate truth-value but it cannot be determined from available knowledge (e.g., a present empirical fact you have no access to, or a contingent future event).
MI = META-INDETERMINATE: the sentence is incoherent or self-contradictory; trying to fully mentally instantiate it produces internal contradiction (e.g., the liar paradox, a married bachelor, 2+2=5 by definition, a four-sided triangle). This is INCOHERENCE-WHEN-FULLY-ENTERTAINED, not merely surprising or false.
NA = NOT APPLICABLE: the sentence is a category mistake; none of T/F/I/MI apply because the predicate-subject pairing is type-incoherent in a way that does not even produce a tractable contradiction (e.g., "the number 7 smells like vanilla" -- numbers do not have olfactory properties to be true or false about).

Sentence: {prop}

Respond with ONLY the code (T, F, I, MI, or NA) and nothing else.""",
}

VALID_SETS = {
    "binary": {"T", "F"},
    "5tier": {"T", "F", "I", "MI", "NA"},
}

PARSE_PATTERNS = {
    "binary": re.compile(r"\b(T|F|TRUE|FALSE)\b", re.I),
    "5tier": re.compile(r"\b(MI|NA|T|F|I)\b"),
}

def parse(text, mode):
    if text is None: return None
    t = text.strip().upper()
    if t in VALID_SETS[mode]: return t
    m = PARSE_PATTERNS[mode].search(t)
    if not m: return None
    g = m.group(1)
    if g == "TRUE": return "T"
    if g == "FALSE": return "F"
    return g if g in VALID_SETS[mode] else None

def rate_oai(c, m, p, mode):
    try:
        r = c.chat.completions.create(model=m, max_tokens=10, temperature=0,
            messages=[{"role":"user","content":PROMPTS[mode].format(prop=p)}])
        return parse(r.choices[0].message.content, mode)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:100]}\n"); sys.stderr.flush()
        return None

def rate_anth(c, m, p, mode):
    try:
        r = c.messages.create(model=m, max_tokens=10,
            messages=[{"role":"user","content":PROMPTS[mode].format(prop=p)}])
        return parse(r.content[0].text, mode)
    except Exception as e:
        sys.stderr.write(f"anth-err: {str(e)[:100]}\n"); sys.stderr.flush()
        return None

DIR = "analyses/fleiss_binary_vs_5tier_1000_2026_05_27"
TEST = f"{DIR}/test_set.json"
OUT = f"{DIR}/ratings_{MODE}.json"

assert MODE in PROMPTS, f"MODE must be binary or 5tier, got {MODE}"

with open(TEST) as f: props = json.load(f)

if os.path.exists(OUT):
    with open(OUT) as f: results = json.load(f)
    done_ids = {r["id"]: r for r in results}
else:
    results = []; done_ids = {}

print(f"[{MODE}] Loaded {len(props)} props; {len(done_ids)} already rated", flush=True)

oai = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
             base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
anth = Anthropic(api_key=os.environ["AI_INTEGRATIONS_ANTHROPIC_API_KEY"],
                 base_url=os.environ["AI_INTEGRATIONS_ANTHROPIC_BASE_URL"])

RATERS = [("R1_gpt4o_mini","oai","gpt-4o-mini"),
          ("R2_gpt4o_mini_b","oai","gpt-4o-mini"),
          ("R3_claude_haiku","anth","claude-haiku-4-5")]

TIME_BUDGET = float(os.environ.get("CHUNK_BUDGET_SEC", "110"))
CHECKPOINT_EVERY = int(os.environ.get("CHECKPOINT_EVERY", "10"))
start = time.time()

new_results = list(results)
since_ckpt = 0
for p in props:
    if p["id"] in done_ids:
        continue
    if time.time() - start > TIME_BUDGET:
        print(f"[{MODE}] Time budget {TIME_BUDGET}s reached", flush=True)
        break
    row = {"id": p["id"], "gold": p["gold"], "text": p["text"], "ratings": {}}
    def _do(spec):
        rname, prov, model = spec
        v = rate_oai(oai, model, p["text"], MODE) if prov == "oai" else rate_anth(anth, model, p["text"], MODE)
        return rname, v
    with ThreadPoolExecutor(max_workers=3) as ex:
        for rname, v in ex.map(_do, RATERS):
            row["ratings"][rname] = v
    new_results.append(row)
    since_ckpt += 1
    if since_ckpt >= CHECKPOINT_EVERY:
        with open(OUT, "w") as f: json.dump(new_results, f, indent=2)
        since_ckpt = 0
    if len(new_results) % 25 == 0:
        print(f"[{MODE}]   {len(new_results)}/{len(props)} elapsed={time.time()-start:.0f}s", flush=True)

with open(OUT, "w") as f: json.dump(new_results, f, indent=2)
elapsed = time.time() - start
print(f"[{MODE}] DONE chunk: {len(new_results)}/{len(props)} total, {elapsed:.1f}s elapsed", flush=True)
