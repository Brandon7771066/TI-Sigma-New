"""
Pass-77-B24 five-tier Fleiss kappa rater study.
3 LLM raters score propositions on 5-tier MR Truth Labels {T,F,I,DT,NA}.
Checkpoints ratings.json after EACH proposition; safe to re-run for resume.
"""
import json
import os
import re
import sys
import time
from openai import OpenAI
from anthropic import Anthropic

PROMPT = """You are a logical/epistemic rater. Classify the following proposition into exactly ONE of these 5 categories:

T  = TRUE: the proposition is well-established as true given common knowledge.
F  = FALSE: the proposition is well-established as false given common knowledge.
I  = INDETERMINATE: the proposition has a determinate truth-value but it cannot be determined from available knowledge (e.g., a present empirical fact you have no access to, or a contingent future event).
DT = DOUBLE TRALSE: the proposition is inconceivable-under-mental-actualization; trying to fully mentally instantiate it produces internal contradiction (e.g., the liar paradox, a married bachelor, 2+2=5 by definition, a four-sided triangle). This is INCOHERENCE-WHEN-FULLY-ENTERTAINED, not merely surprising or false.
NA = NOT APPLICABLE: the proposition is a category mistake; none of T/F/I/DT apply because the predicate-subject pairing is type-incoherent in a way that doesn't even produce a tractable contradiction (e.g., "the number 7 smells like vanilla" — numbers don't have olfactory properties to be true or false about).

Proposition: {prop}

Respond with ONLY the two-letter code (T, F, I, DT, or NA) and nothing else."""

VALID = {"T","F","I","DT","NA"}

def parse(text):
    if text is None: return None
    t = text.strip().upper()
    if t in VALID: return t
    m = re.search(r"\b(DT|NA|T|F|I)\b", t)
    return m.group(1) if m else None

def rate_oai(c, m, p):
    try:
        r = c.chat.completions.create(model=m, max_tokens=10, temperature=0,
            messages=[{"role":"user","content":PROMPT.format(prop=p)}])
        return parse(r.choices[0].message.content)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:100]}\n"); sys.stderr.flush()
        return None

def rate_anth(c, m, p):
    try:
        r = c.messages.create(model=m, max_tokens=10,
            messages=[{"role":"user","content":PROMPT.format(prop=p)}])
        return parse(r.content[0].text)
    except Exception as e:
        sys.stderr.write(f"anth-err: {str(e)[:100]}\n"); sys.stderr.flush()
        return None

DIR = "analyses/fleiss_5tier_2026_05_27"
TEST = f"{DIR}/test_set.json"
OUT = f"{DIR}/ratings.json"

with open(TEST) as f: props = json.load(f)

# Resume from existing
if os.path.exists(OUT):
    with open(OUT) as f: results = json.load(f)
    done_ids = {r["id"]: r for r in results}
else:
    results = []; done_ids = {}

print(f"Loaded {len(props)} props; {len(done_ids)} already rated", flush=True)

oai = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
             base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
anth = Anthropic(api_key=os.environ["AI_INTEGRATIONS_ANTHROPIC_API_KEY"],
                 base_url=os.environ["AI_INTEGRATIONS_ANTHROPIC_BASE_URL"])

RATERS = [("R1_gpt4o_mini","oai","gpt-4o-mini"),
          ("R2_gpt4o_mini_b","oai","gpt-4o-mini"),
          ("R3_claude_haiku","anth","claude-haiku-4-5")]

# Time budget: stop new props after this many seconds (chunk boundary)
TIME_BUDGET = float(os.environ.get("CHUNK_BUDGET_SEC", "100"))
start = time.time()

new_results = list(results)
for p in props:
    if p["id"] in done_ids:
        continue
    if time.time() - start > TIME_BUDGET:
        print(f"Time budget {TIME_BUDGET}s reached; checkpointing", flush=True)
        break
    row = {"id": p["id"], "gold": p["gold"], "text": p["text"], "ratings": {}}
    for rname, prov, model in RATERS:
        v = rate_oai(oai, model, p["text"]) if prov == "oai" else rate_anth(anth, model, p["text"])
        row["ratings"][rname] = v
    new_results.append(row)
    # checkpoint every proposition
    with open(OUT, "w") as f: json.dump(new_results, f, indent=2)
    print(f"  {len(new_results)}/{len(props)} {p['id']} -> {row['ratings']}", flush=True)

elapsed = time.time() - start
print(f"DONE chunk: {len(new_results)}/{len(props)} total, {elapsed:.1f}s elapsed", flush=True)
