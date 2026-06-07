"""
Pass-77-B108 — INDEPENDENT PD-degree rating pass over the 500 gold propositions.

Design (anti-circularity, #69): PD is measured here as a CONTINUOUS degree on the
canonical PD-real scale (-3, +2) via a SEPARATE instrument (numeric, zone-rubric
prompt) than the categorical 5-tier {T,F,I,MI,NA} labels. The link is then tested
against the PRE-EXISTING gold labels (independent ground truth), NOT against the
categorical rater pass -> no deterministic-function circularity.

Reuses the 1000-statement test set from the B26 study; rates only the 500 GOLD
props (gold in {T,F,I,MI,NA}; CASUAL excluded -- no ground-truth label to link to).

3 raters (same as B26 for comparability): 2x gpt-4o-mini + 1x claude-haiku.
Output per prop per rater: a float in [-3, 2]  OR  the token OFFAXIS (off the
truth spectrum entirely = NAO-1 N/A coordinate).

Checkpoint after each chunk; safe to re-run for resume.
Usage:  python run_pd_raters.py     (CHUNK_BUDGET_SEC controls per-invocation time)
"""
import json, os, re, sys, time
from concurrent.futures import ThreadPoolExecutor
from openai import OpenAI
from anthropic import Anthropic

PD_PROMPT = """You are rating a sentence on the PD-real "Permissibility Distribution" axis: a CONTINUOUS degree-of-truth coordinate.

The scale runs from -3 to +2 (it is deliberately asymmetric):
  +2  = clearly, strongly TRUE (well-established as true given common knowledge)
  +1  = soft-true (probably true, leans true)
   0  = neutral / genuinely balanced
  between -2/3 and +1/3 = INDETERMINATE: the sentence HAS a definite truth-value or is coherent, but it cannot be settled from available knowledge (an empirical fact you lack access to, or a contingent future event). Coherent but unsettled.
  -1  = soft-false (probably false, leans false)
  -2  = clearly FALSE (well-established as false)
  -3  = the MI CLIFF: the sentence is INCOHERENT or self-contradictory when you try to FULLY entertain it (e.g. the liar paradox, a married bachelor, a four-sided triangle, 2+2=5 by definition). Reserve values near -3 for genuine incoherence, NOT mere falsehood.

There is also an OFF-AXIS option, OUTSIDE the -3..+2 scale entirely:
  OFFAXIS = the sentence is a CATEGORY MISTAKE; the predicate-subject pairing is type-incoherent so no degree of truth/falsity applies at all (e.g. "the number 7 smells like vanilla"). This is off the truth spectrum, not a point on it.

Sentence: {prop}

Respond with EITHER a single number between -3 and 2 (decimals allowed, e.g. 1.5, -2, -0.3) OR the single word OFFAXIS. Output ONLY that, nothing else."""

NUM_RE = re.compile(r"-?\d+(?:\.\d+)?")

def parse(text):
    if text is None:
        return None
    t = text.strip().upper()
    if "OFFAXIS" in t.replace(" ", "").replace("-", ""):
        return "OFFAXIS"
    m = NUM_RE.search(t)
    if not m:
        return None
    try:
        v = float(m.group(0))
    except ValueError:
        return None
    # clamp to canonical scale
    if v < -3: v = -3.0
    if v > 2: v = 2.0
    return v

def rate_oai(c, m, p):
    try:
        r = c.chat.completions.create(model=m, max_tokens=10, temperature=0,
            messages=[{"role": "user", "content": PD_PROMPT.format(prop=p)}])
        return parse(r.choices[0].message.content)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

def rate_anth(c, m, p):
    try:
        r = c.messages.create(model=m, max_tokens=10,
            messages=[{"role": "user", "content": PD_PROMPT.format(prop=p)}])
        return parse(r.content[0].text)
    except Exception as e:
        sys.stderr.write(f"anth-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

SRC = "analyses/fleiss_binary_vs_5tier_1000_2026_05_27/test_set.json"
DIR = "analyses/pass77_b108_pd_truthlabel_link_2026_06_06"
OUT = f"{DIR}/ratings_pd.json"

all_props = json.load(open(SRC))
props = [p for p in all_props if p.get("gold") not in (None, "CASUAL")]

if os.path.exists(OUT):
    results = json.load(open(OUT))
    done = {r["id"] for r in results}
else:
    results, done = [], set()

print(f"[PD] {len(props)} gold props; {len(done)} already rated", flush=True)

oai = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
             base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
anth = Anthropic(api_key=os.environ["AI_INTEGRATIONS_ANTHROPIC_API_KEY"],
                 base_url=os.environ["AI_INTEGRATIONS_ANTHROPIC_BASE_URL"])

RATERS = [("R1_gpt4o_mini", "oai", "gpt-4o-mini"),
          ("R2_gpt4o_mini_b", "oai", "gpt-4o-mini"),
          ("R3_claude_haiku", "anth", "claude-haiku-4-5")]

TIME_BUDGET = float(os.environ.get("CHUNK_BUDGET_SEC", "110"))
MAX_PROPS = int(os.environ.get("MAX_PROPS", "9999"))
start = time.time()

pending = [p for p in props if p["id"] not in done][:MAX_PROPS]

def rate_one(p):
    out = {"id": p["id"], "gold": p["gold"], "text": p["text"], "pd": {}}
    for rname, prov, model in RATERS:
        out["pd"][rname] = rate_oai(oai, model, p["text"]) if prov == "oai" else rate_anth(anth, model, p["text"])
    return out

done_count = 0
with ThreadPoolExecutor(max_workers=12) as ex:
    futs = {ex.submit(rate_one, p): p for p in pending}
    from concurrent.futures import as_completed
    for fut in as_completed(futs):
        if time.time() - start > TIME_BUDGET:
            break
        results.append(fut.result()); done_count += 1
        if done_count % 10 == 0:
            json.dump(results, open(OUT + ".tmp", "w"), indent=2); os.replace(OUT + ".tmp", OUT)
        if done_count % 25 == 0:
            print(f"[PD]   +{done_count} this chunk; {len(results)} total; elapsed={time.time()-start:.0f}s", flush=True)

json.dump(results, open(OUT + ".tmp", "w"), indent=2); os.replace(OUT + ".tmp", OUT)
print(f"[PD] DONE chunk: +{done_count}; {len(results)}/{len(props)} total, {time.time()-start:.1f}s", flush=True)
