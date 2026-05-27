"""Pass-77-B30 refined-NA 5-tier rater run.
500 statements x 3 raters = 1500 API calls.
Chunked via TIME_BUDGET to fit within 120s bash limit.
"""
import json, os, re, sys, time
from concurrent.futures import ThreadPoolExecutor
from openai import OpenAI
from anthropic import Anthropic

PROMPT = """You are a logical/epistemic rater operating under the TI Sigma 5-tier truth system with refined NA scope. Classify the following sentence into EXACTLY ONE of these 5 categories:

T  = TRUE: the sentence is well-established as true given common knowledge.
F  = FALSE: the sentence is well-established as false given common knowledge.
I  = INDETERMINATE: the sentence has a determinate truth-value that exists in principle and is in-principle-knowable, but it cannot be determined from currently available knowledge (a proposition-property — the truth-value is just under-specified by present information).
MI = META-INDETERMINATE: the sentence is incoherent or self-contradictory; trying to fully mentally instantiate it produces internal contradiction (e.g., the liar paradox, a married bachelor, 2+2=5 by definition, a four-sided triangle). This is INCOHERENCE-WHEN-FULLY-ENTERTAINED, not merely surprising or false.
NA = NOT APPLICABLE: truth-evaluation itself is impossible or has-not-yet-been-made for you, the rating mind, at this moment. This is a mind-relative process-state property and applies in FOUR modes:
     • NA-FUT (future-undeterminable): the event has not yet occurred and cannot be determined now by any mind (e.g., the exact closing price of a stock on a specific future date).
     • NA-PST-FORGOTTEN (past-inaccessible): a past truth exists in principle somewhere, but you the rater have zero reliable retrieval access to it (e.g., the exact air temperature at a specific obscure coordinate decades ago, or a specific second of your own AI training).
     • NA-PRE-DECISION (working-memory default): the sentence explicitly frames itself as being in a pre-truth-evaluation state in working memory, before any truth-decision has been committed (e.g., "the truth-value of this sentence in your working memory has not yet been computed").
     • NA-CAT (category-mistake): predicate-subject pairing is type-incoherent in a way that does not even produce a tractable contradiction (e.g., "the number 7 smells like vanilla" — numbers do not have olfactory properties).

Key NA vs I distinction: I is a PROPOSITION-PROPERTY (the truth-value exists in-principle but is currently under-specified). NA is a MIND-RELATIVE PROCESS-STATE (the truth-EVALUATION itself is impossible-or-not-yet-made for you at this moment, even though a fact may exist somewhere in principle).

Sentence: {prop}

Respond with ONLY the code (T, F, I, MI, or NA) and nothing else."""

VALID = {"T","F","I","MI","NA"}
PAT = re.compile(r"\b(MI|NA|T|F|I)\b")

def parse(text):
    if text is None: return None
    t = text.strip().upper()
    if t in VALID: return t
    m = PAT.search(t)
    return m.group(1) if m and m.group(1) in VALID else None

def rate_oai(c, m, p):
    try:
        r = c.chat.completions.create(model=m, max_tokens=10, temperature=0,
            messages=[{"role":"user","content":PROMPT.format(prop=p)}])
        return parse(r.choices[0].message.content)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

def rate_anth(c, m, p):
    try:
        r = c.messages.create(model=m, max_tokens=10,
            messages=[{"role":"user","content":PROMPT.format(prop=p)}])
        return parse(r.content[0].text)
    except Exception as e:
        sys.stderr.write(f"anth-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

DIR = "analyses/fleiss_5tier_refined_NA_2026_05_27"
TEST = f"{DIR}/test_set.json"
OUT = f"{DIR}/ratings.json"

with open(TEST) as f: props = json.load(f)
results = json.load(open(OUT)) if os.path.exists(OUT) else []
done = {r["id"] for r in results}

print(f"[B30] {len(props)} props; {len(done)} done; {len(props)-len(done)} remaining", flush=True)

oai = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
             base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
anth = Anthropic(api_key=os.environ["AI_INTEGRATIONS_ANTHROPIC_API_KEY"],
                 base_url=os.environ["AI_INTEGRATIONS_ANTHROPIC_BASE_URL"])

RATERS = [("R1_gpt4o_mini","oai","gpt-4o-mini"),
          ("R2_gpt4o_mini_b","oai","gpt-4o-mini"),
          ("R3_claude_haiku","anth","claude-haiku-4-5")]

BUDGET = float(os.environ.get("CHUNK_BUDGET_SEC", "105"))
start = time.time()
since = 0
for p in props:
    if p["id"] in done: continue
    if time.time() - start > BUDGET:
        print(f"[B30] budget {BUDGET}s reached", flush=True); break
    row = {"id": p["id"], "gold": p["gold"], "subgold": p.get("subgold"), "text": p["text"], "ratings": {}}
    def _do(spec):
        rname, prov, model = spec
        v = rate_oai(oai, model, p["text"]) if prov == "oai" else rate_anth(anth, model, p["text"])
        return rname, v
    with ThreadPoolExecutor(max_workers=3) as ex:
        for rname, v in ex.map(_do, RATERS):
            row["ratings"][rname] = v
    results.append(row); since += 1
    if since >= 10:
        json.dump(results, open(OUT,"w"), indent=2); since = 0
    if len(results) % 25 == 0:
        print(f"[B30] {len(results)}/{len(props)} elapsed={time.time()-start:.0f}s", flush=True)

json.dump(results, open(OUT,"w"), indent=2)
print(f"[B30] chunk DONE: {len(results)}/{len(props)} total, {time.time()-start:.1f}s elapsed", flush=True)
