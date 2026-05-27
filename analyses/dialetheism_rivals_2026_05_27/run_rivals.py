"""Pass-77-B31 rival dialetheism / multi-valued-logic raters.

Re-rates the SAME 500 gold props from Pass-77-B30 under two rival systems:
  - LP  (Priest, 3-valued dialetheism): {T, F, B}
  - FDE (Belnap-Dunn, 4-valued):        {T, F, Both, Neither}

500 props * 3 raters * 2 systems = 3000 calls.
Chunked via CHUNK_BUDGET_SEC to fit within bash 120s limit.
"""
import json, os, re, sys, time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from openai import OpenAI
from anthropic import Anthropic

D = Path(__file__).parent
GOLD = json.load(open("analyses/fleiss_5tier_refined_NA_2026_05_27/test_set.json"))

PROMPT_LP = """You are a logical rater operating under Graham Priest's LP (Logic of Paradox), the canonical 3-valued dialetheist system. Every proposition gets EXACTLY ONE of:

T = TRUE only
F = FALSE only
B = BOTH true and false (a true contradiction / dialetheia — e.g., the Liar sentence, or paradoxes of self-reference)

LP has NO separate value for "unknown", "undetermined", "not-applicable", or "category mistake". Every proposition must collapse to one of T, F, or B. Use B only when the proposition is genuinely both-true-and-false (a dialetheia / true contradiction); use F for false-as-far-as-we-can-tell and for undetermined-or-unknowable propositions (LP is glut-tolerant, not gap-tolerant).

Sentence: {prop}

Respond with ONLY the code (T, F, or B) and nothing else."""

PROMPT_FDE = """You are a logical rater operating under the Belnap-Dunn FDE (First-Degree Entailment / Four-valued Logic) system. Every proposition gets EXACTLY ONE of:

T  = TRUE only (told true, not told false)
F  = FALSE only (told false, not told true)
BO = BOTH true and false (told both — a glut, e.g., contradictory database)
N  = NEITHER true nor false (told nothing — a gap; the proposition is undetermined, unevaluable, presupposition-failing, or category-mistaken)

FDE has no separate slot for "incoherent" vs "not applicable" vs "future-undetermined" — all of these collapse to N (Neither). Glutty contradictions (Liar, married-bachelor, square-circle) collapse to BO (Both).

Sentence: {prop}

Respond with ONLY the code (T, F, BO, or N) and nothing else."""

VALID_LP = {"T","F","B"}
VALID_FDE = {"T","F","BO","N"}
PAT_LP = re.compile(r"\b(T|F|B)\b")
PAT_FDE = re.compile(r"\b(BO|N|T|F)\b")

def parse(text, valid, pat):
    if text is None: return None
    t = text.strip().upper()
    if t in valid: return t
    m = pat.search(t)
    return m.group(1) if m and m.group(1) in valid else None

def rate_oai(c, m, p, prompt, valid, pat):
    try:
        r = c.chat.completions.create(model=m, max_tokens=10, temperature=0,
            messages=[{"role":"user","content":prompt.format(prop=p)}])
        return parse(r.choices[0].message.content, valid, pat)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

def rate_anth(c, m, p, prompt, valid, pat):
    try:
        r = c.messages.create(model=m, max_tokens=10,
            messages=[{"role":"user","content":prompt.format(prop=p)}])
        return parse(r.content[0].text if r.content else None, valid, pat)
    except Exception as e:
        sys.stderr.write(f"anth-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

oai = OpenAI(base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL"),
             api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"))
anth = Anthropic(base_url=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL"),
                 api_key=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY"))

RATERS = [
    ("oai_gptmini_A", "openai/gpt-4o-mini", rate_oai),
    ("oai_gptmini_B", "openai/gpt-4o-mini", rate_oai),
    ("anth_haiku45",  "claude-haiku-4-5",   rate_anth),
]

def rate_one(prop, prompt, valid, pat):
    out = {}
    with ThreadPoolExecutor(max_workers=3) as ex:
        futs = {}
        for name, model, fn in RATERS:
            client = oai if fn is rate_oai else anth
            futs[ex.submit(fn, client, model, prop, prompt, valid, pat)] = name
        for f in futs:
            out[futs[f]] = f.result()
    return out

def run_system(system_name, prompt, valid, pat, outfile):
    budget = float(os.environ.get("CHUNK_BUDGET_SEC", "95"))
    existing = json.load(open(outfile)) if outfile.exists() else []
    done_ids = {r["id"] for r in existing}
    todo = [p for p in GOLD if p["id"] not in done_ids]
    print(f"[{system_name}] {len(GOLD)} props; {len(existing)} done; {len(todo)} remaining")
    t0 = time.time()
    for i, p in enumerate(todo):
        if time.time() - t0 > budget:
            print(f"[{system_name}] budget {budget}s reached")
            break
        ratings = rate_one(p["text"], prompt, valid, pat)
        existing.append({"id": p["id"], "gold": p["gold"], "subgold": p.get("subgold"),
                         "text": p["text"], "ratings": ratings})
        if (len(existing)) % 10 == 0 or i == len(todo)-1:
            json.dump(existing, open(outfile, "w"), indent=1)
            print(f"[{system_name}] {len(existing)}/{len(GOLD)} elapsed={int(time.time()-t0)}s")
    json.dump(existing, open(outfile, "w"), indent=1)
    print(f"[{system_name}] chunk DONE: {len(existing)}/{len(GOLD)} total, {time.time()-t0:.1f}s elapsed")
    return len(existing) >= len(GOLD)

# Drive both systems in this single invocation, switching when one is complete.
SYS_LP_OUT = D / "ratings_lp.json"
SYS_FDE_OUT = D / "ratings_fde.json"

if __name__ == "__main__":
    only = os.environ.get("ONLY_SYS", "")
    if only == "LP" or only == "":
        done_lp = run_system("LP", PROMPT_LP, VALID_LP, PAT_LP, SYS_LP_OUT)
    else:
        done_lp = (SYS_LP_OUT.exists() and len(json.load(open(SYS_LP_OUT))) >= len(GOLD))
    if done_lp and (only == "FDE" or only == ""):
        run_system("FDE", PROMPT_FDE, VALID_FDE, PAT_FDE, SYS_FDE_OUT)
