"""Fix-up: re-run only the openai raters for LP and FDE with correct model name.
Anthropic raters already populated; only oai_gptmini_A and oai_gptmini_B need refill.
"""
import json, os, re, sys, time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from openai import OpenAI

sys.path.insert(0, str(Path(__file__).parent))
from run_rivals import PROMPT_LP, PROMPT_FDE, VALID_LP, VALID_FDE, PAT_LP, PAT_FDE, parse

D = Path(__file__).parent
oai = OpenAI(base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL"),
             api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"))

MODEL = "gpt-4o-mini"

def rate_oai(p, prompt, valid, pat):
    try:
        r = oai.chat.completions.create(model=MODEL, max_tokens=10, temperature=0,
            messages=[{"role":"user","content":prompt.format(prop=p)}])
        return parse(r.choices[0].message.content, valid, pat)
    except Exception as e:
        sys.stderr.write(f"oai-err: {str(e)[:120]}\n"); sys.stderr.flush()
        return None

def fix_system(name, prompt, valid, pat, outfile):
    rows = json.load(open(outfile))
    budget = float(os.environ.get("CHUNK_BUDGET_SEC", "95"))
    needs_fix = [(i, r) for i, r in enumerate(rows)
                 if r["ratings"].get("oai_gptmini_A") is None
                 or r["ratings"].get("oai_gptmini_B") is None]
    print(f"[{name}] {len(needs_fix)}/{len(rows)} rows need oai fix")
    t0 = time.time()
    for j, (i, r) in enumerate(needs_fix):
        if time.time() - t0 > budget:
            print(f"[{name}] budget {budget}s reached at row {i}")
            break
        with ThreadPoolExecutor(max_workers=2) as ex:
            fA = ex.submit(rate_oai, r["text"], prompt, valid, pat) if r["ratings"].get("oai_gptmini_A") is None else None
            fB = ex.submit(rate_oai, r["text"], prompt, valid, pat) if r["ratings"].get("oai_gptmini_B") is None else None
            if fA is not None: r["ratings"]["oai_gptmini_A"] = fA.result()
            if fB is not None: r["ratings"]["oai_gptmini_B"] = fB.result()
        if (j+1) % 25 == 0 or j == len(needs_fix)-1:
            json.dump(rows, open(outfile,"w"), indent=1)
            print(f"[{name}] fixed {j+1}/{len(needs_fix)} elapsed={int(time.time()-t0)}s")
    json.dump(rows, open(outfile,"w"), indent=1)
    print(f"[{name}] chunk DONE: {sum(1 for r in rows if r['ratings'].get('oai_gptmini_A') and r['ratings'].get('oai_gptmini_B'))}/{len(rows)} fully-populated, {time.time()-t0:.1f}s")

if __name__ == "__main__":
    only = os.environ.get("ONLY_SYS", "")
    if only != "FDE":
        fix_system("LP", PROMPT_LP, VALID_LP, PAT_LP, D/"ratings_lp.json")
    if only != "LP":
        fix_system("FDE", PROMPT_FDE, VALID_FDE, PAT_FDE, D/"ratings_fde.json")
