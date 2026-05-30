"""
GBD-1-F2 falsifier: the JUDGMENT-side test of the GILE-Backdrop Discriminator.

Prediction (GBD-1): the SAME slack/silly act is judged well-judged (high score)
when the actor has a HIGH competence backdrop, and foolish (low score) when the
actor has a LOW backdrop. The act text is held BYTE-IDENTICAL across conditions;
only one backdrop sentence changes.
REFUTED if the backdrop does not move the rating (mean_high - mean_low ~ 0).

Raters: 2x gpt-4o-mini + 1x claude-haiku-4-5 (same panel the corpus used before).
Score scale 1-7 (1 = foolish/incompetent, 7 = clever/well-judged/endearing).
Checkpoints after each item; safe to re-run to resume. $0-budget AI integrations.
"""
import json, os, re, sys, time
from openai import OpenAI
from anthropic import Anthropic

# 10 base scenarios. Each = one IDENTICAL act + two backdrops (high / low competence).
SCN = [
 {"id":"song", "hi":"a surgeon with a 20-year flawless operating record",
  "lo":"a trainee who has botched most procedures she has attempted",
  "act":"In the team meeting, she broke into a goofy improvised song to explain the quarterly plan."},
 {"id":"costume","hi":"a physicist whose predictions have repeatedly been confirmed by experiment",
  "lo":"a physicist whose predictions have repeatedly turned out wrong",
  "act":"He showed up to deliver the keynote wearing a full banana costume."},
 {"id":"riddle","hi":"a CEO who has grown three companies to profitability",
  "lo":"a CEO who has run two companies into bankruptcy",
  "act":"She answered the board's hardest question with a cryptic riddle instead of a direct answer."},
 {"id":"doodle","hi":"an architect whose buildings are admired worldwide",
  "lo":"an architect whose buildings have had to be condemned",
  "act":"He presented the city proposal as a set of childlike crayon doodles."},
 {"id":"dance","hi":"a diplomat who has brokered several lasting peace deals",
  "lo":"a diplomat whose talks have all collapsed acrimoniously",
  "act":"She opened the tense negotiation by doing a short silly dance."},
 {"id":"pun","hi":"a judge renowned for fair and careful rulings",
  "lo":"a judge repeatedly overturned on appeal for sloppy reasoning",
  "act":"He delivered the verdict laced with a string of groan-worthy puns."},
 {"id":"nap","hi":"a fund manager with a decade of market-beating returns",
  "lo":"a fund manager who has lost clients money every year",
  "act":"During the high-stakes pitch she announced she was taking a five-minute nap first."},
 {"id":"meme","hi":"a scientist with a long record of landmark discoveries",
  "lo":"a scientist whose papers have mostly failed to replicate",
  "act":"He explained the grant proposal entirely through internet memes."},
 {"id":"whisper","hi":"a general who has won every campaign he led",
  "lo":"a general who has lost every campaign he led",
  "act":"At the strategy briefing he insisted on speaking only in a theatrical whisper."},
 {"id":"juggle","hi":"a teacher whose students consistently excel",
  "lo":"a teacher whose students consistently fail",
  "act":"She taught the entire exam-review lesson while juggling oranges."},
]

PROMPT = """You are rating how WELL-JUDGED a single described action is.

Context: {actor} did the following: "{act}"

On a scale of 1 to 7, how wise / well-judged / appropriate was THIS ACTION in context?
  1 = foolish, incompetent, embarrassing
  7 = clever, well-judged, endearing, a sign of confident mastery

Respond with ONLY a single integer 1-7 and nothing else."""

def parse(t):
    if t is None: return None
    m = re.search(r"[1-7]", t)
    return int(m.group(0)) if m else None

def rate_oai(c,m,actor,act):
    try:
        r=c.chat.completions.create(model=m,max_tokens=5,temperature=0,
            messages=[{"role":"user","content":PROMPT.format(actor=actor,act=act)}])
        return parse(r.choices[0].message.content)
    except Exception as e:
        sys.stderr.write(f"oai-err:{str(e)[:120]}\n"); return None

def rate_anth(c,m,actor,act):
    try:
        r=c.messages.create(model=m,max_tokens=5,
            messages=[{"role":"user","content":PROMPT.format(actor=actor,act=act)}])
        return parse(r.content[0].text)
    except Exception as e:
        sys.stderr.write(f"anth-err:{str(e)[:120]}\n"); return None

DIR="analyses/pass77_b46_gbd1_f2"; OUT=f"{DIR}/ratings.json"
items=[]
for s in SCN:
    items.append({"id":f"{s['id']}_HI","scn":s["id"],"cond":"high","actor":s["hi"],"act":s["act"]})
    items.append({"id":f"{s['id']}_LO","scn":s["id"],"cond":"low","actor":s["lo"],"act":s["act"]})

done={}
if os.path.exists(OUT):
    for r in json.load(open(OUT)): done[r["id"]]=r
results=[done[i["id"]] for i in items if i["id"] in done]

oai=OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
anth=Anthropic(api_key=os.environ["AI_INTEGRATIONS_ANTHROPIC_API_KEY"],base_url=os.environ["AI_INTEGRATIONS_ANTHROPIC_BASE_URL"])
RATERS=[("R1_gpt4o","oai","gpt-4o-mini"),("R2_gpt4o","oai","gpt-4o-mini"),("R3_haiku","anth","claude-haiku-4-5")]

start=time.time()
for it in items:
    if it["id"] in done: continue
    if time.time()-start>105:
        print("time budget hit; checkpoint",flush=True); break
    row=dict(it); row["ratings"]={}
    for rn,prov,model in RATERS:
        v=rate_oai(oai,model,it["actor"],it["act"]) if prov=="oai" else rate_anth(anth,model,it["actor"],it["act"])
        row["ratings"][rn]=v
    results.append(row)
    json.dump(results,open(OUT,"w"),indent=2)
    print(f"  {len(results)}/{len(items)} {it['id']} -> {row['ratings']}",flush=True)
print(f"DONE {len(results)}/{len(items)}",flush=True)
