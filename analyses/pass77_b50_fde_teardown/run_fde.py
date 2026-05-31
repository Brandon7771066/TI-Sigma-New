"""
Pass-77-B50 — empirical teardown of Belnap-Dunn FDE vs TI Sigma.

Two charges:
  STUDY 1 ("Both" is 1D where reality is 2D): indeterminacy is a SPECTRUM
    INDEPENDENT of the true/false poles, and even strongly-true/strongly-false
    statements carry residual indeterminacy. FDE's single "Both" cannot express
    this. Items crossed: polarity {true,false} x indeterminacy {low,high}.
    Each rater gives: fde label {T,F,B,N}, truth 1-7, indet 1-7 (independent axes).
  STUDY 2 ("Neither" is a shrug): MI (meta-indeterminate) and NA (category
    mistake) are structurally distinct but both collapse to FDE "Neither".
    Each rater gives: fde {T,F,B,N} and ti {T,F,I,MI,NA}.

3 raters: 2x gpt-4o-mini + 1x claude-haiku-4-5, temp 0. Checkpoints per item.
$0 AI integrations.
"""
import json, os, re, sys, time
from openai import OpenAI
from anthropic import Anthropic

S1 = {
 "TL":["Water is composed of hydrogen and oxygen.","The Earth orbits the Sun.",
   "Two plus two equals four.","Paris is the capital of France.",
   "Humans need oxygen to survive.","Ice is frozen water."],
 "FL":["The Sun orbits the Earth.","Two plus two equals five.",
   "Whales are a kind of fish.","The Earth is flat.",
   "Humans can breathe underwater without any equipment.","Glass is a type of metal."],
 "TH":["A daily glass of red wine is good for your health.","Honesty is usually the best policy.",
   "Meditation improves long-term wellbeing.","Regular exercise makes people happier.",
   "Reading fiction increases empathy.","Free markets tend to improve overall welfare."],
 "FH":["Astrology accurately predicts personality.","Money reliably buys happiness.",
   "Natural talent matters more than practice for success.","Violent video games cause violent behavior.",
   "Technology is making people lonelier overall.","Modern art is objectively worse than classical art."],
}
S2_MI = [
 "Whether the sentence 'this statement is neither true nor false' itself has a truth-value is unsettled.",
 "It is indeterminate whether the question 'is the universe spatially infinite?' even has a determinate answer.",
 "Whether 'a heap minus one grain is still a heap' has a sharp truth-value is itself unclear.",
 "It may be indeterminate whether it is determinate that free will exists.",
 "Whether 'beauty is objective' is even a factual claim is itself an open question.",
 "It is unsettled whether the continuum hypothesis has a determinate truth-value at all.",
 "Whether qualia have a determinate physical nature may itself be an indeterminate matter.",
 "Whether the statement 'God exists' has a determinate truth-value is itself contested.",
]
S2_NA = [
 "The number 7 smells like vanilla.","The color green tastes triangular.",
 "Justice weighs four kilograms.","Wednesday is heavier than courage.",
 "The square root of democracy is purple.","Sincerity has a melting point of 200 degrees Celsius.",
 "The concept of velocity is married to Tuesday.","The smell of the number five is louder than Thursday.",
]

items=[]
for cell,texts in S1.items():
    pol = "true" if cell[0]=="T" else "false"
    ind = "low" if cell[1]=="L" else "high"
    for i,t in enumerate(texts):
        items.append({"id":f"s1_{cell}{i+1}","study":1,"pol":pol,"indet":ind,"cell":cell,"text":t})
for i,t in enumerate(S2_MI):
    items.append({"id":f"s2_MI{i+1}","study":2,"gold":"MI","text":t})
for i,t in enumerate(S2_NA):
    items.append({"id":f"s2_NA{i+1}","study":2,"gold":"NA","text":t})

P1="""You are a careful logician. For the statement below, give THREE judgments as strict JSON.

Statement: "{t}"

1. "fde": classify under Belnap-Dunn First-Degree Entailment (FDE), EXACTLY one of:
   "T" = just true        "F" = just false
   "B" = BOTH true and false (overdetermined/contradictory)
   "N" = NEITHER true nor false (a truth-value gap)
2. "truth": integer 1-7, how TRUE the statement is (1=clearly false, 7=clearly true).
3. "indet": integer 1-7, how INDETERMINATE / unsettled / lacking a single fixed truth-value it is, INDEPENDENT of whether it leans true or false (1=fully determinate, 7=maximally contested/indeterminate).

Respond with ONLY JSON: {{"fde":"X","truth":N,"indet":N}}"""

P2="""You are a careful logician. For the statement below, give TWO classifications as strict JSON.

Statement: "{t}"

1. "fde": Belnap-Dunn FDE, EXACTLY one of "T","F","B","N":
   "T"=just true, "F"=just false, "B"=both true and false, "N"=neither true nor false.
2. "ti": the TI Sigma label, EXACTLY one of:
   "T"=true, "F"=false, "I"=indeterminate (a real but currently-unsettled truth-value),
   "MI"=META-indeterminate (whether it even HAS a determinate status is itself unsettled / second-order),
   "NA"=NOT APPLICABLE / category mistake (the predicate cannot meaningfully apply to the subject; type-incoherent).

Respond with ONLY JSON: {{"fde":"X","ti":"Y"}}"""

def extract(text):
    if not text: return {}
    m=re.search(r"\{.*\}", text, re.S)
    if not m: return {}
    try: return json.loads(m.group(0))
    except Exception: return {}

def ask_oai(c,model,prompt):
    try:
        r=c.chat.completions.create(model=model,max_tokens=40,temperature=0,
            messages=[{"role":"user","content":prompt}])
        return extract(r.choices[0].message.content)
    except Exception as e:
        sys.stderr.write(f"oai-err:{str(e)[:120]}\n"); return {}
def ask_anth(c,model,prompt):
    try:
        r=c.messages.create(model=model,max_tokens=40,
            messages=[{"role":"user","content":prompt}])
        return extract(r.content[0].text)
    except Exception as e:
        sys.stderr.write(f"anth-err:{str(e)[:120]}\n"); return {}

DIR="analyses/pass77_b50_fde_teardown"; OUT=f"{DIR}/ratings.json"
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
        print("time budget hit; checkpoint & exit",flush=True); break
    prompt=(P1 if it["study"]==1 else P2).format(t=it["text"])
    row=dict(it); row["ratings"]={}
    for rn,prov,model in RATERS:
        row["ratings"][rn]=ask_oai(oai,model,prompt) if prov=="oai" else ask_anth(anth,model,prompt)
    results.append(row)
    json.dump(results,open(OUT,"w"),indent=2)
    print(f"  {len(results)}/{len(items)} {it['id']} -> {row['ratings']}",flush=True)
print(f"DONE {len(results)}/{len(items)}",flush=True)
