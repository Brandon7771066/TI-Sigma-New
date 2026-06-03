import os, json
from concurrent.futures import ThreadPoolExecutor

ITEMS=[
 ("Water is H2O.","T"),("The Earth orbits the Sun.","T"),("2+2=4.","T"),("Paris is the capital of France.","T"),
 ("The Sun orbits the Earth.","F"),("2+2=5.","F"),("Humans breathe through gills.","F"),
 ("There is extraterrestrial microbial life somewhere in the universe.","I"),
 ("The number of grains of sand on Earth right now is even.","I"),
 ("It will rain in Paris exactly one year from today.","I"),
 ("This sentence is false.","MI"),
 ("The set of all sets that do not contain themselves contains itself.","MI"),
 ("There exists a square that is also a perfect circle.","MI"),
 ("What is the color of Wednesday?","NA"),
 ("How much does the number seven weigh in kilograms?","NA"),
 ("Please close the door.","NA"),
 ("Consciousness is fundamental AND emergent AND the question is malformed.","HMR"),
 ("Free will exists, does not exist, and the proposition is empirically moot.","HMR"),
 ("God exists.","HMR"),
]
PROMPT=("Classify the proposition into EXACTLY ONE truth-label. Label set: "
"T=clearly true; F=clearly false; I=indeterminate/unknown but truth-apt; "
"MI=meta-indeterminate (an inconceivable contradiction or self-referential paradox); "
"NA=not truth-apt (category error, command, or not a proposition); "
"HMR=hybrid (two or more of the above hold simultaneously and irreducibly). "
"Proposition: \"{p}\". Respond with ONLY the label code.")

def norm(t):
    t=t.strip().upper()
    for c in ["HMR","MI","NA","T","F","I"]:
        if t.startswith(c): return c
    return "?"

def call(p,temp):
    try:
        import anthropic
        c=anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        r=c.messages.create(model="claude-haiku-4-5",max_tokens=10,temperature=temp,
            messages=[{"role":"user","content":PROMPT.format(p=p)}])
        return norm(r.content[0].text)
    except Exception as e:
        return "ERR"

def one(it):
    p,exp=it
    return {"prop":p,"expected":exp,
            "r1":call(p,0.0),"r2":call(p,0.5),"r3":call(p,1.0)}

with ThreadPoolExecutor(max_workers=10) as ex:
    rows=list(ex.map(one, ITEMS))

cats=["T","F","I","MI","NA","HMR"]
rows=[r for r in rows if "ERR" not in (r["r1"],r["r2"],r["r3"])]
n=len(rows)
# Fleiss kappa, 3 raters
P_i=[]
for r in rows:
    labels=[r["r1"],r["r2"],r["r3"]]
    row=[labels.count(c) for c in cats]
    P_i.append(sum(x*(x-1) for x in row)/(3*2))
P_bar=sum(P_i)/n
tot=n*3
p_j=[sum(1 for r in rows for k in ("r1","r2","r3") if r[k]==c)/tot for c in cats]
P_e=sum(p*p for p in p_j)
kappa=(P_bar-P_e)/(1-P_e) if P_e<1 else 1.0
# accuracy vs expected (majority)
def maj(r):
    labels=[r["r1"],r["r2"],r["r3"]]; return max(labels,key=labels.count)
acc=sum(maj(r)==r["expected"] for r in rows)/n
summary={"n_items":n,"n_raters":3,"rater_type":"anthropic claude-haiku-4-5 @ T=0.0/0.5/1.0 (same-model pseudo-raters)",
 "fleiss_kappa_6way_incl_HMR":round(kappa,3),"majority_accuracy_vs_expected":round(acc,3),
 "HMR_1_F3":("NOT REFUTED (kappa>=0.5)" if kappa>=0.5 else "REFUTED (kappa<0.5)"),
 "prior_corpus_5tier_kappa_ref":"~0.77-0.84 (Pass-63 competent raters)"}
json.dump({"summary":summary,"rows":rows},open("analyses/pass77_b62_three_tests/hmr_results.json","w"),indent=2)
print(json.dumps(summary,indent=2))
print("\nper-item (expected | r1 r2 r3):")
for r in rows: print(f"  {r['expected']:4s} | {r['r1']:4s}{r['r2']:4s}{r['r3']:4s} | {r['prop'][:50]}")
