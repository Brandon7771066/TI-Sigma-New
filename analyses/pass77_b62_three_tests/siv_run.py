import os, json, re
from concurrent.futures import ThreadPoolExecutor

FIGURES = ["Richard Feynman","Albert Einstein","Niels Bohr","Bertrand Russell","Srinivasa Ramanujan",
"Nikola Tesla","Marie Curie","Charles Darwin","Isaac Newton","Kurt Gödel","Alan Turing",
"John von Neumann","Paul Erdős","Paul Dirac","Wolfgang Pauli","Stephen Hawking","Carl Sagan",
"Ludwig Wittgenstein","Buckminster Fuller","Socrates","Diogenes of Sinope","Zhuangzi","Alan Watts",
"Ram Dass","Thich Nhat Hanh","Tenzin Gyatso (14th Dalai Lama)","Rumi","Friedrich Nietzsche",
"Galileo Galilei","Benjamin Franklin"]

PROMPT = ("Rate the historical figure {name} on two independent 0-10 scales using their documented biographical record. "
"(1) INTELLECT = intellectual and/or spiritual depth, originality and capacity. "
"(2) SILLINESS = documented playfulness, humor, whimsy, pranks, childlike silliness. "
'Respond with ONLY compact JSON, no prose: {{"intellect": <0-10>, "silliness": <0-10>}}')

def parse(txt):
    m=re.search(r'\{[^}]*\}', txt)
    if not m: return None
    try:
        d=json.loads(m.group(0)); return (float(d["intellect"]), float(d["silliness"]))
    except Exception: return None

def call_anthropic(name):
    try:
        import anthropic
        c=anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        r=c.messages.create(model="claude-haiku-4-5",max_tokens=40,temperature=0.0,
            messages=[{"role":"user","content":PROMPT.format(name=name)}])
        return parse(r.content[0].text)
    except Exception as e:
        return ("ERR",str(e)[:80])

def call_perplexity(name):
    try:
        from openai import OpenAI
        c=OpenAI(api_key=os.environ.get("PERPLEXITY_API_KEY"),base_url="https://api.perplexity.ai")
        r=c.chat.completions.create(model="sonar",max_tokens=40,temperature=0.0,
            messages=[{"role":"user","content":PROMPT.format(name=name)}])
        return parse(r.choices[0].message.content)
    except Exception as e:
        return ("ERR",str(e)[:80])

def one(name):
    return {"name":name,"anthropic":call_anthropic(name),"perplexity":call_perplexity(name)}

with ThreadPoolExecutor(max_workers=10) as ex:
    rows=list(ex.map(one, FIGURES))

def pearson(xs,ys):
    n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
    sxy=sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
    sx=sum((x-mx)**2 for x in xs)**.5; sy=sum((y-my)**2 for y in ys)**.5
    return sxy/(sx*sy) if sx*sy else 0.0

results={"raters":{}}
for rater in ["anthropic","perplexity"]:
    I=[];S=[]
    for r in rows:
        v=r[rater]
        if isinstance(v,tuple) and v and v[0]!="ERR":
            I.append(v[0]); S.append(v[1])
    if len(I)>=5:
        results["raters"][rater]={"n":len(I),"pearson_intellect_vs_silliness":round(pearson(I,S),3),
                                  "mean_intellect":round(sum(I)/len(I),2),"mean_silliness":round(sum(S)/len(S),2)}
    else:
        results["raters"][rater]={"n":len(I),"error_sample":[r[rater] for r in rows if isinstance(r[rater],tuple) and r[rater] and r[rater][0]=="ERR"][:2]}
# combined (avg of available raters)
Ic=[];Sc=[]
for r in rows:
    iv=[];sv=[]
    for rater in ["anthropic","perplexity"]:
        v=r[rater]
        if isinstance(v,tuple) and v and v[0]!="ERR": iv.append(v[0]); sv.append(v[1])
    if iv: Ic.append(sum(iv)/len(iv)); Sc.append(sum(sv)/len(sv))
if len(Ic)>=5:
    rr=pearson(Ic,Sc)
    results["combined"]={"n":len(Ic),"pearson_intellect_vs_silliness":round(rr,3),
        "SIV_1_F1":"REFUTED (negative corr)" if rr< -0.1 else "NOT REFUTED (corr >= -0.1; silliness coexists with intellect)"}
json.dump({"summary":results,"rows":rows}, open("analyses/pass77_b62_three_tests/siv_results.json","w"), indent=2, default=str)
print(json.dumps(results, indent=2))
