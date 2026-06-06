"""
Pass-77 B92 — Concentration of well-being inventions + Fleiss kappa on the ranking.

3 independent LLM raters (gpt-5 via Replit OpenAI integration, claude-opus-4-1 via
Replit Anthropic integration, perplexity sonar) each score every invention's
importance for human well-being / suffering-reduction on {0,1,2}. We compute Fleiss
kappa on the ranking, take the consensus top-90, count distinct attributed
individuals, and express that as a fraction of humans-ever-lived and currently-living.

Honest #69 notes: attribution is contestable (inventions are cumulative). That
contestability is exactly the hybrid Indeterminate-True resolution (catalyst True,
exclusivity False, catalyst+followers True) — so we report a RANGE, not a point.
"""
import os, re, json, time

# (name, [primary attributed individuals])  -- '' / [] = diffuse/multiple
INVENTIONS = [
    ("Smallpox vaccine", ["Edward Jenner"]),
    ("Antibiotics / penicillin", ["Alexander Fleming", "Howard Florey", "Ernst Chain"]),
    ("Modern sewerage / sanitation", ["Joseph Bazalgette"]),
    ("Germ theory of disease", ["Louis Pasteur", "Robert Koch"]),
    ("Pasteurization", ["Louis Pasteur"]),
    ("Drinking-water chlorination", ["John Leal", "Abel Wolman"]),
    ("Oral rehydration therapy", ["Dilip Mahalanabis", "Hemendra Nath Chatterjee"]),
    ("Surgical anesthesia (ether)", ["William T. G. Morton", "Crawford Long"]),
    ("Antiseptic surgery", ["Joseph Lister"]),
    ("Insulin", ["Frederick Banting", "Charles Best", "John Macleod", "James Collip"]),
    ("Polio vaccine", ["Jonas Salk", "Albert Sabin"]),
    ("X-ray imaging", ["Wilhelm Roentgen"]),
    ("Blood typing / safe transfusion", ["Karl Landsteiner"]),
    ("Attenuated-vaccine principle", ["Louis Pasteur"]),
    ("Haber-Bosch nitrogen fixation", ["Fritz Haber", "Carl Bosch"]),
    ("Mechanical refrigeration", ["Carl von Linde", "Jacob Perkins"]),
    ("Electric generator / dynamo", ["Michael Faraday"]),
    ("Incandescent light bulb", ["Thomas Edison", "Joseph Swan"]),
    ("Printing press (movable type)", ["Johannes Gutenberg"]),
    ("Telephone", ["Alexander Graham Bell"]),
    ("Radio", ["Guglielmo Marconi", "Nikola Tesla"]),
    ("Transistor", ["John Bardeen", "Walter Brattain", "William Shockley"]),
    ("Internet (TCP/IP)", ["Vint Cerf", "Bob Kahn"]),
    ("World Wide Web", ["Tim Berners-Lee"]),
    ("General-purpose computer", ["Alan Turing", "John von Neumann", "Charles Babbage"]),
    ("Steam engine", ["James Watt", "Thomas Newcomen"]),
    ("Internal combustion engine", ["Nikolaus Otto", "Karl Benz"]),
    ("Electric battery", ["Alessandro Volta"]),
    ("Telegraph", ["Samuel Morse"]),
    ("Eyeglasses", []),
    ("Chloroform obstetric anesthesia", ["James Young Simpson"]),
    ("Safe cesarean section", []),
    ("Quinine isolation (antimalarial)", ["Pierre-Joseph Pelletier", "Joseph Caventou"]),
    ("Antiretroviral therapy (HIV)", ["David Ho", "Samuel Broder"]),
    ("mRNA vaccine platform", ["Katalin Kariko", "Drew Weissman"]),
    ("Hand hygiene (puerperal fever)", ["Ignaz Semmelweis"]),
    ("Modern nursing / hospital sanitation", ["Florence Nightingale"]),
    ("DNA double-helix structure", ["James Watson", "Francis Crick", "Rosalind Franklin"]),
    ("PCR amplification", ["Kary Mullis"]),
    ("Recombinant DNA", ["Stanley Cohen", "Herbert Boyer"]),
    ("CRISPR gene editing", ["Jennifer Doudna", "Emmanuelle Charpentier"]),
    ("Kidney dialysis", ["Willem Kolff"]),
    ("Implantable pacemaker", ["Wilson Greatbatch", "Rune Elmqvist"]),
    ("Aspirin", ["Felix Hoffmann"]),
    ("Chlorpromazine (antipsychotic)", ["Henri Laborit", "Jean Delay", "Pierre Deniker"]),
    ("Statins", ["Akira Endo"]),
    ("Vitamin discovery", ["Casimir Funk", "Christiaan Eijkman"]),
    ("Iodized salt", ["David Marine"]),
    ("Green Revolution high-yield wheat", ["Norman Borlaug"]),
    ("Mechanized tractor", ["John Froelich"]),
    ("Steel moldboard plow", ["John Deere"]),
    ("Food canning / appertization", ["Nicolas Appert"]),
    ("Flush toilet (S-trap)", ["Alexander Cumming"]),
    ("Insecticide DDT (historical)", ["Paul Hermann Mueller"]),
    ("Three-point seatbelt", ["Nils Bohlin"]),
    ("Measles vaccine", ["John Enders"]),
    ("Diphtheria/tetanus antitoxin", ["Emil von Behring", "Kitasato Shibasaburo"]),
    ("Local anesthesia (procaine)", ["Karl Koller", "Alfred Einhorn"]),
    ("Blood bank / plasma storage", ["Charles Drew"]),
    ("Medical ultrasound", ["Ian Donald"]),
    ("MRI", ["Paul Lauterbur", "Peter Mansfield"]),
    ("CT scan", ["Godfrey Hounsfield", "Allan Cormack"]),
    ("Beta blockers + H2 antagonists", ["James Black"]),
    ("Oral contraceptive pill", ["Gregory Pincus", "Min Chueh Chang", "John Rock"]),
    ("Electronic hearing aid", []),
    ("Modern wheelchair (folding)", ["Herbert Everest", "Harry Jennings"]),
    ("Braille", ["Louis Braille"]),
    ("Formal sign language education", ["Charles-Michel de l'Epee"]),
    ("Photovoltaic solar cell", ["Daryl Chapin", "Calvin Fuller", "Gerald Pearson"]),
    ("Electric wind turbine", ["Poul la Cour", "Charles Brush"]),
    ("Archimedes water screw", ["Archimedes"]),
    ("Portland cement / concrete", ["Joseph Aspdin"]),
    ("Bessemer steel process", ["Henry Bessemer"]),
    ("Bakelite (first plastic)", ["Leo Baekeland"]),
    ("Chlorine disinfectant (Labarraque)", ["Antoine Labarraque", "Claude Berthollet"]),
    ("Hepatitis B vaccine", ["Baruch Blumberg"]),
    ("HPV vaccine", ["Ian Frazer", "Jian Zhou"]),
    ("Implantable defibrillator/CPR", ["Claude Beck", "William Kouwenhoven"]),
    ("Artemisinin antimalarial", ["Tu Youyou"]),
    ("Intraocular lens / cataract surgery", ["Harold Ridley"]),
    ("Ivermectin (antiparasitic)", ["Satoshi Omura", "William Campbell"]),
    ("Piped clean water at scale", ["Abel Wolman", "John Leal"]),
    ("Anti-tuberculosis chemotherapy", ["Selman Waksman"]),
    ("Smallpox eradication program", ["Donald Henderson"]),
    ("Refrigerated vaccine cold chain", []),
    ("Insecticide-treated bed nets", []),
    ("Smoke detector", []),
    ("Airbag", []),
    ("Anti-rejection transplant immunosuppression", ["Jean Borel", "Roy Calne"]),
    ("Organ transplantation (kidney)", ["Joseph Murray"]),
    ("Cardiac bypass / heart-lung machine", ["John Gibbon"]),
    ("Hip/joint replacement", ["John Charnley"]),
    ("Cochlear implant", ["Graeme Clark"]),
    ("Antidepressants (SSRIs/MAOIs)", []),
    ("Anticoagulants (warfarin/heparin)", ["Karl Paul Link"]),
    ("Sterile syringe / hypodermic needle", ["Alexander Wood", "Charles Pravaz"]),
    ("Sanitary disposable menstrual products", []),
    ("Water-sealed sand filtration", ["John Gibb"]),
]

CATS = ["0", "1", "2"]
N = len(INVENTIONS)

def build_prompt():
    lines = [f'{i+1}. {nm}' for i, (nm, _) in enumerate(INVENTIONS)]
    body = "\n".join(lines)
    return (
        "You are rating inventions by their importance for HUMAN WELL-BEING and "
        "the MINIMIZATION OF SUFFERING (lives saved, suffering reduced, scale of benefit).\n"
        "Use this 3-level scale for EACH item:\n"
        "  2 = world-historic, top-tier (affected billions / massive suffering reduction)\n"
        "  1 = highly significant (large but not civilization-scale)\n"
        "  0 = important but NOT top-tier on the well-being/suffering axis\n\n"
        "Rate ALL of the following:\n" + body + "\n\n"
        "Return ONLY a JSON object mapping the item number (as a string) to its integer "
        'score 0, 1, or 2. Example: {"1": 2, "2": 1, ...}. No prose, no explanation.'
    )

def parse_scores(text):
    m = re.search(r"\{.*\}", text, re.DOTALL)
    if not m:
        return None
    try:
        raw = json.loads(m.group(0))
    except Exception:
        return None
    out = {}
    for k, v in raw.items():
        try:
            ki = int(re.sub(r"[^0-9]", "", str(k)))
            vi = int(v)
            if 1 <= ki <= N and vi in (0, 1, 2):
                out[ki] = vi
        except Exception:
            continue
    return out if len(out) >= int(0.9 * N) else None

def rater_openai(prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"),
               base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL"))
    r = c.chat.completions.create(model="gpt-5",
                                  messages=[{"role": "user", "content": prompt}],
                                  max_completion_tokens=8192)
    return r.choices[0].message.content or ""

def _anthropic_call(prompt, model, temp):
    import anthropic
    c = anthropic.Anthropic(api_key=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY"),
                            base_url=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL"))
    m = c.messages.create(model=model, max_tokens=4096, temperature=temp,
                          messages=[{"role": "user", "content": prompt}])
    return m.content[0].text if m.content and m.content[0].type == "text" else ""

def rater_opus(prompt):
    return _anthropic_call(prompt, "claude-opus-4-1", 0.0)

def rater_haiku(prompt):
    return _anthropic_call(prompt, "claude-haiku-4-5", 0.4)

def get_rater(name, fn, prompt):
    try:
        txt = fn(prompt)
        sc = parse_scores(txt)
        if sc is None:
            return None, f"{name}: parse-fail"
        return sc, f"{name}: ok ({len(sc)} items)"
    except Exception as e:
        return None, f"{name}: ERROR {e}"

def fleiss_kappa(rater_dicts):
    # rater_dicts: list of {item_idx: score}; only items rated by ALL raters
    common = set(rater_dicts[0])
    for d in rater_dicts[1:]:
        common &= set(d)
    items = sorted(common)
    R = len(rater_dicts)
    P_i = []
    cat_counts = {c: 0 for c in CATS}
    for it in items:
        labels = [str(d[it]) for d in rater_dicts]
        row = [labels.count(c) for c in CATS]
        for c in CATS:
            cat_counts[c] += labels.count(c)
        P_i.append((sum(x * (x - 1) for x in row)) / (R * (R - 1)))
    P_bar = sum(P_i) / len(items)
    total = len(items) * R
    p_j = [cat_counts[c] / total for c in CATS]
    P_e = sum(p * p for p in p_j)
    kappa = (P_bar - P_e) / (1 - P_e) if P_e < 1 else 1.0
    return kappa, items, p_j

def main():
    import sys as _sys
    prompt = build_prompt()
    raters, logs = [], []
    for name, fn in [("claude-haiku-4-5", rater_haiku), ("claude-opus-4-1", rater_opus),
                     ("gpt-5", rater_openai)]:
        t0 = time.time()
        print(f"[{name}] calling...", file=_sys.stderr, flush=True)
        sc, log = get_rater(name, fn, prompt)
        print(f"[{name}] {log}  ({time.time()-t0:.0f}s)", file=_sys.stderr, flush=True)
        logs.append(log)
        if sc is not None:
            raters.append((name, sc))
        time.sleep(0.3)

    if len(raters) < 2:
        return {"error": "fewer than 2 raters succeeded", "logs": logs}

    rater_dicts = [d for _, d in raters]
    kappa, common_items, p_j = fleiss_kappa(rater_dicts)

    # consensus score = sum across raters (only common items); rank, take top 90
    consensus = []
    for it in common_items:
        s = sum(d[it] for d in rater_dicts)
        consensus.append((it, s))
    consensus.sort(key=lambda x: (-x[1], x[0]))
    top90_idx = [it for it, _ in consensus[:90]]

    # distinct individuals among top-90
    named_all, catalysts, diffuse = set(), set(), 0
    for it in top90_idx:
        people = INVENTIONS[it - 1][1]
        if not people:
            diffuse += 1
            continue
        catalysts.add(people[0])
        for p in people:
            named_all.add(p)

    HUMANS_EVER = 117e9   # PRB 2022 estimate of humans ever born
    LIVING = 8.1e9        # ~2026 world population
    n_cat = len(catalysts)
    n_named = len(named_all)

    def pct(n, denom):
        return n / denom * 100.0

    summary = {
        "n_inventions": N,
        "n_raters": len(raters),
        "rater_names": [nm for nm, _ in raters],
        "rater_logs": logs,
        "fleiss_kappa": round(kappa, 4),
        "kappa_interp": (
            "almost perfect" if kappa >= 0.81 else "substantial" if kappa >= 0.61
            else "moderate" if kappa >= 0.41 else "fair" if kappa >= 0.21
            else "slight" if kappa > 0 else "poor"),
        "category_marginals_0_1_2": [round(x, 3) for x in p_j],
        "n_common_items_rated_by_all": len(common_items),
        "top90_count": len(top90_idx),
        "top90_diffuse_no_named_catalyst": diffuse,
        "n_distinct_catalysts": n_cat,
        "n_distinct_named_individuals": n_named,
        "humans_ever_lived": HUMANS_EVER,
        "currently_living": LIVING,
        "pct_of_humans_ever__catalysts": pct(n_cat, HUMANS_EVER),
        "pct_of_humans_ever__named": pct(n_named, HUMANS_EVER),
        "pct_of_living__catalysts": pct(n_cat, LIVING),
        "pct_of_living__named": pct(n_named, LIVING),
        "one_in_X_humans_ever__named": int(HUMANS_EVER / n_named) if n_named else None,
    }
    top90_named = [{"rank": r + 1, "invention": INVENTIONS[it - 1][0],
                    "score": s, "people": INVENTIONS[it - 1][1]}
                   for r, (it, s) in enumerate(consensus[:90])]
    return {"summary": summary, "top90": top90_named, "p_j": p_j, "kappa": kappa}

if __name__ == "__main__":
    import sys
    out = main()
    with open("analyses/pass77_b92_inventions_concentration/results.json", "w") as f:
        json.dump(out, f, indent=2)
    json.dump(out.get("summary", out), sys.stdout, indent=2)
