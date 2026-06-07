"""
Pass-77 B115 — Comprehensive, wellbeing-WEIGHTED concentration of the inventions
(material AND abstract) that humanity most has to thank, with ALL primary
contributors counted.

Extends B92 three ways, per Brandon's directive:
  (1) count ALL people PRIMARILY RESPONSIBLE for each invention (not just the lead
      catalyst) -> the "comprehensive percentage of the population to thank";
  (2) add ABSTRACT / FOUNDATIONAL inventions (religion, philosophy, writing,
      mathematics, logic, law, democracy, the scientific method, ethics ...);
  (3) WEIGHT inventions by how much they contribute to wellbeing COLLECTIVELY
      (consensus rater score) and compute what fraction of humanity delivered
      what fraction of the TOTAL cumulative wellbeing mass (Lorenz / share curve).

3 independent LLM raters (gpt-5 via Replit OpenAI integration; claude-opus-4-1
@temp0.0 and claude-haiku-4-5 @temp0.4 via Replit Anthropic integration), the
corpus-standard config (== B92). Fleiss kappa reported straight (#69).

#69 honesty carried over from B92 + sharpened here:
  - Attribution is contestable for cumulative inventions; the hybrid
    Indeterminate-True resolution (catalyst True / exclusivity False /
    catalyst+followers True) is exactly why we report a RANGE, not a point.
  - Abstract inventions (esp. religion) are VALENCE-CONTESTED: reasonable people
    dispute the *sign* of net wellbeing for some. We include them per directive,
    rate NET wellbeing, and flag the contest rather than hide it. Many are deeply
    DIFFUSE (no single catalyst) -> counted as movement-attributed, which widens
    the honest range.
  - novelty (#69, Brandon recalibration 2026-06-07) = "rare enough to be
    pragmatically useful", not "never written before".
"""
import os, re, json, time

# (name, [primary attributed individuals], domain)  -- [] = diffuse / no single catalyst
# domain: "material" (B92 carryover) or "abstract" (B115 addition)
INVENTIONS = [
    # ---- B92 carryover (material / medical / tech / public-health) ----
    ("Smallpox vaccine", ["Edward Jenner"], "material"),
    ("Antibiotics / penicillin", ["Alexander Fleming", "Howard Florey", "Ernst Chain"], "material"),
    ("Modern sewerage / sanitation", ["Joseph Bazalgette"], "material"),
    ("Germ theory of disease", ["Louis Pasteur", "Robert Koch"], "material"),
    ("Pasteurization", ["Louis Pasteur"], "material"),
    ("Drinking-water chlorination", ["John Leal", "Abel Wolman"], "material"),
    ("Oral rehydration therapy", ["Dilip Mahalanabis", "Hemendra Nath Chatterjee"], "material"),
    ("Surgical anesthesia (ether)", ["William T. G. Morton", "Crawford Long"], "material"),
    ("Antiseptic surgery", ["Joseph Lister"], "material"),
    ("Insulin", ["Frederick Banting", "Charles Best", "John Macleod", "James Collip"], "material"),
    ("Polio vaccine", ["Jonas Salk", "Albert Sabin"], "material"),
    ("X-ray imaging", ["Wilhelm Roentgen"], "material"),
    ("Blood typing / safe transfusion", ["Karl Landsteiner"], "material"),
    ("Attenuated-vaccine principle", ["Louis Pasteur"], "material"),
    ("Haber-Bosch nitrogen fixation", ["Fritz Haber", "Carl Bosch"], "material"),
    ("Mechanical refrigeration", ["Carl von Linde", "Jacob Perkins"], "material"),
    ("Electric generator / dynamo", ["Michael Faraday"], "material"),
    ("Incandescent light bulb", ["Thomas Edison", "Joseph Swan"], "material"),
    ("Printing press (movable type)", ["Johannes Gutenberg"], "material"),
    ("Telephone", ["Alexander Graham Bell"], "material"),
    ("Radio", ["Guglielmo Marconi", "Nikola Tesla"], "material"),
    ("Transistor", ["John Bardeen", "Walter Brattain", "William Shockley"], "material"),
    ("Internet (TCP/IP)", ["Vint Cerf", "Bob Kahn"], "material"),
    ("World Wide Web", ["Tim Berners-Lee"], "material"),
    ("General-purpose computer", ["Alan Turing", "John von Neumann", "Charles Babbage"], "material"),
    ("Steam engine", ["James Watt", "Thomas Newcomen"], "material"),
    ("Internal combustion engine", ["Nikolaus Otto", "Karl Benz"], "material"),
    ("Electric battery", ["Alessandro Volta"], "material"),
    ("Telegraph", ["Samuel Morse"], "material"),
    ("Eyeglasses", [], "material"),
    ("Chloroform obstetric anesthesia", ["James Young Simpson"], "material"),
    ("Safe cesarean section", [], "material"),
    ("Quinine isolation (antimalarial)", ["Pierre-Joseph Pelletier", "Joseph Caventou"], "material"),
    ("Antiretroviral therapy (HIV)", ["David Ho", "Samuel Broder"], "material"),
    ("mRNA vaccine platform", ["Katalin Kariko", "Drew Weissman"], "material"),
    ("Hand hygiene (puerperal fever)", ["Ignaz Semmelweis"], "material"),
    ("Modern nursing / hospital sanitation", ["Florence Nightingale"], "material"),
    ("DNA double-helix structure", ["James Watson", "Francis Crick", "Rosalind Franklin"], "material"),
    ("PCR amplification", ["Kary Mullis"], "material"),
    ("Recombinant DNA", ["Stanley Cohen", "Herbert Boyer"], "material"),
    ("CRISPR gene editing", ["Jennifer Doudna", "Emmanuelle Charpentier"], "material"),
    ("Kidney dialysis", ["Willem Kolff"], "material"),
    ("Implantable pacemaker", ["Wilson Greatbatch", "Rune Elmqvist"], "material"),
    ("Aspirin", ["Felix Hoffmann"], "material"),
    ("Chlorpromazine (antipsychotic)", ["Henri Laborit", "Jean Delay", "Pierre Deniker"], "material"),
    ("Statins", ["Akira Endo"], "material"),
    ("Vitamin discovery", ["Casimir Funk", "Christiaan Eijkman"], "material"),
    ("Iodized salt", ["David Marine"], "material"),
    ("Green Revolution high-yield wheat", ["Norman Borlaug"], "material"),
    ("Mechanized tractor", ["John Froelich"], "material"),
    ("Steel moldboard plow", ["John Deere"], "material"),
    ("Food canning / appertization", ["Nicolas Appert"], "material"),
    ("Flush toilet (S-trap)", ["Alexander Cumming"], "material"),
    ("Insecticide DDT (historical)", ["Paul Hermann Mueller"], "material"),
    ("Three-point seatbelt", ["Nils Bohlin"], "material"),
    ("Measles vaccine", ["John Enders"], "material"),
    ("Diphtheria/tetanus antitoxin", ["Emil von Behring", "Kitasato Shibasaburo"], "material"),
    ("Local anesthesia (procaine)", ["Karl Koller", "Alfred Einhorn"], "material"),
    ("Blood bank / plasma storage", ["Charles Drew"], "material"),
    ("Medical ultrasound", ["Ian Donald"], "material"),
    ("MRI", ["Paul Lauterbur", "Peter Mansfield"], "material"),
    ("CT scan", ["Godfrey Hounsfield", "Allan Cormack"], "material"),
    ("Beta blockers + H2 antagonists", ["James Black"], "material"),
    ("Oral contraceptive pill", ["Gregory Pincus", "Min Chueh Chang", "John Rock"], "material"),
    ("Electronic hearing aid", [], "material"),
    ("Modern wheelchair (folding)", ["Herbert Everest", "Harry Jennings"], "material"),
    ("Braille", ["Louis Braille"], "material"),
    ("Formal sign language education", ["Charles-Michel de l'Epee"], "material"),
    ("Photovoltaic solar cell", ["Daryl Chapin", "Calvin Fuller", "Gerald Pearson"], "material"),
    ("Electric wind turbine", ["Poul la Cour", "Charles Brush"], "material"),
    ("Archimedes water screw", ["Archimedes"], "material"),
    ("Portland cement / concrete", ["Joseph Aspdin"], "material"),
    ("Bessemer steel process", ["Henry Bessemer"], "material"),
    ("Bakelite (first plastic)", ["Leo Baekeland"], "material"),
    ("Chlorine disinfectant (Labarraque)", ["Antoine Labarraque", "Claude Berthollet"], "material"),
    ("Hepatitis B vaccine", ["Baruch Blumberg"], "material"),
    ("HPV vaccine", ["Ian Frazer", "Jian Zhou"], "material"),
    ("Implantable defibrillator/CPR", ["Claude Beck", "William Kouwenhoven"], "material"),
    ("Artemisinin antimalarial", ["Tu Youyou"], "material"),
    ("Intraocular lens / cataract surgery", ["Harold Ridley"], "material"),
    ("Ivermectin (antiparasitic)", ["Satoshi Omura", "William Campbell"], "material"),
    ("Piped clean water at scale", ["Abel Wolman", "John Leal"], "material"),
    ("Anti-tuberculosis chemotherapy", ["Selman Waksman"], "material"),
    ("Smallpox eradication program", ["Donald Henderson"], "material"),
    ("Refrigerated vaccine cold chain", [], "material"),
    ("Insecticide-treated bed nets", [], "material"),
    ("Smoke detector", [], "material"),
    ("Airbag", [], "material"),
    ("Anti-rejection transplant immunosuppression", ["Jean Borel", "Roy Calne"], "material"),
    ("Organ transplantation (kidney)", ["Joseph Murray"], "material"),
    ("Cardiac bypass / heart-lung machine", ["John Gibbon"], "material"),
    ("Hip/joint replacement", ["John Charnley"], "material"),
    ("Cochlear implant", ["Graeme Clark"], "material"),
    ("Antidepressants (SSRIs/MAOIs)", [], "material"),
    ("Anticoagulants (warfarin/heparin)", ["Karl Paul Link"], "material"),
    ("Sterile syringe / hypodermic needle", ["Alexander Wood", "Charles Pravaz"], "material"),
    ("Sanitary disposable menstrual products", [], "material"),
    ("Water-sealed sand filtration", ["John Gibb"], "material"),

    # ---- B115 ADDITIONS: abstract / foundational inventions ----
    # Language, writing, number, reasoning
    ("Spoken language", [], "abstract"),
    ("Writing system (cuneiform)", [], "abstract"),
    ("Phonetic alphabet", [], "abstract"),
    ("Zero & positional notation", ["Brahmagupta"], "abstract"),
    ("Hindu-Arabic decimal numerals", ["Aryabhata", "Brahmagupta", "Al-Khwarizmi"], "abstract"),
    ("Deductive proof / axiomatic geometry", ["Euclid", "Thales", "Pythagoras"], "abstract"),
    ("Algebra", ["Al-Khwarizmi"], "abstract"),
    ("Calculus", ["Isaac Newton", "Gottfried Leibniz"], "abstract"),
    ("Formal logic", ["Aristotle"], "abstract"),
    ("Probability theory", ["Blaise Pascal", "Pierre de Fermat"], "abstract"),
    ("The scientific method", ["Ibn al-Haytham", "Francis Bacon", "Galileo Galilei"], "abstract"),
    ("Double-entry bookkeeping", ["Luca Pacioli"], "abstract"),
    # Governance, law, economy, society
    ("Codified law / rule of law", ["Hammurabi"], "abstract"),
    ("Democracy (civic self-government)", ["Cleisthenes", "Solon"], "abstract"),
    ("Coined money / standardized currency", [], "abstract"),
    ("Written constitution & human rights", [], "abstract"),
    ("Abolition of slavery (moral movement)", ["William Wilberforce"], "abstract"),
    ("Universal public schooling", ["Horace Mann", "John Amos Comenius"], "abstract"),
    ("Agriculture (Neolithic cultivation)", [], "abstract"),
    # Ethics, philosophy, contemplative & religious traditions (NET wellbeing; valence-contested)
    ("Systematic philosophy", ["Socrates", "Plato", "Aristotle"], "abstract"),
    ("Practical ethics / Stoicism", ["Zeno of Citium", "Epictetus", "Marcus Aurelius"], "abstract"),
    ("Utilitarian ethics", ["Jeremy Bentham", "John Stuart Mill"], "abstract"),
    ("The Golden Rule (ethic of reciprocity)", [], "abstract"),
    ("Contemplative practice / meditation", ["Gautama Buddha", "Patanjali"], "abstract"),
    ("Buddhism", ["Gautama Buddha"], "abstract"),
    ("Christianity", ["Jesus of Nazareth", "Paul the Apostle"], "abstract"),
    ("Islam", ["Muhammad"], "abstract"),
    ("Judaic monotheism", ["Moses", "Abraham"], "abstract"),
    ("Confucian social ethics", ["Confucius"], "abstract"),
    ("Daoism", ["Laozi"], "abstract"),
    ("Hindu / Vedic tradition", [], "abstract"),
    ("Psychotherapy / talk therapy", ["Sigmund Freud"], "abstract"),
]

CATS = ["0", "1", "2"]
N = len(INVENTIONS)

def build_prompt():
    lines = [f'{i+1}. {nm}' for i, (nm, _, _) in enumerate(INVENTIONS)]
    body = "\n".join(lines)
    return (
        "You are rating inventions and foundational human institutions by their TOTAL "
        "CONTRIBUTION TO HUMAN WELL-BEING and the MINIMIZATION OF SUFFERING across all "
        "of history (lives saved, suffering reduced, meaning/flourishing enabled, scale "
        "of benefit). Some items are ABSTRACT (e.g. writing, mathematics, philosophy, "
        "law, religion); rate their NET contribution to wellbeing as best you can, "
        "acknowledging that for some the net sign is genuinely contested.\n"
        "Use this 3-level scale for EACH item:\n"
        "  2 = world-historic, top-tier (shaped the wellbeing of billions)\n"
        "  1 = highly significant (large but not civilization-scale)\n"
        "  0 = important but NOT top-tier on the net-wellbeing/suffering axis\n\n"
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
                                  max_completion_tokens=16384)
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

def gini(values):
    xs = sorted(values)
    n = len(xs)
    if n == 0 or sum(xs) == 0:
        return 0.0
    cum = 0.0
    for i, x in enumerate(xs, 1):
        cum += i * x
    return (2 * cum) / (n * sum(xs)) - (n + 1) / n

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
    R = len(rater_dicts)

    # consensus wellbeing weight per invention = sum of rater scores (0..2R)
    weighted = []
    for it in common_items:
        w = sum(d[it] for d in rater_dicts)
        nm, people, dom = INVENTIONS[it - 1]
        weighted.append({"idx": it, "name": nm, "weight": w, "people": people, "domain": dom})
    weighted.sort(key=lambda r: (-r["weight"], r["idx"]))

    total_W = sum(r["weight"] for r in weighted)

    HUMANS_EVER = 117e9   # PRB 2022 estimate of humans ever born
    LIVING = 8.1e9        # ~2026 world population

    # ---- (1) comprehensive people-to-thank: ALL primary contributors, whole list ----
    all_named, all_catalysts, diffuse_items = set(), set(), 0
    for r in weighted:
        if not r["people"]:
            diffuse_items += 1
            continue
        all_catalysts.add(r["people"][0])
        for p in r["people"]:
            all_named.add(p)
    n_named = len(all_named)
    n_cat = len(all_catalysts)

    # ---- (3) wellbeing-weighted concentration: people behind X% of total wellbeing ----
    def people_for_share(share):
        target = share * total_W
        acc, named = 0.0, set()
        n_diffuse = 0
        for r in weighted:
            acc += r["weight"]
            if r["people"]:
                named.update(r["people"])
            else:
                n_diffuse += 1
            if acc >= target:
                break
        return len(named), n_diffuse
    share_levels = {}
    for s in (0.50, 0.90, 0.95, 0.99, 1.00):
        n_p, n_d = people_for_share(s)
        share_levels[f"{int(s*100)}pct_wellbeing"] = {
            "named_people": n_p,
            "diffuse_movements_included": n_d,
            "pct_of_humans_ever": n_p / HUMANS_EVER * 100.0,
            "one_in_X_humans_ever": int(HUMANS_EVER / n_p) if n_p else None,
        }

    # per-person wellbeing mass (each invention's weight split equally among its primaries)
    person_mass = {}
    diffuse_mass = 0.0
    for r in weighted:
        if r["people"]:
            share = r["weight"] / len(r["people"])
            for p in r["people"]:
                person_mass[p] = person_mass.get(p, 0.0) + share
        else:
            diffuse_mass += r["weight"]
    named_mass = sum(person_mass.values())

    # Gini computed over NAMED CONTRIBUTORS ONLY (concentration *within* the thin
    # catalyst layer). NB: across all humans-ever (~117e9 carry 0 mass) Gini ->~1.0
    # trivially; the named-only Gini is the informative quantity.
    masses_named = list(person_mass.values())
    gini_named_only = gini(masses_named)

    def pct(n, denom):
        return n / denom * 100.0

    summary = {
        "n_inventions_total": N,
        "n_material": sum(1 for _, _, d in INVENTIONS if d == "material"),
        "n_abstract": sum(1 for _, _, d in INVENTIONS if d == "abstract"),
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
        "total_wellbeing_weight": total_W,
        "diffuse_items_no_single_catalyst": diffuse_items,
        # comprehensive headcount (whole curated list)
        "n_distinct_catalysts_all": n_cat,
        "n_distinct_named_all": n_named,
        "pct_of_humans_ever__named_all": pct(n_named, HUMANS_EVER),
        "pct_of_humans_ever__catalysts_all": pct(n_cat, HUMANS_EVER),
        "one_in_X_humans_ever__named_all": int(HUMANS_EVER / n_named) if n_named else None,
        "one_in_X_humans_ever__catalysts_all": int(HUMANS_EVER / n_cat) if n_cat else None,
        "pct_of_living__named_all": pct(n_named, LIVING),
        # wellbeing-weighted shares
        "wellbeing_share_levels": share_levels,
        "named_wellbeing_mass_fraction": round(named_mass / total_W, 4),
        "diffuse_wellbeing_mass_fraction": round(diffuse_mass / total_W, 4),
        "gini_named_contributors": round(gini_named_only, 4),
        "humans_ever_lived": HUMANS_EVER,
        "currently_living": LIVING,
    }
    ranked = [{"rank": i + 1, "invention": r["name"], "weight": r["weight"],
               "domain": r["domain"], "people": r["people"]}
              for i, r in enumerate(weighted)]
    top_people = sorted(person_mass.items(), key=lambda kv: -kv[1])[:25]
    return {"summary": summary, "ranked": ranked,
            "top_people_by_wellbeing_mass": [{"person": p, "mass": round(m, 3)} for p, m in top_people],
            "p_j": p_j, "kappa": kappa}

if __name__ == "__main__":
    import sys
    out = main()
    with open("analyses/pass77_b115_wellbeing_weighted_concentration/results.json", "w") as f:
        json.dump(out, f, indent=2)
    json.dump(out.get("summary", out), sys.stdout, indent=2)
