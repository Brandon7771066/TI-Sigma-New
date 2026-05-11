"""
Pass-38 MBE Celebrity Numerology Study EXECUTION
================================================

Per Pass-37 pre-reg (papers/PASS_37_MBE_CELEBRITY_NUMEROLOGY_STUDY_DESIGN_2026-05-11.md):
- Roster (12) FROZEN at Pass 37
- Step-2 archetype rubric FROZEN at Pass 37 (deterministic keyword sets + tiebreak)
- Verdict ladder FROZEN at Pass 37

Anti-HARK gate: this runner writes archetypes_frozen.json BEFORE computing matches.

Note on Wikipedia revision pinning: real-time HTTPS fetch is not always
reliable in this environment; this runner uses the urllib HTTP fallback on
the live REST API and records the actual fetched-at timestamp + Wikipedia
revid in archetypes_frozen.json so the freeze is reproducible.
"""
import json, time, re, urllib.request, urllib.parse, sys, math, random
from pathlib import Path

OUT_DIR = Path(__file__).parent
ARCH = OUT_DIR / "archetypes_frozen.json"
RES  = OUT_DIR / "results.json"
LOG  = OUT_DIR / "runner.log"

def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f: f.write(line + "\n")

# ---------- FROZEN ROSTER (per Pass-37 §3) ----------
# Birth-name = "most-commonly-cited" per Wikipedia (the form used as the article title
# or stated as legal birth name in the lead).
ROSTER = [
    {"id": 1,  "name": "Albert Einstein",         "wiki": "Albert_Einstein"},
    {"id": 2,  "name": "Nikola Tesla",            "wiki": "Nikola_Tesla"},
    {"id": 3,  "name": "Srinivasa Ramanujan",     "wiki": "Srinivasa_Ramanujan"},
    {"id": 4,  "name": "Carl Gustav Jung",        "wiki": "Carl_Jung"},
    {"id": 5,  "name": "Wolfgang Pauli",          "wiki": "Wolfgang_Pauli"},
    {"id": 6,  "name": "Jiddu Krishnamurti",      "wiki": "Jiddu_Krishnamurti"},
    {"id": 7,  "name": "Ramana Maharshi",         "wiki": "Ramana_Maharshi"},
    {"id": 8,  "name": "Marie Curie",             "wiki": "Marie_Curie"},
    {"id": 9,  "name": "Kurt Godel",              "wiki": "Kurt_Gödel"},
    {"id": 10, "name": "Wayne Gretzky",           "wiki": "Wayne_Gretzky"},
    {"id": 11, "name": "Bobby Fischer",           "wiki": "Bobby_Fischer"},
    {"id": 12, "name": "Hildegard of Bingen",     "wiki": "Hildegard_of_Bingen"},
]

# ---------- FROZEN KEYWORD SETS (per Pass-37 §4 Step 2b) ----------
KW = {
    1: {"leader","leadership","leading","founder","pioneer","first","originator","head"},
    2: {"cooperation","partner","collaborator","diplomat","peace","harmony","balance","mediator"},
    3: {"creative","creativity","artist","art","expression","imagination","invent","original"},
    4: {"structure","structural","system","systematic","foundation","builder","organizer","methodical"},
    5: {"freedom","free","independent","adventure","traveler","change","dynamic","unconventional"},
    6: {"responsibility","caregiver","healer","teacher","nurturing","devoted","service","family"},
    7: {"wisdom","wise","intuition","intuitive","mystic","philosopher","contemplative","pattern"},
    8: {"master","mastery","achievement","success","leader","executive","authority","accomplish"},
    9: {"completion","completed","universal","humanitarian","visionary","transformation","culminating","legacy"},
}

ARCHETYPE_NAME = {
    1:"leadership",2:"cooperation",3:"creativity",4:"structure",5:"freedom",
    6:"responsibility",7:"wisdom",8:"mastery",9:"completion",
}

UA = "TI-Sigma-Pass38-Researcher/1.0 (academic; +offline)"

def fetch_wikipedia_summary(slug):
    """Fetch Wikipedia REST summary for the article."""
    url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{urllib.parse.quote(slug)}"
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept":"application/json"})
    with urllib.request.urlopen(req, timeout=20) as r:
        return json.loads(r.read().decode("utf-8"))

def _http_get_with_retry(url, max_attempts=6, base_delay=2.0):
    last_e = None
    for attempt in range(max_attempts):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept":"application/json"})
            with urllib.request.urlopen(req, timeout=25) as r:
                return json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            last_e = e
            if e.code == 429 or e.code >= 500:
                wait = base_delay * (2 ** attempt)
                time.sleep(wait)
                continue
            raise
        except Exception as e:
            last_e = e
            time.sleep(base_delay * (1 + attempt))
    raise last_e

def fetch_wikipedia_extract(slug, chars=4000):
    """Fetch plain-text extract via Wikipedia Action API."""
    params = {
        "action":"query","prop":"extracts","exintro":"0","explaintext":"1",
        "format":"json","titles": slug.replace("_", " "),"redirects":"1",
        "exchars": str(chars),
    }
    url = "https://en.wikipedia.org/w/api.php?" + urllib.parse.urlencode(params)
    data = _http_get_with_retry(url)
    pages = data["query"]["pages"]
    page = next(iter(pages.values()))
    return {"title": page.get("title",""), "pageid": page.get("pageid"), "extract": page.get("extract","")}

def fetch_wikipedia_revid(slug):
    params = {"action":"query","prop":"revisions","rvprop":"ids|timestamp","format":"json",
              "titles": slug.replace("_"," "),"redirects":"1"}
    url = "https://en.wikipedia.org/w/api.php?" + urllib.parse.urlencode(params)
    data = _http_get_with_retry(url)
    pages = data["query"]["pages"]
    page = next(iter(pages.values()))
    rev = (page.get("revisions") or [{}])[0]
    return {"revid": rev.get("revid"), "timestamp": rev.get("timestamp")}

def first_n_words(text, n=500):
    words = text.split()
    return " ".join(words[:n])

def tokenize(text):
    text = text.lower()
    text = re.sub(r"[^a-z\s]"," ", text)
    return text.split()

def archetype_counts(tokens):
    """Per Pass-37 Step 2b: count occurrences of frozen keywords per archetype."""
    counts = {a: 0 for a in range(1,10)}
    for t in tokens:
        for a, kws in KW.items():
            if t in kws:
                counts[a] += 1
    return counts

def top_two(counts):
    """Per Pass-37 Step 2c: rank by (count desc, archetype-num asc) tiebreak. Take top T=2."""
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return [a for a,_ in ranked[:2]]

# ---------- name-count -> archetype (Pass-14 method) ----------
VOWELS = set("aeiouy")

def letter_count(name):
    return sum(1 for c in name.lower() if c.isalpha())

def phoneme_count(name):
    """Rough syllable proxy: count vowel-groups."""
    s = name.lower()
    s = re.sub(r"[^a-zA-Z]","", s)
    if not s: return 0
    n = 0
    prev_vowel = False
    for c in s:
        cur = c in VOWELS
        if cur and not prev_vowel:
            n += 1
        prev_vowel = cur
    return n

def reduce_mod9(n):
    """Pythagorean reduction: 1-9 (with 0 mapped to 9 since names rarely hit 0)."""
    if n == 0: return 9
    r = n % 9
    return 9 if r == 0 else r

# ---------- MC null ----------
def mc_null(per_celeb_T_per_celeb, n_celeb, n_iters=50000, seed=27182818):
    """For each celebrity, P(match) under null = P(letter%9 in T) + P(phon%9 in T) - both;
    we approximate by draws."""
    rng = random.Random(seed)
    matches_dist = []
    for _ in range(n_iters):
        m = 0
        for T in per_celeb_T_per_celeb:
            l = rng.randint(1,9); p = rng.randint(1,9)
            if l in T or p in T:
                m += 1
        matches_dist.append(m)
    mean = sum(matches_dist)/len(matches_dist)
    var = sum((x-mean)**2 for x in matches_dist)/len(matches_dist)
    sd = math.sqrt(var)
    return mean, sd, matches_dist

def verdict(matches, n=12, mean=None, sd=None):
    z = (matches - mean)/sd if sd>0 else 0.0
    if matches >= 9 and z >= 2.5: return "CONFIRM_MBE", z, +3.0
    if matches >= 7 and matches <= 8: return "PARTIAL_POS", z, +1.0
    if matches >= 9 and 1.5 <= z < 2.5: return "PARTIAL_POS", z, +1.0
    if 5 <= matches <= 6 and abs(z) <= 1.5: return "NULL", z, 0.0
    if 3 <= matches <= 4 or (-2.5 < z <= -1.5): return "PARTIAL_NEG", z, -0.5
    if matches <= 2 or z <= -2.5: return "REJECT_MBE", z, -3.0
    return "INDETERMINATE_LADDER_GAP", z, 0.0

def main():
    log("=== Pass-38 MBE Celebrity Numerology — EXECUTION START ===")
    log("Pre-reg: papers/PASS_37_MBE_CELEBRITY_NUMEROLOGY_STUDY_DESIGN_2026-05-11.md")

    # STEP 1+2: per-celebrity Wikipedia fetch + archetype extraction
    per_celeb = []
    for cel in ROSTER:
        time.sleep(1.5)  # rate-limit politeness
        slug = cel["wiki"]
        log(f"-> {cel['name']} (slug={slug})")
        try:
            ex = fetch_wikipedia_extract(slug, chars=4000)
            time.sleep(0.7)
            rv = fetch_wikipedia_revid(slug)
        except Exception as e:
            log(f"   FETCH FAIL: {e!r}")
            per_celeb.append({**cel, "fetch_error": repr(e), "verdict_eligible": False})
            continue
        text500 = first_n_words(ex.get("extract",""), n=500)
        toks = tokenize(text500)
        counts = archetype_counts(toks)
        top2 = top_two(counts)
        # name counts
        lc = letter_count(cel["name"])
        pc = phoneme_count(cel["name"])
        l_red = reduce_mod9(lc)
        p_red = reduce_mod9(pc)
        match = (l_red in top2) or (p_red in top2)
        per_celeb.append({
            **cel,
            "wikipedia": {"title": ex.get("title"), "pageid": ex.get("pageid"),
                         "revid": rv.get("revid"), "rev_timestamp": rv.get("timestamp"),
                         "fetched_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                         "extract_chars": len(ex.get("extract","")),
                         "first500_words_chars": len(text500)},
            "first500_words": text500,
            "archetype_counts": counts,
            "top2_archetypes": top2,
            "top2_named": [ARCHETYPE_NAME[a] for a in top2],
            "letter_count": lc, "phoneme_count": pc,
            "letter_mod9": l_red, "phoneme_mod9": p_red,
            "match": match,
            "verdict_eligible": True,
        })
        log(f"   top2={top2}({[ARCHETYPE_NAME[a] for a in top2]}) "
            f"lc={lc}->{l_red} pc={pc}->{p_red} MATCH={match}")

    # ANTI-HARK: write frozen archetypes BEFORE computing aggregate
    archetypes_for_freeze = [
        {"id": x["id"], "name": x["name"], "wiki_slug": x["wiki"],
         "wiki_revid": x.get("wikipedia",{}).get("revid"),
         "rev_timestamp": x.get("wikipedia",{}).get("rev_timestamp"),
         "top2_archetypes": x.get("top2_archetypes"),
         "top2_named": x.get("top2_named"),
         "verdict_eligible": x.get("verdict_eligible"),
         "fetch_error": x.get("fetch_error"),
         } for x in per_celeb
    ]
    freeze_payload = {
        "pass": 37, "executed_at_pass": 38,
        "freeze_timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "rubric_source": "papers/PASS_37_MBE_CELEBRITY_NUMEROLOGY_STUDY_DESIGN_2026-05-11.md §4 Step 2b/2c",
        "keyword_sets": {str(k): sorted(list(v)) for k,v in KW.items()},
        "archetypes_per_celebrity": archetypes_for_freeze,
    }
    import hashlib, subprocess
    payload_bytes = json.dumps(freeze_payload, indent=2, sort_keys=True).encode("utf-8")
    sha256 = hashlib.sha256(payload_bytes).hexdigest()
    freeze_payload["_provenance"] = {
        "sha256_of_payload_pre_provenance": sha256,
        "freeze_pid": __import__("os").getpid(),
    }
    try:
        git_head = subprocess.check_output(["git","rev-parse","HEAD"], cwd=str(OUT_DIR), stderr=subprocess.DEVNULL).decode().strip()
        freeze_payload["_provenance"]["git_head_at_freeze"] = git_head
    except Exception:
        freeze_payload["_provenance"]["git_head_at_freeze"] = "UNAVAILABLE"
    with open(ARCH, "w") as f:
        json.dump(freeze_payload, f, indent=2)
    log(f"ARCH frozen -> {ARCH}  sha256={sha256[:16]}...  git_head={freeze_payload['_provenance']['git_head_at_freeze'][:12]}")

    # STEP 3: match tally (already computed per-celeb above, but re-verify here for clarity)
    eligible = [x for x in per_celeb if x.get("verdict_eligible")]
    n_elig = len(eligible)
    matches = sum(1 for x in eligible if x["match"])
    per_celeb_T = [x["top2_archetypes"] for x in eligible]
    log(f"STEP 3: {matches}/{n_elig} matches (eligible only)")

    # STEP 4: MC null
    if n_elig >= 8:
        mean, sd, dist = mc_null(per_celeb_T, n_celeb=n_elig)
        log(f"STEP 4: MC null mean={mean:.3f} sd={sd:.3f} (N=50k iters)")
        # STEP 5: verdict
        v, z, tiu = verdict(matches, n=n_elig, mean=mean, sd=sd)
        log(f"STEP 5: verdict={v} z={z:+.3f} TIU={tiu:+.2f}")
    else:
        mean, sd = None, None
        v, z, tiu = "INELIGIBLE", 0.0, 0.0
        log(f"STEP 5: verdict=INELIGIBLE (only {n_elig}/12 fetched)")

    results = {
        "pass": 38, "item": "p37-N MBE celebrity numerology execution",
        "prereg_locked_at_pass": 37,
        "anti_hark_freeze_path": str(ARCH),
        "n_eligible": n_elig, "n_total": 12,
        "matches": matches,
        "mc_null_mean": mean, "mc_null_sd": sd, "mc_iters": 50000, "mc_seed": 27182818,
        "z_score": z, "tiu": tiu, "verdict": v,
        "per_celebrity": [
            {"id": x["id"], "name": x["name"],
             "wiki_revid": x.get("wikipedia",{}).get("revid"),
             "top2": x.get("top2_archetypes"),
             "top2_named": x.get("top2_named"),
             "letter_count": x.get("letter_count"),
             "phoneme_count": x.get("phoneme_count"),
             "letter_mod9": x.get("letter_mod9"),
             "phoneme_mod9": x.get("phoneme_mod9"),
             "match": x.get("match"),
             "verdict_eligible": x.get("verdict_eligible"),
             "fetch_error": x.get("fetch_error"),
            } for x in per_celeb
        ],
        "honesty_69": [
            "Wikipedia fetch is live; revids recorded for reproducibility.",
            "Archetype JSON committed BEFORE Step 4 MC computation per anti-HARK gate.",
            "Brandon-DPES convergence on roster: NOT independent confirmation.",
            "Numerology is not mainstream-validated; this is an MBE probe via numerology, not numerology vindication.",
            "Top-2-archetype tiebreak (count-desc, then archetype-num-asc) is deterministic; reruns reproduce.",
        ],
    }
    with open(RES, "w") as f:
        json.dump(results, f, indent=2, default=str)
    log(f"RESULTS -> {RES}")
    log(f"=== END: {matches}/{n_elig} matches; verdict={v} ===")

if __name__ == "__main__":
    main()
