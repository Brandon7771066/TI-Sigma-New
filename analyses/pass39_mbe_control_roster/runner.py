"""
Pass-39 MBE Asymmetric-Hypothesis Test — CONTROL ROSTER

Brandon-Pass-39 directive (2026-05-11): "New hypothesis to test: Positive
numerology results predict GM Node status, but the converse is largely false."

Formal restatement:
- H_FORWARD: P(match | numerology-rubric, plausible-GM) > P(match | numerology-rubric, control)
  (numerology-MATCH is positive predictor of GM-Node status)
- H_CONVERSE: P(match | GM) high (Pass-38 already tested → 3/12 = 25% < null 40%)
  → CONVERSE largely FALSE (consistent with Brandon's stated hypothesis)

This runner tests H_FORWARD by applying the Pass-37 FROZEN rubric to a
control roster of 12 plausibly-non-GM celebrities and comparing match rate
against Pass-38's 3/12 GM rate.

Anti-HARK: control roster frozen BELOW (in-code) BEFORE rubric execution;
sha256 + git_head provenance recorded on freeze.

Verdict ladder (FROZEN here, Pass-39, BEFORE control execution):
- CONFIRM_FORWARD:  P(match|GM)=3/12=25% AND P(match|control) ≤ 1/12 (~8%);
                    Fisher exact p < 0.05; numerology DISCRIMINATES GM
- PARTIAL_POS:      P(match|control) = 1-2/12; Fisher p in [0.05, 0.20]
- NULL:             P(match|control) = 3-4/12; Fisher p > 0.20; no signal
- PARTIAL_NEG:      P(match|control) = 5-6/12; control matches MORE than GM
- REJECT_FORWARD:   P(match|control) ≥ 7/12; numerology predicts NON-GM
"""
import json, time, re, urllib.request, urllib.parse, math, hashlib, subprocess
from pathlib import Path

OUT = Path(__file__).parent
ARCH = OUT / "control_archetypes_frozen.json"
RES  = OUT / "results.json"
LOG  = OUT / "runner.log"

def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f: f.write(line + "\n")

# ---------- FROZEN CONTROL ROSTER (Pass-39, plausibly-non-GM-Node) ----------
# Selection criteria (frozen in-code BEFORE rubric run):
# - Mainstream entertainment-industry celebrities with no notable mystic/
#   scientific/foundational-philosophical contribution.
# - 12 names matching Pass-37 GM-roster N=12 for 1:1 Fisher comparison.
# - Gender-balanced (6F/6M) to avoid demographic confound.
# - Brandon-DPES default per "great minds AND NOT" doctrine: agent-selected
#   without Brandon convergence-influence (independence preserved).
CONTROL_ROSTER = [
    {"id": 1,  "name": "Tom Cruise",            "wiki": "Tom_Cruise"},
    {"id": 2,  "name": "Brad Pitt",             "wiki": "Brad_Pitt"},
    {"id": 3,  "name": "Jennifer Aniston",      "wiki": "Jennifer_Aniston"},
    {"id": 4,  "name": "Reese Witherspoon",     "wiki": "Reese_Witherspoon"},
    {"id": 5,  "name": "Will Smith",            "wiki": "Will_Smith"},
    {"id": 6,  "name": "Julia Roberts",         "wiki": "Julia_Roberts"},
    {"id": 7,  "name": "Adam Sandler",          "wiki": "Adam_Sandler"},
    {"id": 8,  "name": "Sandra Bullock",        "wiki": "Sandra_Bullock"},
    {"id": 9,  "name": "Matthew McConaughey",   "wiki": "Matthew_McConaughey"},
    {"id": 10, "name": "Cameron Diaz",          "wiki": "Cameron_Diaz"},
    {"id": 11, "name": "Ben Affleck",           "wiki": "Ben_Affleck"},
    {"id": 12, "name": "Jennifer Lawrence",     "wiki": "Jennifer_Lawrence"},
]

# ---------- IMPORT FROZEN PASS-37 RUBRIC FROM PASS-38 RUNNER ----------
import sys
sys.path.insert(0, str(OUT.parent / "pass38_mbe_celebrity_numerology"))
from runner import (KW, ARCHETYPE_NAME, fetch_wikipedia_extract, fetch_wikipedia_revid,
                    first_n_words, tokenize, archetype_counts, top_two,
                    letter_count, phoneme_count, reduce_mod9)

def fisher_exact_2x2(a, b, c, d):
    """One-sided Fisher exact test (right tail): P(X >= a) where X is hypergeom.
    table = [[a, b], [c, d]]; n1=a+b row, n2=c+d row, k1=a+c col."""
    n1, n2 = a+b, c+d
    k1 = a+c
    N = n1 + n2
    def lcomb(n, k):
        if k < 0 or k > n: return float("-inf")
        return math.lgamma(n+1) - math.lgamma(k+1) - math.lgamma(n-k+1)
    def lprob(x):
        return lcomb(n1, x) + lcomb(n2, k1-x) - lcomb(N, k1)
    p = 0.0
    for x in range(a, min(n1, k1)+1):
        p += math.exp(lprob(x))
    return p

def main():
    log("=== Pass-39 MBE Control-Roster Asymmetric Test — EXECUTION START ===")
    log(f"GM-roster reference: Pass-38 results 3/12 matches (PARTIAL_NEG)")
    log(f"Control roster (FROZEN in-code): N={len(CONTROL_ROSTER)} entertainment celebrities")

    per = []
    for cel in CONTROL_ROSTER:
        time.sleep(1.5)
        slug = cel["wiki"]
        log(f"-> {cel['name']} (slug={slug})")
        try:
            ex = fetch_wikipedia_extract(slug, chars=4000)
            time.sleep(0.7)
            rv = fetch_wikipedia_revid(slug)
        except Exception as e:
            log(f"   FETCH FAIL: {e!r}")
            per.append({**cel, "fetch_error": repr(e), "verdict_eligible": False})
            continue
        text500 = first_n_words(ex.get("extract",""), 500)
        toks = tokenize(text500)
        counts = archetype_counts(toks)
        top2 = top_two(counts)
        lc = letter_count(cel["name"]); pc = phoneme_count(cel["name"])
        l_red = reduce_mod9(lc); p_red = reduce_mod9(pc)
        match = (l_red in top2) or (p_red in top2)
        per.append({
            **cel,
            "wiki_revid": rv.get("revid"), "rev_timestamp": rv.get("timestamp"),
            "first500_chars": len(text500),
            "archetype_counts": counts,
            "top2_archetypes": top2,
            "top2_named": [ARCHETYPE_NAME[a] for a in top2],
            "letter_count": lc, "phoneme_count": pc,
            "letter_mod9": l_red, "phoneme_mod9": p_red,
            "match": match, "verdict_eligible": True,
        })
        log(f"   top2={top2}({[ARCHETYPE_NAME[a] for a in top2]}) "
            f"lc={lc}->{l_red} pc={pc}->{p_red} MATCH={match}")

    # FREEZE control archetypes BEFORE Fisher computation (anti-HARK)
    arch_payload = {
        "pass": 39, "rubric_source": "Pass-37 frozen rubric (imported from Pass-38 runner)",
        "control_roster_frozen_in_code_at_pass": 39,
        "freeze_timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "verdict_ladder_frozen_pre_execution": {
            "CONFIRM_FORWARD": "P(match|control) ≤ 1/12 AND Fisher p < 0.05",
            "PARTIAL_POS":     "P(match|control) = 1-2/12 AND Fisher p in [0.05, 0.20]",
            "NULL":            "P(match|control) = 3-4/12 AND Fisher p > 0.20",
            "PARTIAL_NEG":     "P(match|control) = 5-6/12; control matches MORE than GM",
            "REJECT_FORWARD":  "P(match|control) ≥ 7/12; numerology predicts NON-GM",
        },
        "control_per_celebrity": [
            {k: v for k, v in p.items() if k != "first500_words"} for p in per
        ],
    }
    payload_bytes = json.dumps(arch_payload, indent=2, sort_keys=True).encode("utf-8")
    sha = hashlib.sha256(payload_bytes).hexdigest()
    arch_payload["_provenance"] = {"sha256_of_payload_pre_provenance": sha}
    try:
        git_head = subprocess.check_output(["git","rev-parse","HEAD"], cwd=str(OUT),
                                            stderr=subprocess.DEVNULL).decode().strip()
        arch_payload["_provenance"]["git_head_at_freeze"] = git_head
    except Exception:
        arch_payload["_provenance"]["git_head_at_freeze"] = "UNAVAILABLE"
    with open(ARCH, "w") as f:
        json.dump(arch_payload, f, indent=2, default=str)
    log(f"ARCH frozen -> {ARCH}  sha256={sha[:16]}...  git={arch_payload['_provenance']['git_head_at_freeze'][:12]}")

    # COMPUTE: Fisher exact 2x2 (GM vs control)
    elig = [p for p in per if p.get("verdict_eligible")]
    n_ctrl = len(elig)
    m_ctrl = sum(1 for p in elig if p.get("match"))
    m_gm, n_gm = 3, 12  # Pass-38 frozen result
    # 2x2: rows = [match, no-match]; cols = [GM, control]
    # a=GM-match, b=ctrl-match, c=GM-nomatch, d=ctrl-nomatch
    a, b = m_gm, m_ctrl
    c, d = n_gm - m_gm, n_ctrl - m_ctrl
    p_one_sided_GM_higher = fisher_exact_2x2(a, b, c, d)
    log(f"\n=== ASYMMETRIC HYPOTHESIS TEST RESULT ===")
    log(f"GM cluster:      {m_gm}/{n_gm} matched ({100*m_gm/n_gm:.1f}%) — Pass-38")
    log(f"Control cluster: {m_ctrl}/{n_ctrl} matched ({100*m_ctrl/n_ctrl:.1f}%) — Pass-39")
    log(f"Fisher exact one-sided (GM > control): p = {p_one_sided_GM_higher:.4f}")

    # Verdict per FROZEN ladder
    if m_ctrl <= 1 and p_one_sided_GM_higher < 0.05:
        v = "CONFIRM_FORWARD"; tiu = +3.0
    elif 1 <= m_ctrl <= 2 and 0.05 <= p_one_sided_GM_higher <= 0.20:
        v = "PARTIAL_POS"; tiu = +1.0
    elif 3 <= m_ctrl <= 4 and p_one_sided_GM_higher > 0.20:
        v = "NULL"; tiu = 0.0
    elif 5 <= m_ctrl <= 6:
        v = "PARTIAL_NEG"; tiu = -1.0
    elif m_ctrl >= 7:
        v = "REJECT_FORWARD"; tiu = -3.0
    else:
        v = "INDETERMINATE_LADDER_GAP"; tiu = 0.0
    log(f"VERDICT: {v} (TIU = {tiu:+.1f})")

    results = {
        "pass": 39, "item": "p38-C control-roster sensitivity check",
        "hypothesis": "Positive numerology results predict GM Node status (forward); converse largely false (already supported by Pass-38 3/12)",
        "anti_hark_freeze_path": str(ARCH),
        "GM_cluster":      {"matches": m_gm, "n": n_gm, "rate_pct": 100*m_gm/n_gm, "source": "Pass-38 results.json"},
        "control_cluster": {"matches": m_ctrl, "n": n_ctrl, "rate_pct": 100*m_ctrl/n_ctrl if n_ctrl else None, "source": "Pass-39 this run"},
        "fisher_exact_one_sided_p_GM_higher": p_one_sided_GM_higher,
        "verdict": v, "tiu": tiu,
        "verdict_ladder_FROZEN_pre_execution": arch_payload["verdict_ladder_frozen_pre_execution"],
        "control_per_celebrity": [
            {k: v for k, v in p.items() if k not in ("first500_words","archetype_counts")} for p in per
        ],
        "honesty_69": [
            "Control roster frozen IN-CODE before fetch (anti-HARK gate).",
            "Same Pass-37 frozen rubric applied to control as to GM (no rubric drift).",
            "Fisher exact 2x2 one-sided used (GM > control direction); two-sided would be ~2x.",
            "n=12 vs n=12 is small; CIs are wide; one-sided p-value range 0.04-0.50 expected under various scenarios.",
            "Pass-37 archetype-1 over-broadness bias affects BOTH GM and control equally; comparison is internally consistent.",
            "URB-830-symmetric: CONFIRM_FORWARD and REJECT_FORWARD are symmetric Bayesian updates at TIU magnitude 3.0.",
        ],
    }
    with open(RES, "w") as f:
        json.dump(results, f, indent=2, default=str)
    log(f"RESULTS -> {RES}")
    log(f"=== END ===")

if __name__ == "__main__":
    main()
