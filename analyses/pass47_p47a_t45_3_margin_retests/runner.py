"""
p47-A — T45-3 v2: BOTH near-margin AND moderate-margin re-tests.

Per Brandon's Pass-47 directive: "go ahead with both a near-margin and a
MODERATE-margin retest, in the spirit of indeterminacy."

This calibrates the original T45-3 d=8.92 result (Wittgenstein vs LeBron =
extreme contrast) by running the SAME 6-criterion rubric against:

  MODERATE-MARGIN:  10 founders of intellectual schools (less iconic than
                    Pass-47 T45-3 GM roster) vs 10 prolific public
                    intellectuals who never founded a school.
  NEAR-MARGIN:      10 creative-domain network-central figures (founders
                    of artistic movements / scenes / schools) vs 10
                    creative-domain solo masters (singular outputs, no
                    school-of-thought spawn).

Pre-reg verdicts (frozen at commit, identical thresholds to T45-3):
  Per contrast: CONFIRM if d ≥ 0.8; KILL if d < 0.4; INDETERMINATE between.
  Cross-contrast read: if BOTH d ≥ 0.8, GM-Node rubric has discriminant
    validity at all margins. If MODERATE d ≥ 0.8 but NEAR d < 0.4, rubric
    works at "intellectual-vs-not" level but collapses at "creative-network-
    central-vs-creative-solo" — i.e. it's tracking "intellectual fame" not
    "network-centrality." If BOTH d < 0.4, the original T45-3 d=8.92 was
    extreme-contrast artifact and the rubric is invalid.

Anti-HARK: same prompt + criteria as T45-3. Only rosters change. Runner
SHA256 logged. Verdicts mechanically follow Cohen's d threshold.
"""
import json, os, time, hashlib, re
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np
from scipy import stats

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

CONTRASTS = {
    "moderate_margin": {
        "GM": [
            "Karl Popper", "Thomas Kuhn", "Jane Jacobs", "Hannah Arendt",
            "Buckminster Fuller", "John Rawls", "Claude Shannon",
            "Stuart Kauffman", "Stewart Brand", "Donna Haraway",
        ],
        "CONTROL": [
            "Steven Pinker", "Malcolm Gladwell", "Yuval Noah Harari",
            "Niall Ferguson", "Jared Diamond", "Mary Beard",
            "Bill Bryson", "Michael Lewis", "Walter Isaacson", "Sam Harris",
        ],
        "GM_description": "Founders of intellectual schools/frameworks (less iconic than T45-3-v1 GM)",
        "CONTROL_description": "Prolific public intellectuals who synthesize but did not found a school",
    },
    "near_margin": {
        "GM": [
            "Brian Eno", "John Cage", "Andy Warhol", "Yoko Ono",
            "Laurie Anderson", "Pauline Oliveros", "Sun Ra", "George Clinton",
            "Hilma af Klint", "Yvonne Rainer",
        ],
        "CONTROL": [
            "Bob Dylan", "Toni Morrison", "Adele", "Beyoncé",
            "Stephen King", "Hayao Miyazaki", "Frida Kahlo",
            "Hemingway", "Mozart", "Joni Mitchell",
        ],
        "GM_description": "Creative-domain network-central figures (founders of movements/scenes/schools)",
        "CONTROL_description": "Creative-domain solo masters (singular outputs, no school-of-thought spawn)",
    },
}

CRITERIA = [
    ("network_position",
     "Network position: degree to which others orient their work or thinking around this person's framework, "
     "vs this person being one node among many similar peers."),
    ("originality_output",
     "Originality of output: degree to which this person's work introduces a new framework, vocabulary, or "
     "way of seeing — vs excellent execution within an existing paradigm."),
    ("mentorship_density",
     "Mentorship density: degree to which this person directly produced a generation of students/disciples "
     "who carry forward and extend the work."),
    ("cross_domain_fluency",
     "Cross-domain fluency: degree to which this person's contributions span multiple disciplines and "
     "their framework is recognized as integrative across fields."),
    ("self_direction",
     "Self-direction: degree to which the person's career trajectory was self-set rather than guided by "
     "an institutional career ladder."),
    ("blinded_rater_central_label",
     "Blinded-rater central-label test: if a blinded rater was asked 'name 10 people whose intellectual or "
     "creative network has shaped a generation,' how strongly would this person come to mind?"),
]

PROMPT_TEMPLATE = (
    "You are scoring public figures on a 6-criterion rubric for the Tralse Informationalism / "
    "Mycelial-Generative-Node (GM-Node) definition. The rubric is meant to discriminate "
    "'network-central original framework-builders' from 'high-achievement individuals who are not "
    "network-central original framework-builders.'\n\n"
    "Score the following individual on EACH of the 6 criteria below on a 1-7 Likert scale, where:\n"
    "  1 = strongly does NOT exhibit this criterion\n"
    "  4 = neutral / mixed evidence\n"
    "  7 = strongly exhibits this criterion\n\n"
    "Be calibrated. Do NOT inflate scores out of politeness or deflate out of skepticism. Use the full 1-7 range.\n\n"
    "Individual to score: {name}\n\n"
    "Criteria:\n{criteria_block}\n\n"
    "Output ONLY a single JSON object on one line, with criterion keys:\n"
    "{{\"network_position\": <int 1-7>, \"originality_output\": <int 1-7>, "
    "\"mentorship_density\": <int 1-7>, \"cross_domain_fluency\": <int 1-7>, "
    "\"self_direction\": <int 1-7>, \"blinded_rater_central_label\": <int 1-7>}}\n"
    "No prose, no markdown fences, just the JSON object."
)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def make_prompt(name):
    crit_block = "\n".join(f"  - {k}: {desc}" for k, desc in CRITERIA)
    return PROMPT_TEMPLATE.format(name=name, criteria_block=crit_block)


def parse_scores(text):
    m = re.search(r"\{.*?\}", text, re.DOTALL)
    if not m: return None
    try:
        d = json.loads(m.group(0))
        return {k: int(round(float(d[k]))) for k, _ in CRITERIA}
    except Exception:
        return None


def call_anthropic(model, prompt):
    from anthropic import Anthropic
    c = Anthropic()
    r = c.messages.create(model=model, max_tokens=200,
                          messages=[{"role": "user", "content": prompt}])
    return r.content[0].text


def call_openai(model, prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
    r = c.chat.completions.create(model=model, max_tokens=200,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content


RATERS = [
    ("gpt_4o_mini", lambda p: call_openai("gpt-4o-mini", p)),
    ("claude_sonnet_4_5", lambda p: call_anthropic("claude-sonnet-4-5", p)),
    ("claude_haiku_4_5", lambda p: call_anthropic("claude-haiku-4-5", p)),
]


def score_one(rater_name, fn, name, contrast):
    prompt = make_prompt(name)
    err = None
    for attempt in range(3):
        try:
            text = fn(prompt)
            s = parse_scores(text)
            if s is not None:
                return rater_name, name, contrast, s, None
        except Exception as e:
            err = f"attempt {attempt}: {type(e).__name__}: {e}"
            time.sleep(2)
    return rater_name, name, contrast, None, err


def analyze_contrast(roster_gm, roster_ctrl, raw):
    per_indiv = {}
    for name in roster_gm + roster_ctrl:
        per_crit = []
        for k, _ in CRITERIA:
            vals = []
            for rn, _ in RATERS:
                s = raw.get(rn, {}).get(name)
                if s and k in s:
                    vals.append(s[k])
            per_crit.append(float(np.mean(vals)) if vals else np.nan)
        per_indiv[name] = {"per_criterion_mean": per_crit, "sum": float(np.nansum(per_crit))}
    gm_sums = np.array([per_indiv[n]["sum"] for n in roster_gm])
    ctrl_sums = np.array([per_indiv[n]["sum"] for n in roster_ctrl])
    pooled_sd = np.sqrt(((len(gm_sums)-1)*np.var(gm_sums, ddof=1) +
                         (len(ctrl_sums)-1)*np.var(ctrl_sums, ddof=1)) /
                        (len(gm_sums) + len(ctrl_sums) - 2))
    d = float((gm_sums.mean() - ctrl_sums.mean()) / pooled_sd) if pooled_sd > 0 else float("nan")
    t, p = stats.ttest_ind(gm_sums, ctrl_sums, equal_var=False)
    if d >= 0.8: verdict = "CONFIRM"
    elif d < 0.4: verdict = "KILL"
    else: verdict = "INDETERMINATE"
    return {
        "gm_mean_sum": float(gm_sums.mean()), "gm_std": float(gm_sums.std(ddof=1)),
        "ctrl_mean_sum": float(ctrl_sums.mean()), "ctrl_std": float(ctrl_sums.std(ddof=1)),
        "cohens_d": d, "welch_t": float(t), "welch_p": float(p),
        "verdict": verdict,
        "per_individual": per_indiv,
    }


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    raw = {rn: {} for rn, _ in RATERS}

    tasks = []
    for cname, c in CONTRASTS.items():
        for n in c["GM"] + c["CONTROL"]:
            for rn, fn in RATERS:
                tasks.append((rn, fn, n, cname))
    print(f"Submitting {len(tasks)} LLM-rating tasks ({len(RATERS)} raters × 40 names)...")
    with ThreadPoolExecutor(max_workers=10) as ex:
        futs = [ex.submit(score_one, rn, fn, n, c) for rn, fn, n, c in tasks]
        n_done = 0
        for f in as_completed(futs):
            rater, name, contrast, s, err = f.result()
            raw.setdefault(rater, {})[name] = s if s is not None else {"_error": err}
            n_done += 1
            if n_done % 30 == 0 or n_done == len(tasks):
                print(f"  {n_done}/{len(tasks)} done")

    out_contrasts = {}
    for cname, c in CONTRASTS.items():
        out_contrasts[cname] = {
            "gm_description": c["GM_description"],
            "control_description": c["CONTROL_description"],
            "gm_roster": c["GM"], "control_roster": c["CONTROL"],
            **analyze_contrast(c["GM"], c["CONTROL"], raw),
        }

    # Cross-contrast read
    near_d = out_contrasts["near_margin"]["cohens_d"]
    mod_d = out_contrasts["moderate_margin"]["cohens_d"]
    if near_d >= 0.8 and mod_d >= 0.8:
        cross_read = "DISCRIMINANT_VALIDITY_AT_ALL_MARGINS"
    elif mod_d >= 0.8 and near_d < 0.4:
        cross_read = "DISCRIMINATES_INTELLECTUAL_FAME_NOT_NETWORK_CENTRALITY"
    elif near_d < 0.4 and mod_d < 0.4:
        cross_read = "ORIGINAL_T45_3_d8_92_WAS_EXTREME_CONTRAST_ARTIFACT"
    elif mod_d >= 0.8 and 0.4 <= near_d < 0.8:
        cross_read = "PARTIAL_DISCRIMINATION_AT_NEAR_MARGIN"
    else:
        cross_read = f"MIXED: near={near_d:.2f} moderate={mod_d:.2f}"

    results = {
        "pass": 47, "test_id": "p47a_t45_3_margin_retests",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "raters": [r[0] for r in RATERS],
        "criteria": [k for k, _ in CRITERIA],
        "context": "T45-3 v2 calibration of original d=8.92 extreme-contrast result (Pass-47 §3)",
        "contrasts": out_contrasts,
        "cross_contrast_read": cross_read,
        "thresholds": {"CONFIRM": "d >= 0.8", "KILL": "d < 0.4", "INDETERMINATE": "0.4 <= d < 0.8"},
        "raw": raw,
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)

    print()
    for cname, r in out_contrasts.items():
        print(f"=== {cname} ===")
        print(f"  GM mean={r['gm_mean_sum']:.2f}±{r['gm_std']:.2f}, "
              f"Ctrl mean={r['ctrl_mean_sum']:.2f}±{r['ctrl_std']:.2f}")
        print(f"  d={r['cohens_d']:.3f}, t={r['welch_t']:.3f}, p={r['welch_p']:.4g}")
        print(f"  VERDICT: {r['verdict']}")
    print(f"\nCROSS-CONTRAST READ: {cross_read}")


if __name__ == "__main__":
    main()
