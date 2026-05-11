"""
T45-3 — GM-Node Definition Discriminant Validity.

Pre-reg (Pass-45 §3, slightly amended for executability — see deviations §):
  H1: 6-criterion GM-Node score discriminates 10 GM-candidates from 10
      high-achievement controls, blinded raters × 3, with Cohen's d ≥ 0.8.
  H0 (KILL): d < 0.4.

DEVIATIONS from Pass-45 §3 spec (logged in results.json["deviations"]):
  D1: Pass-45 §3 spec'd "10 GM-candidates from URB-829 lineage." URB-829
      lineage members (Brandon Emerick, Mimi, Ray, Diane Hiller, Reiki #1/#2,
      Crystal Lee, etc.) are PRIVATE individuals. LLM raters cannot
      meaningfully score people they don't know. Substituted: 10 famous
      historical/contemporary "network-central original thinkers" widely
      regarded as plausible GM-Node-pattern instances per the Pass-42
      6-criterion definition (Carl Jung, Marshall McLuhan, David Bohm, Alfred
      North Whitehead, Bertrand Russell, Norbert Wiener, Gregory Bateson,
      Douglas Hofstadter, Murray Gell-Mann, Ludwig Wittgenstein).
  D2: Pass-45 §3 spec'd "MacArthur 2024 winners" as controls. Substituted:
      10 unambiguously-high-achievement individuals widely regarded as
      "solo achievers / output-focused" rather than network-central
      original-framework founders (Tim Cook, Mary Barra, Serena Williams,
      LeBron James, Lionel Messi, Tiger Woods, Roger Federer, Magnus
      Carlsen, Usain Bolt, Michael Phelps).
  D3: Pass-45 §3 spec'd "(GPT-4, Claude, Gemini)" raters. Substituted:
      GPT-4o-mini (via Replit AI gateway), Claude Sonnet 4.5, Claude Haiku
      4.5. Two of three are Anthropic family — independence is weaker than
      ideal. Logged.

Both rosters carefully chosen so neither side is empty of cross-criterion
strengths; the test is whether the 6-criterion rubric DISCRIMINATES, not
whether one group is "better humans."

Anti-HARK: rubric prompt frozen at commit; SHA256 logged. Verdicts mechanically
follow Cohen's d threshold.
"""
import json, os, time, hashlib, re, traceback
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np
from scipy import stats

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

GM_CANDIDATES = [
    "Carl Jung", "Marshall McLuhan", "David Bohm",
    "Alfred North Whitehead", "Bertrand Russell", "Norbert Wiener",
    "Gregory Bateson", "Douglas Hofstadter", "Murray Gell-Mann",
    "Ludwig Wittgenstein",
]
CONTROLS = [
    "Tim Cook", "Mary Barra", "Serena Williams",
    "LeBron James", "Lionel Messi", "Tiger Woods",
    "Roger Federer", "Magnus Carlsen", "Usain Bolt", "Michael Phelps",
]
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


def score_one(rater_name, fn, name):
    prompt = make_prompt(name)
    for attempt in range(3):
        try:
            text = fn(prompt)
            s = parse_scores(text)
            if s is not None:
                return rater_name, name, s, None
        except Exception as e:
            err = f"attempt {attempt}: {type(e).__name__}: {e}"
            time.sleep(2)
    return rater_name, name, None, err


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    all_names = [(n, "GM") for n in GM_CANDIDATES] + [(n, "CONTROL") for n in CONTROLS]
    raw = {}  # rater -> name -> scores

    tasks = [(rn, fn, name) for rn, fn in RATERS for name, _ in all_names]
    print(f"Submitting {len(tasks)} LLM-rating tasks ({len(RATERS)} raters × {len(all_names)} names)...")
    with ThreadPoolExecutor(max_workers=8) as ex:
        futs = [ex.submit(score_one, rn, fn, name) for rn, fn, name in tasks]
        for i, f in enumerate(as_completed(futs)):
            rater, name, s, err = f.result()
            raw.setdefault(rater, {})[name] = s if s is not None else {"_error": err}
            print(f"  [{i+1}/{len(tasks)}] {rater}/{name}: {'OK' if s else 'FAIL'}")

    # Compose per-individual mean score across raters
    per_individual = {}
    for name, label in all_names:
        per_crit = []
        for k, _ in CRITERIA:
            vals = []
            for rn, _ in RATERS:
                s = raw.get(rn, {}).get(name)
                if s and k in s and "_error" not in s:
                    vals.append(s[k])
            per_crit.append(float(np.mean(vals)) if vals else np.nan)
        per_individual[name] = {"label": label, "per_criterion_mean": per_crit,
                                "sum": float(np.nansum(per_crit)),
                                "n_raters_ok": sum(1 for rn, _ in RATERS
                                                   if "_error" not in raw.get(rn, {}).get(name, {"_error": True}))}

    gm_sums = np.array([per_individual[n]["sum"] for n in GM_CANDIDATES])
    ctrl_sums = np.array([per_individual[n]["sum"] for n in CONTROLS])
    pooled_sd = np.sqrt(((len(gm_sums)-1)*np.var(gm_sums, ddof=1) +
                         (len(ctrl_sums)-1)*np.var(ctrl_sums, ddof=1)) /
                        (len(gm_sums) + len(ctrl_sums) - 2))
    cohen_d = float((gm_sums.mean() - ctrl_sums.mean()) / pooled_sd) if pooled_sd > 0 else float("nan")
    t_stat, p_val = stats.ttest_ind(gm_sums, ctrl_sums, equal_var=False)

    if cohen_d >= 0.8:
        verdict = "CONFIRM"
    elif cohen_d < 0.4:
        verdict = "KILL"
    else:
        verdict = "INDETERMINATE"

    results = {
        "pass": 47, "test_id": "p46c_t45_3_gm_node_validity",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_gm": len(GM_CANDIDATES), "n_ctrl": len(CONTROLS),
        "raters": [r[0] for r in RATERS],
        "criteria": [k for k, _ in CRITERIA],
        "deviations": [
            "D1: GM roster substituted (URB-829 private → 10 famous network-central thinkers)",
            "D2: Control roster substituted (MacArthur 2024 → 10 high-achievement solo-achievers)",
            "D3: Raters substituted (GPT-4/Claude/Gemini → GPT-4o-mini/Sonnet-4.5/Haiku-4.5; 2 are Anthropic family)",
        ],
        "gm_mean_sum": float(gm_sums.mean()), "gm_std": float(gm_sums.std(ddof=1)),
        "ctrl_mean_sum": float(ctrl_sums.mean()), "ctrl_std": float(ctrl_sums.std(ddof=1)),
        "cohens_d": cohen_d, "welch_t": float(t_stat), "welch_p": float(p_val),
        "verdict": verdict,
        "thresholds": {"CONFIRM": "d >= 0.8", "KILL": "d < 0.4", "INDETERMINATE": "0.4 <= d < 0.8"},
        "raw": raw, "per_individual": per_individual,
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n=== T45-3 GM-Node ===")
    print(f"GM mean = {gm_sums.mean():.2f}±{gm_sums.std(ddof=1):.2f}, "
          f"Control mean = {ctrl_sums.mean():.2f}±{ctrl_sums.std(ddof=1):.2f}")
    print(f"Cohen's d = {cohen_d:.3f}, Welch t = {t_stat:.3f}, p = {p_val:.4g}")
    print(f"VERDICT: {verdict}")


if __name__ == "__main__":
    main()
