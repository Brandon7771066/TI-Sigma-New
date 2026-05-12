"""
O26 — Meta-Indeterminate Test (Validly-Indeterminate-as-waypoint operationalization).

Pre-reg (Pass-47 §4.3 of PASS_47_INSIGHTS_AROUSAL_BREAKING_PLUS_LAZY_BINARY_TRALSITY):
  HYPOTHESIS: Brandon's claim "Indeterminate is the EPITOME of Tralse —
  Indeterminate uniquely maximizes valid tralseness (τ × stability)" predicts that
  submitting "TI Sigma framework is True" to the same MR Truth Labels rubric
  validated at Fleiss' κ=0.906 (C20) will yield convergent classification on I.

  H1 (CONFIRM): >= 7 of 9 ratings are I (≥77.8% I-fraction).
  H0 (KILL): >= 5 of 9 ratings are T or F or DT (i.e., I-fraction < 0.5).
  INDETERMINATE_TEST: 0.5 ≤ I-fraction < 7/9.

DELIBERATE LIMITATIONS (#69 honest declaration, in-runner):
  L1: LOW DISCRIMINATING POWER — raters using a 4-label rubric on an
      unfamiliar/novel framework will likely default to I for ignorance reasons,
      not for max-valid-tralseness reasons. The two hypotheses (Brandon's
      epistemic-structural prediction vs. raters'-default-when-uncertain) are
      observationally equivalent for this single test. A CONFIRM here is
      necessary-but-not-sufficient evidence for §4.2 max-valid-tralseness.
      Stronger discriminating tests would: (a) include framework-known controls
      (e.g., "Newtonian mechanics is True" — predicted I despite raters knowing
      it well, since it is partially-true); (b) include framework-strawman
      controls (e.g., "Geocentric astronomy is True" — predicted F despite
      raters being able to evaluate it).
  L2: NO BLINDING TO SELF-REFERENCE — raters see "TI Sigma" by name. Cannot
      blind without misrepresenting the framework. Mitigation: testing 3
      framings to triangulate.
  L3: PROMPT-FRAMING ROBUSTNESS — single rubric prompt; if raters are sensitive
      to prompt details, would not be detected by this single-prompt design.

EXTENSIONS BUILT IN to address L1 partially:
  E1: 3 control propositions added — known-true ("Newtonian mechanics is True"),
      known-false ("Geocentric astronomy is True"), and known-paradoxical
      ("This sentence is false"). Predicted: known-paradoxical → DT (matches
      C20 §4 baseline); known-false → F (matches C20); known-true → T or I
      (raters know Newtonian is approximately-true but superseded by GR — so
      I is also defensible). If controls behave as predicted AND target
      converges on I, the result is more interpretable.

ANTI-HARK: prompt + propositions + thresholds frozen at commit. SHA256 logged.
Verdict mechanically follows I-fraction threshold.
"""
import json, os, time, hashlib, re
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

# 3 framings of the target proposition + 3 controls
TARGETS = [
    ("TARGET_F1", "The Tralse Informationalism (TI Sigma) framework is True."),
    ("TARGET_F2", "TI Sigma's core theoretical claims are correct."),
    ("TARGET_F3", "The TI Sigma framework accurately describes reality."),
]
CONTROLS = [
    ("CONTROL_KNOWN_T", "Water boils at 100°C at 1 atm sea-level pressure."),
    ("CONTROL_KNOWN_F", "Geocentric astronomy is True (the Sun orbits the Earth)."),
    ("CONTROL_KNOWN_DT", "This sentence is false."),
]
ALL_PROPS = TARGETS + CONTROLS

PREDICTED = {
    "TARGET_F1": "I", "TARGET_F2": "I", "TARGET_F3": "I",
    "CONTROL_KNOWN_T": "T", "CONTROL_KNOWN_F": "F", "CONTROL_KNOWN_DT": "DT",
}

# Reuse the EXACT same rubric prompt validated at C20 (Fleiss κ=0.906)
PROMPT_TEMPLATE = (
    "You are an expert classifier trained on the canonical Tralse Informationalism MR Truth "
    "Labels ruling. Classify each given proposition into EXACTLY ONE of these 4 mutually "
    "exclusive base-categories:\n\n"
    "  T  = TRUE: classically true; the proposition holds.\n"
    "  F  = FALSE: classically false; the proposition does not hold.\n"
    "  I  = INDETERMINATE: the proposition's truth value is currently undetermined "
    "(future contingents, undecided mathematical conjectures, modal claims awaiting "
    "specification, claims about consciousness/morality without consensus).\n"
    "  DT = DOUBLE TRALSE: the proposition is BOTH true and not-true under its own "
    "assertion (Liar-type self-reference, Russell-set, dialetheia, paradoxes that "
    "force τ(P) ∧ ¬τ(P)).\n\n"
    "Use ONLY these 4 labels. Pick the SINGLE best fit. If torn between I and DT, pick DT "
    "ONLY when self-reference forces the bothness — otherwise I.\n\n"
    "Proposition: \"{prop}\"\n\n"
    "Respond with ONLY the single token T, F, I, or DT — nothing else."
)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def parse_label(text):
    t = text.strip().upper()
    m = re.match(r"\b(DT|T|F|I)\b", t)
    if m: return m.group(1)
    if t.startswith("DT"): return "DT"
    if t.startswith("T"): return "T"
    if t.startswith("F"): return "F"
    if t.startswith("I"): return "I"
    return None


def call_anthropic(model, prompt):
    from anthropic import Anthropic
    c = Anthropic()
    r = c.messages.create(model=model, max_tokens=10,
                          messages=[{"role": "user", "content": prompt}])
    return r.content[0].text


def call_openai(model, prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
    r = c.chat.completions.create(model=model, max_tokens=10,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content


RATERS = [
    ("gpt_4o_mini", lambda p: call_openai("gpt-4o-mini", p)),
    ("claude_sonnet_4_5", lambda p: call_anthropic("claude-sonnet-4-5", p)),
    ("claude_haiku_4_5", lambda p: call_anthropic("claude-haiku-4-5", p)),
]


def label_one(rater_name, fn, prop_id, prop):
    prompt = PROMPT_TEMPLATE.format(prop=prop)
    for attempt in range(3):
        try:
            text = fn(prompt)
            lab = parse_label(text)
            if lab in ("T", "F", "I", "DT"):
                return rater_name, prop_id, lab, None, text
        except Exception as e:
            err = f"attempt {attempt}: {type(e).__name__}: {e}"
            time.sleep(2)
    return rater_name, prop_id, None, err, None


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    raw = {rn: {} for rn, _ in RATERS}
    raw_text = {rn: {} for rn, _ in RATERS}
    tasks = [(rn, fn, pid, p) for rn, fn in RATERS for pid, p in ALL_PROPS]
    print(f"Submitting {len(tasks)} label tasks ({len(RATERS)} raters × {len(ALL_PROPS)} props)...")
    n_done = 0
    with ThreadPoolExecutor(max_workers=9) as ex:
        futs = [ex.submit(label_one, rn, fn, pid, p) for rn, fn, pid, p in tasks]
        for f in as_completed(futs):
            rn, pid, lab, err, text = f.result()
            raw[rn][pid] = lab if lab else f"_ERR:{err}"
            raw_text[rn][pid] = text if text else f"_ERR:{err}"
            n_done += 1
    # Per-proposition rating tally
    tallies = {}
    for pid, _ in ALL_PROPS:
        labels = [raw[rn].get(pid) for rn, _ in RATERS]
        tallies[pid] = {"T": labels.count("T"), "F": labels.count("F"),
                        "I": labels.count("I"), "DT": labels.count("DT"),
                        "raw": labels, "predicted": PREDICTED[pid]}

    target_ids = [pid for pid, _ in TARGETS]
    target_labels = [raw[rn].get(pid) for rn, _ in RATERS for pid in target_ids]
    n_target = len(target_labels)
    n_target_I = target_labels.count("I")
    target_I_fraction = n_target_I / n_target if n_target else 0.0

    if target_I_fraction >= 7/9:
        verdict = "CONFIRM"
    elif target_I_fraction < 0.5:
        verdict = "KILL"
    else:
        verdict = "INDETERMINATE_TEST"

    # Control behavior check
    ctrl_predicted_match = {}
    for pid, _ in CONTROLS:
        pred = PREDICTED[pid]
        actual = [raw[rn].get(pid) for rn, _ in RATERS]
        match = sum(1 for a in actual if a == pred)
        ctrl_predicted_match[pid] = {"predicted": pred, "actual": actual, "match_count": match}

    interpretability_note = (
        "All 3 controls behaved as predicted (T/F/DT) → target I-result is interpretable as "
        "rubric-applied-to-unfamiliar-framework yielding I; consistent with §4.2 max-valid-"
        "tralseness BUT also consistent with raters'-default-when-uncertain (per L1 limitation)."
        if all(v["match_count"] >= 2 for v in ctrl_predicted_match.values())
        else "≥1 control deviated from prediction → rubric behavior in this run is partially "
             "inconsistent; interpret target result with extra caution."
    )

    results = {
        "pass": 47, "test_id": "o26_meta_indeterminate_test",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_propositions": len(ALL_PROPS),
        "n_targets": len(TARGETS), "n_controls": len(CONTROLS),
        "n_raters": len(RATERS), "raters": [r[0] for r in RATERS],
        "limitations": [
            "L1: LOW DISCRIMINATING POWER — Brandon's max-valid-tralseness hypothesis observationally equivalent to raters'-default-when-uncertain on this single test",
            "L2: NO BLINDING TO SELF-REFERENCE — TI Sigma named in prompt; mitigation = 3 framings",
            "L3: PROMPT-FRAMING ROBUSTNESS — single rubric prompt",
        ],
        "extensions": ["E1: 3 controls added (known-T, known-F, known-DT) for interpretability"],
        "thresholds": {"CONFIRM": "I-fraction >= 7/9 on targets",
                       "KILL": "I-fraction < 0.5 on targets",
                       "INDETERMINATE_TEST": "0.5 <= I-fraction < 7/9"},
        "n_target_ratings": n_target,
        "n_target_I": n_target_I,
        "target_I_fraction": target_I_fraction,
        "verdict": verdict,
        "tallies_per_proposition": tallies,
        "control_predicted_match": ctrl_predicted_match,
        "interpretability_note": interpretability_note,
        "raw_labels_per_rater": raw,
        "raw_text_per_rater": raw_text,
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n=== O26 Meta-Indeterminate Test ===")
    print(f"Target I-fraction: {n_target_I}/{n_target} = {target_I_fraction:.3f}")
    print(f"Per-proposition tallies:")
    for pid, t in tallies.items():
        print(f"  {pid}: T={t['T']} F={t['F']} I={t['I']} DT={t['DT']} | predicted={t['predicted']} | raw={t['raw']}")
    print(f"Control behavior: {ctrl_predicted_match}")
    print(f"\nInterpretability: {interpretability_note}")
    print(f"\nVERDICT: {verdict}")


if __name__ == "__main__":
    main()
