"""
T45-4 — MR Truth Labels Inter-Rater Reliability (Fleiss' κ).

Pre-reg (Pass-45 §4, deviation logged):
  H1: 3 raters classify 100 propositions into {True, False, Indeterminate,
      Double Tralse} with Fleiss' κ ≥ 0.6 (substantial agreement).
  H0 (KILL): κ < 0.4 (poor / fair).

DEVIATIONS from Pass-45 §4:
  D1: Pass-45 §4 spec'd "2 humans + 1 LLM" raters. Substituted 3 LLMs
      (GPT-4o-mini, Claude Sonnet 4.5, Claude Haiku 4.5) because no human
      raters are recruitable on this turn. This UNDER-tests the "trained
      humans can use the scheme" claim and OVER-tests "LLMs can use the
      scheme." Honest implication: a CONFIRM here means the scheme is at
      least operationally usable BY LLMs given the canonical ruling
      paper as instructions; it does NOT establish that humans can use
      it. A KILL here is a strong signal — if 3 frontier LLMs with the
      full ruling cannot agree, humans almost certainly cannot.
  D2: Substituted 100-proposition test set drawn from public corpus
      patterns (25 obvious-True facts, 25 obvious-False, 25 paradoxical,
      25 borderline-modal). List frozen at commit-time below.

Anti-HARK: prompt + classification rubric + test propositions all frozen
at commit. SHA256 logged. Verdict mechanically follows Fleiss' κ threshold.
"""
import json, os, time, hashlib, re
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

# 100 propositions: 25 True / 25 False / 25 Paradoxical / 25 Borderline-Modal
PROPOSITIONS = (
    # 25 obvious-TRUE (mathematical, geographical, physical)
    ["2 + 2 = 4", "Water boils at 100°C at 1 atm sea-level pressure", "Paris is the capital of France",
     "The Earth orbits the Sun", "Hydrogen has atomic number 1", "DNA has a double-helix structure",
     "Light travels faster than sound in air", "The Pacific is larger than the Atlantic Ocean",
     "Humans have 23 pairs of chromosomes", "Mount Everest is the tallest mountain above sea level",
     "All circles are conic sections", "The integers are closed under addition",
     "Napoleon Bonaparte died in 1821", "Tokyo is in Asia", "Pi is irrational",
     "Mammals are warm-blooded", "Sodium chloride is table salt's chemical name",
     "Shakespeare wrote Hamlet", "World War II ended in 1945", "Photosynthesis requires light",
     "The square root of 144 is 12", "Antarctica contains the South Pole",
     "Carbon's atomic symbol is C", "The human heart has four chambers",
     "Aluminum is a metal"],
    # 25 obvious-FALSE
    ["3 + 5 = 9", "Water boils at 50°C at sea level", "Paris is the capital of Germany",
     "The Sun orbits the Earth daily", "Helium has atomic number 6", "DNA is composed of lipids only",
     "Sound travels faster than light in vacuum", "The Atlantic is larger than the Pacific Ocean",
     "Humans have 100 chromosomes total", "Mount Everest is in Australia",
     "All triangles have four sides", "The integers are closed under division",
     "Napoleon Bonaparte died in 1965", "Tokyo is in South America", "Pi equals exactly 3",
     "All reptiles are mammals", "Sodium chloride is the chemical name for sugar",
     "Shakespeare wrote War and Peace", "World War II ended in 1812", "Photosynthesis requires darkness",
     "The square root of 144 is 8", "Antarctica is in the Northern Hemisphere",
     "Gold's atomic symbol is G", "The human heart has two chambers",
     "Aluminum is a noble gas"],
    # 25 PARADOXICAL (Liar, Russell, Sorites, Ship-of-Theseus, etc.)
    ["This sentence is false",
     "The barber shaves all and only those who do not shave themselves; does he shave himself?",
     "The set of all sets that do not contain themselves contains itself",
     "A heap of sand remains a heap if you remove one grain (Sorites)",
     "The sentence on the back of this card is true; the sentence on the back of this card is false",
     "Achilles can never overtake the tortoise (Zeno)",
     "If God is omnipotent, can He create a stone He cannot lift?",
     "The Ship of Theseus, with all parts replaced, is the same ship",
     "There exists a smallest natural number that cannot be defined in fewer than fifteen English words",
     "All Cretans are liars (said by a Cretan)",
     "Tomorrow's sea-battle will occur (Aristotle)",
     "The next sentence is true. The previous sentence is false.",
     "An arrow in flight is always at rest (Zeno)",
     "Newcomb's predictor placed $1M in box B iff it predicted you'd take only B; you should take only B",
     "The unexpected hanging will occur on a weekday next week, but you cannot predict the day",
     "If a tree falls in a forest with no observer, it makes a sound",
     "Every event has a cause; the first event has no cause",
     "The probability that this sentence has probability greater than 0.5 is less than 0.5",
     "Moore's paradox: 'It is raining but I do not believe it is raining'",
     "The sorites series of Hercules: removing one strand of hair from a head still leaves a non-bald person",
     "I know that I know nothing (Socrates)",
     "Bootstrap-paradox: a time-traveler delivers Hamlet to Shakespeare, who copies it",
     "The grandfather paradox: a time-traveler kills their own grandfather",
     "Quantum cat is both alive and dead until observed (Schrödinger)",
     "Theseus's ship reassembled from original parts is the original ship"],
    # 25 BORDERLINE-MODAL (future contingents, consciousness, moral, mathematical existence)
    ["There will be a sea battle tomorrow",
     "Consciousness is fundamentally physical",
     "Mathematical objects exist independently of minds",
     "Murder is morally wrong in all possible worlds",
     "The continuum hypothesis is true",
     "Free will is compatible with determinism",
     "There exists a god",
     "Beauty is in the eye of the beholder",
     "The universe had a cause",
     "Time is an illusion",
     "P = NP",
     "Some moral statements are objectively true",
     "Other minds exist",
     "The external world exists independently of perception",
     "Personal identity persists through bodily change",
     "The axiom of choice is true",
     "Numbers are abstract objects",
     "Aesthetic value is objective",
     "Quantum mechanics is fundamentally indeterministic",
     "There are infinitely many twin primes",
     "Animals have moral status equal to humans",
     "Linguistic meaning is determined by use",
     "The future is fixed",
     "Causation is reducible to constant conjunction",
     "Mathematical truths would be true even if no mind existed"],
)
TEST_SET = [p for cat in PROPOSITIONS for p in cat]
TRUE_LABELS_HINT = (
    ["TRUE_BUCKET"] * 25 + ["FALSE_BUCKET"] * 25 +
    ["PARADOXICAL_BUCKET"] * 25 + ["MODAL_BUCKET"] * 25
)
assert len(TEST_SET) == 100, f"got {len(TEST_SET)}"

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
    # Match leading token
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


def label_one(rater_name, fn, prop_idx, prop):
    prompt = PROMPT_TEMPLATE.format(prop=prop)
    for attempt in range(3):
        try:
            text = fn(prompt)
            lab = parse_label(text)
            if lab in ("T", "F", "I", "DT"):
                return rater_name, prop_idx, lab, None
        except Exception as e:
            err = f"attempt {attempt}: {type(e).__name__}: {e}"
            time.sleep(2)
    return rater_name, prop_idx, None, err


def fleiss_kappa(matrix):
    """matrix: shape (N items, K categories), value = number of raters per category."""
    N, K = matrix.shape
    n_raters = matrix.sum(axis=1)
    assert np.all(n_raters == n_raters[0]), "ragged"
    n = int(n_raters[0])
    P_i = ((matrix * (matrix - 1)).sum(axis=1)) / (n * (n - 1))
    P_bar = float(P_i.mean())
    p_j = matrix.sum(axis=0) / (N * n)
    P_e = float((p_j ** 2).sum())
    if abs(1 - P_e) < 1e-12:
        return float("nan")
    return float((P_bar - P_e) / (1 - P_e))


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    raw = {rn: {} for rn, _ in RATERS}
    tasks = [(rn, fn, i, p) for rn, fn in RATERS for i, p in enumerate(TEST_SET)]
    print(f"Submitting {len(tasks)} label tasks ({len(RATERS)} raters × {len(TEST_SET)} props)...")
    n_done = 0
    with ThreadPoolExecutor(max_workers=12) as ex:
        futs = [ex.submit(label_one, rn, fn, i, p) for rn, fn, i, p in tasks]
        for f in as_completed(futs):
            rn, i, lab, err = f.result()
            raw[rn][i] = lab if lab else f"_ERR:{err}"
            n_done += 1
            if n_done % 50 == 0 or n_done == len(tasks):
                print(f"  {n_done}/{len(tasks)} done")

    # Build Fleiss matrix
    K_LABELS = ["T", "F", "I", "DT"]
    matrix = np.zeros((len(TEST_SET), len(K_LABELS)), dtype=int)
    n_invalid = 0
    for i in range(len(TEST_SET)):
        for rn, _ in RATERS:
            lab = raw[rn].get(i)
            if lab in K_LABELS:
                matrix[i, K_LABELS.index(lab)] += 1
            else:
                n_invalid += 1
    # Only keep rows where all 3 raters provided valid labels
    full_mask = matrix.sum(axis=1) == len(RATERS)
    matrix_full = matrix[full_mask]
    n_full = int(full_mask.sum())
    kappa = fleiss_kappa(matrix_full) if n_full >= 5 else float("nan")

    # Per-rater agreement-with-majority (sanity)
    majority = []
    for i in range(len(TEST_SET)):
        if matrix[i].sum() == len(RATERS):
            majority.append(K_LABELS[int(np.argmax(matrix[i]))])
        else:
            majority.append(None)
    rater_majority_agreement = {}
    for rn, _ in RATERS:
        agree, total = 0, 0
        for i in range(len(TEST_SET)):
            if majority[i] is not None and raw[rn].get(i) in K_LABELS:
                total += 1
                if raw[rn][i] == majority[i]:
                    agree += 1
        rater_majority_agreement[rn] = agree / total if total else None

    if not np.isnan(kappa):
        if kappa >= 0.6:
            verdict = "CONFIRM"
        elif kappa < 0.4:
            verdict = "KILL"
        else:
            verdict = "INDETERMINATE"
    else:
        verdict = "INDETERMINATE_INSUFFICIENT_DATA"

    # Per-bucket distribution
    bucket_dist = {}
    for bucket_idx, bucket_name in enumerate(["TRUE_BUCKET", "FALSE_BUCKET", "PARADOXICAL_BUCKET", "MODAL_BUCKET"]):
        start, end = bucket_idx * 25, (bucket_idx + 1) * 25
        sub = matrix[start:end]
        bucket_dist[bucket_name] = {
            "T": int(sub[:, 0].sum()), "F": int(sub[:, 1].sum()),
            "I": int(sub[:, 2].sum()), "DT": int(sub[:, 3].sum()),
        }

    results = {
        "pass": 47, "test_id": "p46c_t45_4_mr_truth_kappa",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_propositions": len(TEST_SET), "n_raters": len(RATERS),
        "raters": [r[0] for r in RATERS],
        "deviations": [
            "D1: 3 LLMs substituted for 2-humans+1-LLM (no humans recruitable this turn)",
            "D2: Test set frozen in runner (drawn from public corpus patterns: 25 obvious-T, 25 obvious-F, 25 paradoxical, 25 borderline-modal)",
        ],
        "n_full_3rater_rows": n_full,
        "n_invalid_responses": n_invalid,
        "fleiss_kappa": kappa,
        "verdict": verdict,
        "thresholds": {"CONFIRM": "κ >= 0.6", "KILL": "κ < 0.4", "INDETERMINATE": "0.4 <= κ < 0.6"},
        "rater_majority_agreement": rater_majority_agreement,
        "bucket_distribution": bucket_dist,
        "raw_labels_per_rater": raw,
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n=== T45-4 MR Truth Labels ===")
    print(f"n_full_3rater_rows = {n_full}/{len(TEST_SET)}, n_invalid = {n_invalid}")
    print(f"Fleiss' κ = {kappa:.3f}" if not np.isnan(kappa) else f"Fleiss' κ = NaN")
    print(f"Per-rater agreement-with-majority: {rater_majority_agreement}")
    print(f"Bucket dist: {bucket_dist}")
    print(f"VERDICT: {verdict}")


if __name__ == "__main__":
    main()
