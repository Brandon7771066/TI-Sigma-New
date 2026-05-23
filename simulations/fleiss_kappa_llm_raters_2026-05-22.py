"""
Pass-63 batch-5: Re-run Fleiss kappa 2/3/4-label comparison using
ACTUAL LLM raters with semantic judgment, not halfwidth-noise proxy.

Per Brandon's Pass-63 batch-4 critique: the prior sim's halfwidth-noise
mechanism could not distinguish coherent unresolved claims (Riemann
Hypothesis -> Indeterminate) from incoherent self-referential claims
(liar paradox -> Double-Tralse). A competent rater immediately
distinguishes these by content structure. This rebuild uses actual
LLM judgment as the rater.

Raters (3 semi-independent):
  - R1: openai gpt-4o-mini, neutral stance
  - R2: openai gpt-4o-mini, strict-coherence-detection stance
  - R3: anthropic claude-haiku-4-5, charitable stance

#69 disclosure:
  - 2 of 3 raters share openai family; the 3rd is anthropic; this is
    closer to "3 semi-independent LLM raters" than to "3 independent
    humans" but is the strongest within-budget proxy.
  - Each rater returns: (a) PD-interval (mean, halfwidth), (b)
    4-label classification {T,F,I,DT} with reason. The PD-interval
    is the underlying scoring; the categorical label is the
    classifier-judged quantization.
  - 100 propositions written with explicit content (not bucket-label
    placeholders) so that a competent rater can apply real semantic
    discrimination.

Seed (for any deterministic operations): 20260530.
"""

import os
import json
import time
import concurrent.futures as cf
from openai import OpenAI
from anthropic import Anthropic
import numpy as np

# Corpus: 100 propositions. ~25 TRUE / ~25 FALSE / ~25 MODAL / ~25 PARADOX.
# Bucket label is the analyst's ground-truth expectation, NOT given to raters.
CORPUS = [
    # ===== TRUE BUCKET (25) =====
    ("Water is composed of hydrogen and oxygen atoms.", "TRUE"),
    ("The number 7 is a prime number.", "TRUE"),
    ("The Earth orbits the Sun.", "TRUE"),
    ("Mammals are warm-blooded.", "TRUE"),
    ("DNA carries genetic information.", "TRUE"),
    ("The speed of light in vacuum is approximately 3*10^8 m/s.", "TRUE"),
    ("Pythagoras' theorem holds for right triangles in Euclidean geometry.", "TRUE"),
    ("Humans have two lungs under normal anatomy.", "TRUE"),
    ("The atomic number of carbon is 6.", "TRUE"),
    ("Antarctica is colder on average than the Sahara desert.", "TRUE"),
    ("There are infinitely many prime numbers.", "TRUE"),
    ("The sum of angles in a Euclidean triangle is 180 degrees.", "TRUE"),
    ("Photosynthesis converts light energy to chemical energy in plants.", "TRUE"),
    ("Sound requires a medium to propagate.", "TRUE"),
    ("Mount Everest is taller than Mount Kilimanjaro.", "TRUE"),
    ("The mitochondria are organelles found in eukaryotic cells.", "TRUE"),
    ("E = mc^2 is a relation from special relativity.", "TRUE"),
    ("Newton's third law states forces come in equal and opposite pairs.", "TRUE"),
    ("The Pacific Ocean is larger than the Atlantic Ocean.", "TRUE"),
    ("Insulin is produced in the pancreas.", "TRUE"),
    ("Diamond is harder than graphite.", "TRUE"),
    ("Helium is a noble gas.", "TRUE"),
    ("Sodium reacts vigorously with water.", "TRUE"),
    ("The Fibonacci sequence begins 1, 1, 2, 3, 5, 8.", "TRUE"),
    ("Gravity causes objects to accelerate toward Earth at ~9.8 m/s^2 at the surface.", "TRUE"),

    # ===== FALSE BUCKET (25) =====
    ("The Sun orbits the Earth.", "FALSE"),
    ("The number 9 is a prime number.", "FALSE"),
    ("Humans have three hearts.", "FALSE"),
    ("Water boils at 50 degrees Celsius at standard atmospheric pressure.", "FALSE"),
    ("The chemical symbol for gold is Au, and Au stands for silver.", "FALSE"),
    ("All mammals lay eggs.", "FALSE"),
    ("The Great Wall of China is visible from the Moon with the naked eye.", "FALSE"),
    ("Light travels slower than sound.", "FALSE"),
    ("Atoms cannot be split.", "FALSE"),
    ("Pluto is the largest planet in our solar system.", "FALSE"),
    ("The square root of 25 is 6.", "FALSE"),
    ("The human body has 12 chromosomes per cell.", "FALSE"),
    ("Bats are blind.", "FALSE"),
    ("Lightning never strikes the same place twice.", "FALSE"),
    ("Goldfish have a memory span of only 3 seconds.", "FALSE"),
    ("The Sahara Desert is the largest desert in the world.", "FALSE"),
    ("All snakes are venomous.", "FALSE"),
    ("Penguins live at the North Pole.", "FALSE"),
    ("Sound travels faster than light in air.", "FALSE"),
    ("The element with atomic number 1 is helium.", "FALSE"),
    ("Cleopatra lived closer in time to the moon landing than to the construction of the pyramids.", "TRUE"),
    ("Sharks are mammals.", "FALSE"),
    ("The capital of Australia is Sydney.", "FALSE"),
    ("Glass is a liquid that flows slowly at room temperature.", "FALSE"),
    ("Albert Einstein failed math in school.", "FALSE"),

    # ===== MODAL BUCKET (25): currently-unresolved but decidable-in-principle =====
    ("The Riemann Hypothesis is true.", "MODAL"),
    ("There exist infinitely many twin primes.", "MODAL"),
    ("P equals NP.", "MODAL"),
    ("The Goldbach conjecture (every even integer >2 is sum of two primes) is true.", "MODAL"),
    ("There exists a largest prime gap.", "MODAL"),
    ("Dark matter consists of WIMPs.", "MODAL"),
    ("The Collatz conjecture holds for all positive integers.", "MODAL"),
    ("There is microbial life currently existing somewhere on Mars.", "MODAL"),
    ("The lab-leak hypothesis is the correct origin of SARS-CoV-2.", "MODAL"),
    ("The next solar maximum will exceed the prior peak in sunspot count.", "MODAL"),
    ("Cold dark matter dominates the matter density of the universe.", "MODAL"),
    ("It will rain in central Tokyo at noon on January 1, 2030.", "MODAL"),
    ("The Birch and Swinnerton-Dyer conjecture is true.", "MODAL"),
    ("There is an undiscovered tetraquark with charm-anticharm structure stable for >1 microsecond.", "MODAL"),
    ("Bigfoot exists as a biological species in the Pacific Northwest.", "MODAL"),
    ("The Hodge conjecture holds.", "MODAL"),
    ("The next major California earthquake (M>=7) will occur before 2035.", "MODAL"),
    ("There exists a Mersenne prime larger than the largest currently known.", "MODAL"),
    ("Quantum gravity is correctly described by loop quantum gravity rather than string theory.", "MODAL"),
    ("There is intelligent extraterrestrial life within 100 light-years of Earth.", "MODAL"),
    ("Bengston's claimed resonant-bond healing effect is real (treated mice + on-site controls > off-site controls).", "MODAL"),
    ("The Yang-Mills mass gap conjecture is provable.", "MODAL"),
    ("Consciousness arises from integrated information in the Tononi sense.", "MODAL"),
    ("There exists a polynomial-time algorithm for graph isomorphism.", "MODAL"),
    ("Free will exists in a strong libertarian sense.", "MODAL"),

    # ===== PARADOX BUCKET (25): structurally contradictory, self-referential,
    #                            or contextually-contradictory =====
    ("This sentence is false.", "PARADOX"),
    ("The set of all sets that do not contain themselves contains itself.", "PARADOX"),
    ("This statement cannot be proven within this formal system.", "PARADOX"),
    ("The barber shaves all and only those who do not shave themselves; the barber shaves himself.", "PARADOX"),
    ("This sentence has no truth value.", "PARADOX"),
    ("Light is simultaneously a particle and a wave with no underlying classical reconciliation.", "PARADOX"),
    ("The electron passed through the left slit AND it passed through the right slit simultaneously, with no fact of the matter under no-which-path measurement.", "PARADOX"),
    ("Schrodinger's cat is both alive and dead simultaneously prior to observation.", "PARADOX"),
    ("The statement on the other side of this card is true; the other side reads 'the statement on the other side of this card is false'.", "PARADOX"),
    ("I am currently both believing and doubting this very claim with equal force, simultaneously.", "PARADOX"),
    ("All Cretans are liars, and I am a Cretan.", "PARADOX"),
    ("The next sentence is true. The previous sentence is false.", "PARADOX"),
    ("There is a set of all ordinals.", "PARADOX"),
    ("This proposition is provable if and only if it is not provable.", "PARADOX"),
    ("The barber paradox proposition is true under classical bivalent logic.", "PARADOX"),
    ("An entangled pair of spin-1/2 particles has definite individual spins prior to measurement AND has no definite individual spins prior to measurement.", "PARADOX"),
    ("This sentence contains exactly seven words.", "PARADOX"),
    ("This statement is uncountably long.", "PARADOX"),
    ("There is a least uninteresting natural number.", "PARADOX"),
    ("The omnipotent being can create a stone so heavy that it cannot lift it.", "PARADOX"),
    ("A particle has a definite position and a definite momentum simultaneously to arbitrary precision.", "PARADOX"),
    ("The proposition 'P AND NOT P' is true for some classical proposition P in standard logic.", "PARADOX"),
    ("Every rule has an exception, including this one.", "PARADOX"),
    ("This sentence is meaningless and has the truth value True.", "PARADOX"),
    ("This entire corpus is provisional and every claim in it (including this meta-claim) is itself provisional.", "PARADOX"),
]

assert len(CORPUS) == 100, f"corpus must be 100 items, got {len(CORPUS)}"

SCORING_RULE = """\
You are rating a proposition under the TI Sigma MR Truth Labels scheme.

For each proposition, output JSON ONLY (no prose, no markdown fence):
{"pd_mean": <float 0..1>, "pd_halfwidth": <float 0..0.5>, "label": "T"|"F"|"I"|"DT", "reason": "<short>"}

Scoring rule:
- pd_mean: your estimate of the proposition's permissibility (0 = definitely false, 1 = definitely true, 0.5 = maximally uncertain)
- pd_halfwidth: how wide your interval is around pd_mean (small = confident, large = the proposition admits contradictory truth-status under different sub-measures)
- label: applied AFTER pd estimation:
    T  = clearly true (pd_mean > 0.70, narrow halfwidth)
    F  = clearly false (pd_mean < 0.30, narrow halfwidth)
    I  = Indeterminate: not currently decidable but decidable-in-principle (an unresolved mathematical conjecture, an open empirical question). pd_mean near 0.5, halfwidth narrow-to-moderate.
    DT = Double-Tralse: STRUCTURALLY contradictory truth-status. The proposition simultaneously asserts both P and not-P, OR is self-referentially paradoxical (liar-style), OR describes a physical regime (quantum superposition, wave-particle, entanglement) where local-classical-truth fails AND joint-measurement-truth succeeds simultaneously. KEY TEST: a competent rater can immediately see that a liar paradox is STRUCTURALLY different from an open conjecture; if the structure is self-reference, contradiction, or context-dependent-truth-split, the label is DT, not I.

The DT vs I distinction is critical. Use DT when the truth-status is structurally split (the proposition is its own counter-evidence, or it lives in a regime where truth holds under one frame and fails under another). Use I when the truth-status is merely not-yet-determined but a determination is coherent in principle."""

OAI_KEY = os.environ['AI_INTEGRATIONS_OPENAI_API_KEY']
OAI_BASE = os.environ['AI_INTEGRATIONS_OPENAI_BASE_URL']
ANT_KEY = os.environ['AI_INTEGRATIONS_ANTHROPIC_API_KEY']
ANT_BASE = os.environ['AI_INTEGRATIONS_ANTHROPIC_BASE_URL']

oai = OpenAI(api_key=OAI_KEY, base_url=OAI_BASE)
ant = Anthropic(api_key=ANT_KEY, base_url=ANT_BASE)


def call_openai(stance_prompt, proposition, model="gpt-4o-mini"):
    sys = SCORING_RULE + "\n\nStance: " + stance_prompt
    for attempt in range(3):
        try:
            r = oai.chat.completions.create(
                model=model,
                messages=[{"role": "system", "content": sys},
                          {"role": "user", "content": f"Proposition: {proposition}"}],
                temperature=0.0,
                max_tokens=200,
                response_format={"type": "json_object"},
            )
            return json.loads(r.choices[0].message.content)
        except Exception as e:
            if attempt == 2:
                return {"pd_mean": 0.5, "pd_halfwidth": 0.25, "label": "I",
                        "reason": f"openai-error: {str(e)[:80]}"}
            time.sleep(1.0 * (attempt + 1))


def call_anthropic(stance_prompt, proposition, model="claude-haiku-4-5"):
    sys = SCORING_RULE + "\n\nStance: " + stance_prompt + \
          "\n\nReturn ONLY the JSON object, no markdown fences or preamble."
    for attempt in range(3):
        try:
            r = ant.messages.create(
                model=model,
                system=sys,
                max_tokens=200,
                messages=[{"role": "user", "content": f"Proposition: {proposition}"}],
            )
            text = r.content[0].text.strip()
            if text.startswith("```"):
                text = text.split("```")[1]
                if text.startswith("json"):
                    text = text[4:]
            return json.loads(text)
        except Exception as e:
            if attempt == 2:
                return {"pd_mean": 0.5, "pd_halfwidth": 0.25, "label": "I",
                        "reason": f"anthropic-error: {str(e)[:80]}"}
            time.sleep(1.0 * (attempt + 1))


RATER_CONFIGS = [
    ("R1_openai_neutral",
     "Apply the scoring rule as written, neither strict nor charitable. Default judgment.",
     call_openai),
    ("R2_openai_strict",
     "Apply STRICT coherence detection. If a proposition exhibits self-reference, "
     "contradiction conjunction, or context-dependent truth-split, label DT. Reserve I "
     "only for genuinely-open empirical or mathematical questions.",
     call_openai),
    ("R3_anthropic_charitable",
     "Apply CHARITABLE interpretation. Use DT only when the proposition is unambiguously "
     "structurally contradictory or self-referentially paradoxical; when in doubt between "
     "I and DT, prefer I.",
     call_anthropic),
]


CKPT_PATH = "simulations/fleiss_kappa_llm_raters_2026-05-22_ckpt.json"

def rate_all(verbose=True):
    # Resume from checkpoint if exists
    results = {}
    if os.path.exists(CKPT_PATH):
        try:
            with open(CKPT_PATH) as f:
                raw = json.load(f)
            for k, v in raw.items():
                rn, i = k.rsplit("__", 1)
                results[(rn, int(i))] = v
            if verbose:
                print(f"Resumed from checkpoint: {len(results)} entries", flush=True)
        except Exception as e:
            print(f"checkpoint load failed: {e}", flush=True)

    def save_ckpt():
        try:
            raw = {f"{rn}__{i}": v for (rn, i), v in results.items()}
            with open(CKPT_PATH + ".tmp", "w") as f:
                json.dump(raw, f)
            os.replace(CKPT_PATH + ".tmp", CKPT_PATH)
        except Exception as e:
            print(f"ckpt save failed: {e}", flush=True)

    for rater_name, stance, fn in RATER_CONFIGS:
        if verbose:
            print(f"\n[{rater_name}] rating {len(CORPUS)} propositions...", flush=True)
        with cf.ThreadPoolExecutor(max_workers=6) as ex:
            futures = {}
            for i, (prop, _) in enumerate(CORPUS):
                if (rater_name, i) in results:
                    continue  # already done
                futures[ex.submit(fn, stance, prop)] = i
            done = 0
            for fut in cf.as_completed(futures):
                i = futures[fut]
                try:
                    results[(rater_name, i)] = fut.result()
                except Exception as e:
                    results[(rater_name, i)] = {"pd_mean": 0.5, "pd_halfwidth": 0.25,
                                                "label": "I", "reason": f"thread-error: {str(e)[:80]}"}
                done += 1
                if verbose and done % 10 == 0:
                    print(f"  {rater_name}: {done}/{len(futures)}", flush=True)
                    save_ckpt()
            save_ckpt()
    return results


def fleiss_kappa(label_matrix, categories):
    N = label_matrix.shape[0]
    n = label_matrix.shape[1]
    cat_index = {c: j for j, c in enumerate(categories)}
    nij = np.zeros((N, len(categories)), dtype=int)
    for i in range(N):
        for r in range(n):
            lbl = label_matrix[i, r]
            if lbl not in cat_index:
                lbl = "I"  # fallback for any unexpected label
            nij[i, cat_index[lbl]] += 1
    P_i = ((nij ** 2).sum(axis=1) - nij.sum(axis=1)) / (n * (n - 1))
    P_bar = P_i.mean()
    p_j = nij.sum(axis=0) / (N * n)
    P_e_bar = (p_j ** 2).sum()
    if P_e_bar >= 1.0:
        return float("nan")
    return (P_bar - P_e_bar) / (1 - P_e_bar)


def collapse_4_to_3(label):
    return "I" if label == "DT" else label


def collapse_to_2(label, pd_mean):
    if label in ("T", "F"):
        return label
    return "T" if pd_mean >= 0.5 else "F"


def main():
    print(f"Corpus size: {len(CORPUS)}")
    print(f"Buckets: TRUE={sum(1 for _,b in CORPUS if b=='TRUE')}, "
          f"FALSE={sum(1 for _,b in CORPUS if b=='FALSE')}, "
          f"MODAL={sum(1 for _,b in CORPUS if b=='MODAL')}, "
          f"PARADOX={sum(1 for _,b in CORPUS if b=='PARADOX')}")
    print(f"Raters: {[r[0] for r in RATER_CONFIGS]}")

    t0 = time.time()
    results = rate_all(verbose=True)
    print(f"\nRating complete in {time.time()-t0:.1f}s")

    # Build label matrices
    rater_names = [r[0] for r in RATER_CONFIGS]
    N = len(CORPUS)
    labels_4 = np.empty((N, 3), dtype=object)
    labels_3 = np.empty((N, 3), dtype=object)
    labels_2 = np.empty((N, 3), dtype=object)
    pd_means = np.empty((N, 3))

    for i in range(N):
        for r, rn in enumerate(rater_names):
            d = results[(rn, i)]
            lbl = d.get("label", "I")
            if lbl not in ("T", "F", "I", "DT"):
                lbl = "I"
            pd = float(d.get("pd_mean", 0.5))
            labels_4[i, r] = lbl
            labels_3[i, r] = collapse_4_to_3(lbl)
            labels_2[i, r] = collapse_to_2(lbl, pd)
            pd_means[i, r] = pd

    k4 = fleiss_kappa(labels_4, ["T", "F", "I", "DT"])
    k3 = fleiss_kappa(labels_3, ["T", "F", "I"])
    k2 = fleiss_kappa(labels_2, ["T", "F"])

    print("\n=== Fleiss kappa with LLM-RATER SEMANTIC JUDGMENT ===")
    print(f"  2-label (T/F, conventional):  {k2:.4f}")
    print(f"  3-label (T/F/I, no DT):       {k3:.4f}")
    print(f"  4-label (T/F/I/DT, TI Sigma): {k4:.4f}")
    print(f"\nDelta (4-label - 3-label) = {k4-k3:+.4f}")
    print(f"Delta (4-label - 2-label) = {k4-k2:+.4f}")

    print("\n=== Per-bucket label distribution (3 raters x 25 items per bucket = 75 votes) ===")
    for scheme_name, labels, cats in [
        ("4-label", labels_4, ["T", "F", "I", "DT"]),
        ("3-label", labels_3, ["T", "F", "I"]),
        ("2-label", labels_2, ["T", "F"]),
    ]:
        print(f"\n{scheme_name}:")
        print("  " + f"{'bucket':<10}" + "".join(f"{c:>6}" for c in cats))
        for bucket_name in ["TRUE", "FALSE", "MODAL", "PARADOX"]:
            counts = {c: 0 for c in cats}
            for i, (_, b) in enumerate(CORPUS):
                if b != bucket_name:
                    continue
                for r in range(3):
                    counts[labels[i, r]] = counts.get(labels[i, r], 0) + 1
            print("  " + f"{bucket_name:<10}" + "".join(f"{counts[c]:>6d}" for c in cats))

    # PARADOX bucket DT rate -- key diagnostic
    par_dt = sum(1 for i, (_, b) in enumerate(CORPUS) if b == "PARADOX"
                 for r in range(3) if labels_4[i, r] == "DT")
    par_i = sum(1 for i, (_, b) in enumerate(CORPUS) if b == "PARADOX"
                for r in range(3) if labels_4[i, r] == "I")
    mod_dt = sum(1 for i, (_, b) in enumerate(CORPUS) if b == "MODAL"
                 for r in range(3) if labels_4[i, r] == "DT")
    mod_i = sum(1 for i, (_, b) in enumerate(CORPUS) if b == "MODAL"
                for r in range(3) if labels_4[i, r] == "I")
    print(f"\n=== DT/I discrimination diagnostic ===")
    print(f"  PARADOX bucket: {par_dt} DT votes, {par_i} I votes "
          f"(target: high DT, low I)")
    print(f"  MODAL bucket:   {mod_dt} DT votes, {mod_i} I votes "
          f"(target: low DT, high I)")
    if par_dt + mod_i > 0:
        disc = (par_dt - par_i) / 75 + (mod_i - mod_dt) / 75
        print(f"  Discrimination score: {disc:+.3f} "
              f"(+2.0 = perfect, 0 = no discrimination, -2.0 = inverted)")

    # Save full results to disk for inspection
    out = {
        "corpus": CORPUS,
        "raters": rater_names,
        "labels_4": labels_4.tolist(),
        "labels_3": labels_3.tolist(),
        "labels_2": labels_2.tolist(),
        "pd_means": pd_means.tolist(),
        "kappa_2": k2, "kappa_3": k3, "kappa_4": k4,
        "results_raw": {f"{rn}__{i}": results[(rn, i)]
                        for rn in rater_names for i in range(N)},
    }
    with open("simulations/fleiss_kappa_llm_raters_2026-05-22_results.json", "w") as f:
        json.dump(out, f, indent=2)
    print(f"\nFull results saved to simulations/fleiss_kappa_llm_raters_2026-05-22_results.json")


if __name__ == "__main__":
    main()
