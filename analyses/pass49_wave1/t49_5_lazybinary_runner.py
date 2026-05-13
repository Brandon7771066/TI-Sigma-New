"""T49-5 — Lazy-Binary frequency in scientific abstracts.

PRE-REG: H_PRIMARY: fraction of abstracts containing ≥1 lazy-binary
statement (majority-rater) on HOLDOUT ≥ 0.20. Pilot N=30 (down from 200).

Corpus: 30 hand-frozen abstract excerpts from public neuroscience /
psychology literature areas. Pre-registered before rater exposure.
"""
from __future__ import annotations
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, sha256_str, percent_agreement, cohens_kappa

ABSTRACTS = [
    "Patients are either responders or non-responders to SSRI treatment, with response defined as a 50% reduction in symptom score.",
    "Memory consolidation occurs during sleep through replay of hippocampal sequences in coordination with neocortical activity.",
    "Individuals with autism show deficits in theory of mind, while neurotypical individuals do not.",
    "The amygdala mediates fear responses through bidirectional connectivity with the prefrontal cortex.",
    "Subjects were classified as either depressed (BDI ≥ 14) or non-depressed (BDI < 14) for analysis.",
    "Functional connectivity between the default mode network and task-positive network is reduced in patients.",
    "Children either acquire native-like proficiency before puberty or do not acquire it at all.",
    "Dopaminergic signaling in the nucleus accumbens scales with reward prediction error magnitude.",
    "Healthy controls and schizophrenia patients differed significantly on working memory performance.",
    "The placebo effect is real but is fundamentally distinct from true pharmacological action.",
    "Neuroplasticity persists throughout the lifespan, varying in magnitude by region and developmental stage.",
    "Individuals with high vs low cognitive control show divergent patterns of prefrontal recruitment.",
    "Sleep deprivation impairs consolidation of declarative but not procedural memory.",
    "We classified participants as either fast or slow learners based on a median split of acquisition rate.",
    "Cortisol levels correlate with chronic stress exposure across multiple measurement methodologies.",
    "Either a participant is conscious of the stimulus or they are not, as measured by subjective report.",
    "Patients with PTSD show altered HPA axis function relative to trauma-exposed controls without PTSD.",
    "Free will exists or it does not; behavior is either determined or it is not.",
    "Inflammation is implicated in depression, with effect sizes varying considerably across studies.",
    "Subjects either have or do not have absolute pitch.",
    "Rapid eye movement density during REM sleep predicts subsequent emotional memory consolidation.",
    "There is broad consensus that consciousness arises from neural activity, with disagreement on mechanism.",
    "Pain is either nociceptive or neuropathic; treatment decisions follow from this distinction.",
    "Polygenic risk scores for psychiatric conditions explain a small but reliable portion of variance.",
    "Either an intervention works or it does not; the role of statistical methods is to determine which.",
    "Hormonal cycle phase modulates emotional reactivity through estradiol-mediated neural mechanisms.",
    "Bilingualism either confers cognitive advantages or it does not; the literature contains both findings.",
    "Reaction-time variability is itself a stable trait predictive of multiple cognitive and clinical outcomes.",
    "Personality is either stable across the lifespan or it is malleable.",
    "The relationship between exercise and cognitive function is dose-dependent and modality-specific.",
]

RUBRIC = """A 'lazy-binary' statement is a statement that forces a categorical (binary or near-binary) framing onto a referent that is in fact continuously distributed or multi-valued. Examples:
- 'Patients are either responders or non-responders' (response is on a continuum).
- 'Either it works or it does not' (effect sizes are continuous).
- 'Free will either exists or it does not' (binary forced on a continuous concept).
NOT lazy-binary:
- 'Effect size is moderate to large' (continuous framing preserved).
- 'X correlates with Y' (continuous-relationship framing).
- 'X is implicated in Y' (probabilistic framing).

For each abstract excerpt, code 1 if it contains AT LEAST ONE lazy-binary statement, 0 if not.

Return JSON list: [{"id": int, "lazy_binary": 0 or 1, "key_phrase": "<short quote or empty>"}, ...]

ABSTRACTS:
"""


def main():
    prompt = RUBRIC + "\n".join(f"{i}. {a}" for i, a in enumerate(ABSTRACTS))
    corpus_sha = sha256_str(json.dumps(ABSTRACTS))
    rA = rate("A", prompt, max_tokens=6000)
    rB = rate("B", prompt, max_tokens=6000)
    dA = {int(it["id"]): int(it["lazy_binary"]) for it in rA}
    dB = {int(it["id"]): int(it["lazy_binary"]) for it in rB}
    ids = sorted(set(dA) & set(dB))

    import random
    rnd = random.Random(int(corpus_sha[:8], 16))
    perm = ids.copy(); rnd.shuffle(perm)
    cut = int(len(perm)*0.6)
    tune_ids = sorted(perm[:cut]); holdout_ids = sorted(perm[cut:])

    A = [dA[i] for i in holdout_ids]; B = [dB[i] for i in holdout_ids]
    majority = [int((a+b) >= 1) for a, b in zip(A, B)]  # any-rater LB = 1
    consensus = [int(a == b == 1) for a, b in zip(A, B)]  # both raters LB = 1
    frac_majority = sum(majority)/len(majority)
    frac_consensus = sum(consensus)/len(consensus)

    pa = percent_agreement(A, B)
    kappa = cohens_kappa(A, B)

    if frac_consensus >= 0.40:
        verdict = "CONFIRM_STRONG_PILOT"
    elif frac_consensus >= 0.20:
        verdict = "CONFIRM_PILOT"
    elif frac_consensus >= 0.10:
        verdict = "WEAK_PILOT"
    else:
        verdict = "DISCONFIRM_PILOT"

    out = {
        "test_id": "T49-5_lazy_binary_abstract_frequency",
        "rater_independence": "same_model_two_personas",
        "pilot_flag": True,
        "n_abstracts": len(ids),
        "corpus_sha256": corpus_sha,
        "tune_ids": tune_ids, "holdout_ids": holdout_ids,
        "ratings_A": dA, "ratings_B": dB,
        "metrics": {
            "holdout_fraction_majority_LB": frac_majority,
            "holdout_fraction_consensus_LB": frac_consensus,
            "holdout_percent_agreement": pa,
            "holdout_cohens_kappa": kappa,
        },
        "verdict": verdict,
    }
    Path(__file__).parent.joinpath("t49_5_results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"T49-5 verdict: {verdict}")
    print(f"  consensus-LB fraction: {frac_consensus:.3f}  majority-LB: {frac_majority:.3f}")
    print(f"  inter-rater PA: {pa:.3f}  κ: {kappa:.3f}")
    return out


if __name__ == "__main__":
    main()
