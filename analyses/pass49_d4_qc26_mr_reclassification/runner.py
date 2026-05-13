"""
D4 — Pass-49: Re-classify qc26 GHZ-5 Mermin counts into MR Truth Labels.

PRE-REGISTRATION (frozen at write-time, anti-cheat per Pass-45 §11):
  Input: analyses/pass45_qc26_ghz5_mermin/results.json (counts per setting,
         3 settings A_1Y / B_3Y / C_5Y, n=1024 shots/setting on ibm_marrakesh).

  Classification rule (Filter-D4-frozen):
    For each 5-bit measurement outcome b = b4 b3 b2 b1 b0:
      Let HW(b) = sum of bits.
      T  : HW in {0, 5}                  — canonical GHZ-pole alignment
      F  : HW in {1, 4}                  — single-bit deviation from a pole
      DT : HW in {2, 3}                  — both-pole signature coexistence
      I  : not assigned in Z-basis projection
           (rationale: I is a measurement-CONTEXT property, not an
            outcome property; absence of I bucket here is informative,
            not a defect — see urb_608 §7 Indeterminate-as-Epitome)

  Outputs (per setting + aggregate):
    n_T, n_F, n_DT, total
    fraction f_T, f_F, f_DT
    Wilson 95% CI on each fraction
    Tralse-bucket cross-check: f_T + f_F + f_DT == 1.0 exactly
                              (i.e., I-bucket = 0 by design)

  CONFIRM / DISCONFIRM per Pass-49 D4 directional pre-reg:
    H_D4 (directional): qc26 GHZ-5 hardware data exhibits a non-trivial
      DT bucket. Specifically, predict f_DT > 0.50 (the classical-mixture
      null would give f_DT ~ 5/16 = 0.3125 from binomial(5, 0.5) on
      HW in {2,3}; a true GHZ would give f_DT -> 0 in the noiseless
      limit). The observed Mermin |M5| = 14.535 (71-sigma) implies
      strong entanglement, which under this classification rule should
      drive intermediate HW bins UP because Y-basis measurements rotate
      probability mass off the {00000, 11111} poles into the mid-HW
      shell.
    f_DT >= 0.50 -> CONFIRM directional
    0.3125 < f_DT < 0.50 -> WEAK (consistent with mixed/decohered)
    f_DT <= 0.3125 -> DISCONFIRM (would indicate near-classical statistics)

  Discriminator hierarchy (most-confirmatory first):
    1. f_DT >> 0.50 simultaneously across all 3 settings -> strongest CONFIRM
    2. f_DT >> 0.50 in >=2 settings -> CONFIRM
    3. f_DT > 0.3125 in >=2 settings -> WEAK
    4. f_DT <= 0.3125 across all settings -> DISCONFIRM

NOTE: This is a re-analysis of existing data; no QPU time consumed; cost $0.
"""

import json
import math
from pathlib import Path

INPUT_PATH = Path("analyses/pass45_qc26_ghz5_mermin/results.json")
OUTPUT_PATH = Path("analyses/pass49_d4_qc26_mr_reclassification/results.json")


def hamming_weight(bitstring: str) -> int:
    return sum(1 for c in bitstring if c == "1")


def classify(bitstring: str) -> str:
    hw = hamming_weight(bitstring)
    if hw in (0, 5):
        return "T"
    if hw in (1, 4):
        return "F"
    if hw in (2, 3):
        return "DT"
    return "I"  # unreachable for 5-bit


def wilson_95_ci(k: int, n: int) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    z = 1.959963984540054
    p = k / n
    denom = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / denom
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / denom
    return (max(0.0, centre - half), min(1.0, centre + half))


def reclassify_setting(counts: dict[str, int]) -> dict:
    buckets = {"T": 0, "F": 0, "DT": 0, "I": 0}
    for bitstring, c in counts.items():
        buckets[classify(bitstring)] += c
    total = sum(buckets.values())
    fractions = {k: (v / total if total else 0.0) for k, v in buckets.items()}
    cis = {k: wilson_95_ci(buckets[k], total) for k in buckets}
    return {"counts": buckets, "fractions": fractions, "wilson_95ci": cis, "n": total}


def main() -> dict:
    with INPUT_PATH.open() as f:
        data = json.load(f)

    per_setting = {}
    aggregate_counts = {"T": 0, "F": 0, "DT": 0, "I": 0}

    for name, payload in data["settings"].items():
        result = reclassify_setting(payload["counts"])
        per_setting[name] = result
        for k in aggregate_counts:
            aggregate_counts[k] += result["counts"][k]

    agg_total = sum(aggregate_counts.values())
    agg_fractions = {k: v / agg_total for k, v in aggregate_counts.items()}
    agg_cis = {k: wilson_95_ci(aggregate_counts[k], agg_total) for k in aggregate_counts}

    f_dt_per_setting = {n: per_setting[n]["fractions"]["DT"] for n in per_setting}
    n_settings_above_050 = sum(1 for v in f_dt_per_setting.values() if v > 0.50)
    n_settings_above_null = sum(1 for v in f_dt_per_setting.values() if v > 0.3125)

    if n_settings_above_050 == 3:
        verdict = "CONFIRM_STRONG"
    elif n_settings_above_050 >= 2:
        verdict = "CONFIRM"
    elif n_settings_above_null >= 2:
        verdict = "WEAK"
    else:
        verdict = "DISCONFIRM"

    out = {
        "test_id": "D4_qc26_mr_reclassification",
        "pass": 49,
        "input_source": str(INPUT_PATH),
        "input_sha_note": data.get("runner_sha256"),
        "n_settings": len(per_setting),
        "per_setting": per_setting,
        "aggregate": {
            "counts": aggregate_counts,
            "fractions": agg_fractions,
            "wilson_95ci": agg_cis,
            "n": agg_total,
        },
        "directional_test": {
            "hypothesis": "f_DT > 0.50",
            "classical_null_f_DT": 0.3125,
            "f_DT_per_setting": f_dt_per_setting,
            "n_settings_above_0.50": n_settings_above_050,
            "n_settings_above_classical_null": n_settings_above_null,
            "verdict": verdict,
        },
        "i_bucket_check": {
            "f_I_aggregate": agg_fractions["I"],
            "expected_zero_in_z_basis": True,
            "note": "Confirms I-as-context (urb_608 §7) not I-as-outcome.",
        },
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT_PATH.open("w") as f:
        json.dump(out, f, indent=2)

    print(f"D4 verdict: {verdict}")
    print(f"f_DT per setting: {f_dt_per_setting}")
    print(f"f_DT aggregate: {agg_fractions['DT']:.4f} (95% CI: {agg_cis['DT']})")
    print(f"f_T aggregate:  {agg_fractions['T']:.4f}")
    print(f"f_F aggregate:  {agg_fractions['F']:.4f}")
    print(f"f_I aggregate:  {agg_fractions['I']:.4f} (expected 0.0)")
    return out


if __name__ == "__main__":
    main()
