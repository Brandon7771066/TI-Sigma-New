"""
r20 Prospective Replication of R-A — Pass 21 (Brandon directive).

Tests the inverted H4 prediction "higher restricted-H ⇒ SAT" on a
FRESH 200-instance corpus generated under independent seed
(31415927, π-derived) using the K=100 mapping-sensitivity protocol
established in Pass 20.

Decision thresholds are frozen in PRE_REGISTRATION.json BEFORE this
runner is executed. The runner reads thresholds from that file and
reports the verdict against them verbatim.

Per #69:
  - This is a single fresh-corpus replication; the verdict explicitly
    requires further 3rd-party / 3rd-corpus replication to upgrade
    beyond TI-Sigma-internal confirmation.
  - If a CONFIRM verdict emerges, the headline is "R-A confirmed on
    one fresh corpus" — NOT "TI Sigma framework prediction validated."
"""
import argparse, json, math, random
from pathlib import Path

import numpy as np

import sys
sys.path.insert(0, str(Path("analyses/tsc_h4_sat")))
from tsc_h4_sat_prototype import (
    build_tsc_hamiltonian, gen_3sat, is_sat, restricted_ground, roc_auc
)

PRE_REG = Path("analyses/tsc_h4_sat_r20_replication/PRE_REGISTRATION.json")
OUT = Path("analyses/tsc_h4_sat_r20_replication/results.json")
OUT_TXT = Path("analyses/tsc_h4_sat_r20_replication/results.txt")


def gen_corpus(seed, n_instances, min_vars, max_vars, ratio_min, ratio_max):
    """Independent corpus generator matching Pass-20 generate_instances
    contract but with explicit fresh-seed parameter (no SEED constant
    fallback)."""
    rng = random.Random(seed)
    out = []
    for _ in range(n_instances):
        n_vars = rng.randint(min_vars, max_vars)
        ratio = ratio_min + rng.random() * (ratio_max - ratio_min)
        n_clauses = max(3, int(round(n_vars * ratio)))
        inst = gen_3sat(rng, n_vars, n_clauses)
        sat = is_sat(inst, n_vars)
        if n_vars + n_clauses <= 57:
            out.append((n_vars, n_clauses, inst, sat))
    return out


def run():
    pre = json.loads(PRE_REG.read_text())
    d = pre["design"]
    rules = pre["pre_registered_decision_rules"]

    print("=" * 72)
    print("r20 Prospective Replication of R-A (Pass 21)")
    print("=" * 72)
    print(f"Pre-registration: {PRE_REG}")
    print(f"Filed before run: {pre['filed_before_run']}")
    print(f"Hypothesis: {pre['hypothesis_under_test']}")
    print(f"Instance seed: {d['instance_seed']} (FRESH, distinct from training)")
    print(f"N_instances: {d['n_instances']}; vars {d['min_vars']}-{d['max_vars']};"
          f" clauses/var {d['clause_var_ratio_min']}-{d['clause_var_ratio_max']}")
    print(f"K mappings/instance: {d['mappings_per_instance']}")
    print(f"Pre-registered confirm threshold: {rules['confirm_threshold']}")
    print(f"Pre-registered disconfirm threshold: {rules['disconfirm_threshold']}")

    H, _ = build_tsc_hamiltonian()
    instances = gen_corpus(
        d["instance_seed"], d["n_instances"],
        d["min_vars"], d["max_vars"],
        d["clause_var_ratio_min"], d["clause_var_ratio_max"],
    )
    M = len(instances)
    K = d["mappings_per_instance"]
    n_sat = sum(1 for (_, _, _, s) in instances if s)
    n_unsat = M - n_sat
    print(f"\nCorpus generated: M={M}; SAT={n_sat}; UNSAT={n_unsat}")

    if n_sat < 20 or n_unsat < 20:
        verdict = "CORPUS-QUALITY FAILURE (n_sat or n_unsat < 20)"
        print(f"\n>>> {verdict} <<<")
        out = {"verdict": verdict, "n_sat": n_sat, "n_unsat": n_unsat,
               "pre_reg": pre, "corpus_quality_failure": True}
        OUT.write_text(json.dumps(out, indent=2))
        return out

    print(f"Computing K={K} mappings × M={M} instances ...")
    energies = np.zeros((M, K))
    labels = np.array([0 if s else 1 for (_, _, _, s) in instances])
    base = d["instance_seed"]
    for i in range(M):
        n_vars, n_clauses, _, _ = instances[i]
        n_needed = n_vars + n_clauses
        for k in range(K):
            map_rng = random.Random((base * 10007) + (i * 31337) + k)
            indices = map_rng.sample(range(57), n_needed)
            energies[i, k] = restricted_ground(H, indices)

    # AUC for "lower-E ⇒ SAT" using mean energy per instance:
    mean_e = energies.mean(axis=1)
    auc_lower = roc_auc(mean_e.tolist(), labels.tolist())
    auc_inverted = 1.0 - auc_lower  # "higher-E ⇒ SAT"

    # Per-mapping inverted AUCs
    per_map_inverted = []
    for k in range(K):
        a = roc_auc(energies[:, k].tolist(), labels.tolist())
        if not math.isnan(a):
            per_map_inverted.append(1.0 - a)
    per_map_inverted = np.array(per_map_inverted)
    z = (per_map_inverted.mean() - 0.5) / (per_map_inverted.std(ddof=1) / math.sqrt(K))

    # Decision per pre-reg
    primary = float(auc_inverted)
    if primary >= rules["confirm_threshold"]:
        verdict = (f"CONFIRMED — averaged_energy_auc_inverted = {primary:.4f} "
                   f">= confirm threshold {rules['confirm_threshold']}. "
                   "R-A upgraded to corpus-confirmed; 3rd-corpus / 3rd-party "
                   "replication still required for external claim.")
    elif primary < rules["disconfirm_threshold"]:
        verdict = (f"DISCONFIRMED — averaged_energy_auc_inverted = {primary:.4f} "
                   f"< disconfirm threshold {rules['disconfirm_threshold']}. "
                   "R-A sign-flip rejected on this corpus; H4 must be "
                   "retired or substantially reframed.")
    else:
        verdict = (f"AMBIGUOUS — averaged_energy_auc_inverted = {primary:.4f} "
                   f"in [{rules['disconfirm_threshold']}, {rules['confirm_threshold']}). "
                   "Third corpus required; current evidence inconclusive.")

    print()
    print("## Result")
    print(f"  Averaged-energy AUC (lower-E ⇒ SAT):  {auc_lower:.4f}")
    print(f"  Averaged-energy AUC (HIGHER-E ⇒ SAT): {auc_inverted:.4f}  <- PRIMARY")
    print(f"  Per-mapping inverted AUC: mean={per_map_inverted.mean():.4f}  "
          f"std={per_map_inverted.std(ddof=1):.4f}  N={len(per_map_inverted)}")
    print(f"  Per-mapping inverted AUC range: "
          f"[{per_map_inverted.min():.4f}, {per_map_inverted.max():.4f}]")
    print(f"  z(per-map inverted mean vs 0.5) = {z:+.2f}")
    print()
    print(f"## Pre-registered decision: {verdict}")

    out = {
        "study_id": pre["study_id"],
        "instance_seed": d["instance_seed"],
        "n_instances_attempted": d["n_instances"],
        "n_instances_used": int(M),
        "n_sat": int(n_sat),
        "n_unsat": int(n_unsat),
        "K": K,
        "averaged_energy_auc_lower": float(auc_lower),
        "averaged_energy_auc_inverted": float(auc_inverted),
        "per_mapping_inverted_mean": float(per_map_inverted.mean()),
        "per_mapping_inverted_std": float(per_map_inverted.std(ddof=1)),
        "per_mapping_inverted_min": float(per_map_inverted.min()),
        "per_mapping_inverted_max": float(per_map_inverted.max()),
        "z_per_map_inverted_vs_half": float(z),
        "primary_metric_value": primary,
        "confirm_threshold": rules["confirm_threshold"],
        "disconfirm_threshold": rules["disconfirm_threshold"],
        "verdict": verdict,
        "pre_registration_path": str(PRE_REG),
    }
    OUT.write_text(json.dumps(out, indent=2))

    summary = [
        f"r20 prospective replication — {pre['study_id']}",
        f"Fresh seed: {d['instance_seed']}; M={M} (SAT={n_sat}, UNSAT={n_unsat}); K={K}",
        f"Averaged-energy AUC (HIGHER-E ⇒ SAT): {auc_inverted:.4f}",
        f"Per-mapping inverted AUC: {per_map_inverted.mean():.4f} ± "
        f"{per_map_inverted.std(ddof=1):.4f} (N={len(per_map_inverted)})",
        f"Pre-registered decision: {verdict}",
    ]
    OUT_TXT.write_text("\n".join(summary) + "\n")
    print(f"\nSaved {OUT}, {OUT_TXT}")
    return out


if __name__ == "__main__":
    run()
