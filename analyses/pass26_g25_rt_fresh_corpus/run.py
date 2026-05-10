"""
g25 — Pre-registered fresh-corpus K=500 R_t-vs-accuracy run.
Pre-registration: ./PRE_REGISTRATION.json (frozen before this script ran).
"""
import json, math, random, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path("analyses/tsc_h4_sat")))
from tsc_h4_sat_prototype import (
    build_tsc_hamiltonian, gen_3sat, is_sat, restricted_ground, roc_auc,
)

PRE = json.loads(Path("analyses/pass26_g25_rt_fresh_corpus/PRE_REGISTRATION.json").read_text())
d = PRE["design"]
seed = d["instance_seed"]
M_target = d["n_instances"]; K = d["mappings_per_instance"]

H_tsc, _ = build_tsc_hamiltonian()

rng = random.Random(seed)
instances = []
for _ in range(M_target):
    n_vars = rng.randint(d["min_vars"], d["max_vars"])
    ratio = d["clause_var_ratio_min"] + rng.random() * (
        d["clause_var_ratio_max"] - d["clause_var_ratio_min"])
    n_clauses = max(3, int(round(n_vars * ratio)))
    inst = gen_3sat(rng, n_vars, n_clauses)
    sat = is_sat(inst, n_vars)
    if n_vars + n_clauses <= 57:
        instances.append((n_vars, n_clauses, inst, sat))
M = len(instances)
print(f"Fresh corpus: M={M}, K={K}, seed={seed}")

energies = np.zeros((M, K))
labels = np.array([0 if s else 1 for (_, _, _, s) in instances])
for i in range(M):
    n_vars, n_clauses, _, _ = instances[i]
    n_needed = n_vars + n_clauses
    for k in range(K):
        map_rng = random.Random((seed * 10007) + (i * 31337) + k)
        indices = map_rng.sample(range(57), n_needed)
        energies[i, k] = restricted_ground(H_tsc, indices)
    if (i + 1) % 50 == 0:
        print(f"  ... {i+1}/{M} instances done")

per_map_auc = np.array([1.0 - roc_auc(energies[:, k].tolist(), labels.tolist())
                        for k in range(K)])

T = float(energies.std(axis=0).mean())
alpha = np.exp(-(energies - energies.min(axis=0, keepdims=True)) / T)
alpha = alpha / alpha.sum(axis=0, keepdims=True)
ent = -(alpha * np.log(alpha + 1e-30)).sum(axis=0)
R_t = 1.0 - ent / math.log(M)


def pearson(x, y):
    x = np.asarray(x); y = np.asarray(y)
    xm, ym = x.mean(), y.mean()
    num = ((x - xm) * (y - ym)).sum()
    den = math.sqrt(((x - xm) ** 2).sum() * ((y - ym) ** 2).sum())
    return num / den if den > 0 else float('nan')


r_obs = pearson(R_t, per_map_auc)
rng_p = np.random.RandomState(seed)
n_perm = 10000
perm_r = np.empty(n_perm); idx = np.arange(K)
for p in range(n_perm):
    rng_p.shuffle(idx)
    perm_r[p] = pearson(R_t, per_map_auc[idx])
p_two = float((np.abs(perm_r) >= abs(r_obs)).mean())

if r_obs > 0.15 and p_two < 0.01: verdict = "CONFIRM"
elif r_obs > 0.10 and p_two < 0.05: verdict = "WEAK_CONFIRM"
elif r_obs > 0 and p_two >= 0.05: verdict = "NULL"
else: verdict = "DISCONFIRM"

print(f"\nPearson r = {r_obs:+.4f} ; perm p = {p_two:.4f}")
print(f"Per-map AUC mean = {per_map_auc.mean():.4f} ; R_t mean = {R_t.mean():.4f}")
print(f"Verdict: {verdict}")

out = {
    "study_id": PRE["study_id"], "M": int(M), "K": int(K), "seed": int(seed),
    "softmax_T": float(T), "pearson_r": float(r_obs),
    "permutation_p_two_sided": p_two, "permutation_n": n_perm,
    "permutation_null_mean": float(perm_r.mean()),
    "permutation_null_std": float(perm_r.std()),
    "per_map_auc_mean": float(per_map_auc.mean()),
    "per_map_auc_std": float(per_map_auc.std()),
    "R_t_mean": float(R_t.mean()), "R_t_std": float(R_t.std()),
    "verdict": verdict,
    "pre_registration_path": "analyses/pass26_g25_rt_fresh_corpus/PRE_REGISTRATION.json",
}
Path("analyses/pass26_g25_rt_fresh_corpus/results.json").write_text(json.dumps(out, indent=2))
print(f"Saved → analyses/pass26_g25_rt_fresh_corpus/results.json")
