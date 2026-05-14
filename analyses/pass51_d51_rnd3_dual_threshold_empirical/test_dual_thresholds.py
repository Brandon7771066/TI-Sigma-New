"""
D51-RND-3 Empirical Test: Dual-Threshold Validation
====================================================

Tests Brandon-approved dual-threshold framework:
- T_RAND  = 1 - T_TI  ≈ 0.0660  (saturation-complement; "true randomness" boundary)
- T_BORDER = 1 - MR1  ≈ 0.13534 (existence-complement; sub-detection-coupling boundary)
- C       = 1/(φ√2)   ≈ 0.4370  (LCC causal-detection floor; preserved)

Brandon's framing: 0.0660 is suitable successor to p=0.05 because it sits in the
neighborhood of statistical convention while being derived from corpus-canonical T_TI.

We compute, under KNOWN-RANDOM null pairs (CSPRNG, π digits, hash-stream), the
sampling distribution of Pearson |R| at multiple window sizes. Then we ask:

  (Q1) At what window size N does the empirical 95th-percentile of |R| under null
       fall below T_RAND = 0.0660?  (i.e., where does T_RAND match the p=0.05
       convention in practice?)
  (Q2) Same question for T_BORDER = 0.13534.
  (Q3) Same question for C = 0.4370.
  (Q4) At a fixed window size N=384 (Pass-49 PRIMARY n_aligned_months), what
       fraction of null draws land in each tier?

This validates whether the proposed thresholds carry the operational meaning
Brandon ascribed: T_RAND ≈ p=0.05-successor, T_BORDER ≈ broader randomness
neighborhood, C ≈ where signal-detection becomes reliable.

$0 dependencies: numpy, hashlib (stdlib), secrets (stdlib).
"""

import numpy as np
import hashlib
import secrets
import json
from pathlib import Path

# Canonical thresholds
T_RAND = 1.0 - 0.9340       # 1 - T_TI saturation-complement
T_BORDER = 1.0 - 0.8647     # 1 - MR1 existence-complement
C_LCC = 1.0 / (1.6180339887 * np.sqrt(2.0))  # 1/(φ√2)
P05_CRITICAL = lambda N: 1.96 / np.sqrt(N - 2 + 1.96**2)  # Fisher z approx

print(f"=== D51-RND-3 Dual-Threshold Empirical Test ===")
print(f"T_RAND   = 1 - T_TI  = {T_RAND:.5f}")
print(f"T_BORDER = 1 - MR1   = {T_BORDER:.5f}")
print(f"C_LCC    = 1/(φ√2)   = {C_LCC:.5f}")
print()

# ============================================================
# Source 1: System CSPRNG (secrets module)
# ============================================================
def gen_csprng(n):
    """Generate n floats in [0,1) from system CSPRNG."""
    raw = secrets.token_bytes(n * 4)
    arr = np.frombuffer(raw, dtype=np.uint32) / 2**32
    return arr.astype(np.float64)

# ============================================================
# Source 2: π digits (deterministic, statistically random)
# ============================================================
def gen_pi_digits(n, offset=0):
    """Use a large precomputed π-digit-derived stream via hash chain
    (avoids needing mpmath). For testing purposes this behaves as a
    high-quality pseudorandom stream seeded from π's hex representation."""
    # Use SHA-256 hash chain seeded with π's first 100 hex digits as proxy
    pi_seed = b"3.243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"
    out = []
    state = pi_seed
    while len(out) < n:
        state = hashlib.sha256(state).digest()
        chunk = np.frombuffer(state, dtype=np.uint32) / 2**32
        out.extend(chunk.tolist())
    return np.array(out[offset:offset+n], dtype=np.float64)

# ============================================================
# Source 3: Hash-stream (alternative CSPRNG)
# ============================================================
def gen_hash_stream(n, seed_int):
    """Hash-chain PRNG with integer seed."""
    out = []
    state = seed_int.to_bytes(8, 'little')
    while len(out) < n:
        state = hashlib.sha256(state).digest()
        chunk = np.frombuffer(state, dtype=np.uint32) / 2**32
        out.extend(chunk.tolist())
    return np.array(out[:n], dtype=np.float64)


# ============================================================
# Test: sampling distribution of |R| under null
# ============================================================
def sampling_dist(n_window, n_draws, source_pair):
    """Compute |R| for n_draws independent pairs, each of size n_window."""
    rs = []
    for k in range(n_draws):
        x = source_pair[0](n_window) if source_pair[0].__name__ != 'gen_hash_stream' else source_pair[0](n_window, 1000+k)
        y = source_pair[1](n_window) if source_pair[1].__name__ != 'gen_hash_stream' else source_pair[1](n_window, 5000+k)
        r = np.corrcoef(x, y)[0, 1]
        rs.append(abs(r))
    return np.array(rs)


# Q1-Q3: scan window sizes; find where 95th percentile crosses each threshold
WINDOWS = [10, 20, 30, 50, 75, 100, 150, 200, 300, 384, 500, 750, 1000]
N_DRAWS = 2000
np.random.seed(42)

print(f"=== Sampling distributions of |R| under null (CSPRNG × CSPRNG) ===")
print(f"{'N':>5} {'mean|R|':>9} {'med|R|':>9} {'p95|R|':>9} {'p99|R|':>9} {'max|R|':>9} {'p=.05crit':>10}")
print(f"{'-'*5:>5} {'-'*9:>9} {'-'*9:>9} {'-'*9:>9} {'-'*9:>9} {'-'*9:>9} {'-'*10:>10}")

scan_results = []
for N in WINDOWS:
    rs = sampling_dist(N, N_DRAWS, (gen_csprng, gen_csprng))
    p95 = np.percentile(rs, 95)
    p99 = np.percentile(rs, 99)
    crit = P05_CRITICAL(N)
    scan_results.append({
        "N": N,
        "mean_abs_R": float(rs.mean()),
        "median_abs_R": float(np.median(rs)),
        "p95_abs_R": float(p95),
        "p99_abs_R": float(p99),
        "max_abs_R": float(rs.max()),
        "p05_critical_pearson": float(crit),
        "frac_below_T_RAND": float((rs < T_RAND).mean()),
        "frac_below_T_BORDER": float((rs < T_BORDER).mean()),
        "frac_below_C_LCC": float((rs < C_LCC).mean()),
    })
    print(f"{N:>5} {rs.mean():>9.4f} {np.median(rs):>9.4f} {p95:>9.4f} {p99:>9.4f} {rs.max():>9.4f} {crit:>10.4f}")

print()

# ============================================================
# Q1: at what N does p95(|R|) cross T_RAND from above?
# ============================================================
print(f"=== Q1: At what N does p95(|R|_null) drop below T_RAND = {T_RAND:.4f}? ===")
for r in scan_results:
    if r["p95_abs_R"] < T_RAND:
        print(f"  First crossing at N={r['N']}: p95={r['p95_abs_R']:.4f} < {T_RAND:.4f}")
        q1_N = r['N']
        break
else:
    print(f"  Never crosses in scanned range (max N={WINDOWS[-1]})")
    q1_N = None

print(f"=== Q2: At what N does p95(|R|_null) drop below T_BORDER = {T_BORDER:.4f}? ===")
for r in scan_results:
    if r["p95_abs_R"] < T_BORDER:
        print(f"  First crossing at N={r['N']}: p95={r['p95_abs_R']:.4f} < {T_BORDER:.4f}")
        q2_N = r['N']
        break
else:
    q2_N = None

print(f"=== Q3: At what N does p95(|R|_null) drop below C_LCC = {C_LCC:.4f}? ===")
for r in scan_results:
    if r["p95_abs_R"] < C_LCC:
        print(f"  First crossing at N={r['N']}: p95={r['p95_abs_R']:.4f} < {C_LCC:.4f}")
        q3_N = r['N']
        break
else:
    q3_N = None

# ============================================================
# Q4: at N=384 (Pass-49 PRIMARY), what is the tier breakdown?
# ============================================================
print()
print(f"=== Q4: At N=384 (Pass-49 PRIMARY n_aligned_months), tier breakdown under null ===")
n384_result = [r for r in scan_results if r["N"] == 384][0]
print(f"  Frac in TRUE-RANDOMNESS    [0, T_RAND={T_RAND:.4f})   : {n384_result['frac_below_T_RAND']:.4f}")
print(f"  Frac in T_RAND-to-T_BORDER [{T_RAND:.4f}, {T_BORDER:.4f})  : {n384_result['frac_below_T_BORDER'] - n384_result['frac_below_T_RAND']:.4f}")
print(f"  Frac in T_BORDER-to-C_LCC  [{T_BORDER:.4f}, {C_LCC:.4f})  : {n384_result['frac_below_C_LCC'] - n384_result['frac_below_T_BORDER']:.4f}")
print(f"  Frac at SIGNAL ≥ C_LCC     [{C_LCC:.4f}, 1]        : {1 - n384_result['frac_below_C_LCC']:.4f}")

# ============================================================
# Q5: Cross-source validation (π × CSPRNG, hash × CSPRNG)
# ============================================================
print()
print(f"=== Q5: Cross-source check at N=384 (consistency across PRNG types) ===")
cross_sources = [
    ("CSPRNG × CSPRNG", (gen_csprng, gen_csprng)),
    ("π-stream × CSPRNG", (gen_pi_digits, gen_csprng)),
    ("hash × CSPRNG", (gen_hash_stream, gen_csprng)),
    ("hash × hash", (gen_hash_stream, gen_hash_stream)),
]
cross_results = {}
for label, pair in cross_sources:
    rs = sampling_dist(384, 1000, pair)
    cross_results[label] = {
        "p95": float(np.percentile(rs, 95)),
        "p99": float(np.percentile(rs, 99)),
        "max": float(rs.max()),
        "frac_below_T_RAND": float((rs < T_RAND).mean()),
        "frac_below_T_BORDER": float((rs < T_BORDER).mean()),
        "frac_below_C_LCC": float((rs < C_LCC).mean()),
    }
    print(f"  {label:>25}: p95={cross_results[label]['p95']:.4f}  p99={cross_results[label]['p99']:.4f}  max={cross_results[label]['max']:.4f}")

# ============================================================
# Q6: Compare to Pass-49 PRIMARY empirical observation
# ============================================================
print()
print(f"=== Q6: Reality check — Pass-49 PRIMARY empirical observations ===")
pass49_obs = {
    "L-1 initial (single block UMCSENT×SPY)": 0.0205,
    "L-1 PRIMARY (530 windows UMCSENT×SPY monthly)": 0.0306,
    "L-1 SECONDARY (530 windows SPY×^VIX)": 0.1208,
}
for label, val in pass49_obs.items():
    tier = ("TRUE-RANDOMNESS" if val < T_RAND else
            "T_RAND-to-T_BORDER" if val < T_BORDER else
            "T_BORDER-to-C_LCC" if val < C_LCC else
            "SIGNAL")
    p05_eq = P05_CRITICAL(384)  # rough comparison anchor
    print(f"  {label[:55]:<55}: |R|={val:.4f}  →  tier={tier}")

# ============================================================
# Save full results JSON
# ============================================================
out = {
    "thresholds": {
        "T_RAND_saturation_complement": T_RAND,
        "T_BORDER_existence_complement": T_BORDER,
        "C_LCC_causal_detection_floor": C_LCC,
        "p05_critical_at_N384": P05_CRITICAL(384),
    },
    "scan_results": scan_results,
    "Q1_first_N_p95_below_T_RAND": q1_N,
    "Q2_first_N_p95_below_T_BORDER": q2_N,
    "Q3_first_N_p95_below_C_LCC": q3_N,
    "Q4_tier_breakdown_at_N384": {
        "TRUE_RANDOMNESS_below_T_RAND": n384_result['frac_below_T_RAND'],
        "T_RAND_to_T_BORDER": n384_result['frac_below_T_BORDER'] - n384_result['frac_below_T_RAND'],
        "T_BORDER_to_C_LCC": n384_result['frac_below_C_LCC'] - n384_result['frac_below_T_BORDER'],
        "SIGNAL_above_C_LCC": 1 - n384_result['frac_below_C_LCC'],
    },
    "Q5_cross_source": cross_results,
    "Q6_pass49_observations_classified": {
        label: {
            "abs_R": val,
            "tier": ("TRUE-RANDOMNESS" if val < T_RAND else
                     "T_RAND-to-T_BORDER" if val < T_BORDER else
                     "T_BORDER-to-C_LCC" if val < C_LCC else
                     "SIGNAL")
        }
        for label, val in pass49_obs.items()
    },
    "n_draws_per_cell": N_DRAWS,
}
Path(__file__).parent.joinpath("results.json").write_text(json.dumps(out, indent=2))
print()
print("Results written to analyses/pass51_d51_rnd3_dual_threshold_empirical/results.json")
