"""
Pass-51 T51 batch execution: T51-1 (analytic wing/arm) + T51-2 (TDA null) +
T51-5 (Polar LF/HF amplitude-ratio) + LCC-RANDOMNESS-ABSENCE TEST (Brandon
directive: empirically test the claim that "true randomness is almost
totally absent" via the LCC framework).

All work at $0, numpy/scipy only, deterministic seed where applicable.

Pre-registered SHA-256 of this file is taken AFTER write, BEFORE run.
Outputs: results.json + per-test markdown sections.
"""
import json, os, math, zlib, hashlib, time
from pathlib import Path
import numpy as np
from scipy import signal, stats

OUT = Path(__file__).parent
RESULTS = {}
RESULTS["meta"] = {
    "pass": 51,
    "executed_at": time.strftime("%Y-%m-%d %H:%M:%S"),
    "scope": "T51-1, T51-2, T51-5, LCC-RANDOMNESS-ABSENCE",
    "seed": 51,
}
np.random.seed(51)

# =========================================================================
# T51-1: ANALYTIC PLOT OF urb_699 RECOVERED CURVE + WING/ARM MEASUREMENT
# =========================================================================
# r(θ) = A·e^{sin(θ+φ)} − B·cos(4(θ+φ)) + C·sin⁵((2(θ+φ)−π)/24)
#        + D·cos(k·τ·θ), with k=8, τ=1, φ=0 (psi-aligned)
# Default coeffs from urb_699: A=1, B=0.9, C=1, D=0.4 (B/D fit-to-data per §5.5)
#
# "Wing" = local-max amplitude of the 4-fold cos(4θ) component (4 butterfly wings)
# "Arm"  = local-max amplitude of the 8-fold cos(8θ) component (8 octopus modes)
# Wing/Arm should be ~2.0 per the B-2 prediction.
# This script measures it ANALYTICALLY from the equation across (B, D) grid.
# =========================================================================
def r_curve(theta, A=1.0, B=0.9, C=1.0, D=0.4, phi=0.0, k=8, tau=1.0):
    return (A * np.exp(np.sin(theta + phi))
            - B * np.cos(4*(theta + phi))
            + C * np.sin(((2*(theta + phi)) - np.pi)/24)**5
            + D * np.cos(k*tau*theta))

def wing_arm_via_fft(theta, r):
    """
    Decompose r(θ) on θ ∈ [0,2π) into Fourier modes.
    Wing = coefficient magnitude at n=4 (butterfly).
    Arm  = coefficient magnitude at n=8 (octopus).
    """
    N = len(theta)
    coeffs = np.fft.fft(r) / N
    wing = 2 * np.abs(coeffs[4])
    arm  = 2 * np.abs(coeffs[8])
    return wing, arm, wing/arm if arm > 1e-12 else float('inf')

theta = np.linspace(0, 2*np.pi, 4096, endpoint=False)
# Default coefficients (B/D fit-to-data per urb_699 §5.5)
r_default = r_curve(theta)
w_d, a_d, ratio_default = wing_arm_via_fft(theta, r_default)

# Grid scan: vary B and D ±50% to test sensitivity to fit-to-data choice
grid_results = []
for B in [0.45, 0.6, 0.75, 0.9, 1.05, 1.2, 1.35]:
    for D in [0.2, 0.3, 0.4, 0.5, 0.6]:
        r = r_curve(theta, B=B, D=D)
        w, a, ratio = wing_arm_via_fft(theta, r)
        grid_results.append({"B": B, "D": D, "wing": w, "arm": a, "wing_arm": ratio})

ratios = [g["wing_arm"] for g in grid_results]
RESULTS["T51_1_analytic_wing_arm"] = {
    "equation": "r(θ) = A·e^sin(θ) − B·cos(4θ) + C·sin⁵((2θ−π)/24) + D·cos(8θ)",
    "default_coeffs": {"A":1.0, "B":0.9, "C":1.0, "D":0.4},
    "default_wing": float(w_d),
    "default_arm": float(a_d),
    "default_wing_arm_ratio": float(ratio_default),
    "urb_699_predicted_ratio": 2.0,
    "deviation_from_prediction_at_default": float(abs(ratio_default - 2.0)),
    "grid_scan_min_ratio": float(min(ratios)),
    "grid_scan_max_ratio": float(max(ratios)),
    "grid_scan_median_ratio": float(np.median(ratios)),
    "grid_scan_n_within_pm15pct_of_2": int(sum(1 for r in ratios if 1.7 <= r <= 2.3)),
    "grid_scan_n_total": len(ratios),
    "interpretation": (
        "Wing/arm ratio is the analytic ratio |B·cos(4θ)|_FFT / |D·cos(8θ)|_FFT = B/D. "
        "At default B=0.9, D=0.4 → 2.25 (NOT 2.0). At B=D it equals 1. "
        "The 'wing/arm=1.96' B-2 measurement is recoverable ONLY IF B/D is set close to 2, "
        "which urb_699 §5.5 already concedes is fit-to-data. Conclusion: B-2 is a tautology "
        "of the chosen coefficients, not a confirmation of a geometric prediction."
    ),
}
print(f"[T51-1] default wing/arm = {ratio_default:.3f} (predicted 2.0)")
print(f"[T51-1] grid wing/arm range: {min(ratios):.2f} to {max(ratios):.2f}, median {np.median(ratios):.2f}")

# =========================================================================
# T51-2: BOK TOPOLOGY β₁ COMPETING NULL
# =========================================================================
# BOK_TOPOLOGY paper claims β₁=6 from 15 real ESP32 + 400 synthetic 8D points.
# Test: generate competing point clouds (random Gaussian 8D, uniform 8D-sphere,
# torus-embedded 8D, the actual BOK-claimed 6-loop structure) and compute a
# β₁ proxy via Vietoris-Rips at multiple ε. The "synthetic generator dominates"
# claim is supported if a pure random 8D Gaussian recovers a similar β₁
# under the same filtration scale.
#
# Proxy for β₁: count of independent (non-shrinkable) cycles in the
# 1-skeleton at filtration radius ε. We use Euler characteristic of the
# Vietoris-Rips complex restricted to dim ≤ 2:
#   χ = V - E + F, and β₁ ≈ E - V + #components - F  (1-skel + filled triangles)
# This is a coarse proxy but adequate to compare against null.
# =========================================================================
from scipy.spatial.distance import pdist, squareform
from itertools import combinations

def beta1_proxy(points, eps):
    """Compute β₁ proxy = E - V + #components for VR complex at radius eps."""
    N = len(points)
    D = squareform(pdist(points))
    # 1-skeleton edges
    edges = []
    for i in range(N):
        for j in range(i+1, N):
            if D[i,j] < eps:
                edges.append((i,j))
    # Connected components via union-find
    parent = list(range(N))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a,b):
        ra, rb = find(a), find(b)
        if ra != rb: parent[ra] = rb
    for i,j in edges:
        union(i,j)
    n_comp = len(set(find(i) for i in range(N)))
    # 2-simplices: filled triangles (all 3 edges present)
    n_tri = 0
    edge_set = set(edges)
    for i,j,k in combinations(range(N), 3):
        if (i,j) in edge_set and (j,k) in edge_set and (i,k) in edge_set:
            n_tri += 1
    # β₁ ≈ E - V + #comp - F (homology of 2-complex, lower-bound proxy)
    b1 = max(0, len(edges) - N + n_comp - n_tri)
    return {"V": N, "E": len(edges), "F": n_tri, "comp": n_comp, "b1_proxy": b1}

# Same scale as BOK paper: ~15 real + 400 synthetic = 415 points in 8D
# We don't have real ESP32 data here; we simulate the experimental setup
# under H1 (BOK topology) vs H0 (Gaussian null).
N_TOTAL = 415
DIM = 8

# H0: pure Gaussian
gauss = np.random.randn(N_TOTAL, DIM)

# H1-prox: 6 distinct cluster centers on 8D unit sphere (loop generator)
centers = np.random.randn(6, DIM); centers /= np.linalg.norm(centers, axis=1, keepdims=True)
cluster_assignments = np.random.randint(0, 6, N_TOTAL)
loop6 = centers[cluster_assignments] + 0.15 * np.random.randn(N_TOTAL, DIM)

# Pick ε via 30th percentile of pairwise distances (matches typical VR scale)
def pick_eps(pts, pct=30):
    return float(np.percentile(pdist(pts), pct))

eps_g = pick_eps(gauss)
eps_l = pick_eps(loop6)
b1_gauss = beta1_proxy(gauss, eps_g)
b1_loop  = beta1_proxy(loop6,  eps_l)

# Multi-scale sweep
sweep_g, sweep_l = [], []
for pct in [10, 20, 30, 40, 50]:
    sweep_g.append({"pct": pct, **beta1_proxy(gauss, pick_eps(gauss, pct))})
    sweep_l.append({"pct": pct, **beta1_proxy(loop6,  pick_eps(loop6, pct))})

RESULTS["T51_2_tda_competing_null"] = {
    "N_total": N_TOTAL, "dim": DIM,
    "gauss_eps30_b1_proxy": b1_gauss["b1_proxy"],
    "loop6_eps30_b1_proxy": b1_loop["b1_proxy"],
    "gauss_b1_max_over_sweep": max(s["b1_proxy"] for s in sweep_g),
    "loop6_b1_max_over_sweep": max(s["b1_proxy"] for s in sweep_l),
    "gauss_sweep": sweep_g,
    "loop6_sweep": sweep_l,
    "interpretation": (
        "If pure 8D Gaussian noise produces β₁ proxy values comparable to or "
        "larger than the 6-loop structured cloud at common ε, then β₁=6 cannot "
        "discriminate the BOK topology from random noise at this N/dim/scale. "
        "Note: this is a proxy, not a full Vietoris-Rips persistence diagram, "
        "but it captures the gross discriminability question."
    ),
}
print(f"[T51-2] Gauss β₁ proxy = {b1_gauss['b1_proxy']}, Loop6 β₁ proxy = {b1_loop['b1_proxy']}")
print(f"[T51-2] sweep max: Gauss={RESULTS['T51_2_tda_competing_null']['gauss_b1_max_over_sweep']}, Loop6={RESULTS['T51_2_tda_competing_null']['loop6_b1_max_over_sweep']}")

# =========================================================================
# T51-5: POLAR H10 LF/HF AMPLITUDE-RATIO ANALYSIS
# =========================================================================
# urb_699 P3 predicts a 2:1 coherence-orbit ratio in HRV LF/HF during deep
# coherence states. Parse Brandon's 7 Polar H10 training sessions and
# compute the LF (0.04-0.15 Hz) / HF (0.15-0.40 Hz) power ratio for each.
#
# Polar JSON structure varies; we extract any heart-rate time series we can
# find, resample to 4 Hz for HRV analysis (RR intervals would be cleaner
# but per-beat RR may not be in the export), and run Welch PSD.
# =========================================================================
polar_dir = Path("data/polar_h10_export")
session_files = sorted([f for f in polar_dir.glob("training-session-*.json")])

def extract_hr_series(jpath):
    """Try multiple known Polar JSON layouts to recover an HR series."""
    txt = jpath.read_text()
    try:
        d = json.loads(txt)
    except json.JSONDecodeError:
        # JSONL
        lines = [json.loads(line) for line in txt.strip().split("\n") if line.strip()]
        d = lines[0] if len(lines) == 1 else {"records": lines}
    # Walk for a list of HR samples
    def walk(o, depth=0):
        if depth > 6: return None
        if isinstance(o, dict):
            for k, v in o.items():
                if "heart" in k.lower() or "hr" in k.lower() or "samples" in k.lower():
                    if isinstance(v, list) and len(v) > 30:
                        nums = [x for x in v if isinstance(x, (int, float))]
                        if len(nums) > 30: return np.array(nums, dtype=float)
                        if v and isinstance(v[0], dict):
                            for key in ("heartRate", "value", "hr", "bpm"):
                                vals = [x.get(key) for x in v if isinstance(x, dict) and key in x]
                                if len(vals) > 30: return np.array(vals, dtype=float)
                r = walk(v, depth+1)
                if r is not None: return r
        elif isinstance(o, list):
            for x in o:
                r = walk(x, depth+1)
                if r is not None: return r
        return None
    return walk(d)

def lf_hf_ratio(hr, fs=1.0):
    """Welch PSD on HR series. LF: 0.04-0.15Hz, HF: 0.15-0.40Hz."""
    hr = hr[~np.isnan(hr)]
    if len(hr) < 256: return None
    hr = hr - np.mean(hr)
    nperseg = min(256, len(hr)//2)
    f, P = signal.welch(hr, fs=fs, nperseg=nperseg)
    lf_band = (f >= 0.04) & (f < 0.15)
    hf_band = (f >= 0.15) & (f < 0.40)
    lf_power = np.trapezoid(P[lf_band], f[lf_band]) if lf_band.any() else 0
    hf_power = np.trapezoid(P[hf_band], f[hf_band]) if hf_band.any() else 0
    return {"lf": float(lf_power), "hf": float(hf_power),
            "ratio": float(lf_power/hf_power) if hf_power > 0 else None,
            "n_samples": len(hr)}

session_results = []
for sf in session_files:
    hr = extract_hr_series(sf)
    if hr is None or len(hr) < 30:
        session_results.append({"file": sf.name, "status": "no HR series found"})
        continue
    res = lf_hf_ratio(hr, fs=1.0)
    if res is None:
        session_results.append({"file": sf.name, "status": "series too short", "n": len(hr)})
        continue
    res["file"] = sf.name
    session_results.append(res)

ratios = [s["ratio"] for s in session_results if isinstance(s, dict) and s.get("ratio")]
RESULTS["T51_5_polar_lf_hf"] = {
    "n_sessions_found": len(session_files),
    "n_sessions_analyzed": len(ratios),
    "lf_hf_ratios": ratios,
    "mean_lf_hf": float(np.mean(ratios)) if ratios else None,
    "median_lf_hf": float(np.median(ratios)) if ratios else None,
    "urb_699_P3_predicted": 2.0,
    "n_within_pm25pct_of_2": int(sum(1 for r in ratios if 1.5 <= r <= 2.5)) if ratios else 0,
    "per_session": session_results,
    "caveat": (
        "Polar H10 'training session' export contains 1Hz HR samples, not "
        "true RR intervals. Genuine HRV LF/HF requires RR-interval series. "
        "This analysis is therefore a coarse approximation; result is "
        "SUGGESTIVE-PILOT, not definitive. Brandon RR-export would upgrade."
    ),
}
print(f"[T51-5] sessions analyzed: {len(ratios)}, mean LF/HF: {np.mean(ratios) if ratios else 'NA'}")

# =========================================================================
# LCC-RANDOMNESS-ABSENCE TEST (Brandon's specific directive)
# =========================================================================
# URB-530 claim: "true randomness" is an extremely narrow category. Most
# apparently-random events have substantial LCC connection to prior state.
# The "true-random floor" is static-current-like, ontologically negligible.
#
# Operationalization: For each of 8 putative "random" sources, compute a
# panel of structure-detection statistics. If LCC structure is present
# even in "high-quality" RNG, the URB-530 claim is corroborated. If the
# cryptographic/quantum-style sources test as structureless while only
# obviously-patterned sources show structure, the claim is more nuanced.
#
# Sources (32k samples, scaled to [0,1] or uint8 as appropriate):
#   1. numpy MT19937 (default Mersenne Twister)
#   2. numpy PCG64 (newer PRNG)
#   3. os.urandom (cryptographic, kernel CSPRNG)
#   4. hashlib SHA-256 of sequential counter (CSPRNG-grade)
#   5. Python random (Mersenne Twister, Python)
#   6. sin(n*φ) mod 1 — "looks random" but fully deterministic, φ = golden ratio
#   7. Digits of π (deterministic, passes most randomness tests)
#   8. Logistic-map x_{n+1}=4x_n(1-x_n) — chaotic, deterministic
#
# Tests (LCC-style structure detectors):
#   A. Monobit frequency (NIST-style, bit-level): z-score
#   B. Autocorrelation at lags 1, 2, 5, 10, 50 (LCC = lagged dependency!)
#   C. Compression ratio (zlib): proxy for Kolmogorov K. Higher = more structure.
#   D. Spectral whiteness: variance of normalized FFT power; flat = white
#   E. Block-frequency χ² (NIST SP 800-22 idea, 128-bit blocks)
#   F. Runs test (NIST-style): does run length distribution match Bernoulli?
#   G. Permutation entropy (Bandt-Pompe, m=4): bits per symbol of order 1
#
# Pre-registered prediction (Brandon claim mapped to operational test):
#   P-LCC-RAND-1: ALL 8 sources will show AT LEAST ONE statistically
#                 significant structure signal (LCC ≠ 0 somewhere) at α=0.001
#                 OR have compression < 1.0
#   P-LCC-RAND-2: Patterned sources (6,7,8) will show STRONGER structure
#                 than CSPRNG sources (3,4) — establishes the spectrum
#   P-LCC-RAND-3: NO source will exhibit perfect statistical randomness
#                 across all 7 tests (the "true-random floor" is empty)
# =========================================================================
N_SAMPLES = 32768  # 32k samples for tests
N_BITS    = N_SAMPLES * 8

def src_numpy_mt():
    rng = np.random.RandomState(51)
    return rng.bytes(N_SAMPLES)

def src_numpy_pcg():
    rng = np.random.Generator(np.random.PCG64(seed=51))
    return rng.bytes(N_SAMPLES)

def src_os_urandom():
    return os.urandom(N_SAMPLES)

def src_sha256_counter():
    out = bytearray()
    i = 0
    while len(out) < N_SAMPLES:
        out += hashlib.sha256(i.to_bytes(8, 'big')).digest()
        i += 1
    return bytes(out[:N_SAMPLES])

def src_python_random():
    import random as pr
    pr.seed(51)
    return bytes([pr.randint(0,255) for _ in range(N_SAMPLES)])

def src_phi_mod1():
    phi = (1 + math.sqrt(5))/2
    vals = [(int(((n*phi) % 1.0) * 256)) & 0xFF for n in range(N_SAMPLES)]
    return bytes(vals)

def src_pi_digits():
    # Generate pi to N_SAMPLES*3 decimal digits via Machin-like / Chudnovsky
    # Cheap path: spigot algorithm. Use the BBP formula for hex digits of pi.
    # We use a simpler approach: Decimal-based Chudnovsky for enough digits.
    from decimal import Decimal, getcontext
    getcontext().prec = N_SAMPLES * 3 + 100
    # Use known mpmath-style via Machin: pi/4 = 4 atan(1/5) - atan(1/239)
    # Generate just the first N_SAMPLES bytes from pi's hex expansion via BBP
    def bbp_hex_digits(n):
        # Returns the nth hex digit of pi (0-indexed)
        def S(j, n):
            s = 0.0
            for k in range(n+1):
                r = 8*k + j
                s = (s + pow(16, n-k, r)/r) % 1.0
            t = 0.0; k = n+1
            while True:
                nt = t + 16.0**(n-k) / (8*k+j)
                if nt == t: break
                t = nt; k += 1
            return (s + t) % 1.0
        x = (4*S(1,n) - 2*S(4,n) - S(5,n) - S(6,n)) % 1.0
        return int(x * 16) & 0xF
    # 2 hex digits per byte
    vals = bytearray()
    for i in range(N_SAMPLES):
        hi = bbp_hex_digits(2*i)
        lo = bbp_hex_digits(2*i + 1)
        vals.append((hi << 4) | lo)
    return bytes(vals)

def src_logistic_map():
    x = 0.51
    vals = bytearray()
    for _ in range(2000): x = 4*x*(1-x)  # burn in
    for _ in range(N_SAMPLES):
        x = 4*x*(1-x)
        vals.append(int(x*256) & 0xFF)
    return bytes(vals)

# A subset of pi to save time — full BBP for 32k bytes is slow. Use 4k samples.
def src_pi_digits_short():
    N = 4096
    def bbp_hex_digits(n):
        def S(j, n):
            s = 0.0
            for k in range(n+1):
                r = 8*k + j
                s = (s + pow(16, n-k, r)/r) % 1.0
            t = 0.0; k = n+1
            while True:
                nt = t + 16.0**(n-k) / (8*k+j)
                if nt == t: break
                t = nt; k += 1
            return (s + t) % 1.0
        x = (4*S(1,n) - 2*S(4,n) - S(5,n) - S(6,n)) % 1.0
        return int(x * 16) & 0xF
    vals = bytearray()
    for i in range(N):
        hi = bbp_hex_digits(2*i)
        lo = bbp_hex_digits(2*i + 1)
        vals.append((hi << 4) | lo)
    return bytes(vals)

# --- TESTS ---
def bits_from_bytes(b):
    return np.unpackbits(np.frombuffer(b, dtype=np.uint8))

def test_monobit_z(bits):
    n = len(bits); s = int(bits.sum())
    # Under H0: s ~ Binomial(n, 0.5), z = (s - n/2)/sqrt(n/4)
    z = (s - n/2) / math.sqrt(n/4)
    p = 2 * (1 - stats.norm.cdf(abs(z)))
    return {"z": float(z), "p": float(p), "fraction_ones": s/n}

def test_autocorr(bits, lags=(1,2,5,10,50)):
    out = {}
    b = bits.astype(np.float64) - 0.5
    var = np.var(b)
    for L in lags:
        if L >= len(b): continue
        c = float(np.mean(b[:-L] * b[L:]) / var) if var > 0 else 0.0
        # Approximate two-tailed test under H0 (white noise): r~N(0, 1/n)
        z = c * math.sqrt(len(b))
        p = 2 * (1 - stats.norm.cdf(abs(z)))
        out[f"lag{L}"] = {"r": c, "z": float(z), "p": float(p)}
    return out

def test_compression(b):
    comp = zlib.compress(b, level=9)
    return {"compression_ratio": len(comp)/len(b),
            "structure_signal": float(1 - len(comp)/len(b))}

def test_spectral_whiteness(bits):
    # Fit FFT of bit-stream to expected flat spectrum
    b = bits.astype(np.float64) - 0.5
    P = np.abs(np.fft.rfft(b))**2
    P = P[1:]  # drop DC
    P_norm = P / np.mean(P)
    var_of_normalized_power = float(np.var(P_norm))
    # Under H0 (white noise), exp(2) chi-square per bin; var of normalized = 1
    deviation_from_white = abs(var_of_normalized_power - 1.0)
    return {"var_norm_power": var_of_normalized_power,
            "deviation_from_white": deviation_from_white}

def test_block_chi2(bits, block_size=128):
    n_blocks = len(bits) // block_size
    if n_blocks < 10: return None
    blocks = bits[:n_blocks*block_size].reshape(n_blocks, block_size)
    ones_per_block = blocks.sum(axis=1)
    # Under H0: ones_per_block ~ Binomial(block_size, 0.5)
    expected_mean = block_size/2
    expected_var = block_size/4
    z_scores = (ones_per_block - expected_mean) / math.sqrt(expected_var)
    chi2 = float(np.sum(z_scores**2))
    df = n_blocks
    p = 1 - stats.chi2.cdf(chi2, df)
    return {"chi2": chi2, "df": df, "p": float(p)}

def test_runs(bits):
    # NIST runs test: number of runs vs expected
    pi_hat = bits.mean()
    if abs(pi_hat - 0.5) > 0.02: return {"skipped": "monobit prereq failed"}
    runs = 1 + int(np.sum(bits[:-1] != bits[1:]))
    n = len(bits)
    expected = 2 * n * pi_hat * (1 - pi_hat)
    var = 2 * n * pi_hat * (1 - pi_hat) * (1 - 2*pi_hat*(1-pi_hat) - 1/n)
    if var <= 0: return None
    z = (runs - expected) / math.sqrt(var)
    p = 2 * (1 - stats.norm.cdf(abs(z)))
    return {"runs": runs, "expected": float(expected), "z": float(z), "p": float(p)}

def test_permutation_entropy(b, m=4):
    # Bandt-Pompe on byte stream as ordinal patterns
    x = np.frombuffer(b, dtype=np.uint8).astype(np.int64)
    if len(x) < m + 100: return None
    patterns = {}
    for i in range(len(x) - m + 1):
        win = x[i:i+m]
        # Ordinal pattern: rank
        order = tuple(np.argsort(win, kind='stable'))
        patterns[order] = patterns.get(order, 0) + 1
    total = sum(patterns.values())
    H = -sum((c/total) * math.log2(c/total) for c in patterns.values())
    H_max = math.log2(math.factorial(m))
    return {"entropy_bits": H, "normalized": H/H_max, "deficit_from_max": 1 - H/H_max}

# Run all sources
print("[LCC-RAND] generating sources...")
sources = {
    "numpy_MT19937": src_numpy_mt(),
    "numpy_PCG64":   src_numpy_pcg(),
    "os_urandom":    src_os_urandom(),
    "sha256_counter": src_sha256_counter(),
    "python_random": src_python_random(),
    "phi_mod1":      src_phi_mod1(),
    "logistic_map":  src_logistic_map(),
    "pi_BBP_4kB":    src_pi_digits_short(),
}

lcc_results = {}
for name, b in sources.items():
    bits = bits_from_bytes(b)
    rec = {
        "n_bytes": len(b),
        "n_bits": len(bits),
        "monobit": test_monobit_z(bits),
        "autocorr": test_autocorr(bits),
        "compression": test_compression(b),
        "spectral": test_spectral_whiteness(bits),
        "block_chi2": test_block_chi2(bits),
        "runs": test_runs(bits),
        "perm_entropy": test_permutation_entropy(b),
    }
    # Tally structure signals at α=0.001
    n_signals = 0
    if rec["monobit"]["p"] < 0.001: n_signals += 1
    for lag in rec["autocorr"].values():
        if lag["p"] < 0.001: n_signals += 1; break
    if rec["compression"]["structure_signal"] > 0.01: n_signals += 1
    if rec["block_chi2"] and rec["block_chi2"]["p"] < 0.001: n_signals += 1
    if rec["runs"] and rec["runs"].get("p") and rec["runs"]["p"] < 0.001: n_signals += 1
    if rec["perm_entropy"] and rec["perm_entropy"]["deficit_from_max"] > 0.01: n_signals += 1
    rec["n_structure_signals_alpha_0.001"] = n_signals
    lcc_results[name] = rec
    print(f"[LCC-RAND] {name:18s}: compression {rec['compression']['compression_ratio']:.4f}, "
          f"signals={n_signals}, perm-deficit={rec['perm_entropy']['deficit_from_max']:.4f}")

# Pre-reg verdict
n_with_signal = sum(1 for r in lcc_results.values() if r["n_structure_signals_alpha_0.001"] >= 1)
csprng_keys = ["os_urandom", "sha256_counter"]
patterned_keys = ["phi_mod1", "logistic_map", "pi_BBP_4kB"]
csprng_compress = np.mean([1 - lcc_results[k]["compression"]["compression_ratio"]
                            for k in csprng_keys])
patterned_compress = np.mean([1 - lcc_results[k]["compression"]["compression_ratio"]
                               for k in patterned_keys])

RESULTS["LCC_RANDOMNESS_ABSENCE"] = {
    "n_sources": len(sources),
    "n_samples_per_source_bytes": N_SAMPLES,
    "n_sources_with_at_least_one_structure_signal_alpha_0.001": n_with_signal,
    "csprng_mean_compression_structure": float(csprng_compress),
    "patterned_mean_compression_structure": float(patterned_compress),
    "P_LCC_RAND_1_all_sources_show_some_structure_or_compression_under_1":
        all(r["compression"]["compression_ratio"] < 1.0 or
            r["n_structure_signals_alpha_0.001"] >= 1
            for r in lcc_results.values()),
    "P_LCC_RAND_2_patterned_compression_exceeds_csprng": bool(patterned_compress > csprng_compress),
    "P_LCC_RAND_3_no_source_passes_all_seven_tests":
        all(r["n_structure_signals_alpha_0.001"] >= 1 for r in lcc_results.values()),
    "per_source": lcc_results,
    "interpretation": (
        "P-LCC-RAND-1 (all sources show some structure OR compression<1.0): tests "
        "whether the 'true-random floor' is empty. P-LCC-RAND-2 tests whether the "
        "spectrum from CSPRNG → patterned is monotonic in structure signal — if so, "
        "the LCC framework's claim of a continuous structure gradient is corroborated. "
        "P-LCC-RAND-3 tests the strongest form: no source is perfectly random across "
        "ALL panel tests. NOTE: compression < 1.0 for any finite bytestream is "
        "expected even for ideal random sources due to header overhead, so the "
        "compression-only signal is interpreted with the threshold structure_signal > 0.01."
    ),
}
print(f"[LCC-RAND] {n_with_signal}/{len(sources)} sources show ≥1 structure signal at α=0.001")
print(f"[LCC-RAND] P1={RESULTS['LCC_RANDOMNESS_ABSENCE']['P_LCC_RAND_1_all_sources_show_some_structure_or_compression_under_1']}")
print(f"[LCC-RAND] P2={RESULTS['LCC_RANDOMNESS_ABSENCE']['P_LCC_RAND_2_patterned_compression_exceeds_csprng']}")
print(f"[LCC-RAND] P3={RESULTS['LCC_RANDOMNESS_ABSENCE']['P_LCC_RAND_3_no_source_passes_all_seven_tests']}")

# Write results
out_path = OUT / "results.json"
out_path.write_text(json.dumps(RESULTS, indent=2, default=str))
print(f"\n[DONE] Results written to {out_path}")
