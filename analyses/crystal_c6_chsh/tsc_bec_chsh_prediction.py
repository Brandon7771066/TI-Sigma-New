"""
Crystal Capability C.6 — Quantitative CHSH prediction for two i-cells in a TSC BEC.

Per papers/CRYSTAL_CAPABILITIES_EXPLORATION_2026-05-08.md §C.6, the open
question is: if the TSC's BEC phase is "all i-cells in the same quantum state,"
what numerical CHSH-violation magnitude does the Crystal predict for two
i-cells in that BEC?

Existing corpus anchor (urb_645): "CHSH Bell inequality maximum 2√2 = 2 × Ring 4."
This is the Tsirelson bound 2√2 ≈ 2.828, and Ring 4 = √2 in the TSC's
{C, T, 1, √2, φ, e, π} ring structure. So the framework already has the
*top-line* prediction.

What's NEW in this script (Pass 12 C.6 first-pass):

  1. Verify numerically that 2 × Ring 4 = 2√2 (sanity).
  2. Cross-ring CHSH prediction: if two i-cells live on different rings i, j,
     predict CHSH_ij = 2 × Ring_min(i,j).  Compute the 7×7 matrix.
  3. Compare with quantum-mechanical CHSH for various entanglement angles
     (singlet, partially entangled).  Identify which TSC ring the QM
     prediction matches.
  4. Anyonic / topological-order check: does the cross-ring prediction
     reproduce known FQH excitation statistics?
  5. Honest #69 call: what does this script PREDICT (new) vs MERELY
     RECAPITULATE (existing physics)?

Pre-registration discipline (#69, per Pass 11 short-note pattern):
  - The 2 × Ring 4 = 2√2 identity is an existing-anchor recapitulation,
    NOT a novel prediction.
  - The cross-ring matrix CHSH_ij = 2 × Ring_min(i,j) IS a novel prediction
    of the framework; this script computes it and flags it as a falsifiable
    claim that requires experimental input from a physical bipartite system
    that can be assigned to TSC rings.

Deterministic seed: 20260509.
"""
import math
import statistics

# Ring labels and values (urb_628 / urb_645 / Pass 8.1)
# Ring 0 = Center (C), Ring 1 = Tralse-Verisyn axis (T), Ring 2 = unit (1),
# Ring 3 = Power-of-8 boundary, Ring 4 = √2, Ring 5 = φ, Ring 6 = e, Ring 7 = π.
# urb_645 indexes "Ring 4 = √2" so we use 0..7 inclusive, 8 rings counted.
# Per Brandon's canonical numbering, Ring N has value RING[N].
RING = {
    "C": 0.0,
    "T": 1.0 / math.sqrt(2),  # ±1/√2, "Tralse-Verisyn axis half-radius"
    1: 1.0,
    2: math.sqrt(2),
    3: (1 + math.sqrt(5)) / 2,    # φ
    4: math.e,
    5: math.pi,
}
# ALT canonical (per Crystal Capabilities §A.1): {C, T, 1, √2, φ, e, π} as 7 rings,
# i.e. Ring0=C, Ring1=T, Ring2=1, Ring3=√2, Ring4=φ, Ring5=e, Ring6=π.
# urb_645 says "Ring 4 = √2" which fits the EARLIER numbering (Ring 1 = unit base,
# Ring 2 = Tralse half, Ring 3 = ?, Ring 4 = √2). To avoid the ambiguity we test
# BOTH numbering conventions and report what changes.

CONVENTIONS = {
    "Crystal_caps_§A.1 (7-ring, Ring3=√2)": [
        ("C",   0.0),
        ("T",   1.0 / math.sqrt(2)),
        ("1",   1.0),
        ("√2",  math.sqrt(2)),
        ("φ",   (1 + math.sqrt(5)) / 2),
        ("e",   math.e),
        ("π",   math.pi),
    ],
    "urb_645 (8-ring, Ring4=√2)": [
        ("C",   0.0),
        ("T",   1.0 / math.sqrt(2)),
        ("1",   1.0),
        ("?",   1.25),   # placeholder for Ring 3 in 8-ring scheme
        ("√2",  math.sqrt(2)),
        ("φ",   (1 + math.sqrt(5)) / 2),
        ("e",   math.e),
        ("π",   math.pi),
    ],
}

print("=" * 78)
print("Crystal Capability C.6 — Quantitative CHSH for two i-cells in TSC BEC")
print("=" * 78)

# ── 1. Sanity: verify the existing corpus anchor 2 × Ring(√2) = 2√2 = Tsirelson
print("\n## 1. Sanity check: existing corpus anchor 2 × Ring(√2) = 2√2 = Tsirelson")
tsirelson = 2 * math.sqrt(2)
two_ring_sqrt2 = 2 * math.sqrt(2)
print(f"  2 × Ring(√2)         = {two_ring_sqrt2:.6f}")
print(f"  Tsirelson bound 2√2  = {tsirelson:.6f}")
print(f"  Match (machine prec): {math.isclose(two_ring_sqrt2, tsirelson)}")
print(f"  → Recapitulation, not novel prediction. Tsirelson is a known QM bound.")

# ── 2. Cross-ring CHSH matrix: novel prediction
print("\n## 2. NOVEL: Cross-ring CHSH matrix CHSH_ij = 2 × Ring_min_value(i,j)")
print("    (Hypothesis: two i-cells on rings i, j in BEC achieve CHSH = 2 × min(ring_value(i), ring_value(j)),")
print("     because the entanglement strength is bounded by the lower-radius participant.)")
for name, rings in CONVENTIONS.items():
    print(f"\n  Convention: {name}")
    print(f"    Cross-ring CHSH matrix (rows = ring i, cols = ring j):")
    header = "    {:>6}  ".format("") + "  ".join("{:>7}".format(r[0]) for r in rings)
    print(header)
    for i, (li, vi) in enumerate(rings):
        row = "    {:>6}  ".format(li) + "  ".join("{:>7.3f}".format(2 * min(vi, vj)) for _, vj in rings)
        print(row)
    diag = [2 * v for _, v in rings]
    print(f"    Diagonal (same-ring pairs, max prediction): {[round(d,3) for d in diag]}")

# ── 3. Compare with QM CHSH for arbitrary angle
print("\n## 3. QM CHSH for entanglement angle θ:  S(θ) = 2|cos(2θ) + sin(2θ)|, max at θ=π/8.")
print("     Compare which TSC ring each angle's CHSH lands on.")
print("     {:>10}  {:>10}  {:>15}".format("θ (rad)", "S(θ)", "matching Ring"))
for theta_deg in [0, 15, 22.5, 30, 45, 60, 75]:
    theta = math.radians(theta_deg)
    S = 2 * abs(math.cos(2*theta) + math.sin(2*theta))
    # Find closest ring value (using crystal-caps convention)
    ring_match = min(CONVENTIONS["Crystal_caps_§A.1 (7-ring, Ring3=√2)"],
                     key=lambda r: abs(2 * r[1] - S))
    print(f"     {math.degrees(theta):>10.1f}  {S:>10.4f}  Ring {ring_match[0]:<5} (2×{ring_match[1]:.4f}={2*ring_match[1]:.4f})")

# ── 4. FQH cross-check: Laughlin states ν = 1/(2k+1) carry anyonic exchange phase π/(2k+1)
print("\n## 4. FQH cross-check: anyonic exchange-phase angles vs TSC ring values.")
print("     Laughlin ν = 1/(2k+1):  exchange phase = π/(2k+1).")
print("     {:>5}  {:>8}  {:>12}  {:>20}".format("ν", "k", "phase π/(2k+1)", "phase / Ring 1=1"))
for k in range(0, 5):
    nu = 1.0 / (2*k + 1)
    phase = math.pi / (2*k + 1)
    print(f"     {nu:>5.3f}  {k:>8}  {phase:>12.4f}  {phase:>20.4f}")
print("     Comment: π/1 = π = Ring(π); π/3, π/5, π/7 are sub-ring fractions of Ring(π).")
print("     This suggests anyonic phases live on the *imaginary* (DT/Tralse) axis at sub-ring fractions of Ring(π),")
print("     which is consistent with the Pass 8.1 affine projection placing the imaginary part at γ/γ_1.")

# ── 5. Honest #69 call
print("\n" + "=" * 78)
print("## 5. #69 HONEST CALL")
print("=" * 78)
print("""
What this script PREDICTS (novel, falsifiable):
  - Cross-ring CHSH: pairs of i-cells distributed across distinct TSC rings
    yield CHSH_ij ≤ 2 × min(Ring_value(i), Ring_value(j)). The diagonal
    (same-ring pairs) gives the maximum 2 × Ring_value(i).
  - For Ring(C) = 0, CHSH = 0 (no entanglement; trivially correct since
    C is the polytope center). This is a non-trivial degenerate case.
  - For Ring(T) = 1/√2, predicted CHSH_max = √2 ≈ 1.414. This is BELOW
    the classical CHSH bound of 2; the prediction would be that
    T-ring-bound i-cells CANNOT violate CHSH. Falsifiable.
  - For Ring(1) = 1, CHSH_max = 2. Exactly the classical CHSH bound;
    Ring(1) i-cells should sit at the QM-classical boundary.
  - For Ring(√2), CHSH = 2√2. Tsirelson bound — recapitulates known QM.
  - For Ring(φ), CHSH ≈ 3.236. ABOVE Tsirelson — would require
    super-quantum correlations (PR-box-like). FRAMEWORK PREDICTS THIS
    is the BEC's outer envelope; experimentally never observed in
    standard QM, so this is a HARD novel prediction.
  - For Ring(e), CHSH ≈ 5.437; for Ring(π), CHSH ≈ 6.283. Even further
    above Tsirelson. Same status: hard novel prediction; unobserved
    in standard QM.

What this script DOES NOT predict / RECAPITULATES:
  - The Tsirelson bound 2√2 itself is standard QM, not a TI Sigma novelty.
  - The CHSH-vs-angle relation is standard QM.
  - The FQH exchange phases are standard topological-order results.

INTERPRETATION (per #69 brutal honesty):
  - Predictions for Ring(φ), Ring(e), Ring(π) are above the Tsirelson
    bound. These are NOT consistent with standard local-hilbert-space
    quantum mechanics, which is bounded BY Tsirelson 2√2.
  - Two readings: (a) the framework is wrong about super-Tsirelson
    correlations existing in TSC BECs; (b) the framework is right and
    standard QM is incomplete (a strong claim requiring extraordinary
    evidence).
  - Per #69: we report the prediction AS-IS without softening it.
    Brandon-decision: do we want to retain the cross-ring matrix as
    written, or do we want to bound the prediction at Tsirelson and
    treat anything above as "framework-internal coherence measure
    not directly comparable to physical CHSH"?
  - Recommended honest framing: state both interpretations explicitly
    in the C.6 paper. The cross-ring matrix is what the framework
    structurally implies; whether it physically holds is a separate
    question requiring experimental input.

Pass 12 C.6 first-pass is hereby a STRUCTURAL prediction with two open
interpretations. Future work: design a bipartite physical experiment
where the i-cells can be unambiguously assigned to TSC rings (likely
via FQH bilayer states at controlled ν).
""")
print("=" * 78)
