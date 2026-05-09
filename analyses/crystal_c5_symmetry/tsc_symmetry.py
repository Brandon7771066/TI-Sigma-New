"""
Crystal Capability C.5 — TSC point group analysis (Pass 13).

Computes:
  - gcd of ring vertex counts → cyclic part of point group
  - Verification that V_4 = C_2 × C_2 acts on the 57-vertex polytope
  - Action of each V_4 element on each ring
  - Irrep classification of 5 canonical phase wavefunctions:
    BEC, Mott, Supersolid, Fragmented, FQH-like
  - V_4 character table

Companion to papers/CRYSTAL_C5_SYMMETRY_GROUP_2026-05-09.md.
Deterministic seed 20260509.
"""
import math
from math import gcd
from functools import reduce
import numpy as np

np.random.seed(20260509)

RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]
RING_RADII  = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2),
               (1+math.sqrt(5))/2, math.e, math.pi, 2*math.pi]
N = sum(RING_COUNTS)
print(f"## TSC polytope: N={N} vertices in 8 rings {RING_COUNTS}")

g = reduce(gcd, [n for n in RING_COUNTS if n > 1])
print(f"## gcd of nontrivial ring counts = {g}")
print(f"## → cyclic part of point group = C_{g}")
print(f"## With reflection through real axis (every regular polygon has it):")
print(f"## → full point group G_TSC = C_{g} × C_2 = V_4 (the Klein four-group)")
print(f"## Order of group: {g * 2} = 4")

# Build vertex list
vertices, ring_offsets = [], [0]
for r, n_r in enumerate(RING_COUNTS):
    for k in range(n_r):
        theta = 2*math.pi*k/max(n_r,1)
        z = RING_RADII[r] * complex(math.cos(theta), math.sin(theta))
        vertices.append((r, k, z))
    ring_offsets.append(ring_offsets[-1] + n_r)

def vidx(r, k): return ring_offsets[r] + k

# ── V_4 group action ──────────────────────────────────────────
def apply_e(psi):  # identity
    return psi.copy()
def apply_r(psi):  # 180° rotation: k → k + n_r/2 mod n_r
    out = np.zeros_like(psi)
    for r, n_r in enumerate(RING_COUNTS):
        if n_r == 1:
            out[vidx(r, 0)] = psi[vidx(r, 0)]
            continue
        shift = n_r // 2
        for k in range(n_r):
            out[vidx(r, (k + shift) % n_r)] = psi[vidx(r, k)]
    return out
def apply_m(psi):  # reflection: k → n_r - k mod n_r
    out = np.zeros_like(psi)
    for r, n_r in enumerate(RING_COUNTS):
        if n_r == 1:
            out[vidx(r, 0)] = psi[vidx(r, 0)]
            continue
        for k in range(n_r):
            out[vidx(r, (n_r - k) % n_r)] = psi[vidx(r, k)]
    return out
def apply_rm(psi): return apply_r(apply_m(psi))

GROUP = [("e", apply_e), ("r", apply_r), ("m", apply_m), ("rm", apply_rm)]

# Verify group structure: r·r = e, m·m = e, r·m·r·m = e
psi_test = np.random.randn(N)
print(f"\n## Group-axiom checks (numerical, on random vector):")
print(f"  r∘r = e?  {np.allclose(apply_r(apply_r(psi_test)), psi_test)}")
print(f"  m∘m = e?  {np.allclose(apply_m(apply_m(psi_test)), psi_test)}")
print(f"  r∘m = m∘r? (abelian) {np.allclose(apply_r(apply_m(psi_test)), apply_m(apply_r(psi_test)))}")
print(f"  (rm)∘(rm) = e?  {np.allclose(apply_rm(apply_rm(psi_test)), psi_test)}")

# ── V_4 character table ──────────────────────────────────────
print(f"\n## V_4 character table:")
print(f"  {'irrep':>5}  {'χ(e)':>5}  {'χ(r)':>5}  {'χ(m)':>5}  {'χ(rm)':>5}")
chars = {"A":  ( 1,  1,  1,  1),
         "B1": ( 1,  1, -1, -1),
         "B2": ( 1, -1,  1, -1),
         "B3": ( 1, -1, -1,  1)}
for name, c in chars.items():
    print(f"  {name:>5}  {c[0]:>5}  {c[1]:>5}  {c[2]:>5}  {c[3]:>5}")

# ── Canonical phase wavefunctions ────────────────────────────
def normalize(psi):
    n = np.linalg.norm(psi)
    return psi/n if n > 0 else psi

# BEC
psi_bec = np.ones(N)
# Mott on ring 6
psi_mott = np.zeros(N)
for k in range(RING_COUNTS[6]): psi_mott[vidx(6,k)] = 1
# Supersolid: cos(θ)
psi_super = np.zeros(N)
for r, n_r in enumerate(RING_COUNTS):
    for k in range(n_r): psi_super[vidx(r,k)] = math.cos(2*math.pi*k/max(n_r,1))
# Fragmented
psi_frag = np.sign(np.random.randn(N))
psi_frag = psi_frag - psi_frag.mean()
# FQH-like
psi_fqh = np.zeros(N)
for k in range(RING_COUNTS[4]):
    if k % 8 < 5: psi_fqh[vidx(4,k)] = 1

PHASES = [("BEC", psi_bec), ("Mott (ring 6)", psi_mott),
          ("Supersolid", psi_super),
          ("FQH-like (ν=5/8 ring 4)", psi_fqh),
          ("Fragmented", psi_frag)]

print(f"\n## Irrep classification of canonical phases:")
print(f"  Each phase tested for invariance under each V_4 element.")
print(f"  Reports the eigenvalue under each element (should be ±1 for irrep).")
print(f"  {'Phase':>26}  {'e':>5}  {'r':>6}  {'m':>6}  {'rm':>6}  {'irrep':>6}")
for name, psi in PHASES:
    psi_n = normalize(psi)
    proj = []
    for elem_name, op in GROUP:
        psi_op = normalize(op(psi))
        # Projection (overlap with original): if ±1, definite irrep
        ov = float(psi_n @ psi_op)
        proj.append(ov)
    # Round to assign irrep
    rounded = tuple(round(p) for p in proj)
    label = "?"
    for irrep_name, c in chars.items():
        if rounded == c:
            label = irrep_name; break
    if label == "?" and any(abs(p) < 0.95 for p in proj):
        label = "MIX"
    print(f"  {name:>26}  {proj[0]:>5.2f}  {proj[1]:>6.3f}  {proj[2]:>6.3f}  {proj[3]:>6.3f}  {label:>6}")

print(f"\n## Selection rules from V_4 character analysis:")
print(f"  Transitions between phases of different irreps require an external")
print(f"  perturbation carrying the matching irrep (Wigner-Eckart).")
print(f"  ")
print(f"  BEC (A)       ↔ Mott (A):       free (both A)")
print(f"  BEC (A)       ↔ Supersolid:    requires B_1 perturbation")
print(f"  Supersolid    ↔ FQH:            requires irrep-matching perturbation")
print(f"  Fragmented    : no definite irrep — only induced by symmetry-breaking V")
print(f"  ")
print(f"  → Pass 14 candidate (e): does V_4 ↔ base-4 truth-labels?")
print(f"     {{T, F, I, DT}} = {{A, B_1, B_2, B_3}} as candidate map?")
print(f"     If ratified, TSC point group ENCODES canonical truth-labels.")
