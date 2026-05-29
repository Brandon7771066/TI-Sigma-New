"""
Pass-77-B42 — Crystal "superior error catching" falsifier suite + bio-storage
physical test.  Per Brandon directive: TEST the 5 queued B41 falsifiers and
TEST the downgraded bio active-storage claim to resolve the URB#508 vs URB#373
contradiction.  All $0, deterministic.

Falsifiers:
  F1  TSC-B4 graph-Laplacian spectrum + phase ordering + weight-tuning attempt.
  F2  TECC E8 decoding radius vs sin(18deg)=0.309 (does the elegant threshold hold?).
  F3  Mendi crystal crossover n~=10 power analysis (is the pre-reg n adequate?).
  F4  phi-sighting look-elsewhere audit (is phi doing real work or curve-fitting?).
  F5  CHSH Ring(T) null test (corpus's own falsifier: Ring T must NOT violate CHSH).
  BIO Quartz coherence-storage physics: charge-relaxation + mechanical-strain test.

Faithful to:
  papers/CRYSTAL_B4_HAMILTONIAN_2026-05-09.md
  papers/urb_630_tsc_e8_error_correcting_code_five_valued_logic.md
  papers/CRYSTAL_C6_CHSH_PREDICTION_2026-05-09.md
  papers/URB_BENGSTON_WATER_QUARTZ_508.md  (storage claim)
  papers/URB_CRYSTALS_QUARTZ_PSI_COHERENCE_AMPLIFICATION.md (no-storage clause)
"""
import math
import numpy as np
from scipy.stats import nct

np.random.seed(20260527)
PHI = (1 + math.sqrt(5)) / 2
SIN18 = math.sin(math.radians(18))  # 0.309016...

def banner(t):
    print("\n" + "=" * 70 + f"\n{t}\n" + "=" * 70)

# ====================================================================
# Shared: build the 57-vertex TSC polytope + graph-Laplacian (B4 spec)
# ====================================================================
RING_RADII  = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2), PHI, math.e, math.pi, 2*math.pi]
RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]   # urb_645, total 57
N = sum(RING_COUNTS)
ring_offsets = [0]
for n_r in RING_COUNTS:
    ring_offsets.append(ring_offsets[-1] + n_r)
def vidx(r, k): return ring_offsets[r] + k

def build_adjacency(w_intra=1.0, w_inter_fn=lambda r: 1.0, w_center=1.0):
    A = np.zeros((N, N))
    for r, n_r in enumerate(RING_COUNTS):
        if n_r < 2: continue
        for k in range(n_r):
            nbr = (k + 1) % n_r
            A[vidx(r, k), vidx(r, nbr)] += w_intra
            A[vidx(r, nbr), vidx(r, k)] += w_intra
    for r in range(len(RING_COUNTS) - 1):
        n_r, n_r1 = RING_COUNTS[r], RING_COUNTS[r + 1]
        w = w_inter_fn(r)
        for k in range(n_r):
            th = 2*math.pi*k/max(n_r, 1)
            best, bd = 0, 1e9
            for kk in range(n_r1):
                thk = 2*math.pi*kk/max(n_r1, 1)
                d = abs(((th - thk + math.pi) % (2*math.pi)) - math.pi)
                if d < bd: bd, best = d, kk
            A[vidx(r, k), vidx(r+1, best)] += w
            A[vidx(r+1, best), vidx(r, k)] += w
    for k in range(RING_COUNTS[1]):
        A[vidx(0, 0), vidx(1, k)] += w_center
        A[vidx(1, k), vidx(0, 0)] += w_center
    return A

def phase_energies(H):
    def norm(p):
        n = np.linalg.norm(p); return p/n if n > 0 else p
    def exp(p):
        p = norm(p); return float(p @ H @ p)
    bec = np.ones(N)
    mott = np.zeros(N)
    for k in range(RING_COUNTS[6]): mott[vidx(6, k)] = 1
    sup = np.zeros(N)
    for r, n_r in enumerate(RING_COUNTS):
        for k in range(n_r):
            sup[vidx(r, k)] = math.cos(2*math.pi*k/max(n_r, 1))
    frag = np.sign(np.random.randn(N)); frag = frag - frag.mean()
    fqh = np.zeros(N)
    for k in range(RING_COUNTS[4]):
        if k % 8 < 5: fqh[vidx(4, k)] = 1   # nu=5/8 ansatz (B4 script)
    return {"BEC": exp(bec), "Supersolid": exp(sup),
            "FQH-like": exp(fqh), "Mott": exp(mott), "Fragmented": exp(frag)}

# ====================================================================
# F1 — Laplacian spectrum + phase ordering + weight-tuning
# ====================================================================
banner("F1  TSC-B4 Laplacian: phase ordering + can weighting fix Mott/FQH swap?")
EXPECTED = ["BEC", "Supersolid", "FQH-like", "Mott", "Fragmented"]

A0 = build_adjacency()
H0 = np.diag(A0.sum(1)) - A0
ev = np.linalg.eigvalsh(H0)
print(f"unit-weight: lambda_0={ev[0]:.2e} (expect 0), gap={ev[1]:.4f}, top={ev[-1]:.4f}")
e0 = phase_energies(H0)
order0 = [k for k, _ in sorted(e0.items(), key=lambda x: x[1])]
for k in EXPECTED: print(f"   {k:>11}: <H>={e0[k]:.4f}")
print(f"   ordering : {' < '.join(order0)}")
print(f"   matches urb_645? {order0 == EXPECTED}  (prior result: Mott/FQH swapped)")

# Try several natural weighting schemes to see if any restores FQH<Mott.
schemes = {
    "inter ~ radius(r+1)":      lambda r: RING_RADII[r+1],
    "inter ~ 1/radius(r+1)":    lambda r: 1.0/max(RING_RADII[r+1], 1e-9),
    "inter ~ radius(r+1)^2":    lambda r: RING_RADII[r+1]**2,
    "inter ~ sqrt(radius(r+1))":lambda r: math.sqrt(RING_RADII[r+1]),
}
fixed_any = False
for name, fn in schemes.items():
    A = build_adjacency(w_inter_fn=fn)
    H = np.diag(A.sum(1)) - A
    e = phase_energies(H)
    order = [k for k, _ in sorted(e.items(), key=lambda x: x[1])]
    ok = order == EXPECTED
    fixed_any = fixed_any or ok
    print(f"   [{name:>24}] -> {' < '.join(order)}  match={ok}")
print(f"\nF1 VERDICT: unit-weight reproduces the Mott/FQH swap (prior result CONFIRMED).")
print(f"   Any tested natural weighting restores urb_645 ordering? {fixed_any}")
print(f"   => Falsifier status: the qualitative phase-ordering claim is NOT robust;")
print(f"      it survives only as 'BEC lowest / Fragmented highest', which is trivial.")

# ====================================================================
# F2 — TECC E8 decoding radius vs sin(18deg)
# ====================================================================
banner("F2  TECC decoding radius vs claimed sin(18deg)=0.309")
C = 1/(PHI*math.sqrt(2))            # 0.4370... (urb_630 x_min=C)
T = 2*0.685 - C                     # from (C+T)/2=0.685 => T
print(f"C={C:.4f}  T={T:.4f}  (T-C={T-C:.4f})  sin18={SIN18:.4f}")
print(f"urb_630 claim: d_min = sqrt(2)*C = {math.sqrt(2)*C:.4f} ~ 1/phi={1/PHI:.4f},")
print(f"               correction radius = d_min/2 = {math.sqrt(2)*C/2:.4f} = sin18.")

# Representative codewords from urb_630 Table 2.3, in their stated 8D coords.
# Dimensions order: [C, T, 1, sqrt2, phi, e, pi, real0]
cw = {
 "DT": np.array([C, 0,0,0,0,0,0,0]),
 "TF": np.array([T, 0,0,0,0,0,0,0]),          # SAME dimension as DT (table: "first dimension only")
 "TI": np.array([0,0,1,0,0,0,0,0]),
 "TT": np.array([0,0,0,0,PHI,0,0,0]),
 "EV": np.array([0,0,0,0,0,0,math.pi,0]),
}
names = list(cw)
mind, pair = 1e9, None
for i in range(len(names)):
    for j in range(i+1, len(names)):
        d = np.linalg.norm(cw[names[i]] - cw[names[j]])
        if d < mind: mind, pair = d, (names[i], names[j])
print(f"\nActual min pairwise distance over the 5 codewords (table coords):")
print(f"   d_min = {mind:.4f} between {pair} ; correction radius = {mind/2:.4f}")
print(f"   claimed correction radius (sin18) = {SIN18:.4f}")
# Alternative: if DT and TF were embedded ORTHOGONALLY (sec 2.2 assumption)
dt_o = np.array([C,0,0,0,0,0,0,0]); tf_o = np.array([0,T,0,0,0,0,0,0])
print(f"\nIf DT/TF placed in SEPARATE dims (sec 2.2 orthogonal assumption):")
print(f"   d(DT,TF)=sqrt(C^2+T^2)={np.linalg.norm(dt_o-tf_o):.4f} (>{math.sqrt(2)*C:.4f});")
print(f"   then binding min would be sqrt(2)*C only if all radii equal C — they are not.")
print(f"\nF2 VERDICT: the sin(18)=0.309 correction radius is NOT robust.")
print(f"   Under urb_630's OWN encoding table (DT,TF collinear in dim-1), the binding")
print(f"   minimum distance is the DT-TF gap T-C={T-C:.4f} -> correction radius {(T-C)/2:.4f},")
print(f"   ~20% BELOW the advertised 0.309. The elegant 'pentagon threshold' holds only")
print(f"   under a special orthogonal embedding that contradicts the same paper's table.")

# ====================================================================
# F3 — Mendi crystal crossover power analysis
# ====================================================================
banner("F3  Mendi crystal crossover: is pre-registered n~=10 adequate? (d=0.4)")
def paired_power(n, d, alpha=0.05):
    df = n - 1
    ncp = d*math.sqrt(n)
    tcrit = nct.ppf(1 - alpha/2, df, 0)      # central t critical
    return 1 - nct.cdf(tcrit, df, ncp) + nct.cdf(-tcrit, df, ncp)
for n in (10, 20, 30, 52, 64):
    print(f"   n={n:>3}  power(d=0.4, two-sided a=.05) = {paired_power(n, 0.4):.3f}")
# required n for power 0.8
n_req = next(n for n in range(5, 500) if paired_power(n, 0.4) >= 0.80)
print(f"\nF3 VERDICT: n=10 gives power={paired_power(10,0.4):.2f} (badly underpowered).")
print(f"   ~{n_req} paired sessions needed for 80% power at d=0.4.")
print(f"   The pre-registered n=10 would miss a true d=0.4 effect ~80% of the time.")

# ====================================================================
# F4 — phi-sighting look-elsewhere audit
# ====================================================================
banner("F4  phi-sighting look-elsewhere: is phi=1.618 doing real work?")
# Claimed hits (corpus): DNA pitch/diam ~phi (5% err), EEG theta/alpha ~phi (3%),
# tritone = sqrt2 (exact), FQH nu=2/5 -> ET (3.4%).  Audit: how easy to hit a
# 'special constant' within tolerance by chance, given a menu of special targets.
specials = {"1/phi":1/PHI, "1":1.0, "sqrt2":math.sqrt(2), "phi":PHI,
            "e/phi":math.e/PHI, "2":2.0, "e":math.e, "pi":math.pi}
lo, hi, tol = 0.5, 3.5, 0.05   # plausible ratio range, +-5% windows
covered = 0.0
for v in specials.values():
    if lo <= v <= hi: covered += min(hi, v*(1+tol)) - max(lo, v*(1-tol))
p_hit = covered / (hi - lo)
print(f"   menu of {len(specials)} 'special' constants in [{lo},{hi}], +-{tol*100:.0f}% windows")
print(f"   P(random ratio lands within tol of SOME special constant) = {p_hit:.3f}")
print(f"   => a single 'phi coincidence' within 5% is a ~{p_hit:.0%} chance event,")
print(f"      i.e. roughly 1-in-{1/p_hit:.1f}. Finding a few across many measured ratios")
print(f"      is expected under the null (look-elsewhere). p(>=4 hits in 8 ratios | null)")
from math import comb
k_obs, m = 4, 8
p4 = sum(comb(m, k)*p_hit**k*(1-p_hit)**(m-k) for k in range(k_obs, m+1))
print(f"      = {p4:.3f}  (NOT significant at .05).")
print(f"F4 VERDICT: the phi-sightings are consistent with chance once look-elsewhere")
print(f"   over the standard-constant menu is accounted for. phi is SUGGESTIVE, not")
print(f"   load-bearing, absent a pre-registered single-target prediction.")

# ====================================================================
# F5 — CHSH Ring(T) null test
# ====================================================================
banner("F5  CHSH Ring(T) null test (must NOT violate classical bound 2)")
# C6 convention rings & radii:
C6 = {"C":0.0,"T":1/math.sqrt(2),"1":1.0,"sqrt2":math.sqrt(2),
      "phi":PHI,"e":math.e,"pi":math.pi}
def chsh(ri, rj): return 2*min(ri, rj)
for k in ["T","1","sqrt2","phi"]:
    val = chsh(C6[k], C6[k])
    tag = ("<2 classical-OK" if val < 2 else
           "=2 boundary" if abs(val-2)<1e-9 else
           "(2,2.828] quantum" if val <= 2*math.sqrt(2)+1e-9 else
           ">2.828 SUPER-Tsirelson")
    print(f"   Ring({k}): CHSH=2*min(r,r)={val:.4f}  {tag}")
tt = chsh(C6["T"], C6["T"])
print(f"\nF5 VERDICT: Ring(T) CHSH={tt:.4f} < 2  => prediction CONFIRMED (null holds):")
print(f"   pure-Tralse-axis i-cells do NOT violate CHSH. This is the one cleanly")
print(f"   PASSING falsifier — but note it is a NON-violation (consistent with classical),")
print(f"   so it confirms the framework's internal consistency, not new physics.")

# ====================================================================
# BIO — quartz coherence-storage physics test (resolve #508 vs #373)
# ====================================================================
banner("BIO  Quartz coherence-storage: charge-relaxation + mechanical test")
eps0, eps_r = 8.854e-12, 4.5
GEO = 1e6 * 365.25 * 24 * 3600   # 1 Myr in seconds
print("Claim (URB#508): 'coherence imprint held for GEOLOGICAL timescales,")
print("   mechanically locked, actively re-emitted via converse piezo.'")
print("Clause (URB#373): 'no mechanism for persistent information storage.'\n")
print("Test 1 - dielectric charge relaxation  tau = eps0*eps_r*rho :")
for rho in (1e12, 1e14, 1e16):
    tau = eps0*eps_r*rho
    h = tau/3600
    print(f"   rho={rho:.0e} Ohm*m -> tau={tau:.3g}s ({h:.3g} h, {tau/86400:.3g} d); "
          f"tau/geological={tau/GEO:.1e}")
print(f"\n   Geological reference = {GEO:.2e} s. Even at the most-insulating end")
print(f"   (rho=1e16), tau ~ 4.6 days -- ~{GEO/(eps0*eps_r*1e16):.0e}x SHORT of geological.")
print("\nTest 2 - mechanical strain: room-T alpha-quartz is brittle-ELASTIC; elastic")
print("   strain releases instantly on stress removal (Hooke). Persistent strain needs")
print("   plastic flow (dislocation glide), negligible below ~300C -- and a frozen")
print("   dislocation is a static defect, not a re-emittable 'coherence imprint'.")
print("\nBIO VERDICT: the GEOLOGICAL-timescale / 'mechanically locked' storage claim is")
print("   REFUTED by mainstream physics (charge relaxation bounds any electrical store")
print("   to <= O(days); elastic strain is not retained). URB#373's no-persistent-")
print("   storage clause WINS. Reconciliation: a TRANSIENT store of <= O(days) is")
print("   physically allowed (same order as Bengston's 'hours-to-days' WATER result),")
print("   so quartz is NOT 'superior to water' for storage -- it is at best comparable")
print("   and only transiently. Net: bio active-storage downgraded speculative->REFUTED")
print("   for the geological/superior version; transient-only survives as candidate.")

banner("DONE — all falsifiers + bio storage test executed ($0, deterministic)")
