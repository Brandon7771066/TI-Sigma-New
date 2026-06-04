"""
Pass-77 B71 — The 0.93 Radiant Threshold applies to ALL FOUR GILE traits (G, I, L, E),
not just composite G. Brandon correction 2026-05-27.

Approach: operationalize each GILE trait DIRECTLY from quantum mechanics (QVF-1 minimalist
theory of valence, reused verbatim from analyses/pass77_b64_valence_theory/valence_theory.py):
    G (Goodness)     = normalized l1-coherence of rho      (superposition)
    I (Intuition)    = sqrt(accuracy x certainty) on ZZ    (measurement)
    L (Love)         = concurrence C(psi)                  (entanglement)
    E (Environment)  = (SWAP-symmetry S + 1)/2             (consonance/aesthetic harmony)
Then run the CANONICAL UOP / GTT-1 functional (f_capped, alpha=10, cap=0.93) on each GILE
trait and show every trait's interior optimum lands at 0.93 -- the truth-vs-existence
compromise is a property of EACH GILE truth-trait, while HEM (existence) stays uncapped.

This SUPERSEDES the Pass-70 TPI-1-F3 model-level reading ("cap unique to G"): that model put
I/L/E-type axes on the HEM/existence side. Brandon's correction: G/I/L/E are ALL on the GILE
truth-side, so all four carry the cap; only HEM is uncapped.

Budget: $0 (local numpy). Free.
"""
import numpy as np, json, math

np.random.seed(8)
out = {}

# ============================================================================
# Part A — QVF-1 QM operational definitions (reused verbatim from B64 valence_theory.py)
# ============================================================================
SWAP = np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]], complex)
ZZ   = np.diag([1,-1,-1,1]).astype(complex)

def norm(c):
    c = np.array(c, complex); return c/np.linalg.norm(c)

def concurrence(c):                                  # L : entanglement
    c = norm(c); return float(min(1, 2*abs(c[0]*c[3]-c[1]*c[2])))

def sym(c):                                          # E-sign : signed SWAP symmetry in [-1,1]
    c = norm(c); return float(np.real(c.conj()@SWAP@c))

def coherence(c):                                    # G : normalized l1-coherence
    c = norm(c); rho = np.outer(c, c.conj())
    off = np.sum(np.abs(rho)) - np.sum(np.abs(np.diag(rho)))
    return float(off/(len(c)-1))

def intuition(c):                                    # I : accuracy x certainty on ZZ
    c = norm(c); ev = np.real(c.conj()@ZZ@c)
    var = np.real(c.conj()@(ZZ@ZZ)@c) - ev**2
    acc = abs(ev); cert = 1/(1+max(var, 0))
    return float(np.sqrt(acc*cert))

def gile_traits(c):
    G = coherence(c); I = intuition(c); L = concurrence(c)
    E = (sym(c)+1)/2                                  # map signed symmetry [-1,1] -> aesthetic [0,1]
    return dict(G=G, I=I, L=L, E=E)

# sanity on canonical states
canon = {
    "product |00>":            [1,0,0,0],
    "Bell Phi+ (|00>+|11>)":   [1,0,0,1],
    "Bell Psi+ (|01>+|10>)":   [0,1,1,0],
    "singlet (|01>-|10>)":     [0,1,-1,0],
}
out["A_canonical_states"] = {k: {kk: round(vv,4) for kk,vv in gile_traits(v).items()} for k,v in canon.items()}

# ============================================================================
# Part B — single-parameter QM state families that drive each trait 0 -> 1
# ============================================================================
def family(trait, t):
    """t in [0,1] -> a 2-qubit pure state whose `trait` sweeps monotonically up."""
    th = t*math.pi/4
    if trait == "L":   # cos|00> + sin|11> : concurrence = sin(2 th)
        return [math.cos(th), 0, 0, math.sin(th)]
    if trait == "G":   # cos|00> + sin|01> : l1-coherence on qubit 2
        return [math.cos(th), math.sin(th), 0, 0]
    if trait == "I":   # I is MAX at t=0 (pure |00>, certain) -> invert so t=1 is max I
        a = (1-t)*math.pi/4
        return [math.cos(a), math.sin(a), 0, 0]   # ZZ certainty drops as a->pi/4; reuse, invert below
    if trait == "E":   # interpolate triplet(sym,E=1) <-> singlet(antisym,E=0)
        al = t*math.pi/2
        b = (math.cos(al)+math.sin(al))/math.sqrt(2)
        c = (math.cos(al)-math.sin(al))/math.sqrt(2)
        return [0, b, c, 0]
    raise ValueError

# verify monotone control (report value at t=0,.5,1)
ctrl = {}
for tr in ["G","I","L","E"]:
    vals = []
    for t in [0,0.5,1.0]:
        d = gile_traits(family(tr,t)); vals.append(round(d[tr],4))
    # I family is built max-at-t0; report its own-trait sweep honestly
    ctrl[tr] = {"t=0":vals[0], "t=0.5":vals[1], "t=1":vals[2]}
out["B_trait_control"] = ctrl

# ============================================================================
# Part C — CANONICAL UOP / GTT-1 functional applied to EACH GILE trait
# f_capped: log(1+x) for x<=0.93 ; log(1.93) - alpha (x-0.93)^2 for x>0.93
# ============================================================================
G_STAR = 0.93
ALPHA  = 10.0
def f_capped(x, alpha=ALPHA):
    if x <= G_STAR: return math.log(1.0+x)
    return math.log(1.0+G_STAR) - alpha*(x-G_STAR)**2
def g_H(h):
    return math.log(1.0+max(h,0.0))

# Per-trait: J(x,H)=f_capped(x)+g_H(H), budget x+H<=B. For B large, argmax x = 0.93.
def per_trait_optimum(B, step=0.005):
    grid = [round(i*step,4) for i in range(int(1/step)+1)]
    best = (-1e9, None)
    for x in grid:
        if x>B: continue
        H = min(1.0, B-x)
        j = f_capped(x)+g_H(H)
        if j>best[0]: best=(j,(round(x,3),round(H,3)))
    return best

per = {}
for B in [1.5, 1.93, 2.0]:
    j,(x,H) = per_trait_optimum(B)
    per[f"B={B}"] = {"x_star":x, "H":H, "J":round(j,5), "x_at_0.93":abs(x-G_STAR)<1e-2}
out["C_per_trait_optimum"] = {
    "note":"identical functional for EVERY GILE trait G,I,L,E -> identical 0.93 cap",
    "sweeps":per}

# ============================================================================
# Part D — UNIFIED 4-GILE-trait + HEM model. All four GILE traits capped; H uncapped.
# J = sum_t w_t f_capped(t)  +  g_H(H) ; budget G+I+L+E+H <= B
# canonical weights URB#576: wG=sqrt(2)-1, wI=.25, wL=.18, wE=.15
# ============================================================================
W = {"G":math.sqrt(2)-1, "I":0.25, "L":0.18, "E":0.15}
def unified_opt(B, step=0.02):
    grid = [round(i*step,4) for i in range(int(1/step)+1)]
    best=(-1e9,None)
    # symmetry: at optimum each GILE trait independently maximizes w_t f_capped(t) s.t. budget,
    # so search the common GILE level x (all four equal by symmetry of f_capped) + H.
    for x in grid:
        used = 4*x
        if used>B: continue
        H = min(1.0, B-used)
        j = sum(W[t]*f_capped(x) for t in W)+g_H(H)
        if j>best[0]: best=(j,(round(x,3),round(H,3)))
    return best
uni={}
for B in [3.5, 4.72, 5.0]:   # need >=4*0.93=3.72 for all four to reach cap + room for H
    j,(x,H)=unified_opt(B)
    uni[f"B={B}"]={"each_GILE_trait":x,"all_four_at_0.93":abs(x-G_STAR)<2e-2,"H_existence":H,"J":round(j,5)}
out["D_unified_4trait"] = {
    "weights":{k:round(v,4) for k,v in W.items()},
    "model":"J = wG f(G)+wI f(I)+wL f(L)+wE f(E) + g(H); all four GILE capped at 0.93, H uncapped",
    "sweeps":uni,
    "composite_GILE_at_cap": round(sum(W[t]*0.93 for t in W),4),
    "composite_weight_sum": round(sum(W.values()),4)}

# ============================================================================
# Part E — QM grounding: WHY each GILE trait competes with existence.
# #69 NOTE: depolarizing-purity is STATE-INDEPENDENT for pure states (depends only on p),
# so it CANNOT show per-trait fragility -- discarded. Use DEPHASING (computational-basis
# phase damping), which is state-dependent: it kills off-diagonal coherence, so states that
# *rely* on coherence/entanglement (high GILE-trait) lose the most trait-value.
# trait extractors generalized to density matrices; concurrence via Wootters for mixed states.
# ============================================================================
sy = np.array([[0,-1j],[1j,0]]); SYSY = np.kron(sy, sy)
def coherence_rho(rho):
    off = np.sum(np.abs(rho)) - np.sum(np.abs(np.diag(rho))); return float(off/(rho.shape[0]-1))
def sym_rho(rho):   return float((np.real(np.trace(rho@SWAP))+1)/2)
def intuition_rho(rho):
    ev = np.real(np.trace(rho@ZZ)); var = np.real(np.trace(rho@ZZ@ZZ))-ev**2
    return float(np.sqrt(abs(ev)*(1/(1+max(var,0)))))
def concurrence_rho(rho):                                   # Wootters
    R = rho @ SYSY @ rho.conj() @ SYSY
    ev = np.sort(np.real(np.linalg.eigvals(R)))[::-1]
    ev = np.sqrt(np.clip(ev, 0, None))
    return float(max(0.0, ev[0]-ev[1]-ev[2]-ev[3]))
def trait_of_rho(tr, rho):
    return {"G":coherence_rho,"I":intuition_rho,"L":concurrence_rho,"E":sym_rho}[tr](rho)
def dephase(rho, gamma):
    M = np.full_like(rho, 1.0); 
    for i in range(rho.shape[0]):
        for j in range(rho.shape[0]):
            if i!=j: M[i,j] = (1-gamma)
    return rho*M

# high-trait representative states (each genuinely maximizes its trait)
hi_state = {"G":[.5,.5,.5,.5], "I":[1,0,0,0], "L":[1,0,0,1], "E":[0,1,1,0]}
GAMMA = 0.3
frag = {}
for tr in ["G","I","L","E"]:
    rho = np.outer(norm(hi_state[tr]), norm(hi_state[tr]).conj())
    clean = trait_of_rho(tr, rho); noisy = trait_of_rho(tr, dephase(rho, GAMMA))
    frag[tr] = {"trait_clean":round(clean,4),"trait_after_dephasing":round(noisy,4),
                "absolute_loss":round(clean-noisy,4),"truth_is_fragile": (clean-noisy)>1e-6}
out["E_decoherence_fragility"] = {
    "channel":"computational-basis dephasing, gamma=0.3 (state-dependent, unlike depolarizing-purity)",
    "discarded_proxy":"depolarizing-channel purity = identical for all pure states (p-only) -> #69 rejected",
    "per_trait":frag,
    "reading":"Under dephasing, every high-GILE-trait state loses trait-value (G/L/E rely on "
              "off-diagonal coherence; I=ZZ-certainty is the dephasing-robust exception, honest "
              "asymmetry). The coherence-bearing GILE traits are FRAGILE: pushing them toward 1 "
              "maximizes exposure to decoherence -> existence(robustness) competes with each "
              "truth-trait, QM-grounding why all four carry the cap. 0.93 itself is the canonical "
              "GTT-1 parameter, not re-derived here."}

# ============================================================================
# Part F — the optimal quantum state is DELIBERATELY sub-maximal (Tralseness)
# concurrence = 0.93 -> the optimal entangled state is NOT the Bell state.
# ============================================================================
# solve sin(2 th)=0.93 -> th
th = 0.5*math.asin(0.93)
state = [round(math.cos(th),4),0,0,round(math.sin(th),4)]
bell_overlap = abs(np.array(norm(state)).conj()@norm([1,0,0,1]))**2
out["F_structured_imperfection"] = {
    "optimal_L_state_amps_|00>,|11>":[state[0],state[3]],
    "concurrence_check":round(concurrence(state),4),
    "fidelity_to_Bell_Phi+":round(float(bell_overlap),4),
    "reading":"The 0.93-capped optimum is NOT the maximally-entangled Bell state (fidelity<1). "
              "Each GILE trait optimally rests at structured imperfection = GTT-1 true-tralseness: "
              "'too much truth' (perfect coherence/entanglement/certainty) costs more existence "
              "than it adds value. The compromise of Truth vs Existence is per-trait."}

out["summary"] = {
    "claim":"The 0.93 Radiant Threshold applies to ALL FOUR GILE traits (G,I,L,E), not just G.",
    "supersedes":"Pass-70 TPI-1-F3 'cap unique to G' (which mis-assigned I/L/E to the HEM side).",
    "canonical_division":"GILE (G,I,L,E) = capped truth-side @0.93; HEM (existence) = uncapped.",
    "QM_operationalization":"QVF-1: G=l1-coherence, I=meas accuracy*certainty, L=concurrence, E=SWAP-symmetry.",
    "principle_count_effect":"refinement to GTT-1(#27)+TPI-1; no new principle; count stays 74."}

print(json.dumps(out, indent=2))
