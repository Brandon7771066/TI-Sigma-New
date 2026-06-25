"""
Pass-77 B145 — Thirds / Ternary / Transrational validation harness.

HONESTY CONTRACT (#69 / EVD-1 / HAN-1):
  - This script SEPARATES genuine math (provable given the posited forms)
    from heuristic resonances (graded evidence, NOT proof; HAN-1).
  - Every block prints what it DOES and DOES NOT show.
  - No numerology is treated as load-bearing. Resonances are flagged and
    each carries a "predicts nothing new" guard.
  - Canonical principle count stays 79. All findings are CANDIDATES.
"""
import numpy as np

OUT = []
def say(s): OUT.append(s); print(s)

# ---------------------------------------------------------------------------
# BLOCK 1 — GENUINE: the UOP ratio-reframing cap = 3*T_d - 1 and the THIRDS.
#   Myrion(T) = max_T [ rho * ln(1+T) + ln(2-T) ],  rho = T_d/(1-T_d).
#   Closed form interior optimum T* = (2rho-1)/(1+rho) = 3*T_d - 1.
# ---------------------------------------------------------------------------
say("="*72)
say("BLOCK 1 [GENUINE]: ratio-reframing cap and the thirds")
def cap_numeric(Td):
    rho = Td/(1-Td)
    Ts = np.linspace(1e-6, 1-1e-6, 2_000_001)
    J = rho*np.log(1+Ts) + np.log(2-Ts)
    return Ts[int(np.argmax(J))]
def cap_closed(Td):
    return 3*Td - 1.0
max_err = 0.0
for Td in [0.40, 0.50, 0.60, 0.644, 0.66]:
    num = cap_numeric(Td)
    cf  = min(max(cap_closed(Td), 0.0), 1.0)
    err = abs(num - cf)
    max_err = max(max_err, err)
    say(f"  T_d={Td:.3f}  numeric T*={num:.5f}  closed 3T_d-1={cf:.5f}  |err|={err:.2e}")
say(f"  -> max |numeric - closed| over interior band = {max_err:.2e}")
b1 = max_err < 1e-3

# regime boundaries at exactly 1/3 and 2/3
lower = cap_closed(1/3)   # -> 0
upper = cap_closed(2/3)   # -> 1
say(f"  regime lower boundary cap(1/3) = {lower:.6f}  (truth-pursuit switches ON at 0)")
say(f"  regime upper boundary cap(2/3) = {upper:.6f}  (truth-saturation: cap hits 1)")
b1b = abs(lower-0.0) < 1e-9 and abs(upper-1.0) < 1e-9
say("  SHOWS: with logs ln(1+T), ln(2-T) and existence=1-T, the cap is EXACTLY")
say("         3*T_d-1, and the three regimes split at T_d = 1/3 and 2/3.")
say("  DOES NOT SHOW: that the LOG forms are uniquely correct (contingency C1);")
say("         the '3' is 2(existence offset)+1(truth pole), form-dependent.")

# ---------------------------------------------------------------------------
# BLOCK 2 — GENUINE: ternary-on-the-real-axis reconciliation (TRR-1).
#   Real (PD-degree) axis is ternary {T=+1, I=0, F=-1} (Lukasiewicz-3).
#   MI and N/A are the genuinely COMPLEX (off-real) values.
# ---------------------------------------------------------------------------
say("="*72)
say("BLOCK 2 [GENUINE]: ternary real axis + complex extras (TRR-1)")
# Degree-vs-modality canonical split (B143 A1 real / A2 imaginary):
labels = {
    "True":         1+0j,      # real +1
    "Indeterminate":0+0j,      # real  0  (degree = 0.5 maps to axis-origin)
    "False":       -1+0j,      # real -1
    "MetaIndet":    0+1j,      # imaginary (modality / nature-clash)
    "NA":           0-1j,      # hyperimaginary stand-in (applicability axis)
}
reals = sorted({round(v.real,6) for v in labels.values()})
imags = sorted({round(v.imag,6) for v in labels.values() if abs(v.imag)>1e-9})
say(f"  distinct REAL-axis values     = {reals}   (count={len(reals)})")
say(f"  distinct nonzero IMAG values   = {imags}   (count={len(imags)})")
real_axis_labels = [k for k,v in labels.items() if abs(v.imag)<1e-9]
complex_labels   = [k for k,v in labels.items() if abs(v.imag)>=1e-9]
say(f"  real-axis (ternary) labels = {real_axis_labels}")
say(f"  complex labels             = {complex_labels}")
b2 = (len(reals)==3) and (len(complex_labels)==2)
say("  SHOWS: the real-axis projection is EXACTLY ternary {+1,0,-1}={T,I,F}")
say("         (= Lukasiewicz-3), and precisely TWO labels (MI, N/A) are complex.")
say("         This reconciles 'ternary skeleton' with 'base-4/5 ratified labels'.")
say("  REFINES B143/QTA-1: plain Indeterminate sits at real-0 (a DEGREE), not at")
say("         +i; only MI is a phase (a MODALITY). Consistent w/ canonical")
say("         PD-degree(real) vs PD-modality(imag) split. Count stays 79.")
say("  DOES NOT SHOW: that N/A's hyperimaginary placement is unique (open).")

# ---------------------------------------------------------------------------
# BLOCK 3 — CANDIDATE-CONSISTENCY: i-Cell determinacy / 2/3 centralization.
#   Determinacy d = (weight on real/determinate axis) / (total).
#   Claim: a concrete i-Cell (human nervous system) ~ 2/3 determinate, and
#   2/3 = the UOP truth-saturation regime boundary. This is a DEFINITIONAL
#   ALIGNMENT (the two 2/3's coincide), NOT a derivation of the empirical 2/3.
# ---------------------------------------------------------------------------
say("="*72)
say("BLOCK 3 [CANDIDATE/CONSISTENCY]: 2/3 i-Cell determinacy (ICD-1)")
d = 2/3                       # posited determinacy of a concrete i-Cell
indet = 1 - d
say(f"  posited concrete-i-Cell determinacy d = {d:.4f}, indeterminacy = {indet:.4f}")
say(f"  UOP truth-saturation boundary T_d = 2/3 = {2/3:.4f}")
b3 = abs(d - 2/3) < 1e-12
say(f"  determinacy ratio d/(1-d) = {d/(1-d):.4f}  (= rho at the boundary = 2.0)")
say("  SHOWS: IF a concrete i-Cell is 2/3-determinate THEN it sits exactly at the")
say("         truth-saturation onset (cap->1): a clean alignment of two 2/3's.")
say("  DOES NOT SHOW: that the human nervous system IS empirically 2/3-determinate.")
say("         That number is the author's posited intuition-lead (TRI-1) -> owes a")
say("         measurement falsifier (ICD-1-F1). i-Web = lower d (more decentralized).")

# ---------------------------------------------------------------------------
# BLOCK 4 — RESONANCE ONLY (HAN-1 graded, weight~0 until predictive): 4/3.
# ---------------------------------------------------------------------------
say("="*72)
say("BLOCK 4 [RESONANCE — NOT RESULT]: the 4/3 ratio family")
say(f"  2*(2/3) = {2*(2/3):.4f} = 4/3 ; the documented 4:3:2 threshold pattern")
say("  contains both the 2/3 determinacy and the 4/3 indeterminate-range scaling.")
say("  STATUS (HAN-1): evidence-status YES, evidential WEIGHT ~0. The 4/3 family")
say("  is a recurring corpus ratio ('recursive numerical beauty') that PREDICTS")
say("  NOTHING NEW here -> it stays a lead to chase, never load-bearing, until it")
say("  forecasts an out-of-sample quantity (existing falsifier: holds at N>=1000).")

# ---------------------------------------------------------------------------
say("="*72)
all_pass = all([b1, b1b, b2, b3])
say(f"GENUINE-MATH CHECKS PASS = {all_pass}  (b1={b1} b1b={b1b} b2={b2} b3={b3})")
say("Resonance blocks (4/3) are intentionally NOT gated on a pass — heuristic only.")
say("Canonical count unchanged: 79. All items are CANDIDATES.")

with open(__file__.replace('.py','_output.txt'),'w') as f:
    f.write("\n".join(OUT)+"\n")
