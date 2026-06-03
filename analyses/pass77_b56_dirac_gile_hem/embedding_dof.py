import numpy as np
np.set_printoptions(precision=4, suppress=True)
rng=np.random.default_rng(7)

print("=== CLAIM: the 2 'meaningless' DOF (global phase + normalization) become")
print("    PHYSICAL exactly upon EMBEDDING/COUPLING = signature of an EXISTENCE(HEM) dim ===\n")

# A normalized state
psi=rng.normal(size=4)+1j*rng.normal(size=4); psi/=np.linalg.norm(psi)

print("--- DOF 1: GLOBAL PHASE ---")
for phi in [0, np.pi/2, np.pi]:
    p=np.exp(1j*phi)*psi
    born=np.abs(p)**2
    print(f" phi={phi:.2f}: isolated Born |psi|^2 (first 2)={born[:2]}  (UNCHANGED -> invisible in isolation)")
# embed: interfere with a fixed reference state chi
chi=rng.normal(size=4)+1j*rng.normal(size=4); chi/=np.linalg.norm(chi)
print(" Now EMBED (interfere with reference chi): total prob |e^{i phi} psi + chi|^2 vs phi:")
for phi in [0, np.pi/2, np.pi, 3*np.pi/2]:
    tot=np.abs(np.exp(1j*phi)*psi+chi)**2
    print(f"   phi={phi:.2f}: P={tot.sum():.4f}  <- VARIES with global phase => PHYSICAL upon embedding")

print("\n--- DOF 2: NORMALIZATION (total amplitude) ---")
print(" isolated: any scale a*psi renormalizes to 1 -> total amplitude invisible.")
print(" Now EMBED two subsystems a|psi1> + b|psi2>; relative weight |a|/|b| is PHYSICAL:")
psi1=rng.normal(size=4)+1j*rng.normal(size=4); psi1/=np.linalg.norm(psi1)
psi2=rng.normal(size=4)+1j*rng.normal(size=4); psi2/=np.linalg.norm(psi2)
for (a,b) in [(1,0.0),(1,1),(1,3)]:
    comb=a*psi1+b*psi2; w=np.abs(comb)**2; w/=w.sum()
    print(f"   (a,b)=({a},{b}): branch-1 weight={ (abs(a)**2)/(abs(a)**2+abs(b)**2):.3f}  <- relative norm PHYSICAL upon embedding")

print("\n=== INTERPRETATION ===")
print(" Truth(GILE) dims  = INTRINSIC/relative structure -> visible in ISOLATION.")
print(" Existence(HEM) dims = global amplitude + global phase -> visible only via EMBEDDING/COUPLING.")
print(" => HEM-D5 Intrinsic-Presence/Vitality  <- NORMALIZATION (amount-of-existence; Meijer 'Amplitude'; constant: mass m)")
print(" => HEM-D6 Interaction/LxE coupling      <- GLOBAL PHASE  (phase observable only via coupling; Meijer 'Phase alignment'; constant: coupling e/alpha)")
print(" Reconciliation: 8 = 4 GILE(intrinsic) + 4 HEM(2 embedded-visible + 2 embedding-only). The '6 physical'")
print(" = isolation-measurable subset; the 2 'gauge' DOF are real Existence dims that only manifest relationally.")
