import numpy as np
np.set_printoptions(precision=3, suppress=True)
I2=np.eye(2,dtype=complex); Z2=np.zeros((2,2),dtype=complex)
sx=np.array([[0,1],[1,0]],dtype=complex); sy=np.array([[0,-1j],[1j,0]],dtype=complex); sz=np.array([[1,0],[0,-1]],dtype=complex)
sig=[sx,sy,sz]
def blk(a,b,c,d): return np.block([[a,b],[c,d]])
g0=blk(I2,Z2,Z2,-I2)
g=[g0]+[blk(Z2,s,-s,Z2) for s in sig]   # Dirac basis
g5=1j*g[0]@g[1]@g[2]@g[3]
eta=np.diag([1,-1,-1,-1]).astype(complex)
I4=np.eye(4,dtype=complex)

print("=== T_A: Clifford algebra {g^mu,g^nu}=2 eta^{mu nu} I4 ===")
ok=True
for m in range(4):
    for n in range(4):
        anti=g[m]@g[n]+g[n]@g[m]
        target=2*eta[m,n]*I4
        if not np.allclose(anti,target): ok=False; print("FAIL",m,n)
print("Clifford algebra holds:",ok)
print("signature split: (g0)^2=+I:",np.allclose(g[0]@g[0],I4),
      "| (g1,2,3)^2=-I:",all(np.allclose(g[i]@g[i],-I4) for i in (1,2,3)))
print("-> FORCED 1+3 split: exactly ONE generator squares to +1 (timelike), THREE square to -1.")

print("\n=== T_B: chiral gamma5 and 4+4 Weyl split ===")
print("(g5)^2=I:",np.allclose(g5@g5,I4),"| {g5,g^mu}=0 all mu:",
      all(np.allclose(g5@g[m]+g[m]@g5,0) for m in range(4)))
PL=(I4-g5)/2; PR=(I4+g5)/2
print("PL+PR=I:",np.allclose(PL+PR,I4),"| PL^2=PL:",np.allclose(PL@PL,PL),
      "| PL*PR=0:",np.allclose(PL@PR,0))
print("rank PL =",int(round(np.trace(PL).real)),", rank PR =",int(round(np.trace(PR).real)),
      "-> 4-cplx-spinor splits into 2+2 complex = 4+4 REAL Weyl halves.")

print("\n=== T_C: honest real-DOF count of a Dirac spinor STATE ===")
psi=np.random.randn(4)+1j*np.random.randn(4)
raw=8
print("raw real components (4 complex):",raw)
print("minus normalization constraint |psi|=1: -1")
print("minus unobservable GLOBAL phase (U(1) gauge): -1")
print("=> PHYSICAL real DOF =",raw-2,"  (NOT a clean 8; 2 are gauge/constraint)")

print("\n=== T_D: magnitude/phase decomposition (corpus 'magnitude=HEM, phase=GIL') ===")
psi=psi/np.linalg.norm(psi)
mags=np.abs(psi); phases=np.angle(psi)
print("4 moduli (candidate HEM/Existence):",np.round(mags,3),"  sum sq =",round(float((mags**2).sum()),3))
print("4 phases (candidate GILE/valence) rad:",np.round(phases,3))
rel=phases-phases[0]
print("relative phases (global removed):",np.round(rel,3)," -> only 3 phases physical, not 4")
print("=> 4 moduli (1 fixed by norm => 3 free) + 4 phases (1 global gauge => 3 free) = 6 physical, as T_C.")

print("\n=== VERDICT INPUTS ===")
print("MATCHED (forced on both sides): dim 8=4+4; complex=mag+phase; non-commutative algebra; 1+3 sub-split.")
print("FREE (assignment, not forced): WHICH axis is timelike-G; WHICH chirality is GILE vs HEM.")
print("DEFLATION (#69): 2 of 8 real comps are gauge/norm; clean 4+4 needs that asterisk.")
