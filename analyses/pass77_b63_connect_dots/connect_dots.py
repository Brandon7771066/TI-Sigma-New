import numpy as np
np.random.seed(7)

# ---- Dirac algebra (Dirac representation) ----
I2=np.eye(2); Z2=np.zeros((2,2))
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]],complex); sz=np.array([[1,0],[0,-1]],complex)
g0=np.block([[I2,Z2],[Z2,-I2]]).astype(complex)
def gi(s): return np.block([[Z2,s],[-s,Z2]]).astype(complex)
g1,g2,g3=gi(sx),gi(sy),gi(sz)
g5=1j*g0@g1@g2@g3
G=[g0,g1,g2,g3]
LAB=["G (γ0, Goodness/Four-C's, timelike)","I (γ1, Intuition acc+cert)","L (γ2, Love/relational)","E (γ3, Environment/aesthetics)"]

def bar(psi): return psi.conj()@g0
def Vmu(psi): return np.array([np.real(bar(psi)@G[m]@psi) for m in range(4)])   # vector current (PHYSICAL/HEM)
def Amu(psi): return np.array([np.real(bar(psi)@g5@G[m]@psi) for m in range(4)])# axial  current (ABSTRACT/GILE)

def rnd_spinor():
    v=np.random.randn(4)+1j*np.random.randn(4); return v/np.linalg.norm(v)
def chiral(handed=+1):
    P=(np.eye(4)+handed*g5)/2; v=P@rnd_spinor()
    n=np.linalg.norm(v); return v/n if n>1e-9 else chiral(handed)

def per_cell_ratio(psi):
    V=Vmu(psi); A=Amu(psi)
    # regress A = rho*V through origin over the 4 dims; R^2 = proportionality quality
    denom=np.dot(V,V)
    rho=np.dot(A,V)/denom if denom>1e-12 else np.nan
    resid=A-rho*V; ss=np.dot(A,A)
    r2=1-np.dot(resid,resid)/ss if ss>1e-12 else 1.0
    return rho,r2,V,A

print("=== DIRAC: per-i-cell proportionality  A^mu (GILE/abstract) vs V^mu (HEM/physical) ===")
print("Mapping mu=0,1,2,3  ->  "+", ".join(l.split(',')[0] for l in LAB))
# chiral (Weyl) eigenstates -> expect exact proportionality
for h in (+1,-1):
    rho,r2,V,A=per_cell_ratio(chiral(h))
    print(f"  Weyl handed={h:+d}: rho(|A|/|V|-signed)={rho:+.4f}  R^2={r2:.5f}  (V={np.round(V,3)}, A={np.round(A,3)})")
# generic (massive-mixed) ensemble
rs=[];r2s=[]
for _ in range(4000):
    rho,r2,_,_=per_cell_ratio(rnd_spinor()); 
    if np.isfinite(rho): rs.append(rho); r2s.append(r2)
rs=np.array(rs); r2s=np.array(r2s)
print(f"  generic ensemble (n={len(rs)}): rho mean={rs.mean():+.3f} std={rs.std():.3f} range=[{rs.min():+.3f},{rs.max():+.3f}]")
print(f"     -> ratio DIFFERS per i-cell (std {rs.std():.3f}) -- matches Brandon 'ratio differs per i-cell'")
print(f"  per-cell proportionality R^2: mean={r2s.mean():.3f} median={np.median(r2s):.3f} frac(R^2>0.9)={np.mean(r2s>0.9):.3f}")
print(f"     -> 'GILE = rho x HEM componentwise' holds EXACTLY for chiral (R^2=1), LARGELY for generic (median R^2={np.median(r2s):.2f})")

print("\n=== I (Intuition = accuracy + certainty), concrete on observable Sigma_z (gamma1-sector) ===")
def acc_cert(psi,Op):
    e=np.real(bar(psi)@g0@Op@psi)  # use density-weighted expectation via psi^dag Op psi
    ev=np.real(psi.conj()@Op@psi); var=np.real(psi.conj()@(Op@Op)@psi)-ev**2
    return abs(ev), 1.0/(1.0+max(var,0))   # accuracy=|<O>|, certainty=1/(1+Var)
Sz=np.block([[sz,Z2],[Z2,sz]])
for name,st in [("eigenstate |up>",np.array([1,0,0,0],complex)),("superpos (|up>+|dn>)/v2",np.array([1,0,1,0],complex)/np.sqrt(2))]:
    a,c=acc_cert(st,Sz); print(f"  {name:26s}: accuracy={a:.3f}  certainty={c:.3f}  (Intuition is 2-D: acc x cert)")

print("\n=== L (Love = relational valence) = entanglement; corpus formula L=tanh(entanglement)*2 ===")
def concurrence(c):  # 2-qubit pure state amplitudes c00,c01,c10,c11
    c=c/np.linalg.norm(c); return float(2*abs(c[0]*c[3]-c[1]*c[2]))
for name,c in [("product |00>",np.array([1,0,0,0],complex)),("Bell (|00>+|11>)/v2",np.array([1,0,0,1],complex))]:
    C=concurrence(c); L=np.tanh(C)*2; print(f"  {name:20s}: concurrence={C:.3f} -> L=tanh(C)*2={L:.3f}  (product->0, max-entangled->{np.tanh(1)*2:.3f})")

print("\n=== E (Environment = aesthetics/symmetry) = overlap with symmetric subspace ===")
SWAP=np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]],complex)
for name,c in [("symmetric (|01>+|10>)/v2",np.array([0,1,1,0],complex)/np.sqrt(2)),("antisym (|01>-|10>)/v2",np.array([0,1,-1,0],complex)/np.sqrt(2))]:
    c=c/np.linalg.norm(c); sym=float(np.real(c.conj()@SWAP@c)); print(f"  {name:24s}: <SWAP>={sym:+.3f}  aesthetics/symmetry score={ (sym+1)/2:.3f}")

print("\n=== MAXWELL knot: physical energy density vs abstract helicity (relational/Love-analog) ===")
def field_ratio(E,B):
    E=np.array(E,float); B=np.array(B,float)
    u=0.5*(E@E+B@B)            # energy density (PHYSICAL/HEM)
    hel=E@B                    # helicity density ~ E.B (ABSTRACT/relational, pseudoscalar)
    return u,hel,hel/u if u>1e-12 else 0
for name,E,B in [("plane wave E perp B",[1,0,0],[0,1,0]),("null/knot-like E||B",[1,0,0],[0.8,0,0])]:
    u,h,r=field_ratio(E,B); print(f"  {name:22s}: energy u={u:.3f}  helicity E.B={h:+.3f}  ratio={r:+.3f}  ({'zero helicity (orthogonal)' if abs(r)<1e-6 else 'nonzero linking (knotted)'})")

print("\n#69 VERDICTS:")
print("  grade-2: 4 gamma matrices = 4 GILE dims (count exact); Weyl A^mu = +-V^mu EXACT proportionality (R^2=1).")
print("  grade-1.5: V/A = HEM/GILE assignment; per-dim semantics (G/I/L/E) to gammas; L=tanh(C)*2 corpus formula.")
print("  grade-1: generic proportionality only 'largely' (deviations = mass/mixing = independent DOF, echoes B62 phase-perp-modulus); Maxwell side helicity-analog suggestive not exhaustive.")
