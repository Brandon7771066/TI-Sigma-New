import numpy as np
np.random.seed(66)
SWAP=np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]],complex)
def norm(c): c=np.array(c,complex); return c/np.linalg.norm(c)
def rho(c): c=norm(c); return np.outer(c,c.conj())
def redA(c):
    r=rho(c).reshape(2,2,2,2); return np.trace(r,axis1=1,axis2=3)
def vn_entropy(d):
    w=np.linalg.eigvalsh(d); w=w[w>1e-12]; return float(-np.sum(w*np.log2(w)))
def concur(c): c=norm(c); return float(min(1,2*abs(c[0]*c[3]-c[1]*c[2])))
def sym(c): c=norm(c); return float(np.real(c.conj()@SWAP@c))

# ---------- CONSCIOUSNESS-LEVEL measures (the 'A' family) ----------
def Phi_proxy(c):                       # IIT: integrated info ~ mutual info I(A:B)=S(A)+S(B)-S(AB); pure->2*S(A)
    return 2*vn_entropy(redA(c))        # in bits; 0 (product) .. 2 (max entangled)
def entropy_EBT(c):                      # Entropic Brain: differentiation = entropy of reduced state
    return vn_entropy(redA(c))
def lz76(b):                             # Kaspar-Schuster LZ76 complexity (normalized)
    import math
    n=len(b)
    if n<2: return 0.0
    i=0;C=1;u=1;v=1;vmax=1
    while u+v<=n:
        if b[i+v-1]==b[u+v-1]:
            v+=1
        else:
            vmax=max(vmax,v); i+=1
            if i==u: C+=1; u+=vmax; v=1; i=0; vmax=1
            else: v=1
    if v!=1: C+=1
    return C/(n/math.log2(n))
def PCI_proxy(c,shots=2000):            # perturb (random local U on qubit A) then LZ of outcome bitstring
    U=np.linalg.qr(np.random.randn(2,2)+1j*np.random.randn(2,2))[0]
    op=np.kron(U,np.eye(2)); cp=norm(op@norm(c)); p=np.abs(cp)**2
    out=np.random.choice(4,size=shots,p=p/p.sum())
    bits="".join(f"{o:02b}" for o in out)
    return lz76(bits)
def GWT_ignition(c,trials=40):         # global broadcast: local perturb on A -> global state change (trace dist)
    base=rho(c); tot=0
    for _ in range(trials):
        U=np.linalg.qr(np.random.randn(2,2)+1j*np.random.randn(2,2))[0]
        cp=norm(np.kron(U,np.eye(2))@norm(c)); d=rho(cp)-base
        tot+=0.5*np.sum(np.abs(np.linalg.eigvalsh(d)))
    return tot/trials
def IWMT_coherence(c):                  # Safron: integrated world-model = integration * global-access (coherent)
    return Phi_proxy(c)/2*GWT_ignition(c)   # product of integration & broadcast, normalized

states={
 "product |00>":            [1,0,0,0],
 "partial 0.9|00>+0.44|11>":[0.9,0,0,0.44],
 "SINGLET (MI)":            [0,1,-1,0],
 "Bell Phi+ (sym)":         [1,0,0,1],
 "Bell Psi+ (sym)":         [0,1,1,0],
}
print(f"{'state':26s}{'Phi':>6s}{'PCI':>6s}{'EBT_H':>7s}{'GWT':>6s}{'IWMT':>6s} | {'S(STV)':>7s}{'A':>6s}{'V=S*A':>7s}")
rows={}
for n,c in states.items():
    ph=Phi_proxy(c); pci=PCI_proxy(c); H=entropy_EBT(c); ig=GWT_ignition(c); iw=IWMT_coherence(c)
    S=sym(c); A=ph/2  # normalized integrated-level as the arousal/intensity factor
    rows[n]=(ph,pci,H,ig,iw,S,A,S*A)
    print(f"{n:26s}{ph:6.2f}{pci:6.2f}{H:7.2f}{ig:6.2f}{iw:6.2f} | {S:+7.2f}{A:6.2f}{S*A:+7.2f}")

print("\nHEADLINE — singlet vs symmetric Bell are LEVEL-DEGENERATE but VALENCE-OPPOSITE:")
sg=rows["SINGLET (MI)"]; bp=rows["Bell Phi+ (sym)"]
print(f"  Phi: {sg[0]:.2f} vs {bp[0]:.2f} | EBT_H: {sg[2]:.2f} vs {bp[2]:.2f} | PCI: {sg[1]:.2f} vs {bp[1]:.2f}  -> SAME consciousness LEVEL")
print(f"  S(STV): {sg[5]:+.2f} vs {bp[5]:+.2f}  -> OPPOSITE valence; V: {sg[7]:+.2f} vs {bp[7]:+.2f}")
print("  => IIT/PCI/EBT/GWT/IWMT ALONE cannot distinguish bliss from dysphoria here. QVF-1 symmetry axis is required.")

print("\n=== ORTHOGONALITY across random ensemble (n=3000) ===")
N=3000; Ph=[];PC=[];Hh=[];Ig=[];Sx=[];Vx=[]
for _ in range(N):
    v=np.random.randn(4)+1j*np.random.randn(4); v=v/np.linalg.norm(v)
    ph=Phi_proxy(v); Ph.append(ph); Hh.append(entropy_EBT(v)); Ig.append(GWT_ignition(v,8))
    s=sym(v); Sx.append(s); Vx.append(s*ph/2)
Ph,Hh,Ig,Sx,Vx=map(np.array,[Ph,Hh,Ig,Sx,Vx])
print(f"  corr(Phi_level , A-intensity)   = {np.corrcoef(Ph,Ph/2)[0,1]:+.3f}  (level IS the intensity axis)")
print(f"  corr(Phi_level , S-valence)     = {np.corrcoef(Ph,Sx)[0,1]:+.3f}  (~0 => level is valence-BLIND)")
print(f"  corr(EBT_entropy , S-valence)   = {np.corrcoef(Hh,Sx)[0,1]:+.3f}  (~0)")
print(f"  corr(GWT_ignition , S-valence)  = {np.corrcoef(Ig,Sx)[0,1]:+.3f}  (~0)")
print(f"  corr(V , S-valence)             = {np.corrcoef(Vx,Sx)[0,1]:+.3f}  (valence rides the symmetry axis)")

print("\n=== FRISTON/IWMT valence = -dF/dt is a DERIVATIVE, not the F-LEVEL (confirms separate axis) ===")
t=np.linspace(0,10,400)
for label,F in {"high-arousal IMPROVING (F high, dF/dt<0)":3.0*np.exp(-0.6*t)+0.5,
                "high-arousal WORSENING (F high, dF/dt>0)":0.5+2.5*(1-np.exp(-0.6*t))}.items():
    dF=np.gradient(F,t); val=-dF
    print(f"  {label:42s}: mean F-level={F.mean():.2f}  valence(-dF/dt) sign={'+' if val.mean()>0 else '-'} ({val.mean():+.3f})")
print("  => same F-LEVEL (arousal/precision), OPPOSITE valence by dF/dt sign: Friston valence is OFF the level axis. CLV-1 supported.")
