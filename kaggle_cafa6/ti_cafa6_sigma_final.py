"""
TI CAFA 6 - SIGMA FINAL
=======================
Bio-tuned TAF + 100 GO terms + BLOSUM homology
Optimized for completion
"""

import numpy as np
import pandas as pd
from collections import Counter, defaultdict
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI CAFA 6 - SIGMA FINAL")
print("="*70)

TAF_T = 0.5  # Bio-tuned temperature
LCC_042, LCC_085 = 0.42, 0.85

AA_H = {'A':1.8,'R':-4.5,'N':-3.5,'D':-3.5,'C':2.5,'Q':-3.5,'E':-3.5,'G':-0.4,
        'H':-3.2,'I':4.5,'L':3.8,'K':-3.9,'M':1.9,'F':2.8,'P':-1.6,'S':-0.8,
        'T':-0.7,'W':-0.9,'Y':-1.3,'V':4.2}
AAS = 'ARNDCQEGHILKMFPSTWYV'
BLOSUM = {'hydro':'AILMFWV','polar':'STYCNQ','pos':'RKH','neg':'DE','arom':'FWY'}

def parse_fasta(fp):
    seqs = {}
    cid, cs = None, []
    for l in open(fp):
        if l[0]=='>':
            if cid: seqs[cid] = ''.join(cs)
            ps = l[1:].split('|')
            cid = ps[1] if len(ps)>1 else ps[0].split()[0]
            cs = []
        else: cs.append(l.strip())
    if cid: seqs[cid] = ''.join(cs)
    return seqs

def bio_taf(x):
    if len(x)<3: return .5,.5,.5,.5
    xr = max(x)-min(x)
    xn = 2*(x-min(x))/xr-1 if xr>0 else np.zeros_like(x)
    t,fn = np.maximum(0,xn), np.maximum(0,-xn)
    phi = np.exp(-xn**2/TAF_T)
    psi = np.concatenate([[0],np.tanh(np.abs(np.diff(xn)))])
    nm = np.sqrt(t**2+fn**2+phi**2+psi**2+1e-10)
    return np.mean(t/nm), np.mean(fn/nm), np.mean(phi/nm), np.mean(psi/nm)

def holes(x):
    if len(x)<5: return .5,.5,.5,.5
    exp = np.convolve(x,np.ones(5)/5,mode='same')
    I = float(np.mean(np.abs(x-exp))/(np.std(x)+1e-8))
    E = float(np.mean((exp>np.median(exp))&(x<np.median(x))))
    ac = np.corrcoef(x[:-1],x[1:])[0,1] if len(x)>3 else 0
    L = float(1-np.abs(ac if not np.isnan(ac) else 0))
    G = float(np.clip(np.mean(np.abs(np.diff(x)))/2,0,1))
    return I,E,L,G

def extract(seq):
    if len(seq)<10: return None
    f, n = {}, len(seq)
    f['len'] = np.log1p(n)
    cts = Counter(seq)
    for aa in AAS: f[f'aa_{aa}'] = cts.get(aa,0)/n
    h = np.array([AA_H.get(a,0) for a in seq])
    f['h_mean'], f['h_std'] = np.mean(h), np.std(h)
    
    # Bio-tuned TAF
    t,fn,phi,psi = bio_taf(h)
    f['taf_T'], f['taf_F'], f['taf_phi'], f['taf_psi'] = t, fn, phi, psi
    f['taf_cert'] = 1-phi
    
    # Anti-GILE Holes
    I,E,L,G = holes(h)
    f['I_hole'], f['E_hole'], f['L_hole'], f['G_hole'] = I, E, L, G
    f['tot_hole'] = (I+E+L+G)/4
    
    # LCC
    mx = np.max(np.abs(h))+1e-10
    nrm = np.abs(h)/mx
    f['lcc_042'], f['lcc_085'] = np.mean(nrm>LCC_042), np.mean(nrm>LCC_085)
    
    # BLOSUM homology groups
    for g,aas in BLOSUM.items(): f[f'bl_{g}'] = sum(1 for a in seq if a in aas)/n
    
    # Entropy
    pr = np.array(list(cts.values()))/n
    f['entropy'] = -np.sum(pr*np.log2(pr+1e-10))/np.log2(20)
    
    # Structure
    f['helix'] = sum(1 for a in seq if a in 'AELM')/n
    f['sheet'] = sum(1 for a in seq if a in 'VIY')/n
    
    # Regional TAF
    th = n//3
    if th>5:
        f['h_N'], f['h_C'] = np.mean(h[:th]), np.mean(h[-th:])
        _,_,pN,psN = bio_taf(h[:th])
        _,_,pC,psC = bio_taf(h[-th:])
        f['taf_phi_N'], f['taf_phi_C'] = pN, pC
    
    # TI synergy
    f['ti_syn'] = f['taf_cert']*0.3 + (1-f['tot_hole'])*0.3 + f['lcc_085']*0.2 + f['entropy']*0.2
    f['ti_conf'] = f['taf_cert']*(1-f['I_hole'])
    return f

print("\nLoading data...")
trn = parse_fasta('train_sequences.fasta')
tst = parse_fasta('test_sequences.fasta')
print(f"Train: {len(trn)}, Test: {len(tst)}")

terms = pd.read_csv('train_terms.tsv',sep='\t',header=0,names=['id','term','asp'])
prot_terms = defaultdict(set)
for _,r in terms.iterrows(): prot_terms[r['id']].add(r['term'])
tc = terms['term'].value_counts()
TOP = 100
top_terms = tc.head(TOP).index.tolist()
print(f"Targeting top {TOP} GO terms")

print("\nExtracting features...")
trf, tri = [], []
for i,(pid,s) in enumerate(trn.items()):
    f = extract(s)
    if f: trf.append(f); tri.append(pid)
    if (i+1)%20000==0: print(f"  Train: {i+1}")
tsf, tsi = [], []
for i,(pid,s) in enumerate(tst.items()):
    f = extract(s)
    if f: tsf.append(f); tsi.append(pid)
    if (i+1)%50000==0: print(f"  Test: {i+1}")

Xtr = pd.DataFrame(trf, index=tri)
Xts = pd.DataFrame(tsf, index=tsi)
cols = list(set(Xtr.columns)&set(Xts.columns))
Xtr, Xts = Xtr[cols].fillna(0), Xts[cols].fillna(0)
print(f"Features: {len(cols)}")

print("\nTraining classifiers...")
sc = StandardScaler()
Xtr_s, Xts_s = sc.fit_transform(Xtr), sc.transform(Xts)
preds = defaultdict(dict)

for i,tm in enumerate(top_terms):
    y = np.array([1 if tm in prot_terms.get(p,set()) else 0 for p in tri])
    if y.sum()<30: continue
    clf = LogisticRegression(class_weight='balanced', max_iter=150, C=0.5, random_state=42)
    clf.fit(Xtr_s, y)
    pr = clf.predict_proba(Xts_s)[:,1]
    for pid,p in zip(tsi, pr):
        if p>0.04: preds[pid][tm] = p
    if (i+1)%20==0: print(f"  {i+1}/{TOP}")

print(f"\nPredictions: {len(preds)} proteins")

# Feature importance
print("\n" + "="*70)
print("TI SIGMA IMPORTANCE")
print("="*70)
y_ex = np.array([1 if top_terms[0] in prot_terms.get(p,set()) else 0 for p in tri])
rf = RandomForestClassifier(n_estimators=50, max_depth=6, class_weight='balanced', random_state=42, n_jobs=-1)
rf.fit(Xtr_s, y_ex)
imp = pd.Series(rf.feature_importances_, index=cols).sort_values(ascending=False)

def cat(f):
    if 'taf_' in f: return 'TAF'
    if 'hole' in f.lower(): return 'HOLE'
    if 'lcc_' in f: return 'LCC'
    if 'ti_' in f: return 'TI'
    if 'bl_' in f: return 'BLOSUM'
    return 'CONV'

cats = defaultdict(float)
for f,v in imp.items(): cats[cat(f)] += v
tot = sum(imp)

print("\nImportance by category:")
for c in ['TAF','HOLE','LCC','TI','BLOSUM','CONV']:
    if c in cats:
        pct = cats[c]/tot*100
        mk = "★" if c!='CONV' else " "
        print(f"  {mk}{c:<6}: {pct:5.1f}%")

ti_imp = sum(v for k,v in cats.items() if k!='CONV')
print(f"\n  TOTAL TI SIGMA: {ti_imp/tot*100:.1f}%")

print("\nTop 15 features:")
for i,(f,v) in enumerate(imp.head(15).items()):
    mk = "★" if cat(f)!='CONV' else " "
    print(f"  {mk}{i+1:2d}. [{cat(f):<5}] {f:<20} {v:.4f}")

# TI separation
print("\n" + "="*70)
print("TI FEATURE SEPARATION")
print("="*70)
for f in ['taf_phi','taf_psi','taf_cert','I_hole','L_hole','tot_hole','lcc_085','ti_syn','bl_hydro']:
    if f in Xtr.columns:
        pos, neg = Xtr.loc[y_ex==1, f].mean(), Xtr.loc[y_ex==0, f].mean()
        sep = abs(pos-neg)/(Xtr[f].std()+1e-8)
        d = "+" if pos>neg else "-"
        print(f"  {f:<15}: {d}{sep:.2f}σ")

# Submission
print("\n" + "="*70)
print("SUBMISSION")
print("="*70)
rows = []
for pid,tps in preds.items():
    for tm,pr in sorted(tps.items(), key=lambda x:-x[1]):
        rows.append(f"{pid}\t{tm}\t{pr:.6f}")

with open('submission_ti_sigma_final.tsv', 'w') as f:
    for r in rows: f.write(r+'\n')

print(f"\nRows: {len(rows):,}")
print(f"Proteins: {len(preds):,}")
print(f"File: submission_ti_sigma_final.tsv")

try:
    bl = sum(1 for _ in open('submission_ti_sigma_fast.tsv'))
    print(f"\n📊 Comparison:")
    print(f"  Baseline (v1): {bl:,} rows")
    print(f"  Enhanced (v2): {len(rows):,} rows")
    pct = (len(rows)-bl)/bl*100
    print(f"  Change: {pct:+.1f}%")
except: pass

print("\n✅ TI SIGMA FINAL COMPLETE")
