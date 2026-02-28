"""
TI Heart Disease v5 — XGBoost + LightGBM + HGB Deadline Ensemble
XGBoost 3.2.0 + LightGBM 4.6.0 confirmed available in environment.
2-fold CV on full 630k. Target: 90-93% OOF.
Feb 28, 2026 DEADLINE DAY
"""
import sys, os, time, warnings
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
warnings.filterwarnings('ignore')

import numpy as np
import pandas as pd
import xgboost as xgb
import lightgbm as lgb
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import StratifiedKFold
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import accuracy_score

print("="*70)
print("TI HEART v5 — XGB+LGB+HGB DEADLINE SPRINT")
print(f"XGBoost {xgb.__version__} | LightGBM {lgb.__version__}")
print("="*70)

DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'data', 'kaggle_s6e2')
train = pd.read_csv(os.path.join(DATA_DIR, 'train.csv'))
test  = pd.read_csv(os.path.join(DATA_DIR, 'test.csv'))
y     = (train['Heart Disease'] == 'Presence').astype(int).values
ids   = test['id'].values
Xr    = train.drop(columns=['id','Heart Disease'])
Xte   = test.drop(columns=['id'])

PHI = 1.61803398875

def featurize(df):
    a=df['Age'].values.astype(float); sx=df['Sex'].values.astype(float)
    cp=df['Chest pain type'].values.astype(float); bp=df['BP'].values.astype(float)
    ch=df['Cholesterol'].values.astype(float); fb=df['FBS over 120'].values.astype(float)
    ek=df['EKG results'].values.astype(float); mh=df['Max HR'].values.astype(float)
    ea=df['Exercise angina'].values.astype(float); st=df['ST depression'].values.astype(float)
    sl=df['Slope of ST'].values.astype(float); nv=df['Number of vessels fluro'].values.astype(float)
    th=df['Thallium'].values.astype(float)
    raw = np.column_stack([a,sx,cp,bp,ch,fb,ek,mh,ea,st,sl,nv,th])
    ohe = np.column_stack([(cp==1),(cp==2),(cp==3),(cp==4),(ek==0),(ek==2),
                           (sl==1),(sl==2),(sl==3),(th==3),(th==6),(th==7),
                           (nv==0),(nv==1),(nv==2),(nv==3)]).astype(float)
    ixn = np.column_stack([
        a*st*ea, nv*(th==7), (cp==4)*st, mh/np.clip(220-a,80,220),
        bp*mh/10000, (th==7)*a/60, ch*a/10000, np.log1p(abs(st)*a),
        (a-42)/(PHI*42), (nv>=2), (nv>=2)*(th==7), a*sx, nv*st,
        (sl==2)*st, (cp==4)*ea, (ch<200), np.clip(220-a-mh,0,100),
        nv*nv, st*st, th*nv, a*nv/10,
    ]).astype(float)
    t5 = np.column_stack([nv,th,cp,st,ea])
    po = np.column_stack([t5[:,i]*t5[:,j] for i in range(5) for j in range(i,5)])
    return np.hstack([raw,ohe,ixn,po])

print("[1] Building features...")
t0=time.time()
Xf=featurize(Xr); Xft=featurize(Xte)
print(f"  {Xf.shape[1]} features in {time.time()-t0:.1f}s")

sc=StandardScaler(); Xs=sc.fit_transform(Xf); Xts=sc.transform(Xft)
cv=StratifiedKFold(n_splits=2,shuffle=True,random_state=42)
oof={k:np.zeros(len(Xf)) for k in ['xgb','lgb','hgb']}
prd={k:np.zeros(len(Xft)) for k in ['xgb','lgb','hgb']}

xp=dict(n_estimators=300,learning_rate=0.05,max_depth=6,subsample=0.8,
        colsample_bytree=0.8,reg_alpha=0.1,reg_lambda=1.0,
        eval_metric='logloss',tree_method='hist',random_state=42,n_jobs=-1)
lp=dict(n_estimators=300,learning_rate=0.05,max_depth=6,num_leaves=63,
        subsample=0.8,colsample_bytree=0.8,reg_alpha=0.1,reg_lambda=1.0,
        random_state=42,n_jobs=-1,verbose=-1)
hp=dict(learning_rate=0.04,max_iter=200,max_depth=8,min_samples_leaf=20,
        l2_regularization=0.2,max_features=0.9,random_state=42)

print("[2] Training 2-fold ensemble...")
for fold,(tr,val) in enumerate(cv.split(Xf,y)):
    print(f"\n  Fold {fold+1}/2")
    Xtr,Xvl,ytr,yvl = Xf[tr],Xf[val],y[tr],y[val]

    t=time.time()
    m=xgb.XGBClassifier(**xp)
    m.fit(Xtr,ytr,eval_set=[(Xvl,yvl)],verbose=False)
    oof['xgb'][val]=m.predict_proba(Xvl)[:,1]
    prd['xgb']+=m.predict_proba(Xft)[:,1]/2
    print(f"  XGB: {accuracy_score(yvl,oof['xgb'][val]>=0.5):.4f} ({time.time()-t:.1f}s)")

    t=time.time()
    m2=lgb.LGBMClassifier(**lp)
    m2.fit(Xtr,ytr,eval_set=[(Xvl,yvl)],
           callbacks=[lgb.early_stopping(40,verbose=False),lgb.log_evaluation(-1)])
    oof['lgb'][val]=m2.predict_proba(Xvl)[:,1]
    prd['lgb']+=m2.predict_proba(Xft)[:,1]/2
    print(f"  LGB: {accuracy_score(yvl,oof['lgb'][val]>=0.5):.4f} ({time.time()-t:.1f}s)")

    t=time.time()
    m3=HistGradientBoostingClassifier(**hp)
    m3.fit(Xs[tr],ytr)
    oof['hgb'][val]=m3.predict_proba(Xs[val])[:,1]
    prd['hgb']+=m3.predict_proba(Xts)[:,1]/2
    print(f"  HGB: {accuracy_score(yvl,oof['hgb'][val]>=0.5):.4f} ({time.time()-t:.1f}s)")

print("\n[3] Computing ensemble...")
wts={}
for k in ['xgb','lgb','hgb']:
    ba,bt=0,0.5
    for t in np.linspace(0.3,0.7,81):
        a=accuracy_score(y,oof[k]>=t)
        if a>ba: ba,bt=a,t
    wts[k]=ba
    print(f"  {k.upper()}: {ba:.4f}")

wt=sum(wts.values())
oe=sum(oof[k]*wts[k]/wt for k in wts)
pe=sum(prd[k]*wts[k]/wt for k in wts)
ba,bt=0,0.5
for t in np.linspace(0.3,0.7,81):
    a=accuracy_score(y,oe>=t)
    if a>ba: ba,bt=a,t

print(f"\n{'='*60}")
print(f"ENSEMBLE OOF = {ba:.4f} @ thresh={bt:.3f}")
print(f"  v4 baseline:  0.8877")
print(f"  v5 XGB+LGB:   {ba:.4f}  ({(ba-0.8877)*100:+.2f} pp)")
print(f"{'='*60}")

yp=(pe>=bt).astype(int)
sub=pd.DataFrame({'id':ids,'Heart Disease':np.where(yp==1,'Presence','Absence')})
out=os.path.join(os.path.dirname(__file__),'submission_heart_v5_xgb_lgb.csv')
sub.to_csv(out,index=False)
print(f"\n>>> SUBMIT: {out}")
print(f"    Presence: {yp.sum():,}/{len(yp):,} ({yp.mean()*100:.1f}%)")
print("="*70)
