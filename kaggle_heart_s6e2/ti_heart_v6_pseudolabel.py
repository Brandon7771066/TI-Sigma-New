"""
TI Heart Disease v6 — Pseudo-Labeling Sprint
=============================================
Pseudo-labeling: use v5 model's high-confidence test predictions as extra
training data. Only add samples with predicted probability > 0.97 or < 0.03
(the RESOLVED zone — outside the Tralse zone).

This is Gap #1 from Paper #341: Implementable TODAY, zero new packages.

Expected gain: +0.3–0.8pp above v5's 88.79%.

Feb 28, 2026 — COMPETITION DEADLINE
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
print("TI HEART v6 — PSEUDO-LABELING (Gap #1 from Paper #341)")
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

# ─── Phase 1: Train base model to get test pseudo-labels ───────────────────
print("\n[2] Phase 1 — Base XGB to generate pseudo-labels...")
xp=dict(n_estimators=300,learning_rate=0.05,max_depth=6,subsample=0.8,
        colsample_bytree=0.8,reg_alpha=0.1,reg_lambda=1.0,
        eval_metric='logloss',tree_method='hist',random_state=42,n_jobs=-1)

# Quick 2-fold to get test probabilities
cv=StratifiedKFold(n_splits=2,shuffle=True,random_state=42)
test_prob = np.zeros(len(Xft))
for fold,(tr,val) in enumerate(cv.split(Xf,y)):
    m=xgb.XGBClassifier(**xp)
    m.fit(Xf[tr],y[tr],eval_set=[(Xf[val],y[val])],verbose=False)
    test_prob += m.predict_proba(Xft)[:,1] / 2
    print(f"  Fold {fold+1}: val_acc={accuracy_score(y[val], m.predict_proba(Xf[val])[:,1]>=0.5):.4f}")

# Identify RESOLVED zone test samples (outside Tralse zone)
# Using LCC_TRALSE analog: samples with prob > 0.97 or < 0.03 are "True" or "False"
RESOLVED_HIGH = 0.97  # above this = Presence (True)
RESOLVED_LOW  = 0.03  # below this = Absence (False)

resolved_mask = (test_prob > RESOLVED_HIGH) | (test_prob < RESOLVED_LOW)
pseudo_X      = Xft[resolved_mask]
pseudo_y      = (test_prob[resolved_mask] > 0.5).astype(int)
print(f"\n  Resolved test samples: {resolved_mask.sum():,} / {len(test_prob):,}")
print(f"  ({resolved_mask.mean()*100:.1f}% of test set outside Tralse zone)")
print(f"  Pseudo Presence: {pseudo_y.sum():,} | Pseudo Absence: {(1-pseudo_y).sum():,}")

# ─── Phase 2: Retrain on train + pseudo-labels ──────────────────────────────
print(f"\n[3] Phase 2 — Retrain with pseudo-labeled data...")
Xf_aug = np.vstack([Xf, pseudo_X])
y_aug  = np.concatenate([y, pseudo_y])
print(f"  Augmented training set: {len(y_aug):,} samples")
print(f"  ({len(pseudo_y):,} pseudo-labeled samples added)")

# 2-fold CV on ORIGINAL training data only (to measure OOF accuracy fairly)
oof_xgb = np.zeros(len(Xf)); oof_lgb = np.zeros(len(Xf)); oof_hgb = np.zeros(len(Xf))
prd_xgb = np.zeros(len(Xft)); prd_lgb = np.zeros(len(Xft)); prd_hgb = np.zeros(len(Xft))
sc = StandardScaler(); Xs_aug = sc.fit_transform(Xf_aug); Xts = sc.transform(Xft)

lp=dict(n_estimators=300,learning_rate=0.05,max_depth=6,num_leaves=63,
        subsample=0.8,colsample_bytree=0.8,reg_alpha=0.1,reg_lambda=1.0,
        random_state=42,n_jobs=-1,verbose=-1)
hp=dict(learning_rate=0.04,max_iter=200,max_depth=8,min_samples_leaf=20,
        l2_regularization=0.2,max_features=0.9,random_state=42)

# For OOF measurement: split indices are on original training set only
# Model trains on augmented data
n_orig = len(Xf)
for fold,(tr_idx,val_idx) in enumerate(cv.split(Xf,y)):
    print(f"\n  Fold {fold+1}/2")
    # Augmented training: original fold train + all pseudo labels
    aug_tr  = np.concatenate([tr_idx, np.arange(n_orig, len(Xf_aug))])
    Xtr_aug = Xf_aug[aug_tr]; ytr_aug = y_aug[aug_tr]
    Xvl     = Xf[val_idx]; yvl = y[val_idx]

    t=time.time()
    mx=xgb.XGBClassifier(**xp)
    mx.fit(Xtr_aug,ytr_aug,eval_set=[(Xvl,yvl)],verbose=False)
    oof_xgb[val_idx]=mx.predict_proba(Xvl)[:,1]
    prd_xgb+=mx.predict_proba(Xft)[:,1]/2
    print(f"  XGB: {accuracy_score(yvl,oof_xgb[val_idx]>=0.5):.4f} ({time.time()-t:.1f}s)")

    t=time.time()
    ml=lgb.LGBMClassifier(**lp)
    ml.fit(Xtr_aug,ytr_aug,eval_set=[(Xvl,yvl)],
           callbacks=[lgb.early_stopping(40,verbose=False),lgb.log_evaluation(-1)])
    oof_lgb[val_idx]=ml.predict_proba(Xvl)[:,1]
    prd_lgb+=ml.predict_proba(Xft)[:,1]/2
    print(f"  LGB: {accuracy_score(yvl,oof_lgb[val_idx]>=0.5):.4f} ({time.time()-t:.1f}s)")

    t=time.time()
    mh=HistGradientBoostingClassifier(**hp)
    mh.fit(Xs_aug[aug_tr],ytr_aug)
    oof_hgb[val_idx]=mh.predict_proba(Xts[val_idx] if False else sc.transform(Xvl))[:,1]
    prd_hgb+=mh.predict_proba(Xts)[:,1]/2
    print(f"  HGB: {accuracy_score(yvl,oof_hgb[val_idx]>=0.5):.4f} ({time.time()-t:.1f}s)")

print("\n[4] Final ensemble...")
wts={}
for k,oo in [('xgb',oof_xgb),('lgb',oof_lgb),('hgb',oof_hgb)]:
    ba,bt=0,0.5
    for t in np.linspace(0.3,0.7,81):
        a=accuracy_score(y,oo>=t)
        if a>ba: ba,bt=a,t
    wts[k]=ba
    print(f"  {k.upper()}: {ba:.4f}")

wt=sum(wts.values())
pe=(prd_xgb*wts['xgb']+prd_lgb*wts['lgb']+prd_hgb*wts['hgb'])/wt
oe=(oof_xgb*wts['xgb']+oof_lgb*wts['lgb']+oof_hgb*wts['hgb'])/wt
ba,bt=0,0.5
for t in np.linspace(0.3,0.7,81):
    a=accuracy_score(y,oe>=t)
    if a>ba: ba,bt=a,t

print(f"\n{'='*60}")
print(f"PSEUDO-LABEL ENSEMBLE OOF = {ba:.4f} @ thresh={bt:.3f}")
print(f"  v5 (no pseudo-labeling):  0.8879")
print(f"  v6 (pseudo-labeling):     {ba:.4f}  ({(ba-0.8879)*100:+.2f} pp)")
print(f"  Pseudo samples added: {len(pseudo_y):,} ({resolved_mask.mean()*100:.1f}% of test)")
print(f"{'='*60}")

yp=(pe>=bt).astype(int)
sub=pd.DataFrame({'id':ids,'Heart Disease':np.where(yp==1,'Presence','Absence')})
out=os.path.join(os.path.dirname(__file__),'submission_heart_v6_pseudolabel.csv')
sub.to_csv(out,index=False)
print(f"\n>>> DEADLINE SUBMISSION: {out}")
print(f"    Presence: {yp.sum():,}/{len(yp):,} ({yp.mean()*100:.1f}%)")
print("="*70)
