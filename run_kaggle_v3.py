import pandas as pd, numpy as np, time
from sklearn.model_selection import StratifiedKFold
from sklearn.metrics import accuracy_score
import xgboost as xgb
import lightgbm as lgb

t0 = time.time()
train = pd.read_csv('data/kaggle_s6e2/train.csv')
test = pd.read_csv('data/kaggle_s6e2/test.csv')

rename = {'Age':'age','Sex':'sex','Chest pain type':'cp','BP':'trestbps','Cholesterol':'chol',
    'FBS over 120':'fbs','EKG results':'restecg','Max HR':'thalach','Exercise angina':'exang',
    'ST depression':'oldpeak','Slope of ST':'slope','Number of vessels fluro':'ca',
    'Thallium':'thal','Heart Disease':'target'}
train.rename(columns=rename, inplace=True)
test.rename(columns={k:v for k,v in rename.items() if k!='Heart Disease'}, inplace=True)
train['target'] = (train['target'].str.strip().str.lower()=='presence').astype(int)
test_ids = test['id'].values

def eng(df):
    d = df.copy()
    d['age_hr_ratio'] = d['age']/(d['thalach']+1)
    d['heart_reserve'] = 220-d['age']-d['thalach']
    d['max_hr_pct'] = d['thalach']/(220-d['age']+1e-8)
    d['exercise_risk'] = d['exang']*d['oldpeak']
    d['vessel_thal'] = d['ca']+(d['thal']>=7).astype(int)*2
    d['cardiac_stress'] = d['oldpeak']*d['slope']*(1+d['exang'])
    return d

train_eng, test_eng = eng(train), eng(test)
fcols = [c for c in train_eng.columns if c not in ('target','id')]
X, y = train_eng[fcols].values, train_eng['target'].values
Xt = test_eng[fcols].values

skf = StratifiedKFold(n_splits=3, shuffle=True, random_state=42)
oof_xgb, oof_lgb = np.zeros(len(y)), np.zeros(len(y))
test_xgb, test_lgb = np.zeros(len(Xt)), np.zeros(len(Xt))

for fold,(tr_idx,val_idx) in enumerate(skf.split(X,y)):
    t1=time.time()
    Xtr,Xv,ytr,yv = X[tr_idx],X[val_idx],y[tr_idx],y[val_idx]
    
    mx = xgb.XGBClassifier(n_estimators=300,max_depth=5,learning_rate=0.08,subsample=0.8,
        colsample_bytree=0.7,min_child_weight=5,gamma=0.1,reg_alpha=0.1,reg_lambda=1.0,
        random_state=42,eval_metric='logloss',n_jobs=-1,tree_method='hist')
    mx.fit(Xtr,ytr)
    oof_xgb[val_idx] = mx.predict_proba(Xv)[:,1]
    test_xgb += mx.predict_proba(Xt)[:,1]/3
    
    ml = lgb.LGBMClassifier(n_estimators=300,max_depth=-1,learning_rate=0.08,subsample=0.8,
        colsample_bytree=0.7,min_child_samples=20,num_leaves=31,reg_alpha=0.1,reg_lambda=1.0,
        random_state=42,verbose=-1,n_jobs=-1)
    ml.fit(Xtr,ytr)
    oof_lgb[val_idx] = ml.predict_proba(Xv)[:,1]
    test_lgb += ml.predict_proba(Xt)[:,1]/3
    
    print(f"Fold {fold+1}: XGB={accuracy_score(yv,(oof_xgb[val_idx]>=0.5).astype(int)):.4f}, LGB={accuracy_score(yv,(oof_lgb[val_idx]>=0.5).astype(int)):.4f} ({time.time()-t1:.0f}s)")

print(f"\nOOF XGB: {accuracy_score(y,(oof_xgb>=0.5).astype(int)):.4f}")
print(f"OOF LGB: {accuracy_score(y,(oof_lgb>=0.5).astype(int)):.4f}")

best_w,best_acc=0.5,0
for w in np.arange(0,1.01,0.05):
    a=accuracy_score(y,((w*oof_xgb+(1-w)*oof_lgb)>=0.5).astype(int))
    if a>best_acc: best_w,best_acc=w,a
print(f"Best blend w_xgb={best_w:.2f}: {best_acc:.4f}")

blend=best_w*oof_xgb+(1-best_w)*oof_lgb
best_t,best_ta=0.5,0
for t in np.arange(0.40,0.60,0.005):
    a=accuracy_score(y,(blend>=t).astype(int))
    if a>best_ta: best_t,best_ta=t,a
print(f"Best threshold={best_t:.3f}: {best_ta:.4f}")

tb=best_w*test_xgb+(1-best_w)*test_lgb
preds=(tb>=best_t).astype(int)
sub=pd.DataFrame({'id':test_ids,'Heart Disease':preds})
sub.to_csv('submission.csv',index=False)
print(f"\nSubmission: {len(sub)} rows, {preds.sum()} positive ({preds.mean()*100:.1f}%)")
print(f"Final CV accuracy: {best_ta:.4f} ({best_ta*100:.2f}%)")
print(f"Time: {time.time()-t0:.0f}s")

fi=np.argsort(mx.feature_importances_)[::-1]
print("\nTop features:")
for i in fi[:8]: print(f"  {fcols[i]:25s} {mx.feature_importances_[i]:.4f}")
