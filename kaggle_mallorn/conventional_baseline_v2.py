"""
MALLORN CONVENTIONAL BASELINE V2 (No Data Leakage)
===================================================
Excludes spec_encoded which leaks the answer in training.
This is the TRUE challenge: predict TDE from light curves only.
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier, HistGradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score, roc_auc_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("MALLORN CONVENTIONAL BASELINE V2 (No Data Leakage)")
print("Predicting TDE from light curves ONLY (no SpecType)")
print("=" * 70)

BANDS = ['u', 'g', 'r', 'i', 'z', 'y']

train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"\nTraining: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")
print(f"Class imbalance: 1:{int((1-train_log['target'].mean())/train_log['target'].mean())}")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

print("\nLoading light curves...")
train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')
train_lc = train_lc.rename(columns={'Time (MJD)': 'mjd'})
test_lc = test_lc.rename(columns={'Time (MJD)': 'mjd'})
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_features(obj_id, lc_dict, meta_row):
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id].copy().sort_values('mjd')
    f = {}
    
    # Metadata (NO spec_encoded!)
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    all_flux = df['Flux'].dropna().values
    all_err = df['Flux_err'].dropna().values
    all_mjd = df['mjd'].values
    
    if len(all_flux) < 5:
        return None
    
    # Global statistics
    f['n_obs'] = len(all_flux)
    f['flux_mean'] = np.mean(all_flux)
    f['flux_std'] = np.std(all_flux)
    f['flux_median'] = np.median(all_flux)
    f['flux_skew'] = stats.skew(all_flux)
    f['flux_kurtosis'] = stats.kurtosis(all_flux)
    f['flux_min'] = np.min(all_flux)
    f['flux_max'] = np.max(all_flux)
    f['flux_range'] = f['flux_max'] - f['flux_min']
    f['flux_iqr'] = np.percentile(all_flux, 75) - np.percentile(all_flux, 25)
    f['flux_mad'] = np.median(np.abs(all_flux - f['flux_median']))
    
    # SNR
    if len(all_err) > 0:
        min_len = min(len(all_flux), len(all_err))
        snr = np.abs(all_flux[:min_len]) / (all_err[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
        f['snr_std'] = np.std(snr)
    else:
        f['snr_mean'] = f['snr_max'] = f['snr_std'] = 5.0
    
    # Temporal
    f['duration'] = all_mjd[-1] - all_mjd[0]
    f['cadence_mean'] = np.mean(np.diff(all_mjd))
    f['cadence_std'] = np.std(np.diff(all_mjd))
    
    # Peak analysis (TDE signature)
    peak_idx = np.argmax(all_flux)
    f['peak_flux'] = all_flux[peak_idx]
    f['peak_time_frac'] = peak_idx / len(all_flux)
    f['time_to_peak'] = all_mjd[peak_idx] - all_mjd[0] if peak_idx > 0 else 0
    
    # Rise
    if peak_idx > 2:
        rise_flux = all_flux[:peak_idx+1]
        rise_time = all_mjd[:peak_idx+1]
        f['rise_rate'] = (rise_flux[-1] - rise_flux[0]) / (rise_time[-1] - rise_time[0] + 1e-8)
        f['rise_duration'] = rise_time[-1] - rise_time[0]
    else:
        f['rise_rate'] = f['rise_duration'] = 0
    
    # Fade (TDE t^-5/3 law)
    if peak_idx < len(all_flux) - 3:
        fade_flux = all_flux[peak_idx:]
        fade_time = all_mjd[peak_idx:]
        f['fade_rate'] = (fade_flux[-1] - fade_flux[0]) / (fade_time[-1] - fade_time[0] + 1e-8)
        f['fade_duration'] = fade_time[-1] - fade_time[0]
        
        positive_fade = fade_flux[fade_flux > 0]
        if len(positive_fade) > 3:
            log_flux = np.log(positive_fade)
            log_time = np.log(np.arange(1, len(positive_fade) + 1))
            slope, intercept, r, p, se = stats.linregress(log_time, log_flux)
            f['fade_slope'] = slope
            f['fade_r2'] = r**2
            f['tde_match'] = max(0, 1 - np.abs(slope - (-5/3)) / 2)
        else:
            f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
    else:
        f['fade_rate'] = f['fade_duration'] = 0
        f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
    
    # Variability
    diffs = np.diff(all_flux)
    f['diff_mean'] = np.mean(np.abs(diffs))
    f['diff_std'] = np.std(diffs)
    
    if len(all_flux) > 2 and len(all_err) > 2:
        min_len = min(len(all_flux), len(all_err))
        residuals = (all_flux[:min_len] - f['flux_mean']) / (all_err[:min_len] + 1e-8)
        f['stetson_k'] = np.mean(np.abs(residuals)) / np.sqrt(np.mean(residuals**2) + 1e-8)
    else:
        f['stetson_k'] = 1.0
    
    if len(all_flux) > 3:
        ac = np.corrcoef(all_flux[:-1], all_flux[1:])[0, 1]
        f['autocorr'] = ac if not np.isnan(ac) else 0
    else:
        f['autocorr'] = 0
    
    # Per-band features
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) >= 2:
            bf = band_df['Flux'].values
            f[f'b_{band}_mean'] = np.mean(bf)
            f[f'b_{band}_std'] = np.std(bf)
            f[f'b_{band}_max'] = np.max(bf)
            f[f'b_{band}_n'] = len(bf)
        else:
            f[f'b_{band}_mean'] = f[f'b_{band}_std'] = f[f'b_{band}_max'] = 0
            f[f'b_{band}_n'] = 0
    
    # Colors
    blue = f.get('b_u_mean', 0) + f.get('b_g_mean', 0)
    red = f.get('b_i_mean', 0) + f.get('b_z_mean', 0) + f.get('b_y_mean', 0)
    f['blue_red'] = blue / (red + 1e-8) if red != 0 else 1.0
    f['color_gr'] = f.get('b_g_mean', 0) - f.get('b_r_mean', 0)
    f['color_ri'] = f.get('b_r_mean', 0) - f.get('b_i_mean', 0)
    
    # Flux sign fractions
    f['frac_pos'] = np.mean(all_flux > 0)
    f['frac_neg'] = np.mean(all_flux < 0)
    f['frac_zero'] = np.mean(np.abs(all_flux) < f['flux_std'])
    
    # FFT (periodicity - AGN more periodic)
    if len(all_flux) > 10:
        fft_v = np.abs(np.fft.fft(all_flux - f['flux_mean']))
        f['fft_max'] = np.max(fft_v[1:len(fft_v)//2])
        f['fft_mean'] = np.mean(fft_v[1:len(fft_v)//2])
    else:
        f['fft_max'] = f['fft_mean'] = 0
    
    return f

print("\nExtracting features...")
train_f, train_y = [], []
for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict, r)
    if feat:
        train_f.append(feat)
        train_y.append(r['target'])
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

test_f, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_features(r['object_id'], test_lc_dict, r)
    if feat:
        test_f.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 1000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_train = pd.DataFrame(train_f)
y_train = np.array(train_y)
X_test = pd.DataFrame(test_f)

common = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common].fillna(0)
X_test = X_test[common].fillna(0)

print(f"\nFeatures: {len(common)}")

# Training
print("\n" + "=" * 70)
print("TRAINING (5-Fold CV)")
print("=" * 70)

scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

models = {
    'RF': RandomForestClassifier(n_estimators=300, max_depth=10, min_samples_leaf=3,
                                  class_weight='balanced', random_state=42, n_jobs=-1),
    'HGB': HistGradientBoostingClassifier(learning_rate=0.05, max_iter=300, max_depth=8,
                                           min_samples_leaf=10, random_state=42)
}

oof = {n: np.zeros(len(X_train)) for n in models}
test_p = {n: np.zeros(len(X_test)) for n in models}
scores = {n: [] for n in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr, y_train)):
    Xtr, Xval = X_tr[tr_idx], X_tr[val_idx]
    ytr, yval = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models.items():
        model.fit(Xtr, ytr)
        vp = model.predict_proba(Xval)[:, 1]
        oof[name][val_idx] = vp
        test_p[name] += model.predict_proba(X_te)[:, 1] / 5
        
        best = max(f1_score(yval, vp >= th) for th in np.linspace(0.1, 0.5, 21))
        scores[name].append(best)
    
    print(f"  Fold {fold+1}: RF={scores['RF'][-1]:.4f}, HGB={scores['HGB'][-1]:.4f}")

# Results
print("\n" + "=" * 70)
print("MODEL RESULTS (OOF)")
print("=" * 70)

for name in models:
    print(f"\n{name}: Mean F1 = {np.mean(scores[name]):.4f} ± {np.std(scores[name]):.4f}")
    
    best_f1, best_th = 0, 0.3
    for th in np.linspace(0.05, 0.5, 46):
        f1 = f1_score(y_train, oof[name] >= th)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    preds = oof[name] >= best_th
    prec = precision_score(y_train, preds)
    rec = recall_score(y_train, preds)
    auc = roc_auc_score(y_train, oof[name])
    
    print(f"  OOF F1: {best_f1:.4f} @ {best_th:.3f}")
    print(f"  Precision: {prec:.4f}, Recall: {rec:.4f}, AUC: {auc:.4f}")

# Ensemble
oof_ens = 0.5 * oof['RF'] + 0.5 * oof['HGB']
test_ens = 0.5 * test_p['RF'] + 0.5 * test_p['HGB']

print("\n" + "=" * 70)
print("ENSEMBLE")
print("=" * 70)

best_f1, best_th = 0, 0.3
for th in np.linspace(0.05, 0.5, 46):
    f1 = f1_score(y_train, oof_ens >= th)
    if f1 > best_f1:
        best_f1, best_th = f1, th

preds = oof_ens >= best_th
prec = precision_score(y_train, preds)
rec = recall_score(y_train, preds)
auc = roc_auc_score(y_train, oof_ens)

print(f"\nENSEMBLE OOF F1: {best_f1:.4f} @ {best_th:.3f}")
print(f"Precision: {prec:.4f}, Recall: {rec:.4f}, AUC: {auc:.4f}")

# Feature importance
print("\n" + "=" * 70)
print("TOP 20 FEATURES")
print("=" * 70)

rf = RandomForestClassifier(n_estimators=300, max_depth=10, class_weight='balanced', random_state=42, n_jobs=-1)
rf.fit(X_tr, y_train)
imp = pd.Series(rf.feature_importances_, index=X_train.columns).sort_values(ascending=False)
for i, (feat, val) in enumerate(imp.head(20).items()):
    print(f"  {i+1:2d}. {feat:25s} {val:.4f}")

# TDE vs Non-TDE analysis
print("\n" + "=" * 70)
print("TDE vs NON-TDE FEATURE COMPARISON")
print("=" * 70)

key_feats = ['tde_match', 'fade_slope', 'fade_r2', 'Z', 'flux_mad', 'blue_red']
for feat in key_feats:
    if feat in X_train.columns:
        tde = X_train.loc[y_train == 1, feat].mean()
        non = X_train.loc[y_train == 0, feat].mean()
        sep = abs(tde - non) / (X_train[feat].std() + 1e-8)
        print(f"  {feat:20s}: TDE={tde:8.4f}, Non={non:8.4f}, Sep={sep:.2f}σ")

# Save
y_pred = (test_ens >= best_th).astype(int)
submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_conventional_v2.csv', index=False)

print(f"\n{'='*70}")
print(f"SUBMISSION: submission_conventional_v2.csv")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")
print(f"{'='*70}")

print("\n" + "=" * 70)
print("WHY THE PLATEAU? ANALYSIS")
print("=" * 70)

print("\n1. WITHOUT spec_encoded, the task is MUCH harder")
print("   - spec_encoded was 49.5% of the importance!")
print("   - Now we must detect TDE from light curve patterns only")

print("\n2. KEY DISCRIMINATING FEATURES:")
for feat in imp.head(5).index:
    tde = X_train.loc[y_train == 1, feat].mean()
    non = X_train.loc[y_train == 0, feat].mean()
    diff = (tde - non) / (non + 1e-8) * 100
    print(f"   {feat}: TDE={tde:.4f}, Non={non:.4f}, Diff={diff:+.1f}%")

print("\n3. THE 0.75 PLATEAU likely comes from:")
print("   - Limited feature separation (most <0.5σ)")
print("   - Class imbalance (1:19)")
print("   - AGN variability mimics TDE patterns")
print("   - Incomplete light curves")

print("\n4. TI SIGMA OPPORTUNITIES:")
print("   - Uncertainty quantification (φ dimension)")
print("   - Contradiction detection (Myrion)")
print("   - Multi-valued truth states for edge cases")

print("\n✅ CONVENTIONAL BASELINE V2 COMPLETE")
