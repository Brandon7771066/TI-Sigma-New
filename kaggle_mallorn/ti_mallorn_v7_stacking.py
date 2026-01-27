"""
TI MALLORN v7 - META-LEARNER STACKING
Two-level stacking with diverse base models + meta-learner
Combines TI features with ensemble power
Target: F1 > 0.75
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import (
    HistGradientBoostingClassifier, 
    RandomForestClassifier, 
    ExtraTreesClassifier,
    GradientBoostingClassifier,
    AdaBoostClassifier
)
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v7 - META-LEARNER STACKING")
print("Two-level stacking for superior performance")
print("="*70)

# TI Constants
LCC_THRESHOLD_042 = 0.42
LCC_THRESHOLD_085 = 0.85
LCC_THRESHOLD_TT = 0.8464
TDE_POWER_LAW = -5/3

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Training: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

print("Loading light curves...")
train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')

train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_features(object_id, lc_dict):
    """Comprehensive TI feature extraction"""
    if object_id not in lc_dict:
        return {}
    
    obj = lc_dict[object_id].sort_values('Time (MJD)').copy()
    if len(obj) < 5:
        return {}
    
    f = {}
    t = obj['Time (MJD)'].values
    flux = obj['Flux'].values
    err = obj['Flux_err'].values
    n = len(flux)
    
    # Basic stats
    f['n_obs'] = n
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_min'] = np.min(flux)
    f['flux_max'] = np.max(flux)
    f['flux_range'] = f['flux_max'] - f['flux_min']
    f['flux_iqr'] = np.percentile(flux, 75) - np.percentile(flux, 25)
    f['flux_mad'] = np.median(np.abs(flux - np.median(flux)))
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurt'] = stats.kurtosis(flux)
    
    for p in [5, 10, 25, 75, 90, 95]:
        f[f'flux_p{p}'] = np.percentile(flux, p)
    
    # SNR
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_std'] = np.std(snr)
    f['snr_median'] = np.median(snr)
    
    weights = 1 / (err**2 + 1e-8)
    f['flux_wmean'] = np.average(flux, weights=weights)
    
    # Temporal
    f['duration'] = t.max() - t.min()
    dt = np.diff(t)
    if len(dt) > 0:
        f['cadence_mean'] = np.mean(dt)
        f['cadence_std'] = np.std(dt)
    
    # Error patterns
    f['err_mean'] = np.mean(err)
    f['err_std'] = np.std(err)
    f['err_skew'] = stats.skew(err)
    if np.std(flux) > 0 and np.std(err) > 0:
        f['flux_err_corr'] = np.corrcoef(flux, err)[0, 1]
    else:
        f['flux_err_corr'] = 0
    
    # Existence Intensity Tensor
    lambda_decay = 0.01
    persistence = np.exp(-lambda_decay * (t.max() - t))
    constraint = 1 / (err + 1e-8)
    constraint = constraint / (constraint.max() + 1e-8)
    
    xi_raw = np.abs(flux) * persistence * constraint
    f['xi_total'] = np.sum(xi_raw)
    f['xi_mean'] = np.mean(xi_raw)
    f['xi_max'] = np.max(xi_raw)
    f['xi_std'] = np.std(xi_raw)
    
    xi_tt = n / (f['duration'] + 1e-8)
    xi_ff = np.mean(np.abs(flux))
    f['xi_tt'] = xi_tt
    f['xi_ff'] = xi_ff
    f['xi_invariant'] = np.sqrt(xi_tt**2 + xi_ff**2)
    
    # TDE shape
    peak_idx = np.argmax(flux)
    f['peak_position'] = peak_idx / n
    f['peak_flux'] = flux[peak_idx]
    f['peak_snr'] = snr[peak_idx]
    f['time_to_peak'] = t[peak_idx] - t[0]
    f['time_from_peak'] = t[-1] - t[peak_idx]
    f['peak_time_ratio'] = f['time_to_peak'] / (f['duration'] + 1e-8)
    
    # Rise
    if peak_idx > 2:
        rise = flux[:peak_idx+1]
        rise_t = t[:peak_idx+1]
        f['rise_rate'] = (rise[-1] - rise[0]) / (rise_t[-1] - rise_t[0] + 1e-8)
        if len(rise) > 1:
            f['rise_max_rate'] = np.max(np.diff(rise) / (np.diff(rise_t) + 1e-8))
        else:
            f['rise_max_rate'] = 0
    else:
        f['rise_rate'] = 0
        f['rise_max_rate'] = 0
    
    # Decline + power-law
    if peak_idx < n - 3:
        decline = flux[peak_idx:]
        decline_t = t[peak_idx:]
        f['decline_rate'] = (decline[-1] - decline[0]) / (decline_t[-1] - decline_t[0] + 1e-8)
        
        if len(decline) > 4:
            rel_t = decline_t - decline_t[0] + 1
            log_t = np.log(rel_t)
            log_f = np.log(np.abs(decline) + 1e-8)
            
            try:
                slope, intercept, r, p, se = stats.linregress(log_t, log_f)
                f['decline_power_slope'] = slope
                f['decline_power_r2'] = r**2
                f['tde_slope_match'] = 1 / (1 + np.abs(slope - TDE_POWER_LAW))
            except:
                f['decline_power_slope'] = 0
                f['decline_power_r2'] = 0
                f['tde_slope_match'] = 0
    else:
        f['decline_rate'] = 0
        f['decline_power_slope'] = 0
        f['decline_power_r2'] = 0
        f['tde_slope_match'] = 0
    
    f['rate_asymmetry'] = abs(f.get('rise_rate', 0)) / (abs(f.get('decline_rate', 1e-8)) + 1e-8)
    f['duration_asymmetry'] = f['time_to_peak'] / (f['time_from_peak'] + 1e-8)
    
    # LCC thresholds
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    f['lcc_042'] = np.sum(np.abs(norm) > LCC_THRESHOLD_042)
    f['lcc_085'] = np.sum(np.abs(norm) > LCC_THRESHOLD_085)
    f['lcc_tt'] = np.sum(np.abs(norm) > LCC_THRESHOLD_TT)
    f['lcc_042_ratio'] = f['lcc_042'] / n
    f['lcc_085_ratio'] = f['lcc_085'] / n
    f['lcc_tt_ratio'] = f['lcc_tt'] / n
    f['tralse_zone'] = f['lcc_042'] - f['lcc_085']
    f['tralse_ratio'] = f['tralse_zone'] / (f['lcc_042'] + 1)
    
    # Spectral fingerprints
    f['agn_fingerprint'] = 1 / (f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8) + 1)
    f['tde_fingerprint'] = f.get('tde_slope_match', 0) * f.get('rate_asymmetry', 1)
    
    # Holistic features
    f['holistic_tde_1'] = f['peak_flux'] * f.get('rate_asymmetry', 1) * (1 - f['peak_position'])
    f['holistic_tde_2'] = f.get('lcc_085_ratio', 0) * f.get('tde_slope_match', 0)
    f['holistic_tde_3'] = f['xi_max'] * f.get('decline_power_r2', 0)
    
    # Non-local correlations
    mid = n // 2
    if mid > 2 and mid*2 <= n:
        try:
            f['half_correlation'] = np.corrcoef(flux[:mid], flux[mid:mid*2])[0,1]
        except:
            f['half_correlation'] = 0
    else:
        f['half_correlation'] = 0
    
    if n > 3:
        f['autocorr_1'] = np.corrcoef(flux[:-1], flux[1:])[0,1]
    else:
        f['autocorr_1'] = 0
    
    # GILE
    f['gile_width'] = f['flux_std'] / (f['flux_range'] + 1e-8)
    sacred_low = f['flux_mean'] - 2*f['flux_std']/3
    sacred_high = f['flux_mean'] + f['flux_std']/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / n
    
    # Variability
    f['excess_var'] = (np.var(flux) - np.mean(err**2)) / (f['flux_mean']**2 + 1e-8)
    f['amp_ratio'] = f['flux_range'] / (np.abs(f['flux_mean']) + 1e-8)
    f['cv'] = f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8)
    
    if n > 2:
        residual = (flux - f['flux_mean']) / (err + 1e-8)
        f['stetson_j'] = np.sum(np.sign(residual[:-1] * residual[1:]) * 
                                np.sqrt(np.abs(residual[:-1] * residual[1:])))
    else:
        f['stetson_j'] = 0
    
    # Per-filter
    filter_means = {}
    for filt in ['u', 'g', 'r', 'i', 'z', 'y']:
        fd = obj[obj['Filter'] == filt] if 'Filter' in obj.columns else pd.DataFrame()
        if len(fd) > 0:
            ff = fd['Flux'].values
            f[f'{filt}_n'] = len(fd)
            f[f'{filt}_mean'] = np.mean(ff)
            f[f'{filt}_std'] = np.std(ff)
            f[f'{filt}_max'] = np.max(ff)
            f[f'{filt}_range'] = np.ptp(ff)
            f[f'{filt}_frac'] = len(fd) / n
            filter_means[filt] = f[f'{filt}_mean']
            
            if len(ff) > 3 and np.std(ff) > 0:
                norm_f = (ff - np.mean(ff)) / np.std(ff)
                f[f'{filt}_lcc_042'] = np.sum(np.abs(norm_f) > LCC_THRESHOLD_042) / len(ff)
            else:
                f[f'{filt}_lcc_042'] = 0
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_range'] = 0
            f[f'{filt}_frac'] = 0
            f[f'{filt}_lcc_042'] = 0
            filter_means[filt] = 0
    
    # Color
    blue_flux = filter_means.get('u', 0) + filter_means.get('g', 0)
    red_flux = filter_means.get('r', 0) + filter_means.get('i', 0) + filter_means.get('z', 0)
    f['blue_red_ratio'] = blue_flux / (red_flux + 1e-8)
    f['color_e_dimension'] = (blue_flux - red_flux) / (blue_flux + red_flux + 1e-8)
    f['g_r'] = filter_means.get('g', 0) - filter_means.get('r', 0)
    f['r_i'] = filter_means.get('r', 0) - filter_means.get('i', 0)
    f['u_g'] = filter_means.get('u', 0) - filter_means.get('g', 0)
    
    return f

# Extract features
print("\nExtracting features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    feat['Z_squared'] = feat['Z']**2
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    train_feats.append(feat)
    if (i+1) % 500 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    feat['Z_squared'] = feat['Z']**2
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    test_feats.append(feat)
    if (i+1) % 1000 == 0: print(f"  Test: {i+1}/{len(test_log)}")

train_df = pd.DataFrame(train_feats)
test_df = pd.DataFrame(test_feats)

cols = [c for c in train_df.columns if c != 'object_id']
X = train_df[cols].fillna(0)
X_test = test_df[cols].fillna(0)
y = train_log['target'].values

print(f"\nFeatures: {len(cols)}")

scaler = StandardScaler()
X_s = scaler.fit_transform(X)
X_test_s = scaler.transform(X_test)

# ============ TWO-LEVEL STACKING ============
print("\n" + "="*60)
print("LEVEL 1: BASE MODELS (5-fold OOF predictions)")
print("="*60)

n_folds = 5
skf = StratifiedKFold(n_splits=n_folds, shuffle=True, random_state=42)

# Define base models
base_models = {
    'hgb_deep': HistGradientBoostingClassifier(
        max_iter=1000, max_depth=12, learning_rate=0.015,
        l2_regularization=0.005, max_bins=255, min_samples_leaf=3,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=80, random_state=42
    ),
    'hgb_medium': HistGradientBoostingClassifier(
        max_iter=600, max_depth=7, learning_rate=0.03,
        l2_regularization=0.02, max_bins=255, min_samples_leaf=8,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=50, random_state=43
    ),
    'hgb_shallow': HistGradientBoostingClassifier(
        max_iter=400, max_depth=4, learning_rate=0.05,
        l2_regularization=0.1, max_bins=128, min_samples_leaf=15,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=30, random_state=44
    ),
    'rf': RandomForestClassifier(
        n_estimators=500, max_depth=15, min_samples_leaf=2,
        class_weight='balanced', random_state=45, n_jobs=-1
    ),
    'et': ExtraTreesClassifier(
        n_estimators=500, max_depth=18, min_samples_leaf=2,
        class_weight='balanced', random_state=46, n_jobs=-1
    ),
    'rf_shallow': RandomForestClassifier(
        n_estimators=300, max_depth=8, min_samples_leaf=10,
        class_weight='balanced', random_state=47, n_jobs=-1
    ),
    'gb': GradientBoostingClassifier(
        n_estimators=200, max_depth=5, learning_rate=0.05,
        min_samples_leaf=10, random_state=48
    ),
}

n_models = len(base_models)
oof_meta = np.zeros((len(X), n_models))
test_meta = np.zeros((len(X_test), n_models))

for m_idx, (name, model) in enumerate(base_models.items()):
    print(f"\n  Training {name}...")
    test_preds_fold = np.zeros(len(X_test))
    
    for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
        Xt, Xv = X_s[ti], X_s[vi]
        yt, yv = y[ti], y[vi]
        
        model_clone = type(model)(**model.get_params())
        model_clone.fit(Xt, yt)
        
        oof_meta[vi, m_idx] = model_clone.predict_proba(Xv)[:, 1]
        test_preds_fold += model_clone.predict_proba(X_test_s)[:, 1] / n_folds
    
    test_meta[:, m_idx] = test_preds_fold
    
    # Calculate OOF F1 for this model
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.1, 0.7, 0.01):
        f1 = f1_score(y, (oof_meta[:, m_idx] >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    print(f"    {name}: OOF F1 = {best_f1:.4f} @ {best_th:.2f}")

print("\n" + "="*60)
print("LEVEL 2: META-LEARNER TRAINING")
print("="*60)

# Create meta features (base model predictions + top original features)
# Select top 20 most important features to add to meta
# (Use RF from last fold for importance)
rf_model = base_models['rf']
rf_model.fit(X_s, y)
importance = rf_model.feature_importances_
top_feat_idx = np.argsort(importance)[::-1][:20]
top_feat_names = [cols[i] for i in top_feat_idx]

print(f"Top features for meta-learner: {top_feat_names[:10]}...")

# Create meta datasets
X_meta = np.hstack([oof_meta, X_s[:, top_feat_idx]])
X_test_meta = np.hstack([test_meta, X_test_s[:, top_feat_idx]])

print(f"Meta features: {X_meta.shape[1]} (7 base models + 20 top features)")

# Meta-learner: Logistic Regression (captures linear combinations)
meta_lr = LogisticRegression(C=1.0, class_weight='balanced', max_iter=1000, random_state=42)

# Also train a second meta-learner: HGB for non-linear combinations
meta_hgb = HistGradientBoostingClassifier(
    max_iter=200, max_depth=4, learning_rate=0.05,
    l2_regularization=0.1, class_weight='balanced',
    early_stopping=True, validation_fraction=0.15,
    n_iter_no_change=30, random_state=42
)

# Train meta-learners with CV
oof_meta_lr = np.zeros(len(X))
oof_meta_hgb = np.zeros(len(X))
test_meta_lr = np.zeros(len(X_test))
test_meta_hgb = np.zeros(len(X_test))

meta_scores_lr = []
meta_scores_hgb = []

for fold, (ti, vi) in enumerate(skf.split(X_meta, y)):
    Xt_m, Xv_m = X_meta[ti], X_meta[vi]
    yt, yv = y[ti], y[vi]
    
    # LR meta-learner
    meta_lr_clone = LogisticRegression(C=1.0, class_weight='balanced', max_iter=1000, random_state=42)
    meta_lr_clone.fit(Xt_m, yt)
    oof_meta_lr[vi] = meta_lr_clone.predict_proba(Xv_m)[:, 1]
    test_meta_lr += meta_lr_clone.predict_proba(X_test_meta)[:, 1] / n_folds
    
    # HGB meta-learner
    meta_hgb_clone = HistGradientBoostingClassifier(
        max_iter=200, max_depth=4, learning_rate=0.05,
        l2_regularization=0.1, class_weight='balanced',
        early_stopping=True, validation_fraction=0.15,
        n_iter_no_change=30, random_state=42
    )
    meta_hgb_clone.fit(Xt_m, yt)
    oof_meta_hgb[vi] = meta_hgb_clone.predict_proba(Xv_m)[:, 1]
    test_meta_hgb += meta_hgb_clone.predict_proba(X_test_meta)[:, 1] / n_folds
    
    # Fold scores
    best_lr, _ = max([(f1_score(yv, (oof_meta_lr[vi] >= t).astype(int), zero_division=0), t) 
                      for t in np.arange(0.1, 0.7, 0.01)], key=lambda x: x[0])
    best_hgb, _ = max([(f1_score(yv, (oof_meta_hgb[vi] >= t).astype(int), zero_division=0), t) 
                       for t in np.arange(0.1, 0.7, 0.01)], key=lambda x: x[0])
    
    meta_scores_lr.append(best_lr)
    meta_scores_hgb.append(best_hgb)
    print(f"  Fold {fold+1}: Meta-LR F1={best_lr:.4f}, Meta-HGB F1={best_hgb:.4f}")

print(f"\nMeta-LR CV F1: {np.mean(meta_scores_lr):.4f} ± {np.std(meta_scores_lr):.4f}")
print(f"Meta-HGB CV F1: {np.mean(meta_scores_hgb):.4f} ± {np.std(meta_scores_hgb):.4f}")

# Final ensemble: blend meta-learners
final_oof = 0.5 * oof_meta_lr + 0.5 * oof_meta_hgb
final_test = 0.5 * test_meta_lr + 0.5 * test_meta_hgb

# Find optimal threshold
best_f1, best_th = 0, 0.5
threshold_results = []
for th in np.arange(0.05, 0.8, 0.005):
    f1 = f1_score(y, (final_oof >= th).astype(int), zero_division=0)
    threshold_results.append((th, f1))
    if f1 > best_f1:
        best_f1, best_th = f1, th

print("\n" + "="*60)
print("FINAL RESULTS")
print("="*60)

print(f"\nOptimal threshold: {best_th:.3f}")
print(f"Final Stacked OOF F1: {best_f1:.4f}")

# Compare to simple average
simple_avg = oof_meta.mean(axis=1)
best_simple_f1, _ = max([(f1_score(y, (simple_avg >= t).astype(int), zero_division=0), t) 
                          for t in np.arange(0.1, 0.7, 0.01)], key=lambda x: x[0])
print(f"Simple Average OOF F1: {best_simple_f1:.4f}")
print(f"Improvement from stacking: +{(best_f1 - best_simple_f1):.4f}")

# Predictions
pred = (final_test >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

# Save submission
sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v7.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v7.csv")

# Also save with different thresholds
for alt_th in [0.3, 0.35, 0.4, 0.45]:
    alt_pred = (final_test >= alt_th).astype(int)
    alt_sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': alt_pred})
    alt_sub.to_csv(f'submission_mallorn_v7_th{int(alt_th*100)}.csv', index=False)
    print(f"   Also saved: submission_mallorn_v7_th{int(alt_th*100)}.csv ({alt_pred.sum()} TDEs)")

# Base model comparison
print("\n" + "="*60)
print("BASE MODEL COMPARISON")
print("="*60)
for m_idx, name in enumerate(base_models.keys()):
    best_f1_m, _ = max([(f1_score(y, (oof_meta[:, m_idx] >= t).astype(int), zero_division=0), t) 
                        for t in np.arange(0.1, 0.7, 0.01)], key=lambda x: x[0])
    print(f"  {name:15s}: {best_f1_m:.4f}")
