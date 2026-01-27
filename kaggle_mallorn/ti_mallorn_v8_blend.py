"""
TI MALLORN v8 - OPTIMIZED WEIGHTED BLENDING
Learning from v7: Simple average > complex stacking
Use optimized weights based on individual model performance
Target: Maximize F1 through smart blending
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import (
    HistGradientBoostingClassifier, 
    RandomForestClassifier, 
    ExtraTreesClassifier,
    GradientBoostingClassifier
)
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.optimize import minimize
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v8 - OPTIMIZED WEIGHTED BLENDING")
print("Smart weight optimization based on F1")
print("="*70)

# TI Constants
LCC_THRESHOLD_042 = 0.42
LCC_THRESHOLD_085 = 0.85
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
    """Full TI feature extraction"""
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
    f['xi_invariant'] = np.sqrt((n / (f['duration'] + 1e-8))**2 + np.mean(np.abs(flux))**2)
    
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
    else:
        f['rise_rate'] = 0
    
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
    
    # LCC thresholds
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    f['lcc_042_ratio'] = np.sum(np.abs(norm) > LCC_THRESHOLD_042) / n
    f['lcc_085_ratio'] = np.sum(np.abs(norm) > LCC_THRESHOLD_085) / n
    f['tralse_ratio'] = (np.sum(np.abs(norm) > LCC_THRESHOLD_042) - np.sum(np.abs(norm) > LCC_THRESHOLD_085)) / (np.sum(np.abs(norm) > LCC_THRESHOLD_042) + 1)
    
    # Fingerprints
    f['tde_fingerprint'] = f.get('tde_slope_match', 0) * f.get('rate_asymmetry', 1)
    
    # Holistic features
    f['holistic_tde_1'] = f['peak_flux'] * f.get('rate_asymmetry', 1) * (1 - f['peak_position'])
    f['holistic_tde_2'] = f.get('lcc_085_ratio', 0) * f.get('tde_slope_match', 0)
    
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
            f[f'{filt}_frac'] = len(fd) / n
            filter_means[filt] = f[f'{filt}_mean']
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_frac'] = 0
            filter_means[filt] = 0
    
    # Color
    blue = filter_means.get('u', 0) + filter_means.get('g', 0)
    red = filter_means.get('r', 0) + filter_means.get('i', 0) + filter_means.get('z', 0)
    f['blue_red_ratio'] = blue / (red + 1e-8)
    f['g_r'] = filter_means.get('g', 0) - filter_means.get('r', 0)
    
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

# ============ TRAINING BASE MODELS ============
print("\n" + "="*60)
print("TRAINING BASE MODELS (5-fold OOF)")
print("="*60)

n_folds = 5
skf = StratifiedKFold(n_splits=n_folds, shuffle=True, random_state=42)

# Define diverse models
base_models = {
    'hgb1': HistGradientBoostingClassifier(
        max_iter=800, max_depth=10, learning_rate=0.02,
        l2_regularization=0.01, max_bins=255, min_samples_leaf=5,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=60, random_state=42
    ),
    'hgb2': HistGradientBoostingClassifier(
        max_iter=500, max_depth=6, learning_rate=0.04,
        l2_regularization=0.05, max_bins=200, min_samples_leaf=10,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=40, random_state=43
    ),
    'rf1': RandomForestClassifier(
        n_estimators=500, max_depth=12, min_samples_leaf=3,
        class_weight='balanced', random_state=44, n_jobs=-1
    ),
    'rf2': RandomForestClassifier(
        n_estimators=400, max_depth=8, min_samples_leaf=8,
        class_weight='balanced', random_state=45, n_jobs=-1
    ),
    'et1': ExtraTreesClassifier(
        n_estimators=500, max_depth=15, min_samples_leaf=2,
        class_weight='balanced', random_state=46, n_jobs=-1
    ),
    'et2': ExtraTreesClassifier(
        n_estimators=400, max_depth=10, min_samples_leaf=5,
        class_weight='balanced', random_state=47, n_jobs=-1
    ),
}

n_models = len(base_models)
oof_preds = {name: np.zeros(len(X)) for name in base_models}
test_preds = {name: np.zeros(len(X_test)) for name in base_models}
model_f1s = {}

for name, model in base_models.items():
    print(f"\n  Training {name}...")
    
    for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
        Xt, Xv = X_s[ti], X_s[vi]
        yt, yv = y[ti], y[vi]
        
        m = type(model)(**model.get_params())
        m.fit(Xt, yt)
        
        oof_preds[name][vi] = m.predict_proba(Xv)[:, 1]
        test_preds[name] += m.predict_proba(X_test_s)[:, 1] / n_folds
    
    # Calculate OOF F1
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.1, 0.7, 0.01):
        f1 = f1_score(y, (oof_preds[name] >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    model_f1s[name] = best_f1
    print(f"    {name}: OOF F1 = {best_f1:.4f} @ {best_th:.2f}")

# ============ WEIGHT OPTIMIZATION ============
print("\n" + "="*60)
print("OPTIMIZING BLEND WEIGHTS")
print("="*60)

# Stack OOF predictions
oof_matrix = np.column_stack([oof_preds[name] for name in base_models])
test_matrix = np.column_stack([test_preds[name] for name in base_models])

def neg_f1_loss(weights, oof_matrix, y):
    """Negative F1 loss for minimization"""
    weights = np.abs(weights)  # Ensure positive
    weights = weights / weights.sum()  # Normalize
    
    blend = np.dot(oof_matrix, weights)
    
    # Find best threshold
    best_f1 = 0
    for th in np.arange(0.1, 0.7, 0.02):
        f1 = f1_score(y, (blend >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1 = f1
    
    return -best_f1

# Initialize with equal weights
init_weights = np.ones(n_models) / n_models

# Also try performance-based initialization
perf_weights = np.array([model_f1s[name] for name in base_models])
perf_weights = perf_weights / perf_weights.sum()

print("\nTrying different weight initializations...")

best_overall_f1 = 0
best_weights = init_weights

# Try optimization from equal weights
result1 = minimize(
    neg_f1_loss, init_weights, args=(oof_matrix, y),
    method='Nelder-Mead', options={'maxiter': 500}
)
opt_weights1 = np.abs(result1.x)
opt_weights1 = opt_weights1 / opt_weights1.sum()
f1_1 = -result1.fun
print(f"  From equal weights: F1 = {f1_1:.4f}")

if f1_1 > best_overall_f1:
    best_overall_f1 = f1_1
    best_weights = opt_weights1

# Try optimization from performance weights
result2 = minimize(
    neg_f1_loss, perf_weights, args=(oof_matrix, y),
    method='Nelder-Mead', options={'maxiter': 500}
)
opt_weights2 = np.abs(result2.x)
opt_weights2 = opt_weights2 / opt_weights2.sum()
f1_2 = -result2.fun
print(f"  From perf weights: F1 = {f1_2:.4f}")

if f1_2 > best_overall_f1:
    best_overall_f1 = f1_2
    best_weights = opt_weights2

# Also try simple average
simple_avg = oof_matrix.mean(axis=1)
best_simple_f1, best_simple_th = 0, 0.5
for th in np.arange(0.1, 0.7, 0.01):
    f1 = f1_score(y, (simple_avg >= th).astype(int), zero_division=0)
    if f1 > best_simple_f1:
        best_simple_f1, best_simple_th = f1, th
print(f"  Simple average: F1 = {best_simple_f1:.4f}")

if best_simple_f1 > best_overall_f1:
    best_overall_f1 = best_simple_f1
    best_weights = np.ones(n_models) / n_models

# Also try rank-based weighting
ranks = np.column_stack([np.argsort(np.argsort(-oof_preds[name])) for name in base_models])
rank_avg = ranks.mean(axis=1)
rank_probs = (len(X) - rank_avg) / len(X)

best_rank_f1, best_rank_th = 0, 0.5
for th in np.arange(0.01, 0.3, 0.01):
    f1 = f1_score(y, (rank_probs >= th).astype(int), zero_division=0)
    if f1 > best_rank_f1:
        best_rank_f1, best_rank_th = f1, th
print(f"  Rank averaging: F1 = {best_rank_f1:.4f}")

print(f"\nFinal optimized weights:")
for i, name in enumerate(base_models):
    print(f"  {name}: {best_weights[i]:.4f}")

# ============ FINAL BLEND ============
print("\n" + "="*60)
print("FINAL RESULTS")
print("="*60)

# Create final blend
final_oof = np.dot(oof_matrix, best_weights)
final_test = np.dot(test_matrix, best_weights)

# Find optimal threshold
best_f1, best_th = 0, 0.5
for th in np.arange(0.05, 0.8, 0.005):
    f1 = f1_score(y, (final_oof >= th).astype(int), zero_division=0)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print(f"\nOptimal threshold: {best_th:.3f}")
print(f"Final OOF F1: {best_f1:.4f}")

# Predictions
pred = (final_test >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v8.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v8.csv")

# Also save rank-based if it's competitive
if best_rank_f1 > 0.35:
    rank_pred = (rank_probs >= best_rank_th).astype(int)
    
    # For test set
    test_ranks = np.column_stack([np.argsort(np.argsort(-test_preds[name])) for name in base_models])
    test_rank_avg = test_ranks.mean(axis=1)
    test_rank_probs = (len(X_test) - test_rank_avg) / len(X_test)
    test_rank_pred = (test_rank_probs >= best_rank_th).astype(int)
    
    rank_sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': test_rank_pred})
    rank_sub.to_csv('submission_mallorn_v8_rank.csv', index=False)
    print(f"   Also saved: submission_mallorn_v8_rank.csv ({test_rank_pred.sum()} TDEs)")

# Multiple thresholds
for alt_th in [0.25, 0.30, 0.35, 0.40]:
    alt_pred = (final_test >= alt_th).astype(int)
    alt_sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': alt_pred})
    alt_sub.to_csv(f'submission_mallorn_v8_th{int(alt_th*100)}.csv', index=False)
    print(f"   Also saved: submission_mallorn_v8_th{int(alt_th*100)}.csv ({alt_pred.sum()} TDEs)")

print("\n" + "="*60)
print("SUMMARY")
print("="*60)
print(f"Best individual model: {max(model_f1s, key=model_f1s.get)} ({max(model_f1s.values()):.4f})")
print(f"Simple average: {best_simple_f1:.4f}")
print(f"Optimized blend: {best_f1:.4f}")
print(f"Rank averaging: {best_rank_f1:.4f}")
