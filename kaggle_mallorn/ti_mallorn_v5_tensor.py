"""
TI MALLORN v5 - TENSOR THEORY ENHANCED
Applying TI Tensor Theory, LCC Thresholds, Non-Local Correlations
Target: F1 > 0.75
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier, ExtraTreesClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.ndimage import uniform_filter1d
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN SOLVER v5 - TENSOR THEORY ENHANCED")
print("Applying: Ξ Tensor, LCC Thresholds, Non-Local Correlations")
print("="*70)

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Training: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

# Load light curves
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

# Build lookup
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

# TI LCC Thresholds
LCC_THRESHOLD_042 = 0.42    # Detectable correlation
LCC_THRESHOLD_085 = 0.85    # Causal correlation
LCC_THRESHOLD_TT = 0.92**2  # True-Tralseness = 0.8464
TDE_POWER_LAW = -5/3       # TDE decay follows t^(-5/3)

def extract_ti_tensor_features(object_id, lc_dict):
    """TI Tensor Theory enhanced feature extraction"""
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
    
    # ============ BASIC STATISTICS ============
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
    
    # Percentiles
    for p in [5, 10, 25, 75, 90, 95]:
        f[f'flux_p{p}'] = np.percentile(flux, p)
    
    # ============ SIGNAL QUALITY ============
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_std'] = np.std(snr)
    f['snr_median'] = np.median(snr)
    
    # Weighted mean
    weights = 1 / (err**2 + 1e-8)
    f['flux_wmean'] = np.average(flux, weights=weights)
    
    # ============ TEMPORAL ============
    f['duration'] = t.max() - t.min()
    dt = np.diff(t)
    if len(dt) > 0:
        f['cadence_mean'] = np.mean(dt)
        f['cadence_std'] = np.std(dt)
        f['cadence_min'] = np.min(dt)
        f['cadence_max'] = np.max(dt)
        f['cadence_range'] = np.ptp(dt)
    
    # ============ TI EXISTENCE INTENSITY TENSOR (Ξ) ============
    # Ξ = Amplitude × Persistence × Constraint
    
    # Persistence: exponential decay from latest observation
    lambda_decay = 0.01  # decay rate
    persistence = np.exp(-lambda_decay * (t.max() - t))
    
    # Constraint: inverse of error (higher SNR = more constraining)
    constraint = 1 / (err + 1e-8)
    constraint = constraint / constraint.max()  # normalize
    
    # Existence Intensity components
    xi_raw = np.abs(flux) * persistence * constraint
    f['xi_total'] = np.sum(xi_raw)
    f['xi_mean'] = np.mean(xi_raw)
    f['xi_max'] = np.max(xi_raw)
    f['xi_std'] = np.std(xi_raw)
    
    # Temporal density (frequency dimension of tensor)
    xi_tt = n / f['duration'] if f['duration'] > 0 else 0
    f['xi_tt'] = xi_tt
    
    # Flux intensity (magnitude dimension)
    xi_ff = np.mean(np.abs(flux))
    f['xi_ff'] = xi_ff
    
    # Tensor invariant
    f['xi_invariant'] = np.sqrt(xi_tt**2 + xi_ff**2)
    
    # ============ TDE LIGHT CURVE SHAPE ============
    peak_idx = np.argmax(flux)
    f['peak_position'] = peak_idx / n
    f['peak_flux'] = flux[peak_idx]
    f['peak_snr'] = snr[peak_idx]
    
    f['time_to_peak'] = t[peak_idx] - t[0]
    f['time_from_peak'] = t[-1] - t[peak_idx]
    f['peak_time_ratio'] = f['time_to_peak'] / (f['duration'] + 1e-8)
    
    # Rise phase
    if peak_idx > 2:
        rise = flux[:peak_idx+1]
        rise_t = t[:peak_idx+1]
        f['rise_rate'] = (rise[-1] - rise[0]) / (rise_t[-1] - rise_t[0] + 1e-8)
        
        # Max instantaneous rise
        if len(rise) > 1:
            f['rise_max_rate'] = np.max(np.diff(rise) / (np.diff(rise_t) + 1e-8))
        else:
            f['rise_max_rate'] = 0
        
        # Rise smoothness
        if len(rise) > 3:
            smooth = uniform_filter1d(rise, min(3, len(rise)))
            f['rise_smoothness'] = 1 - np.std(rise - smooth) / (np.std(rise) + 1e-8)
        else:
            f['rise_smoothness'] = 0
    else:
        f['rise_rate'] = 0
        f['rise_max_rate'] = 0
        f['rise_smoothness'] = 0
    
    # Decline phase
    if peak_idx < n - 3:
        decline = flux[peak_idx:]
        decline_t = t[peak_idx:]
        f['decline_rate'] = (decline[-1] - decline[0]) / (decline_t[-1] - decline_t[0] + 1e-8)
        
        # Power-law fit for TDE decline (t^-5/3)
        if len(decline) > 4:
            # Shift time so peak is at t=1
            rel_t = decline_t - decline_t[0] + 1
            # Log-log fit
            log_t = np.log(rel_t)
            log_f = np.log(np.abs(decline) + 1e-8)
            
            try:
                slope, intercept, r, p, se = stats.linregress(log_t, log_f)
                f['decline_power_slope'] = slope
                f['decline_power_r2'] = r**2
                
                # How close to TDE signature (-5/3 ≈ -1.67)?
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
    
    # Asymmetry (TDEs: rapid rise, slow decline)
    f['rate_asymmetry'] = abs(f.get('rise_rate', 0)) / (abs(f.get('decline_rate', 1e-8)) + 1e-8)
    f['duration_asymmetry'] = f['time_to_peak'] / (f['time_from_peak'] + 1e-8)
    
    # ============ TI LCC THRESHOLDS ============
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    
    # Count observations exceeding each threshold
    f['lcc_042'] = np.sum(np.abs(norm) > LCC_THRESHOLD_042)
    f['lcc_085'] = np.sum(np.abs(norm) > LCC_THRESHOLD_085)
    f['lcc_tt'] = np.sum(np.abs(norm) > LCC_THRESHOLD_TT)  # True-Tralseness
    
    # As ratios
    f['lcc_042_ratio'] = f['lcc_042'] / n
    f['lcc_085_ratio'] = f['lcc_085'] / n
    f['lcc_tt_ratio'] = f['lcc_tt'] / n
    
    # Gradient between thresholds (TI "tralse zone" activity)
    f['tralse_zone'] = f['lcc_042'] - f['lcc_085']  # Events in uncertain zone
    f['tralse_ratio'] = f['tralse_zone'] / (f['lcc_042'] + 1)
    
    # ============ NON-LOCAL CORRELATIONS (LCC-inspired) ============
    
    # First-half to second-half correlation
    mid = n // 2
    if mid > 2:
        f['half_correlation'] = np.corrcoef(flux[:mid], flux[mid:mid*2])[0,1] if mid*2 <= n else 0
    else:
        f['half_correlation'] = 0
    
    # Rise to decline correlation (TDEs: negative correlation expected)
    if peak_idx > 2 and peak_idx < n - 3:
        rise_len = peak_idx
        decline_len = n - peak_idx - 1
        min_len = min(rise_len, decline_len)
        
        if min_len > 2:
            rise_seg = flux[:min_len]
            decline_seg = flux[peak_idx+1:peak_idx+1+min_len]
            
            try:
                f['rise_decline_corr'] = np.corrcoef(rise_seg, decline_seg[::-1])[0,1]
            except:
                f['rise_decline_corr'] = 0
        else:
            f['rise_decline_corr'] = 0
    else:
        f['rise_decline_corr'] = 0
    
    # Lag-1 autocorrelation
    if n > 3:
        f['autocorr_1'] = np.corrcoef(flux[:-1], flux[1:])[0,1]
    else:
        f['autocorr_1'] = 0
    
    # ============ GILE WIDTH (from TI Statistics) ============
    # Consciousness spread analog for light curve
    f['gile_width'] = f['flux_std'] / (f['flux_range'] + 1e-8)
    
    # Sacred interval (80% of normal activity)
    sacred_low = f['flux_mean'] - 2*f['flux_std']/3
    sacred_high = f['flux_mean'] + f['flux_std']/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / n
    
    # ============ VARIABILITY METRICS ============
    # Excess variance
    f['excess_var'] = (np.var(flux) - np.mean(err**2)) / (f['flux_mean']**2 + 1e-8)
    
    # Amplitude ratio
    f['amp_ratio'] = f['flux_range'] / (np.abs(f['flux_mean']) + 1e-8)
    
    # Coefficient of variation
    f['cv'] = f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8)
    
    # Stetson J
    if n > 2:
        residual = (flux - f['flux_mean']) / (err + 1e-8)
        f['stetson_j'] = np.sum(np.sign(residual[:-1] * residual[1:]) * 
                                np.sqrt(np.abs(residual[:-1] * residual[1:])))
    else:
        f['stetson_j'] = 0
    
    # ============ PER-FILTER FEATURES ============
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
            
            # Per-filter LCC
            if len(ff) > 3 and np.std(ff) > 0:
                norm_f = (ff - np.mean(ff)) / np.std(ff)
                f[f'{filt}_lcc_042'] = np.sum(np.abs(norm_f) > LCC_THRESHOLD_042) / len(ff)
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_range'] = 0
            f[f'{filt}_frac'] = 0
            f[f'{filt}_lcc_042'] = 0
    
    # ============ COLOR FEATURES ============
    # TDEs are characteristically blue
    if f.get('g_mean', 0) > 0 and f.get('r_mean', 0) > 0:
        f['g_r'] = f['g_mean'] - f['r_mean']
        f['g_r_ratio'] = f['g_mean'] / (f['r_mean'] + 1e-8)
    else:
        f['g_r'] = 0
        f['g_r_ratio'] = 1
    
    if f.get('r_mean', 0) > 0 and f.get('i_mean', 0) > 0:
        f['r_i'] = f['r_mean'] - f['i_mean']
    else:
        f['r_i'] = 0
    
    if f.get('i_mean', 0) > 0 and f.get('z_mean', 0) > 0:
        f['i_z'] = f['i_mean'] - f['z_mean']
    else:
        f['i_z'] = 0
    
    return f

# Extract features
print("\nExtracting TI Tensor features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_ti_tensor_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    
    # Z * EBV interaction
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    
    train_feats.append(feat)
    if (i+1) % 500 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_ti_tensor_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
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
print(f"TI Tensor features included: xi_*, lcc_*, tde_slope_match, gile_width, sacred_fraction")

scaler = StandardScaler()
X_s = scaler.fit_transform(X)
X_test_s = scaler.transform(X_test)

# Training with enhanced ensemble
print("\n" + "="*50)
print("TRAINING (TI Enhanced Ensemble)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

# Multiple models for diversity
oof_preds = {f'm{i}': np.zeros(len(X)) for i in range(4)}
test_preds = {f'm{i}': np.zeros(len(X_test)) for i in range(4)}

scores = []

for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
    Xt, Xv = X_s[ti], X_s[vi]
    yt, yv = y[ti], y[vi]
    
    # Model 1: Deep HGB
    m1 = HistGradientBoostingClassifier(
        max_iter=800, max_depth=10, learning_rate=0.02,
        l2_regularization=0.01, max_bins=255, min_samples_leaf=5,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=60, random_state=42
    )
    m1.fit(Xt, yt)
    oof_preds['m0'][vi] = m1.predict_proba(Xv)[:, 1]
    test_preds['m0'] += m1.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 2: Shallow HGB (regularized)
    m2 = HistGradientBoostingClassifier(
        max_iter=400, max_depth=5, learning_rate=0.05,
        l2_regularization=0.1, max_bins=128, min_samples_leaf=20,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=40, random_state=43
    )
    m2.fit(Xt, yt)
    oof_preds['m1'][vi] = m2.predict_proba(Xv)[:, 1]
    test_preds['m1'] += m2.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 3: Random Forest
    m3 = RandomForestClassifier(
        n_estimators=400, max_depth=12, min_samples_leaf=3,
        class_weight='balanced', random_state=44, n_jobs=-1
    )
    m3.fit(Xt, yt)
    oof_preds['m2'][vi] = m3.predict_proba(Xv)[:, 1]
    test_preds['m2'] += m3.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 4: ExtraTrees
    m4 = ExtraTreesClassifier(
        n_estimators=400, max_depth=15, min_samples_leaf=3,
        class_weight='balanced', random_state=45, n_jobs=-1
    )
    m4.fit(Xt, yt)
    oof_preds['m3'][vi] = m4.predict_proba(Xv)[:, 1]
    test_preds['m3'] += m4.predict_proba(X_test_s)[:, 1] / 5
    
    # Blend (TI-weighted: emphasize ensemble diversity)
    blend = 0.35 * oof_preds['m0'][vi] + 0.25 * oof_preds['m1'][vi] + \
            0.25 * oof_preds['m2'][vi] + 0.15 * oof_preds['m3'][vi]
    
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.05, 0.8, 0.01):
        f1 = f1_score(yv, (blend >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    scores.append(best_f1)
    print(f"Fold {fold+1}: F1={best_f1:.4f} @ thresh={best_th:.2f}")

print(f"\nCV F1: {np.mean(scores):.4f} ± {np.std(scores):.4f}")

# Final blend
oof_blend = 0.35 * oof_preds['m0'] + 0.25 * oof_preds['m1'] + \
            0.25 * oof_preds['m2'] + 0.15 * oof_preds['m3']
test_blend = 0.35 * test_preds['m0'] + 0.25 * test_preds['m1'] + \
             0.25 * test_preds['m2'] + 0.15 * test_preds['m3']

# Optimal threshold search
best_f1, best_th = 0, 0.5
for th in np.arange(0.05, 0.8, 0.005):
    f1 = f1_score(y, (oof_blend >= th).astype(int), zero_division=0)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print(f"\nOptimal threshold: {best_th:.3f}")
print(f"OOF F1: {best_f1:.4f}")

pred = (test_blend >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v5.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v5.csv")

# Feature importance analysis
print("\n" + "="*50)
print("TOP FEATURES (by importance)")
print("="*50)

# Use last fold's RF for feature importance
feature_names = cols
importance = m3.feature_importances_
top_idx = np.argsort(importance)[::-1][:20]

for i, idx in enumerate(top_idx):
    print(f"{i+1:2d}. {feature_names[idx]:25s}: {importance[idx]:.4f}")
