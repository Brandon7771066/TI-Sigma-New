"""
TI MALLORN v6 - MYRION RESOLUTION + LCC EMPIRICAL TEST
Full TI Framework Integration:
- MR-based classification (outside indeterminate range)
- LCC thresholds as empirical markers
- DE-Photon Time / Jeff Time redshift interpretation
- Spectral fingerprinting without labels
- Noise pattern analysis (errors as information)
- Holistic (not additive) feature patterns
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
print("TI MALLORN v6 - MYRION RESOLUTION + LCC EMPIRICAL")
print("Full TI: MR Classification, LCC Test, Spectral Fingerprints, Noise Patterns")
print("="*70)

# ============ TI CONSTANTS ============
# Myrion Resolution Thresholds
PD_INDETERMINATE_LOW = -0.5   # Below this: leaning false
PD_INDETERMINATE_HIGH = 0.5   # Above this: leaning true
PD_CONCLUSIVE_FALSE = -2.0    # Strong refutation
PD_CONCLUSIVE_TRUE = 1.5      # Strong support

# LCC Thresholds (for empirical validation!)
LCC_THRESHOLD_042 = 0.42      # Minimum detectable correlation
LCC_THRESHOLD_085 = 0.85      # Causal correlation
LCC_THRESHOLD_TT = 0.92**2    # True-Tralseness = 0.8464

# TDE Physics
TDE_POWER_LAW = -5/3          # t^(-5/3) decay

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

train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_ti_mr_features(object_id, lc_dict):
    """
    TI Myrion Resolution enhanced feature extraction
    Key innovations:
    1. MR-based scoring (not binary)
    2. LCC threshold markers for empirical test
    3. DE-Photon Time / Jeff Time redshift features
    4. Spectral fingerprinting
    5. Noise/error pattern analysis
    6. Holistic interaction features
    """
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
    
    for p in [5, 10, 25, 75, 90, 95]:
        f[f'flux_p{p}'] = np.percentile(flux, p)
    
    # ============ SNR & WEIGHTED STATS ============
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_std'] = np.std(snr)
    f['snr_median'] = np.median(snr)
    
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
    
    # ============ NOISE PATTERN ANALYSIS (TI Innovation!) ============
    # The errors themselves may contain TDE signatures
    
    f['err_mean'] = np.mean(err)
    f['err_std'] = np.std(err)
    f['err_median'] = np.median(err)
    f['err_skew'] = stats.skew(err)
    f['err_kurt'] = stats.kurtosis(err)
    
    # Error-flux correlation (do errors scale with flux? Different for TDE vs AGN)
    if np.std(flux) > 0 and np.std(err) > 0:
        f['flux_err_corr'] = np.corrcoef(flux, err)[0, 1]
    else:
        f['flux_err_corr'] = 0
    
    # Error temporal pattern (do errors increase over time? Decrease?)
    if np.std(t) > 0 and np.std(err) > 0:
        f['err_time_corr'] = np.corrcoef(t, err)[0, 1]
    else:
        f['err_time_corr'] = 0
    
    # Error variability relative to flux variability
    f['err_flux_var_ratio'] = np.std(err) / (np.std(flux) + 1e-8)
    
    # ============ EXISTENCE INTENSITY TENSOR (Ξ) ============
    lambda_decay = 0.01
    persistence = np.exp(-lambda_decay * (t.max() - t))
    constraint = 1 / (err + 1e-8)
    constraint = constraint / (constraint.max() + 1e-8)
    
    xi_raw = np.abs(flux) * persistence * constraint
    f['xi_total'] = np.sum(xi_raw)
    f['xi_mean'] = np.mean(xi_raw)
    f['xi_max'] = np.max(xi_raw)
    f['xi_std'] = np.std(xi_raw)
    
    # Frequency-Magnitude unified (per user guidance)
    xi_tt = n / (f['duration'] + 1e-8)
    xi_ff = np.mean(np.abs(flux))
    f['xi_tt'] = xi_tt
    f['xi_ff'] = xi_ff
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
        
        if len(rise) > 1:
            f['rise_max_rate'] = np.max(np.diff(rise) / (np.diff(rise_t) + 1e-8))
        else:
            f['rise_max_rate'] = 0
    else:
        f['rise_rate'] = 0
        f['rise_max_rate'] = 0
    
    # Decline phase with power-law fit
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
                
                # MR-style scoring: How conclusive is the power-law match?
                slope_deviation = np.abs(slope - TDE_POWER_LAW)
                if slope_deviation < 0.3:
                    f['tde_mr_score'] = 1.5  # Strong TDE evidence (PD > 1.5)
                elif slope_deviation < 0.6:
                    f['tde_mr_score'] = 0.75  # Moderate evidence
                elif slope_deviation < 1.0:
                    f['tde_mr_score'] = 0.0  # Indeterminate
                else:
                    f['tde_mr_score'] = -1.0  # Against TDE
            except:
                f['decline_power_slope'] = 0
                f['decline_power_r2'] = 0
                f['tde_slope_match'] = 0
                f['tde_mr_score'] = 0
    else:
        f['decline_rate'] = 0
        f['decline_power_slope'] = 0
        f['decline_power_r2'] = 0
        f['tde_slope_match'] = 0
        f['tde_mr_score'] = 0
    
    # Asymmetry
    f['rate_asymmetry'] = abs(f.get('rise_rate', 0)) / (abs(f.get('decline_rate', 1e-8)) + 1e-8)
    f['duration_asymmetry'] = f['time_to_peak'] / (f['time_from_peak'] + 1e-8)
    
    # ============ LCC THRESHOLDS (EMPIRICAL TEST!) ============
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    
    f['lcc_042'] = np.sum(np.abs(norm) > LCC_THRESHOLD_042)
    f['lcc_085'] = np.sum(np.abs(norm) > LCC_THRESHOLD_085)
    f['lcc_tt'] = np.sum(np.abs(norm) > LCC_THRESHOLD_TT)
    
    f['lcc_042_ratio'] = f['lcc_042'] / n
    f['lcc_085_ratio'] = f['lcc_085'] / n
    f['lcc_tt_ratio'] = f['lcc_tt'] / n
    
    # Tralse zone (between 0.42 and 0.85)
    f['tralse_zone'] = f['lcc_042'] - f['lcc_085']
    f['tralse_ratio'] = f['tralse_zone'] / (f['lcc_042'] + 1)
    
    # ============ SPECTRAL FINGERPRINTING (without SpecType labels) ============
    # Different source types have characteristic light curve patterns
    
    # AGN fingerprint: Low variability, no clear peak
    f['agn_fingerprint'] = 1 / (f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8) + 1)
    
    # SN fingerprint: Single bright peak, symmetric-ish
    f['sn_fingerprint'] = f['peak_flux'] / (f['flux_mean'] + 1e-8) * (1 - np.abs(f['rate_asymmetry'] - 1))
    
    # TDE fingerprint: Asymmetric, power-law decline, blue color
    f['tde_fingerprint'] = f.get('tde_slope_match', 0) * f.get('rate_asymmetry', 1)
    
    # ============ MYRION RESOLUTION SCORING ============
    # Combine evidence using PD scale, not binary!
    
    # Evidence FOR TDE:
    pd_tde = 0.0
    
    # Power-law match
    if f.get('decline_power_r2', 0) > 0.5 and np.abs(f.get('decline_power_slope', 0) - TDE_POWER_LAW) < 0.5:
        pd_tde += 0.8
    
    # Asymmetric rise/decline
    if f.get('rate_asymmetry', 1) > 2.0:
        pd_tde += 0.5
    
    # Early peak
    if f.get('peak_position', 0.5) < 0.3:
        pd_tde += 0.3
    
    # High LCC events
    if f.get('lcc_085_ratio', 0) > 0.1:
        pd_tde += 0.4
    
    # Evidence AGAINST TDE:
    # Low variability (AGN-like)
    if f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8) < 0.1:
        pd_tde -= 0.8
    
    # Symmetric (SN-like)
    if 0.8 < f.get('rate_asymmetry', 1) < 1.2:
        pd_tde -= 0.3
    
    f['pd_tde'] = pd_tde
    
    # MR Decision: Outside indeterminate range?
    f['mr_outside_indeterminate'] = 1 if (pd_tde > PD_INDETERMINATE_HIGH or pd_tde < PD_INDETERMINATE_LOW) else 0
    f['mr_decision'] = 1 if pd_tde > PD_INDETERMINATE_HIGH else (0 if pd_tde < PD_INDETERMINATE_LOW else 0.5)
    
    # ============ HOLISTIC INTERACTION FEATURES (not additive!) ============
    # Per user: Use MR to find holistic patterns
    
    # Peak × Asymmetry × Duration (captures TDE signature holistically)
    f['holistic_tde_1'] = f['peak_flux'] * f.get('rate_asymmetry', 1) * (1 - f['peak_position'])
    
    # LCC × Power-law (correlational + physical)
    f['holistic_tde_2'] = f.get('lcc_085_ratio', 0) * f.get('tde_slope_match', 0)
    
    # Existence intensity × Decline quality
    f['holistic_tde_3'] = f['xi_max'] * f.get('decline_power_r2', 0)
    
    # SNR × Asymmetry × Peak position
    f['holistic_tde_4'] = f['snr_max'] * f.get('rate_asymmetry', 1) * (1 - f['peak_position'])
    
    # ============ NON-LOCAL CORRELATIONS ============
    mid = n // 2
    if mid > 2:
        try:
            f['half_correlation'] = np.corrcoef(flux[:mid], flux[mid:mid*2])[0,1] if mid*2 <= n else 0
        except:
            f['half_correlation'] = 0
    else:
        f['half_correlation'] = 0
    
    if peak_idx > 2 and peak_idx < n - 3:
        rise_len = peak_idx
        decline_len = n - peak_idx - 1
        min_len = min(rise_len, decline_len)
        
        if min_len > 2:
            try:
                rise_seg = flux[:min_len]
                decline_seg = flux[peak_idx+1:peak_idx+1+min_len]
                f['rise_decline_corr'] = np.corrcoef(rise_seg, decline_seg[::-1])[0,1]
            except:
                f['rise_decline_corr'] = 0
        else:
            f['rise_decline_corr'] = 0
    else:
        f['rise_decline_corr'] = 0
    
    if n > 3:
        f['autocorr_1'] = np.corrcoef(flux[:-1], flux[1:])[0,1]
    else:
        f['autocorr_1'] = 0
    
    # ============ GILE WIDTH / SACRED INTERVAL ============
    f['gile_width'] = f['flux_std'] / (f['flux_range'] + 1e-8)
    
    sacred_low = f['flux_mean'] - 2*f['flux_std']/3
    sacred_high = f['flux_mean'] + f['flux_std']/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / n
    
    # ============ VARIABILITY METRICS ============
    f['excess_var'] = (np.var(flux) - np.mean(err**2)) / (f['flux_mean']**2 + 1e-8)
    f['amp_ratio'] = f['flux_range'] / (np.abs(f['flux_mean']) + 1e-8)
    f['cv'] = f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8)
    
    if n > 2:
        residual = (flux - f['flux_mean']) / (err + 1e-8)
        f['stetson_j'] = np.sum(np.sign(residual[:-1] * residual[1:]) * 
                                np.sqrt(np.abs(residual[:-1] * residual[1:])))
    else:
        f['stetson_j'] = 0
    
    # ============ PER-FILTER + COLOR AS E-DIMENSION ============
    filter_means = {}
    for filt in ['u', 'g', 'r', 'i', 'z', 'y']:
        fd = obj[obj['Filter'] == filt] if 'Filter' in obj.columns else pd.DataFrame()
        if len(fd) > 0:
            ff = fd['Flux'].values
            fe = fd['Flux_err'].values
            
            f[f'{filt}_n'] = len(fd)
            f[f'{filt}_mean'] = np.mean(ff)
            f[f'{filt}_std'] = np.std(ff)
            f[f'{filt}_max'] = np.max(ff)
            f[f'{filt}_range'] = np.ptp(ff)
            f[f'{filt}_frac'] = len(fd) / n
            
            # Per-filter error patterns
            f[f'{filt}_err_mean'] = np.mean(fe)
            
            # Per-filter LCC
            if len(ff) > 3 and np.std(ff) > 0:
                norm_f = (ff - np.mean(ff)) / np.std(ff)
                f[f'{filt}_lcc_042'] = np.sum(np.abs(norm_f) > LCC_THRESHOLD_042) / len(ff)
            else:
                f[f'{filt}_lcc_042'] = 0
            
            filter_means[filt] = f[f'{filt}_mean']
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_range'] = 0
            f[f'{filt}_frac'] = 0
            f[f'{filt}_err_mean'] = 0
            f[f'{filt}_lcc_042'] = 0
            filter_means[filt] = 0
    
    # Color as unified E-dimension (not just additive features!)
    # TDEs are blue: high u/g relative to r/i/z
    blue_flux = filter_means.get('u', 0) + filter_means.get('g', 0)
    red_flux = filter_means.get('r', 0) + filter_means.get('i', 0) + filter_means.get('z', 0)
    
    f['blue_red_ratio'] = blue_flux / (red_flux + 1e-8)
    f['color_e_dimension'] = (blue_flux - red_flux) / (blue_flux + red_flux + 1e-8)
    
    # Individual color differences
    f['g_r'] = filter_means.get('g', 0) - filter_means.get('r', 0)
    f['r_i'] = filter_means.get('r', 0) - filter_means.get('i', 0)
    f['i_z'] = filter_means.get('i', 0) - filter_means.get('z', 0)
    f['u_g'] = filter_means.get('u', 0) - filter_means.get('g', 0)
    
    return f

# Extract features
print("\nExtracting TI MR + LCC features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_ti_mr_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    
    # DE-Photon Time interpretation of redshift:
    # Higher Z = more "timeless" photon journey = different existence intensity
    feat['Z_log'] = np.log1p(feat['Z'])
    feat['Z_squared'] = feat['Z']**2
    
    # Z interactions (per user: non-local causation may depend on distance)
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    feat['Z_flux_range'] = feat['Z'] * feat.get('flux_range', 0)
    
    train_feats.append(feat)
    if (i+1) % 500 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_ti_mr_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    feat['Z_squared'] = feat['Z']**2
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    feat['Z_flux_range'] = feat['Z'] * feat.get('flux_range', 0)
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

# Training
print("\n" + "="*50)
print("TRAINING (TI MR + LCC Enhanced Ensemble)")
print("="*50)

skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

oof_preds = {f'm{i}': np.zeros(len(X)) for i in range(4)}
test_preds = {f'm{i}': np.zeros(len(X_test)) for i in range(4)}

scores = []

for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
    Xt, Xv = X_s[ti], X_s[vi]
    yt, yv = y[ti], y[vi]
    
    # Model 1: Deep HGB
    m1 = HistGradientBoostingClassifier(
        max_iter=1000, max_depth=12, learning_rate=0.015,
        l2_regularization=0.005, max_bins=255, min_samples_leaf=3,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=80, random_state=42
    )
    m1.fit(Xt, yt)
    oof_preds['m0'][vi] = m1.predict_proba(Xv)[:, 1]
    test_preds['m0'] += m1.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 2: Medium HGB
    m2 = HistGradientBoostingClassifier(
        max_iter=600, max_depth=7, learning_rate=0.03,
        l2_regularization=0.02, max_bins=255, min_samples_leaf=8,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=50, random_state=43
    )
    m2.fit(Xt, yt)
    oof_preds['m1'][vi] = m2.predict_proba(Xv)[:, 1]
    test_preds['m1'] += m2.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 3: Random Forest
    m3 = RandomForestClassifier(
        n_estimators=500, max_depth=15, min_samples_leaf=2,
        class_weight='balanced', random_state=44, n_jobs=-1
    )
    m3.fit(Xt, yt)
    oof_preds['m2'][vi] = m3.predict_proba(Xv)[:, 1]
    test_preds['m2'] += m3.predict_proba(X_test_s)[:, 1] / 5
    
    # Model 4: ExtraTrees
    m4 = ExtraTreesClassifier(
        n_estimators=500, max_depth=18, min_samples_leaf=2,
        class_weight='balanced', random_state=45, n_jobs=-1
    )
    m4.fit(Xt, yt)
    oof_preds['m3'][vi] = m4.predict_proba(Xv)[:, 1]
    test_preds['m3'] += m4.predict_proba(X_test_s)[:, 1] / 5
    
    # Blend
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

# Optimal threshold
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
sub.to_csv('submission_mallorn_v6.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v6.csv")

# ============ LCC EMPIRICAL VALIDATION ============
print("\n" + "="*50)
print("LCC EMPIRICAL VALIDATION")
print("="*50)

# Analyze LCC features vs actual TDE status
train_df_with_target = train_df.copy()
train_df_with_target['target'] = y

tde_mask = train_df_with_target['target'] == 1
non_tde_mask = train_df_with_target['target'] == 0

print("\nLCC Feature Analysis (TDE vs Non-TDE):")
for lcc_feat in ['lcc_042_ratio', 'lcc_085_ratio', 'lcc_tt_ratio', 'tralse_ratio']:
    if lcc_feat in train_df_with_target.columns:
        tde_mean = train_df_with_target.loc[tde_mask, lcc_feat].mean()
        non_mean = train_df_with_target.loc[non_tde_mask, lcc_feat].mean()
        ratio = tde_mean / (non_mean + 1e-8)
        print(f"  {lcc_feat:20s}: TDE={tde_mean:.4f}, Non-TDE={non_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*50)
print("TOP 25 FEATURES (by importance)")
print("="*50)

feature_names = cols
importance = m3.feature_importances_
top_idx = np.argsort(importance)[::-1][:25]

for i, idx in enumerate(top_idx):
    if idx < len(feature_names):
        print(f"{i+1:2d}. {feature_names[idx]:30s}: {importance[idx]:.4f}")
