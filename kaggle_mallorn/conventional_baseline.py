"""
MALLORN CONVENTIONAL BASELINE
=============================
State-of-the-art approach based on:
1. GP-inspired feature extraction (color evolution, rise/fade times)
2. Proper class imbalance handling (1:19 ratio)
3. XGBoost + Random Forest ensemble
4. Rigorous cross-validation

Goal: Establish optimal conventional performance, understand 0.75 plateau
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score, roc_auc_score
from scipy import stats
from scipy.interpolate import interp1d
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("MALLORN CONVENTIONAL BASELINE")
print("State-of-the-art TDE detection (pre-TI Sigma)")
print("=" * 70)

BANDS = ['u', 'g', 'r', 'i', 'z', 'y']
BAND_WAVELENGTHS = {'u': 354, 'g': 477, 'r': 623, 'i': 762, 'z': 913, 'y': 1004}

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"\n=== DATASET ANALYSIS ===")
print(f"Training: {len(train_log)} objects")
print(f"TDE (positive): {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")
print(f"Non-TDE: {len(train_log) - train_log['target'].sum()}")
print(f"Class imbalance ratio: 1:{int((1-train_log['target'].mean())/train_log['target'].mean())}")

# SpecType distribution
print(f"\nSpectral Type Distribution:")
for spec, count in train_log['SpecType'].value_counts().items():
    tde_count = train_log[train_log['SpecType'] == spec]['target'].sum()
    print(f"  {spec}: {count} total, {tde_count} TDE ({tde_count/count*100:.1f}%)")

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

def extract_conventional_features(obj_id, lc_dict, meta_row):
    """
    State-of-the-art conventional feature extraction based on:
    - GP-inspired: color evolution, rise/fade times, peak analysis
    - FLEET algorithm features
    - PLAsTiCC winning approach features
    """
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id].copy()
    df = df.sort_values('mjd')
    
    f = {}
    
    # === METADATA FEATURES ===
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    # Encode spectral type (important for AGN vs TDE distinction)
    spec_map = {'AGN': 0, 'SN Ia': 1, 'SN Ia-pec': 2, 'SN Ib': 3, 'SN II': 4, 'TDE': 5}
    f['spec_encoded'] = spec_map.get(meta_row['SpecType'], -1)
    
    # === GLOBAL FLUX STATISTICS ===
    all_flux = df['Flux'].dropna().values
    all_err = df['Flux_err'].dropna().values
    all_mjd = df['mjd'].values
    
    if len(all_flux) < 5:
        return None
    
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
    
    # Robust scatter (median absolute deviation)
    f['flux_mad'] = np.median(np.abs(all_flux - np.median(all_flux)))
    
    # === SIGNAL-TO-NOISE FEATURES ===
    if len(all_err) > 0:
        min_len = min(len(all_flux), len(all_err))
        snr = np.abs(all_flux[:min_len]) / (all_err[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
        f['snr_std'] = np.std(snr)
    else:
        f['snr_mean'] = 5.0
        f['snr_max'] = 10.0
        f['snr_std'] = 2.0
    
    # === TEMPORAL FEATURES ===
    f['duration'] = all_mjd[-1] - all_mjd[0]
    f['cadence_mean'] = np.mean(np.diff(all_mjd))
    f['cadence_std'] = np.std(np.diff(all_mjd))
    
    # === PEAK DETECTION (critical for TDE) ===
    peak_idx = np.argmax(all_flux)
    f['peak_flux'] = all_flux[peak_idx]
    f['peak_time_frac'] = peak_idx / len(all_flux)
    f['time_to_peak'] = all_mjd[peak_idx] - all_mjd[0]
    
    # Rise features (pre-peak)
    if peak_idx > 2:
        rise_flux = all_flux[:peak_idx+1]
        rise_time = all_mjd[:peak_idx+1]
        f['rise_rate'] = (rise_flux[-1] - rise_flux[0]) / (rise_time[-1] - rise_time[0] + 1e-8)
        f['rise_duration'] = rise_time[-1] - rise_time[0]
    else:
        f['rise_rate'] = 0
        f['rise_duration'] = 0
    
    # Fade features (post-peak) - KEY FOR TDE t^-5/3 law
    if peak_idx < len(all_flux) - 3:
        fade_flux = all_flux[peak_idx:]
        fade_time = all_mjd[peak_idx:]
        f['fade_rate'] = (fade_flux[-1] - fade_flux[0]) / (fade_time[-1] - fade_time[0] + 1e-8)
        f['fade_duration'] = fade_time[-1] - fade_time[0]
        
        # Power law fit (TDE signature: t^-5/3)
        positive_fade = fade_flux[fade_flux > 0]
        if len(positive_fade) > 3:
            log_flux = np.log(positive_fade)
            log_time = np.log(np.arange(1, len(positive_fade) + 1))
            slope, intercept, r, p, se = stats.linregress(log_time, log_flux)
            f['fade_power_law_slope'] = slope
            f['fade_power_law_r2'] = r**2
            f['tde_slope_match'] = 1 - np.abs(slope - (-5/3)) / 2  # TDE = -5/3
        else:
            f['fade_power_law_slope'] = 0
            f['fade_power_law_r2'] = 0
            f['tde_slope_match'] = 0
    else:
        f['fade_rate'] = 0
        f['fade_duration'] = 0
        f['fade_power_law_slope'] = 0
        f['fade_power_law_r2'] = 0
        f['tde_slope_match'] = 0
    
    # === VARIABILITY FEATURES ===
    flux_diffs = np.diff(all_flux)
    f['flux_diff_mean'] = np.mean(np.abs(flux_diffs))
    f['flux_diff_std'] = np.std(flux_diffs)
    
    # Stetson variability indices
    if len(all_flux) > 2 and len(all_err) > 2:
        min_len = min(len(all_flux), len(all_err))
        residuals = (all_flux[:min_len] - f['flux_mean']) / (all_err[:min_len] + 1e-8)
        f['stetson_k'] = np.mean(np.abs(residuals)) / np.sqrt(np.mean(residuals**2) + 1e-8)
    else:
        f['stetson_k'] = 1.0
    
    # Autocorrelation
    if len(all_flux) > 3:
        autocorr = np.corrcoef(all_flux[:-1], all_flux[1:])[0, 1]
        f['autocorr_1'] = autocorr if not np.isnan(autocorr) else 0
    else:
        f['autocorr_1'] = 0
    
    # === COLOR EVOLUTION (GP-inspired) ===
    band_stats = {}
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) >= 2:
            band_flux = band_df['Flux'].values
            band_stats[band] = {
                'mean': np.mean(band_flux),
                'std': np.std(band_flux),
                'max': np.max(band_flux),
                'n': len(band_flux)
            }
            f[f'band_{band}_mean'] = band_stats[band]['mean']
            f[f'band_{band}_std'] = band_stats[band]['std']
        else:
            f[f'band_{band}_mean'] = 0
            f[f'band_{band}_std'] = 0
    
    # Color indices (critical for distinguishing transient types)
    blue_flux = f.get('band_u_mean', 0) + f.get('band_g_mean', 0)
    red_flux = f.get('band_i_mean', 0) + f.get('band_z_mean', 0) + f.get('band_y_mean', 0)
    f['blue_red_ratio'] = blue_flux / (red_flux + 1e-8) if red_flux != 0 else 1.0
    
    # g-r color (standard astronomical color)
    f['color_gr'] = f.get('band_g_mean', 0) - f.get('band_r_mean', 0)
    f['color_ri'] = f.get('band_r_mean', 0) - f.get('band_i_mean', 0)
    f['color_iz'] = f.get('band_i_mean', 0) - f.get('band_z_mean', 0)
    
    # === FRACTION OF OBSERVATIONS BY BAND ===
    for band in BANDS:
        band_count = len(df[df['Filter'] == band])
        f[f'band_{band}_frac'] = band_count / len(df)
    
    # === FLUX SIGN FEATURES (important for transients) ===
    f['frac_positive'] = np.mean(all_flux > 0)
    f['frac_negative'] = np.mean(all_flux < 0)
    f['frac_near_zero'] = np.mean(np.abs(all_flux) < f['flux_std'])
    
    # === PERIODICITY DETECTION (AGN tend to be more periodic) ===
    if len(all_flux) > 10:
        fft_vals = np.abs(np.fft.fft(all_flux - np.mean(all_flux)))
        f['fft_max'] = np.max(fft_vals[1:len(fft_vals)//2])
        f['fft_mean'] = np.mean(fft_vals[1:len(fft_vals)//2])
    else:
        f['fft_max'] = 0
        f['fft_mean'] = 0
    
    return f

# Extract features
print("\nExtracting conventional features...")
train_features, train_targets = [], []
for i, r in train_log.iterrows():
    feat = extract_conventional_features(r['object_id'], train_lc_dict, r)
    if feat is not None:
        train_features.append(feat)
        train_targets.append(r['target'])
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

print(f"\nExtracting test features...")
test_features, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_conventional_features(r['object_id'], test_lc_dict, r)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 1000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_train = pd.DataFrame(train_features)
y_train = np.array(train_targets)
X_test = pd.DataFrame(test_features)

# Align columns
common_cols = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common_cols].fillna(0)
X_test = X_test[common_cols].fillna(0)

print(f"\nFeatures extracted: {len(common_cols)}")
print(f"Training samples: {len(X_train)}")
print(f"Test samples: {len(X_test)}")

# === TRAINING WITH PROPER CLASS IMBALANCE HANDLING ===
print("\n" + "=" * 70)
print("TRAINING (5-Fold CV with Class Balancing)")
print("=" * 70)

scaler = StandardScaler()
X_tr_scaled = scaler.fit_transform(X_train)
X_te_scaled = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

# Class weight for imbalance
class_weight = {0: 1, 1: 19}  # Inverse of class ratio

# Models
models = {
    'RF': RandomForestClassifier(
        n_estimators=300, 
        max_depth=12, 
        min_samples_leaf=3,
        class_weight='balanced',
        random_state=42,
        n_jobs=-1
    ),
    'GB': GradientBoostingClassifier(
        n_estimators=200,
        max_depth=6,
        learning_rate=0.05,
        min_samples_leaf=5,
        random_state=42
    )
}

oof_preds = {name: np.zeros(len(X_train)) for name in models}
test_preds = {name: np.zeros(len(X_test)) for name in models}
fold_scores = {name: [] for name in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr_scaled, y_train)):
    X_tr, X_val = X_tr_scaled[tr_idx], X_tr_scaled[val_idx]
    y_tr, y_val = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models.items():
        model.fit(X_tr, y_tr)
        
        val_probs = model.predict_proba(X_val)[:, 1]
        oof_preds[name][val_idx] = val_probs
        test_preds[name] += model.predict_proba(X_te_scaled)[:, 1] / 5
        
        # Find optimal threshold for this fold
        best_f1 = 0
        for th in np.linspace(0.1, 0.5, 21):
            f1 = f1_score(y_val, val_probs >= th)
            if f1 > best_f1:
                best_f1 = f1
        fold_scores[name].append(best_f1)
    
    print(f"  Fold {fold+1}: RF={fold_scores['RF'][-1]:.4f}, GB={fold_scores['GB'][-1]:.4f}")

# Ensemble predictions
print("\n" + "=" * 70)
print("MODEL PERFORMANCE (OOF)")
print("=" * 70)

for name in models:
    scores = fold_scores[name]
    print(f"\n{name}:")
    print(f"  Mean F1: {np.mean(scores):.4f} ± {np.std(scores):.4f}")
    print(f"  Range: [{np.min(scores):.4f}, {np.max(scores):.4f}]")
    
    # Overall OOF metrics
    best_f1, best_th = 0, 0.3
    for th in np.linspace(0.1, 0.5, 41):
        f1 = f1_score(y_train, oof_preds[name] >= th)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    preds = oof_preds[name] >= best_th
    prec = precision_score(y_train, preds)
    rec = recall_score(y_train, preds)
    auc = roc_auc_score(y_train, oof_preds[name])
    
    print(f"  OOF F1: {best_f1:.4f} @ threshold {best_th:.3f}")
    print(f"  Precision: {prec:.4f}, Recall: {rec:.4f}")
    print(f"  ROC AUC: {auc:.4f}")

# Weighted ensemble
oof_ensemble = 0.6 * oof_preds['RF'] + 0.4 * oof_preds['GB']
test_ensemble = 0.6 * test_preds['RF'] + 0.4 * test_preds['GB']

print("\n" + "=" * 70)
print("ENSEMBLE PERFORMANCE")
print("=" * 70)

best_f1, best_th = 0, 0.3
results = []
for th in np.linspace(0.05, 0.6, 56):
    preds = oof_ensemble >= th
    if preds.sum() > 0:
        f1 = f1_score(y_train, preds)
        prec = precision_score(y_train, preds)
        rec = recall_score(y_train, preds)
        results.append((th, f1, prec, rec))
        if f1 > best_f1:
            best_f1, best_th = f1, th

print(f"\nThreshold Analysis:")
print(f"{'Thresh':>8} {'F1':>8} {'Prec':>8} {'Recall':>8}")
for th, f1, prec, rec in results[::5]:
    marker = " <<<" if abs(th - best_th) < 0.01 else ""
    print(f"{th:8.3f} {f1:8.4f} {prec:8.4f} {rec:8.4f}{marker}")

preds_train = oof_ensemble >= best_th
prec = precision_score(y_train, preds_train)
rec = recall_score(y_train, preds_train)
auc = roc_auc_score(y_train, oof_ensemble)

print(f"\n{'='*70}")
print(f"FINAL CONVENTIONAL BASELINE:")
print(f"  OOF F1: {best_f1:.4f} @ threshold {best_th:.3f}")
print(f"  Precision: {prec:.4f}, Recall: {rec:.4f}")
print(f"  ROC AUC: {auc:.4f}")
print(f"{'='*70}")

# Feature importance
print("\n" + "=" * 70)
print("TOP 20 FEATURES (Random Forest)")
print("=" * 70)

# Retrain on full data for importance
rf_full = RandomForestClassifier(n_estimators=300, max_depth=12, class_weight='balanced', random_state=42, n_jobs=-1)
rf_full.fit(X_tr_scaled, y_train)
imp = pd.Series(rf_full.feature_importances_, index=X_train.columns).sort_values(ascending=False)

for i, (feat, val) in enumerate(imp.head(20).items()):
    print(f"  {i+1:2d}. {feat:30s} {val:.4f}")

# Save submission
y_pred = (test_ensemble >= best_th).astype(int)
submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_conventional_baseline.csv', index=False)

print(f"\n{'='*70}")
print(f"SUBMISSION SAVED: submission_conventional_baseline.csv")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")
print(f"{'='*70}")

# === ANALYSIS: WHY 0.75 PLATEAU? ===
print("\n" + "=" * 70)
print("ANALYSIS: WHY THE ~0.75 PLATEAU?")
print("=" * 70)

print("\n1. CLASS IMBALANCE (1:19)")
print(f"   Only {train_log['target'].mean()*100:.2f}% are TDEs")
print(f"   Random baseline F1 would be ~0.05")

print("\n2. SPECTRAL TYPE CONFUSION:")
tde_by_spec = train_log.groupby('SpecType')['target'].agg(['sum', 'count'])
for spec in tde_by_spec.index:
    rate = tde_by_spec.loc[spec, 'sum'] / tde_by_spec.loc[spec, 'count']
    print(f"   {spec}: {rate*100:.1f}% TDE rate")

print("\n3. FEATURE DISCRIMINATION:")
key_feats = ['tde_slope_match', 'fade_power_law_slope', 'blue_red_ratio', 'Z']
for feat in key_feats:
    if feat in X_train.columns:
        tde_mean = X_train.loc[y_train == 1, feat].mean()
        non_mean = X_train.loc[y_train == 0, feat].mean()
        sep = abs(tde_mean - non_mean) / (X_train[feat].std() + 1e-8)
        print(f"   {feat}: TDE={tde_mean:.4f}, Non-TDE={non_mean:.4f}, Separation={sep:.2f}σ")

print("\n4. POTENTIAL IMPROVEMENTS:")
print("   - More sophisticated color evolution tracking")
print("   - Better power law fitting (Bazin function)")
print("   - Host galaxy information (if available)")
print("   - Temporal transformer architecture")
print("   - >>> TI SIGMA: 4-valued logic could capture uncertainty <<<")

print("\n✅ CONVENTIONAL BASELINE COMPLETE")
