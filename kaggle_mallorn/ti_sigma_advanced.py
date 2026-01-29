"""
TI SIGMA ADVANCED - Push Toward 0.75
====================================
Building on ablation results:
- TAF: +6.26% (keep and enhance)
- Anti-GILE Holes: +6.78% (keep and enhance)
- Myrion/LCC: marginal (simplify)

Adding advanced conventional features:
- Bazin function fitting
- Color evolution tracking
- Multi-scale temporal analysis
- Advanced statistics
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold, train_test_split
from sklearn.ensemble import RandomForestClassifier, HistGradientBoostingClassifier, ExtraTreesClassifier
from sklearn.preprocessing import StandardScaler, RobustScaler
from sklearn.metrics import f1_score, precision_score, recall_score, roc_auc_score
from scipy import stats
from scipy.optimize import curve_fit
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI SIGMA ADVANCED - Pushing Toward 0.75")
print("=" * 70)

# Constants
PHI = (1 + np.sqrt(5)) / 2
LCC_DETECTABLE = 0.42
LCC_CAUSAL = 0.85
TDE_POWER_LAW = -5/3
BANDS = ['u', 'g', 'r', 'i', 'z', 'y']

# === BAZIN FUNCTION (for TDE fitting) ===

def bazin_func(t, A, B, t0, tfall, trise):
    """Bazin function for supernova/TDE light curves."""
    return A * (np.exp(-(t - t0) / tfall)) / (1 + np.exp(-(t - t0) / trise)) + B

def fit_bazin(mjd, flux):
    """Fit Bazin function to light curve."""
    try:
        mjd = np.asarray(mjd)
        flux = np.asarray(flux)
        
        # Initial guess
        A0 = np.max(flux) - np.min(flux)
        B0 = np.min(flux)
        t0_0 = mjd[np.argmax(flux)]
        tfall0 = (mjd[-1] - t0_0) / 2
        trise0 = (t0_0 - mjd[0]) / 2 if t0_0 > mjd[0] else 1
        
        p0 = [A0, B0, t0_0, max(1, tfall0), max(1, trise0)]
        bounds = ([0, -np.inf, mjd[0], 0.1, 0.1], 
                  [np.inf, np.inf, mjd[-1], 1000, 1000])
        
        popt, pcov = curve_fit(bazin_func, mjd, flux, p0=p0, bounds=bounds, maxfev=1000)
        
        fitted = bazin_func(mjd, *popt)
        residuals = flux - fitted
        ss_res = np.sum(residuals**2)
        ss_tot = np.sum((flux - np.mean(flux))**2)
        r2 = 1 - (ss_res / (ss_tot + 1e-10))
        
        return {
            'amplitude': popt[0],
            'baseline': popt[1],
            't_peak': popt[2],
            't_fall': popt[3],
            't_rise': popt[4],
            'r2': r2,
            'residual_std': np.std(residuals),
            'success': True
        }
    except:
        return {
            'amplitude': 0, 'baseline': 0, 't_peak': 0,
            't_fall': 0, 't_rise': 0, 'r2': 0, 'residual_std': 0, 'success': False
        }


# === FORMAL TAF (unit sphere normalized) ===

def tralse_activation(flux, temperature=1.0):
    """TAF with proper unit sphere normalization."""
    x = np.asarray(flux)
    
    t = np.maximum(0, x)
    f = np.maximum(0, -x)
    phi = np.exp(-x**2 / temperature)
    psi = np.tanh(np.abs(np.gradient(x)) if len(x) > 1 else np.zeros_like(x)) * 0.5
    
    norm = np.sqrt(t**2 + f**2 + phi**2 + psi**2 + 1e-10)
    return t/norm, f/norm, phi/norm, psi/norm


# === ANTI-GILE HOLES ===

def compute_gile_holes(flux, expected, flux_std):
    """Compute all four GILE dimension holes."""
    flux = np.asarray(flux)
    expected = np.asarray(expected)[:len(flux)]
    
    residual = flux - expected
    
    I_hole = np.mean(np.abs(residual)) / (flux_std + 1e-10)
    
    exp_sig = expected > np.median(expected)
    act_sig = flux > np.median(flux)
    E_hole = np.mean(exp_sig & ~act_sig)
    
    if len(flux) > 3:
        ac = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        L_hole = 1.0 - np.abs(ac) if not np.isnan(ac) else 0.5
    else:
        L_hole = 0.5
    
    peak_idx = np.argmax(flux)
    if peak_idx < len(flux) - 3:
        fade = flux[peak_idx:]
        pos = fade[fade > 0]
        if len(pos) > 3:
            slope, _, _, _, _ = stats.linregress(
                np.log(np.arange(1, len(pos)+1)), np.log(pos + 1e-10)
            )
            G_hole = np.abs(slope - TDE_POWER_LAW) / 2
        else:
            G_hole = 1.0
    else:
        G_hole = 1.0
    
    return I_hole, E_hole, L_hole, G_hole


# === ADVANCED FEATURE EXTRACTION ===

def extract_advanced_features(obj_id, lc_dict, meta_row):
    """Extract advanced features for pushing toward 0.75."""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id].copy().sort_values('mjd')
    flux = df['Flux'].dropna().values
    err = df['Flux_err'].dropna().values
    mjd = df['mjd'].values
    
    if len(flux) < 10:  # Need more points for advanced features
        return None
    
    f = {}
    
    # === METADATA ===
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    # === BASIC STATISTICS ===
    f['n_obs'] = len(flux)
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurtosis'] = stats.kurtosis(flux)
    f['flux_mad'] = np.median(np.abs(flux - f['flux_median']))
    f['flux_iqr'] = np.percentile(flux, 75) - np.percentile(flux, 25)
    f['flux_range'] = np.max(flux) - np.min(flux)
    
    # Robust statistics
    f['flux_trim_mean'] = stats.trim_mean(flux, 0.1)
    f['flux_winsor_mean'] = np.mean(stats.mstats.winsorize(flux, limits=[0.05, 0.05]))
    
    # === SNR FEATURES ===
    if len(err) > 0:
        min_len = min(len(flux), len(err))
        snr = np.abs(flux[:min_len]) / (err[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
        f['snr_std'] = np.std(snr)
        f['snr_median'] = np.median(snr)
        f['snr_skew'] = stats.skew(snr)
    else:
        f['snr_mean'] = f['snr_max'] = f['snr_std'] = f['snr_median'] = f['snr_skew'] = 5.0
    
    # === TEMPORAL FEATURES ===
    duration = mjd[-1] - mjd[0]
    f['duration'] = duration
    f['cadence_mean'] = np.mean(np.diff(mjd))
    f['cadence_std'] = np.std(np.diff(mjd))
    f['cadence_iqr'] = np.percentile(np.diff(mjd), 75) - np.percentile(np.diff(mjd), 25)
    
    # === PEAK ANALYSIS ===
    peak_idx = np.argmax(flux)
    f['peak_flux'] = flux[peak_idx]
    f['peak_frac'] = peak_idx / len(flux)
    f['time_to_peak'] = mjd[peak_idx] - mjd[0]
    f['time_after_peak'] = mjd[-1] - mjd[peak_idx]
    f['peak_prominence'] = (flux[peak_idx] - np.median(flux)) / (f['flux_std'] + 1e-8)
    
    # Multiple peaks
    from scipy.signal import find_peaks
    peaks, properties = find_peaks(flux, height=np.percentile(flux, 75), distance=5)
    f['n_peaks'] = len(peaks)
    f['primary_peak_ratio'] = flux[peak_idx] / (np.mean(flux[peaks]) + 1e-8) if len(peaks) > 0 else 1.0
    
    # === RISE/FADE ANALYSIS ===
    if peak_idx > 3:
        rise_flux = flux[:peak_idx+1]
        rise_time = mjd[:peak_idx+1]
        f['rise_rate'] = (rise_flux[-1] - rise_flux[0]) / (rise_time[-1] - rise_time[0] + 1e-8)
        f['rise_duration'] = rise_time[-1] - rise_time[0]
        f['rise_linearity'], _, r_rise, _, _ = stats.linregress(rise_time, rise_flux)
        f['rise_r2'] = r_rise**2
    else:
        f['rise_rate'] = f['rise_duration'] = f['rise_linearity'] = f['rise_r2'] = 0
    
    if peak_idx < len(flux) - 5:
        fade_flux = flux[peak_idx:]
        fade_time = mjd[peak_idx:]
        f['fade_rate'] = (fade_flux[-1] - fade_flux[0]) / (fade_time[-1] - fade_time[0] + 1e-8)
        f['fade_duration'] = fade_time[-1] - fade_time[0]
        
        pos_fade = fade_flux[fade_flux > 0]
        if len(pos_fade) > 3:
            slope, intercept, r, p, se = stats.linregress(
                np.log(np.arange(1, len(pos_fade)+1)),
                np.log(pos_fade + 1e-10)
            )
            f['fade_slope'] = slope
            f['fade_r2'] = r**2
            f['tde_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
            f['fade_slope_diff'] = np.abs(slope - TDE_POWER_LAW)
        else:
            f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
            f['fade_slope_diff'] = 2.0
    else:
        f['fade_rate'] = f['fade_duration'] = 0
        f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
        f['fade_slope_diff'] = 2.0
    
    # === BAZIN FIT ===
    bazin = fit_bazin(mjd, flux)
    f['bazin_amplitude'] = bazin['amplitude']
    f['bazin_t_fall'] = bazin['t_fall']
    f['bazin_t_rise'] = bazin['t_rise']
    f['bazin_r2'] = bazin['r2']
    f['bazin_residual'] = bazin['residual_std']
    f['bazin_success'] = 1 if bazin['success'] else 0
    
    # TDE-specific Bazin ratios
    if bazin['success'] and bazin['t_rise'] > 0:
        f['bazin_fall_rise_ratio'] = bazin['t_fall'] / bazin['t_rise']
    else:
        f['bazin_fall_rise_ratio'] = 1.0
    
    # === PER-BAND FEATURES ===
    band_means = {}
    band_maxes = {}
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) >= 3:
            bf = band_df['Flux'].values
            bt = band_df['mjd'].values
            band_means[band] = np.mean(bf)
            band_maxes[band] = np.max(bf)
            f[f'b_{band}_mean'] = np.mean(bf)
            f[f'b_{band}_std'] = np.std(bf)
            f[f'b_{band}_max'] = np.max(bf)
            f[f'b_{band}_n'] = len(bf)
            f[f'b_{band}_skew'] = stats.skew(bf)
            
            # Peak time per band
            f[f'b_{band}_peak_frac'] = np.argmax(bf) / len(bf)
        else:
            band_means[band] = 0
            band_maxes[band] = 0
            f[f'b_{band}_mean'] = f[f'b_{band}_std'] = f[f'b_{band}_max'] = 0
            f[f'b_{band}_n'] = f[f'b_{band}_skew'] = f[f'b_{band}_peak_frac'] = 0
    
    # === COLOR FEATURES ===
    blue = band_means.get('u', 0) + band_means.get('g', 0)
    red = band_means.get('i', 0) + band_means.get('z', 0) + band_means.get('y', 0)
    f['blue_red_ratio'] = blue / (red + 1e-8) if abs(red) > 1e-8 else 1.0
    
    f['color_ug'] = band_means.get('u', 0) - band_means.get('g', 0)
    f['color_gr'] = band_means.get('g', 0) - band_means.get('r', 0)
    f['color_ri'] = band_means.get('r', 0) - band_means.get('i', 0)
    f['color_iz'] = band_means.get('i', 0) - band_means.get('z', 0)
    
    # Color evolution (TDEs evolve from blue to red)
    u_early = df[(df['Filter'] == 'u') & (df['mjd'] < np.median(mjd))]['Flux'].mean()
    u_late = df[(df['Filter'] == 'u') & (df['mjd'] >= np.median(mjd))]['Flux'].mean()
    r_early = df[(df['Filter'] == 'r') & (df['mjd'] < np.median(mjd))]['Flux'].mean()
    r_late = df[(df['Filter'] == 'r') & (df['mjd'] >= np.median(mjd))]['Flux'].mean()
    
    if not np.isnan(u_early) and not np.isnan(u_late) and not np.isnan(r_early) and not np.isnan(r_late):
        color_early = (u_early if u_early else 0) - (r_early if r_early else 0)
        color_late = (u_late if u_late else 0) - (r_late if r_late else 0)
        f['color_evolution'] = color_late - color_early  # Negative = blue→red
    else:
        f['color_evolution'] = 0
    
    # === VARIABILITY ===
    diffs = np.diff(flux)
    f['diff_mean'] = np.mean(np.abs(diffs))
    f['diff_std'] = np.std(diffs)
    f['diff_skew'] = stats.skew(diffs)
    
    # Stetson variability indices
    if len(flux) > 2 and len(err) > 2:
        min_len = min(len(flux), len(err))
        residuals = (flux[:min_len] - f['flux_mean']) / (err[:min_len] + 1e-8)
        f['stetson_j'] = np.mean(np.abs(residuals))
        f['stetson_k'] = np.mean(np.abs(residuals)) / np.sqrt(np.mean(residuals**2) + 1e-8)
    else:
        f['stetson_j'] = f['stetson_k'] = 1.0
    
    # Autocorrelation at multiple lags
    for lag in [1, 2, 3]:
        if len(flux) > lag + 1:
            ac = np.corrcoef(flux[:-lag], flux[lag:])[0, 1]
            f[f'autocorr_lag{lag}'] = ac if not np.isnan(ac) else 0
        else:
            f[f'autocorr_lag{lag}'] = 0
    
    # === FFT FEATURES ===
    if len(flux) > 10:
        fft_vals = np.abs(np.fft.fft(flux - f['flux_mean']))
        n = len(fft_vals)
        f['fft_max'] = np.max(fft_vals[1:n//2])
        f['fft_mean'] = np.mean(fft_vals[1:n//2])
        f['fft_ratio'] = np.max(fft_vals[1:n//4]) / (np.max(fft_vals[n//4:n//2]) + 1e-8)
    else:
        f['fft_max'] = f['fft_mean'] = f['fft_ratio'] = 0
    
    # === FORMAL TAF FEATURES ===
    t, f_neg, phi, psi = tralse_activation(flux)
    
    f['taf_T_mean'] = np.mean(t)
    f['taf_T_std'] = np.std(t)
    f['taf_F_mean'] = np.mean(f_neg)
    f['taf_F_std'] = np.std(f_neg)
    f['taf_phi_mean'] = np.mean(phi)
    f['taf_phi_std'] = np.std(phi)
    f['taf_psi_mean'] = np.mean(psi)
    f['taf_psi_std'] = np.std(psi)
    
    f['taf_certainty'] = np.mean(1 - phi)
    f['taf_T_F_ratio'] = np.sum(t) / (np.sum(f_neg) + 1e-8)
    
    # TAF on differences (temporal uncertainty)
    t_d, f_d, phi_d, psi_d = tralse_activation(diffs)
    f['taf_diff_phi'] = np.mean(phi_d)
    f['taf_diff_psi'] = np.mean(psi_d)
    
    # === ANTI-GILE HOLES ===
    expected = flux[peak_idx] * np.power(np.arange(1, len(flux)+1), TDE_POWER_LAW)
    I_hole, E_hole, L_hole, G_hole = compute_gile_holes(flux, expected, f['flux_std'])
    
    f['I_hole'] = I_hole
    f['E_hole'] = E_hole
    f['L_hole'] = L_hole
    f['G_hole'] = G_hole
    f['total_hole'] = (I_hole + E_hole + L_hole + G_hole) / 4
    
    # Hole asymmetry (pattern deviations)
    f['hole_asymmetry'] = np.abs(I_hole - E_hole) + np.abs(L_hole - G_hole)
    
    # === LCC CASCADE ===
    max_flux = np.max(np.abs(flux)) + 1e-10
    normalized = np.abs(flux) / max_flux
    f['lcc_042'] = np.mean(normalized > LCC_DETECTABLE)
    f['lcc_085'] = np.mean(normalized > LCC_CAUSAL)
    
    # === SYNERGY FEATURES ===
    f['ti_synergy'] = (
        f['taf_certainty'] * 0.3 +
        f['lcc_085'] * 0.2 +
        f['tde_match'] * 0.3 +
        (1 - f['total_hole']) * 0.2
    )
    
    f['ti_confidence'] = f['taf_certainty'] * (1 - f['I_hole'])
    f['ti_uncertainty'] = f['taf_phi_mean'] * f['total_hole']
    
    # TDE signature score (combines all TDE indicators)
    f['tde_signature'] = (
        f['tde_match'] * 0.3 +
        (1 - f['G_hole']) * 0.3 +
        f['bazin_success'] * f['bazin_r2'] * 0.2 +
        (1 - f['fade_slope_diff']/2) * 0.2
    )
    
    return f


# === MAIN EXECUTION ===

train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"\nTraining: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

print("Loading data...")
train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')
train_lc = train_lc.rename(columns={'Time (MJD)': 'mjd'})
test_lc = test_lc.rename(columns={'Time (MJD)': 'mjd'})
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

print("\nExtracting advanced features...")
train_f, train_y = [], []
for i, r in train_log.iterrows():
    feat = extract_advanced_features(r['object_id'], train_lc_dict, r)
    if feat:
        train_f.append(feat)
        train_y.append(r['target'])
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

test_f, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_advanced_features(r['object_id'], test_lc_dict, r)
    if feat:
        test_f.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 1000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_train = pd.DataFrame(train_f)
y_train = np.array(train_y)
X_test = pd.DataFrame(test_f)

common = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common].fillna(0).replace([np.inf, -np.inf], 0)
X_test = X_test[common].fillna(0).replace([np.inf, -np.inf], 0)

# Clip extreme values
for col in common:
    p1, p99 = X_train[col].quantile(0.01), X_train[col].quantile(0.99)
    X_train[col] = X_train[col].clip(p1, p99)
    X_test[col] = X_test[col].clip(p1, p99)

print(f"\nTotal features: {len(common)}")
print(f"Training samples: {len(X_train)} ({sum(y_train)} TDE)")
print(f"Test samples: {len(X_test)}")


# === TRAINING WITH MULTIPLE MODELS ===
print("\n" + "=" * 70)
print("TRAINING ENSEMBLE")
print("=" * 70)

scaler = RobustScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

models = {
    'RF': RandomForestClassifier(n_estimators=500, max_depth=12, min_samples_leaf=2,
                                  class_weight='balanced', random_state=42, n_jobs=-1),
    'ET': ExtraTreesClassifier(n_estimators=500, max_depth=12, min_samples_leaf=2,
                                class_weight='balanced', random_state=42, n_jobs=-1),
    'HGB': HistGradientBoostingClassifier(learning_rate=0.03, max_iter=500, max_depth=8,
                                           min_samples_leaf=10, random_state=42)
}

oof = {name: np.zeros(len(X_train)) for name in models}
test_preds = {name: np.zeros(len(X_test)) for name in models}
scores = {name: [] for name in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr, y_train)):
    Xtr, Xval = X_tr[tr_idx], X_tr[val_idx]
    ytr, yval = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models.items():
        model.fit(Xtr, ytr)
        val_probs = model.predict_proba(Xval)[:, 1]
        oof[name][val_idx] = val_probs
        test_preds[name] += model.predict_proba(X_te)[:, 1] / 5
        
        best = max(f1_score(yval, val_probs >= th) for th in np.linspace(0.1, 0.5, 21))
        scores[name].append(best)
    
    print(f"  Fold {fold+1}: RF={scores['RF'][-1]:.4f}, ET={scores['ET'][-1]:.4f}, HGB={scores['HGB'][-1]:.4f}")


# === ENSEMBLE ===
print("\n" + "=" * 70)
print("MODEL RESULTS")
print("=" * 70)

for name in models:
    best_f1, best_th = 0, 0.3
    for th in np.linspace(0.05, 0.5, 46):
        f1 = f1_score(y_train, oof[name] >= th)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    prec = precision_score(y_train, oof[name] >= best_th)
    rec = recall_score(y_train, oof[name] >= best_th)
    auc = roc_auc_score(y_train, oof[name])
    
    print(f"\n{name}:")
    print(f"  Mean CV F1: {np.mean(scores[name]):.4f} ± {np.std(scores[name]):.4f}")
    print(f"  OOF F1: {best_f1:.4f} @ {best_th:.3f}")
    print(f"  Precision: {prec:.4f}, Recall: {rec:.4f}, AUC: {auc:.4f}")

# Weighted ensemble
oof_ens = 0.4 * oof['RF'] + 0.3 * oof['ET'] + 0.3 * oof['HGB']
test_ens = 0.4 * test_preds['RF'] + 0.3 * test_preds['ET'] + 0.3 * test_preds['HGB']

best_f1, best_th = 0, 0.3
for th in np.linspace(0.05, 0.5, 46):
    f1 = f1_score(y_train, oof_ens >= th)
    if f1 > best_f1:
        best_f1, best_th = f1, th

prec = precision_score(y_train, oof_ens >= best_th)
rec = recall_score(y_train, oof_ens >= best_th)
auc = roc_auc_score(y_train, oof_ens)

print("\n" + "=" * 70)
print("ENSEMBLE RESULTS")
print("=" * 70)
print(f"\nOOF F1: {best_f1:.4f} @ threshold {best_th:.3f}")
print(f"Precision: {prec:.4f}, Recall: {rec:.4f}")
print(f"ROC AUC: {auc:.4f}")


# === FEATURE IMPORTANCE ===
print("\n" + "=" * 70)
print("TOP 30 FEATURES")
print("=" * 70)

rf = RandomForestClassifier(n_estimators=500, max_depth=12, class_weight='balanced', random_state=42, n_jobs=-1)
rf.fit(X_tr, y_train)
imp = pd.Series(rf.feature_importances_, index=X_train.columns).sort_values(ascending=False)

def get_category(feat):
    if 'taf_' in feat: return 'TAF'
    if 'hole' in feat.lower(): return 'HOLE'
    if 'lcc_' in feat: return 'LCC'
    if 'ti_' in feat: return 'SYN'
    if 'bazin' in feat: return 'BAZIN'
    if 'color' in feat.lower(): return 'COLOR'
    return 'CONV'

for i, (feat, val) in enumerate(imp.head(30).items()):
    cat = get_category(feat)
    marker = "★" if cat not in ['CONV', 'BAZIN', 'COLOR'] else " "
    print(f"  {marker}{i+1:2d}. [{cat:5s}] {feat:30s} {val:.4f}")


# === TDE vs NON-TDE ===
print("\n" + "=" * 70)
print("KEY TI FEATURES: TDE vs NON-TDE")
print("=" * 70)

ti_features = ['taf_phi_mean', 'taf_certainty', 'I_hole', 'G_hole', 'tde_signature', 
               'ti_confidence', 'bazin_r2', 'tde_match']

for feat in ti_features:
    if feat in X_train.columns:
        tde = X_train.loc[y_train == 1, feat].mean()
        non = X_train.loc[y_train == 0, feat].mean()
        sep = abs(tde - non) / (X_train[feat].std() + 1e-8)
        print(f"  {feat:<20}: TDE={tde:.4f}, Non={non:.4f}, Sep={sep:.2f}σ")


# === SUBMISSION ===
y_pred = (test_ens >= best_th).astype(int)
submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_ti_sigma_advanced.csv', index=False)

print(f"\n{'='*70}")
print(f"SUBMISSION: submission_ti_sigma_advanced.csv")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")
print(f"{'='*70}")

# Also save probabilities
submission_probs = pd.DataFrame({'object_id': test_ids, 'target': test_ens})
submission_probs.to_csv('submission_ti_sigma_advanced_probs.csv', index=False)


# === HOLDOUT VALIDATION ===
print("\n" + "=" * 70)
print("HOLDOUT VALIDATION (5 seeds)")
print("=" * 70)

holdout_scores = []
for seed in [42, 123, 456, 789, 999]:
    X_tr, X_val, y_tr, y_val = train_test_split(X_train, y_train, test_size=0.2, stratify=y_train, random_state=seed)
    
    scaler = RobustScaler()
    Xtr = scaler.fit_transform(X_tr)
    Xval = scaler.transform(X_val)
    
    rf = RandomForestClassifier(n_estimators=500, max_depth=12, class_weight='balanced', random_state=42, n_jobs=-1)
    rf.fit(Xtr, y_tr)
    probs = rf.predict_proba(Xval)[:, 1]
    
    best = max(f1_score(y_val, probs >= th) for th in np.linspace(0.1, 0.5, 21))
    holdout_scores.append(best)
    print(f"  Seed {seed}: F1 = {best:.4f}")

print(f"\nHoldout Mean: {np.mean(holdout_scores):.4f} ± {np.std(holdout_scores):.4f}")
print(f"Holdout Best: {np.max(holdout_scores):.4f}")

print(f"\nTARGET: 0.75 | CURRENT: {np.mean(holdout_scores):.4f} | GAP: {0.75 - np.mean(holdout_scores):.4f}")

print("\n✅ TI SIGMA ADVANCED COMPLETE")
