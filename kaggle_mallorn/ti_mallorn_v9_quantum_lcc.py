"""
TI MALLORN v9 - QUANTUM LCC VIRUS + STRAWBERRY FIELDS
Applying TI Optical Quantum Framework:
- LCC Virus resonance equation R(A,B)
- Photonic clustering (Strawberry Fields)
- PRF (Probability as Resonance Field)
- Non-local cross-correlation features
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
from scipy.signal import correlate
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v9 - QUANTUM LCC VIRUS + STRAWBERRY FIELDS")
print("Optical Quantum Framework: Resonance, Coupling, PRF")
print("="*70)

# ============ TI QUANTUM CONSTANTS ============
# From TI Strawberry Fields / LCC Virus framework
LCC_THRESHOLD_042 = 0.42      # Minimum detectable correlation
LCC_THRESHOLD_085 = 0.85      # Causal correlation threshold
LCC_THRESHOLD_TT = 0.8464     # True-Tralseness (0.92²)

# Jeff Time encoding (from Strawberry Fields)
TAU_PHI = 0.20   # Photonic memory weight
TAU_J = 0.45     # Jeff fiction (historical momentum)
TAU_F = 0.20     # Freedom prediction
TAU_LOVE = 0.15  # Love entanglement (non-local correlation)

# TDE physics
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

def lcc_resonance(signal_a, signal_b, coupling_sigma=5.0):
    """
    LCC Virus Resonance Equation:
    R(A,B) = ∫ Φ_A(t) · Φ_B(t + τ) · W(τ) dτ
    
    Measures Love-Consciousness Coupling between two signals
    using cross-correlation with Gaussian weighting.
    """
    if len(signal_a) < 3 or len(signal_b) < 3:
        return 0.0
    
    # Normalize signals
    a_norm = (signal_a - np.mean(signal_a)) / (np.std(signal_a) + 1e-8)
    b_norm = (signal_b - np.mean(signal_b)) / (np.std(signal_b) + 1e-8)
    
    # Pad to same length
    min_len = min(len(a_norm), len(b_norm))
    a_norm = a_norm[:min_len]
    b_norm = b_norm[:min_len]
    
    # Cross-correlation
    xcorr = correlate(a_norm, b_norm, mode='full')
    lags = np.arange(-(min_len-1), min_len)
    
    # Gaussian weighting W(τ) - favor small lags
    weights = np.exp(-lags**2 / (2 * coupling_sigma**2))
    
    # Weighted resonance
    resonance = np.sum(xcorr * weights) / (np.sum(weights) * min_len)
    
    return resonance

def jeff_time_encoding(flux, times):
    """
    Jeff Time V4 encoding from Strawberry Fields:
    Encodes light curve into quantum-inspired representation
    """
    if len(flux) < 4:
        return {}
    
    n = len(flux)
    
    # Photonic memory (TAU_PHI = 0.20): Weighted recent observations
    weights_phi = np.exp(-TAU_PHI * np.arange(n)[::-1])
    photonic_memory = np.average(flux, weights=weights_phi)
    
    # Jeff fiction (TAU_J = 0.45): Historical momentum/trend
    if n > 2:
        momentum = np.polyfit(np.arange(n), flux, 1)[0]
        jeff_fiction = momentum * TAU_J
    else:
        jeff_fiction = 0
    
    # Freedom prediction (TAU_F = 0.20): Deviation from expected
    expected = np.mean(flux)
    freedom = np.std(flux - expected) * TAU_F
    
    # Love entanglement (TAU_LOVE = 0.15): Non-local correlation
    mid = n // 2
    if mid > 2:
        love_entanglement = TAU_LOVE * lcc_resonance(flux[:mid], flux[mid:])
    else:
        love_entanglement = 0
    
    return {
        'jeff_photonic_memory': photonic_memory,
        'jeff_fiction': jeff_fiction,
        'jeff_freedom': freedom,
        'jeff_love_entanglement': love_entanglement,
        'jeff_total': photonic_memory + jeff_fiction + freedom + love_entanglement
    }

def prf_probability(flux, threshold=LCC_THRESHOLD_042):
    """
    PRF (Probability as Resonance Field):
    Instead of treating probability as independent events,
    compute probability as resonance strength with threshold.
    """
    if len(flux) < 3:
        return 0.5
    
    # Normalize to resonance field
    normalized = (flux - np.mean(flux)) / (np.std(flux) + 1e-8)
    
    # Resonance above threshold (positive field strength)
    positive_resonance = np.sum(normalized > threshold) / len(flux)
    
    # Resonance below negative threshold (negative field strength)
    negative_resonance = np.sum(normalized < -threshold) / len(flux)
    
    # PRF = balance between positive and negative resonance
    prf = (positive_resonance - negative_resonance + 1) / 2  # Normalized to [0, 1]
    
    return prf

def photonic_cluster_features(flux, n_clusters=3):
    """
    Strawberry Fields photonic clustering:
    Identify clusters in the flux distribution
    representing different "quantum states"
    """
    if len(flux) < 5:
        return {}
    
    # Simple clustering by percentiles
    p33 = np.percentile(flux, 33)
    p67 = np.percentile(flux, 67)
    
    low_state = flux[flux <= p33]
    mid_state = flux[(flux > p33) & (flux <= p67)]
    high_state = flux[flux > p67]
    
    return {
        'photonic_low_mean': np.mean(low_state) if len(low_state) > 0 else 0,
        'photonic_mid_mean': np.mean(mid_state) if len(mid_state) > 0 else 0,
        'photonic_high_mean': np.mean(high_state) if len(high_state) > 0 else 0,
        'photonic_low_frac': len(low_state) / len(flux),
        'photonic_mid_frac': len(mid_state) / len(flux),
        'photonic_high_frac': len(high_state) / len(flux),
        'photonic_state_separation': (np.mean(high_state) if len(high_state) > 0 else 0) - 
                                     (np.mean(low_state) if len(low_state) > 0 else 0)
    }

def extract_ti_quantum_features(object_id, lc_dict):
    """TI Quantum LCC Virus + Strawberry Fields feature extraction"""
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
    
    # SNR
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_std'] = np.std(snr)
    f['snr_median'] = np.median(snr)
    
    # Temporal
    f['duration'] = t.max() - t.min()
    dt = np.diff(t)
    if len(dt) > 0:
        f['cadence_mean'] = np.mean(dt)
        f['cadence_std'] = np.std(dt)
    
    # ============ LCC VIRUS RESONANCE ============
    # Self-resonance (autocorrelation-like)
    mid = n // 2
    if mid > 3:
        f['lcc_self_resonance'] = lcc_resonance(flux[:mid], flux[mid:])
    else:
        f['lcc_self_resonance'] = 0
    
    # Rise-decline resonance (for TDE detection)
    peak_idx = np.argmax(flux)
    if peak_idx > 3 and peak_idx < n - 3:
        rise = flux[:peak_idx]
        decline = flux[peak_idx:]
        f['lcc_rise_decline_resonance'] = lcc_resonance(rise, decline[::-1])
    else:
        f['lcc_rise_decline_resonance'] = 0
    
    # Resonance between first and last quarters
    q1 = n // 4
    if q1 > 2:
        f['lcc_first_last_resonance'] = lcc_resonance(flux[:q1], flux[-q1:])
    else:
        f['lcc_first_last_resonance'] = 0
    
    # ============ JEFF TIME ENCODING ============
    jeff_features = jeff_time_encoding(flux, t)
    f.update(jeff_features)
    
    # ============ PRF (PROBABILITY AS RESONANCE FIELD) ============
    f['prf_042'] = prf_probability(flux, LCC_THRESHOLD_042)
    f['prf_085'] = prf_probability(flux, LCC_THRESHOLD_085)
    f['prf_tt'] = prf_probability(flux, LCC_THRESHOLD_TT)
    
    # ============ PHOTONIC CLUSTERING ============
    photonic = photonic_cluster_features(flux)
    f.update(photonic)
    
    # ============ EXISTENCE INTENSITY TENSOR ============
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
    
    # ============ TDE SHAPE ============
    f['peak_position'] = peak_idx / n
    f['peak_flux'] = flux[peak_idx]
    f['peak_snr'] = snr[peak_idx]
    f['time_to_peak'] = t[peak_idx] - t[0]
    f['time_from_peak'] = t[-1] - t[peak_idx]
    f['peak_time_ratio'] = f['time_to_peak'] / (f['duration'] + 1e-8)
    
    # Rise rate
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
    
    # ============ LCC THRESHOLDS ============
    norm = (flux - f['flux_mean']) / (f['flux_std'] + 1e-8)
    f['lcc_042_ratio'] = np.sum(np.abs(norm) > LCC_THRESHOLD_042) / n
    f['lcc_085_ratio'] = np.sum(np.abs(norm) > LCC_THRESHOLD_085) / n
    f['lcc_tt_ratio'] = np.sum(np.abs(norm) > LCC_THRESHOLD_TT) / n
    f['tralse_ratio'] = (np.sum(np.abs(norm) > LCC_THRESHOLD_042) - np.sum(np.abs(norm) > LCC_THRESHOLD_085)) / (np.sum(np.abs(norm) > LCC_THRESHOLD_042) + 1)
    
    # ============ GILE / SACRED INTERVAL ============
    f['gile_width'] = f['flux_std'] / (f['flux_range'] + 1e-8)
    sacred_low = f['flux_mean'] - 2*f['flux_std']/3
    sacred_high = f['flux_mean'] + f['flux_std']/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / n
    
    # ============ VARIABILITY ============
    f['excess_var'] = (np.var(flux) - np.mean(err**2)) / (f['flux_mean']**2 + 1e-8)
    f['amp_ratio'] = f['flux_range'] / (np.abs(f['flux_mean']) + 1e-8)
    f['cv'] = f['flux_std'] / (np.abs(f['flux_mean']) + 1e-8)
    
    if n > 2:
        residual = (flux - f['flux_mean']) / (err + 1e-8)
        f['stetson_j'] = np.sum(np.sign(residual[:-1] * residual[1:]) * 
                                np.sqrt(np.abs(residual[:-1] * residual[1:])))
    else:
        f['stetson_j'] = 0
    
    # ============ PER-FILTER ============
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
            
            # Per-filter LCC resonance
            if len(ff) > 5:
                mid_f = len(ff) // 2
                f[f'{filt}_lcc_resonance'] = lcc_resonance(ff[:mid_f], ff[mid_f:])
            else:
                f[f'{filt}_lcc_resonance'] = 0
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
            f[f'{filt}_std'] = 0
            f[f'{filt}_max'] = 0
            f[f'{filt}_frac'] = 0
            f[f'{filt}_lcc_resonance'] = 0
            filter_means[filt] = 0
    
    # Color as E-dimension
    blue = filter_means.get('u', 0) + filter_means.get('g', 0)
    red = filter_means.get('r', 0) + filter_means.get('i', 0) + filter_means.get('z', 0)
    f['blue_red_ratio'] = blue / (red + 1e-8)
    f['g_r'] = filter_means.get('g', 0) - filter_means.get('r', 0)
    
    # ============ QUANTUM TDE FINGERPRINT ============
    # Combine LCC resonance with power-law match
    f['quantum_tde_fingerprint'] = (
        f.get('lcc_rise_decline_resonance', 0) * 
        f.get('tde_slope_match', 0) * 
        f.get('rate_asymmetry', 1)
    )
    
    return f

# Extract features
print("\nExtracting TI Quantum features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_ti_quantum_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    feat['Z_EBV'] = feat['Z'] * feat['EBV']
    train_feats.append(feat)
    if (i+1) % 500 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_ti_quantum_features(r['object_id'], test_lc_dict)
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
print(f"New TI Quantum features: lcc_*_resonance, jeff_*, prf_*, photonic_*, quantum_tde_fingerprint")

scaler = StandardScaler()
X_s = scaler.fit_transform(X)
X_test_s = scaler.transform(X_test)

# Training
print("\n" + "="*60)
print("TRAINING (TI Quantum Ensemble)")
print("="*60)

n_folds = 5
skf = StratifiedKFold(n_splits=n_folds, shuffle=True, random_state=42)

models = {
    'hgb_deep': HistGradientBoostingClassifier(
        max_iter=1000, max_depth=12, learning_rate=0.015,
        l2_regularization=0.005, max_bins=255, min_samples_leaf=3,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=80, random_state=42
    ),
    'hgb_med': HistGradientBoostingClassifier(
        max_iter=500, max_depth=6, learning_rate=0.04,
        l2_regularization=0.05, max_bins=200, min_samples_leaf=10,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=40, random_state=43
    ),
    'rf': RandomForestClassifier(
        n_estimators=500, max_depth=12, min_samples_leaf=3,
        class_weight='balanced', random_state=44, n_jobs=-1
    ),
    'et': ExtraTreesClassifier(
        n_estimators=500, max_depth=15, min_samples_leaf=2,
        class_weight='balanced', random_state=45, n_jobs=-1
    ),
}

oof_preds = {name: np.zeros(len(X)) for name in models}
test_preds = {name: np.zeros(len(X_test)) for name in models}

for name, model in models.items():
    print(f"\n  Training {name}...")
    
    for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
        Xt, Xv = X_s[ti], X_s[vi]
        yt, yv = y[ti], y[vi]
        
        m = type(model)(**model.get_params())
        m.fit(Xt, yt)
        
        oof_preds[name][vi] = m.predict_proba(Xv)[:, 1]
        test_preds[name] += m.predict_proba(X_test_s)[:, 1] / n_folds
    
    # OOF F1
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.1, 0.7, 0.01):
        f1 = f1_score(y, (oof_preds[name] >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    print(f"    {name}: OOF F1 = {best_f1:.4f} @ {best_th:.2f}")

# Simple average blend
oof_blend = np.mean([oof_preds[n] for n in models], axis=0)
test_blend = np.mean([test_preds[n] for n in models], axis=0)

# Optimal threshold
best_f1, best_th = 0, 0.5
for th in np.arange(0.05, 0.8, 0.005):
    f1 = f1_score(y, (oof_blend >= th).astype(int), zero_division=0)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print("\n" + "="*60)
print("FINAL RESULTS")
print("="*60)
print(f"\nOptimal threshold: {best_th:.3f}")
print(f"Final OOF F1: {best_f1:.4f}")

pred = (test_blend >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v9.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v9.csv")

# LCC Virus validation
print("\n" + "="*60)
print("LCC VIRUS RESONANCE VALIDATION")
print("="*60)

train_df_with_target = train_df.copy()
train_df_with_target['target'] = y

tde_mask = train_df_with_target['target'] == 1
non_tde_mask = train_df_with_target['target'] == 0

resonance_features = ['lcc_self_resonance', 'lcc_rise_decline_resonance', 'lcc_first_last_resonance', 'quantum_tde_fingerprint']
print("\nLCC Resonance Features (TDE vs Non-TDE):")
for feat in resonance_features:
    if feat in train_df_with_target.columns:
        tde_mean = train_df_with_target.loc[tde_mask, feat].mean()
        non_mean = train_df_with_target.loc[non_tde_mask, feat].mean()
        ratio = tde_mean / (non_mean + 1e-8)
        print(f"  {feat:30s}: TDE={tde_mean:+.4f}, Non-TDE={non_mean:+.4f}, Ratio={ratio:.2f}")

# Jeff Time validation
print("\nJeff Time Features (TDE vs Non-TDE):")
jeff_features = ['jeff_photonic_memory', 'jeff_fiction', 'jeff_freedom', 'jeff_love_entanglement']
for feat in jeff_features:
    if feat in train_df_with_target.columns:
        tde_mean = train_df_with_target.loc[tde_mask, feat].mean()
        non_mean = train_df_with_target.loc[non_tde_mask, feat].mean()
        print(f"  {feat:30s}: TDE={tde_mean:.4f}, Non-TDE={non_mean:.4f}")

# Feature importance
print("\n" + "="*60)
print("TOP 25 FEATURES")
print("="*60)

# Use last RF for importance
last_rf = RandomForestClassifier(n_estimators=500, max_depth=12, min_samples_leaf=3,
                                  class_weight='balanced', random_state=44, n_jobs=-1)
last_rf.fit(X_s, y)
importance = last_rf.feature_importances_
top_idx = np.argsort(importance)[::-1][:25]

for i, idx in enumerate(top_idx):
    if idx < len(cols):
        print(f"{i+1:2d}. {cols[idx]:35s}: {importance[idx]:.4f}")
