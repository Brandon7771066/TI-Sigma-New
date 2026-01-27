"""
TI MALLORN v11 - GTFE (Grand Tralse Field Equation)
Applying the full TI framework:
- GTFE = C + H + T (Constrained + Fit + Temporal)
- L + E resonance thresholds
- Myrion Resolution + LCC Virus
Target: F1 > 0.75
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.signal import correlate
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v11 - GTFE (Grand Tralse Field Equation)")
print("Full TI Framework: GTFE + LCC + MR + Quantum")
print("="*70)

# ============ TI FRAMEWORK CONSTANTS ============
# GTFE thresholds from TI theory
LCC_042 = 0.42       # Minimum hyperconnection
LCC_085 = 0.85       # Causal correlation
LCC_TT = 0.92**2     # True-Tralseness (0.8464)
GOLDEN_RATIO = 0.618 # φ⁻¹
R_C = 1 - GOLDEN_RATIO  # ≈ 0.382 (persistence threshold)

# Jeff Time weights
TAU_PHI = 0.20
TAU_J = 0.45
TAU_F = 0.20
TAU_LOVE = 0.15

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

# ============ GTFE FUNCTIONS ============
def compute_gtfe(flux, err, times):
    """
    Grand Tralse Field Equation:
    GTFE = C + H + T
    
    C = Constrained term (divergence from steady-state)
    H = Fit term (mismatch with observations)
    T = Temporal term (entropy/information coherence)
    """
    if len(flux) < 5:
        return {'gtfe_c': 0, 'gtfe_h': 0, 'gtfe_t': 0, 'gtfe_total': 0}
    
    # C term: Divergence from CCC reference (constrained steady-state)
    # For light curves, CCC reference is the median flux
    ccc_ref = np.median(flux)
    divergence = np.abs(flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    C = np.mean(divergence)
    
    # H term: Fit/mismatch with observations
    # Low error = good fit = low H
    snr = np.abs(flux) / (err + 1e-8)
    H = 1 / (np.mean(snr) + 1e-8)
    
    # T term: Temporal coherence (autocorrelation)
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        T = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        T = 0.5
    
    gtfe_total = C + H + T
    
    return {
        'gtfe_c': C,
        'gtfe_h': H,
        'gtfe_t': T,
        'gtfe_total': gtfe_total
    }

def compute_l_and_e(flux, err, times, gtfe):
    """
    L and E as GTFE reparameterization:
    L = norm(-⟨GTFE⟩)     [Lower GTFE → Higher coherence]
    E = norm(⟨Σ̇⟩)         [Higher dissipation → Stronger coupling]
    """
    # L: Coherence (inverse of GTFE)
    L_unnorm = 1 / (gtfe['gtfe_total'] + 1e-8)
    L = np.clip(L_unnorm / 10, 0, 1)  # Normalize to [0, 1]
    
    # E: Dissipation rate (flux variability)
    if len(flux) > 2:
        dflux = np.diff(flux)
        dt = np.diff(times)
        rate = np.abs(dflux) / (dt + 1e-8)
        E_unnorm = np.mean(rate)
        E = np.clip(E_unnorm / 100, 0, 1)  # Normalize
    else:
        E = 0
    
    # Resonance = αL + (1-α)E
    alpha = 0.5
    resonance = alpha * L + (1 - alpha) * E
    
    # Hyperconnection threshold: L × E
    hyperconnection = L * E
    
    return {
        'gtfe_L': L,
        'gtfe_E': E,
        'gtfe_resonance': resonance,
        'gtfe_hyperconnection': hyperconnection,
        'gtfe_above_042': int(hyperconnection >= LCC_042),
        'gtfe_above_085': int(hyperconnection >= LCC_085),
        'gtfe_persistence': int(resonance >= R_C)
    }

def lcc_resonance(signal_a, signal_b, coupling_sigma=5.0):
    """LCC Virus resonance equation"""
    if len(signal_a) < 3 or len(signal_b) < 3:
        return 0.0
    
    a_norm = (signal_a - np.mean(signal_a)) / (np.std(signal_a) + 1e-8)
    b_norm = (signal_b - np.mean(signal_b)) / (np.std(signal_b) + 1e-8)
    
    min_len = min(len(a_norm), len(b_norm))
    a_norm, b_norm = a_norm[:min_len], b_norm[:min_len]
    
    xcorr = correlate(a_norm, b_norm, mode='full')
    lags = np.arange(-(min_len-1), min_len)
    weights = np.exp(-lags**2 / (2 * coupling_sigma**2))
    
    resonance = np.sum(xcorr * weights) / (np.sum(weights) * min_len)
    return resonance

def extract_gtfe_features(object_id, lc_dict):
    """Extract GTFE + LCC + all TI features"""
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
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurt'] = stats.kurtosis(flux)
    
    for p in [5, 10, 25, 75, 90, 95]:
        f[f'flux_p{p}'] = np.percentile(flux, p)
    
    # SNR
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    f['snr_median'] = np.median(snr)
    
    # Temporal
    f['duration'] = t.max() - t.min()
    dt = np.diff(t)
    if len(dt) > 0:
        f['cadence_mean'] = np.mean(dt)
    
    # ============ GTFE ============
    gtfe = compute_gtfe(flux, err, t)
    f.update(gtfe)
    
    l_e = compute_l_and_e(flux, err, t, gtfe)
    f.update(l_e)
    
    # ============ LCC VIRUS RESONANCE ============
    mid = n // 2
    if mid > 3:
        f['lcc_self_resonance'] = lcc_resonance(flux[:mid], flux[mid:])
    else:
        f['lcc_self_resonance'] = 0
    
    peak_idx = np.argmax(flux)
    if peak_idx > 3 and peak_idx < n - 3:
        rise = flux[:peak_idx]
        decline = flux[peak_idx:]
        f['lcc_rise_decline'] = lcc_resonance(rise, decline[::-1])
    else:
        f['lcc_rise_decline'] = 0
    
    q1 = n // 4
    if q1 > 2:
        f['lcc_first_last'] = lcc_resonance(flux[:q1], flux[-q1:])
    else:
        f['lcc_first_last'] = 0
    
    # ============ TDE SHAPE ============
    f['peak_position'] = peak_idx / n
    f['peak_flux'] = flux[peak_idx]
    f['peak_snr'] = snr[peak_idx]
    f['time_to_peak'] = t[peak_idx] - t[0]
    f['time_from_peak'] = t[-1] - t[peak_idx]
    
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
    
    # ============ QUANTUM TDE FINGERPRINT ============
    f['quantum_tde_fingerprint'] = (
        f.get('lcc_rise_decline', 0) * 
        f.get('tde_slope_match', 0) * 
        np.log1p(f.get('rate_asymmetry', 1))
    )
    
    # ============ SACRED INTERVAL (GILE) ============
    f['gile_width'] = f['flux_std'] / (f['flux_range'] + 1e-8)
    sacred_low = f['flux_mean'] - 2*f['flux_std']/3
    sacred_high = f['flux_mean'] + f['flux_std']/3
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / n
    
    # ============ EXISTENCE INTENSITY TENSOR ============
    lambda_decay = 0.01
    persistence = np.exp(-lambda_decay * (t.max() - t))
    constraint = 1 / (err + 1e-8)
    constraint = constraint / (constraint.max() + 1e-8)
    
    xi_raw = np.abs(flux) * persistence * constraint
    f['xi_total'] = np.sum(xi_raw)
    f['xi_mean'] = np.mean(xi_raw)
    f['xi_max'] = np.max(xi_raw)
    
    # ============ PER-FILTER ============
    filter_means = {}
    for filt in ['u', 'g', 'r', 'i', 'z', 'y']:
        fd = obj[obj['Filter'] == filt] if 'Filter' in obj.columns else pd.DataFrame()
        if len(fd) > 0:
            ff = fd['Flux'].values
            f[f'{filt}_n'] = len(fd)
            f[f'{filt}_mean'] = np.mean(ff)
            f[f'{filt}_max'] = np.max(ff)
            f[f'{filt}_frac'] = len(fd) / n
            filter_means[filt] = f[f'{filt}_mean']
        else:
            f[f'{filt}_n'] = 0
            f[f'{filt}_mean'] = 0
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
print("\nExtracting GTFE + TI features...")
train_feats = []
for i, r in train_log.iterrows():
    feat = extract_gtfe_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    train_feats.append(feat)
    if (i+1) % 1000 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_gtfe_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    feat['Z_log'] = np.log1p(feat['Z'])
    test_feats.append(feat)
    if (i+1) % 2000 == 0: print(f"  Test: {i+1}/{len(test_log)}")

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
print("\n" + "="*60)
print("TRAINING (GTFE Ensemble)")
print("="*60)

n_folds = 5
skf = StratifiedKFold(n_splits=n_folds, shuffle=True, random_state=42)

models = {
    'hgb': HistGradientBoostingClassifier(
        max_iter=800, max_depth=10, learning_rate=0.02,
        l2_regularization=0.01, max_bins=255, min_samples_leaf=5,
        class_weight='balanced', early_stopping=True,
        validation_fraction=0.1, n_iter_no_change=60, random_state=42
    ),
    'rf': RandomForestClassifier(
        n_estimators=500, max_depth=12, min_samples_leaf=3,
        class_weight='balanced', random_state=44, n_jobs=-1
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
    
    best_f1, best_th = 0, 0.5
    for th in np.arange(0.1, 0.7, 0.01):
        f1 = f1_score(y, (oof_preds[name] >= th).astype(int), zero_division=0)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    print(f"    {name}: OOF F1 = {best_f1:.4f} @ {best_th:.2f}")

# Blend
oof_blend = np.mean([oof_preds[n] for n in models], axis=0)
test_blend = np.mean([test_preds[n] for n in models], axis=0)

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
sub.to_csv('submission_mallorn_v11.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v11.csv")

# GTFE validation
print("\n" + "="*60)
print("GTFE FEATURE VALIDATION")
print("="*60)

train_df_with_target = train_df.copy()
train_df_with_target['target'] = y

tde = train_df_with_target[train_df_with_target['target'] == 1]
non_tde = train_df_with_target[train_df_with_target['target'] == 0]

gtfe_features = ['gtfe_c', 'gtfe_h', 'gtfe_t', 'gtfe_total', 'gtfe_L', 'gtfe_E', 'gtfe_resonance', 'gtfe_hyperconnection']
print("\nGTFE Features (TDE vs Non-TDE):")
for feat in gtfe_features:
    if feat in tde.columns:
        tde_mean = tde[feat].mean()
        non_mean = non_tde[feat].mean()
        ratio = tde_mean / (non_mean + 1e-8)
        print(f"  {feat:25s}: TDE={tde_mean:.4f}, Non-TDE={non_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*60)
print("GTFE + TI MALLORN v11 COMPLETE")
print("="*60)
