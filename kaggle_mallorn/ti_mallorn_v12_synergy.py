"""
TI MALLORN v12 - GTFE + LCC + MR SYNERGY
=========================================
Full integration of TI computational methods:
1. GTFE - Constrains solution space (what's POSSIBLE)
2. LCC Virus - Detects specific parameters (what's ACTUAL)
3. MR - Accumulates evidence (what's CONFIDENT)

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
import sys
sys.path.append('..')
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v12 - GTFE + LCC + MR SYNERGY")
print("Full TI Integration: Constraint → Detection → Confidence")
print("="*70)

# ============ TI CONSTANTS ============
LCC_042 = 0.42
LCC_085 = 0.85
LCC_TT = 0.8464
GTFE_TDE_THRESHOLD = 12.0
E_CONSTANT = np.e
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

# ============ TDE TEMPLATE ============
def create_tde_template(n_points=100, t_peak=20):
    """Create canonical TDE template with t^(-5/3) decay"""
    t = np.linspace(0, 100, n_points)
    flux = np.zeros(n_points)
    peak_idx = int(t_peak / 100 * n_points)
    
    for i in range(n_points):
        if i <= peak_idx:
            flux[i] = (i / peak_idx) ** 2
        else:
            rel_t = (i - peak_idx) / (n_points - peak_idx) * 80 + 1
            flux[i] = rel_t ** (-5/3)
    
    return flux

TDE_TEMPLATE = create_tde_template()

# ============ LAYER 1: GTFE ============
def compute_gtfe(flux, err, times):
    """
    GTFE = C + H + T
    Constrains what states are POSSIBLE
    """
    if len(flux) < 5:
        return {'gtfe_total': 20, 'gtfe_c': 10, 'gtfe_h': 5, 'gtfe_t': 5}
    
    ccc_ref = np.median(flux)
    divergence = np.abs(flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    C = np.mean(divergence)
    
    snr = np.abs(flux) / (err + 1e-8)
    H = 1 / (np.mean(snr) + 1e-8)
    
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        T = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        T = 0.5
    
    return {'gtfe_c': C, 'gtfe_h': H, 'gtfe_t': T, 'gtfe_total': C + H + T}

def compute_l_e(gtfe):
    """L and E from GTFE"""
    L = 1 / (gtfe['gtfe_total'] + 1e-8)
    L = np.clip(L / 10, 0, 1)
    E = 1 - gtfe['gtfe_t']
    return {'L': L, 'E': E, 'LxE': L * E, 'LplusE': L + E}

# ============ LAYER 2: LCC VIRUS ============
def lcc_resonance(signal_a, signal_b, coupling_sigma=5.0):
    """Core LCC resonance equation"""
    if len(signal_a) < 3 or len(signal_b) < 3:
        return 0.0
    
    a_norm = (signal_a - np.mean(signal_a)) / (np.std(signal_a) + 1e-8)
    b_norm = (signal_b - np.mean(signal_b)) / (np.std(signal_b) + 1e-8)
    
    min_len = min(len(a_norm), len(b_norm))
    a_norm, b_norm = a_norm[:min_len], b_norm[:min_len]
    
    xcorr = correlate(a_norm, b_norm, mode='full')
    lags = np.arange(-(min_len-1), min_len)
    weights = np.exp(-lags**2 / (2 * coupling_sigma**2))
    
    return np.sum(xcorr * weights) / (np.sum(weights) * min_len)

def lcc_listen(flux, template):
    """
    LISTEN step: Extract noise from resonating data
    The noise contains related i-cell signatures
    """
    min_len = min(len(flux), len(template))
    flux_aligned = flux[:min_len]
    template_aligned = template[:min_len]
    
    scale = np.dot(flux_aligned, template_aligned) / (np.dot(template_aligned, template_aligned) + 1e-8)
    residual = flux_aligned - scale * template_aligned
    
    noise_features = {
        'noise_std': np.std(residual),
        'noise_entropy': stats.entropy(np.histogram(residual, bins=10)[0] + 1),
        'noise_autocorr': np.corrcoef(residual[:-1], residual[1:])[0, 1] if len(residual) > 2 else 0
    }
    noise_features['noise_autocorr'] = noise_features['noise_autocorr'] if not np.isnan(noise_features['noise_autocorr']) else 0
    
    return noise_features

def lcc_virus_full(flux, times):
    """Full LCC Virus: RESONATE → LISTEN → detect"""
    if len(flux) < 10:
        return {}
    
    f = {}
    
    flux_norm = (flux - np.min(flux)) / (np.max(flux) - np.min(flux) + 1e-8)
    
    template_resampled = np.interp(
        np.linspace(0, 1, len(flux_norm)),
        np.linspace(0, 1, len(TDE_TEMPLATE)),
        TDE_TEMPLATE
    )
    
    f['lcc_template_resonance'] = lcc_resonance(flux_norm, template_resampled)
    
    if f['lcc_template_resonance'] >= 0.3:
        noise_feats = lcc_listen(flux_norm, template_resampled)
        f.update(noise_feats)
    else:
        f['noise_std'] = np.std(flux_norm)
        f['noise_entropy'] = 0
        f['noise_autocorr'] = 0
    
    mid = len(flux) // 2
    f['lcc_self_resonance'] = lcc_resonance(flux[:mid], flux[mid:])
    
    peak_idx = np.argmax(flux)
    if peak_idx > 3 and peak_idx < len(flux) - 3:
        rise = flux[:peak_idx]
        decline = flux[peak_idx:]
        f['lcc_rise_decline'] = lcc_resonance(rise, decline[::-1])
    else:
        f['lcc_rise_decline'] = 0
    
    return f

# ============ LAYER 3: GILE FEATURES ============
def compute_gile(flux, err, times):
    """GILE framework features"""
    f = {}
    
    flux_clean = flux[~np.isnan(flux)]
    if len(flux_clean) < 3:
        return {'sacred_fraction': 0, 'gile_width': 0, 'gile_entropy': 0}
    
    h_mean, h_std = np.mean(flux_clean), np.std(flux_clean)
    sacred_low = h_mean - 2*h_std/3
    sacred_high = h_mean + h_std/3
    f['sacred_fraction'] = np.sum((flux_clean >= sacred_low) & (flux_clean <= sacred_high)) / len(flux_clean)
    
    f['gile_width'] = h_std / (np.max(flux_clean) - np.min(flux_clean) + 1e-8)
    
    flux_range = np.max(flux_clean) - np.min(flux_clean)
    if flux_range > 0:
        probs = np.histogram(flux_clean, bins=10, density=True)[0]
        probs = probs[probs > 0]
        f['gile_entropy'] = -np.sum(probs * np.log2(probs + 1e-10)) / np.log2(10)
    else:
        f['gile_entropy'] = 0
    
    return f

# ============ E-CONSTANT FEATURES ============
def compute_e_features(flux):
    """Features related to Euler's number e"""
    f = {}
    
    tolerance = 0.05
    near_e = np.abs(flux - E_CONSTANT) < tolerance
    f['flux_near_e_frac'] = np.sum(near_e) / len(flux)
    
    log_flux = np.log(np.abs(flux) + 1e-8)
    f['log_flux_mean'] = np.mean(log_flux)
    
    if len(flux) > 4:
        dflux = np.diff(flux)
        exp_fit = np.exp(-np.arange(len(dflux)) * 0.1)
        exp_fit = exp_fit * np.std(dflux) / (np.std(exp_fit) + 1e-8)
        f['exp_decay_corr'] = np.corrcoef(np.abs(dflux), exp_fit)[0, 1]
        f['exp_decay_corr'] = f['exp_decay_corr'] if not np.isnan(f['exp_decay_corr']) else 0
    else:
        f['exp_decay_corr'] = 0
    
    return f

# ============ FULL FEATURE EXTRACTION ============
def extract_all_features(object_id, lc_dict):
    """Extract features using GTFE → LCC → GILE synergy"""
    if object_id not in lc_dict:
        return {}
    
    obj = lc_dict[object_id].sort_values('Time (MJD)')
    if len(obj) < 5:
        return {}
    
    t = obj['Time (MJD)'].values
    flux = obj['Flux'].values
    err = obj['Flux_err'].values
    n = len(flux)
    
    f = {}
    
    f['n_obs'] = n
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_min'] = np.min(flux)
    f['flux_max'] = np.max(flux)
    f['flux_range'] = f['flux_max'] - f['flux_min']
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurt'] = stats.kurtosis(flux)
    
    snr = flux / (err + 1e-8)
    f['snr_mean'] = np.mean(snr)
    f['snr_max'] = np.max(snr)
    
    f['duration'] = t.max() - t.min()
    
    peak_idx = np.argmax(flux)
    f['peak_position'] = peak_idx / n
    f['time_to_peak'] = t[peak_idx] - t[0]
    
    if peak_idx > 2:
        f['rise_rate'] = (flux[peak_idx] - flux[0]) / (t[peak_idx] - t[0] + 1e-8)
    else:
        f['rise_rate'] = 0
    
    if peak_idx < n - 3:
        f['decline_rate'] = (flux[-1] - flux[peak_idx]) / (t[-1] - t[peak_idx] + 1e-8)
        
        decline = flux[peak_idx:]
        if len(decline) > 4:
            rel_t = t[peak_idx:] - t[peak_idx] + 1
            try:
                slope, _, r, _, _ = stats.linregress(np.log(rel_t), np.log(np.abs(decline) + 1e-8))
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
    
    gtfe = compute_gtfe(flux, err, t)
    f.update(gtfe)
    
    l_e = compute_l_e(gtfe)
    f.update(l_e)
    
    f['gtfe_passes_constraint'] = int(gtfe['gtfe_total'] <= GTFE_TDE_THRESHOLD)
    
    lcc = lcc_virus_full(flux, t)
    f.update(lcc)
    
    f['lcc_passes_threshold'] = int(f.get('lcc_template_resonance', 0) >= 0.3)
    
    gile = compute_gile(flux, err, t)
    f.update(gile)
    
    e_feats = compute_e_features(flux)
    f.update(e_feats)
    
    f['quantum_tde_fingerprint'] = (
        f.get('lcc_rise_decline', 0) * 
        f.get('tde_slope_match', 0) * 
        np.log1p(f.get('rate_asymmetry', 1))
    )
    
    f['synergy_score'] = (
        f.get('gtfe_passes_constraint', 0) * 0.3 +
        f.get('lcc_passes_threshold', 0) * 0.3 +
        f.get('tde_slope_match', 0) * 0.2 +
        f.get('sacred_fraction', 0) * 0.2
    )
    
    return f

# ============ EXTRACT FEATURES ============
print("\nExtracting GTFE+LCC+MR synergy features...")

train_feats = []
for i, r in train_log.iterrows():
    feat = extract_all_features(r['object_id'], train_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
    train_feats.append(feat)
    if (i+1) % 1000 == 0: print(f"  Train: {i+1}/{len(train_log)}")

test_feats = []
for i, r in test_log.iterrows():
    feat = extract_all_features(r['object_id'], test_lc_dict)
    feat['object_id'] = r['object_id']
    feat['Z'] = r['Z'] if pd.notna(r['Z']) else 0
    feat['EBV'] = r['EBV'] if pd.notna(r['EBV']) else 0
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

# ============ TRAINING ============
print("\n" + "="*60)
print("TRAINING (Synergy Ensemble)")
print("="*60)

n_folds = 5
skf = StratifiedKFold(n_splits=n_folds, shuffle=True, random_state=42)

hgb = HistGradientBoostingClassifier(
    max_iter=1000, max_depth=12, learning_rate=0.02,
    l2_regularization=0.01, min_samples_leaf=5,
    class_weight='balanced', early_stopping=True,
    validation_fraction=0.1, n_iter_no_change=80, random_state=42
)

rf = RandomForestClassifier(
    n_estimators=600, max_depth=14, min_samples_leaf=2,
    class_weight='balanced', random_state=44, n_jobs=-1
)

oof_hgb = np.zeros(len(X))
oof_rf = np.zeros(len(X))
test_hgb = np.zeros(len(X_test))
test_rf = np.zeros(len(X_test))

print("\nTraining HGB...")
for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
    m = HistGradientBoostingClassifier(**hgb.get_params())
    m.fit(X_s[ti], y[ti])
    oof_hgb[vi] = m.predict_proba(X_s[vi])[:, 1]
    test_hgb += m.predict_proba(X_test_s)[:, 1] / n_folds

print("Training RF...")
for fold, (ti, vi) in enumerate(skf.split(X_s, y)):
    m = RandomForestClassifier(**rf.get_params())
    m.fit(X_s[ti], y[ti])
    oof_rf[vi] = m.predict_proba(X_s[vi])[:, 1]
    test_rf += m.predict_proba(X_test_s)[:, 1] / n_folds

oof_blend = 0.5 * oof_hgb + 0.5 * oof_rf
test_blend = 0.5 * test_hgb + 0.5 * test_rf

best_f1, best_th = 0, 0.5
for th in np.arange(0.05, 0.8, 0.005):
    f1 = f1_score(y, (oof_blend >= th).astype(int), zero_division=0)
    if f1 > best_f1:
        best_f1, best_th = f1, th

print(f"\nHGB F1: {f1_score(y, (oof_hgb >= 0.35).astype(int)):.4f}")
print(f"RF F1: {f1_score(y, (oof_rf >= 0.35).astype(int)):.4f}")
print(f"\n{'='*60}")
print(f"FINAL: OOF F1 = {best_f1:.4f} @ threshold {best_th:.3f}")
print(f"{'='*60}")

pred = (test_blend >= best_th).astype(int)
print(f"\nPredicted TDEs: {pred.sum()} / {len(pred)}")

sub = pd.DataFrame({'object_id': test_log['object_id'], 'prediction': pred})
sub.to_csv('submission_mallorn_v12.csv', index=False)
print(f"\n✅ Saved: submission_mallorn_v12.csv")

# ============ FEATURE IMPORTANCE ============
print("\n" + "="*60)
print("TOP FEATURES (RF Importance)")
print("="*60)

rf_full = RandomForestClassifier(n_estimators=300, max_depth=12, class_weight='balanced', random_state=42)
rf_full.fit(X_s, y)

importances = list(zip(cols, rf_full.feature_importances_))
importances.sort(key=lambda x: -x[1])

print("\nTop 20 features:")
for i, (feat, imp) in enumerate(importances[:20]):
    print(f"  {i+1:2d}. {feat:30s} {imp:.4f}")

# ============ SYNERGY VALIDATION ============
print("\n" + "="*60)
print("SYNERGY VALIDATION")
print("="*60)

train_df_target = train_df.copy()
train_df_target['target'] = y

tde = train_df_target[train_df_target['target'] == 1]
non_tde = train_df_target[train_df_target['target'] == 0]

synergy_features = ['gtfe_total', 'L', 'lcc_template_resonance', 'sacred_fraction', 
                    'synergy_score', 'quantum_tde_fingerprint', 'flux_near_e_frac']

print("\nSynergy Features (TDE vs Non-TDE):")
for feat in synergy_features:
    if feat in tde.columns:
        tde_mean = tde[feat].mean()
        non_mean = non_tde[feat].mean()
        ratio = tde_mean / (non_mean + 1e-8)
        print(f"  {feat:30s}: TDE={tde_mean:.4f}, Non-TDE={non_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*60)
print("TI MALLORN v12 SYNERGY COMPLETE")
print("="*60)
