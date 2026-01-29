"""
TI MALLORN v16 LITE - TRALSE NEURAL ARCHITECTURE (Fast Version)
===============================================================
Core Tralse features with faster training.
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI MALLORN v16 LITE - TRALSE NEURAL ARCHITECTURE")
print("=" * 70)

# Constants
PHI = (1 + np.sqrt(5)) / 2
BANDS = ['u', 'g', 'r', 'i', 'z', 'y']
TDE_POWER_LAW = -5/3
LCC_DETECTABLE = 0.42
LCC_CAUSAL = 0.85

def tralse_activation(x):
    """TAF: returns (t, f, phi, psi)"""
    x = np.asarray(x).flatten()
    t = np.maximum(0, x)
    f = np.maximum(0, -x)
    phi = np.exp(-x**2)
    psi = 0.1 * np.tanh(np.abs(x))
    return t, f, phi, psi

def myrion_resolve(pos, neg):
    """Myrion Resolution"""
    contradiction = np.minimum(np.abs(pos), np.abs(neg))
    net = pos - neg
    phi = contradiction / (np.abs(pos) + np.abs(neg) + 1e-8)
    return net, contradiction, phi

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

if 'Time (MJD)' in train_lc.columns:
    train_lc = train_lc.rename(columns={'Time (MJD)': 'mjd'})
    test_lc = test_lc.rename(columns={'Time (MJD)': 'mjd'})

train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

def extract_features(obj_id, lc_dict, meta_row):
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id]
    f = {}
    
    # Metadata
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    # Global flux
    all_flux = df['Flux'].dropna().values
    if len(all_flux) < 5:
        return None
    
    f['flux_mean'] = np.mean(all_flux)
    f['flux_std'] = np.std(all_flux)
    f['flux_skew'] = stats.skew(all_flux)
    f['n_obs'] = len(all_flux)
    
    # ===== TRALSE FEATURES =====
    t, fal, phi, psi = tralse_activation(all_flux)
    f['taf_t_mean'] = np.mean(t)
    f['taf_f_mean'] = np.mean(fal)
    f['taf_phi_mean'] = np.mean(phi)
    f['taf_certainty'] = np.mean(1 - phi)
    f['taf_tf_ratio'] = np.sum(t) / (np.sum(fal) + 1e-8)
    f['taf_info_density'] = np.mean(t + fal + phi + psi)
    
    # ===== MYRION FEATURES =====
    flux_diffs = np.diff(all_flux)
    pos_diffs = np.sum(np.maximum(0, flux_diffs))
    neg_diffs = np.sum(np.maximum(0, -flux_diffs))
    
    net, contra, myr_phi = myrion_resolve(pos_diffs, neg_diffs)
    f['myr_contradiction'] = float(contra)
    f['myr_phi'] = float(myr_phi)
    
    # Reversal fraction
    if len(flux_diffs) > 1:
        reversals = np.sum((flux_diffs[:-1] * flux_diffs[1:]) < 0)
        f['myr_reversal_frac'] = reversals / (len(flux_diffs) - 1)
    else:
        f['myr_reversal_frac'] = 0
    
    # ===== LCC THRESHOLDS =====
    flux_norm = (all_flux - np.mean(all_flux)) / (np.std(all_flux) + 1e-8)
    f['lcc_042'] = np.mean(np.abs(flux_norm) > LCC_DETECTABLE)
    f['lcc_085'] = np.mean(np.abs(flux_norm) > LCC_CAUSAL)
    
    # LCC deep (simulated cascade)
    for d in [1, 3, 5]:
        preserve = 0.95 ** d
        f[f'lcc_d{d}_085'] = np.mean(np.abs(flux_norm * preserve) > LCC_CAUSAL)
    
    # ===== ANTI-GILE HOLE DETECTION =====
    # G-hole: deviation from power law
    peak_idx = np.argmax(all_flux)
    if peak_idx < len(all_flux) - 3:
        decline = all_flux[peak_idx:]
        expected = all_flux[peak_idx] * np.power(
            np.arange(1, len(decline) + 1), TDE_POWER_LAW
        )
        f['hole_G'] = np.mean(np.abs(decline - expected)) / (np.mean(np.abs(all_flux)) + 1e-8)
    else:
        f['hole_G'] = 0.5
    
    # ===== GTFE (from v15) =====
    ccc_ref = np.median(all_flux)
    divergence = np.abs(all_flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    f['gtfe_c'] = np.mean(divergence)
    
    err = df['Flux_err'].values if 'Flux_err' in df.columns else np.ones(len(all_flux))
    err_clean = err[~np.isnan(err)]
    if len(err_clean) > 0:
        min_len = min(len(all_flux), len(err_clean))
        snr = np.abs(all_flux[:min_len]) / (err_clean[:min_len] + 1e-8)
        f['gtfe_h'] = 1 / (np.mean(snr) + 1e-8)
        f['snr_mean'] = np.mean(snr)
    else:
        f['gtfe_h'] = 0.5
        f['snr_mean'] = 5.0
    
    if len(all_flux) > 3:
        autocorr = np.corrcoef(all_flux[:-1], all_flux[1:])[0, 1]
        f['gtfe_t'] = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        f['gtfe_t'] = 0.5
    
    f['gtfe_total'] = f['gtfe_c'] + f['gtfe_h'] + f['gtfe_t']
    f['L'] = 1 / (f['gtfe_total'] + 1e-8)
    
    # Sacred fraction
    h_mean, h_std = np.mean(all_flux), np.std(all_flux)
    sacred_low = h_mean - 2*h_std/3
    sacred_high = h_mean + h_std/3
    f['E'] = np.sum((all_flux >= sacred_low) & (all_flux <= sacred_high)) / len(all_flux)
    f['LxE'] = f['L'] * f['E']
    
    # TDE power law
    if peak_idx < len(all_flux) - 5:
        decline_flux = all_flux[peak_idx:]
        positive_decline = decline_flux[decline_flux > 0]
        if len(positive_decline) > 3:
            log_flux = np.log(positive_decline)
            log_times = np.log(np.arange(1, len(positive_decline) + 1))
            slope, _, r, _, _ = stats.linregress(log_times, log_flux)
            f['decline_slope'] = slope
            f['tde_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
        else:
            f['decline_slope'] = 0
            f['tde_match'] = 0
    else:
        f['decline_slope'] = 0
        f['tde_match'] = 0
    
    # ===== TRALSE SYNERGY =====
    f['tralse_synergy'] = (
        f['taf_certainty'] * 0.25 +
        (1 - f['myr_phi']) * 0.25 +
        (1 - f['hole_G']) * 0.25 +
        f['lcc_085'] * 0.25
    )
    
    # Per-band basics
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) > 2:
            f[f'b_{band}_mean'] = band_df['Flux'].mean()
        else:
            f[f'b_{band}_mean'] = 0
    
    # Blue-red ratio
    blue = f.get('b_u_mean', 0) + f.get('b_g_mean', 0)
    red = f.get('b_i_mean', 0) + f.get('b_z_mean', 0) + f.get('b_y_mean', 0)
    f['blue_red_ratio'] = blue / (red + 1e-8) if red != 0 else 1.0
    
    return f

# Extract features
print("\nExtracting features...")
train_features, train_targets = [], []
for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict, r)
    if feat is not None:
        train_features.append(feat)
        train_targets.append(r['target'])
    if (i + 1) % 1000 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

X_train = pd.DataFrame(train_features)
y_train = np.array(train_targets)

print("\nExtracting test features...")
test_features, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_features(r['object_id'], test_lc_dict, r)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 2000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_test = pd.DataFrame(test_features)

# Align
common_cols = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common_cols].fillna(0)
X_test = X_test[common_cols].fillna(0)
print(f"\nFeatures: {len(common_cols)}")

# Train
print("\n" + "=" * 60)
print("TRAINING (2-Model Ensemble)")
print("=" * 60)

scaler = StandardScaler()
X_tr_sc = scaler.fit_transform(X_train)
X_te_sc = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

hgb = HistGradientBoostingClassifier(
    learning_rate=0.05, max_iter=500, max_depth=6, 
    min_samples_leaf=15, random_state=42
)
rf = RandomForestClassifier(
    n_estimators=200, max_depth=10, min_samples_leaf=5,
    class_weight='balanced', random_state=42, n_jobs=-1
)

models = [('HGB', hgb), ('RF', rf)]
oof_preds = {name: np.zeros(len(X_train)) for name, _ in models}
test_preds = {name: np.zeros(len(X_test)) for name, _ in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr_sc, y_train)):
    X_tr, X_val = X_tr_sc[tr_idx], X_tr_sc[val_idx]
    y_tr, y_val = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models:
        model.fit(X_tr, y_tr)
        oof_preds[name][val_idx] = model.predict_proba(X_val)[:, 1]
        test_preds[name] += model.predict_proba(X_te_sc)[:, 1] / 5
    
    print(f"  Fold {fold+1}/5 complete")

# Ensemble
print("\nModel Performance:")
model_scores = {}
for name in oof_preds:
    best_f1, best_thresh = 0, 0.3
    for thresh in np.linspace(0.1, 0.6, 26):
        f1 = f1_score(y_train, oof_preds[name] >= thresh)
        if f1 > best_f1:
            best_f1, best_thresh = f1, thresh
    model_scores[name] = (best_f1, best_thresh)
    print(f"  {name}: F1={best_f1:.4f} @ {best_thresh:.3f}")

total_f1 = sum(s[0] for s in model_scores.values())
weights = {name: model_scores[name][0] / total_f1 for name in model_scores}

oof_ens = sum(weights[name] * oof_preds[name] for name in weights)
test_ens = sum(weights[name] * test_preds[name] for name in weights)

# Find threshold
best_f1, best_thresh = 0, 0.3
for thresh in np.linspace(0.1, 0.5, 41):
    f1 = f1_score(y_train, oof_ens >= thresh)
    if f1 > best_f1:
        best_f1, best_thresh = f1, thresh

preds_train = oof_ens >= best_thresh
prec = precision_score(y_train, preds_train)
rec = recall_score(y_train, preds_train)

print(f"\n{'='*60}")
print(f"FINAL: OOF F1 = {best_f1:.4f} @ threshold {best_thresh:.3f}")
print(f"       Precision = {prec:.4f}, Recall = {rec:.4f}")
print(f"{'='*60}")

# Save
y_pred = (test_ens >= best_thresh).astype(int)
submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_mallorn_v16_tralse_lite.csv', index=False)
print(f"\nPredicted TDEs: {y_pred.sum()} / {len(y_pred)}")
print(f"Saved: submission_mallorn_v16_tralse_lite.csv")

# Feature importance
print("\n" + "=" * 60)
print("TOP TRALSE FEATURES")
print("=" * 60)

rf.fit(X_tr_sc, y_train)
imp = pd.Series(rf.feature_importances_, index=X_train.columns).sort_values(ascending=False)

tralse_feats = ['taf', 'myr', 'lcc', 'hole', 'tralse', 'LxE']
print("\nTop 20 features:")
for i, (feat, val) in enumerate(imp.head(20).items()):
    ti = "★" if any(x in feat for x in tralse_feats) else " "
    print(f"  {ti} {i+1:2d}. {feat:25s} {val:.4f}")

# TDE vs non-TDE comparison
print("\n" + "=" * 60)
print("TDE vs NON-TDE: TRALSE FEATURES")
print("=" * 60)

key_feats = ['taf_certainty', 'taf_phi_mean', 'myr_phi', 'myr_contradiction',
             'lcc_085', 'hole_G', 'tralse_synergy', 'LxE']

for feat in key_feats:
    if feat in X_train.columns:
        tde_mean = X_train.loc[y_train == 1, feat].mean()
        non_tde_mean = X_train.loc[y_train == 0, feat].mean()
        diff = (tde_mean - non_tde_mean) / (non_tde_mean + 1e-8) * 100
        print(f"  {feat:20s}: TDE={tde_mean:.4f}, Non-TDE={non_tde_mean:.4f}, Diff={diff:+.1f}%")

print("\n✅ TI MALLORN v16 LITE COMPLETE")
