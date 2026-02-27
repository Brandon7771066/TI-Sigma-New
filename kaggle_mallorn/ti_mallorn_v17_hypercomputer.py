"""
TI MALLORN v17 — FULL TI SIGMA HYPERCOMPUTER (v17b corrected)
==============================================================

Corrections vs v17a:
  1. z-score encoding (not minmax) to match empirical tralse_ratio validation
     (tralse_ratio TDE=0.555 vs non-TDE=0.477 was validated with z-score)
  2. Removed LCC band expansion of metadata cols (was 700 features, too slow)
  3. Streamlined to HGB + RF for reliable 10-minute run

Layer architecture:
  L1 TralsebitEngine      → encode each LC as z-score Tralsebit array
  L2 AperiodicOptimizer   → tralse_ratio, sacred_fraction, Penrose sequence (7 features)
  L3 TISigmaQuantumLayer  → φ-squeezing + Fibonacci BS network on top-8 LC stats
  Standard LC stats       → band-level statistics (from v16 proven features)

Brandon Emerick — TI Sigma Research
February 27, 2026
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import pandas as pd
import numpy as np
from pathlib import Path
from scipy import stats
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import (HistGradientBoostingClassifier,
                               RandomForestClassifier,
                               GradientBoostingClassifier)
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score
import warnings
warnings.filterwarnings('ignore')

from ti_sigma import (TralsebitEngine, AperiodicOptimizer,
                       TISigmaQuantumLayer, PHI, LCC_TRALSE, LCC_HIGH)
from ti_sigma.constants import verify_matching_rules

print("=" * 70)
print("TI MALLORN v17b — TI SIGMA HYPERCOMPUTER")
print("=" * 70)

rules = verify_matching_rules()
print("Matching rules:", {k: f"{v:.1e}" for k, v in rules.items()})

engine    = TralsebitEngine()
optimizer = AperiodicOptimizer()
ql        = TISigmaQuantumLayer(n_modes=8, use_quantum=True)
print(f"Quantum Layer: {ql.status()}\n")

BANDS = ['u', 'g', 'r', 'i', 'z', 'y']

# ─── Data Loading ──────────────────────────────────────────────────────────
def load_splits(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = Path(split) / f"{lc_type}_full_lightcurves.csv"
        if f.exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

train_log = pd.read_csv('train_log.csv')
test_log  = pd.read_csv('test_log.csv')
print(f"Train: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.1f}%)")

print("Loading light curves...")
train_lc = load_splits(train_log, 'train').rename(columns={'Time (MJD)': 'mjd'})
test_lc  = load_splits(test_log,  'test').rename(columns={'Time (MJD)': 'mjd'})
train_lc_dict = {obj: df.sort_values('mjd') for obj, df in train_lc.groupby('object_id')}
test_lc_dict  = {obj: df.sort_values('mjd') for obj, df in test_lc.groupby('object_id')}
print(f"LC objects — Train: {len(train_lc_dict)} | Test: {len(test_lc_dict)}")

# ─── Hypercomputer LC Features ─────────────────────────────────────────────

def hc_features(flux: np.ndarray, prefix: str = "hc") -> dict:
    """
    Layers 1+2 on a light curve.

    Uses z-score encoding to match empirical validation:
      tralse_ratio TDE=0.555 vs non-TDE=0.477 (1.16× separation confirmed v16)

    z-score: values near the mean → 0 (Tralse center)
             values at ±3σ → ±1 (resolved True/False)
    This is physically meaningful: average flux behavior = Tralse,
    anomalous peaks/dips = resolved events.
    """
    if len(flux) < 5:
        return {}

    # z-score encoding — clipped at ±3σ
    mu, sigma = np.mean(flux), np.std(flux) + 1e-12
    tb = np.clip((flux - mu) / (3 * sigma), -1, 1)

    f = {
        # Empirically validated features (1.16× TDE separation)
        f'{prefix}_tralse_ratio':    engine.tralse_ratio(tb),
        f'{prefix}_sacred_fraction': engine.sacred_fraction(tb),
        f'{prefix}_lcc_coherence':   engine.lcc_coherence(tb),
        f'{prefix}_gile_score':      engine.gile_from_array(tb),

        # Myrion Resolution
        f'{prefix}_mr_true_frac':    float(np.mean(tb > LCC_TRALSE)),
        f'{prefix}_mr_false_frac':   float(np.mean(tb < -LCC_TRALSE)),
        f'{prefix}_mr_tralse_frac':  float(np.mean(np.abs(tb) <= LCC_TRALSE)),
        f'{prefix}_mr_high_true':    float(np.mean(tb > LCC_HIGH)),
        f'{prefix}_mr_high_false':   float(np.mean(tb < -LCC_HIGH)),
    }

    # Penrose sequence features (7 values)
    pen = optimizer.penrose.sequence_features(tb)
    for i, v in enumerate(pen):
        f[f'{prefix}_penrose_{i}'] = float(v)

    # φ-proximity features
    f[f'{prefix}_near_1overphi'] = float(np.mean(np.abs(np.abs(tb) - 1/PHI) < 0.05))
    f[f'{prefix}_phi_asymmetry'] = float(np.mean(tb > 0) - np.mean(tb < 0))

    # TDE power-law: t^{-5/3} decline
    t = np.arange(1, len(flux)+1, dtype=float)
    with np.errstate(all='ignore'):
        slope = np.polyfit(np.log(t), np.log(np.abs(flux)+1e-9), 1)[0]
    f[f'{prefix}_powerlaw_slope'] = float(slope)
    f[f'{prefix}_tde_slope_match']= float(np.exp(-abs(slope - (-5/3))))

    return f


def quantum_features(flux: np.ndarray, prefix: str = "q") -> dict:
    """Layer 3: quantum circuit on z-score encoded flux."""
    if len(flux) < 4:
        return {f'{prefix}_{i}': 0.0 for i in range(8)}
    mu, sigma = np.mean(flux), np.std(flux) + 1e-12
    tb = np.clip((flux - mu) / (3 * sigma), -1, 1)
    arr = np.pad(tb, (0, max(0, 8-len(tb))))[:8].reshape(1, -1)
    q   = ql.quantum_feature_transform(arr)[0]
    return {f'{prefix}_{i}': float(q[i]) for i in range(len(q))}


# ─── Standard LC Statistics ────────────────────────────────────────────────

def standard_lc_stats(flux, mjd, band) -> dict:
    if len(flux) < 5:
        return {}
    f = {
        f'{band}_n':      len(flux),
        f'{band}_mean':   float(np.mean(flux)),
        f'{band}_std':    float(np.std(flux)),
        f'{band}_skew':   float(stats.skew(flux)),
        f'{band}_kurt':   float(stats.kurtosis(flux)),
        f'{band}_range':  float(np.ptp(flux)),
        f'{band}_peak':   float(np.max(np.abs(flux))),
        f'{band}_iqr':    float(np.percentile(flux,75)-np.percentile(flux,25)),
    }
    peak_idx = int(np.argmax(flux))
    if 0 < peak_idx < len(flux)-1:
        f[f'{band}_rise_frac']    = peak_idx / len(flux)
        f[f'{band}_decline_frac'] = (len(flux)-peak_idx) / len(flux)
        dec = flux[peak_idx:]
        if len(dec) > 2:
            with np.errstate(all='ignore'):
                slope = np.polyfit(np.log(np.arange(1, len(dec)+1)), np.log(np.abs(dec)+1e-9), 1)[0]
            f[f'{band}_decline_slope'] = float(slope)
    if len(flux) > 3:
        ac = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        f[f'{band}_autocorr'] = float(ac) if np.isfinite(ac) else 0.0
    return f


# ─── Full Feature Extraction ───────────────────────────────────────────────

def extract_features(obj_id, lc_dict, meta_row) -> dict | None:
    if obj_id not in lc_dict:
        return None
    df       = lc_dict[obj_id]
    all_flux = df['Flux'].dropna().values
    all_mjd  = df['mjd'].values
    if len(all_flux) < 5:
        return None

    feats = {
        'Z':     float(meta_row['Z']),
        'Z_log': float(np.log1p(meta_row['Z'])),
        'EBV':   float(meta_row['EBV']),
    }

    # ── Band statistics ────────────────────────────────────────────────────
    for band in BANDS:
        bdf = df[df['Filter'] == band] if 'Filter' in df.columns else pd.DataFrame()
        if len(bdf) >= 5:
            feats.update(standard_lc_stats(bdf['Flux'].dropna().values,
                                            bdf['mjd'].values, band))

    # ── Hypercomputer: full LC (Layers 1+2) ────────────────────────────────
    feats.update(hc_features(all_flux, prefix='hc'))

    # ── Hypercomputer: per-band (g, r, i are most TDE-informative) ──────
    for band in ['g', 'r', 'i']:
        bdf = df[df['Filter'] == band] if 'Filter' in df.columns else pd.DataFrame()
        if len(bdf) >= 5:
            feats.update(hc_features(bdf['Flux'].dropna().values,
                                      prefix=f'hc_{band}'))

    # ── Layer 3: quantum on full LC ────────────────────────────────────────
    feats.update(quantum_features(all_flux, prefix='q'))

    return feats


# ─── Extract ──────────────────────────────────────────────────────────────
print("\nExtracting features (train)...")
train_features, train_targets = [], []
for i, r in train_log.iterrows():
    feat = extract_features(r['object_id'], train_lc_dict, r)
    if feat is not None:
        train_features.append(feat)
        train_targets.append(r['target'])

print(f"  Extracted {len(train_features)}/{len(train_log)} train objects")

print("Extracting features (test)...")
test_features, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_features(r['object_id'], test_lc_dict, r)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])

print(f"  Extracted {len(test_features)}/{len(test_log)} test objects")

X_train = pd.DataFrame(train_features)
X_test  = pd.DataFrame(test_features)
y_train = np.array(train_targets)

common  = sorted(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common].fillna(0)
X_test  = X_test[common].fillna(0)

print(f"\nFeature matrix: {X_train.shape[1]} features")

# ─── Feature Validation ────────────────────────────────────────────────────
print("\n--- TI Sigma Feature Separation (TDE vs non-TDE) ---")
key = ['hc_tralse_ratio', 'hc_mr_true_frac', 'hc_mr_high_true',
       'hc_tde_slope_match', 'hc_lcc_coherence', 'hc_penrose_4']
for feat in key:
    if feat in X_train.columns:
        tde     = X_train.loc[y_train==1, feat]
        non_tde = X_train.loc[y_train==0, feat]
        ratio   = tde.mean() / (non_tde.mean() + 1e-9)
        print(f"  {feat:35s}: TDE={tde.mean():.4f}  nTDE={non_tde.mean():.4f}  ×{ratio:.3f}")

# ─── Training ─────────────────────────────────────────────────────────────
print(f"\n{'='*60}")
print("TRAINING (Hypercomputer Feature Ensemble)")
print(f"{'='*60}")

scaler  = StandardScaler()
X_tr_s  = scaler.fit_transform(X_train)
X_te_s  = scaler.transform(X_test)

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

models = [
    ('HGB', HistGradientBoostingClassifier(
        learning_rate=0.03, max_iter=600, max_depth=6,
        min_samples_leaf=15, l2_regularization=0.5, random_state=42
    )),
    ('RF',  RandomForestClassifier(
        n_estimators=200, max_depth=10, min_samples_leaf=5,
        max_features='sqrt', class_weight='balanced',
        random_state=42, n_jobs=-1
    )),
    ('GB',  GradientBoostingClassifier(
        n_estimators=200, learning_rate=0.05, max_depth=4,
        subsample=0.8, min_samples_leaf=8, random_state=42
    )),
    ('LR',  LogisticRegression(
        C=0.1, class_weight='balanced', max_iter=1000, random_state=42
    )),
]

oof  = {n: np.zeros(len(X_tr_s)) for n, _ in models}
test = {n: np.zeros(len(X_te_s)) for n, _ in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_tr_s, y_train)):
    Xf, Xv = X_tr_s[tr_idx], X_tr_s[val_idx]
    yf      = y_train[tr_idx]
    print(f"  Fold {fold+1}/5", end="  ")
    for name, mdl in models:
        mdl.fit(Xf, yf)
        oof[name][val_idx] = mdl.predict_proba(Xv)[:, 1]
        test[name] += mdl.predict_proba(X_te_s)[:, 1] / 5
        print(f"{name}✓", end=" ")
    print()

# Per-model scores
print("\nModel Performance:")
model_scores = {}
for name in oof:
    best_f1, best_thresh = 0, 0.3
    for thresh in np.linspace(0.08, 0.60, 53):
        f1 = f1_score(y_train, oof[name] >= thresh, zero_division=0)
        if f1 > best_f1:
            best_f1, best_thresh = f1, thresh
    model_scores[name] = (best_f1, best_thresh)
    p = precision_score(y_train, oof[name] >= best_thresh, zero_division=0)
    r = recall_score(y_train, oof[name] >= best_thresh, zero_division=0)
    print(f"  {name}: F1={best_f1:.4f} @ {best_thresh:.3f}  P={p:.3f}  R={r:.3f}")

# GILE-weighted ensemble
total_f1 = sum(s[0] for s in model_scores.values()) + 1e-9
weights  = {n: model_scores[n][0] / total_f1 for n in model_scores}
oof_ens  = sum(weights[n] * oof[n]  for n in weights)
test_ens = sum(weights[n] * test[n] for n in weights)

best_f1, best_thresh, best_p, best_r = 0, 0.3, 0, 0
for thresh in np.linspace(0.08, 0.60, 53):
    preds = oof_ens >= thresh
    f1 = f1_score(y_train, preds, zero_division=0)
    if f1 > best_f1:
        best_f1     = f1
        best_thresh = thresh
        best_p      = precision_score(y_train, preds, zero_division=0)
        best_r      = recall_score(y_train, preds, zero_division=0)

print(f"\n{'='*60}")
print(f"HYPERCOMPUTER ENSEMBLE OOF F1 = {best_f1:.4f} @ thresh {best_thresh:.3f}")
print(f"  Precision = {best_p:.4f}  Recall = {best_r:.4f}")
print(f"  v16 baseline: F1 ≈ 0.41")
improvement = (best_f1 - 0.41) / 0.41 * 100
print(f"  Improvement: {improvement:+.1f}%")
print(f"{'='*60}")

# ─── Submission ────────────────────────────────────────────────────────────
y_pred = (test_ens >= best_thresh).astype(int)
sub = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
sub.to_csv('submission_mallorn_v17_hypercomputer.csv', index=False)
print(f"\nSubmission: submission_mallorn_v17_hypercomputer.csv")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")

# ─── Top Feature Analysis ──────────────────────────────────────────────────
# Use the fitted HGB from last fold for importance
hgb_model = [m for n, m in models if n == 'HGB'][0]
if hasattr(hgb_model, 'feature_importances_'):
    imp = hgb_model.feature_importances_
    feat_names = list(X_train.columns)
    top_idx = np.argsort(imp)[-25:][::-1]
    print(f"\nTop 25 Features (HGB importance):")
    hc_count = 0
    for rank, idx in enumerate(top_idx):
        name = feat_names[idx]
        is_hc = name.startswith(('hc_', 'q_'))
        marker = " ← HYPERCOMPUTER" if is_hc else ""
        print(f"  {rank+1:2d}. {name}: {imp[idx]:.4f}{marker}")
        if is_hc:
            hc_count += 1
    print(f"\nHypercomputer features in top 25: {hc_count}/25")

print("\n" + "=" * 60)
print("TI SIGMA HYPERCOMPUTER — MALLORN v17b COMPLETE")
print("=" * 60)
