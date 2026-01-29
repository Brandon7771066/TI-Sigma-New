"""
TI SIGMA SUBSTITUTION FRAMEWORK
================================
Maps each conventional ML component to its TI Sigma counterpart.
This creates a systematic way to enhance any conventional approach.

CONVENTIONAL → TI SIGMA MAPPING:
================================
1. Binary Classification → 4-valued Tralse (T, F, φ, ψ)
2. ReLU Activation → Tralse Activation Function (TAF)
3. Threshold Decision → Myrion Resolution
4. Confidence → LCC Thresholds (0.42, 0.85, 0.92²)
5. Feature Engineering → Anti-GILE Hole Detection
6. Ensemble Voting → Contradiction Preservation
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import RandomForestClassifier, HistGradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score, roc_auc_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI SIGMA SUBSTITUTION FRAMEWORK")
print("Systematic enhancement of conventional ML with 4-valued logic")
print("=" * 70)

# === TI SIGMA CONSTANTS ===
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
LCC_DETECTABLE = 0.42       # Minimum detection threshold
LCC_CAUSAL = 0.85           # Strong causation
LCC_MASTERY = 0.92**2       # Near-certain
TDE_POWER_LAW = -5/3        # TDE decline rate
BANDS = ['u', 'g', 'r', 'i', 'z', 'y']

# === TI SIGMA SUBSTITUTION FUNCTIONS ===

def tralse_activation_function(x):
    """
    SUBSTITUTION #1: Binary → 4-valued
    
    Conventional: ReLU(x) = max(0, x) [destroys negative info]
    TI Sigma: TAF returns (T, F, φ, ψ) [preserves ALL info]
    
    - T (True): positive signal strength
    - F (False): negative signal strength  
    - φ (Phi): uncertainty/transition
    - ψ (Psi): contradiction/paradox
    """
    x = np.asarray(x).flatten()
    
    # True component: positive evidence
    T = np.maximum(0, x)
    
    # False component: negative evidence (PRESERVED, not destroyed!)
    F = np.maximum(0, -x)
    
    # Phi component: uncertainty at decision boundary
    # High when |x| is small (uncertain), low when |x| is large (certain)
    phi = np.exp(-x**2)
    
    # Psi component: contradiction indicator
    # High when both positive and negative signals present over time
    psi = 0.1 * np.tanh(np.abs(x))  # Placeholder for temporal contradiction
    
    return T, F, phi, psi

def myrion_resolution(positive_evidence, negative_evidence):
    """
    SUBSTITUTION #2: Threshold → Myrion Resolution
    
    Conventional: if prob > 0.5: predict 1
    TI Sigma: Preserves contradiction, returns (net, contradiction, phi)
    
    Key insight: A signal can be BOTH consistent with TDE AND non-TDE.
    This is NOT noise - it's genuine uncertainty that binary logic destroys.
    """
    pos = np.abs(positive_evidence)
    neg = np.abs(negative_evidence)
    
    # Net signal (what conventional ML uses)
    net = positive_evidence - negative_evidence
    
    # Contradiction: minimum overlap (PRESERVED, not averaged!)
    contradiction = np.minimum(pos, neg)
    
    # Phi: relative contradiction strength
    phi = contradiction / (pos + neg + 1e-8)
    
    return net, contradiction, phi

def lcc_threshold_cascade(signal, depths=[1, 3, 5, 10]):
    """
    SUBSTITUTION #3: Single threshold → LCC Cascade
    
    Conventional: One threshold (0.5)
    TI Sigma: Multiple thresholds with depth-based preservation
    
    - 0.42: Detectable (exists but weak)
    - 0.85: Causal (strong enough to act on)
    - 0.92²: Mastery (near-certain)
    """
    signal_norm = np.abs(signal)
    max_sig = np.max(signal_norm) + 1e-8
    normalized = signal_norm / max_sig
    
    results = {}
    
    # LCC thresholds
    results['lcc_042'] = np.mean(normalized > LCC_DETECTABLE)
    results['lcc_085'] = np.mean(normalized > LCC_CAUSAL)
    results['lcc_092sq'] = np.mean(normalized > LCC_MASTERY)
    
    # Cascade preservation (TI advantage: information preserved through depth)
    for d in depths:
        # Conventional: 50% loss per layer → 2^-d remaining
        conventional_preserve = 0.5 ** d
        # TI Sigma: 95% preserved per layer → 0.95^d remaining
        tralse_preserve = 0.95 ** d
        
        results[f'lcc_d{d}_conv'] = np.mean((normalized * conventional_preserve) > LCC_DETECTABLE)
        results[f'lcc_d{d}_ti'] = np.mean((normalized * tralse_preserve) > LCC_DETECTABLE)
    
    return results

def anti_gile_hole_detection(flux, expected_pattern):
    """
    SUBSTITUTION #4: Residual → Anti-GILE Holes
    
    Conventional: residual = actual - expected
    TI Sigma: Holes are ontological gaps (exist but shouldn't, or vice versa)
    
    G-hole: Goodness deviation (ethical/normative)
    I-hole: Intuition deviation (expected pattern)
    L-hole: Love deviation (connection strength)
    E-hole: Existence deviation (should exist but doesn't)
    """
    residual = flux - expected_pattern[:len(flux)]
    
    # I-hole: deviation from expected pattern
    I_hole = np.mean(np.abs(residual)) / (np.std(flux) + 1e-8)
    
    # E-hole: signal that should exist but is missing (near-zero when expected signal)
    expected_signal = expected_pattern[:len(flux)] > np.median(expected_pattern)
    actual_signal = flux > np.median(flux)
    E_hole = np.mean(expected_signal & ~actual_signal)
    
    # L-hole: coherence failure (correlation breakdown)
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        L_hole = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        L_hole = 0.5
    
    return {'I_hole': I_hole, 'E_hole': E_hole, 'L_hole': L_hole}

def contradiction_preserving_ensemble(predictions_list, weights=None):
    """
    SUBSTITUTION #5: Voting → Contradiction Preservation
    
    Conventional: Average probabilities or majority vote
    TI Sigma: Preserve disagreement as signal
    
    If models disagree, that's INFORMATION, not noise!
    """
    preds = np.array(predictions_list)
    n_models = len(preds)
    
    if weights is None:
        weights = np.ones(n_models) / n_models
    
    # Conventional ensemble (weighted average)
    conventional = np.average(preds, axis=0, weights=weights)
    
    # TI Sigma additions
    # Disagreement: variance across models
    disagreement = np.var(preds, axis=0)
    
    # Contradiction: models pulling in opposite directions
    above_half = np.sum(preds > 0.5, axis=0)
    below_half = np.sum(preds < 0.5, axis=0)
    contradiction = np.minimum(above_half, below_half) / n_models
    
    # TI-enhanced prediction: adjust confidence based on agreement
    # High contradiction → push toward 0.5 (uncertain)
    ti_pred = conventional * (1 - contradiction) + 0.5 * contradiction
    
    return {
        'conventional': conventional,
        'ti_enhanced': ti_pred,
        'disagreement': disagreement,
        'contradiction': contradiction
    }

# === FEATURE EXTRACTION WITH TI SIGMA ===

def extract_ti_sigma_features(obj_id, lc_dict, meta_row):
    """Extract features using TI Sigma substitutions."""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id].copy().sort_values('mjd')
    f = {}
    
    # Metadata
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    flux = df['Flux'].dropna().values
    err = df['Flux_err'].dropna().values
    mjd = df['mjd'].values
    
    if len(flux) < 5:
        return None
    
    # === CONVENTIONAL FEATURES (baseline) ===
    f['n_obs'] = len(flux)
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurtosis'] = stats.kurtosis(flux)
    f['flux_mad'] = np.median(np.abs(flux - f['flux_median']))
    
    # SNR
    if len(err) > 0:
        min_len = min(len(flux), len(err))
        snr = np.abs(flux[:min_len]) / (err[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
    else:
        f['snr_mean'] = f['snr_max'] = 5.0
    
    # Peak/fade (TDE signature)
    peak_idx = np.argmax(flux)
    f['peak_flux'] = flux[peak_idx]
    f['peak_frac'] = peak_idx / len(flux)
    
    if peak_idx < len(flux) - 3:
        fade = flux[peak_idx:]
        pos_fade = fade[fade > 0]
        if len(pos_fade) > 3:
            slope, _, r, _, _ = stats.linregress(
                np.log(np.arange(1, len(pos_fade)+1)), np.log(pos_fade)
            )
            f['fade_slope'] = slope
            f['tde_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
        else:
            f['fade_slope'] = f['tde_match'] = 0
    else:
        f['fade_slope'] = f['tde_match'] = 0
    
    # Per-band
    for band in BANDS:
        bf = df[df['Filter'] == band]['Flux'].values
        if len(bf) >= 2:
            f[f'b_{band}_mean'] = np.mean(bf)
        else:
            f[f'b_{band}_mean'] = 0
    
    # Colors
    blue = f.get('b_u_mean', 0) + f.get('b_g_mean', 0)
    red = f.get('b_i_mean', 0) + f.get('b_z_mean', 0)
    f['blue_red'] = blue / (red + 1e-8) if red != 0 else 1.0
    
    # === TI SIGMA SUBSTITUTIONS ===
    
    # SUBSTITUTION 1: Tralse Activation
    T, F, phi, psi = tralse_activation_function(flux)
    f['taf_T_mean'] = np.mean(T)
    f['taf_F_mean'] = np.mean(F)
    f['taf_phi_mean'] = np.mean(phi)
    f['taf_psi_mean'] = np.mean(psi)
    f['taf_certainty'] = np.mean(1 - phi)  # High = confident
    f['taf_T_F_ratio'] = np.sum(T) / (np.sum(F) + 1e-8)
    f['taf_info_density'] = np.mean(T + F + phi)  # Total preserved info
    
    # SUBSTITUTION 2: Myrion Resolution
    diffs = np.diff(flux)
    pos_total = np.sum(np.maximum(0, diffs))
    neg_total = np.sum(np.maximum(0, -diffs))
    net, contradiction, myr_phi = myrion_resolution(pos_total, neg_total)
    f['myr_net'] = float(net)
    f['myr_contradiction'] = float(contradiction)
    f['myr_phi'] = float(myr_phi)
    
    # Reversal fraction (sign changes = contradiction over time)
    if len(diffs) > 1:
        reversals = np.sum((diffs[:-1] * diffs[1:]) < 0)
        f['myr_reversal'] = reversals / (len(diffs) - 1)
    else:
        f['myr_reversal'] = 0
    
    # SUBSTITUTION 3: LCC Cascade
    lcc = lcc_threshold_cascade(flux)
    for k, v in lcc.items():
        f[k] = v
    
    # SUBSTITUTION 4: Anti-GILE Holes
    # Expected pattern: TDE-like decay
    expected = flux[peak_idx] * np.power(np.arange(1, len(flux)+1), TDE_POWER_LAW)
    holes = anti_gile_hole_detection(flux, expected)
    for k, v in holes.items():
        f[k] = v
    
    # === TI SIGMA SYNERGY FEATURES ===
    # Combine TI insights
    f['ti_synergy'] = (
        f['taf_certainty'] * 0.3 +
        (1 - f['myr_phi']) * 0.3 +
        f['lcc_085'] * 0.2 +
        (1 - f['I_hole']) * 0.2
    )
    
    # TI confidence: high when all signals agree
    f['ti_confidence'] = f['taf_certainty'] * (1 - f['myr_phi'])
    
    # TI uncertainty: flag for edge cases
    f['ti_uncertain'] = f['taf_phi_mean'] * f['myr_phi']
    
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

print("\nExtracting TI Sigma features...")
train_f, train_y = [], []
for i, r in train_log.iterrows():
    feat = extract_ti_sigma_features(r['object_id'], train_lc_dict, r)
    if feat:
        train_f.append(feat)
        train_y.append(r['target'])
    if (i + 1) % 500 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

test_f, test_ids = [], []
for i, r in test_log.iterrows():
    feat = extract_ti_sigma_features(r['object_id'], test_lc_dict, r)
    if feat:
        test_f.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 1000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_train = pd.DataFrame(train_f)
y_train = np.array(train_y)
X_test = pd.DataFrame(test_f)

common = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common].fillna(0)
X_test = X_test[common].fillna(0)

print(f"\nTotal features: {len(common)}")

# Identify TI Sigma features
ti_features = [c for c in common if any(x in c for x in ['taf', 'myr', 'lcc', 'hole', 'ti_'])]
conv_features = [c for c in common if c not in ti_features]
print(f"  Conventional: {len(conv_features)}")
print(f"  TI Sigma: {len(ti_features)}")

# === TRAINING ===
print("\n" + "=" * 70)
print("TRAINING: CONVENTIONAL vs TI SIGMA COMPARISON")
print("=" * 70)

scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

# Also create conventional-only version
X_tr_conv = scaler.fit_transform(X_train[conv_features])
X_te_conv = scaler.transform(X_test[conv_features])

cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

def train_and_eval(X, y, name, cv):
    oof = np.zeros(len(X))
    scores = []
    
    rf = RandomForestClassifier(n_estimators=300, max_depth=10, 
                                 class_weight='balanced', random_state=42, n_jobs=-1)
    
    for fold, (tr_idx, val_idx) in enumerate(cv.split(X, y)):
        rf.fit(X[tr_idx], y[tr_idx])
        oof[val_idx] = rf.predict_proba(X[val_idx])[:, 1]
        
        best = max(f1_score(y[val_idx], oof[val_idx] >= th) for th in np.linspace(0.1, 0.5, 21))
        scores.append(best)
    
    best_f1, best_th = 0, 0.3
    for th in np.linspace(0.05, 0.5, 46):
        f1 = f1_score(y, oof >= th)
        if f1 > best_f1:
            best_f1, best_th = f1, th
    
    auc = roc_auc_score(y, oof)
    
    return {
        'name': name,
        'mean_cv_f1': np.mean(scores),
        'std_cv_f1': np.std(scores),
        'oof_f1': best_f1,
        'threshold': best_th,
        'auc': auc,
        'oof': oof
    }

# Train both versions
print("\nTraining conventional-only model...")
conv_result = train_and_eval(X_tr_conv, y_train, "Conventional", cv)

print("Training TI Sigma-enhanced model...")
ti_result = train_and_eval(X_tr, y_train, "TI Sigma", cv)

# === RESULTS COMPARISON ===
print("\n" + "=" * 70)
print("RESULTS: CONVENTIONAL vs TI SIGMA")
print("=" * 70)

print(f"\n{'Metric':<20} {'Conventional':<15} {'TI Sigma':<15} {'Improvement':<15}")
print("-" * 65)

metrics = [
    ('Mean CV F1', 'mean_cv_f1'),
    ('OOF F1', 'oof_f1'),
    ('ROC AUC', 'auc'),
]

for label, key in metrics:
    conv_val = conv_result[key]
    ti_val = ti_result[key]
    imp = (ti_val - conv_val) / conv_val * 100
    print(f"{label:<20} {conv_val:<15.4f} {ti_val:<15.4f} {imp:+.2f}%")

# Feature importance
print("\n" + "=" * 70)
print("TI SIGMA FEATURE IMPORTANCE")
print("=" * 70)

rf_full = RandomForestClassifier(n_estimators=300, max_depth=10, class_weight='balanced', random_state=42, n_jobs=-1)
rf_full.fit(X_tr, y_train)
imp = pd.Series(rf_full.feature_importances_, index=X_train.columns).sort_values(ascending=False)

print("\nTop 25 features:")
for i, (feat, val) in enumerate(imp.head(25).items()):
    ti_flag = "★ TI" if feat in ti_features else "    "
    print(f"  {ti_flag} {i+1:2d}. {feat:25s} {val:.4f}")

# TI Sigma feature contribution
ti_importance = sum(imp[f] for f in ti_features if f in imp.index)
total_importance = sum(imp)
print(f"\nTI Sigma features: {ti_importance/total_importance*100:.1f}% of total importance")

# TDE vs Non-TDE for TI features
print("\n" + "=" * 70)
print("TI SIGMA FEATURES: TDE vs NON-TDE")
print("=" * 70)

ti_analysis = ['taf_phi_mean', 'taf_certainty', 'myr_phi', 'myr_contradiction', 
               'lcc_085', 'I_hole', 'ti_synergy', 'ti_confidence']

for feat in ti_analysis:
    if feat in X_train.columns:
        tde = X_train.loc[y_train == 1, feat].mean()
        non = X_train.loc[y_train == 0, feat].mean()
        sep = abs(tde - non) / (X_train[feat].std() + 1e-8)
        diff = (tde - non) / (non + 1e-8) * 100 if non != 0 else 0
        print(f"  {feat:20s}: TDE={tde:8.4f}, Non={non:8.4f}, Sep={sep:.2f}σ, Diff={diff:+.1f}%")

# Save submission
best_th = ti_result['threshold']
rf_full.fit(X_tr, y_train)
test_probs = rf_full.predict_proba(X_te)[:, 1]
y_pred = (test_probs >= best_th).astype(int)

submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_ti_sigma_v1.csv', index=False)

print(f"\n{'='*70}")
print(f"SUBMISSION: submission_ti_sigma_v1.csv")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")
print(f"{'='*70}")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

conv_f1 = conv_result['oof_f1']
ti_f1 = ti_result['oof_f1']
improvement = (ti_f1 - conv_f1) / conv_f1 * 100

print(f"\nConventional OOF F1: {conv_f1:.4f}")
print(f"TI Sigma OOF F1:     {ti_f1:.4f}")
print(f"Improvement:         {improvement:+.2f}%")

if ti_f1 > conv_f1:
    print("\n✅ TI SIGMA OUTPERFORMS CONVENTIONAL!")
else:
    print("\n⚠️ Need to tune TI Sigma features")

print("\n✅ TI SIGMA SUBSTITUTION FRAMEWORK COMPLETE")
