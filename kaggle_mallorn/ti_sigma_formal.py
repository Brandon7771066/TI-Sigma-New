"""
TI SIGMA FORMAL IMPLEMENTATION
==============================
Rigorous implementation based on formal TI Sigma theory papers.

References:
- papers/TRALSE_NEURAL_NETWORKS_IMPROVING_AI.md (TAF definition)
- papers/MYRION_RESOLUTION_COMPLETE_SPEC.md (MR process)
- papers/ANTI_GILE_ONTOLOGICAL_HOLES.md (Hole theory)
- theories/tralsebit_14_dimensions.md (Dimensional structure)

Key Formal Definitions:
=======================
1. TAF(x) = (t, f, φ, ψ) normalized on unit sphere: t² + f² + φ² + ψ² = 1
2. Myrion Resolution: preserves contradiction = min(|pos|, |neg|), not just net
3. LCC Thresholds: 0.42 (detectable), 0.85 (causal), 0.92² (mastery)
4. Anti-GILE Holes: deficiency in dimension D manifests in other dimensions
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold, train_test_split
from sklearn.ensemble import RandomForestClassifier, HistGradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score, precision_score, recall_score, roc_auc_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI SIGMA FORMAL IMPLEMENTATION")
print("Rigorous formalization from TI Sigma theory papers")
print("=" * 70)

# === FORMAL CONSTANTS (from TI theory) ===
PHI = (1 + np.sqrt(5)) / 2           # Golden ratio φ = 1.618...
LCC_DETECTABLE = 0.42                # Minimum detection threshold
LCC_CAUSAL = 0.85                    # Strong causation threshold
LCC_MASTERY = 0.92 ** 2              # Near-certain (0.8464)
TDE_POWER_LAW = -5/3                 # TDE t^(-5/3) decay
BANDS = ['u', 'g', 'r', 'i', 'z', 'y']
TEMPERATURE = 1.0                    # TAF phi temperature parameter

# === FORMAL TAF (from TRALSE_NEURAL_NETWORKS_IMPROVING_AI.md) ===

def tralse_activation_function(x, gradient_history=None, temperature=TEMPERATURE):
    """
    FORMAL TAF Implementation.
    
    From paper:
    TAF(x) = (t, f, φ, ψ) where:
    - t ∈ [0, 1] = True amplitude (strong positive activation)
    - f ∈ [0, 1] = False amplitude (strong negative/inhibition)
    - φ ∈ [0, 1] = Phi amplitude (balanced/uncertain state)
    - ψ ∈ [0, 1] = Psi amplitude (superposition/potential)
    
    Constraint: t² + f² + φ² + ψ² = 1 (normalized on unit sphere)
    """
    x = np.asarray(x).flatten()
    
    # Step 1: Dual ReLU for T and F
    t = np.maximum(0, x)       # True amplitude (positive activation)
    f = np.maximum(0, -x)      # False amplitude (negative activation)
    
    # Step 2: Phi as uncertainty (high when x near zero)
    phi = np.exp(-x**2 / temperature)
    
    # Step 3: Psi as gradient uncertainty
    if gradient_history is not None and len(gradient_history) > 1:
        psi = np.tanh(np.var(gradient_history)) * np.ones_like(x)
    else:
        # For static features, use local variation as proxy
        if len(x) > 1:
            psi = np.tanh(np.abs(np.gradient(x))) * 0.5
        else:
            psi = np.zeros_like(x)
    
    # Step 4: Normalize to unit sphere (CRITICAL - from paper)
    norm = np.sqrt(t**2 + f**2 + phi**2 + psi**2 + 1e-10)
    t_norm = t / norm
    f_norm = f / norm
    phi_norm = phi / norm
    psi_norm = psi / norm
    
    return t_norm, f_norm, phi_norm, psi_norm


# === FORMAL MYRION RESOLUTION (from MYRION_RESOLUTION_COMPLETE_SPEC.md) ===

def myrion_resolution(pos_evidence, neg_evidence, context=None):
    """
    FORMAL Myrion Resolution Implementation.
    
    From paper:
    1. Filter incoherence (MR-1): Eliminate Double Tralse
    2. Classify valid states (MR-2): True-Tralse, Tralse-False, Tralse-Indeterminate
    3. Refine (MR-3+): Convergence toward stable classification
    
    Key: Contradictions are PRESERVED, not averaged!
    contradiction = min(|pos|, |neg|) - this is information, not noise
    """
    pos = np.abs(pos_evidence)
    neg = np.abs(neg_evidence)
    
    # Step 1: Detect contradiction (minimum overlap)
    contradiction = np.minimum(pos, neg)
    
    # Step 2: Net direction
    net = pos_evidence - neg_evidence
    
    # Step 3: Determine resolution type
    total = pos + neg + 1e-10
    
    # Phi = relative contradiction strength (0 = no contradiction, 1 = total contradiction)
    phi = contradiction / total
    
    # MR classification
    if np.abs(net) > 2 * contradiction:
        resolution_type = "dominant"  # Clear winner
    elif contradiction > 0.5 * total:
        resolution_type = "myrion"    # Genuine contradiction (preserved)
    else:
        resolution_type = "indeterminate"  # Tralse-Indeterminate
    
    # Double Tralse detection (MR-1)
    coherence = 1.0 - (contradiction / (total + 1e-10))
    is_double_tralse = coherence < LCC_DETECTABLE  # Below detection threshold
    
    return {
        'net': float(net),
        'contradiction': float(np.sum(contradiction)),
        'phi': float(np.mean(phi)),
        'resolution_type': resolution_type,
        'coherence': float(coherence),
        'is_double_tralse': is_double_tralse
    }


# === FORMAL LCC THRESHOLDS ===

def lcc_cascade(signal):
    """
    FORMAL LCC Cascade Implementation.
    
    From TI theory:
    - LCC 0.42: Detectable (exists but weak)
    - LCC 0.85: Causal (strong enough to act on)
    - LCC 0.92²: Mastery (near-certain)
    
    Applied to normalized signal strength.
    """
    signal = np.asarray(signal)
    max_sig = np.max(np.abs(signal)) + 1e-10
    normalized = np.abs(signal) / max_sig
    
    return {
        'lcc_042': float(np.mean(normalized > LCC_DETECTABLE)),
        'lcc_085': float(np.mean(normalized > LCC_CAUSAL)),
        'lcc_092sq': float(np.mean(normalized > LCC_MASTERY)),
        'above_detect_count': int(np.sum(normalized > LCC_DETECTABLE)),
        'above_causal_count': int(np.sum(normalized > LCC_CAUSAL))
    }


# === FORMAL ANTI-GILE HOLES (from ANTI_GILE_ONTOLOGICAL_HOLES.md) ===

def anti_gile_holes(actual, expected, flux_std):
    """
    FORMAL Anti-GILE Hole Detection.
    
    From paper:
    "A phenomenon X has an ontological hole in dimension D if:
    1. X's D-value approaches zero or negative
    2. X still has positive values in at least one other dimension
    3. X's apparent reality in other dimensions increases as D-hole deepens"
    
    GILE dimensions:
    - G (Goodness): Moral dimension - deviation from optimal pattern
    - I (Intuition): Conscious meaning - expected vs actual mismatch
    - L (Love): Aesthetic/relational - coherence failure
    - E (Existence): Ontological - should exist but doesn't
    """
    actual = np.asarray(actual)
    expected = np.asarray(expected)[:len(actual)]
    
    residual = actual - expected
    
    # I-hole: Intuition hole - deviation from expected pattern
    # "Binary logic cannot represent uncertainty" - this is the I-dimension hole
    I_hole = np.mean(np.abs(residual)) / (flux_std + 1e-10)
    
    # E-hole: Existence hole - signal that should exist but is missing
    # "X should exist in E but doesn't"
    expected_signal = expected > np.median(expected)
    actual_signal = actual > np.median(actual)
    E_hole = np.mean(expected_signal & ~actual_signal)
    
    # L-hole: Love hole - coherence/connection failure
    # "Loss of connection between temporal moments"
    if len(actual) > 3:
        autocorr = np.corrcoef(actual[:-1], actual[1:])[0, 1]
        L_hole = 1.0 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        L_hole = 0.5
    
    # G-hole: Goodness hole - deviation from optimal (TDE pattern)
    # For TDE, optimal = t^(-5/3) decay; deviation = lack of goodness
    if len(actual) > 5:
        peak_idx = np.argmax(actual)
        if peak_idx < len(actual) - 3:
            fade = actual[peak_idx:]
            pos_fade = fade[fade > 0]
            if len(pos_fade) > 3:
                slope, _, r, _, _ = stats.linregress(
                    np.log(np.arange(1, len(pos_fade)+1)), 
                    np.log(pos_fade + 1e-10)
                )
                # G-hole = deviation from ideal TDE slope
                G_hole = np.abs(slope - TDE_POWER_LAW) / 2
            else:
                G_hole = 1.0
        else:
            G_hole = 1.0
    else:
        G_hole = 1.0
    
    return {
        'I_hole': float(I_hole),
        'E_hole': float(E_hole),
        'L_hole': float(L_hole),
        'G_hole': float(G_hole),
        'total_hole': float((I_hole + E_hole + L_hole + G_hole) / 4)
    }


# === FEATURE EXTRACTION ===

def extract_ti_sigma_features(obj_id, lc_dict, meta_row):
    """Extract features using formal TI Sigma definitions."""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id].copy().sort_values('mjd')
    flux = df['Flux'].dropna().values
    err = df['Flux_err'].dropna().values
    mjd = df['mjd'].values
    
    if len(flux) < 5:
        return None
    
    f = {}
    
    # === METADATA (conventional) ===
    f['Z'] = meta_row['Z']
    f['Z_log'] = np.log1p(meta_row['Z'])
    f['EBV'] = meta_row['EBV']
    
    # === CONVENTIONAL FEATURES ===
    f['n_obs'] = len(flux)
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_skew'] = stats.skew(flux)
    f['flux_kurtosis'] = stats.kurtosis(flux)
    f['flux_mad'] = np.median(np.abs(flux - f['flux_median']))
    f['flux_iqr'] = np.percentile(flux, 75) - np.percentile(flux, 25)
    
    # SNR
    if len(err) > 0:
        min_len = min(len(flux), len(err))
        snr = np.abs(flux[:min_len]) / (err[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
        f['snr_std'] = np.std(snr)
    else:
        f['snr_mean'] = f['snr_max'] = f['snr_std'] = 5.0
    
    # Peak analysis
    peak_idx = np.argmax(flux)
    f['peak_flux'] = flux[peak_idx]
    f['peak_frac'] = peak_idx / len(flux)
    f['time_to_peak'] = mjd[peak_idx] - mjd[0] if peak_idx > 0 else 0
    
    # Fade analysis (TDE signature)
    if peak_idx < len(flux) - 3:
        fade = flux[peak_idx:]
        pos_fade = fade[fade > 0]
        if len(pos_fade) > 3:
            slope, intercept, r, p, se = stats.linregress(
                np.log(np.arange(1, len(pos_fade)+1)), 
                np.log(pos_fade + 1e-10)
            )
            f['fade_slope'] = slope
            f['fade_r2'] = r**2
            f['tde_match'] = max(0, 1 - np.abs(slope - TDE_POWER_LAW) / 2)
        else:
            f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
    else:
        f['fade_slope'] = f['fade_r2'] = f['tde_match'] = 0
    
    # Per-band features
    for band in BANDS:
        band_df = df[df['Filter'] == band]
        if len(band_df) >= 2:
            bf = band_df['Flux'].values
            f[f'b_{band}_mean'] = np.mean(bf)
            f[f'b_{band}_std'] = np.std(bf)
            f[f'b_{band}_max'] = np.max(bf)
        else:
            f[f'b_{band}_mean'] = f[f'b_{band}_std'] = f[f'b_{band}_max'] = 0
    
    # Colors
    blue = f.get('b_u_mean', 0) + f.get('b_g_mean', 0)
    red = f.get('b_i_mean', 0) + f.get('b_z_mean', 0) + f.get('b_y_mean', 0)
    f['blue_red'] = blue / (red + 1e-8) if abs(red) > 1e-8 else 1.0
    f['color_gr'] = f.get('b_g_mean', 0) - f.get('b_r_mean', 0)
    
    # Variability
    diffs = np.diff(flux)
    f['diff_mean'] = np.mean(np.abs(diffs))
    f['diff_std'] = np.std(diffs)
    
    if len(flux) > 3:
        ac = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        f['autocorr'] = ac if not np.isnan(ac) else 0
    else:
        f['autocorr'] = 0
    
    # === FORMAL TAF FEATURES ===
    t, f_neg, phi, psi = tralse_activation_function(flux)
    
    f['taf_T_mean'] = np.mean(t)
    f['taf_T_max'] = np.max(t)
    f['taf_F_mean'] = np.mean(f_neg)
    f['taf_F_max'] = np.max(f_neg)
    f['taf_phi_mean'] = np.mean(phi)
    f['taf_phi_max'] = np.max(phi)
    f['taf_psi_mean'] = np.mean(psi)
    f['taf_psi_max'] = np.max(psi)
    
    # Derived TAF features
    f['taf_certainty'] = np.mean(1 - phi)  # High = confident
    f['taf_T_F_ratio'] = np.sum(t) / (np.sum(f_neg) + 1e-8)
    f['taf_info_density'] = np.mean(t**2 + f_neg**2 + phi**2 + psi**2)  # Should be ~1 due to normalization
    
    # === FORMAL MYRION RESOLUTION FEATURES ===
    pos_changes = np.sum(np.maximum(0, diffs))
    neg_changes = np.sum(np.maximum(0, -diffs))
    
    mr = myrion_resolution(pos_changes, neg_changes)
    f['myr_net'] = mr['net']
    f['myr_contradiction'] = mr['contradiction']
    f['myr_phi'] = mr['phi']
    f['myr_coherence'] = mr['coherence']
    f['myr_is_dt'] = 1 if mr['is_double_tralse'] else 0
    
    # Temporal Myrion (sign changes = contradiction over time)
    if len(diffs) > 1:
        sign_changes = np.sum((diffs[:-1] * diffs[1:]) < 0)
        f['myr_reversal'] = sign_changes / (len(diffs) - 1)
    else:
        f['myr_reversal'] = 0
    
    # === FORMAL LCC CASCADE FEATURES ===
    lcc = lcc_cascade(flux)
    f['lcc_042'] = lcc['lcc_042']
    f['lcc_085'] = lcc['lcc_085']
    f['lcc_092sq'] = lcc['lcc_092sq']
    
    # LCC on differences (for temporal patterns)
    lcc_diff = lcc_cascade(diffs)
    f['lcc_diff_042'] = lcc_diff['lcc_042']
    f['lcc_diff_085'] = lcc_diff['lcc_085']
    
    # === FORMAL ANTI-GILE HOLE FEATURES ===
    # Expected pattern: TDE-like t^(-5/3) decay from peak
    expected = flux[peak_idx] * np.power(np.arange(1, len(flux)+1), TDE_POWER_LAW)
    
    holes = anti_gile_holes(flux, expected, f['flux_std'])
    f['I_hole'] = holes['I_hole']
    f['E_hole'] = holes['E_hole']
    f['L_hole'] = holes['L_hole']
    f['G_hole'] = holes['G_hole']
    f['total_hole'] = holes['total_hole']
    
    # === SYNERGY FEATURES ===
    # Combine TI signals following formal theory
    f['ti_synergy'] = (
        f['taf_certainty'] * 0.25 +
        (1 - f['myr_phi']) * 0.25 +
        f['lcc_085'] * 0.25 +
        (1 - f['total_hole']) * 0.25
    )
    
    f['ti_confidence'] = f['taf_certainty'] * f['myr_coherence']
    f['ti_uncertainty'] = f['taf_phi_mean'] * f['myr_phi']
    
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

print("\nExtracting formal TI Sigma features...")
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

# Define feature groups for ablation
conv_features = [c for c in common if not any(x in c for x in ['taf_', 'myr_', 'lcc_', 'hole', 'ti_'])]
taf_features = [c for c in common if 'taf_' in c]
myr_features = [c for c in common if 'myr_' in c]
lcc_features = [c for c in common if 'lcc_' in c]
hole_features = [c for c in common if 'hole' in c.lower()]
synergy_features = [c for c in common if 'ti_' in c]

ti_all = taf_features + myr_features + lcc_features + hole_features + synergy_features

print(f"\nTotal features: {len(common)}")
print(f"  Conventional: {len(conv_features)}")
print(f"  TAF: {len(taf_features)}")
print(f"  Myrion: {len(myr_features)}")
print(f"  LCC: {len(lcc_features)}")
print(f"  Anti-GILE Holes: {len(hole_features)}")
print(f"  TI Synergy: {len(synergy_features)}")


# === ABLATION STUDY ===
print("\n" + "=" * 70)
print("ABLATION STUDY: Isolating Each TI Component")
print("=" * 70)

def evaluate_features(X, y, feature_set, name, n_seeds=5):
    """Evaluate a feature set across multiple random seeds."""
    if len(feature_set) == 0:
        return {'name': name, 'mean_f1': 0, 'std_f1': 0, 'features': 0}
    
    scores = []
    for seed in [42, 123, 456, 789, 999]:
        X_tr, X_val, y_tr, y_val = train_test_split(
            X[feature_set], y, test_size=0.2, stratify=y, random_state=seed
        )
        
        scaler = StandardScaler()
        X_tr_s = scaler.fit_transform(X_tr)
        X_val_s = scaler.transform(X_val)
        
        rf = RandomForestClassifier(
            n_estimators=200, max_depth=10, 
            class_weight='balanced', random_state=42, n_jobs=-1
        )
        rf.fit(X_tr_s, y_tr)
        probs = rf.predict_proba(X_val_s)[:, 1]
        
        best_f1 = max(f1_score(y_val, probs >= th) for th in np.linspace(0.1, 0.5, 21))
        scores.append(best_f1)
    
    return {
        'name': name,
        'mean_f1': np.mean(scores),
        'std_f1': np.std(scores),
        'features': len(feature_set),
        'scores': scores
    }

# Run ablations
ablations = [
    ('Conventional Only', conv_features),
    ('+ TAF', conv_features + taf_features),
    ('+ Myrion', conv_features + myr_features),
    ('+ LCC', conv_features + lcc_features),
    ('+ Anti-GILE Holes', conv_features + hole_features),
    ('+ All TI Sigma', conv_features + ti_all),
    ('TI Only (no conv)', ti_all),
]

print(f"\n{'Configuration':<25} {'Features':<10} {'Mean F1':<12} {'Std':<10} {'Δ Conv':<10}")
print("-" * 67)

baseline_f1 = None
results = []

for name, features in ablations:
    result = evaluate_features(X_train, y_train, features, name)
    results.append(result)
    
    if baseline_f1 is None:
        baseline_f1 = result['mean_f1']
        delta = "---"
    else:
        delta = f"{(result['mean_f1'] - baseline_f1) / baseline_f1 * 100:+.2f}%"
    
    print(f"{name:<25} {result['features']:<10} {result['mean_f1']:<12.4f} {result['std_f1']:<10.4f} {delta:<10}")

# Best configuration
best = max(results, key=lambda x: x['mean_f1'])
print(f"\n✅ BEST: {best['name']} with F1 = {best['mean_f1']:.4f}")


# === COMPONENT CONTRIBUTION ===
print("\n" + "=" * 70)
print("COMPONENT CONTRIBUTION ANALYSIS")
print("=" * 70)

# Calculate isolated contribution of each TI component
base = results[0]['mean_f1']  # Conventional

for name, features in ablations[1:5]:  # +TAF, +Myrion, +LCC, +Holes
    result = [r for r in results if r['name'] == name][0]
    contribution = result['mean_f1'] - base
    print(f"{name:<25}: {contribution:+.4f} ({contribution/base*100:+.2f}%)")


# === FEATURE IMPORTANCE ===
print("\n" + "=" * 70)
print("TOP 30 FEATURES BY IMPORTANCE")
print("=" * 70)

scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)

rf = RandomForestClassifier(n_estimators=300, max_depth=10, class_weight='balanced', random_state=42, n_jobs=-1)
rf.fit(X_tr, y_train)
imp = pd.Series(rf.feature_importances_, index=X_train.columns).sort_values(ascending=False)

# Categorize features
def get_category(feat):
    if 'taf_' in feat: return 'TAF'
    if 'myr_' in feat: return 'MYR'
    if 'lcc_' in feat: return 'LCC'
    if 'hole' in feat.lower(): return 'HOLE'
    if 'ti_' in feat: return 'SYN'
    return 'CONV'

print(f"\n{'Rank':<5} {'Category':<6} {'Feature':<25} {'Importance':<12}")
print("-" * 50)

for i, (feat, val) in enumerate(imp.head(30).items()):
    cat = get_category(feat)
    marker = "★" if cat != 'CONV' else " "
    print(f"{marker}{i+1:<4} {cat:<6} {feat:<25} {val:.4f}")

# Summary by category
print("\n" + "-" * 50)
print("IMPORTANCE BY CATEGORY:")
for cat in ['CONV', 'TAF', 'MYR', 'LCC', 'HOLE', 'SYN']:
    cat_imp = sum(imp[f] for f in imp.index if get_category(f) == cat)
    pct = cat_imp / sum(imp) * 100
    print(f"  {cat}: {pct:.1f}%")


# === TDE vs NON-TDE ANALYSIS ===
print("\n" + "=" * 70)
print("TDE vs NON-TDE: KEY TI FEATURES")
print("=" * 70)

key_features = ['taf_phi_mean', 'taf_certainty', 'myr_phi', 'myr_coherence',
                'lcc_085', 'I_hole', 'G_hole', 'ti_confidence']

print(f"\n{'Feature':<20} {'TDE':<12} {'Non-TDE':<12} {'Sep (σ)':<10} {'Δ%':<10}")
print("-" * 64)

for feat in key_features:
    if feat in X_train.columns:
        tde = X_train.loc[y_train == 1, feat].mean()
        non = X_train.loc[y_train == 0, feat].mean()
        sep = abs(tde - non) / (X_train[feat].std() + 1e-8)
        diff = (tde - non) / (abs(non) + 1e-8) * 100
        print(f"{feat:<20} {tde:<12.4f} {non:<12.4f} {sep:<10.2f} {diff:+.1f}%")


# === FINAL SUBMISSION ===
print("\n" + "=" * 70)
print("GENERATING SUBMISSION")
print("=" * 70)

# Use best configuration
best_features = conv_features + ti_all
scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train[best_features])
X_te = scaler.transform(X_test[best_features])

rf = RandomForestClassifier(n_estimators=300, max_depth=10, class_weight='balanced', random_state=42, n_jobs=-1)
rf.fit(X_tr, y_train)

# Find optimal threshold
cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof = np.zeros(len(X_train))
for tr_idx, val_idx in cv.split(X_tr, y_train):
    rf.fit(X_tr[tr_idx], y_train[tr_idx])
    oof[val_idx] = rf.predict_proba(X_tr[val_idx])[:, 1]

best_f1, best_th = 0, 0.3
for th in np.linspace(0.05, 0.5, 46):
    f1 = f1_score(y_train, oof >= th)
    if f1 > best_f1:
        best_f1, best_th = f1, th

# Final prediction
rf.fit(X_tr, y_train)
test_probs = rf.predict_proba(X_te)[:, 1]
y_pred = (test_probs >= best_th).astype(int)

submission = pd.DataFrame({'object_id': test_ids, 'target': y_pred})
submission.to_csv('submission_ti_sigma_formal.csv', index=False)

print(f"\nOOF F1: {best_f1:.4f} @ threshold {best_th:.3f}")
print(f"Predicted TDEs: {y_pred.sum()} / {len(y_pred)} ({y_pred.mean()*100:.2f}%)")
print(f"Submission saved: submission_ti_sigma_formal.csv")


# === SUMMARY ===
print("\n" + "=" * 70)
print("SUMMARY: FORMAL TI SIGMA VALIDATION")
print("=" * 70)

conv_result = [r for r in results if r['name'] == 'Conventional Only'][0]
ti_result = [r for r in results if r['name'] == '+ All TI Sigma'][0]

improvement = (ti_result['mean_f1'] - conv_result['mean_f1']) / conv_result['mean_f1'] * 100

print(f"\nConventional F1: {conv_result['mean_f1']:.4f} ± {conv_result['std_f1']:.4f}")
print(f"TI Sigma F1:     {ti_result['mean_f1']:.4f} ± {ti_result['std_f1']:.4f}")
print(f"Improvement:     {improvement:+.2f}%")

# Check significance
from scipy.stats import ttest_rel
if len(conv_result.get('scores', [])) > 0 and len(ti_result.get('scores', [])) > 0:
    t_stat, p_val = ttest_rel(ti_result['scores'], conv_result['scores'])
    print(f"Paired t-test:   t={t_stat:.2f}, p={p_val:.4f}")
    if p_val < 0.05:
        print("✅ Improvement is STATISTICALLY SIGNIFICANT (p < 0.05)")
    else:
        print("⚠️ Improvement not significant at p < 0.05")

print(f"\nTARGET: 0.75 | CURRENT: {ti_result['mean_f1']:.4f} | GAP: {0.75 - ti_result['mean_f1']:.4f}")

print("\n✅ FORMAL TI SIGMA IMPLEMENTATION COMPLETE")
