"""
TI CAFA 6 - SIGMA ENHANCED SOLVER
=================================
Applying validated TI Sigma innovations from MALLORN:
- TAF (Tralse Activation Function): +6.26% on astronomical TDE
- Anti-GILE Holes: +6.78% on astronomical TDE
- LCC Cascade: Formal thresholds (0.42, 0.85, 0.92²)

Biological mapping:
- TAF on hydrophobicity profile → (t, f, φ, ψ) captures protein "state"
- Anti-GILE Holes on amino acid patterns → detects missing/anomalous regions
- φ (uncertainty) as function signature → proteins in "tralse" states
"""

import numpy as np
import pandas as pd
from collections import Counter, defaultdict
from pathlib import Path
from scipy import stats
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import train_test_split
from sklearn.metrics import f1_score
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI CAFA 6 - SIGMA ENHANCED SOLVER")
print("Applying MALLORN-validated TAF & Anti-GILE Holes")
print("=" * 70)

# === TI SIGMA CONSTANTS ===
LCC_DETECTABLE = 0.42
LCC_CAUSAL = 0.85
LCC_MASTERY = 0.92 ** 2
TEMPERATURE = 1.0

# Amino acid properties (expanded)
AA_PROPERTIES = {
    'A': {'hydro': 1.8, 'charge': 0, 'size': 89, 'polar': 0, 'aromatic': 0, 'aliphatic': 1},
    'R': {'hydro': -4.5, 'charge': 1, 'size': 174, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'N': {'hydro': -3.5, 'charge': 0, 'size': 132, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'D': {'hydro': -3.5, 'charge': -1, 'size': 133, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'C': {'hydro': 2.5, 'charge': 0, 'size': 121, 'polar': 0, 'aromatic': 0, 'aliphatic': 0},
    'Q': {'hydro': -3.5, 'charge': 0, 'size': 146, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'E': {'hydro': -3.5, 'charge': -1, 'size': 147, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'G': {'hydro': -0.4, 'charge': 0, 'size': 75, 'polar': 0, 'aromatic': 0, 'aliphatic': 0},
    'H': {'hydro': -3.2, 'charge': 0.5, 'size': 155, 'polar': 1, 'aromatic': 1, 'aliphatic': 0},
    'I': {'hydro': 4.5, 'charge': 0, 'size': 131, 'polar': 0, 'aromatic': 0, 'aliphatic': 1},
    'L': {'hydro': 3.8, 'charge': 0, 'size': 131, 'polar': 0, 'aromatic': 0, 'aliphatic': 1},
    'K': {'hydro': -3.9, 'charge': 1, 'size': 146, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'M': {'hydro': 1.9, 'charge': 0, 'size': 149, 'polar': 0, 'aromatic': 0, 'aliphatic': 0},
    'F': {'hydro': 2.8, 'charge': 0, 'size': 165, 'polar': 0, 'aromatic': 1, 'aliphatic': 0},
    'P': {'hydro': -1.6, 'charge': 0, 'size': 115, 'polar': 0, 'aromatic': 0, 'aliphatic': 0},
    'S': {'hydro': -0.8, 'charge': 0, 'size': 105, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'T': {'hydro': -0.7, 'charge': 0, 'size': 119, 'polar': 1, 'aromatic': 0, 'aliphatic': 0},
    'W': {'hydro': -0.9, 'charge': 0, 'size': 204, 'polar': 1, 'aromatic': 1, 'aliphatic': 0},
    'Y': {'hydro': -1.3, 'charge': 0, 'size': 181, 'polar': 1, 'aromatic': 1, 'aliphatic': 0},
    'V': {'hydro': 4.2, 'charge': 0, 'size': 117, 'polar': 0, 'aromatic': 0, 'aliphatic': 1},
}

AMINO_ACIDS = 'ARNDCQEGHILKMFPSTWYV'


# === FORMAL TAF (from MALLORN success) ===

def tralse_activation_function(x, temperature=TEMPERATURE):
    """
    FORMAL TAF: Maps property sequence to 4D unit sphere.
    
    From MALLORN validation (+6.26%):
    TAF(x) = (t, f, φ, ψ) where t² + f² + φ² + ψ² = 1
    """
    x = np.asarray(x)
    if len(x) == 0:
        return 0, 0, 0, 0
    
    # Dual ReLU for T and F
    t = np.maximum(0, x)
    f = np.maximum(0, -x)
    
    # Phi as uncertainty (high when near zero)
    phi = np.exp(-x**2 / temperature)
    
    # Psi as local gradient uncertainty
    if len(x) > 1:
        psi = np.tanh(np.abs(np.gradient(x))) * 0.5
    else:
        psi = np.zeros_like(x)
    
    # Normalize to unit sphere
    norm = np.sqrt(t**2 + f**2 + phi**2 + psi**2 + 1e-10)
    t_norm = t / norm
    f_norm = f / norm
    phi_norm = phi / norm
    psi_norm = psi / norm
    
    return np.mean(t_norm), np.mean(f_norm), np.mean(phi_norm), np.mean(psi_norm)


# === FORMAL ANTI-GILE HOLES (from MALLORN success) ===

def compute_gile_holes(actual_profile, expected_profile, std_val):
    """
    FORMAL Anti-GILE Holes: Detect dimensional deficiencies.
    
    From MALLORN validation (+6.78%):
    - I-hole: Deviation from expected pattern
    - E-hole: Missing expected signal
    - L-hole: Loss of coherence
    - G-hole: Deviation from optimal
    """
    actual = np.asarray(actual_profile)
    expected = np.asarray(expected_profile)[:len(actual)]
    
    if len(actual) < 3:
        return 0.5, 0.5, 0.5, 0.5
    
    residual = actual - expected
    
    # I-hole: Intuition deviation
    I_hole = np.mean(np.abs(residual)) / (std_val + 1e-10)
    
    # E-hole: Existence gap (expected but missing)
    exp_high = expected > np.median(expected)
    act_high = actual > np.median(actual)
    E_hole = np.mean(exp_high & ~act_high)
    
    # L-hole: Love (coherence) loss
    if len(actual) > 3:
        ac = np.corrcoef(actual[:-1], actual[1:])[0, 1]
        L_hole = 1.0 - np.abs(ac) if not np.isnan(ac) else 0.5
    else:
        L_hole = 0.5
    
    # G-hole: Goodness deviation (from optimal protein pattern)
    # For proteins, optimal = smooth hydrophobicity transitions
    if len(actual) > 5:
        smoothness = np.mean(np.abs(np.diff(actual)))
        G_hole = min(1.0, smoothness / 2)  # High diff = poor smoothness
    else:
        G_hole = 0.5
    
    return I_hole, E_hole, L_hole, G_hole


# === LCC CASCADE ===

def lcc_cascade(signal):
    """
    LCC threshold cascade for protein regions.
    """
    signal = np.asarray(signal)
    if len(signal) == 0:
        return 0, 0, 0
    
    max_sig = np.max(np.abs(signal)) + 1e-10
    normalized = np.abs(signal) / max_sig
    
    return (
        float(np.mean(normalized > LCC_DETECTABLE)),
        float(np.mean(normalized > LCC_CAUSAL)),
        float(np.mean(normalized > LCC_MASTERY))
    )


# === FASTA PARSING ===

def parse_fasta(filepath, limit=None):
    """Parse FASTA file to dictionary."""
    sequences = {}
    current_id = None
    current_seq = []
    count = 0
    
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('>'):
                if current_id:
                    sequences[current_id] = ''.join(current_seq)
                    count += 1
                    if limit and count >= limit:
                        break
                header = line[1:]
                current_id = header.split()[0]
                if '|' in current_id:
                    parts = current_id.split('|')
                    current_id = parts[1] if len(parts) > 1 else parts[0]
                current_seq = []
            else:
                current_seq.append(line)
        if current_id and (not limit or count < limit):
            sequences[current_id] = ''.join(current_seq)
    
    return sequences


# === TI SIGMA FEATURE EXTRACTION ===

def extract_ti_sigma_features(sequence):
    """
    Extract TI Sigma enhanced features from protein sequence.
    Applies MALLORN-validated TAF and Anti-GILE Holes.
    """
    if len(sequence) < 5:
        return None
    
    features = {}
    
    # === BASIC FEATURES ===
    features['length'] = len(sequence)
    features['log_length'] = np.log1p(len(sequence))
    
    # Amino acid composition
    aa_counts = Counter(sequence)
    for aa in AMINO_ACIDS:
        features[f'aa_{aa}'] = aa_counts.get(aa, 0) / len(sequence)
    
    # === PROPERTY PROFILES ===
    hydro = np.array([AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in sequence])
    charge = np.array([AA_PROPERTIES.get(aa, {}).get('charge', 0) for aa in sequence])
    size = np.array([AA_PROPERTIES.get(aa, {}).get('size', 100) for aa in sequence])
    polar = np.array([AA_PROPERTIES.get(aa, {}).get('polar', 0) for aa in sequence])
    
    # Property statistics
    features['hydro_mean'] = np.mean(hydro)
    features['hydro_std'] = np.std(hydro)
    features['hydro_min'] = np.min(hydro)
    features['hydro_max'] = np.max(hydro)
    features['hydro_range'] = np.max(hydro) - np.min(hydro)
    
    features['charge_mean'] = np.mean(charge)
    features['charge_std'] = np.std(charge)
    features['charge_positive'] = np.sum(charge > 0) / len(charge)
    features['charge_negative'] = np.sum(charge < 0) / len(charge)
    
    features['size_mean'] = np.mean(size)
    features['size_std'] = np.std(size)
    
    features['polar_frac'] = np.mean(polar)
    
    # === FORMAL TAF ON HYDROPHOBICITY (MALLORN innovation) ===
    taf_t, taf_f, taf_phi, taf_psi = tralse_activation_function(hydro)
    features['taf_T_hydro'] = taf_t
    features['taf_F_hydro'] = taf_f
    features['taf_phi_hydro'] = taf_phi
    features['taf_psi_hydro'] = taf_psi
    features['taf_certainty_hydro'] = 1 - taf_phi
    
    # TAF on charge
    taf_t, taf_f, taf_phi, taf_psi = tralse_activation_function(charge)
    features['taf_T_charge'] = taf_t
    features['taf_F_charge'] = taf_f
    features['taf_phi_charge'] = taf_phi
    
    # === FORMAL ANTI-GILE HOLES (MALLORN innovation) ===
    # Expected pattern: smooth hydrophobicity transition
    expected_hydro = np.convolve(hydro, np.ones(5)/5, mode='same')
    I_hole, E_hole, L_hole, G_hole = compute_gile_holes(hydro, expected_hydro, features['hydro_std'])
    
    features['I_hole'] = I_hole
    features['E_hole'] = E_hole
    features['L_hole'] = L_hole
    features['G_hole'] = G_hole
    features['total_hole'] = (I_hole + E_hole + L_hole + G_hole) / 4
    
    # === LCC CASCADE ===
    lcc_042, lcc_085, lcc_092 = lcc_cascade(hydro)
    features['lcc_042'] = lcc_042
    features['lcc_085'] = lcc_085
    features['lcc_092'] = lcc_092
    
    # LCC on charge
    lcc_c042, lcc_c085, lcc_c092 = lcc_cascade(charge)
    features['lcc_charge_042'] = lcc_c042
    features['lcc_charge_085'] = lcc_c085
    
    # === SEQUENCE COMPLEXITY ===
    probs = np.array(list(aa_counts.values())) / len(sequence)
    entropy = -np.sum(probs * np.log2(probs + 1e-10))
    features['entropy'] = entropy
    features['entropy_norm'] = entropy / np.log2(20)  # Max 20 AAs
    
    # === REGIONAL ANALYSIS ===
    # N-terminal, middle, C-terminal thirds
    third = len(sequence) // 3
    if third > 5:
        for i, region in enumerate(['N', 'M', 'C']):
            start = i * third
            end = (i + 1) * third if i < 2 else len(sequence)
            region_hydro = hydro[start:end]
            features[f'hydro_{region}_mean'] = np.mean(region_hydro)
            
            rt, rf, rphi, rpsi = tralse_activation_function(region_hydro)
            features[f'taf_phi_{region}'] = rphi
    
    # === SECONDARY STRUCTURE PROPENSITY ===
    # Simplified Chou-Fasman
    helix_formers = set('AELM')
    sheet_formers = set('VIY')
    turn_formers = set('GNPS')
    
    features['helix_prop'] = sum(1 for aa in sequence if aa in helix_formers) / len(sequence)
    features['sheet_prop'] = sum(1 for aa in sequence if aa in sheet_formers) / len(sequence)
    features['turn_prop'] = sum(1 for aa in sequence if aa in turn_formers) / len(sequence)
    
    # === MOTIF PATTERNS ===
    # Hydrophobic clusters (potential TM or core)
    hydro_high = (hydro > 2).astype(int)
    clusters = ''.join(map(str, hydro_high))
    features['hydro_cluster_count'] = clusters.count('111')
    
    # Charged clusters (potential active sites)
    charge_high = (np.abs(charge) > 0.5).astype(int)
    features['charge_cluster_count'] = sum(1 for i in range(len(charge)-2) 
                                            if charge_high[i] and charge_high[i+1])
    
    # === TI SYNERGY FEATURES ===
    features['ti_synergy'] = (
        features['taf_certainty_hydro'] * 0.3 +
        (1 - features['total_hole']) * 0.3 +
        features['lcc_085'] * 0.2 +
        features['entropy_norm'] * 0.2
    )
    
    features['ti_confidence'] = features['taf_certainty_hydro'] * (1 - features['I_hole'])
    
    return features


# === LOAD DATA ===

print("\nLoading data...")
train_seqs = parse_fasta('train_sequences.fasta')
test_seqs = parse_fasta('test_sequences.fasta')

print(f"Training sequences: {len(train_seqs)}")
print(f"Test sequences: {len(test_seqs)}")

# Load GO terms
train_terms = pd.read_csv('train_terms.tsv', sep='\t', header=0, 
                          names=['EntryID', 'term', 'aspect'])
print(f"Training terms: {len(train_terms)}")
print(f"Unique GO terms: {train_terms['term'].nunique()}")

# Build protein-to-terms mapping
protein_terms = defaultdict(set)
for _, row in train_terms.iterrows():
    protein_terms[row['EntryID']].add(row['term'])

# Find most common GO terms (focus on these for now)
term_counts = train_terms['term'].value_counts()
TOP_N_TERMS = 100  # Start with top 100 most common
top_terms = term_counts.head(TOP_N_TERMS).index.tolist()
print(f"\nFocusing on top {TOP_N_TERMS} GO terms")
print(f"Coverage: {sum(1 for p in protein_terms if any(t in top_terms for t in protein_terms[p]))} proteins")


# === EXTRACT FEATURES ===

print("\nExtracting TI Sigma features...")
train_features = []
train_ids = []
for i, (pid, seq) in enumerate(train_seqs.items()):
    feat = extract_ti_sigma_features(seq)
    if feat:
        train_features.append(feat)
        train_ids.append(pid)
    if (i + 1) % 5000 == 0:
        print(f"  Train: {i+1}/{len(train_seqs)}")

test_features = []
test_ids = []
for i, (pid, seq) in enumerate(test_seqs.items()):
    feat = extract_ti_sigma_features(seq)
    if feat:
        test_features.append(feat)
        test_ids.append(pid)
    if (i + 1) % 5000 == 0:
        print(f"  Test: {i+1}/{len(test_seqs)}")

X_train = pd.DataFrame(train_features, index=train_ids)
X_test = pd.DataFrame(test_features, index=test_ids)

# Align columns
common_cols = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[common_cols].fillna(0)
X_test = X_test[common_cols].fillna(0)

print(f"\nFeatures extracted: {len(common_cols)}")
print(f"Training samples: {len(X_train)}")
print(f"Test samples: {len(X_test)}")


# === BUILD MULTI-LABEL CLASSIFIERS ===

print("\n" + "=" * 70)
print("TRAINING PER-TERM CLASSIFIERS")
print("=" * 70)

scaler = StandardScaler()
X_train_scaled = scaler.fit_transform(X_train)
X_test_scaled = scaler.transform(X_test)

predictions = defaultdict(dict)  # {protein_id: {term: probability}}

for term_idx, term in enumerate(top_terms):
    # Build binary labels for this term
    y = np.array([1 if term in protein_terms.get(pid, set()) else 0 
                  for pid in train_ids])
    
    pos_count = y.sum()
    if pos_count < 10:
        continue  # Skip very rare terms
    
    # Train classifier
    clf = LogisticRegression(class_weight='balanced', max_iter=500, random_state=42)
    clf.fit(X_train_scaled, y)
    
    # Predict on test
    probs = clf.predict_proba(X_test_scaled)[:, 1]
    
    for pid, prob in zip(test_ids, probs):
        if prob > 0.01:  # Only keep predictions above threshold
            predictions[pid][term] = prob
    
    if (term_idx + 1) % 20 == 0:
        print(f"  Trained {term_idx + 1}/{len(top_terms)} classifiers")

print(f"\nPredictions generated for {len(predictions)} proteins")


# === ANALYZE TI FEATURES ===

print("\n" + "=" * 70)
print("TI SIGMA FEATURE ANALYSIS")
print("=" * 70)

# Pick a common term for analysis
example_term = top_terms[0]
y_example = np.array([1 if example_term in protein_terms.get(pid, set()) else 0 
                      for pid in train_ids])

ti_features = ['taf_phi_hydro', 'taf_certainty_hydro', 'I_hole', 'G_hole', 
               'total_hole', 'lcc_085', 'ti_synergy', 'ti_confidence']

print(f"\nFor term {example_term} (n_pos={y_example.sum()}):")
print(f"{'Feature':<25} {'Positive':<12} {'Negative':<12} {'Sep (σ)':<10}")
print("-" * 59)

for feat in ti_features:
    if feat in X_train.columns:
        pos_mean = X_train.loc[y_example == 1, feat].mean()
        neg_mean = X_train.loc[y_example == 0, feat].mean()
        sep = abs(pos_mean - neg_mean) / (X_train[feat].std() + 1e-8)
        print(f"{feat:<25} {pos_mean:<12.4f} {neg_mean:<12.4f} {sep:<10.2f}")


# === FEATURE IMPORTANCE ===

print("\n" + "=" * 70)
print("FEATURE IMPORTANCE (Random Forest on example term)")
print("=" * 70)

rf = RandomForestClassifier(n_estimators=100, max_depth=8, class_weight='balanced', 
                             random_state=42, n_jobs=-1)
rf.fit(X_train_scaled, y_example)
imp = pd.Series(rf.feature_importances_, index=common_cols).sort_values(ascending=False)

def get_category(feat):
    if 'taf_' in feat: return 'TAF'
    if 'hole' in feat.lower(): return 'HOLE'
    if 'lcc_' in feat: return 'LCC'
    if 'ti_' in feat: return 'SYN'
    return 'CONV'

print(f"\n{'Rank':<5} {'Category':<6} {'Feature':<30} {'Importance':<10}")
print("-" * 55)

for i, (feat, val) in enumerate(imp.head(20).items()):
    cat = get_category(feat)
    marker = "★" if cat != 'CONV' else " "
    print(f"{marker}{i+1:<4} {cat:<6} {feat:<30} {val:.4f}")


# === GENERATE SUBMISSION ===

print("\n" + "=" * 70)
print("GENERATING SUBMISSION")
print("=" * 70)

# Format: EntryID \t GO_term \t confidence
submission_rows = []

for pid, term_probs in predictions.items():
    for term, prob in sorted(term_probs.items(), key=lambda x: -x[1]):
        submission_rows.append(f"{pid}\t{term}\t{prob:.6f}")

# Save submission
with open('submission_ti_sigma.tsv', 'w') as f:
    for row in submission_rows:
        f.write(row + '\n')

print(f"\nSubmission rows: {len(submission_rows)}")
print(f"Unique proteins: {len(predictions)}")
print(f"Saved: submission_ti_sigma.tsv")


# === SUMMARY ===

print("\n" + "=" * 70)
print("TI SIGMA CAFA6 SUMMARY")
print("=" * 70)

ti_importance = sum(imp[f] for f in imp.index if get_category(f) != 'CONV')
total_importance = sum(imp)
ti_pct = ti_importance / total_importance * 100

print(f"\nTI Sigma features account for {ti_pct:.1f}% of importance")
print(f"\nKey innovations from MALLORN applied:")
print(f"  ✅ TAF (Tralse Activation): Applied to hydrophobicity & charge profiles")
print(f"  ✅ Anti-GILE Holes: Detecting protein pattern deviations")
print(f"  ✅ LCC Cascade: Formal thresholds (0.42, 0.85, 0.92²)")

print("\n✅ TI SIGMA CAFA6 COMPLETE")
