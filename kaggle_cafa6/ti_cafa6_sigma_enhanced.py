"""
TI CAFA 6 - SIGMA ENHANCED v2
=============================
Three major improvements:
1. Bio-tuned TAF (temperature=0.5, adaptive normalization)
2. Expanded to top 200 GO terms
3. Protein homology features (k-mer patterns, BLOSUM-based similarity)
"""

import numpy as np
import pandas as pd
from collections import Counter, defaultdict
from itertools import product
from scipy import stats
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier
from sklearn.model_selection import cross_val_score
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI CAFA 6 - SIGMA ENHANCED v2")
print("Bio-tuned TAF + 200 GO terms + Homology features")
print("=" * 70)

# === BIO-TUNED CONSTANTS ===
# Lower temperature for proteins - they have more discrete states
TAF_TEMPERATURE = 0.5  # Reduced from 1.0 for sharper activation
LCC_DETECTABLE = 0.42
LCC_CAUSAL = 0.85

# Expanded amino acid properties
AA_PROPS = {
    'A': {'hydro': 1.8, 'vol': 88.6, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'R': {'hydro': -4.5, 'vol': 173.4, 'charge': 1, 'hbond': 2, 'aromatic': 0},
    'N': {'hydro': -3.5, 'vol': 114.1, 'charge': 0, 'hbond': 2, 'aromatic': 0},
    'D': {'hydro': -3.5, 'vol': 111.1, 'charge': -1, 'hbond': 2, 'aromatic': 0},
    'C': {'hydro': 2.5, 'vol': 108.5, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'Q': {'hydro': -3.5, 'vol': 143.8, 'charge': 0, 'hbond': 2, 'aromatic': 0},
    'E': {'hydro': -3.5, 'vol': 138.4, 'charge': -1, 'hbond': 2, 'aromatic': 0},
    'G': {'hydro': -0.4, 'vol': 60.1, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'H': {'hydro': -3.2, 'vol': 153.2, 'charge': 0.5, 'hbond': 1, 'aromatic': 1},
    'I': {'hydro': 4.5, 'vol': 166.7, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'L': {'hydro': 3.8, 'vol': 166.7, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'K': {'hydro': -3.9, 'vol': 168.6, 'charge': 1, 'hbond': 1, 'aromatic': 0},
    'M': {'hydro': 1.9, 'vol': 162.9, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'F': {'hydro': 2.8, 'vol': 189.9, 'charge': 0, 'hbond': 0, 'aromatic': 1},
    'P': {'hydro': -1.6, 'vol': 112.7, 'charge': 0, 'hbond': 0, 'aromatic': 0},
    'S': {'hydro': -0.8, 'vol': 89.0, 'charge': 0, 'hbond': 1, 'aromatic': 0},
    'T': {'hydro': -0.7, 'vol': 116.1, 'charge': 0, 'hbond': 1, 'aromatic': 0},
    'W': {'hydro': -0.9, 'vol': 227.8, 'charge': 0, 'hbond': 1, 'aromatic': 1},
    'Y': {'hydro': -1.3, 'vol': 193.6, 'charge': 0, 'hbond': 1, 'aromatic': 1},
    'V': {'hydro': 4.2, 'vol': 140.0, 'charge': 0, 'hbond': 0, 'aromatic': 0},
}

# BLOSUM62 similarity groups (for homology features)
BLOSUM_GROUPS = {
    'hydrophobic': 'AILMFWV',
    'polar': 'STYCNQ',
    'positive': 'RKH',
    'negative': 'DE',
    'special': 'GP',
    'aromatic': 'FWY',
    'aliphatic': 'AILV',
    'small': 'AGST',
    'tiny': 'AG',
}

AMINO_ACIDS = 'ARNDCQEGHILKMFPSTWYV'


# === BIO-TUNED TAF ===

def bio_taf(signal, temperature=TAF_TEMPERATURE):
    """
    Bio-tuned Tralse Activation Function.
    
    Improvements over generic TAF:
    1. Lower temperature (0.5) for sharper protein state detection
    2. Adaptive normalization based on signal range
    3. ψ captures local hydrophobic/hydrophilic transitions
    """
    x = np.asarray(signal)
    if len(x) < 3:
        return 0.5, 0.5, 0.5, 0.5
    
    # Normalize to [-1, 1] range for proteins
    x_range = np.max(x) - np.min(x)
    if x_range > 0:
        x_norm = 2 * (x - np.min(x)) / x_range - 1
    else:
        x_norm = np.zeros_like(x)
    
    # Bio-tuned activations
    t = np.maximum(0, x_norm)  # Positive (hydrophobic)
    f = np.maximum(0, -x_norm)  # Negative (hydrophilic)
    
    # Sharper phi with lower temperature
    phi = np.exp(-x_norm**2 / temperature)
    
    # Psi: transition strength (important for protein folding)
    transitions = np.abs(np.diff(x_norm))
    psi = np.concatenate([[0], np.tanh(transitions)])
    
    # Adaptive normalization
    norm = np.sqrt(t**2 + f**2 + phi**2 + psi**2 + 1e-10)
    
    return (
        float(np.mean(t / norm)),
        float(np.mean(f / norm)),
        float(np.mean(phi / norm)),
        float(np.mean(psi / norm))
    )


# === ENHANCED ANTI-GILE HOLES ===

def bio_gile_holes(signal, expected=None):
    """
    Bio-tuned Anti-GILE Holes for protein sequences.
    
    Enhancements:
    - Uses protein-specific expected patterns
    - L-hole measures autocorrelation at multiple lags
    - G-hole uses protein folding smoothness heuristics
    """
    x = np.asarray(signal)
    if len(x) < 5:
        return 0.5, 0.5, 0.5, 0.5
    
    if expected is None:
        # Expected: running mean (proteins should have smooth transitions)
        expected = np.convolve(x, np.ones(7)/7, mode='same')
    
    residual = x - expected[:len(x)]
    
    # I-hole: Intuition deviation (unexpected amino acids)
    I_hole = float(np.mean(np.abs(residual)) / (np.std(x) + 1e-8))
    
    # E-hole: Existence gap (expected high but got low)
    threshold = np.median(expected)
    exp_high = expected[:len(x)] > threshold
    act_high = x > threshold
    E_hole = float(np.mean(exp_high & ~act_high))
    
    # L-hole: Love/coherence loss - multi-lag autocorrelation
    if len(x) > 10:
        ac1 = np.corrcoef(x[:-1], x[1:])[0, 1]
        ac3 = np.corrcoef(x[:-3], x[3:])[0, 1] if len(x) > 6 else 0
        ac1 = ac1 if not np.isnan(ac1) else 0
        ac3 = ac3 if not np.isnan(ac3) else 0
        L_hole = float(1.0 - (0.7 * np.abs(ac1) + 0.3 * np.abs(ac3)))
    else:
        L_hole = 0.5
    
    # G-hole: Goodness - protein folding smoothness
    # Good proteins have smooth hydrophobicity transitions
    diffs = np.abs(np.diff(x))
    G_hole = float(np.clip(np.mean(diffs) / 2, 0, 1))
    
    return I_hole, E_hole, L_hole, G_hole


# === K-MER HOMOLOGY FEATURES ===

def get_kmer_spectrum(sequence, k=3):
    """Extract k-mer frequency spectrum."""
    if len(sequence) < k:
        return {}
    
    kmers = Counter()
    for i in range(len(sequence) - k + 1):
        kmer = sequence[i:i+k]
        if all(aa in AMINO_ACIDS for aa in kmer):
            kmers[kmer] += 1
    
    total = sum(kmers.values())
    if total > 0:
        for kmer in kmers:
            kmers[kmer] /= total
    
    return kmers


def kmer_similarity(seq1, seq2, k=3):
    """Cosine similarity between k-mer spectra."""
    spec1 = get_kmer_spectrum(seq1, k)
    spec2 = get_kmer_spectrum(seq2, k)
    
    all_kmers = set(spec1.keys()) | set(spec2.keys())
    if not all_kmers:
        return 0.0
    
    dot = sum(spec1.get(km, 0) * spec2.get(km, 0) for km in all_kmers)
    norm1 = np.sqrt(sum(v**2 for v in spec1.values()))
    norm2 = np.sqrt(sum(v**2 for v in spec2.values()))
    
    if norm1 * norm2 == 0:
        return 0.0
    
    return dot / (norm1 * norm2)


def blosum_group_composition(sequence):
    """Composition based on BLOSUM similarity groups."""
    n = len(sequence)
    if n == 0:
        return {g: 0.0 for g in BLOSUM_GROUPS}
    
    comp = {}
    for group, aas in BLOSUM_GROUPS.items():
        comp[group] = sum(1 for aa in sequence if aa in aas) / n
    
    return comp


# === FASTA PARSING ===

def parse_fasta(filepath):
    """Parse FASTA file."""
    sequences = {}
    current_id = None
    current_seq = []
    
    with open(filepath, 'r') as f:
        for line in f:
            if line.startswith('>'):
                if current_id:
                    sequences[current_id] = ''.join(current_seq)
                parts = line[1:].split('|')
                current_id = parts[1] if len(parts) > 1 else parts[0].split()[0]
                current_seq = []
            else:
                current_seq.append(line.strip())
        if current_id:
            sequences[current_id] = ''.join(current_seq)
    
    return sequences


# === ENHANCED FEATURE EXTRACTION ===

def extract_enhanced_features(sequence):
    """
    Extract enhanced TI Sigma features with all 3 improvements.
    """
    if len(sequence) < 10:
        return None
    
    f = {}
    n = len(sequence)
    
    # === BASIC ===
    f['length'] = n
    f['log_length'] = np.log1p(n)
    
    # AA composition
    counts = Counter(sequence)
    for aa in AMINO_ACIDS:
        f[f'aa_{aa}'] = counts.get(aa, 0) / n
    
    # === PROPERTY PROFILES ===
    hydro = np.array([AA_PROPS.get(aa, {}).get('hydro', 0) for aa in sequence])
    vol = np.array([AA_PROPS.get(aa, {}).get('vol', 100) for aa in sequence])
    charge = np.array([AA_PROPS.get(aa, {}).get('charge', 0) for aa in sequence])
    hbond = np.array([AA_PROPS.get(aa, {}).get('hbond', 0) for aa in sequence])
    
    for prop, arr in [('hydro', hydro), ('vol', vol), ('charge', charge), ('hbond', hbond)]:
        f[f'{prop}_mean'] = np.mean(arr)
        f[f'{prop}_std'] = np.std(arr)
        f[f'{prop}_min'] = np.min(arr)
        f[f'{prop}_max'] = np.max(arr)
    
    # === BIO-TUNED TAF (Improvement #1) ===
    for prop, arr in [('hydro', hydro), ('vol', vol), ('charge', charge)]:
        t, fp, phi, psi = bio_taf(arr, temperature=TAF_TEMPERATURE)
        f[f'taf_T_{prop}'] = t
        f[f'taf_F_{prop}'] = fp
        f[f'taf_phi_{prop}'] = phi
        f[f'taf_psi_{prop}'] = psi
        f[f'taf_cert_{prop}'] = 1 - phi
    
    # === BIO-TUNED ANTI-GILE HOLES (Improvement #1) ===
    I_h, E_h, L_h, G_h = bio_gile_holes(hydro)
    f['I_hole'] = I_h
    f['E_hole'] = E_h
    f['L_hole'] = L_h
    f['G_hole'] = G_h
    f['total_hole'] = (I_h + E_h + L_h + G_h) / 4
    
    # Holes on volume profile too
    I_v, E_v, L_v, G_v = bio_gile_holes(vol)
    f['I_hole_vol'] = I_v
    f['L_hole_vol'] = L_v
    
    # === LCC CASCADE ===
    for prop, arr in [('hydro', hydro), ('charge', charge)]:
        max_val = np.max(np.abs(arr)) + 1e-10
        normalized = np.abs(arr) / max_val
        f[f'lcc_042_{prop}'] = np.mean(normalized > LCC_DETECTABLE)
        f[f'lcc_085_{prop}'] = np.mean(normalized > LCC_CAUSAL)
    
    # === BLOSUM GROUP COMPOSITION (Improvement #3) ===
    blosum_comp = blosum_group_composition(sequence)
    for group, val in blosum_comp.items():
        f[f'blosum_{group}'] = val
    
    # === K-MER FEATURES (Improvement #3) ===
    # Top k-mer frequencies
    kmer_spec = get_kmer_spectrum(sequence, k=2)
    top_2mers = ['LL', 'AA', 'VV', 'GG', 'SS', 'EE', 'KK', 'AL', 'LA', 'LV']
    for kmer in top_2mers:
        f[f'kmer_{kmer}'] = kmer_spec.get(kmer, 0)
    
    # K-mer diversity
    f['kmer_diversity'] = len(kmer_spec) / 400  # Max 20*20
    
    # === REGIONAL ANALYSIS ===
    third = n // 3
    if third > 5:
        for i, region in enumerate(['N', 'M', 'C']):
            start = i * third
            end = (i + 1) * third if i < 2 else n
            region_hydro = hydro[start:end]
            f[f'hydro_{region}_mean'] = np.mean(region_hydro)
            
            rt, rf, rphi, rpsi = bio_taf(region_hydro)
            f[f'taf_phi_{region}'] = rphi
            f[f'taf_psi_{region}'] = rpsi
    
    # === SECONDARY STRUCTURE PROPENSITY ===
    f['helix'] = sum(1 for aa in sequence if aa in 'AELM') / n
    f['sheet'] = sum(1 for aa in sequence if aa in 'VIY') / n
    f['turn'] = sum(1 for aa in sequence if aa in 'GNPS') / n
    f['disorder'] = sum(1 for aa in sequence if aa in 'EKRSP') / n
    
    # === ENTROPY ===
    probs = np.array(list(counts.values())) / n
    entropy = -np.sum(probs * np.log2(probs + 1e-10))
    f['entropy'] = entropy / np.log2(20)
    
    # === TI SYNERGY FEATURES ===
    f['ti_synergy'] = (
        f['taf_cert_hydro'] * 0.3 +
        (1 - f['total_hole']) * 0.3 +
        f['lcc_085_hydro'] * 0.2 +
        f['entropy'] * 0.2
    )
    
    f['ti_confidence'] = f['taf_cert_hydro'] * (1 - f['I_hole'])
    f['ti_folding'] = (1 - f['L_hole']) * (1 - f['G_hole'])
    
    return f


# === LOAD DATA ===

print("\nLoading data...")
train_seqs = parse_fasta('train_sequences.fasta')
test_seqs = parse_fasta('test_sequences.fasta')

print(f"Training: {len(train_seqs)}")
print(f"Test: {len(test_seqs)}")

# Load GO terms
train_terms = pd.read_csv('train_terms.tsv', sep='\t', header=0, 
                          names=['EntryID', 'term', 'aspect'])
print(f"GO terms: {train_terms['term'].nunique()}")

protein_terms = defaultdict(set)
for _, row in train_terms.iterrows():
    protein_terms[row['EntryID']].add(row['term'])

# IMPROVEMENT #2: Expand to top 200 GO terms
term_counts = train_terms['term'].value_counts()
TOP_N = 200
top_terms = term_counts.head(TOP_N).index.tolist()
print(f"Targeting top {TOP_N} GO terms")


# === EXTRACT FEATURES ===

print("\nExtracting enhanced features...")

train_features = []
train_ids = []
for i, (pid, seq) in enumerate(train_seqs.items()):
    feat = extract_enhanced_features(seq)
    if feat:
        train_features.append(feat)
        train_ids.append(pid)
    if (i + 1) % 10000 == 0:
        print(f"  Train: {i+1}/{len(train_seqs)}")

test_features = []
test_ids = []
for i, (pid, seq) in enumerate(test_seqs.items()):
    feat = extract_enhanced_features(seq)
    if feat:
        test_features.append(feat)
        test_ids.append(pid)
    if (i + 1) % 25000 == 0:
        print(f"  Test: {i+1}/{len(test_seqs)}")

X_train = pd.DataFrame(train_features, index=train_ids)
X_test = pd.DataFrame(test_features, index=test_ids)

cols = list(set(X_train.columns) & set(X_test.columns))
X_train = X_train[cols].fillna(0)
X_test = X_test[cols].fillna(0)

print(f"\nFeatures: {len(cols)}")
print(f"Train: {len(X_train)}, Test: {len(X_test)}")


# === TRAIN CLASSIFIERS ===

print("\n" + "=" * 70)
print("TRAINING CLASSIFIERS (200 GO terms)")
print("=" * 70)

scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

predictions = defaultdict(dict)
term_cv_scores = {}

for i, term in enumerate(top_terms):
    y = np.array([1 if term in protein_terms.get(pid, set()) else 0 for pid in train_ids])
    
    pos_count = y.sum()
    if pos_count < 30:
        continue
    
    clf = LogisticRegression(class_weight='balanced', max_iter=300, 
                             C=0.5, random_state=42, n_jobs=-1)
    clf.fit(X_tr, y)
    
    probs = clf.predict_proba(X_te)[:, 1]
    
    for pid, prob in zip(test_ids, probs):
        if prob > 0.03:
            predictions[pid][term] = prob
    
    if (i + 1) % 25 == 0:
        print(f"  Trained {i+1}/{len(top_terms)}")

print(f"\nPredictions for {len(predictions)} proteins")


# === FEATURE IMPORTANCE ===

print("\n" + "=" * 70)
print("ENHANCED TI SIGMA FEATURE IMPORTANCE")
print("=" * 70)

y_ex = np.array([1 if top_terms[0] in protein_terms.get(pid, set()) else 0 for pid in train_ids])

rf = RandomForestClassifier(n_estimators=100, max_depth=8, class_weight='balanced', 
                             random_state=42, n_jobs=-1)
rf.fit(X_tr, y_ex)
imp = pd.Series(rf.feature_importances_, index=cols).sort_values(ascending=False)

def categorize_feature(f):
    if 'taf_' in f: return 'TAF'
    if 'hole' in f.lower(): return 'HOLE'
    if 'lcc_' in f: return 'LCC'
    if 'ti_' in f: return 'TI'
    if 'blosum_' in f: return 'BLOSUM'
    if 'kmer_' in f: return 'KMER'
    return 'CONV'

categories = defaultdict(float)
for feat, val in imp.items():
    categories[categorize_feature(feat)] += val

print("\n📊 Importance by Category:")
for cat in ['TAF', 'HOLE', 'LCC', 'TI', 'BLOSUM', 'KMER', 'CONV']:
    if cat in categories:
        pct = categories[cat] / sum(imp) * 100
        marker = "★" if cat not in ['CONV'] else " "
        print(f"  {marker}{cat:<8}: {pct:5.1f}%")

ti_importance = sum(v for k, v in categories.items() if k != 'CONV')
print(f"\n  Total TI Sigma: {ti_importance/sum(imp)*100:.1f}%")

print("\nTop 20 Features:")
for i, (feat, val) in enumerate(imp.head(20).items()):
    cat = categorize_feature(feat)
    marker = "★" if cat != 'CONV' else " "
    print(f"  {marker}{i+1:2d}. [{cat:<5}] {feat:<30} {val:.4f}")


# === TI FEATURE SEPARATION ===

print("\n" + "=" * 70)
print("TI FEATURE SEPARATION (Enhanced)")
print("=" * 70)

ti_cols = ['taf_phi_hydro', 'taf_psi_hydro', 'taf_cert_hydro', 
           'I_hole', 'L_hole', 'total_hole', 
           'lcc_085_hydro', 'ti_synergy', 'ti_folding',
           'blosum_hydrophobic', 'blosum_aromatic']

for feat in ti_cols:
    if feat in X_train.columns:
        pos = X_train.loc[y_ex == 1, feat].mean()
        neg = X_train.loc[y_ex == 0, feat].mean()
        sep = abs(pos - neg) / (X_train[feat].std() + 1e-8)
        direction = "+" if pos > neg else "-"
        print(f"  {feat:<25}: {direction}{sep:.2f}σ (Pos={pos:.3f}, Neg={neg:.3f})")


# === SUBMISSION ===

print("\n" + "=" * 70)
print("GENERATING ENHANCED SUBMISSION")
print("=" * 70)

rows = []
for pid, term_probs in predictions.items():
    for term, prob in sorted(term_probs.items(), key=lambda x: -x[1]):
        rows.append(f"{pid}\t{term}\t{prob:.6f}")

with open('submission_ti_sigma_enhanced.tsv', 'w') as f:
    for row in rows:
        f.write(row + '\n')

print(f"\nSubmission rows: {len(rows)}")
print(f"Unique proteins: {len(predictions)}")
print(f"Saved: submission_ti_sigma_enhanced.tsv")

# Compare to baseline
try:
    baseline = sum(1 for line in open('submission_ti_sigma_fast.tsv'))
    print(f"\nComparison to baseline:")
    print(f"  Baseline rows: {baseline:,}")
    print(f"  Enhanced rows: {len(rows):,}")
    print(f"  Change: {(len(rows) - baseline) / baseline * 100:+.1f}%")
except:
    pass

print("\n✅ TI SIGMA CAFA6 ENHANCED v2 COMPLETE")
