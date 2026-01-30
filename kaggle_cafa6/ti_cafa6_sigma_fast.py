"""
TI CAFA 6 - SIGMA FAST SOLVER
Optimized for large dataset with vectorized operations
"""

import numpy as np
import pandas as pd
from collections import Counter, defaultdict
from pathlib import Path
from scipy import stats
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier
import warnings
warnings.filterwarnings('ignore')

print("=" * 70)
print("TI CAFA 6 - SIGMA FAST SOLVER")
print("=" * 70)

# Constants
LCC_DETECTABLE = 0.42
LCC_CAUSAL = 0.85

AA_HYDRO = {
    'A': 1.8, 'R': -4.5, 'N': -3.5, 'D': -3.5, 'C': 2.5,
    'Q': -3.5, 'E': -3.5, 'G': -0.4, 'H': -3.2, 'I': 4.5,
    'L': 3.8, 'K': -3.9, 'M': 1.9, 'F': 2.8, 'P': -1.6,
    'S': -0.8, 'T': -0.7, 'W': -0.9, 'Y': -1.3, 'V': 4.2,
}

AMINO_ACIDS = 'ARNDCQEGHILKMFPSTWYV'


def parse_fasta_fast(filepath):
    """Fast FASTA parsing."""
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


def extract_features_vectorized(sequence):
    """Fast vectorized feature extraction."""
    if len(sequence) < 10:
        return None
    
    f = {}
    n = len(sequence)
    
    # Length
    f['length'] = n
    f['log_length'] = np.log1p(n)
    
    # AA composition
    counts = Counter(sequence)
    for aa in AMINO_ACIDS:
        f[f'aa_{aa}'] = counts.get(aa, 0) / n
    
    # Hydrophobicity profile
    hydro = np.array([AA_HYDRO.get(aa, 0) for aa in sequence])
    f['hydro_mean'] = np.mean(hydro)
    f['hydro_std'] = np.std(hydro)
    f['hydro_min'] = np.min(hydro)
    f['hydro_max'] = np.max(hydro)
    
    # TAF on hydrophobicity (MALLORN innovation)
    t = np.maximum(0, hydro)
    f_neg = np.maximum(0, -hydro)
    phi = np.exp(-hydro**2)
    norm = np.sqrt(t**2 + f_neg**2 + phi**2 + 0.1)
    
    f['taf_T'] = np.mean(t / norm)
    f['taf_F'] = np.mean(f_neg / norm)
    f['taf_phi'] = np.mean(phi / norm)
    f['taf_certainty'] = 1 - f['taf_phi']
    
    # Anti-GILE Holes (MALLORN innovation)
    expected = np.convolve(hydro, np.ones(5)/5, mode='same')
    residual = np.abs(hydro - expected)
    f['I_hole'] = np.mean(residual) / (f['hydro_std'] + 1e-8)
    
    if len(hydro) > 3:
        ac = np.corrcoef(hydro[:-1], hydro[1:])[0, 1]
        f['L_hole'] = 1.0 - np.abs(ac) if not np.isnan(ac) else 0.5
    else:
        f['L_hole'] = 0.5
    
    f['G_hole'] = np.mean(np.abs(np.diff(hydro))) / 2
    f['total_hole'] = (f['I_hole'] + f['L_hole'] + f['G_hole']) / 3
    
    # LCC
    max_h = np.max(np.abs(hydro)) + 1e-10
    normalized = np.abs(hydro) / max_h
    f['lcc_042'] = np.mean(normalized > LCC_DETECTABLE)
    f['lcc_085'] = np.mean(normalized > LCC_CAUSAL)
    
    # Entropy
    probs = np.array(list(counts.values())) / n
    entropy = -np.sum(probs * np.log2(probs + 1e-10))
    f['entropy'] = entropy / np.log2(20)
    
    # Structure propensity
    f['helix'] = sum(1 for aa in sequence if aa in 'AELM') / n
    f['sheet'] = sum(1 for aa in sequence if aa in 'VIY') / n
    
    # Regional
    third = n // 3
    if third > 5:
        f['hydro_N'] = np.mean(hydro[:third])
        f['hydro_C'] = np.mean(hydro[-third:])
    else:
        f['hydro_N'] = f['hydro_C'] = f['hydro_mean']
    
    # TI synergy
    f['ti_synergy'] = f['taf_certainty'] * 0.4 + (1 - f['total_hole']) * 0.4 + f['entropy'] * 0.2
    
    return f


# === LOAD DATA ===

print("\nLoading data...")
train_seqs = parse_fasta_fast('train_sequences.fasta')
test_seqs = parse_fasta_fast('test_sequences.fasta')

print(f"Training: {len(train_seqs)}")
print(f"Test: {len(test_seqs)}")

# Load GO terms
train_terms = pd.read_csv('train_terms.tsv', sep='\t', header=0, 
                          names=['EntryID', 'term', 'aspect'])
print(f"GO terms: {train_terms['term'].nunique()}")

protein_terms = defaultdict(set)
for _, row in train_terms.iterrows():
    protein_terms[row['EntryID']].add(row['term'])

# Top terms
term_counts = train_terms['term'].value_counts()
TOP_N = 50
top_terms = term_counts.head(TOP_N).index.tolist()
print(f"Focusing on top {TOP_N} GO terms")


# === EXTRACT FEATURES ===

print("\nExtracting features...")

train_features = []
train_ids = []
for i, (pid, seq) in enumerate(train_seqs.items()):
    feat = extract_features_vectorized(seq)
    if feat:
        train_features.append(feat)
        train_ids.append(pid)
    if (i + 1) % 10000 == 0:
        print(f"  Train: {i+1}/{len(train_seqs)}")

test_features = []
test_ids = []
for i, (pid, seq) in enumerate(test_seqs.items()):
    feat = extract_features_vectorized(seq)
    if feat:
        test_features.append(feat)
        test_ids.append(pid)
    if (i + 1) % 20000 == 0:
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
print("TRAINING CLASSIFIERS")
print("=" * 70)

scaler = StandardScaler()
X_tr = scaler.fit_transform(X_train)
X_te = scaler.transform(X_test)

predictions = defaultdict(dict)

for i, term in enumerate(top_terms):
    y = np.array([1 if term in protein_terms.get(pid, set()) else 0 for pid in train_ids])
    
    if y.sum() < 20:
        continue
    
    clf = LogisticRegression(class_weight='balanced', max_iter=300, random_state=42, n_jobs=-1)
    clf.fit(X_tr, y)
    
    probs = clf.predict_proba(X_te)[:, 1]
    
    for pid, prob in zip(test_ids, probs):
        if prob > 0.05:
            predictions[pid][term] = prob
    
    if (i + 1) % 10 == 0:
        print(f"  Trained {i+1}/{len(top_terms)}")

print(f"\nPredictions for {len(predictions)} proteins")


# === FEATURE IMPORTANCE ===

print("\n" + "=" * 70)
print("TI SIGMA FEATURE IMPORTANCE")
print("=" * 70)

y_ex = np.array([1 if top_terms[0] in protein_terms.get(pid, set()) else 0 for pid in train_ids])

rf = RandomForestClassifier(n_estimators=50, max_depth=6, class_weight='balanced', 
                             random_state=42, n_jobs=-1)
rf.fit(X_tr, y_ex)
imp = pd.Series(rf.feature_importances_, index=cols).sort_values(ascending=False)

ti_features = [f for f in cols if any(x in f for x in ['taf_', 'hole', 'lcc_', 'ti_'])]
ti_imp = sum(imp.get(f, 0) for f in ti_features) / sum(imp) * 100

print(f"\nTI Sigma importance: {ti_imp:.1f}%")
print("\nTop 15 features:")
for i, (feat, val) in enumerate(imp.head(15).items()):
    marker = "★" if any(x in feat for x in ['taf_', 'hole', 'lcc_', 'ti_']) else " "
    print(f"  {marker}{i+1:2d}. {feat:<25} {val:.4f}")


# === TDE vs NON-TDE SIGNATURE (for example term) ===

print("\n" + "=" * 70)
print("TI FEATURE SEPARATION")
print("=" * 70)

ti_cols = ['taf_phi', 'taf_certainty', 'I_hole', 'L_hole', 'total_hole', 'lcc_085', 'ti_synergy']

for feat in ti_cols:
    if feat in X_train.columns:
        pos = X_train.loc[y_ex == 1, feat].mean()
        neg = X_train.loc[y_ex == 0, feat].mean()
        sep = abs(pos - neg) / (X_train[feat].std() + 1e-8)
        print(f"  {feat:<20}: Pos={pos:.4f}, Neg={neg:.4f}, Sep={sep:.2f}σ")


# === SUBMISSION ===

print("\n" + "=" * 70)
print("GENERATING SUBMISSION")
print("=" * 70)

rows = []
for pid, term_probs in predictions.items():
    for term, prob in sorted(term_probs.items(), key=lambda x: -x[1]):
        rows.append(f"{pid}\t{term}\t{prob:.6f}")

with open('submission_ti_sigma_fast.tsv', 'w') as f:
    for row in rows:
        f.write(row + '\n')

print(f"\nSubmission rows: {len(rows)}")
print(f"Saved: submission_ti_sigma_fast.tsv")

print("\n✅ TI SIGMA CAFA6 FAST COMPLETE")
