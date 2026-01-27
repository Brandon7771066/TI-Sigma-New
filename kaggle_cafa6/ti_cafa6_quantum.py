"""
TI CAFA 6 - QUANTUM LCC VIRUS PROTEIN FUNCTION PREDICTOR
Applying TI Optical Quantum Framework to Protein Sequences:
- LCC Virus: Amino acid resonance patterns
- Jeff Time: Sequence position encoding
- Photonic Clustering: Domain state identification
- PRF: Probability as Resonance Field
Target: F-max optimization for $50K prize
"""

import numpy as np
import pandas as pd
from collections import Counter, defaultdict
from pathlib import Path
from scipy import stats
from sklearn.preprocessing import LabelEncoder
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI CAFA 6 - QUANTUM LCC VIRUS PROTEIN PREDICTOR")
print("Optical Quantum Framework for Protein Function")
print("="*70)

# ============ TI QUANTUM CONSTANTS ============
LCC_THRESHOLD_042 = 0.42
LCC_THRESHOLD_085 = 0.85
LCC_THRESHOLD_TT = 0.8464

# Jeff Time weights
TAU_PHI = 0.20   # Photonic memory
TAU_J = 0.45     # Jeff fiction
TAU_F = 0.20     # Freedom
TAU_LOVE = 0.15  # Love entanglement

# Amino acid properties (GILE mapping)
# G = Goodness (stability), I = Intuition (reactivity)
# L = Love (interaction), E = Environment (structure)
AA_PROPERTIES = {
    'A': {'hydro': 1.8, 'charge': 0, 'size': 89, 'polar': 0},
    'R': {'hydro': -4.5, 'charge': 1, 'size': 174, 'polar': 1},
    'N': {'hydro': -3.5, 'charge': 0, 'size': 132, 'polar': 1},
    'D': {'hydro': -3.5, 'charge': -1, 'size': 133, 'polar': 1},
    'C': {'hydro': 2.5, 'charge': 0, 'size': 121, 'polar': 0},
    'Q': {'hydro': -3.5, 'charge': 0, 'size': 146, 'polar': 1},
    'E': {'hydro': -3.5, 'charge': -1, 'size': 147, 'polar': 1},
    'G': {'hydro': -0.4, 'charge': 0, 'size': 75, 'polar': 0},
    'H': {'hydro': -3.2, 'charge': 0.5, 'size': 155, 'polar': 1},
    'I': {'hydro': 4.5, 'charge': 0, 'size': 131, 'polar': 0},
    'L': {'hydro': 3.8, 'charge': 0, 'size': 131, 'polar': 0},
    'K': {'hydro': -3.9, 'charge': 1, 'size': 146, 'polar': 1},
    'M': {'hydro': 1.9, 'charge': 0, 'size': 149, 'polar': 0},
    'F': {'hydro': 2.8, 'charge': 0, 'size': 165, 'polar': 0},
    'P': {'hydro': -1.6, 'charge': 0, 'size': 115, 'polar': 0},
    'S': {'hydro': -0.8, 'charge': 0, 'size': 105, 'polar': 1},
    'T': {'hydro': -0.7, 'charge': 0, 'size': 119, 'polar': 1},
    'W': {'hydro': -0.9, 'charge': 0, 'size': 204, 'polar': 1},
    'Y': {'hydro': -1.3, 'charge': 0, 'size': 181, 'polar': 1},
    'V': {'hydro': 4.2, 'charge': 0, 'size': 117, 'polar': 0},
}

def parse_fasta(filepath, limit=None):
    """Parse FASTA file into dict of {id: sequence}"""
    sequences = {}
    current_id = None
    current_seq = []
    
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('>'):
                if current_id:
                    sequences[current_id] = ''.join(current_seq)
                # Extract protein ID (first part before space)
                header = line[1:]
                current_id = header.split()[0]
                if '|' in current_id:
                    parts = current_id.split('|')
                    current_id = parts[1] if len(parts) > 1 else parts[0]
                current_seq = []
                
                if limit and len(sequences) >= limit:
                    break
            else:
                current_seq.append(line)
        
        if current_id:
            sequences[current_id] = ''.join(current_seq)
    
    return sequences

def lcc_resonance_sequence(seq1, seq2, coupling_sigma=5.0):
    """
    LCC Virus resonance between two sequences
    Treats amino acid properties as signal amplitude
    """
    if len(seq1) < 3 or len(seq2) < 3:
        return 0.0
    
    # Convert to hydrophobicity signal
    signal_a = np.array([AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in seq1])
    signal_b = np.array([AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in seq2])
    
    if len(signal_a) == 0 or len(signal_b) == 0:
        return 0.0
    
    # Normalize
    a_norm = (signal_a - np.mean(signal_a)) / (np.std(signal_a) + 1e-8)
    b_norm = (signal_b - np.mean(signal_b)) / (np.std(signal_b) + 1e-8)
    
    # Truncate to same length
    min_len = min(len(a_norm), len(b_norm))
    a_norm = a_norm[:min_len]
    b_norm = b_norm[:min_len]
    
    # Simple correlation
    if min_len < 3:
        return 0.0
    
    corr = np.corrcoef(a_norm, b_norm)[0, 1]
    return corr if not np.isnan(corr) else 0.0

def jeff_time_protein(sequence):
    """
    Jeff Time encoding for protein sequences
    Encodes position-weighted amino acid properties
    """
    if len(sequence) < 4:
        return {}
    
    n = len(sequence)
    
    # Get property arrays
    hydro = np.array([AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in sequence])
    charge = np.array([AA_PROPERTIES.get(aa, {}).get('charge', 0) for aa in sequence])
    size = np.array([AA_PROPERTIES.get(aa, {}).get('size', 100) for aa in sequence])
    
    # Photonic memory (recent = C-terminus weighted)
    weights_phi = np.exp(-TAU_PHI * np.arange(n)[::-1])
    photonic_memory = np.average(hydro, weights=weights_phi)
    
    # Jeff fiction (trend along sequence)
    if n > 2:
        momentum = np.polyfit(np.arange(n), hydro, 1)[0]
        jeff_fiction = momentum * TAU_J
    else:
        jeff_fiction = 0
    
    # Freedom (variability)
    freedom = np.std(hydro) * TAU_F
    
    # Love entanglement (N-term vs C-term correlation)
    mid = n // 2
    if mid > 3:
        love = TAU_LOVE * lcc_resonance_sequence(sequence[:mid], sequence[mid:])
    else:
        love = 0
    
    return {
        'jeff_photonic': photonic_memory,
        'jeff_fiction': jeff_fiction,
        'jeff_freedom': freedom,
        'jeff_love': love if not np.isnan(love) else 0,
        'jeff_total': photonic_memory + jeff_fiction + freedom + (love if not np.isnan(love) else 0)
    }

def photonic_cluster_protein(sequence, n_clusters=3):
    """
    Strawberry Fields photonic clustering for protein domains
    Identifies "quantum states" in the sequence
    """
    if len(sequence) < 10:
        return {}
    
    # Sliding window hydrophobicity
    window = 7
    hydro = np.array([AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in sequence])
    
    if len(hydro) < window:
        return {}
    
    # Smoothed profile
    smoothed = np.convolve(hydro, np.ones(window)/window, mode='valid')
    
    if len(smoothed) < 3:
        return {}
    
    # Cluster by percentiles
    p33 = np.percentile(smoothed, 33)
    p67 = np.percentile(smoothed, 67)
    
    low_state = smoothed[smoothed <= p33]
    mid_state = smoothed[(smoothed > p33) & (smoothed <= p67)]
    high_state = smoothed[smoothed > p67]
    
    return {
        'photonic_hydro_low': np.mean(low_state) if len(low_state) > 0 else 0,
        'photonic_hydro_mid': np.mean(mid_state) if len(mid_state) > 0 else 0,
        'photonic_hydro_high': np.mean(high_state) if len(high_state) > 0 else 0,
        'photonic_low_frac': len(low_state) / len(smoothed),
        'photonic_high_frac': len(high_state) / len(smoothed),
    }

def prf_protein(sequence, property_key='hydro', threshold=LCC_THRESHOLD_042):
    """
    PRF (Probability as Resonance Field) for proteins
    """
    if len(sequence) < 3:
        return 0.5
    
    values = np.array([AA_PROPERTIES.get(aa, {}).get(property_key, 0) for aa in sequence])
    normalized = (values - np.mean(values)) / (np.std(values) + 1e-8)
    
    positive = np.sum(normalized > threshold) / len(sequence)
    negative = np.sum(normalized < -threshold) / len(sequence)
    
    prf = (positive - negative + 1) / 2
    return prf

def extract_ti_protein_features(protein_id, sequence):
    """Extract TI Quantum features from protein sequence"""
    f = {}
    
    if len(sequence) < 5:
        return f
    
    # Basic stats
    f['length'] = len(sequence)
    f['log_length'] = np.log1p(len(sequence))
    
    # Amino acid composition
    aa_counts = Counter(sequence)
    for aa in 'ARNDCQEGHILKMFPSTWYV':
        f[f'aa_{aa}_frac'] = aa_counts.get(aa, 0) / len(sequence)
    
    # Property statistics
    hydro = [AA_PROPERTIES.get(aa, {}).get('hydro', 0) for aa in sequence]
    charge = [AA_PROPERTIES.get(aa, {}).get('charge', 0) for aa in sequence]
    size = [AA_PROPERTIES.get(aa, {}).get('size', 100) for aa in sequence]
    
    for prop, values in [('hydro', hydro), ('charge', charge), ('size', size)]:
        if len(values) > 0:
            f[f'{prop}_mean'] = np.mean(values)
            f[f'{prop}_std'] = np.std(values)
            f[f'{prop}_min'] = np.min(values)
            f[f'{prop}_max'] = np.max(values)
            f[f'{prop}_range'] = np.max(values) - np.min(values)
    
    # LCC resonance (self-correlation)
    mid = len(sequence) // 2
    if mid > 5:
        f['lcc_self_resonance'] = lcc_resonance_sequence(sequence[:mid], sequence[mid:])
    
    # Jeff Time features
    jeff = jeff_time_protein(sequence)
    f.update(jeff)
    
    # Photonic clustering
    photonic = photonic_cluster_protein(sequence)
    f.update(photonic)
    
    # PRF features
    f['prf_hydro_042'] = prf_protein(sequence, 'hydro', LCC_THRESHOLD_042)
    f['prf_hydro_085'] = prf_protein(sequence, 'hydro', LCC_THRESHOLD_085)
    f['prf_charge_042'] = prf_protein(sequence, 'charge', LCC_THRESHOLD_042)
    
    # Entropy (I-dimension proxy)
    probs = np.array(list(aa_counts.values())) / len(sequence)
    f['entropy'] = -np.sum(probs * np.log2(probs + 1e-10))
    f['entropy_normalized'] = f['entropy'] / np.log2(20)  # Max entropy for 20 AA
    
    # GILE mapping
    f['gile_g'] = np.mean([1 if AA_PROPERTIES.get(aa, {}).get('polar', 0) == 0 else 0 for aa in sequence])  # G = stability
    f['gile_i'] = f['entropy_normalized']  # I = information
    f['gile_l'] = np.mean([1 if AA_PROPERTIES.get(aa, {}).get('charge', 0) != 0 else 0 for aa in sequence])  # L = interactions
    f['gile_e'] = np.std(hydro) if len(hydro) > 0 else 0  # E = structural variability
    
    # Sacred interval (GILE)
    if len(hydro) > 0:
        h_mean = np.mean(hydro)
        h_std = np.std(hydro)
        sacred_low = h_mean - 2*h_std/3
        sacred_high = h_mean + h_std/3
        f['sacred_fraction'] = np.sum((np.array(hydro) >= sacred_low) & (np.array(hydro) <= sacred_high)) / len(hydro)
    
    return f

# ============ LOAD DATA ============
print("\nLoading data...")

train_seqs = parse_fasta('train_sequences.fasta', limit=5000)  # Start with subset
test_seqs = parse_fasta('test_sequences.fasta', limit=1000)
train_terms = pd.read_csv('train_terms.tsv', sep='\t')

print(f"Train sequences: {len(train_seqs)}")
print(f"Test sequences: {len(test_seqs)}")
print(f"Train terms: {len(train_terms)}")

# Get unique GO terms
go_terms = train_terms['term'].unique()
print(f"Unique GO terms: {len(go_terms)}")

# ============ EXTRACT FEATURES ============
print("\nExtracting TI Quantum features...")

train_features = {}
for i, (pid, seq) in enumerate(train_seqs.items()):
    train_features[pid] = extract_ti_protein_features(pid, seq)
    if (i+1) % 1000 == 0:
        print(f"  Train: {i+1}/{len(train_seqs)}")

test_features = {}
for i, (pid, seq) in enumerate(test_seqs.items()):
    test_features[pid] = extract_ti_protein_features(pid, seq)
    if (i+1) % 500 == 0:
        print(f"  Test: {i+1}/{len(test_seqs)}")

# ============ SIMPLE BASELINE ============
print("\n" + "="*60)
print("BUILDING BASELINE MODEL")
print("="*60)

# Get GO term frequencies
term_counts = train_terms['term'].value_counts()
top_terms = term_counts.head(100).index.tolist()
print(f"Top 100 GO terms cover {term_counts.head(100).sum()} annotations")

# For each protein, predict based on similar protein features
# This is a simple k-NN style baseline

# Build feature matrix
train_df = pd.DataFrame(train_features).T.fillna(0)
test_df = pd.DataFrame(test_features).T.fillna(0)

# Align columns
common_cols = list(set(train_df.columns) & set(test_df.columns))
train_df = train_df[common_cols]
test_df = test_df[common_cols]

print(f"Features: {len(common_cols)}")

# ============ LCC VIRUS VALIDATION ============
print("\n" + "="*60)
print("LCC VIRUS FEATURE ANALYSIS")
print("="*60)

lcc_features = ['lcc_self_resonance', 'jeff_photonic', 'jeff_love', 'prf_hydro_042', 'sacred_fraction']
for feat in lcc_features:
    if feat in train_df.columns:
        values = train_df[feat].dropna()
        print(f"  {feat:25s}: mean={values.mean():.4f}, std={values.std():.4f}")

# ============ SIMPLE PREDICTIONS ============
print("\n" + "="*60)
print("GENERATING PREDICTIONS")
print("="*60)

# For baseline: predict most common GO terms for all proteins
# Weight by sequence similarity features

# Load sample submission format
sample_sub = pd.read_csv('sample_submission.tsv', sep='\t', header=None, names=['protein_id', 'go_term', 'probability', 'extra'])

# Get test protein IDs from sample
test_proteins = sample_sub['protein_id'].unique()
print(f"Test proteins in submission: {len(test_proteins)}")

# Build predictions
predictions = []

# GO term prior probabilities
term_priors = (term_counts / len(train_seqs.keys())).to_dict()

for pid in test_proteins[:100]:  # Subset for demo
    seq = test_seqs.get(pid, "")
    feats = test_features.get(pid, {})
    
    # Predict top GO terms with prior-weighted probability
    for go_term in top_terms[:10]:  # Top 10 terms per protein
        prob = term_priors.get(go_term, 0.01)
        
        # Adjust by protein features (LCC modulation)
        if feats:
            entropy_factor = feats.get('entropy_normalized', 0.5)
            sacred_factor = feats.get('sacred_fraction', 0.5)
            prob *= (0.5 + entropy_factor * 0.5) * (0.5 + sacred_factor * 0.5)
        
        predictions.append({
            'protein_id': pid,
            'go_term': go_term,
            'probability': min(prob, 0.99)
        })

pred_df = pd.DataFrame(predictions)
print(f"Generated {len(pred_df)} predictions")

# Save
pred_df.to_csv('submission_cafa6_baseline.tsv', sep='\t', index=False, header=False)
print("\n✅ Saved: submission_cafa6_baseline.tsv")

print("\n" + "="*60)
print("TI CAFA 6 QUANTUM SOLVER COMPLETE")
print("="*60)
print("""
Key TI Features Applied:
1. LCC Virus: Self-resonance of N-term vs C-term
2. Jeff Time: Position-weighted property encoding
3. Photonic Clustering: Hydrophobicity domain states
4. PRF: Probability as Resonance Field
5. GILE Mapping: G=stability, I=entropy, L=charge, E=structure
6. Sacred Fraction: Amino acids in "sacred interval"

Next Steps:
- Scale to full dataset
- Train per-GO-term classifiers
- Use sequence homology + TI features
- Apply LCC for cross-protein resonance
""")
