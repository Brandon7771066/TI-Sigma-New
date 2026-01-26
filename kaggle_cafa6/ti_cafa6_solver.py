"""
TI CAFA 6 PROTEIN FUNCTION PREDICTION SOLVER
Predict Gene Ontology terms from protein sequences
Metric: Multi-label F-max | Prize: $50,000

DATA NEEDED (download from Kaggle):
- train_sequences.fasta
- train_terms.tsv
- test_sequences.fasta
- go_ontology.obo or go_terms.tsv
- sample_submission.csv

This is a MULTI-LABEL classification problem where each protein
can have multiple Gene Ontology (GO) terms.
"""

import pandas as pd
import numpy as np
from pathlib import Path
from collections import defaultdict
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI CAFA 6 PROTEIN FUNCTION PREDICTION SOLVER")
print("Gene Ontology Prediction | F-max Metric | $50K Prize")
print("="*70)

# Check for data
DATA_DIR = Path(".")
required_files = ['sample_submission.csv']

missing = [f for f in required_files if not (DATA_DIR / f).exists()]

if missing:
    print(f"\n⚠️  MISSING DATA FILES")
    print("\nDownload from: https://www.kaggle.com/competitions/cafa-6-protein-function-prediction/data")
    print("Place files in: kaggle_cafa6/")
    print("\nRequired files:")
    print("  - train_sequences.fasta")
    print("  - train_terms.tsv")
    print("  - test_sequences.fasta")
    print("  - sample_submission.csv")

# FASTA parser
def parse_fasta(filepath):
    """Parse FASTA file into dict of {protein_id: sequence}"""
    sequences = {}
    current_id = None
    current_seq = []
    
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith('>'):
                    if current_id:
                        sequences[current_id] = ''.join(current_seq)
                    current_id = line[1:].split()[0]
                    current_seq = []
                else:
                    current_seq.append(line)
            if current_id:
                sequences[current_id] = ''.join(current_seq)
    except FileNotFoundError:
        print(f"File not found: {filepath}")
        return {}
    
    return sequences

# Feature extraction from protein sequences
def extract_protein_features(sequence):
    """Extract features from amino acid sequence (TI-enhanced)"""
    if not sequence:
        return {}
    
    features = {}
    
    # Length
    features['length'] = len(sequence)
    features['log_length'] = np.log1p(len(sequence))
    
    # Amino acid composition
    aa_list = 'ACDEFGHIKLMNPQRSTVWY'
    for aa in aa_list:
        features[f'aa_{aa}'] = sequence.count(aa) / len(sequence)
    
    # Physicochemical groups
    hydrophobic = set('AILMFVPWG')
    polar = set('STYCNQ')
    charged_pos = set('KRH')
    charged_neg = set('DE')
    aromatic = set('FWY')
    
    features['hydrophobic_ratio'] = sum(1 for aa in sequence if aa in hydrophobic) / len(sequence)
    features['polar_ratio'] = sum(1 for aa in sequence if aa in polar) / len(sequence)
    features['charged_pos_ratio'] = sum(1 for aa in sequence if aa in charged_pos) / len(sequence)
    features['charged_neg_ratio'] = sum(1 for aa in sequence if aa in charged_neg) / len(sequence)
    features['aromatic_ratio'] = sum(1 for aa in sequence if aa in aromatic) / len(sequence)
    features['net_charge'] = features['charged_pos_ratio'] - features['charged_neg_ratio']
    
    # TI-inspired: Information entropy (relates to GILE I-dimension)
    from collections import Counter
    aa_counts = Counter(sequence)
    probs = np.array([count/len(sequence) for count in aa_counts.values()])
    features['entropy'] = -np.sum(probs * np.log2(probs + 1e-10))
    
    # Dipeptide features (top 20 most common)
    if len(sequence) >= 2:
        dipeptides = [sequence[i:i+2] for i in range(len(sequence)-1)]
        di_counts = Counter(dipeptides)
        total_di = len(dipeptides)
        
        # Most informative dipeptides for function prediction
        key_dipeptides = ['GG', 'PP', 'SS', 'AA', 'LL', 'VV', 'II', 'FF', 
                         'KK', 'RR', 'DD', 'EE', 'CC', 'MM', 'WW', 'GP', 
                         'PG', 'GS', 'SG', 'GA']
        for di in key_dipeptides:
            features[f'di_{di}'] = di_counts.get(di, 0) / total_di
    
    # Molecular weight estimate (simplified)
    aa_weights = {
        'A': 89, 'R': 174, 'N': 132, 'D': 133, 'C': 121,
        'E': 147, 'Q': 146, 'G': 75, 'H': 155, 'I': 131,
        'L': 131, 'K': 146, 'M': 149, 'F': 165, 'P': 115,
        'S': 105, 'T': 119, 'W': 204, 'Y': 181, 'V': 117
    }
    features['mol_weight'] = sum(aa_weights.get(aa, 100) for aa in sequence)
    
    # Isoelectric point estimate (simplified)
    pKa_pos = {'K': 10.5, 'R': 12.5, 'H': 6.0}
    pKa_neg = {'D': 3.9, 'E': 4.1}
    
    pos_count = sum(1 for aa in sequence if aa in pKa_pos)
    neg_count = sum(1 for aa in sequence if aa in pKa_neg)
    features['pI_estimate'] = 7.0 + 0.5 * (pos_count - neg_count) / len(sequence)
    
    return features

# Load and process data
print("\nChecking for data files...")

train_seq_path = 'train_sequences.fasta'
train_terms_path = 'train_terms.tsv'
test_seq_path = 'test_sequences.fasta'
sample_sub_path = 'sample_submission.csv'

has_train_seq = Path(train_seq_path).exists()
has_train_terms = Path(train_terms_path).exists()
has_test_seq = Path(test_seq_path).exists()
has_sample = Path(sample_sub_path).exists()

print(f"train_sequences.fasta: {'✓' if has_train_seq else '✗'}")
print(f"train_terms.tsv: {'✓' if has_train_terms else '✗'}")
print(f"test_sequences.fasta: {'✓' if has_test_seq else '✗'}")
print(f"sample_submission.csv: {'✓' if has_sample else '✗'}")

if not (has_train_seq and has_train_terms and has_test_seq):
    print("\n⚠️  Missing required data files!")
    print("Download from Kaggle and place in kaggle_cafa6/")
    
    # Create template submission
    print("\nCreating template solver structure...")
    
    # Example of what the full solution would look like
    print("""
FULL SOLUTION PIPELINE:
1. Parse FASTA sequences
2. Extract protein features (length, AA composition, physicochemical)
3. Build GO term embedding from ontology
4. Train multi-label classifier per GO branch (MF, BP, CC)
5. Propagate predictions up the GO hierarchy
6. Optimize threshold for F-max

TI ENHANCEMENTS:
- Use entropy as GILE I-dimension proxy for complexity
- Apply LCC threshold (0.42) for confidence filtering
- Tessellation-inspired GO term clustering
""")
    exit(0)

# Full pipeline when data is available
print("\nLoading sequences...")
train_sequences = parse_fasta(train_seq_path)
test_sequences = parse_fasta(test_seq_path)

print(f"Training proteins: {len(train_sequences)}")
print(f"Test proteins: {len(test_sequences)}")

# Load training labels
print("\nLoading GO terms...")
train_terms = pd.read_csv(train_terms_path, sep='\t')
print(f"Training term assignments: {len(train_terms)}")
print(f"Unique proteins: {train_terms['EntryID'].nunique()}")
print(f"Unique GO terms: {train_terms['term'].nunique()}")

# Build protein -> terms mapping
protein_terms = defaultdict(set)
for _, row in train_terms.iterrows():
    protein_terms[row['EntryID']].add(row['term'])

# Extract features
print("\nExtracting protein features...")

train_features_list = []
for pid, seq in train_sequences.items():
    feats = extract_protein_features(seq)
    feats['protein_id'] = pid
    train_features_list.append(feats)

test_features_list = []
for pid, seq in test_sequences.items():
    feats = extract_protein_features(seq)
    feats['protein_id'] = pid
    test_features_list.append(feats)

train_features = pd.DataFrame(train_features_list)
test_features = pd.DataFrame(test_features_list)

print(f"Train features shape: {train_features.shape}")
print(f"Test features shape: {test_features.shape}")

# Get most common GO terms for baseline
term_counts = train_terms['term'].value_counts()
print(f"\nMost common GO terms:")
print(term_counts.head(10))

# Simple baseline: predict top N most common terms
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler

# Get top 100 most common terms for multi-label prediction
top_terms = term_counts.head(100).index.tolist()

# Build binary labels for each term
print(f"\nBuilding multi-label targets for {len(top_terms)} terms...")

feature_cols = [c for c in train_features.columns if c != 'protein_id']
X = train_features[feature_cols].fillna(0)
X_test = test_features[feature_cols].fillna(0)

# Scale
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
X_test_scaled = scaler.transform(X_test)

# Train one classifier per term
print("\nTraining classifiers (this may take a while)...")

term_predictions = {}
term_models = {}

for i, term in enumerate(top_terms[:50]):  # Start with top 50 for speed
    # Binary label
    y_term = train_features['protein_id'].apply(
        lambda pid: 1 if term in protein_terms.get(pid, set()) else 0
    ).values
    
    if y_term.sum() < 10:  # Skip very rare terms
        continue
    
    # Train model
    model = HistGradientBoostingClassifier(
        max_iter=100,
        max_depth=4,
        learning_rate=0.1,
        l2_regularization=0.5,
        random_state=42
    )
    model.fit(X_scaled, y_term)
    term_models[term] = model
    
    # Predict on test
    test_proba = model.predict_proba(X_test_scaled)[:, 1]
    term_predictions[term] = test_proba
    
    if (i + 1) % 10 == 0:
        print(f"  Trained {i+1}/{len(top_terms[:50])} terms")

print(f"\nTrained models for {len(term_models)} terms")

# Generate submission
print("\nGenerating submission...")

# Load sample submission to get exact format
if has_sample:
    sample = pd.read_csv(sample_sub_path)
    print(f"Sample submission format:")
    print(sample.head())
    sample_cols = sample.columns.tolist()
    print(f"Required columns: {sample_cols}")
else:
    sample_cols = None
    print("⚠️  No sample submission - using default format")

test_protein_ids = test_features['protein_id'].values

submission_rows = []
for pid_idx, pid in enumerate(test_protein_ids):
    for term, proba in term_predictions.items():
        conf = proba[pid_idx]
        if conf > 0.1:
            submission_rows.append({
                'protein_id': pid,
                'term': term,
                'confidence': conf
            })

submission = pd.DataFrame(submission_rows)
print(f"Submission rows: {len(submission)}")

# Align columns with sample if available
if sample_cols:
    col_mapping = {
        'protein_id': ['protein_id', 'EntryID', 'Protein', 'id'],
        'term': ['term', 'GO_term', 'go_term', 'Term'],
        'confidence': ['confidence', 'Confidence', 'score', 'Score', 'probability']
    }
    
    for target_col in sample_cols:
        matched = False
        for our_col, alternatives in col_mapping.items():
            if target_col in alternatives or target_col.lower() == our_col:
                if our_col in submission.columns and target_col != our_col:
                    submission = submission.rename(columns={our_col: target_col})
                matched = True
                break
    
    submission = submission[[c for c in sample_cols if c in submission.columns]]
    print(f"Aligned columns: {submission.columns.tolist()}")

submission.to_csv('submission_cafa6.csv', index=False)
print(f"\n✅ Saved: submission_cafa6.csv")
print(f"\n⚠️  NOTE: This baseline uses only top 50 GO terms.")
print("   For competitive results, implement GO hierarchy propagation")
