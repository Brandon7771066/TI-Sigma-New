"""
TI CAFA6 Hypercomputer — Full TI Sigma Architecture
=====================================================

Competition: CAFA 6 — Critical Assessment of protein Function Annotation
Task:        Predict Gene Ontology (GO) term assignments from protein sequences
Metric:      F-max (weighted precision-recall across all GO terms)

TI Insight:
  The 20 amino acids map cleanly onto Tralsebit 4-valued logic:
    hydrophobic (VILMFYWCA) → +0.8  (True / ordered)
    hydrophilic (DEKRHNQS)  → -0.8  (False / disordered)
    neutral     (GPT)       → 0.0   (Indeterminate)
    ambiguous   (X*-)       → LCC_TRALSE (Tralse / unknown)

  A protein sequence is a Tralsebit string. Its tralse_ratio captures
  the proportion of residues in the structural ambiguity zone — which
  is biologically meaningful: disordered regions (high tralse_ratio)
  tend to be hub proteins with broad GO annotation breadth.

Layer architecture:
  L1  CAFA6Adapter.encode_sequence() → Tralsebit amino acid array
  L2  AperiodicOptimizer             → Penrose sequence features
  L3  TISigmaQuantumLayer            → φ-squeezing on sequence stats
  Model: LogisticRegression per GO term (top-N most common)

Brandon Emerick — TI Sigma Research
February 27, 2026
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import pandas as pd
from collections import defaultdict
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.model_selection import cross_val_score
import warnings
warnings.filterwarnings('ignore')

from ti_sigma import (TralsebitEngine, AperiodicOptimizer,
                       TISigmaQuantumLayer, PHI, LCC_TRALSE)
from ti_sigma.constants import verify_matching_rules
from ti_sigma.kaggle_adapter import CAFA6Adapter

print("=" * 70)
print("TI CAFA6 HYPERCOMPUTER — TI SIGMA ARCHITECTURE")
print("=" * 70)

rules = verify_matching_rules()
print("Matching rules:", {k: f"{v:.1e}" for k, v in rules.items()})

adapter = CAFA6Adapter(n_hash_features=256)
ql      = TISigmaQuantumLayer(n_modes=6)
print(f"CAFA6Adapter initialized\n")

COMP_DIR = os.path.dirname(__file__)

# ─── Data Loading ──────────────────────────────────────────────────────────
def parse_fasta(filepath):
    seqs = {}
    current_id, current_seq = None, []
    with open(filepath) as fh:
        for line in fh:
            line = line.strip()
            if line.startswith('>'):
                if current_id:
                    seqs[current_id] = ''.join(current_seq)
                parts = line[1:].split('|')
                current_id  = parts[1] if len(parts) > 1 else parts[0].split()[0]
                current_seq = []
            else:
                current_seq.append(line)
    if current_id:
        seqs[current_id] = ''.join(current_seq)
    return seqs

print("[1/5] Loading data...")
train_seqs = parse_fasta(os.path.join(COMP_DIR, 'train_sequences.fasta'))
test_seqs  = parse_fasta(os.path.join(COMP_DIR, 'test_sequences.fasta'))
terms_df   = pd.read_csv(os.path.join(COMP_DIR, 'train_terms.tsv'),
                          sep='\t', header=None, names=['protein_id', 'go_id', 'ontology'])

print(f"  Train sequences: {len(train_seqs):,}")
print(f"  Test  sequences: {len(test_seqs):,}")
print(f"  Training annotations: {len(terms_df):,}")
print(f"  Unique GO terms: {terms_df['go_id'].nunique():,}")

# ─── Feature Extraction ────────────────────────────────────────────────────
MAX_LEN = 512

print("\n[2/5] Extracting Hypercomputer features from sequences...")

def seq_to_hc_features(seq: str) -> np.ndarray:
    """
    Full four-layer HC encoding for a protein sequence.

    L1: Tralsebit amino acid encoding (hydrophobic/philic/neutral/ambiguous)
    L2: Penrose aperiodic sequence features on the Tralsebit array
    L3: Quantum feature transform on 6 summary statistics
    """
    tb = adapter.encode_sequence(seq, max_len=MAX_LEN)

    # L2: Penrose features
    pen = adapter.optimizer.penrose.sequence_features(tb)

    # Summary stats for L3
    stats = np.array([
        float(np.mean(tb)),
        float(np.std(tb)),
        adapter.engine.tralse_ratio(tb),
        adapter.engine.sacred_fraction(tb),
        adapter.engine.lcc_coherence(tb),
        float(len(seq)) / MAX_LEN,     # sequence length (normalized)
    ])

    # L3: quantum transform on summary stats
    q = ql.quantum_feature_transform(stats.reshape(1, -1)).flatten()

    return np.concatenate([pen, stats, q])

train_ids = [pid for pid in train_seqs if pid in terms_df['protein_id'].values or True]
test_id_list = list(test_seqs.keys())

print(f"  Computing features for {len(train_seqs):,} train sequences...")
train_feat_dict = {}
for i, (pid, seq) in enumerate(train_seqs.items()):
    train_feat_dict[pid] = seq_to_hc_features(seq)
    if (i + 1) % 2000 == 0:
        print(f"    {i+1:,} / {len(train_seqs):,}", flush=True)

print(f"  Computing features for {len(test_seqs):,} test sequences...")
test_feat_dict = {}
for i, (pid, seq) in enumerate(test_seqs.items()):
    test_feat_dict[pid] = seq_to_hc_features(seq)

# Build matrices
train_protein_ids = list(train_feat_dict.keys())
X_train_mat = np.vstack([train_feat_dict[pid] for pid in train_protein_ids])
X_test_mat  = np.vstack([test_feat_dict[pid]  for pid in test_id_list])

print(f"\n  Train feature matrix: {X_train_mat.shape}")
print(f"  Test  feature matrix: {X_test_mat.shape}")

# ─── TI Sequence-Level Analysis ────────────────────────────────────────────
print("\n--- TI Sequence Statistics ---")
feature_idx = {'tralse_ratio': len(adapter.optimizer.penrose.sequence_features(np.zeros(MAX_LEN))) + 2,
               'sacred_frac':  len(adapter.optimizer.penrose.sequence_features(np.zeros(MAX_LEN))) + 3}

all_tr = X_train_mat[:, feature_idx['tralse_ratio']]
all_sf = X_train_mat[:, feature_idx['sacred_frac']]
print(f"  Mean tralse_ratio (all seqs):    {all_tr.mean():.4f}  (±{all_tr.std():.4f})")
print(f"  Mean sacred_fraction (all seqs): {all_sf.mean():.4f}  (±{all_sf.std():.4f})")
print(f"  Sequences with high tralse (>0.42): {(all_tr > 0.42).mean()*100:.1f}%")

# ─── Per-GO-Term Classification ────────────────────────────────────────────
print("\n[3/5] Training per-GO-term classifiers...")

# Focus on top-200 most frequent GO terms for tractability
go_counts = terms_df['go_id'].value_counts()
top_go    = go_counts.head(200).index.tolist()
print(f"  Training classifiers for top {len(top_go)} GO terms")

# Build label lookup: protein_id → set of GO terms
protein_go = defaultdict(set)
for _, row in terms_df.iterrows():
    protein_go[row['protein_id']].add(row['go_id'])

scaler   = StandardScaler()
X_tr_s   = scaler.fit_transform(X_train_mat)
X_te_s   = scaler.transform(X_test_mat)

classifiers = {}
go_cv_scores = {}

for i, go_term in enumerate(top_go):
    y = np.array([1 if go_term in protein_go.get(pid, set()) else 0
                  for pid in train_protein_ids])
    pos_rate = y.mean()
    if pos_rate < 0.005 or pos_rate > 0.995:
        continue
    clf = LogisticRegression(C=0.5, max_iter=300, n_jobs=-1, random_state=42)
    clf.fit(X_tr_s, y)
    classifiers[go_term] = clf
    if (i + 1) % 50 == 0:
        print(f"    Trained {i+1}/{len(top_go)} GO terms  "
              f"(latest: {go_term}, pos_rate={pos_rate:.3f})", flush=True)

print(f"  Trained {len(classifiers)} classifiers")

# ─── Generate Submission ───────────────────────────────────────────────────
print("\n[4/5] Generating predictions...")

rows = []
conf_threshold = 0.30

for go_term, clf in classifiers.items():
    probs = clf.predict_proba(X_te_s)[:, 1]
    for pid, prob in zip(test_id_list, probs):
        if prob >= conf_threshold:
            rows.append({'protein_id': pid, 'go_id': go_term, 'confidence': round(prob, 4)})

sub_df = pd.DataFrame(rows)
out_path = os.path.join(COMP_DIR, 'submission_cafa6_hypercomputer.tsv')
sub_df.to_csv(out_path, sep='\t', index=False, header=False)

print(f"  Total predictions: {len(sub_df):,}")
print(f"  Unique proteins predicted: {sub_df['protein_id'].nunique():,}")
print(f"  Unique GO terms predicted: {sub_df['go_id'].nunique():,}")
print(f"  Saved: {out_path}")
print(f"\n  Sample predictions:")
print(sub_df.head(10).to_string(index=False))

# ─── Per-Ontology Stats ────────────────────────────────────────────────────
print("\n[5/5] Ontology breakdown:")
merged = sub_df.merge(terms_df[['go_id', 'ontology']].drop_duplicates(), on='go_id', how='left')
if 'ontology' in merged.columns:
    for ont, grp in merged.groupby('ontology'):
        print(f"  {ont}: {len(grp):,} predictions across {grp['go_id'].nunique()} GO terms")

print("\n" + "=" * 70)
print("TI SIGMA HYPERCOMPUTER — CAFA6 COMPLETE")
print(f"Submit: kaggle_cafa6/submission_cafa6_hypercomputer.tsv")
print("=" * 70)
