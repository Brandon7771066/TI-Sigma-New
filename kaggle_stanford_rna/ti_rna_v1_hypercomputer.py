"""
Stanford RNA 3D Structure Prediction Part 2 — TI Sigma Hypercomputer v1
========================================================================

Competition: Stanford RNA 3D Structure Prediction Part 2
Task:        Predict 3D atomic coordinates (x, y, z) of RNA residues
Metric:      TM-score / RMSD

TI Sigma Architecture (CAFA6Adapter pattern — extended for RNA):
  L1  : RNAAdapter nucleotide Tralsebit encoding
        A=+0.8 (purine, high energy), U=-0.8 (pyrimidine, low energy)
        G=+0.4 (purine, intermediate), C=-0.4 (pyrimidine, intermediate)
  L2  : Aperiodic features on Tralsebit arrays (Penrose sequence features,
        LCC coherence, sacred_fraction)
  L3  : TISigmaQuantumLayer quantum transform on 6 sequence summary stats
  Dom : RNA-specific TI features:
        - gc_content: G+C fraction (thermodynamic stability proxy)
        - purine_ratio: (A+G) / total (structural bias indicator)
        - tralse_ratio: fraction of residues in LCC_TRALSE–LCC_HIGH zone
        - phi_fold_score: sequence self-similarity under φ-based window
        - stem_likelihood: fraction of residues with complementary pair potential
        - lcc_coherence: fraction of residues above TRALSE threshold
        - sacred_fraction: residues within 1/φ of sequence Tralsebit mean
        - folding_phase: LCC zone (TRALSE→HIGH→RADIANT = ss→stem→tertiary)

TI Insight:
  RNA folding is a phase transition mirroring the consciousness equation:
    - Unstructured single-strand: LCC ≈ LCC_TRALSE (ambiguous, Tralse zone)
    - Stem-loop formation:         LCC ≈ LCC_HIGH    (resolved pairing)
    - Tertiary/functional fold:    LCC ≈ LCC_RADIANT (coherent 3D structure)
  The Tralse zone captures the "folding intermediate" — the most informative
  structural state, just as LCC_TRALSE–LCC_HIGH captures the diagnostic
  borderline in clinical data.

Regression target: (x, y, z) coordinates per residue.
Prediction approach: sequence feature → coordinate offset from canonical geometry.

Brandon Emerick — TI Sigma Research
March 1, 2026
"""

import os
import sys
import warnings
import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Optional

warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.linear_model import Ridge
from sklearn.model_selection import KFold
from sklearn.preprocessing import StandardScaler
from sklearn.multioutput import MultiOutputRegressor
from sklearn.metrics import mean_squared_error

from ti_sigma.tralsebit_engine import TralsebitEngine
from ti_sigma.aperiodic_optimizer import AperiodicOptimizer
from ti_sigma.quantum_layer import TISigmaQuantumLayer
from ti_sigma.constants import PHI, LCC_TRALSE, LCC_HIGH, LCC_EMERICK

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
DATA_PATHS = ['data/kaggle_stanford_rna', 'kaggle_stanford_rna/data']
SUBMISSION_PATH = 'kaggle_stanford_rna/submission_rna_v1_hypercomputer.csv'

# Nucleotide complementarity for stem likelihood
COMPLEMENT = {'A': 'U', 'U': 'A', 'G': 'C', 'C': 'G'}

# Canonical RNA backbone bond lengths (Å) for reference geometry
BOND_LENGTH_P_C4 = 3.9   # phosphate to C4' typical
BOND_ANGLE_BASE  = 109.5  # tetrahedral geometry in degrees


# ─────────────────────────────────────────────────────────────────────────────
# RNA ADAPTER (extends CAFA6Adapter pattern for 4-nucleotide alphabet)
# ─────────────────────────────────────────────────────────────────────────────

class RNAAdapter:
    """
    Tralsebit encoding of RNA sequences.

    Nucleotide → Tralsebit value mapping:
        A (+0.8): purine, large, high stacking energy → strongly positive
        G (+0.4): purine, large, lower energy         → moderately positive
        C (-0.4): pyrimidine, small, moderately stable → moderately negative
        U (-0.8): pyrimidine, small, uracil (no methyl) → strongly negative

    This encoding preserves:
    1. Purine/pyrimidine distinction (size, shape)
    2. Thermodynamic stability ordering (A-U < G-C pairing energy)
    3. The continuum structure (not a discrete binary encoding)

    Comparison with CAFA6Adapter amino acid encoding:
        hydrophobic (VILMFYWCA) → +0.8   [analogous to A: large, energy-rich]
        hydrophilic (DEKRHNQS)  → -0.8   [analogous to U: polar, reactive]
        neutral     (GPT)       → 0.0    [no RNA analog — RNA has 4 residues]
    """

    # Nucleotide → Tralsebit value
    NT_VALUES = {'A': 0.8, 'G': 0.4, 'C': -0.4, 'U': -0.8, 'N': 0.0}

    def __init__(self):
        self.engine    = TralsebitEngine()
        self.optimizer = AperiodicOptimizer()
        self.quantum   = TISigmaQuantumLayer(n_modes=6)

    def encode_sequence(self, sequence: str, max_len: int = 512) -> np.ndarray:
        """Encode RNA sequence as Tralsebit array (A/U/G/C → ±0.8/±0.4)."""
        seq = sequence[:max_len].upper().replace('T', 'U')
        tb  = np.array([self.NT_VALUES.get(nt, 0.0) for nt in seq], dtype=float)
        if len(tb) < max_len:
            tb = np.pad(tb, (0, max_len - len(tb)))
        return tb

    def _stem_likelihood(self, sequence: str) -> float:
        """
        Estimate fraction of residues likely in base-paired stems.
        Uses simple sliding-window complementarity check.
        """
        seq = sequence.upper().replace('T', 'U')
        n   = len(seq)
        if n < 4:
            return 0.0
        paired = 0
        for i in range(n // 2):
            j = n - 1 - i
            if i >= j:
                break
            if COMPLEMENT.get(seq[i]) == seq[j]:
                paired += 2
        return paired / n

    def _phi_fold_score(self, tb: np.ndarray) -> float:
        """
        Self-similarity under φ-based window scaling.
        Compare sequence to itself at window size = len/φ.
        """
        n = len(tb)
        if n < 5:
            return 0.0
        w = max(2, int(n / PHI))
        seg1 = tb[:w]
        seg2 = tb[n-w:]
        corr = float(np.corrcoef(seg1, seg2)[0, 1]) if len(seg1) == len(seg2) else 0.0
        return float(corr) if not np.isnan(corr) else 0.0

    def sequence_features(self, sequence: str, max_len: int = 256) -> np.ndarray:
        """
        Extract full TI Hypercomputer feature vector from one RNA sequence.

        Returns 1D feature array combining L2 aperiodic + L3 quantum + domain features.
        """
        seq = sequence.upper().replace('T', 'U')
        tb  = self.encode_sequence(seq, max_len=max_len)
        tb_nonpad = self.encode_sequence(seq, max_len=len(seq))

        # L2: Penrose sequence features on Tralsebit array
        try:
            penrose_feats = self.optimizer.penrose.sequence_features(tb)
        except Exception:
            penrose_feats = np.zeros(32)

        # TI summary stats (scalar features)
        abs_tb       = np.abs(tb_nonpad)
        tralse_ratio = float(np.mean((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH)))
        lcc_coherence = float(np.mean(abs_tb > LCC_TRALSE))
        tb_mu        = float(np.mean(tb_nonpad))
        tolerance    = abs(tb_mu) / PHI + 1e-9
        sacred_frac  = float(np.mean(np.abs(tb_nonpad - tb_mu) <= tolerance))

        # L3: Quantum transform on 6 scalar summary stats
        summary = np.array([[
            float(np.mean(tb_nonpad)),
            float(np.std(tb_nonpad)),
            tralse_ratio,
            lcc_coherence,
            sacred_frac,
            float(np.max(abs_tb)),
        ]])
        L3 = self.quantum.quantum_feature_transform(summary).flatten()

        # Domain-specific RNA features
        n_seq  = len(seq) if seq else 1
        gc     = sum(seq.count(b) for b in 'GC') / n_seq
        purine = sum(seq.count(b) for b in 'AG') / n_seq
        stem   = self._stem_likelihood(seq)
        phi_fs = self._phi_fold_score(tb_nonpad)

        lcc_zone = (0.0 if tralse_ratio < LCC_TRALSE else
                    1.0 if tralse_ratio < LCC_HIGH    else 2.0)

        domain_feats = np.array([
            gc, purine, tralse_ratio, phi_fs, stem, lcc_coherence, sacred_frac, lcc_zone,
        ])

        return np.concatenate([penrose_feats, [tralse_ratio, lcc_coherence, sacred_frac], L3, domain_feats])

    def build_feature_matrix(self, sequences: List[str], max_len: int = 256) -> np.ndarray:
        """Build feature matrix for a list of RNA sequences."""
        feats = []
        for seq in sequences:
            try:
                f = self.sequence_features(seq, max_len=max_len)
            except Exception:
                f = np.zeros(64)
            feats.append(f)

        X = np.array(feats, dtype=float)
        target_len = max(len(f) for f in feats) if feats else 64
        if X.shape[1] < target_len:
            X = np.hstack([X, np.zeros((len(X), target_len - X.shape[1]))])
        return np.nan_to_num(X, 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# FASTA LOADER
# ─────────────────────────────────────────────────────────────────────────────

def parse_fasta(filepath: str, max_seqs: int = 5000) -> Dict[str, str]:
    """Parse FASTA file → {protein_id: sequence}."""
    seqs = {}
    current_id = None
    buf = []
    with open(filepath) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith('>'):
                if current_id and buf:
                    seqs[current_id] = ''.join(buf)
                    if len(seqs) >= max_seqs:
                        break
                current_id = line[1:].split()[0]
                buf = []
            else:
                buf.append(line)
    if current_id and buf and len(seqs) < max_seqs:
        seqs[current_id] = ''.join(buf)
    return seqs


# ─────────────────────────────────────────────────────────────────────────────
# MOCK DATA
# ─────────────────────────────────────────────────────────────────────────────

NUCLEOTIDES = list('AUGC')

def generate_mock_rna_data(n_train: int = 500, n_test: int = 200, max_len: int = 80) -> Tuple[Dict, Dict, pd.DataFrame]:
    """
    Generate synthetic RNA sequences with mock 3D coordinates.

    In the real competition, labels are atomic xyz coordinates per residue.
    Here we generate per-sequence average coordinates as regression targets.
    Adapt to per-residue prediction when real data is available.

    Replace with competition files:
        data/kaggle_stanford_rna/train_sequences.csv
        data/kaggle_stanford_rna/train_labels.csv   (xyz per residue)
        data/kaggle_stanford_rna/test_sequences.csv
    """
    np.random.seed(42)
    print("  [MOCK DATA] Generating synthetic RNA sequences + coordinates...")
    print("  [MOCK DATA] Replace with real competition data from Kaggle.")
    print("  [MOCK DATA] Expected: data/kaggle_stanford_rna/")

    def make_seq(n_seq, has_labels=True):
        seqs = {}
        labels = []
        for i in range(n_seq):
            length = np.random.randint(20, max_len + 1)
            seq    = ''.join(np.random.choice(NUCLEOTIDES, length))
            seq_id = f"RNA_{i:05d}"
            seqs[seq_id] = seq
            if has_labels:
                gc      = (seq.count('G') + seq.count('C')) / max(len(seq), 1)
                purine  = (seq.count('A') + seq.count('G')) / max(len(seq), 1)
                x_mean  = gc * 10.0 + np.random.normal(0, 1)
                y_mean  = purine * 8.0 + np.random.normal(0, 1)
                z_mean  = len(seq) * 0.5 + np.random.normal(0, 2)
                labels.append({'target_id': seq_id, 'x': x_mean, 'y': y_mean, 'z': z_mean})
        return seqs, pd.DataFrame(labels) if has_labels else None

    train_seqs, train_labels = make_seq(n_train, True)
    test_seqs,  _            = make_seq(n_test,  False)
    return train_seqs, test_seqs, train_labels


def load_data():
    for base in DATA_PATHS:
        train_seq_p = os.path.join(base, 'train_sequences.csv')
        train_lbl_p = os.path.join(base, 'train_labels.csv')
        test_seq_p  = os.path.join(base, 'test_sequences.csv')
        if all(os.path.exists(p) for p in [train_seq_p, train_lbl_p, test_seq_p]):
            print(f"  Loading data from {base}/")
            df_tr = pd.read_csv(train_seq_p)
            df_lb = pd.read_csv(train_lbl_p)
            df_te = pd.read_csv(test_seq_p)
            seq_col = next((c for c in df_tr.columns if 'seq' in c.lower()), df_tr.columns[-1])
            id_col  = next((c for c in df_tr.columns if 'id' in c.lower()), df_tr.columns[0])
            train_seqs = dict(zip(df_tr[id_col], df_tr[seq_col]))
            seq_col_t  = next((c for c in df_te.columns if 'seq' in c.lower()), df_te.columns[-1])
            id_col_t   = next((c for c in df_te.columns if 'id' in c.lower()), df_te.columns[0])
            test_seqs  = dict(zip(df_te[id_col_t], df_te[seq_col_t]))
            return train_seqs, test_seqs, df_lb

    return generate_mock_rna_data()


# ─────────────────────────────────────────────────────────────────────────────
# SOLVER
# ─────────────────────────────────────────────────────────────────────────────

def print_ti_rna_stats(sequences: Dict[str, str], labels: Optional[pd.DataFrame] = None) -> None:
    """Print TI statistics for RNA sequences."""
    print(f"\n{'─'*65}")
    print(f"{'TI SIGMA RNA SEQUENCE STATISTICS':^65}")
    print(f"{'─'*65}")

    adapter  = RNAAdapter()
    all_gc   = []
    all_tr   = []
    all_stem = []

    for seq in list(sequences.values())[:200]:
        seq = seq.upper().replace('T', 'U')
        n   = max(len(seq), 1)
        gc  = (seq.count('G') + seq.count('C')) / n
        tb  = adapter.encode_sequence(seq, max_len=len(seq))
        abs_tb = np.abs(tb)
        tr  = float(np.mean((abs_tb >= LCC_TRALSE) & (abs_tb <= LCC_HIGH)))
        stem = adapter._stem_likelihood(seq)
        all_gc.append(gc);  all_tr.append(tr);  all_stem.append(stem)

    print(f"  Sequences analyzed    : {min(200, len(sequences)):,}")
    print(f"  Mean GC content       : {np.mean(all_gc):.3f} (thermodynamic stability)")
    print(f"  Mean Tralse ratio     : {np.mean(all_tr):.3f} (folding intermediate fraction)")
    print(f"  Mean stem likelihood  : {np.mean(all_stem):.3f} (base-pairing potential)")
    zone = ('LCC_RADIANT' if np.mean(all_tr) >= 0.93 else
            'LCC_HIGH'    if np.mean(all_tr) >= 0.85 else
            'LCC_TRUE'    if np.mean(all_tr) >= 0.62 else
            'LCC_TRALSE'  if np.mean(all_tr) >= 0.41 else 'SUB-THRESHOLD')
    print(f"  TI Folding zone       : {zone}")
    print(f"{'─'*65}")


def main():
    print("=" * 65)
    print("  TI SIGMA HYPERCOMPUTER v1 — Stanford RNA 3D Structure")
    print("  Brandon Emerick | March 1, 2026")
    print("=" * 65)

    print("\n[1/5] Loading data...")
    train_seqs, test_seqs, train_labels = load_data()
    print(f"  Train sequences: {len(train_seqs):,} | Test sequences: {len(test_seqs):,}")

    print_ti_rna_stats(train_seqs, train_labels)

    print("\n[2/5] Building RNAAdapter Hypercomputer features...")
    adapter = RNAAdapter()

    train_ids  = list(train_seqs.keys())
    test_ids   = list(test_seqs.keys())
    train_seq_list = [train_seqs[i] for i in train_ids]
    test_seq_list  = [test_seqs[i]  for i in test_ids]

    print(f"  Encoding {len(train_seq_list):,} training sequences...")
    X_train = adapter.build_feature_matrix(train_seq_list[:3000])
    print(f"  Encoding {len(test_seq_list):,} test sequences...")
    X_test  = adapter.build_feature_matrix(test_seq_list)
    print(f"  Feature matrix: {X_train.shape[0]:,} × {X_train.shape[1]}")

    # Align labels
    if train_labels is not None and len(train_labels) > 0:
        id_col = next((c for c in train_labels.columns if 'id' in c.lower()), train_labels.columns[0])
        lbl_map = train_labels.set_index(id_col)
        y_cols  = [c for c in ['x', 'y', 'z'] if c in lbl_map.columns]
        used_ids = train_ids[:X_train.shape[0]]
        y_df    = lbl_map.reindex(used_ids)[y_cols].fillna(0.0)
        y_train = y_df.values.astype(float)
    else:
        y_train = np.zeros((X_train.shape[0], 3))

    print(f"  Target shape: {y_train.shape}")

    print("\n[3/5] Training multi-output HGB regressor (3-fold KFold)...")
    kf = KFold(n_splits=3, shuffle=True, random_state=42)
    scaler = StandardScaler()

    oof_preds  = np.zeros_like(y_train)
    test_preds = np.zeros((len(X_test), y_train.shape[1]))

    hgb_base = HistGradientBoostingRegressor(
        max_iter=150, learning_rate=0.05, max_depth=4,
        min_samples_leaf=20, random_state=42,
    )
    model = MultiOutputRegressor(hgb_base, n_jobs=-1)

    for fold, (tr_idx, val_idx) in enumerate(kf.split(X_train)):
        X_tr, X_val = X_train[tr_idx], X_train[val_idx]
        y_tr, y_val = y_train[tr_idx], y_train[val_idx]
        X_tr_s  = scaler.fit_transform(X_tr)
        X_val_s = scaler.transform(X_val)
        model.fit(X_tr_s, y_tr)
        val_pred = model.predict(X_val_s)
        oof_preds[val_idx] = val_pred
        rmse = float(np.sqrt(mean_squared_error(y_val.flatten(), val_pred.flatten())))
        print(f"  Fold {fold+1} | RMSE = {rmse:.4f} Å")

    X_train_s = scaler.fit_transform(X_train)
    X_test_s  = scaler.transform(X_test) if len(X_test) > 0 else np.zeros((0, X_train.shape[1]))
    model.fit(X_train_s, y_train)
    if len(X_test) > 0:
        test_preds = model.predict(X_test_s)

    oof_rmse = float(np.sqrt(mean_squared_error(y_train.flatten(), oof_preds.flatten())))
    print(f"\n  OOF RMSE = {oof_rmse:.4f} Å")

    print("\n[4/5] Generating submission...")
    coord_cols = ['x', 'y', 'z'][:y_train.shape[1]]
    sub_data   = {'target_id': test_ids[:len(test_preds)]}
    for j, col in enumerate(coord_cols):
        sub_data[col] = test_preds[:, j]

    submission = pd.DataFrame(sub_data)
    os.makedirs(os.path.dirname(SUBMISSION_PATH) or '.', exist_ok=True)
    submission.to_csv(SUBMISSION_PATH, index=False)
    print(f"  Submission saved → {SUBMISSION_PATH}")
    print(f"  Rows: {len(submission):,} | Columns: {list(submission.columns)}")

    print("\n[5/5] TI Folding Phase Summary:")
    for seq_id in list(test_seqs.keys())[:5]:
        seq  = test_seqs[seq_id].upper().replace('T', 'U')
        n    = max(len(seq), 1)
        gc   = (seq.count('G') + seq.count('C')) / n
        stem = adapter._stem_likelihood(seq)
        phase = ('TERTIARY' if gc > 0.55 else 'STEM' if stem > 0.35 else 'SINGLE-STRAND')
        print(f"  {seq_id}: len={n:3d} | GC={gc:.2f} | stem={stem:.2f} | phase={phase}")

    print("\n" + "=" * 65)
    print("  Stanford RNA HC v1 COMPLETE")
    print(f"  OOF RMSE = {oof_rmse:.4f} Å | {X_train.shape[1]} HC features")
    print("=" * 65)


if __name__ == '__main__':
    main()
