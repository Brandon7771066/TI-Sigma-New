"""
RNA 3D FOLDING ENGINE
========================
Stanford RNA 3D Folding Part 2 Kaggle Competition Engine
Competition: Predict 3D atomic coordinates of RNA molecules from sequence
Deadline: March 25, 2026 | Prize: $75,000

Implements RNA structure prediction using:
- Nussinov algorithm for secondary structure prediction
- Physics-based 3D coordinate generation
- TM-score and RMSD evaluation metrics
- TI Framework (GILE) structural analysis
- Tralse confidence scoring

Uses only numpy, json, typing, dataclasses, math, random.
No external bioinformatics libraries required.
"""

import json
import math
import random
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field


BASE_PAIRS = {
    ('A', 'U'), ('U', 'A'),
    ('G', 'C'), ('C', 'G'),
    ('G', 'U'), ('U', 'G'),
}

BASE_INDEX = {'A': 0, 'C': 1, 'G': 2, 'U': 3}

BOND_LENGTH_PO = 1.6
BOND_LENGTH_OC = 1.4
BACKBONE_STEP = 3.4
BASE_PAIR_DISTANCE = 8.0
MIN_LOOP_LENGTH = 3

PAIR_ENERGIES = {
    ('G', 'C'): -3.0, ('C', 'G'): -3.0,
    ('A', 'U'): -2.0, ('U', 'A'): -2.0,
    ('G', 'U'): -1.0, ('U', 'G'): -1.0,
}

COMMON_RNA_MOTIFS = [
    "GCGCAAGCGC",
    "GGCUAGCC",
    "GGGAAACCC",
    "CCCCGAUAGGGG",
    "GCAUCGAUGC",
]


@dataclass
class NussinovResult:
    sequence: str
    dp_matrix: np.ndarray
    pairs: List[Tuple[int, int]]
    bracket_notation: str
    num_pairs: int
    free_energy_estimate: float


@dataclass
class PredictionResult:
    sequence: str
    coordinates: np.ndarray
    secondary_structure: NussinovResult
    tm_score: float = 0.0
    rmsd: float = 0.0
    confidence: float = 0.0
    gile_scores: Dict = field(default_factory=dict)


class RNA3DFoldingEngine:
    """
    RNA 3D structure prediction engine for the Stanford RNA 3D Folding
    Kaggle competition. Integrates Nussinov secondary structure prediction,
    physics-based coordinate generation, and TI Framework analysis.
    """

    def __init__(self, seed: int = 42):
        self.rng = np.random.RandomState(seed)
        self.random_gen = random.Random(seed)
        self.prediction_cache = {}
        self.model_version = "1.0.0"
        self.competition_name = "Stanford RNA 3D Folding Part 2"

    def encode_sequence(self, sequence: str) -> np.ndarray:
        seq = sequence.upper().replace('T', 'U')
        n = len(seq)
        encoding = np.zeros((n, 4), dtype=np.float32)
        for i, base in enumerate(seq):
            idx = BASE_INDEX.get(base, -1)
            if idx >= 0:
                encoding[i, idx] = 1.0
            else:
                encoding[i] = 0.25
        return encoding

    def compute_secondary_structure(self, sequence: str) -> dict:
        seq = sequence.upper().replace('T', 'U')
        result = self._nussinov_algorithm(seq)
        return {
            'sequence': seq,
            'bracket_notation': result.bracket_notation,
            'pairs': result.pairs,
            'num_pairs': result.num_pairs,
            'free_energy_estimate': result.free_energy_estimate,
            'pair_ratio': result.num_pairs / max(1, len(seq) // 2),
        }

    def _nussinov_algorithm(self, seq: str) -> NussinovResult:
        n = len(seq)
        dp = np.zeros((n, n), dtype=np.int32)

        for span in range(MIN_LOOP_LENGTH + 1, n):
            for i in range(n - span):
                j = i + span
                dp[i][j] = dp[i + 1][j]
                dp[i][j] = max(dp[i][j], dp[i][j - 1])
                if (seq[i], seq[j]) in BASE_PAIRS and j - i > MIN_LOOP_LENGTH:
                    dp[i][j] = max(dp[i][j], dp[i + 1][j - 1] + 1)
                for k in range(i + 1, j):
                    dp[i][j] = max(dp[i][j], dp[i][k] + dp[k + 1][j])

        pairs = []
        self._nussinov_traceback(dp, seq, 0, n - 1, pairs)
        pairs.sort()

        bracket = ['.'] * n
        for i, j in pairs:
            bracket[i] = '('
            bracket[j] = ')'
        bracket_str = ''.join(bracket)

        energy = sum(PAIR_ENERGIES.get((seq[i], seq[j]), -0.5) for i, j in pairs)

        return NussinovResult(
            sequence=seq,
            dp_matrix=dp,
            pairs=pairs,
            bracket_notation=bracket_str,
            num_pairs=len(pairs),
            free_energy_estimate=energy,
        )

    def _nussinov_traceback(self, dp: np.ndarray, seq: str,
                            i: int, j: int, pairs: List[Tuple[int, int]]):
        if i >= j:
            return

        if dp[i][j] == dp[i + 1][j]:
            self._nussinov_traceback(dp, seq, i + 1, j, pairs)
        elif dp[i][j] == dp[i][j - 1]:
            self._nussinov_traceback(dp, seq, i, j - 1, pairs)
        elif (seq[i], seq[j]) in BASE_PAIRS and j - i > MIN_LOOP_LENGTH and \
                dp[i][j] == dp[i + 1][j - 1] + 1:
            pairs.append((i, j))
            self._nussinov_traceback(dp, seq, i + 1, j - 1, pairs)
        else:
            for k in range(i + 1, j):
                if dp[i][j] == dp[i][k] + dp[k + 1][j]:
                    self._nussinov_traceback(dp, seq, i, k, pairs)
                    self._nussinov_traceback(dp, seq, k + 1, j, pairs)
                    break

    def predict_distance_matrix(self, sequence: str) -> np.ndarray:
        seq = sequence.upper().replace('T', 'U')
        n = len(seq)
        ss = self._nussinov_algorithm(seq)

        dist = np.zeros((n, n), dtype=np.float64)
        for i in range(n):
            for j in range(n):
                seq_dist = abs(i - j) * BACKBONE_STEP
                dist[i][j] = seq_dist

        pair_set = set()
        for pi, pj in ss.pairs:
            pair_set.add((pi, pj))
            pair_set.add((pj, pi))

        for pi, pj in ss.pairs:
            dist[pi][pj] = BASE_PAIR_DISTANCE
            dist[pj][pi] = BASE_PAIR_DISTANCE

            for di in range(-2, 3):
                for dj in range(-2, 3):
                    ni, nj = pi + di, pj + dj
                    if 0 <= ni < n and 0 <= nj < n and ni != nj:
                        stacked_dist = BASE_PAIR_DISTANCE + abs(di + dj) * 1.5
                        dist[ni][nj] = min(dist[ni][nj], stacked_dist)
                        dist[nj][ni] = dist[ni][nj]

        return dist

    def generate_3d_coordinates(self, sequence: str,
                                n_predictions: int = 5) -> List[np.ndarray]:
        seq = sequence.upper().replace('T', 'U')
        n = len(seq)
        ss = self._nussinov_algorithm(seq)
        predictions = []

        for pred_idx in range(n_predictions):
            coords = self._build_backbone(n, pred_idx)
            coords = self._apply_base_pair_constraints(coords, ss.pairs, n)
            coords = self._energy_minimize(coords, ss.pairs, n)
            coords = self._center_coordinates(coords)
            predictions.append(coords)

        return predictions

    def _build_backbone(self, n: int, seed_offset: int = 0) -> np.ndarray:
        coords = np.zeros((n, 3), dtype=np.float64)
        rng = np.random.RandomState(self.rng.randint(0, 100000) + seed_offset)

        theta = 0.0
        phi = 0.0
        pos = np.array([0.0, 0.0, 0.0])

        for i in range(n):
            coords[i] = pos.copy()

            theta += rng.uniform(-0.3, 0.3) + 0.15
            phi += rng.uniform(-0.2, 0.2)

            dx = BACKBONE_STEP * math.cos(theta) * math.cos(phi)
            dy = BACKBONE_STEP * math.sin(theta) * math.cos(phi)
            dz = BACKBONE_STEP * math.sin(phi)

            helical_t = i * 2 * math.pi / 11.0
            dx += 0.5 * math.cos(helical_t)
            dy += 0.5 * math.sin(helical_t)

            pos = pos + np.array([dx, dy, dz])

        return coords

    def _apply_base_pair_constraints(self, coords: np.ndarray,
                                      pairs: List[Tuple[int, int]],
                                      n: int) -> np.ndarray:
        for iteration in range(50):
            for pi, pj in pairs:
                vec = coords[pj] - coords[pi]
                current_dist = np.linalg.norm(vec)
                if current_dist < 1e-8:
                    vec = self.rng.randn(3)
                    current_dist = np.linalg.norm(vec)

                target = BASE_PAIR_DISTANCE
                error = current_dist - target
                correction = vec / current_dist * error * 0.3

                coords[pi] += correction
                coords[pj] -= correction

            for i in range(n - 1):
                vec = coords[i + 1] - coords[i]
                current_dist = np.linalg.norm(vec)
                if current_dist < 1e-8:
                    continue
                target = BACKBONE_STEP
                error = current_dist - target
                correction = vec / current_dist * error * 0.2
                coords[i] += correction
                coords[i + 1] -= correction

        return coords

    def _energy_minimize(self, coords: np.ndarray,
                          pairs: List[Tuple[int, int]],
                          n: int, steps: int = 100,
                          lr: float = 0.01) -> np.ndarray:
        pair_set = {(pi, pj) for pi, pj in pairs}

        for step in range(steps):
            forces = np.zeros_like(coords)

            for i in range(n - 1):
                vec = coords[i + 1] - coords[i]
                dist = np.linalg.norm(vec)
                if dist < 1e-8:
                    continue
                force_mag = 2.0 * (dist - BACKBONE_STEP)
                force_dir = vec / dist
                forces[i] += force_mag * force_dir
                forces[i + 1] -= force_mag * force_dir

            for pi, pj in pairs:
                vec = coords[pj] - coords[pi]
                dist = np.linalg.norm(vec)
                if dist < 1e-8:
                    continue
                force_mag = 1.5 * (dist - BASE_PAIR_DISTANCE)
                force_dir = vec / dist
                forces[pi] += force_mag * force_dir
                forces[pj] -= force_mag * force_dir

            for i in range(n):
                for j in range(i + 2, min(i + 6, n)):
                    if (i, j) in pair_set or (j, i) in pair_set:
                        continue
                    vec = coords[j] - coords[i]
                    dist = np.linalg.norm(vec)
                    if dist < 3.0 and dist > 1e-8:
                        repulsion = 0.5 * (3.0 - dist)
                        force_dir = vec / dist
                        forces[i] -= repulsion * force_dir
                        forces[j] += repulsion * force_dir

            current_lr = lr * (1.0 - step / steps)
            coords -= current_lr * forces

        return coords

    def _center_coordinates(self, coords: np.ndarray) -> np.ndarray:
        centroid = np.mean(coords, axis=0)
        return coords - centroid

    def compute_tm_score(self, predicted: np.ndarray,
                          reference: np.ndarray) -> float:
        n = len(predicted)
        if n != len(reference):
            n = min(len(predicted), len(reference))
            predicted = predicted[:n]
            reference = reference[:n]

        if n == 0:
            return 0.0

        d0 = 1.24 * (max(n, 15) - 15) ** (1.0 / 3.0) - 1.8
        d0 = max(d0, 0.5)

        pred_centered = predicted - np.mean(predicted, axis=0)
        ref_centered = reference - np.mean(reference, axis=0)

        rotation = self._kabsch_rotation(pred_centered, ref_centered)
        aligned = pred_centered @ rotation

        distances = np.sqrt(np.sum((aligned - ref_centered) ** 2, axis=1))

        tm_sum = np.sum(1.0 / (1.0 + (distances / d0) ** 2))
        tm_score = tm_sum / n

        return float(min(1.0, max(0.0, tm_score)))

    def _kabsch_rotation(self, P: np.ndarray, Q: np.ndarray) -> np.ndarray:
        H = P.T @ Q
        try:
            U, S, Vt = np.linalg.svd(H)
            d = np.linalg.det(Vt.T @ U.T)
            sign_matrix = np.diag([1.0, 1.0, np.sign(d)])
            rotation = U @ sign_matrix @ Vt
        except np.linalg.LinAlgError:
            rotation = np.eye(3)
        return rotation

    def compute_rmsd(self, predicted: np.ndarray,
                      reference: np.ndarray) -> float:
        n = len(predicted)
        if n != len(reference):
            n = min(len(predicted), len(reference))
            predicted = predicted[:n]
            reference = reference[:n]

        if n == 0:
            return float('inf')

        pred_centered = predicted - np.mean(predicted, axis=0)
        ref_centered = reference - np.mean(reference, axis=0)

        rotation = self._kabsch_rotation(pred_centered, ref_centered)
        aligned = pred_centered @ rotation

        diff = aligned - ref_centered
        rmsd = float(np.sqrt(np.mean(np.sum(diff ** 2, axis=1))))
        return rmsd

    def apply_tralse_confidence(self, predictions: List[np.ndarray],
                                 scores: List[float]) -> List[dict]:
        if not predictions or not scores:
            return []

        results = []
        max_score = max(scores) if scores else 1.0
        min_score = min(scores) if scores else 0.0
        score_range = max_score - min_score if max_score > min_score else 1.0

        for i, (pred, score) in enumerate(zip(predictions, scores)):
            n = len(pred)

            backbone_dists = np.sqrt(np.sum(np.diff(pred, axis=0) ** 2, axis=1))
            backbone_consistency = 1.0 - min(1.0, float(np.std(backbone_dists)) / BACKBONE_STEP)

            min_dists = []
            for j in range(n):
                dists = np.sqrt(np.sum((pred - pred[j]) ** 2, axis=1))
                dists[j] = float('inf')
                if j > 0:
                    dists[j - 1] = float('inf')
                if j < n - 1:
                    dists[j + 1] = float('inf')
                min_dists.append(float(np.min(dists)) if len(dists) > 2 else 5.0)
            steric_ok = sum(1 for d in min_dists if d > 2.5) / max(1, len(min_dists))

            normalized_score = (score - min_score) / score_range

            tralse_true = backbone_consistency * 0.3 + steric_ok * 0.3 + normalized_score * 0.4
            tralse_false = 1.0 - tralse_true
            tralse_uncertainty = 1.0 - abs(tralse_true - tralse_false)

            confidence = tralse_true * (1.0 - 0.5 * tralse_uncertainty)

            results.append({
                'prediction_index': i,
                'confidence': round(float(confidence), 4),
                'tralse_true': round(float(tralse_true), 4),
                'tralse_false': round(float(tralse_false), 4),
                'tralse_uncertainty': round(float(tralse_uncertainty), 4),
                'backbone_consistency': round(float(backbone_consistency), 4),
                'steric_validity': round(float(steric_ok), 4),
                'normalized_score': round(float(normalized_score), 4),
                'classification': (
                    'high_confidence' if confidence > 0.7 else
                    'moderate_confidence' if confidence > 0.4 else
                    'low_confidence'
                ),
            })

        return results

    def generate_sample_rna_data(self, n_sequences: int = 10) -> List[dict]:
        samples = []
        motif_templates = [
            ("GCGCAAGCGC", "Stem-loop"),
            ("GGCUAGCC", "Simple hairpin"),
            ("GGGAAACCC", "Hairpin with AAA loop"),
            ("CCCCGAUAGGGG", "Long stem"),
            ("GCAUCGAUGC", "Mixed stem"),
            ("GGUUCCAAGGAACC", "Internal loop"),
            ("GGCCCGAAAGGGCC", "Bulge structure"),
            ("AACGUUGGCAACGU", "Palindromic"),
            ("GCGCGCGCGC", "Alternating GC"),
            ("AAAUUUAAAUUU", "AU-rich hairpin"),
            ("GCAUUUAUGC", "Short stem-loop"),
            ("GGGCCCGGGCCC", "Two stems"),
            ("GGAACCGGAAUUCC", "Pseudoknot potential"),
            ("CCGAUAUCGG", "Symmetric stem"),
            ("GCGAAAGCGAAAGCG", "Multi-loop candidate"),
        ]

        for i in range(n_sequences):
            template_idx = i % len(motif_templates)
            base_seq, motif_type = motif_templates[template_idx]

            if i >= len(motif_templates):
                length = self.random_gen.randint(8, 30)
                base_seq = ''.join(self.random_gen.choices('ACGU', k=length))
                motif_type = "Random"

            ss = self.compute_secondary_structure(base_seq)
            coords_list = self.generate_3d_coordinates(base_seq, n_predictions=1)
            coords = coords_list[0] if coords_list else np.zeros((len(base_seq), 3))

            features = self.analyze_sequence_features(base_seq)

            samples.append({
                'id': f"sample_{i:04d}",
                'sequence': base_seq,
                'length': len(base_seq),
                'motif_type': motif_type,
                'secondary_structure': ss['bracket_notation'],
                'num_pairs': ss['num_pairs'],
                'free_energy': ss['free_energy_estimate'],
                'reference_coordinates': coords.tolist(),
                'gc_content': features['gc_content'],
                'features': features,
            })

        return samples

    def analyze_sequence_features(self, sequence: str) -> dict:
        seq = sequence.upper().replace('T', 'U')
        n = len(seq)

        counts = {'A': 0, 'C': 0, 'G': 0, 'U': 0}
        for base in seq:
            if base in counts:
                counts[base] += 1

        gc_content = (counts['G'] + counts['C']) / max(1, n)
        au_content = (counts['A'] + counts['U']) / max(1, n)

        ss = self.compute_secondary_structure(seq)
        bracket = ss['bracket_notation']

        stem_loops = 0
        i = 0
        while i < len(bracket) - 3:
            if bracket[i] == '(' and i + 3 < len(bracket):
                j = i + 1
                while j < len(bracket) and bracket[j] == '.':
                    j += 1
                if j < len(bracket) and bracket[j] == ')' and j - i - 1 >= 3:
                    stem_loops += 1
            i += 1

        pseudoknot_potential = 0.0
        pairs = ss['pairs']
        for idx_a in range(len(pairs)):
            for idx_b in range(idx_a + 1, len(pairs)):
                i1, j1 = pairs[idx_a]
                i2, j2 = pairs[idx_b]
                if i1 < i2 < j1 < j2:
                    pseudoknot_potential += 1.0

        dinucleotides = {}
        for i in range(n - 1):
            di = seq[i:i + 2]
            dinucleotides[di] = dinucleotides.get(di, 0) + 1

        purine_runs = 0
        max_purine_run = 0
        current_run = 0
        for base in seq:
            if base in ('A', 'G'):
                current_run += 1
                max_purine_run = max(max_purine_run, current_run)
            else:
                if current_run >= 3:
                    purine_runs += 1
                current_run = 0

        return {
            'length': n,
            'base_composition': counts,
            'gc_content': round(gc_content, 4),
            'au_content': round(au_content, 4),
            'stem_loops_detected': stem_loops,
            'pseudoknot_potential': pseudoknot_potential,
            'num_base_pairs': ss['num_pairs'],
            'pair_density': round(ss['num_pairs'] / max(1, n // 2), 4),
            'free_energy_estimate': ss['free_energy_estimate'],
            'secondary_structure': ss['bracket_notation'],
            'dinucleotide_frequencies': dinucleotides,
            'purine_rich_regions': purine_runs,
            'max_purine_run': max_purine_run,
            'sequence_complexity': round(self._sequence_complexity(seq), 4),
        }

    def _sequence_complexity(self, seq: str) -> float:
        n = len(seq)
        if n == 0:
            return 0.0
        counts = {}
        for base in seq:
            counts[base] = counts.get(base, 0) + 1
        entropy = 0.0
        for c in counts.values():
            p = c / n
            if p > 0:
                entropy -= p * math.log2(p)
        return entropy / 2.0

    def gile_structural_analysis(self, sequence: str,
                                  predicted_coords: np.ndarray) -> dict:
        seq = sequence.upper().replace('T', 'U')
        n = len(seq)
        ss = self._nussinov_algorithm(seq)

        g_score = self._compute_stability_score(ss, seq)

        features = self.analyze_sequence_features(seq)
        info_content = features['sequence_complexity']
        pair_density = features['pair_density']
        i_score = min(1.0, (info_content * 0.5 + pair_density * 0.5))

        l_score = self._compute_functional_potential(seq, ss)

        e_score = self._compute_physical_validity(predicted_coords, ss.pairs)

        gile_composite = (g_score * 0.3 + i_score * 0.25 +
                          l_score * 0.2 + e_score * 0.25)

        tralse_true = gile_composite
        tralse_false = 1.0 - gile_composite
        tralse_uncertainty = 1.0 - abs(tralse_true - tralse_false)

        fractal_dim = self._fractal_dimension_estimate(predicted_coords)

        return {
            'G': round(float(g_score), 4),
            'I': round(float(i_score), 4),
            'L': round(float(l_score), 4),
            'E': round(float(e_score), 4),
            'gile_composite': round(float(gile_composite), 4),
            'tralse_true': round(float(tralse_true), 4),
            'tralse_false': round(float(tralse_false), 4),
            'tralse_uncertainty': round(float(tralse_uncertainty), 4),
            'fractal_dimension': round(float(fractal_dim), 4),
            'analysis': {
                'stability': {
                    'free_energy': ss.free_energy_estimate,
                    'num_pairs': ss.num_pairs,
                    'score': round(float(g_score), 4),
                },
                'information': {
                    'complexity': round(float(info_content), 4),
                    'pair_density': round(float(pair_density), 4),
                    'score': round(float(i_score), 4),
                },
                'functional': {
                    'binding_potential': round(float(l_score), 4),
                    'catalytic_regions': self._find_catalytic_motifs(seq),
                },
                'physical': {
                    'bond_validity': round(float(e_score), 4),
                    'steric_clashes': self._count_steric_clashes(predicted_coords),
                    'fractal_dimension': round(float(fractal_dim), 4),
                },
            },
        }

    def _compute_stability_score(self, ss: NussinovResult, seq: str) -> float:
        n = len(seq)
        if n == 0:
            return 0.0
        max_pairs = n // 2
        pair_fraction = ss.num_pairs / max(1, max_pairs)
        energy_norm = min(1.0, abs(ss.free_energy_estimate) / max(1, n))
        return min(1.0, pair_fraction * 0.6 + energy_norm * 0.4)

    def _compute_functional_potential(self, seq: str,
                                       ss: NussinovResult) -> float:
        score = 0.0
        catalytic_motifs = self._find_catalytic_motifs(seq)
        score += min(0.4, len(catalytic_motifs) * 0.1)

        bracket = ss.bracket_notation
        loop_count = bracket.count('.(')  + bracket.count(').')
        score += min(0.3, loop_count * 0.05)

        gc = sum(1 for b in seq if b in ('G', 'C')) / max(1, len(seq))
        if 0.4 <= gc <= 0.6:
            score += 0.2
        else:
            score += 0.1

        score += min(0.1, ss.num_pairs * 0.01)

        return min(1.0, score)

    def _find_catalytic_motifs(self, seq: str) -> List[str]:
        motifs_found = []
        known_motifs = {
            'GAAA': 'GNRA tetraloop',
            'GCAA': 'GNRA tetraloop',
            'GUAA': 'GNRA tetraloop',
            'UUCG': 'UNCG tetraloop',
            'UGCG': 'UNCG tetraloop',
            'CUUG': 'CUUG tetraloop',
        }
        for motif, name in known_motifs.items():
            if motif in seq:
                motifs_found.append(name)
        return motifs_found

    def _compute_physical_validity(self, coords: np.ndarray,
                                    pairs: List[Tuple[int, int]]) -> float:
        n = len(coords)
        if n < 2:
            return 0.0

        backbone_dists = np.sqrt(np.sum(np.diff(coords, axis=0) ** 2, axis=1))
        backbone_errors = np.abs(backbone_dists - BACKBONE_STEP)
        backbone_score = 1.0 - min(1.0, float(np.mean(backbone_errors)) / BACKBONE_STEP)

        pair_score = 1.0
        if pairs:
            pair_errors = []
            for pi, pj in pairs:
                if pi < n and pj < n:
                    dist = float(np.linalg.norm(coords[pi] - coords[pj]))
                    pair_errors.append(abs(dist - BASE_PAIR_DISTANCE))
            if pair_errors:
                pair_score = 1.0 - min(1.0, np.mean(pair_errors) / BASE_PAIR_DISTANCE)

        clash_count = self._count_steric_clashes(coords)
        clash_penalty = min(0.5, clash_count * 0.02)
        clash_score = 1.0 - clash_penalty

        return float(backbone_score * 0.4 + pair_score * 0.3 + clash_score * 0.3)

    def _count_steric_clashes(self, coords: np.ndarray,
                               min_dist: float = 2.5) -> int:
        n = len(coords)
        clashes = 0
        for i in range(n):
            for j in range(i + 3, n):
                dist = float(np.linalg.norm(coords[i] - coords[j]))
                if dist < min_dist:
                    clashes += 1
        return clashes

    def _fractal_dimension_estimate(self, coords: np.ndarray) -> float:
        n = len(coords)
        if n < 5:
            return 1.0

        centroid = np.mean(coords, axis=0)
        radii = np.sqrt(np.sum((coords - centroid) ** 2, axis=1))
        max_r = float(np.max(radii))
        if max_r < 1e-8:
            return 1.0

        scales = np.linspace(max_r * 0.1, max_r, 10)
        counts = []
        for r in scales:
            count = int(np.sum(radii <= r))
            counts.append(max(1, count))

        log_scales = np.log(scales + 1e-8)
        log_counts = np.log(np.array(counts, dtype=np.float64) + 1e-8)

        if len(log_scales) > 1:
            coeffs = np.polyfit(log_scales, log_counts, 1)
            return float(max(1.0, min(3.0, coeffs[0])))
        return 1.5

    def format_kaggle_submission(self, predictions: dict,
                                  output_path: str) -> str:
        submission_data = {
            'id': [],
            'x': [],
            'y': [],
            'z': [],
        }

        for seq_id, coords in predictions.items():
            if isinstance(coords, np.ndarray):
                coord_array = coords
            elif isinstance(coords, list):
                coord_array = np.array(coords)
            else:
                continue

            for atom_idx in range(len(coord_array)):
                submission_data['id'].append(f"{seq_id}_{atom_idx}")
                submission_data['x'].append(round(float(coord_array[atom_idx][0]), 4))
                submission_data['y'].append(round(float(coord_array[atom_idx][1]), 4))
                submission_data['z'].append(round(float(coord_array[atom_idx][2]), 4))

        lines = ['id,x,y,z']
        for i in range(len(submission_data['id'])):
            lines.append(
                f"{submission_data['id'][i]},"
                f"{submission_data['x'][i]},"
                f"{submission_data['y'][i]},"
                f"{submission_data['z'][i]}"
            )

        csv_content = '\n'.join(lines)

        with open(output_path, 'w') as f:
            f.write(csv_content)

        return output_path

    def load_competition_data(self, filepath: str) -> List[dict]:
        sequences = []

        try:
            with open(filepath, 'r') as f:
                content = f.read().strip()
        except FileNotFoundError:
            return []

        if filepath.endswith('.json'):
            data = json.loads(content)
            if isinstance(data, list):
                return data
            elif isinstance(data, dict):
                return [data]

        if filepath.endswith('.fasta') or filepath.endswith('.fa'):
            lines = content.split('\n')
            current_id = None
            current_seq = []
            for line in lines:
                line = line.strip()
                if line.startswith('>'):
                    if current_id is not None:
                        sequences.append({
                            'id': current_id,
                            'sequence': ''.join(current_seq),
                        })
                    current_id = line[1:].split()[0]
                    current_seq = []
                elif line:
                    current_seq.append(line)
            if current_id is not None:
                sequences.append({
                    'id': current_id,
                    'sequence': ''.join(current_seq),
                })
            return sequences

        if filepath.endswith('.csv') or filepath.endswith('.tsv'):
            sep = '\t' if filepath.endswith('.tsv') else ','
            lines = content.split('\n')
            if len(lines) < 2:
                return []
            headers = lines[0].split(sep)
            for line in lines[1:]:
                if not line.strip():
                    continue
                values = line.split(sep)
                entry = {}
                for h, v in zip(headers, values):
                    entry[h.strip()] = v.strip()
                sequences.append(entry)
            return sequences

        return sequences

    def get_model_summary(self) -> dict:
        return {
            'model_name': 'TI-RNA3D',
            'version': self.model_version,
            'competition': self.competition_name,
            'deadline': '2026-03-25',
            'prize': '$75,000',
            'approach': {
                'secondary_structure': 'Nussinov dynamic programming algorithm',
                'coordinate_generation': 'Physics-based backbone with constraint satisfaction',
                'energy_minimization': 'Gradient descent on bond/pair distance constraints',
                'evaluation': 'TM-score and RMSD with Kabsch alignment',
                'confidence': 'Tralse framework for prediction uncertainty',
                'analysis': 'GILE structural analysis (Stability, Information, Function, Physics)',
            },
            'parameters': {
                'backbone_step': BACKBONE_STEP,
                'base_pair_distance': BASE_PAIR_DISTANCE,
                'min_loop_length': MIN_LOOP_LENGTH,
                'bond_length_PO': BOND_LENGTH_PO,
                'bond_length_OC': BOND_LENGTH_OC,
                'energy_minimization_steps': 100,
                'constraint_iterations': 50,
            },
            'supported_bases': list(BASE_INDEX.keys()),
            'valid_base_pairs': [f"{a}-{b}" for a, b in BASE_PAIRS],
            'ti_framework': {
                'G': 'Structural stability (free energy, base pairing)',
                'I': 'Information content (sequence complexity, pair density)',
                'L': 'Functional potential (binding sites, catalytic motifs)',
                'E': 'Physical validity (bond geometry, steric clashes)',
            },
            'fractal_connection': (
                'RNA folding exhibits self-similar patterns at multiple scales. '
                'The fractal dimension of predicted structures connects to the '
                'fractal_universe_engine for cross-domain pattern analysis.'
            ),
        }

    def run_full_pipeline(self, sequence: str,
                           n_predictions: int = 5) -> dict:
        seq = sequence.upper().replace('T', 'U')

        encoding = self.encode_sequence(seq)
        features = self.analyze_sequence_features(seq)
        ss = self.compute_secondary_structure(seq)
        distance_matrix = self.predict_distance_matrix(seq)
        predictions = self.generate_3d_coordinates(seq, n_predictions)

        scores = []
        for i, pred in enumerate(predictions):
            if i > 0:
                score = self.compute_tm_score(pred, predictions[0])
            else:
                score = 1.0
            scores.append(score)

        tralse_results = self.apply_tralse_confidence(predictions, scores)

        best_idx = max(range(len(tralse_results)),
                       key=lambda k: tralse_results[k]['confidence'])
        best_coords = predictions[best_idx]

        gile = self.gile_structural_analysis(seq, best_coords)

        pairwise_tm = np.zeros((n_predictions, n_predictions))
        for i in range(n_predictions):
            for j in range(n_predictions):
                if i == j:
                    pairwise_tm[i][j] = 1.0
                elif i < j:
                    tm = self.compute_tm_score(predictions[i], predictions[j])
                    pairwise_tm[i][j] = tm
                    pairwise_tm[j][i] = tm

        return {
            'sequence': seq,
            'length': len(seq),
            'encoding_shape': list(encoding.shape),
            'features': features,
            'secondary_structure': ss,
            'distance_matrix_shape': list(distance_matrix.shape),
            'n_predictions': n_predictions,
            'best_prediction_index': best_idx,
            'best_coordinates': best_coords.tolist(),
            'tralse_results': tralse_results,
            'gile_analysis': gile,
            'pairwise_tm_scores': pairwise_tm.tolist(),
            'model_summary': self.get_model_summary(),
        }

    def batch_predict(self, sequences: List[str],
                       n_predictions: int = 3) -> List[dict]:
        results = []
        for seq in sequences:
            result = self.run_full_pipeline(seq, n_predictions)
            results.append(result)
        return results

    def generate_competition_submission(self, sequences: List[dict],
                                         output_path: str = "kaggle/submissions/rna_3d_submission.csv") -> dict:
        all_predictions = {}

        for entry in sequences:
            seq_id = entry.get('id', f"seq_{len(all_predictions)}")
            sequence = entry.get('sequence', '')
            if not sequence:
                continue

            predictions = self.generate_3d_coordinates(sequence, n_predictions=5)
            scores = []
            for i, pred in enumerate(predictions):
                if i > 0:
                    scores.append(self.compute_tm_score(pred, predictions[0]))
                else:
                    scores.append(1.0)

            tralse = self.apply_tralse_confidence(predictions, scores)
            best_idx = max(range(len(tralse)),
                          key=lambda k: tralse[k]['confidence'])

            all_predictions[seq_id] = predictions[best_idx]

        output_file = self.format_kaggle_submission(all_predictions, output_path)

        return {
            'output_file': output_file,
            'sequences_processed': len(all_predictions),
            'total_atoms': sum(len(c) for c in all_predictions.values()),
            'format': 'id,x,y,z',
        }


def demo():
    engine = RNA3DFoldingEngine(seed=42)

    print("=" * 60)
    print("RNA 3D FOLDING ENGINE - Demo")
    print("Stanford RNA 3D Folding Part 2 Competition")
    print("=" * 60)

    test_seq = "GCGCAAGCGC"
    print(f"\nTest sequence: {test_seq}")

    encoding = engine.encode_sequence(test_seq)
    print(f"Encoding shape: {encoding.shape}")

    ss = engine.compute_secondary_structure(test_seq)
    print(f"Secondary structure: {ss['bracket_notation']}")
    print(f"Base pairs: {ss['num_pairs']}")
    print(f"Free energy: {ss['free_energy_estimate']:.1f} kcal/mol")

    features = engine.analyze_sequence_features(test_seq)
    print(f"GC content: {features['gc_content']:.2%}")
    print(f"Complexity: {features['sequence_complexity']:.3f}")

    predictions = engine.generate_3d_coordinates(test_seq, n_predictions=5)
    print(f"\nGenerated {len(predictions)} 3D predictions")
    for i, pred in enumerate(predictions):
        print(f"  Prediction {i}: shape {pred.shape}, "
              f"span {np.max(np.ptp(pred, axis=0)):.1f}Å")

    scores = []
    for i, pred in enumerate(predictions):
        tm = engine.compute_tm_score(pred, predictions[0])
        rmsd = engine.compute_rmsd(pred, predictions[0])
        scores.append(tm)
        print(f"  vs pred_0: TM={tm:.4f}, RMSD={rmsd:.2f}Å")

    tralse = engine.apply_tralse_confidence(predictions, scores)
    print("\nTralse confidence:")
    for t in tralse:
        print(f"  Pred {t['prediction_index']}: "
              f"confidence={t['confidence']:.4f} "
              f"[{t['classification']}]")

    gile = engine.gile_structural_analysis(test_seq, predictions[0])
    print(f"\nGILE Analysis:")
    print(f"  G (Stability):  {gile['G']:.4f}")
    print(f"  I (Information): {gile['I']:.4f}")
    print(f"  L (Function):    {gile['L']:.4f}")
    print(f"  E (Physics):     {gile['E']:.4f}")
    print(f"  Composite:       {gile['gile_composite']:.4f}")
    print(f"  Fractal dim:     {gile['fractal_dimension']:.4f}")

    samples = engine.generate_sample_rna_data(5)
    print(f"\nGenerated {len(samples)} sample RNA entries")
    for s in samples:
        print(f"  {s['id']}: {s['sequence']} ({s['motif_type']}, "
              f"{s['num_pairs']} pairs)")

    summary = engine.get_model_summary()
    print(f"\nModel: {summary['model_name']} v{summary['version']}")
    print(f"Competition: {summary['competition']}")
    print(f"Deadline: {summary['deadline']}")

    print("\n" + "=" * 60)
    print("Demo complete!")


if __name__ == "__main__":
    demo()
