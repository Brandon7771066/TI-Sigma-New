"""
URB #828 v2 - Section 6 Classical-ML Discriminator Skeleton (Condition C0)

Implements the asymmetric-standards #69 critical falsifier: train a classical
ML classifier on permanent-BPS features only (no live channels, no protocol)
to predict the M=5 target token. Pre-registered prediction:

  Resonance hypothesis : C0 accuracy <= 0.25 (chance ~ 0.20)
  Feature-extraction   : C0 accuracy >  0.35

Uses leave-one-trial-out cross-validation with pre-committed seeds. No
mid-experiment hyperparameter tuning (all hyperparameters fixed below).
Run: python urb828_c0_ml_discriminator_skeleton.py --trials data/urb828/results.csv
"""

import argparse
import json
import os
from pathlib import Path
from typing import List, Tuple

import numpy as np


SEED = 20260501  # pre-committed
M = 5  # token-set size
CHANCE = 1.0 / M


# -------------------- Feature extractors (placeholders) --------------------
# Each function ingests a per-trial directory and returns a 1D numpy vector.
# In production, these are replaced with real extraction calls. For now they
# are deterministic stubs so the pipeline runs end-to-end before real data.


def extract_dna_features(trial_dir: Path) -> np.ndarray:
    """3 floats: mito_snp_score, telomere_proxy, cpg_promoter_density.
    Constant across all trials (DNA is time-invariant)."""
    return np.array([0.9468, 0.4167, 0.4757], dtype=np.float32)


def extract_face_features(trial_dir: Path) -> np.ndarray:
    """68-landmark face geometry, normalized to inter-pupillary distance.
    Stub: 136 zeros until face_recognition library is integrated."""
    return np.zeros(136, dtype=np.float32)


def extract_handwriting_features(trial_dir: Path) -> np.ndarray:
    """Stroke/style features: line-darkness var, aspect, slant, baseline drift,
    letter spacing. Stub: 8 zeros until opencv extractor wired."""
    return np.zeros(8, dtype=np.float32)


def extract_fingerprint_features(trial_dir: Path) -> np.ndarray:
    """Minutiae count + ridge-orientation histogram. Stub: 16 zeros."""
    return np.zeros(16, dtype=np.float32)


def build_feature_vector(trial_dir: Path, include_fingerprint: bool = False) -> np.ndarray:
    parts = [
        extract_dna_features(trial_dir),
        extract_face_features(trial_dir),
        extract_handwriting_features(trial_dir),
    ]
    if include_fingerprint:
        parts.append(extract_fingerprint_features(trial_dir))
    return np.concatenate(parts)


# -------------------- LOO-CV harness --------------------


def load_trial_metadata(results_csv: Path) -> List[Tuple[Path, str]]:
    """Return list of (trial_dir, ground_truth_token).

    results.csv expected columns: trial_dir, ground_truth_token (after Brandon
    opens sealed envelope). Other columns ignored at C0 stage.
    """
    import csv
    out = []
    if not results_csv.exists():
        return out
    with open(results_csv) as f:
        reader = csv.DictReader(f)
        for row in reader:
            td = Path(row.get("trial_dir", ""))
            tok = row.get("ground_truth_token", "")
            if td and tok:
                out.append((td, tok))
    return out


def run_loo_cv(trials: List[Tuple[Path, str]], include_fingerprint: bool = False) -> dict:
    """Leave-one-trial-out CV with three pre-committed classifiers."""
    from sklearn.ensemble import RandomForestClassifier
    from sklearn.neighbors import KNeighborsClassifier
    from sklearn.linear_model import LogisticRegression

    if len(trials) < 5:
        return {
            "n_trials": len(trials),
            "error": "insufficient trials (need >= 5 for LOO-CV)",
            "honest_note": "Report this as 'underpowered, no result' not as 'C0 at chance'.",
        }

    X = np.stack([build_feature_vector(td, include_fingerprint) for td, _ in trials])
    y = np.array([tok for _, tok in trials])

    classifiers = {
        "knn_k3": KNeighborsClassifier(n_neighbors=3),
        "rf_200": RandomForestClassifier(n_estimators=200, random_state=SEED, n_jobs=1),
        "logreg": LogisticRegression(max_iter=1000, random_state=SEED, n_jobs=1),
    }

    results = {}
    for name, clf in classifiers.items():
        n_correct = 0
        for i in range(len(trials)):
            mask = np.ones(len(trials), dtype=bool)
            mask[i] = False
            try:
                clf.fit(X[mask], y[mask])
                pred = clf.predict(X[i:i + 1])[0]
            except Exception as e:
                return {"error": f"{name} fit/predict failed: {e}"}
            if pred == y[i]:
                n_correct += 1
        acc = n_correct / len(trials)
        results[name] = {
            "accuracy": acc,
            "n_correct": n_correct,
            "n_trials": len(trials),
            "above_chance": acc > CHANCE,
            "above_resonance_threshold_0.25": acc > 0.25,
            "above_feature_extraction_threshold_0.35": acc > 0.35,
        }
    return results


def interpret(results: dict) -> str:
    if "error" in results:
        return f"ERROR: {results['error']}"
    lines = []
    any_above_35 = any(r["accuracy"] > 0.35 for r in results.values())
    all_below_25 = all(r["accuracy"] <= 0.25 for r in results.values())
    if any_above_35:
        lines.append("§6 CRITICAL-FALSIFIER TRIGGERED")
        lines.append("At least one classical ML classifier exceeds 0.35 on permanent")
        lines.append("BPS features alone. The resonance interpretation collapses to")
        lines.append("feature-extraction-with-mystical-vocabulary. URB #828 v2 must")
        lines.append("be reframed as a feature-extraction empirical paper.")
    elif all_below_25:
        lines.append("§6 CRITICAL FALSIFIER NOT TRIGGERED")
        lines.append("All classifiers <= 0.25. Resonance interpretation remains")
        lines.append("admissible. Proceed to evaluate live-channel arms (C3-C7).")
    else:
        lines.append("§6 RESULT INCONCLUSIVE")
        lines.append("Some classifiers between 0.25 and 0.35. Replication required.")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", default="data/urb828/results.csv")
    ap.add_argument("--include-fingerprint", action="store_true")
    ap.add_argument("--out", default="data/urb828/c0_results.json")
    args = ap.parse_args()

    trials_path = Path(args.trials)
    trials = load_trial_metadata(trials_path)
    print(f"Loaded {len(trials)} trials from {trials_path}")
    print(f"Chance = {CHANCE:.2f}, M = {M}, seed = {SEED}")
    print(f"Resonance threshold = 0.25, feature-extraction threshold = 0.35")
    print()

    results = run_loo_cv(trials, args.include_fingerprint)

    if "error" not in results:
        for name, r in results.items():
            print(f"  {name}: acc={r['accuracy']:.3f} ({r['n_correct']}/{r['n_trials']})")
        print()
        print(interpret(results))
        os.makedirs(Path(args.out).parent, exist_ok=True)
        with open(args.out, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\nSaved -> {args.out}")
    else:
        print(results["error"])
        if "honest_note" in results:
            print(results["honest_note"])


if __name__ == "__main__":
    main()
