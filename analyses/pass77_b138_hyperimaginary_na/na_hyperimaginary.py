"""
Pass-77 B138 — N/A as Hyperimaginary (NAH-1): a third axis beyond the C4 plane
=============================================================================
Author (Brandon) refinement: "N/A represents an imprecise real value that is
hyperimaginary (with the hyperimaginary value high but also still imprecise)."

Geometry. The base-4 truth labels {T, F, I, MI} live on the C4 *truth plane*
(real axis = determinate T/F; imaginary axis = indeterminacy modality I/MI; this
is TTI-1, B136). N/A is NOT a base-4 label -- in the canonical MR pipeline it is
screened FIRST, before MI/T/F. NAH-1 gives it a geometry: N/A sits on a THIRD,
*hyperimaginary* axis (unit j), off the truth plane:
    value = real * 1  +  imag * i  +  hyper * j
  * N/A's hyperimaginary component is HIGH (large |hyper|): maximally off-plane.
  * N/A's hyperimaginary component is IMPRECISE (wide band): N/A is, by nature,
    an under-determined ("imprecise real") magnitude lifted onto j.

Why this matters. The canonical 64D GILE Matrix FOLDS N/A into MI (NA recall = 0)
to close at 4^3 = 64 cells. PDR-1 (B108) already found the imaginary axis is the
"decisive upgrade" (NA-blind reps tie ~0.746; NA-holding reach ~0.918-0.922).
NAH-1 supplies the *principled* reason and tests the claim ONE LEVEL UP.

FAIR-TEST DESIGN (addresses a code-review point that an earlier version rigged the
baseline). The NA-blind classifier is NOT hand-folded onto MI. Instead BOTH
classifiers get an N/A prototype; the blind one simply lacks the j-axis, so it
sees N/A's *natural projection onto the C4 plane*, which is the origin (0,0)
(N/A's truth-plane coordinates are ~0 -- that is the whole point of "off-plane").
N/A then competes fairly on the C4 plane and loses recall ONLY because the plane
cannot separate an off-plane, imprecise point from the low-magnitude tails of the
other labels. Robustness: results are averaged over many seeds (mean +/- std).

HONESTY (this is a REPRESENTATIONAL CAPACITY toy, NOT a claim about reality):
  * We test whether the geometry CAN separate N/A from the base-4 labels. We do
    NOT claim N/A "exists" as a physical quantity, and this is not a discovery --
    it is consistent with the DIRECTION of PDR-1 (NA-holding > NA-blind); we do
    NOT treat the numeric band-match as independent evidence.
  * No constant coincidence is load-bearing (anti-numerology).
  * Count unchanged 79; NAH-1 is a CANDIDATE refinement, not a ratified principle.
"""
from __future__ import annotations
import json
import numpy as np

LABELS = ["T", "F", "I", "MI", "NA"]

# Canonical prototype codes in 3 axes (real, imaginary=i, hyperimaginary=j).
#   T/F on the real axis; I/MI on the imaginary axis (TTI-1); NA HIGH on j.
PROTOTYPE_3D = {
    "T":  np.array([+1.0, 0.0, 0.0]),
    "F":  np.array([-1.0, 0.0, 0.0]),
    "I":  np.array([0.0, +1.0, 0.0]),
    "MI": np.array([0.0, -1.0, 0.0]),
    "NA": np.array([0.0, 0.0, +1.0]),   # hyperimaginary, HIGH
}

# Per-label sampling spread. N/A is deliberately IMPRECISE: wide on its real part
# (under-determined real value) AND wide on its high hyperimaginary part.
SPREAD_3D = {
    "T":  np.array([0.15, 0.10, 0.05]),
    "F":  np.array([0.15, 0.10, 0.05]),
    "I":  np.array([0.10, 0.15, 0.05]),
    "MI": np.array([0.10, 0.15, 0.05]),
    "NA": np.array([0.40, 0.10, 0.40]),   # imprecise real + imprecise-but-high j
}


def sample(label, n, rng):
    return PROTOTYPE_3D[label] + rng.normal(0, 1, (n, 3)) * SPREAD_3D[label]


def nearest_prototype(X, axes):
    """Nearest of ALL FIVE canonical prototypes, using only `axes`.
    The blind condition (axes=[0,1]) sees each prototype's natural C4 projection;
    N/A's projection is the origin (0,0) -- not a hand-set fold onto MI."""
    names = list(PROTOTYPE_3D.keys())
    P = np.array([PROTOTYPE_3D[k][axes] for k in names])
    preds = []
    for x in X[:, axes]:
        d = ((P - x) ** 2).sum(axis=1)
        preds.append(names[int(np.argmin(d))])
    return preds


def per_label_recall(y_true, y_pred):
    out = {}
    for lab in LABELS:
        idx = [i for i, y in enumerate(y_true) if y == lab]
        correct = sum(1 for i in idx if y_pred[i] == lab)
        out[lab] = correct / len(idx) if idx else None
    return out


def macro_f1(y_true, y_pred):
    f1s = []
    for lab in LABELS:
        tp = sum(1 for t, p in zip(y_true, y_pred) if t == lab and p == lab)
        fp = sum(1 for t, p in zip(y_true, y_pred) if t != lab and p == lab)
        fn = sum(1 for t, p in zip(y_true, y_pred) if t == lab and p != lab)
        prec = tp / (tp + fp) if (tp + fp) else 0.0
        rec = tp / (tp + fn) if (tp + fn) else 0.0
        f1s.append(2 * prec * rec / (prec + rec) if (prec + rec) else 0.0)
    return float(np.mean(f1s))


def na_confusion(y_true, y_pred):
    """Where do blind-misclassified N/A samples go?"""
    counts = {l: 0 for l in LABELS}
    for t, p in zip(y_true, y_pred):
        if t == "NA":
            counts[p] += 1
    tot = sum(counts.values())
    return {l: round(c / tot, 3) for l, c in counts.items()} if tot else {}


def run(n=4000, seeds=range(20)):
    rec_blind_na, rec_nah_na = [], []
    rec_blind_mi, rec_nah_mi = [], []
    f1_blind, f1_nah = [], []
    conf_blind = {l: [] for l in LABELS}
    for s in seeds:
        rng = np.random.default_rng(s)
        X = np.vstack([sample(l, n, rng) for l in LABELS])
        y = sum(([l] * n for l in LABELS), [])
        yb = nearest_prototype(X, axes=[0, 1])     # C4-blind (no j)
        yn = nearest_prototype(X, axes=[0, 1, 2])  # NAH (with j)
        rb, rn = per_label_recall(y, yb), per_label_recall(y, yn)
        rec_blind_na.append(rb["NA"]); rec_nah_na.append(rn["NA"])
        rec_blind_mi.append(rb["MI"]); rec_nah_mi.append(rn["MI"])
        f1_blind.append(macro_f1(y, yb)); f1_nah.append(macro_f1(y, yn))
        cb = na_confusion(y, yb)
        for l in LABELS:
            conf_blind[l].append(cb.get(l, 0.0))

    def ms(a):
        return {"mean": round(float(np.mean(a)), 4), "std": round(float(np.std(a)), 4)}

    out = {
        "model": "NAH-1 — N/A on a hyperimaginary axis (high but imprecise)",
        "design": {
            "labels": LABELS,
            "axes": {"real": "determinate T/F", "imaginary_i": "indeterminacy I/MI (TTI-1)",
                     "hyperimaginary_j": "N/A: HIGH magnitude, IMPRECISE band"},
            "na_is_imprecise": "wide spread on real (under-determined) AND on high j",
            "fair_baseline": "blind classifier keeps an N/A prototype; it just lacks "
                             "the j-axis, so it sees N/A's NATURAL C4 projection = origin "
                             "(NOT a hand-set fold onto MI); N/A competes fairly and loses "
                             "recall only because the plane can't separate an off-plane "
                             "imprecise point from the other labels' tails.",
            "samples_per_label": n, "seeds": len(list(seeds)),
        },
        "na_blind_C4_plane": {
            "NA_recall": ms(rec_blind_na),
            "MI_recall": ms(rec_blind_mi),
            "macro_f1": ms(f1_blind),
            "na_misclassified_to (mean frac)": {l: round(float(np.mean(conf_blind[l])), 3) for l in LABELS},
        },
        "nah_with_hyperimaginary": {
            "NA_recall": ms(rec_nah_na),
            "MI_recall": ms(rec_nah_mi),
            "macro_f1": ms(f1_nah),
        },
        "verdict": {
            "na_recall_improves": bool(np.mean(rec_nah_na) > np.mean(rec_blind_na) + 3 * np.std(rec_blind_na)),
            "mi_not_cannibalised": bool(np.mean(rec_nah_mi) >= np.mean(rec_blind_mi) - 0.02),
            "consistent_with_PDR1_direction": "NA-holding > NA-blind (B108 direction); "
                "the numeric band-match is NOT treated as independent evidence",
        },
        "honesty": {
            "is_empirical_about_reality": False,
            "claim": "representational CAPACITY: the hyperimaginary geometry CAN hold "
                     "the N/A vs base-4 distinction the C4 plane cannot; robust over seeds",
            "is_a_discovery": False,
            "anti_numerology": "no constant coincidence load-bearing",
            "principle_count": 79,
            "NAH1_status": "CANDIDATE refinement (extends TTI-1/ICC label space)",
            "falsifier_NAH1_F1": "OPEN — a genuinely 4-valued (non-N/A) corpus must NOT "
                                 "need the j-axis; if every real labelling task is fit "
                                 "equally well WITHOUT j, j is ornamental, not a joint.",
        },
    }
    with open("analyses/pass77_b138_hyperimaginary_na/results.json", "w") as f:
        json.dump(out, f, indent=2)
    print(json.dumps({
        "NA_recall_blind": out["na_blind_C4_plane"]["NA_recall"],
        "NA_recall_NAH": out["nah_with_hyperimaginary"]["NA_recall"],
        "MI_recall_blind": out["na_blind_C4_plane"]["MI_recall"],
        "MI_recall_NAH": out["nah_with_hyperimaginary"]["MI_recall"],
        "macro_f1_blind": out["na_blind_C4_plane"]["macro_f1"],
        "macro_f1_nah": out["nah_with_hyperimaginary"]["macro_f1"],
        "na_misclassified_to": out["na_blind_C4_plane"]["na_misclassified_to (mean frac)"],
        "na_recall_improves": out["verdict"]["na_recall_improves"],
    }, indent=2))


if __name__ == "__main__":
    run()
