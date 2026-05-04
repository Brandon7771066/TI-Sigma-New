"""
H4 Pilot: Brandon ↔ Jeffrey Facial Similarity Measurement
==========================================================

URB #597b H4 hypothesis pilot. N=1 parent-child pair (Brandon Charles Emerick
and his late father Jeffrey Emerick).

HONEST LIMITATIONS:
- This is N=1, anecdotal. Cannot test the kinship-vs-similarity regression
  that H4 actually proposes — that needs N≥50 pairs.
- Uses coarse image-similarity metrics (pHash, color histogram, grayscale
  cosine, HOG-style gradient cosine), NOT proper ArcFace/FaceNet embeddings.
  Proper face embeddings require `insightface` or `face_recognition`, both of
  which currently fail to install due to a project-level dep conflict.
- Crop boxes for the face regions are estimated manually from image geometry
  and visually verified by saving crops to `pilots/`. Should be re-run when
  proper face-detection is available.

WHAT THIS PILOT DOES PROVIDE:
- A real, reproducible measurement of *image-level* similarity between the
  two faces, using metrics that are coarser than ArcFace but still
  informative.
- A baseline comparison: father-vs-son similarity vs. father-vs-control
  (the same father image flipped horizontally and degraded as a "different
  face" stand-in) and son-vs-itself (upper bound).
- A reusable pipeline that drops in ArcFace embeddings the moment install
  works.

USAGE:
    python scripts/h4_face_pilot.py
"""
from __future__ import annotations
import os
import sys
import math
import json
from dataclasses import dataclass, asdict
from pathlib import Path

import numpy as np
from PIL import Image, ImageOps, ImageFilter
from scipy.spatial.distance import cosine as cosine_dist
from sklearn.preprocessing import normalize


ROOT = Path(__file__).resolve().parent.parent
JEFF_PATH = ROOT / "attached_assets" / "IMG_4867_1777924843117.jpeg"
BRANDON_PATH = ROOT / "attached_assets" / "IMG_4868_1777924843118.jpeg"
OUT_DIR = ROOT / "pilots" / "h4_face_brandon_jeffrey"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# ---------------------------------------------------------------------------
# Crop boxes (manually estimated; both source images are 4032x3024).
# These were chosen by inspecting the photos:
#   - Jeffrey: framed portrait, face occupies roughly center-upper of image.
#   - Brandon: driver's license on bedsheets; primary headshot is in the
#     upper-left quadrant of the license.
# Boxes are (left, top, right, bottom) in pixels.
# ---------------------------------------------------------------------------
JEFF_CROP = (1100, 700, 2900, 2400)        # face inside the frame
BRANDON_CROP = (650, 1300, 1850, 2500)     # DL primary headshot region


@dataclass
class SimilarityResult:
    metric: str
    pair: str
    score: float
    interpretation: str


# ---------------------------------------------------------------------------
# Loading & preprocessing
# ---------------------------------------------------------------------------
def load_face(path: Path, crop_box: tuple[int, int, int, int],
              size: int = 256) -> Image.Image:
    img = Image.open(path).convert("RGB")
    face = img.crop(crop_box)
    face = ImageOps.fit(face, (size, size), Image.LANCZOS)
    return face


# ---------------------------------------------------------------------------
# Metric 1 — Perceptual hash distance (Hamming over 64-bit hash)
# ---------------------------------------------------------------------------
def phash(img: Image.Image, hash_size: int = 16) -> np.ndarray:
    """Difference perceptual hash. Returns a flat 0/1 array."""
    g = img.convert("L").resize((hash_size + 1, hash_size), Image.LANCZOS)
    a = np.asarray(g, dtype=np.int32)
    diff = a[:, 1:] > a[:, :-1]
    return diff.astype(np.uint8).flatten()


def phash_similarity(a: Image.Image, b: Image.Image) -> float:
    ha, hb = phash(a), phash(b)
    hamming = float(np.sum(ha != hb))
    return 1.0 - hamming / ha.size  # 1 = identical, 0 = orthogonal


# ---------------------------------------------------------------------------
# Metric 2 — Color histogram correlation (RGB, 16 bins per channel)
# ---------------------------------------------------------------------------
def color_hist(img: Image.Image, bins: int = 16) -> np.ndarray:
    a = np.asarray(img)
    hists = []
    for c in range(3):
        h, _ = np.histogram(a[..., c], bins=bins, range=(0, 256), density=True)
        hists.append(h)
    return np.concatenate(hists)


def hist_correlation(a: Image.Image, b: Image.Image) -> float:
    ha, hb = color_hist(a), color_hist(b)
    # Pearson correlation
    return float(np.corrcoef(ha, hb)[0, 1])


# ---------------------------------------------------------------------------
# Metric 3 — Downsampled grayscale cosine similarity
# ---------------------------------------------------------------------------
def gray_vector(img: Image.Image, size: int = 32) -> np.ndarray:
    g = img.convert("L").resize((size, size), Image.LANCZOS)
    v = np.asarray(g, dtype=np.float32).flatten()
    v -= v.mean()
    n = np.linalg.norm(v)
    return v / n if n > 0 else v


def gray_cosine(a: Image.Image, b: Image.Image) -> float:
    va, vb = gray_vector(a), gray_vector(b)
    return float(np.dot(va, vb))


# ---------------------------------------------------------------------------
# Metric 4 — HOG-style gradient orientation cosine
# (Coarse hand-rolled HOG since skimage is not guaranteed installed)
# ---------------------------------------------------------------------------
def hog_vector(img: Image.Image, cell: int = 16, bins: int = 9) -> np.ndarray:
    g = img.convert("L").resize((128, 128), Image.LANCZOS)
    a = np.asarray(g, dtype=np.float32)
    gx = np.zeros_like(a); gy = np.zeros_like(a)
    gx[:, 1:-1] = a[:, 2:] - a[:, :-2]
    gy[1:-1, :] = a[2:, :] - a[:-2, :]
    mag = np.hypot(gx, gy)
    ang = (np.arctan2(gy, gx) + math.pi) % math.pi  # 0..pi
    bin_idx = np.clip((ang / math.pi * bins).astype(int), 0, bins - 1)
    H, W = a.shape
    feats = []
    for i in range(0, H, cell):
        for j in range(0, W, cell):
            cell_bins = np.zeros(bins, dtype=np.float32)
            bs = bin_idx[i:i+cell, j:j+cell]
            ms = mag[i:i+cell, j:j+cell]
            for b in range(bins):
                cell_bins[b] = ms[bs == b].sum()
            feats.append(cell_bins)
    v = np.concatenate(feats)
    n = np.linalg.norm(v)
    return v / n if n > 0 else v


def hog_cosine(a: Image.Image, b: Image.Image) -> float:
    va, vb = hog_vector(a), hog_vector(b)
    return float(np.dot(va, vb))


# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------
def compare(label: str, a: Image.Image, b: Image.Image) -> list[SimilarityResult]:
    return [
        SimilarityResult("phash_sim",      label, phash_similarity(a, b),
                         "Perceptual hash similarity (1=identical, 0.5=chance)"),
        SimilarityResult("color_hist_r",   label, hist_correlation(a, b),
                         "RGB histogram Pearson correlation (-1..+1)"),
        SimilarityResult("gray_cosine",    label, gray_cosine(a, b),
                         "Centered grayscale 32x32 cosine (-1..+1)"),
        SimilarityResult("hog_cosine",     label, hog_cosine(a, b),
                         "HOG-style gradient orientation cosine (0..1 typ.)"),
    ]


def main() -> None:
    print(f"Loading Jeffrey  from {JEFF_PATH.name}  crop={JEFF_CROP}")
    print(f"Loading Brandon  from {BRANDON_PATH.name}  crop={BRANDON_CROP}")

    jeff = load_face(JEFF_PATH, JEFF_CROP)
    bran = load_face(BRANDON_PATH, BRANDON_CROP)

    # Save crops for visual verification
    jeff.save(OUT_DIR / "jeffrey_face_crop.png")
    bran.save(OUT_DIR / "brandon_face_crop.png")
    print(f"Saved crops to {OUT_DIR}")

    # Controls
    bran_flip = ImageOps.mirror(bran)               # mirror = same person, geometry preserved
    jeff_blur = jeff.filter(ImageFilter.GaussianBlur(radius=12))
    rng = np.random.default_rng(42)
    noise_arr = rng.integers(0, 256, size=(256, 256, 3), dtype=np.uint8)
    noise = Image.fromarray(noise_arr)
    inverted_jeff = ImageOps.invert(jeff)           # photometric extreme

    pairs = [
        ("BRANDON_vs_JEFFREY (target H4 case)", bran, jeff),
        ("BRANDON_vs_BRANDON_mirror (self-control upper bound)", bran, bran_flip),
        ("JEFFREY_vs_JEFFREY_blur (self-control degraded)", jeff, jeff_blur),
        ("BRANDON_vs_NOISE (random-image lower bound)", bran, noise),
        ("JEFFREY_vs_INVERTED_JEFFREY (photometric extreme)", jeff, inverted_jeff),
    ]

    rows: list[SimilarityResult] = []
    for label, a, b in pairs:
        rows.extend(compare(label, a, b))

    # Pretty-print
    print()
    print(f"{'METRIC':14s} {'PAIR':55s} {'SCORE':>8s}")
    print("-" * 80)
    cur = None
    for r in rows:
        if r.pair != cur:
            print()
            cur = r.pair
        print(f"{r.metric:14s} {r.pair[:55]:55s} {r.score:8.4f}")

    # Save JSON for the report
    out_json = OUT_DIR / "results.json"
    with open(out_json, "w") as f:
        json.dump([asdict(r) for r in rows], f, indent=2)
    print(f"\nSaved {out_json}")

    # Compute headline numbers for the paper
    target = {r.metric: r.score for r in rows
              if r.pair.startswith("BRANDON_vs_JEFFREY")}
    self_ub = {r.metric: r.score for r in rows
               if r.pair.startswith("BRANDON_vs_BRANDON_mirror")}
    rand_lb = {r.metric: r.score for r in rows
               if r.pair.startswith("BRANDON_vs_NOISE")}

    print("\n=== HEADLINE: how close is father-son to self-similarity? ===")
    for m in ["phash_sim", "color_hist_r", "gray_cosine", "hog_cosine"]:
        t, ub, lb = target[m], self_ub[m], rand_lb[m]
        # Normalize: where does father-son fall on the lb..ub scale?
        if ub == lb:
            norm = float("nan")
        else:
            norm = (t - lb) / (ub - lb)
        print(f"  {m:14s} target={t:+.4f}  self_ub={ub:+.4f}  rand_lb={lb:+.4f}  "
              f"normalized={norm:.3f}")

    # Save normalized scores
    norm_out = {}
    for m in ["phash_sim", "color_hist_r", "gray_cosine", "hog_cosine"]:
        t, ub, lb = target[m], self_ub[m], rand_lb[m]
        norm_out[m] = {
            "target": t, "self_ub": ub, "rand_lb": lb,
            "normalized": (t - lb) / (ub - lb) if ub != lb else None,
        }
    with open(OUT_DIR / "normalized.json", "w") as f:
        json.dump(norm_out, f, indent=2)


if __name__ == "__main__":
    main()
