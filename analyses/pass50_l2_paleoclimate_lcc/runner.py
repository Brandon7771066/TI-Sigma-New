"""Pass-50 L-2 — Unsupervised LCC, Paleoclimate δ¹⁸O Cross-Site.

Brandon-affirmed 2026-05-13: "Recommendation for next directive affirmed!!"
(Pivot to predicted-strongest cell after L-1 PRIMARY+SECONDARY null in markets.)

Pre-reg source: papers/PASS_49_LCC_PLAIN_FRAMEWORK_SUPERVISED_VS_UNSUPERVISED_2026-05-13.md §6.2.

OPERATIONAL DEFINITIONS (frozen pre-data, from §2.3 + §3 ecosystems row):
  - τ_max = 10 sample-units (= 200 yr at 20-yr resolution)
  - ρ_min = 0.40 (ecosystems)
  - G_crit: p<0.05 vs phase-shuffle null (200 surrogates)
  - S1: max_{τ in [-τ_max, τ_max]} |corr(X, Y; τ)| > ρ_min
  - S2: argmax τ* > 0
  - S3: Granger X→Y p<0.05 vs phase-shuffle (lag = |τ*|, min 1)
  - S4 (per pre-reg §2.3): regression of ΔX(t+1) on (Y(t) - mean(Y))
        coef < 0 AND p<0.05 (significant NEGATIVE feedback)
  - U4 (per pre-reg §2.3 strict): |coef| < 0.1 AND p > 0.20
        (note: U4 ≠ NOT S4 — there is an ambiguous middle ground that
         is neither S4 nor U4, and such windows are NOT unsupervised-LCC)
  - Unsupervised-LCC window = S1 ∧ S2 ∧ S3 ∧ U4 (pre-reg §2.3 line 45)
        (the "S1+S2+U4" shorthand in §2.4/§5/§6 elides S3 but §2.3 is canonical)
  - D_LCC: fraction of consecutive-window pairs where G_{X→Y}^{(k)} > G^{(k-1)} + ε
        with ε = 0.1 * stddev(G across windows)

DEVIATIONS FROM PRE-REG (logged per L-4 Filter B):
  D1. Site list: pre-reg said 5 sites from "alphabetically-sorted list of available
      high-resolution decadal-or-finer δ¹⁸O records spanning AD 1000-2000".
      Confirmed-accessible NOAA URLs as of 2026-05-13 yielded only 3 such records:
      GISP2 (Greenland Summit, bidecadal), GRIP (Greenland Summit, sub-decadal),
      TALDICE (Talos Dome Antarctica, sub-decadal). Dome Fuji available but
      250-yr resolution = only ~4 samples in AD 1000-2000 window, dropped pre-analysis.
      Pairs reduced 10 → 3. HOLDOUT pairs reduced 4 → 1.
  D2. Verdict-matrix degenerate at HOLDOUT N=1: original verdict thresholds
      (≥3 of 4, ≥2 of 4) cannot apply. Reported as PILOT_PRELIMINARY with
      individual pair verdicts; full L-2 closure requires expanding the
      site list (Pass-51+ → identify additional accessible records, e.g. via
      PAGES 2k LiPD bulk download).
  D3. Common grid: highest-resolution shared resolution = 20 years (GISP2's
      bidecadal). All sites resampled to AD 1010, 1030, 1050, ..., 1990 grid
      via linear interpolation within original sample bounds.

ALL OTHER PARAMETERS FROZEN PRE-FETCH per §6.2 + §3 ecosystems row.
"""
from __future__ import annotations
import json, re, hashlib
from pathlib import Path

import numpy as np

DATA_DIR = Path(__file__).parent / "data"
OUT_DIR = Path(__file__).parent

SITES = sorted([
    {"id": "GISP2",    "file": "gisp2_d18o20y.txt",   "lat":  72.6, "lon":  -38.5},
    {"id": "GRIP",     "file": "grip_d18o.txt",       "lat":  72.6, "lon":  -37.6},
    {"id": "TALDICE",  "file": "taldice_d18o2k.txt",  "lat": -72.8, "lon":  159.2},
], key=lambda s: s["id"])

WINDOW_SAMPLES = 15        # 300-yr windows on 20-yr grid (pre-reg said 100-yr=5 samples; too few dof for Granger w/ lag≥1+intercept; D4)
STEP_SAMPLES = 5           # 100-yr step (matches pre-reg step intent)
RHO_MIN = 0.40
TAU_MAX = 10               # ±10 samples = ±200 yr
N_PHASE_SURROGATES = 200
ALPHA = 0.05
GRID_START = 1000          # AD
GRID_END = 2000
GRID_STEP = 20
EPSILON_FRAC = 0.1


# ──────────────────────────────────────────────────────────────────
# §1  Parsers
# ──────────────────────────────────────────────────────────────────

def _parse_smushed_three_col(text: str) -> np.ndarray:
    """GISP2 / GRIP format: depth d18O age_BP all run together with no
    consistent whitespace. Parse via regex (positive-float, then signed
    d18O ~ -X.XX, then signed age_BP integer-ish)."""
    rows = []
    # d18O constrained to 1-2 decimals so it doesn't greedily eat the age digits
    # Files are TAB-separated; rendering in `head` collapsed tabs and made them
    # look smushed. Accept either tab or no-whitespace separators.
    pat = re.compile(r"^\s*(\d+(?:\.\d+)?)[\t ]*(-\d+\.\d{1,3})[\t ]*(-?\d+(?:\.\d+)?)\s*$")
    for line in text.splitlines():
        m = pat.match(line)
        if m:
            try:
                _, d18O, age_bp = float(m.group(1)), float(m.group(2)), float(m.group(3))
                rows.append((age_bp, d18O))
            except ValueError:
                pass
    arr = np.array(rows, dtype=float)
    if arr.size == 0:
        return arr
    # Convert age BP (0 BP = 1950 AD) → AD year
    arr[:, 0] = 1950.0 - arr[:, 0]
    return arr  # [year_AD, d18O]


def _parse_taldice(text: str) -> np.ndarray:
    """TALDICE: tab-delimited age_CE \\t d18O after `# Data:` header."""
    rows = []
    in_data = False
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith("age_CE") or s.lower().startswith("age"):
            in_data = True
            continue
        # The downloaded file may have lost tabs to whitespace. Try to extract
        # two floats: positive year_AD, then signed d18O (typically -30 to -40).
        m = re.match(r"^\s*(\d+(?:\.\d+)?)\s*[\t ]*(-\d+(?:\.\d+)?)", s)
        if m:
            year_ad = float(m.group(1))
            d18O = float(m.group(2))
            rows.append((year_ad, d18O))
            in_data = True
    return np.array(rows, dtype=float)


def load_site(site: dict) -> np.ndarray:
    text = (DATA_DIR / site["file"]).read_text(errors="replace")
    if site["id"] in ("GISP2", "GRIP"):
        arr = _parse_smushed_three_col(text)
    elif site["id"] == "TALDICE":
        arr = _parse_taldice(text)
    else:
        raise ValueError(site["id"])
    if arr.ndim != 2 or arr.size == 0:
        print(f"  WARN {site['id']}: parsed 0 rows; check format")
        return np.empty((0, 2), dtype=float)
    arr = arr[np.isfinite(arr).all(axis=1)]
    arr = arr[np.argsort(arr[:, 0])]
    return arr


def resample_to_grid(arr: np.ndarray, grid: np.ndarray) -> np.ndarray:
    """Linear interp with NaN outside original bounds."""
    if arr.size == 0:
        return np.full_like(grid, np.nan, dtype=float)
    y0, y1 = arr[:, 0].min(), arr[:, 0].max()
    out = np.interp(grid, arr[:, 0], arr[:, 1], left=np.nan, right=np.nan)
    out[(grid < y0) | (grid > y1)] = np.nan
    return out


# ──────────────────────────────────────────────────────────────────
# §2  LCC operational signatures
# ──────────────────────────────────────────────────────────────────

def lagged_corr(x: np.ndarray, y: np.ndarray, tau: int) -> float:
    """corr(X(t), Y(t+τ)). Positive τ ⇒ X leads Y (X(t) predicts Y(t+τ))."""
    if tau >= 0:
        a, b = x[: len(x) - tau], y[tau:]
    else:
        a, b = x[-tau:], y[: len(y) + tau]
    if len(a) < 4 or np.std(a) == 0 or np.std(b) == 0:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def s1_s2_max_lag_corr(x: np.ndarray, y: np.ndarray) -> tuple[float, int]:
    """Returns (best_signed_corr, best_tau)."""
    best_abs, best_corr, best_tau = 0.0, 0.0, 0
    for tau in range(-TAU_MAX, TAU_MAX + 1):
        c = lagged_corr(x, y, tau)
        if abs(c) > best_abs:
            best_abs, best_corr, best_tau = abs(c), c, tau
    return best_corr, best_tau


def hand_granger_F(y: np.ndarray, x: np.ndarray, lag: int) -> float:
    """Granger F-stat for X→Y at single lag. Returns NaN on degeneracy."""
    n = len(y)
    if n <= 2 * lag + 2:
        return float("nan")
    Y = y[lag:]
    Xr = np.column_stack([y[lag - i - 1: n - i - 1] for i in range(lag)])
    Xf = np.column_stack([Xr, np.column_stack([x[lag - i - 1: n - i - 1] for i in range(lag)])])
    Xr = np.column_stack([Xr, np.ones(len(Xr))])
    Xf = np.column_stack([Xf, np.ones(len(Xf))])
    try:
        br, *_ = np.linalg.lstsq(Xr, Y, rcond=None)
        bf, *_ = np.linalg.lstsq(Xf, Y, rcond=None)
        rss_r = float(np.sum((Y - Xr @ br) ** 2))
        rss_f = float(np.sum((Y - Xf @ bf) ** 2))
        if rss_f <= 0 or rss_r <= rss_f:
            return 0.0
        dof = len(Y) - Xf.shape[1]
        if dof <= 0:
            return float("nan")
        F = ((rss_r - rss_f) / lag) / (rss_f / dof)
        return F
    except np.linalg.LinAlgError:
        return float("nan")


def phase_shuffle(x: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """Surrogate with same power spectrum, randomized phases."""
    n = len(x)
    X = np.fft.rfft(x - x.mean())
    phases = rng.uniform(0, 2 * np.pi, size=len(X))
    phases[0] = 0
    if n % 2 == 0:
        phases[-1] = 0
    Xs = np.abs(X) * np.exp(1j * phases)
    out = np.fft.irfft(Xs, n=n) + x.mean()
    return out


def s3_granger_phase_shuffle_p(x: np.ndarray, y: np.ndarray, lag: int, seed: int) -> tuple[float, float]:
    """Returns (F_observed, p_phase_shuffle)."""
    F_obs = hand_granger_F(y, x, lag)
    if not np.isfinite(F_obs):
        return F_obs, float("nan")
    rng = np.random.default_rng(seed)
    surrogate_F = []
    for _ in range(N_PHASE_SURROGATES):
        x_s = phase_shuffle(x, rng)
        F_s = hand_granger_F(y, x_s, lag)
        if np.isfinite(F_s):
            surrogate_F.append(F_s)
    if len(surrogate_F) < 50:
        return F_obs, float("nan")
    p = (np.sum(np.array(surrogate_F) >= F_obs) + 1) / (len(surrogate_F) + 1)
    return F_obs, float(p)


def s4_feedback_test(x: np.ndarray, y: np.ndarray) -> tuple[float, float]:
    """Regress ΔX(t+1) = a + b * (Y(t) - mean(Y)) + ε. Return (b, p_b)."""
    if len(x) < 5:
        return float("nan"), float("nan")
    dx = np.diff(x)
    yc = (y[:-1] - np.mean(y[:-1]))
    if np.std(yc) == 0:
        return 0.0, 1.0
    b, a = np.polyfit(yc, dx, 1)
    yhat = a + b * yc
    resid = dx - yhat
    n = len(yc)
    if n <= 2:
        return float(b), float("nan")
    se = float(np.sqrt(np.sum(resid ** 2) / (n - 2) / np.sum((yc - yc.mean()) ** 2)))
    if se == 0:
        return float(b), 0.0
    t = b / se
    # two-sided p via normal approx (n typically ~10 so this is rough)
    from math import erf, sqrt
    p = 2 * (1 - 0.5 * (1 + erf(abs(t) / sqrt(2))))
    return float(b), float(p)


# ──────────────────────────────────────────────────────────────────
# §3  Per-window analysis + per-pair aggregation
# ──────────────────────────────────────────────────────────────────

def analyze_window(x: np.ndarray, y: np.ndarray, seed: int) -> dict:
    rho_star, tau_star = s1_s2_max_lag_corr(x, y)
    s1 = abs(rho_star) > RHO_MIN
    s2 = tau_star > 0  # X (left arg) leads Y
    # Cap Granger lag to keep ≥3 dof: max lag = WINDOW_SAMPLES // 5
    lag_for_granger = max(1, min(abs(tau_star), max(2, WINDOW_SAMPLES // 5)))
    F_obs, p_granger = s3_granger_phase_shuffle_p(x, y, lag_for_granger, seed)
    s3 = bool(np.isfinite(p_granger) and p_granger < ALPHA)
    b_fb, p_fb = s4_feedback_test(x, y)
    # Pre-reg §2.3: S4 = significant NEGATIVE coefficient at p<0.05
    s4 = bool(np.isfinite(p_fb) and b_fb < 0 and p_fb < ALPHA)
    # Pre-reg §2.3: U4 = |coef|<0.1 AND p>0.20 (STRICT — middle ground is neither)
    u4 = bool(np.isfinite(p_fb) and abs(b_fb) < 0.1 and p_fb > 0.20)
    return {
        "rho_star": rho_star, "tau_star": int(tau_star),
        "S1": bool(s1), "S2": bool(s2),
        "F_obs": F_obs, "p_granger": p_granger, "S3": s3,
        "b_feedback": b_fb, "p_feedback": p_fb, "S4": s4, "U4": u4,
        "neither_S4_nor_U4": bool(not s4 and not u4),
        # Pre-reg §2.3 line 45: unsupervised-LCC requires S1 ∧ S2 ∧ S3 ∧ U4
        "unsupervised_lcc": bool(s1 and s2 and s3 and u4),
    }


def analyze_pair(x_full: np.ndarray, y_full: np.ndarray,
                 mask_valid: np.ndarray, seed_base: int) -> dict:
    windows = []
    for start in range(0, len(x_full) - WINDOW_SAMPLES + 1, STEP_SAMPLES):
        end = start + WINDOW_SAMPLES
        if not mask_valid[start:end].all():
            continue
        wx = x_full[start:end]; wy = y_full[start:end]
        # detrend (linear) to focus on residual covariation, not shared trend
        t = np.arange(len(wx))
        wx = wx - np.polyval(np.polyfit(t, wx, 1), t)
        wy = wy - np.polyval(np.polyfit(t, wy, 1), t)
        res = analyze_window(wx, wy, seed_base + start)
        res["start_idx"] = start; res["end_idx"] = end
        windows.append(res)
    # D_LCC across windows
    Gs = [w["F_obs"] for w in windows if np.isfinite(w["F_obs"])]
    if len(Gs) >= 2:
        eps = EPSILON_FRAC * float(np.std(Gs))
        d_lcc = sum(1 for k in range(1, len(Gs)) if Gs[k] > Gs[k - 1] + eps) / (len(Gs) - 1)
    else:
        d_lcc = float("nan")
    n_windows = len(windows)
    n_unsup = sum(1 for w in windows if w["unsupervised_lcc"])
    return {
        "n_windows": n_windows,
        "n_unsupervised_lcc_windows": n_unsup,
        "frac_unsupervised_lcc": n_unsup / n_windows if n_windows else float("nan"),
        "D_LCC": d_lcc,
        "windows": windows,
    }


# ──────────────────────────────────────────────────────────────────
# §4  Main
# ──────────────────────────────────────────────────────────────────

def main():
    pre_reg = {
        "WINDOW_yr": WINDOW_SAMPLES * GRID_STEP,
        "STEP_yr": STEP_SAMPLES * GRID_STEP,
        "GRID": [GRID_START, GRID_END, GRID_STEP],
        "RHO_MIN": RHO_MIN, "TAU_MAX_samples": TAU_MAX,
        "N_PHASE_SURROGATES": N_PHASE_SURROGATES, "ALPHA": ALPHA,
        "EPSILON_FRAC": EPSILON_FRAC,
        "SITES": [s["id"] for s in SITES],
        "FILES": {s["id"]: s["file"] for s in SITES},
        "DEVIATIONS_FROM_PRE_REG": [
            "D1: 3 sites instead of 5 (NOAA URL availability constraint)",
            "D2: HOLDOUT N=1 pair (verdict reported as PILOT_PRELIMINARY)",
            "D3: 20-yr common grid (highest-resolution shared resolution)",
            "D4: WINDOW expanded 100→300 yr (5→15 samples) — pre-reg §3 paleo "
            "row specifies τ_max=10 samples, internally inconsistent with §6.2 "
            "100-yr windows = 5 samples (yields dof≤0 for any Granger lag≥1 "
            "after intercept). Lag capped at WINDOW//5=3 (60 yr).",
        ],
        "PROTOCOL_DOC_SHA_PREFIX": hashlib.sha256(
            Path("papers/PASS_49_LCC_PLAIN_FRAMEWORK_SUPERVISED_VS_UNSUPERVISED_2026-05-13.md").read_bytes()
        ).hexdigest()[:16],
    }
    pre_reg_sha = hashlib.sha256(json.dumps(pre_reg, sort_keys=True).encode()).hexdigest()
    print(f"PRE-REG SHA-256: {pre_reg_sha}")

    grid = np.arange(GRID_START + GRID_STEP // 2, GRID_END, GRID_STEP, dtype=float)  # AD 1010, 1030, ...
    series = {}
    print("\n=== Loading + resampling sites to common 20-yr AD-1010..1990 grid ===")
    for s in SITES:
        arr = load_site(s)
        n_total = arr.shape[0]
        if n_total == 0:
            print(f"  {s['id']}: PARSE FAILED — 0 rows")
            continue
        in_window = arr[(arr[:, 0] >= GRID_START) & (arr[:, 0] <= GRID_END)]
        resampled = resample_to_grid(arr, grid)
        n_valid = int(np.isfinite(resampled).sum())
        print(f"  {s['id']}: n_total={n_total} (yr {arr[:,0].min():.0f}..{arr[:,0].max():.0f}); "
              f"in AD-window: {len(in_window)}; resampled-valid: {n_valid}/{len(grid)}")
        series[s["id"]] = resampled

    site_ids = sorted(series.keys())
    if len(site_ids) < 2:
        raise SystemExit("Need ≥2 sites with data")

    pairs = sorted([(a, b) for i, a in enumerate(site_ids) for b in site_ids[i + 1:]])
    print(f"\n=== Pairs (alphabetical, deterministic): {pairs} ===")

    # 60/40 chronological-by-pair-ID split (deterministic)
    n_pairs = len(pairs)
    n_tune = max(1, int(round(n_pairs * 0.6)))
    tune_pairs = pairs[:n_tune]
    hold_pairs = pairs[n_tune:]
    print(f"TUNE pairs ({len(tune_pairs)}): {tune_pairs}")
    print(f"HOLDOUT pairs ({len(hold_pairs)}): {hold_pairs}")

    seed_base = int(pre_reg_sha[:8], 16) % (2**31)

    pair_results = {}
    for i, (a, b) in enumerate(pairs):
        x = series[a]; y = series[b]
        mask = np.isfinite(x) & np.isfinite(y)
        print(f"\n--- pair {a}--{b}: {int(mask.sum())} joint-valid samples ---")
        if int(mask.sum()) < WINDOW_SAMPLES:
            pair_results[f"{a}__{b}"] = {"error": "insufficient overlap"}
            continue
        # restrict to longest contiguous valid stretch
        # (here just use full series with mask check inside analyze_pair)
        res = analyze_pair(x, y, mask, seed_base + i * 1000)
        res["pair"] = [a, b]
        res["split"] = "TUNE" if (a, b) in tune_pairs else "HOLDOUT"
        pair_results[f"{a}__{b}"] = res
        print(f"  windows={res['n_windows']}  unsup-LCC windows={res['n_unsupervised_lcc_windows']}  "
              f"D_LCC={res['D_LCC']:.3f}" if np.isfinite(res.get("D_LCC", np.nan))
              else f"  windows={res['n_windows']}  unsup-LCC windows={res['n_unsupervised_lcc_windows']}  D_LCC=NaN")

    # Aggregation per split
    def agg(pair_list, label):
        d_lccs, fracs = [], []
        for (a, b) in pair_list:
            r = pair_results.get(f"{a}__{b}", {})
            if "D_LCC" in r and np.isfinite(r["D_LCC"]):
                d_lccs.append(r["D_LCC"])
            if "frac_unsupervised_lcc" in r and np.isfinite(r["frac_unsupervised_lcc"]):
                fracs.append(r["frac_unsupervised_lcc"])
        n_pairs_with_unsup = sum(1 for (a, b) in pair_list
                                 if pair_results.get(f"{a}__{b}", {}).get("n_unsupervised_lcc_windows", 0) >= 1)
        return {
            "label": label,
            "n_pairs": len(pair_list),
            "n_pairs_with_any_unsup_window": n_pairs_with_unsup,
            "mean_D_LCC": float(np.mean(d_lccs)) if d_lccs else float("nan"),
            "all_D_LCC": d_lccs,
            "mean_frac_unsup_per_pair": float(np.mean(fracs)) if fracs else float("nan"),
        }

    tune_agg = agg(tune_pairs, "TUNE")
    hold_agg = agg(hold_pairs, "HOLDOUT")

    # Verdict (with D2 caveat)
    if hold_agg["n_pairs"] == 0:
        verdict = "DEGENERATE_NO_HOLDOUT"
    elif hold_agg["n_pairs"] < 4:
        # D2: report tentative
        if (hold_agg["n_pairs_with_any_unsup_window"] >= 1
                and np.isfinite(hold_agg["mean_D_LCC"]) and hold_agg["mean_D_LCC"] > 0.5):
            verdict = "PILOT_PRELIMINARY_TREND_CONFIRM"
        elif (hold_agg["n_pairs_with_any_unsup_window"] >= 1
              and np.isfinite(hold_agg["mean_D_LCC"])):
            verdict = "PILOT_PRELIMINARY_WEAK"
        else:
            verdict = "PILOT_PRELIMINARY_DISCONFIRM"
    else:
        # full pre-reg matrix would apply
        verdict = "FULL_VERDICT_PATH_NOT_TRIGGERED"

    out = {
        "test_id": "L-2_PILOT_paleoclimate_d18O_unsupervised_LCC",
        "pre_reg_sha256": pre_reg_sha,
        "pre_reg_parameters": pre_reg,
        "tune_aggregate": tune_agg,
        "holdout_aggregate": hold_agg,
        "pair_results": pair_results,
        "verdict": verdict,
    }
    OUT_DIR.joinpath("results.json").write_text(json.dumps(out, indent=2, default=str))

    print(f"\n========= L-2 PILOT verdict: {verdict} =========")
    print(f"TUNE:    {tune_agg}")
    print(f"HOLDOUT: {hold_agg}")


if __name__ == "__main__":
    main()
