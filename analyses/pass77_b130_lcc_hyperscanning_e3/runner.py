"""
Pass-77 B130 — LCC Virus Hyperscanning EEG (URB-620 §6 test E3), EXECUTED as a
method-validation / power simulation (NO real two-headset EEG data exists).

What this DOES test (and all it can):
  Given the LCC-Virus generative prediction -- a high-GILE-L "carrier" brain
  directionally entrains a low-GILE-L "host" brain's 40 Hz gamma -- can the
  proposed analysis (directed inter-brain Granger causality + phase-slope index)
  (1) RECOVER the predicted asymmetry GC(high->low) > GC(low->high) at the stated
      N=20 dyads with adequate statistical power, AND
  (2) correctly return NULL under no-coupling AND under a shared-environment
      common-input confound (high coherence, zero true direction), AND
  (3) NOT be fooled into spurious directionality by an SNR asymmetry between the
      two head-sets (asymmetric sensor noise -- the classic Granger-causality
      confound) -- a guard a real lab must pass before any human claim is credible.

What this CANNOT do (#69, Constructive-Honesty floor):
  It uses NO human data. A positive result here is a *necessary, not sufficient*
  condition: it shows the experiment is well-posed and adequately powered and the
  estimator is unbiased under a clean model -- it does NOT show the LCC Virus is
  real in human brains. LCC is the corpus's most empirically fragile claim
  (raw-token substrate FALSIFIED in URB-795; survived only in hidden-state
  activations). This is a pre-registration-grade design+power check, nothing more.

Pure numpy/scipy (statsmodels unavailable). Deterministic (seeded).
"""

import json
import time
import hashlib
import numpy as np
from scipy import signal

# ----------------------------------------------------------------------------- 
# Generative model: two noise-driven 40 Hz gamma resonators (AR(2)), optionally
# coupled directionally with a transmission lag. lfilter (C-fast) keeps it cheap.
# -----------------------------------------------------------------------------
FS = 250.0          # EEG sample rate (Hz)
F0 = 40.0           # gamma carrier (Hz)
POLE_R = 0.92       # resonator sharpness (closer to 1 = narrower gamma peak)
T_SEC = 8.0         # epoch length per dyad (s)
N_SAMP = int(T_SEC * FS)
GC_LAG = 6          # VAR model order (samples) for Granger fit
TX_LAG = 5          # neural transmission lag high->low (samples, ~20 ms)
BAND = (30.0, 50.0) # gamma band for the phase-slope index


def _resonator_coefs(fs=FS, f0=F0, r=POLE_R):
    w0 = 2.0 * np.pi * f0 / fs
    a1 = 2.0 * r * np.cos(w0)
    a2 = -(r ** 2)
    # AR(2): x[t] = a1 x[t-1] + a2 x[t-2] + e[t]  ->  lfilter den = [1,-a1,-a2]
    return np.array([1.0, -a1, -a2])


_DEN = _resonator_coefs()


def gen_dyad(rng, c_h2l, sigma_high=1.0, sigma_low=1.0, common=0.0, tx_lag=TX_LAG):
    """Generate one dyad's two gamma channels (purely feed-forward => fast & clean).

    c_h2l  : DIRECTIONAL coupling high -> low (the LCC-Virus drive of interest)
    sigma_high/low : innovation (noise) std per channel -> sets per-channel SNR
    common : strength of a SHARED 40 Hz driver injected into BOTH channels with
             NO inter-brain link -> models a shared environment/sensory input.
             This is the critical hyperscanning confound: it produces strong
             inter-brain COHERENCE but ZERO true directional flow, so a valid
             directed estimator must return ~0 net asymmetry here.
    """
    n = N_SAMP + 200  # warmup pad
    e_high = rng.standard_normal(n) * sigma_high
    e_low = rng.standard_normal(n) * sigma_low

    drive_high = e_high.copy()
    drive_low = e_low.copy()

    if common != 0.0:
        e_shared = rng.standard_normal(n)
        drive_high += common * e_shared
        drive_low += common * e_shared

    # Intrinsic high resonator.
    x_high = signal.lfilter([1.0], _DEN, drive_high)

    # Low = own resonator + lagged directional drive from high.
    if c_h2l != 0.0:
        drive_low[tx_lag:] += c_h2l * x_high[:-tx_lag]
    x_low = signal.lfilter([1.0], _DEN, drive_low)

    return x_high[200:], x_low[200:]


# -----------------------------------------------------------------------------
# Estimator 1: bivariate time-domain Granger causality (log variance ratio).
# -----------------------------------------------------------------------------
def _lagmat(y, p):
    n = len(y)
    return np.column_stack([y[p - k - 1:n - k - 1] for k in range(p)])


def granger(x, y, p=GC_LAG):
    """GC(x->y): does past of x improve prediction of y beyond y's own past?
    Returns ln(SSR_restricted / SSR_full)  (>0 => x Granger-causes y)."""
    n = len(y)
    target = y[p:]
    Yp = _lagmat(y, p)
    Xp = _lagmat(x, p)

    def ssr(design):
        D = np.column_stack([np.ones(len(target)), design])
        # Normal-equations least squares (much faster than SVD lstsq; tiny ridge
        # keeps G well-conditioned). SSR = y'y - beta'(D'y).
        G = D.T @ D
        G[np.diag_indices_from(G)] += 1e-8
        Dy = D.T @ target
        beta = np.linalg.solve(G, Dy)
        return float(target @ target - beta @ Dy)

    ssr_r = ssr(Yp)               # restricted: y past only
    ssr_f = ssr(np.column_stack([Yp, Xp]))  # full: y + x past
    ssr_f = max(ssr_f, 1e-12)
    return np.log(ssr_r / ssr_f)


def delta_gc(x_high, x_low):
    """Net directional GC: positive => high drives low (LCC-Virus prediction)."""
    return granger(x_high, x_low) - granger(x_low, x_high)


# -----------------------------------------------------------------------------
# Estimator 2: Phase Slope Index (Nolte et al. 2008) over gamma band.
# Robust to SNR asymmetry / volume conduction. Sign convention here is fixed so
# that PSI(high, low) > 0 => HIGH leads LOW (i.e. carrier -> host), CALIBRATED
# against the known-truth directional condition (the raw Im(.) slope from scipy's
# csd convention runs opposite, so we negate to make the convention explicit).
# -----------------------------------------------------------------------------
def psi(x_high, x_low, fs=FS, band=BAND):
    nper = int(fs * 2)  # 2 s segments
    f, Shh = signal.csd(x_high, x_high, fs=fs, nperseg=nper)
    _, Sll = signal.csd(x_low, x_low, fs=fs, nperseg=nper)
    _, Shl = signal.csd(x_high, x_low, fs=fs, nperseg=nper)
    coh = Shl / np.sqrt(np.maximum(Shh.real * Sll.real, 1e-20))
    sel = (f >= band[0]) & (f <= band[1])
    idx = np.where(sel)[0]
    idx = idx[idx + 1 <= np.where(sel)[0].max()]
    val = np.sum(np.conj(coh[idx]) * coh[idx + 1]).imag
    return -float(val)  # negate => positive means HIGH leads (carrier -> host)


# -----------------------------------------------------------------------------
# Experiment: one cohort of N dyads under a condition; return per-dyad metrics.
# Per-dyad heterogeneity: coupling and noise jittered.
# -----------------------------------------------------------------------------
def run_cohort(rng, n_dyads, c_h2l, common=0.0, sensor_high=0.0, sensor_low=0.0,
               with_psi=True):
    """One cohort of n_dyads. sensor_high/low add ASYMMETRIC measurement (headset)
    white noise AFTER signal generation, scaled to each channel's own std -- this
    is the genuine SNR confound (unequal observation-noise floor between the two
    head-sets), the classic artifact that fakes Granger directionality toward the
    cleaner channel. (Distinct from process variance: the neural source is
    unchanged; only the sensor noise floor differs.)  with_psi=False skips the
    (costly) phase-slope index in the power/FPR loops, which only need delta_GC."""
    dgc, psis = [], []
    for _ in range(n_dyads):
        ch = max(0.0, c_h2l * (1.0 + 0.25 * rng.standard_normal())) if c_h2l else 0.0
        xh, xl = gen_dyad(rng, ch, common=common)
        if sensor_high:
            xh = xh + sensor_high * np.std(xh) * rng.standard_normal(len(xh))
        if sensor_low:
            xl = xl + sensor_low * np.std(xl) * rng.standard_normal(len(xl))
        dgc.append(delta_gc(xh, xl))
        if with_psi:
            psis.append(psi(xh, xl))
    return np.array(dgc), (np.array(psis) if with_psi else None)


def one_sample_t(vals):
    m = float(np.mean(vals))
    sd = float(np.std(vals, ddof=1))
    se = sd / np.sqrt(len(vals))
    t = m / se if se > 0 else 0.0
    # two-sided p via normal approx (n=20 fine for headline; power uses empirical)
    from math import erf, sqrt
    p = 2.0 * (1.0 - 0.5 * (1.0 + erf(abs(t) / sqrt(2))))
    return m, sd, t, p


def boot_ci(vals, rng, reps=2000):
    n = len(vals)
    means = np.array([np.mean(vals[rng.integers(0, n, n)]) for _ in range(reps)])
    return float(np.percentile(means, 2.5)), float(np.percentile(means, 97.5))


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
def main():
    t0 = time.time()
    SEED = 20260624
    N_DYADS = 20
    ALPHA = 0.01
    C_MAIN = 0.15  # plausible directional coupling for the named-condition demo

    cfg = dict(fs=FS, f0=F0, pole_r=POLE_R, t_sec=T_SEC, gc_lag=GC_LAG,
               tx_lag=TX_LAG, band=BAND, n_dyads=N_DYADS, alpha=ALPHA,
               c_main=C_MAIN, seed=SEED)
    cfg_hash = hashlib.sha256(json.dumps(cfg, sort_keys=True).encode()).hexdigest()[:12]

    rng = np.random.default_rng(SEED)
    results = {"config": cfg, "config_sha": cfg_hash, "conditions": {}, "power": {}}

    # --- Named conditions, one N=20 cohort each ------------------------------
    conditions = {
        "directional_LCC":   dict(c_h2l=C_MAIN),
        "common_input":      dict(c_h2l=0.0, common=0.8),
        "no_coupling":       dict(c_h2l=0.0),
        # genuine SNR confound: carrier headset clean, host headset 1.5x noisier.
        "snr_confound":      dict(c_h2l=0.0, sensor_high=0.1, sensor_low=1.5),
    }
    for name, kw in conditions.items():
        dgc, ps = run_cohort(rng, N_DYADS, **kw)
        m, sd, t, p = one_sample_t(dgc)
        lo, hi = boot_ci(dgc, rng)
        pm, psd, pt, pp = one_sample_t(ps)
        results["conditions"][name] = dict(
            params=kw,
            delta_gc_mean=m, delta_gc_sd=sd, delta_gc_t=t, delta_gc_p=p,
            delta_gc_ci95=[lo, hi],
            psi_mean=pm, psi_t=pt, psi_p=pp,
            reject_dGC=bool(p < ALPHA and m > 0),
        )

    # --- Empirical power / false-positive rate: repeat the whole N=20 study ---
    def wilson_ci(k, n, z=1.96):
        """95% Wilson score interval for a binomial proportion."""
        if n == 0:
            return [0.0, 0.0]
        p = k / n
        d = 1 + z * z / n
        c = p + z * z / (2 * n)
        h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
        return [round((c - h) / d, 4), round((c + h) / d, 4)]

    def reject_rate(reps, require_positive, **kw):
        hits = 0
        for _ in range(reps):
            dgc, _ = run_cohort(rng, N_DYADS, with_psi=False, **kw)
            _, _, _, p = one_sample_t(dgc)
            if p < ALPHA and (np.mean(dgc) > 0 or not require_positive):
                hits += 1
        return dict(rate=round(hits / reps, 4), n_reps=reps, hits=hits,
                    wilson_ci95=wilson_ci(hits, reps))

    REPS = 1000
    results["power"]["directional_C0.15_power"] = reject_rate(REPS, True, c_h2l=C_MAIN)
    results["power"]["no_coupling_FPR"] = reject_rate(REPS, False, c_h2l=0.0)
    results["power"]["common_input_FPR"] = reject_rate(REPS, False, c_h2l=0.0, common=0.8)
    results["power"]["snr_confound_FPR"] = reject_rate(
        REPS, False, c_h2l=0.0, sensor_high=0.1, sensor_low=1.5)

    # --- Power curve over coupling strength ----------------------------------
    curve = {}
    for c in [0.0, 0.06, 0.10, 0.15, 0.20, 0.30]:
        curve[f"{c:.2f}"] = reject_rate(150, True, c_h2l=c)["rate"]
    results["power"]["power_curve_vs_C"] = curve

    # --- HRV / LCC surrogate downstream prediction: NOT simulated -------------
    # URB-620 E3 also predicts a >=15% rise in a host HRV/LCC surrogate. We do
    # NOT fabricate a number: no HRV generative model is included, and deriving a
    # % from the EEG drive would be circular. Flagged out-of-scope (honesty #69).
    results["hrv_surrogate"] = dict(
        status="NOT_SIMULATED",
        note=("URB-620 E3 predicts >=15% host HRV/LCC-surrogate uplift; left out "
              "of scope because no independent HRV generative model exists here -- "
              "any % would be model-baked/circular. Recover-the-drive (delta_GC) "
              "is the part this package validates."),
        urb620_target_pct=15.0,
    )

    results["runtime_sec"] = round(time.time() - t0, 1)
    with open("analyses/pass77_b130_lcc_hyperscanning_e3/results.json", "w") as f:
        json.dump(results, f, indent=2)

    # Console summary
    print(f"[config_sha {cfg_hash}]  runtime {results['runtime_sec']}s\n")
    print("Named conditions (N=20 dyads), net directional GC = GC(high->low) - GC(low->high):")
    for name, r in results["conditions"].items():
        print(f"  {name:16s} dGC={r['delta_gc_mean']:+.4f} "
              f"CI[{r['delta_gc_ci95'][0]:+.4f},{r['delta_gc_ci95'][1]:+.4f}] "
              f"p={r['delta_gc_p']:.2e}  PSI_mean={r['psi_mean']:+.3f}(p={r['psi_p']:.2e})  "
              f"reject={r['reject_dGC']}")
    print(f"\nEmpirical power / false-positive rate (alpha={ALPHA}, 2-sided + sign):")
    for k in ["directional_C0.15_power", "no_coupling_FPR", "common_input_FPR", "snr_confound_FPR"]:
        r = results['power'][k]
        print(f"  {k:28s} {r['rate']:.3f}  Wilson95={r['wilson_ci95']}  (n={r['n_reps']})")
    print("\nPower curve vs directional coupling C:")
    for c, pw in results["power"]["power_curve_vs_C"].items():
        print(f"  C={c}  power={pw:.3f}")
    print(f"\nHRV/LCC surrogate: {results['hrv_surrogate']['status']} "
          f"(URB-620 target >=15%, left out of scope -- see results.json)")


if __name__ == "__main__":
    main()
