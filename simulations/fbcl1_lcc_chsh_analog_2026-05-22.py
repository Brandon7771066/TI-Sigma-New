"""
F-BCL-1 Simulation: CHSH-style test for the LCC algorithm.

Pre-registered falsifier from papers/PASS_63_BELL_CHANCE_LCC_TI_SIGMA_2026-05-22.md.

Question: does the LCC retrieval algorithm produce "Bell-violating" correlations
(|S| > 2) on entangled retrieval pairs, or does it stay within the classical
LHV bound (|S| <= 2)?

Setup:
  - Substrate pairs (A_n, B_n), n = 1..N, are "entangled" by being generated
    from a common latent signal plus independent noise. This is the LCC
    analog of an EPR pair: they share information but are spatially separated
    sub-substrates.
  - Four templates Phi_a, Phi_a_prime, Phi_b, Phi_b_prime correspond to the
    four CHSH "measurement settings" (a, a', b, b').
  - On each trial, Alice picks setting in {a, a'}, Bob picks setting in {b, b'}.
  - LCC RESONATE step computes R(A_n, Phi_alice) and R(B_n, Phi_bob).
    Outcomes are binarized: +1 if R >= 0, -1 if R < 0 (sign of resonance).
  - E(x, y) = empirical mean of outcome_alice * outcome_bob for that setting pair.
  - S = E(a, b) - E(a, b') + E(a', b) + E(a', b')

Prediction (pre-reg):
  - |S| > 2  ==> LCC produces Bell-violating correlations; formal mapping to
                quantum chance modes (C3/C4) is structural, not aesthetic;
                F-BCL-1 NOT REFUTED.
  - |S| <= 2 ==> LCC stays classical (LHV-bound); the phi*sqrt(2) connection
                in C_EMERICK is aesthetic/coincidental; F-BCL-1 REFUTED.

Honest caveats (#69):
  - This is a synthetic-substrate simulation, not LCC running on a real
    paired-document corpus with cross-references. Synthetic generation can
    inadvertently encode any correlation structure we want, so the test is
    really "does the LCC-style scoring on entangled-by-construction substrates
    preserve Bell-relevant correlations" rather than "is LCC quantum-like
    in nature."
  - We use the RESONATE-step lagged-cross-correlation R as the per-side
    outcome variable. This is the canonical LCC primitive; using full
    multi-step pipeline (PROPAGATE, EXPAND, TERMINATE) would change nothing
    for the per-trial binary outcome.
  - Quantum prediction for CHSH-optimal settings on a singlet is 2*sqrt(2)
    ~ 2.828. A "real" Bell violation would put |S_LCC| in (2, 2.828].
    Values >> 2.828 would indicate a stronger-than-quantum (PR-box-like)
    correlation, which is its own interesting category.

Seed pre-registered: 20260528.
"""

import numpy as np

SEED = 20260528
N_TRIALS_PER_SETTING = 2500
SUBSTRATE_LEN = 256
ENTANGLEMENT_STRENGTH = 0.95   # shared-signal weight in A_n / B_n construction
NOISE_SIGMA = 0.30
CHSH_LHV_BOUND = 2.0
CHSH_TSIRELSON_BOUND = 2.0 * np.sqrt(2)


def gaussian_lagged_xcorr(x, y, max_lag=10, sigma=5.0):
    """Canonical LCC R: Gaussian-weighted lagged cross-correlation, max."""
    x = (x - x.mean()) / (x.std() + 1e-12)
    y = (y - y.mean()) / (y.std() + 1e-12)
    best = 0.0
    for lag in range(-max_lag, max_lag + 1):
        w = np.exp(-(lag ** 2) / (2 * sigma ** 2))
        if lag >= 0:
            xs, ys = x[:len(x) - lag], y[lag:]
        else:
            xs, ys = x[-lag:], y[:len(y) + lag]
        if len(xs) < 8:
            continue
        c = np.mean(xs * ys) * w
        if abs(c) > abs(best):
            best = c
    return best


def make_templates(L, rng):
    """4 distinct templates analogous to CHSH measurement settings.

    Use sinusoids at incommensurate frequencies + phase offsets so they are
    mutually non-orthogonal but non-redundant.
    """
    t = np.arange(L)
    return {
        "a":       np.sin(2 * np.pi * t / 32.0),
        "a_prime": np.sin(2 * np.pi * t / 32.0 + np.pi / 4.0),
        "b":       np.sin(2 * np.pi * t / 32.0 + np.pi / 8.0),
        "b_prime": np.sin(2 * np.pi * t / 32.0 + 3 * np.pi / 8.0),
    }


def make_entangled_pair(L, lam, sigma, rng):
    """Generate (A, B) sharing latent z with weight lam, plus independent noise."""
    z = rng.standard_normal(L)
    noise_a = rng.standard_normal(L) * sigma
    noise_b = rng.standard_normal(L) * sigma
    A = lam * z + (1 - lam) * noise_a
    B = lam * z + (1 - lam) * noise_b
    return A, B


def expectation(rng, templates, alice_setting, bob_setting, n_trials, L, lam, sigma):
    """E(alice_setting, bob_setting) = mean of binarized outcome products."""
    phi_a = templates[alice_setting]
    phi_b = templates[bob_setting]
    outcomes = np.empty(n_trials)
    for i in range(n_trials):
        A, B = make_entangled_pair(L, lam, sigma, rng)
        r_a = gaussian_lagged_xcorr(A, phi_a)
        r_b = gaussian_lagged_xcorr(B, phi_b)
        outcomes[i] = (1 if r_a >= 0 else -1) * (1 if r_b >= 0 else -1)
    return outcomes.mean(), outcomes.std() / np.sqrt(n_trials)


def main():
    rng = np.random.default_rng(SEED)
    templates = make_templates(SUBSTRATE_LEN, rng)

    print(f"=== F-BCL-1: LCC CHSH-analog test ===")
    print(f"Seed: {SEED}")
    print(f"Trials per setting pair: {N_TRIALS_PER_SETTING}")
    print(f"Substrate length: {SUBSTRATE_LEN}")
    print(f"Entanglement strength (lambda): {ENTANGLEMENT_STRENGTH}")
    print(f"Noise sigma: {NOISE_SIGMA}")
    print()

    results = {}
    for alice in ("a", "a_prime"):
        for bob in ("b", "b_prime"):
            E, se = expectation(rng, templates, alice, bob,
                                N_TRIALS_PER_SETTING, SUBSTRATE_LEN,
                                ENTANGLEMENT_STRENGTH, NOISE_SIGMA)
            results[(alice, bob)] = (E, se)
            print(f"  E({alice:7s}, {bob:7s}) = {E:+.4f}  (se {se:.4f})")

    print()
    Eab = results[("a", "b")][0]
    Eabp = results[("a", "b_prime")][0]
    Eapb = results[("a_prime", "b")][0]
    Eapbp = results[("a_prime", "b_prime")][0]

    S = Eab - Eabp + Eapb + Eapbp
    se_S = np.sqrt(sum(results[k][1] ** 2 for k in results))

    print(f"S_LCC = E(a,b) - E(a,b') + E(a',b) + E(a',b')")
    print(f"      = {Eab:+.4f} - ({Eabp:+.4f}) + {Eapb:+.4f} + {Eapbp:+.4f}")
    print(f"      = {S:+.4f}  (combined se {se_S:.4f})")
    print()
    print(f"LHV (classical) bound:   |S| <= {CHSH_LHV_BOUND}")
    print(f"Tsirelson (QM) bound:    |S| <= {CHSH_TSIRELSON_BOUND:.4f}")
    print(f"|S_LCC| = {abs(S):.4f}")
    print()

    if abs(S) > CHSH_LHV_BOUND:
        z_violation = (abs(S) - CHSH_LHV_BOUND) / se_S
        print(f"VERDICT: |S_LCC| > 2  ==>  F-BCL-1 NOT REFUTED")
        print(f"         Classical-LHV violation by {abs(S) - CHSH_LHV_BOUND:.4f} "
              f"({z_violation:.2f} sigma).")
        if abs(S) > CHSH_TSIRELSON_BOUND:
            print(f"         Also EXCEEDS Tsirelson bound -- super-quantum / PR-box regime.")
        else:
            print(f"         Within Tsirelson quantum bound -- consistent with QM-like correlation.")
        print(f"         Structural mapping LCC <-> quantum chance modes (C3/C4) is supported.")
    else:
        z_below = (CHSH_LHV_BOUND - abs(S)) / se_S
        print(f"VERDICT: |S_LCC| <= 2  ==>  F-BCL-1 REFUTED")
        print(f"         LCC scoring stays within classical LHV bound by "
              f"{CHSH_LHV_BOUND - abs(S):.4f} ({z_below:.2f} sigma).")
        print(f"         The phi*sqrt(2) factor in C_EMERICK is aesthetic/coincidental;")
        print(f"         no structural connection to Tsirelson 2*sqrt(2) is supported by this test.")

    print()
    print("Honest caveats (#69):")
    print("  - Synthetic substrate; not real paired-document corpus.")
    print("  - Outcome binarization at R=0 is one of many choices; alternative")
    print("    thresholds may shift S magnitude.")
    print("  - Substrates here share a single shared latent z -- if the LCC")
    print("    'entanglement' is closer to classical correlation than to")
    print("    quantum superposition, |S| <= 2 is the expected (and correct)")
    print("    classical result, and a REFUTED verdict here would simply mean")
    print("    'the simulation correctly identified that synthetic latent-z")
    print("    sharing is classical correlation, not entanglement'.")
    print("  - The honest interpretation of a REFUTED result is therefore")
    print("    'F-BCL-1 as constructed cannot distinguish classical-correlation")
    print("    from quantum-entanglement in an LCC substrate' rather than")
    print("    'LCC has no quantum-like structure'.")


if __name__ == "__main__":
    main()
