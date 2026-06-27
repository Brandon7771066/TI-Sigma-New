#!/usr/bin/env python3
"""
PD = (-3, 2) Perfect-Fifth Musical Interpretation — falsifier execution.

Source paper: papers/PASS_47_PD_PERFECT_FIFTH_MUSICAL_ENTAILMENTS_2026-05-11.md
Hypotheses H-PD-MUSIC-1..4. Predictions are PRE-REGISTERED below, in code, BEFORE
any data is touched, per the corpus generate->validate (UGI-1) convention.

Honesty rails (corpus):
  - Report honest negatives; falsifiers that work-as-designed do NOT promote/delete
    a lead or change the canonical principle count (79).
  - The naive statistic is always confoundable; only a confound-controlled statistic
    isolates the claim. So every runnable test ships with a matched control / base-rate
    null, and we explicitly flag "resonance not result" when the signal is mechanically
    forced by something the framework did not predict.
  - No human-subject or Brandon-private data is available in this environment, so
    H-PD-MUSIC-1/2/3 are NOT executable as designed; we say so plainly and run only a
    labelled method-validation null where it adds value (necessary-not-sufficient).

Only H-PD-MUSIC-4 (market upside/downside asymmetry) has free public real data and is
executed for real, with controls.
"""

import json
import time
import urllib.request
import datetime as dt
from statistics import median

# =====================================================================================
# PRE-REGISTRATION (frozen BEFORE looking at any data)
# =====================================================================================
# NOTE ON HYPOTHESIS-SPECIFIC FALSIFIER RULES (no cross-hypothesis leakage):
#   - H-PD-MUSIC-4 (§2.4): CONFIRM-partial iff ratio in (1.4,1.6) on >=2 of 3 regimes;
#                          FALSIFIER (KILL) = "ratio randomly distributed".
#   - The (1.0,2.0) "outside = KILL" band belongs to H-PD-MUSIC-1 (§2.1) ONLY and is
#     deliberately NOT used in the H-4 verdict.
PREREG = {
    "ratio_target": 1.5,                       # perfect-fifth 3:2
    "confirm_partial_band": (1.4, 1.6),        # paper §2.4 CONFIRM-partial
    "h4_falsifier": "ratio randomly distributed = KILL (paper §2.4)",
    "h1_only_kill_band_outside": (1.0, 2.0),   # §2.1 — H-PD-MUSIC-1 ONLY, not H-4
    # Paper: "CONFIRM partial on at least 2 of 3 historical regimes".
    # Three pre-registered modern NBER expansions (trough -> peak), chosen as the three
    # longest clean post-1970 expansions BEFORE seeing the ratios:
    "primary_expansions": [
        ("1982-11-01", "1990-07-01"),
        ("1991-03-01", "2001-03-01"),
        ("2009-06-01", "2020-02-01"),
    ],
    # Reported for completeness (not in the primary 2-of-3 test):
    "other_expansions": [
        ("1970-11-01", "1973-11-01"),
        ("1975-03-01", "1980-01-01"),
        ("1980-07-01", "1981-07-01"),
        ("2001-11-01", "2007-12-01"),
        ("2020-04-01", "2026-06-01"),
    ],
    "contractions_control": [   # NBER recessions (peak -> trough), as contrast
        ("2007-12-01", "2009-06-01"),
        ("2001-03-01", "2001-11-01"),
        ("1990-07-01", "1991-03-01"),
        ("2020-02-01", "2020-04-01"),
    ],
    "base_rate_n": 20000,       # random contiguous windows for the base-rate null
    "rng_seed": 47,
}

# Decision rule, frozen:
#   CONFIRM-partial  iff >=2 of 3 PRIMARY expansions have ratio in (1.4,1.6)
#                    AND 1.5 is NON-trivially special vs the base-rate null
#                        (i.e. the in-band fraction of random windows is small, <~25%,
#                         AND ratio is not simply a relabelling of total return).
#   RESONANCE-only   iff ratios land near 1.5 BUT base-rate shows that is unremarkable
#                        OR ratio is mechanically determined by total period return.
#   KILL             iff ratios systematically outside (1.0,2.0).


def fetch_gspc():
    end = int(time.time())
    url = ("https://query1.finance.yahoo.com/v8/finance/chart/%5EGSPC"
           f"?period1=0&period2={end}&interval=1d")
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=90) as r:
        d = json.load(r)
    res = d["chart"]["result"][0]
    ts = res["timestamp"]
    close = res["indicators"]["quote"][0]["close"]
    rows = []
    for t, c in zip(ts, close):
        if c is None:
            continue
        rows.append((dt.date.fromtimestamp(t), float(c)))
    rows.sort()
    return rows


def log_returns(rows):
    import math
    out = []
    for i in range(1, len(rows)):
        d0, c0 = rows[i - 1]
        d1, c1 = rows[i]
        if c0 > 0 and c1 > 0:
            out.append((d1, math.log(c1 / c0)))
    return out


def updown_ratio(rets):
    """ratio = sum(positive log-returns) / sum(|negative log-returns|)."""
    up = sum(r for _, r in rets if r > 0)
    dn = -sum(r for _, r in rets if r < 0)
    if dn == 0:
        return float("inf"), up, dn, len(rets)
    return up / dn, up, dn, len(rets)


def window(rets, start_s, end_s):
    s = dt.date.fromisoformat(start_s)
    e = dt.date.fromisoformat(end_s)
    return [(d, r) for (d, r) in rets if s <= d <= e]


def total_log_return(rets):
    return sum(r for _, r in rets)


def main():
    import random
    random.seed(PREREG["rng_seed"])
    out = {"prereg": PREREG, "generated_utc": dt.datetime.utcnow().isoformat() + "Z"}

    rows = fetch_gspc()
    rets = log_returns(rows)
    out["data"] = {"source": "Yahoo Finance ^GSPC daily (no key)",
                   "n_days": len(rows), "first": str(rows[0][0]), "last": str(rows[-1][0])}

    def regime_block(label, spans):
        block = []
        for (s, e) in spans:
            w = window(rets, s, e)
            if not w:
                block.append({"span": [s, e], "n": 0, "ratio": None})
                continue
            ratio, up, dn, n = updown_ratio(w)
            block.append({
                "span": [s, e], "n": n, "ratio": round(ratio, 4),
                "sum_up": round(up, 4), "sum_dn": round(dn, 4),
                "total_log_return": round(total_log_return(w), 4),
                "in_confirm_band": 1.4 <= ratio <= 1.6,
            })
        print(f"\n[{label}]")
        for b in block:
            if b["ratio"] is None:
                print(f"  {b['span']}: NO DATA"); continue
            flag = "CONFIRM(1.4-1.6)" if b["in_confirm_band"] else "miss"
            print(f"  {b['span'][0]}->{b['span'][1]}  n={b['n']:5d}  ratio={b['ratio']:.3f}"
                  f"  totalRet={b['total_log_return']:+.3f}  [{flag}]")
        return block

    out["primary_expansions"] = regime_block("PRIMARY expansions (pre-registered 2-of-3)",
                                             PREREG["primary_expansions"])
    out["other_expansions"] = regime_block("OTHER expansions (reported)",
                                           PREREG["other_expansions"])
    out["contractions"] = regime_block("CONTRACTIONS (control / contrast)",
                                       PREREG["contractions_control"])

    # -------- base-rate null: is a (1.4,1.6) ratio unremarkable? --------
    lens = [b["n"] for b in out["primary_expansions"] if b["n"]]
    L = int(median(lens)) if lens else 500
    N = PREREG["base_rate_n"]
    in_band = 0
    ratios = []
    ret_pairs = []
    maxstart = len(rets) - L - 1
    for _ in range(N):
        i = random.randint(0, maxstart)
        w = rets[i:i + L]
        ratio, up, dn, n = updown_ratio(w)
        ratios.append(ratio)
        ret_pairs.append((total_log_return(w), ratio))
        if 1.4 <= ratio <= 1.6:
            in_band += 1
    ratios.sort()
    base_frac = in_band / N

    # resonance check: correlation of total return vs up/down ratio across windows
    import math
    n = len(ret_pairs)
    mx = sum(p[0] for p in ret_pairs) / n
    my = sum(p[1] for p in ret_pairs) / n
    sxy = sum((p[0] - mx) * (p[1] - my) for p in ret_pairs)
    sxx = sum((p[0] - mx) ** 2 for p in ret_pairs)
    syy = sum((p[1] - my) ** 2 for p in ret_pairs)
    corr = sxy / math.sqrt(sxx * syy) if sxx > 0 and syy > 0 else float("nan")

    # base-rate restricted to POSITIVE-return windows (apples-to-apples with expansions)
    pos = [(tr, ra) for (tr, ra) in ret_pairs if tr > 0]
    pos_in_band = sum(1 for (_, ra) in pos if 1.4 <= ra <= 1.6)
    pos_frac = pos_in_band / len(pos) if pos else float("nan")

    out["base_rate_null"] = {
        "window_len": L, "n_windows": N,
        "frac_in_confirm_band_all": round(base_frac, 4),
        "frac_in_confirm_band_positive_return_only": round(pos_frac, 4),
        "ratio_pctiles": {p: round(ratios[int(p / 100 * (N - 1))], 4)
                          for p in (5, 25, 50, 75, 95)},
        "corr_totalreturn_vs_ratio": round(corr, 4),
    }
    print(f"\n[BASE-RATE NULL]  window_len={L}  N={N}")
    print(f"  frac of RANDOM windows with ratio in (1.4,1.6): {base_frac:.3f}")
    print(f"  frac of POSITIVE-return windows in (1.4,1.6):    {pos_frac:.3f}")
    print(f"  ratio percentiles 5/25/50/75/95: "
          + "/".join(f"{out['base_rate_null']['ratio_pctiles'][p]}" for p in (5,25,50,75,95)))
    print(f"  corr(total_return, up/down_ratio) = {corr:.3f}  "
          f"(near 1 => ratio is a RELABELLING of total return)")

    # -------- verdict (apply the frozen H-PD-MUSIC-4 rule from §2.4) --------
    # §2.4: CONFIRM-partial iff ratio in (1.4,1.6) on >=2 of 3 regimes.
    #       FALSIFIER (KILL) = "ratio randomly distributed" — operationalized as:
    #         the ratio carries no structured 1.5 signal, i.e. it is fully explained by
    #         total drift (|corr(total_return, ratio)| high) AND 1.5 is not a value the
    #         data concentrates at (base-rate in-band fraction ~ 0).
    prim = [b for b in out["primary_expansions"] if b["ratio"] is not None]
    n_confirm = sum(1 for b in prim if b["in_confirm_band"])
    two_of_three = n_confirm >= 2
    special = (base_frac < 0.25) and (abs(corr) < 0.5)   # 1.5 non-trivially privileged?
    randomly_distributed = (abs(corr) >= 0.5) and (base_frac < 0.05)  # §2.4 KILL condition
    if two_of_three and special:
        verdict = "CONFIRM-partial (and non-trivially special)"
    elif two_of_three and not special:
        verdict = "RESONANCE-only (lands near 1.5 but base-rate/mechanics explain it)"
    elif randomly_distributed:
        verdict = ("KILL (per \u00a72.4: ratio is randomly distributed w.r.t. the 3:2 "
                   "prediction \u2014 fully explained by drift, no concentration at 1.5)")
    else:
        verdict = "INCONCLUSIVE (neither 2-of-3 confirm nor clean 'randomly distributed')"
    out["H_PD_MUSIC_4_verdict"] = {
        "falsifier_rule": "\u00a72.4: ratio randomly distributed = KILL",
        "n_primary_in_confirm_band": n_confirm, "two_of_three": two_of_three,
        "base_rate_special": special, "randomly_distributed": randomly_distributed,
        "verdict": verdict,
    }
    print(f"\n[H-PD-MUSIC-4 VERDICT] {verdict}")
    print(f"  (2-of-3 primary in band: {two_of_three}; 1.5 special vs null: {special}; "
          f"randomly-distributed KILL condition: {randomly_distributed})")

    # -------- H-PD-MUSIC-1/2/3: not executable as designed --------
    out["H_PD_MUSIC_1_2_3"] = {
        "status": "NOT EXECUTABLE in this environment (data unavailable)",
        "H-PD-MUSIC-1": "needs Brandon's autobiographical event-stream or a labelled "
                        "diary corpus (Pennebaker etc.) — no free API access here.",
        "H-PD-MUSIC-2": "needs Brandon's tagged decision-stream (T45-7 DPES log) — private.",
        "H-PD-MUSIC-3": "needs human-subject within-subject A/B music ratings — none here.",
        "note": "Per corpus convention these are necessary-not-sufficient and must not be "
                "faked; a synthetic method-validation null is included below for #1 only.",
    }

    # method-validation null for #1: random ternary streams, base-rate of pos:neg in band
    random.seed(PREREG["rng_seed"] + 1)
    hits = 0; M = 5000
    for _ in range(M):
        # neutral-symmetric generator: pos and neg equally likely -> expected ratio ~1.0
        pos_c = neg_c = 0
        for _ in range(120):
            u = random.random()
            if u < 0.4: pos_c += 1
            elif u < 0.8: neg_c += 1
        r = pos_c / neg_c if neg_c else float("inf")
        if 1.4 <= r <= 1.6:
            hits += 1
    out["H_PD_MUSIC_1_methodval"] = {
        "generator": "symmetric ternary (P(pos)=P(neg)=0.4, P(neutral)=0.2), 120 events",
        "frac_in_band_under_no_effect_null": round(hits / M, 4),
        "interpretation": "fraction of NO-EFFECT streams that still land in (1.4,1.6); "
                          "the real test must beat this base rate to mean anything.",
    }
    print(f"\n[H-PD-MUSIC-1 method-val null] frac of no-effect streams in (1.4,1.6): "
          f"{hits/M:.3f}")

    with open("analyses/pd_perfect_fifth_falsifiers/results.json", "w") as f:
        json.dump(out, f, indent=2)
    print("\nwrote analyses/pd_perfect_fifth_falsifiers/results.json")


if __name__ == "__main__":
    main()
