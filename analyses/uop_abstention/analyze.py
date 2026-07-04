"""
Analysis for the UOP-vs-baseline abstention experiment on TruthfulQA MC1.

Central honesty point
---------------------
A selective-prediction risk-coverage curve (and its area, AURC) depends ONLY on
the RANKING of examples by their retained-confidence score. Therefore any
strictly MONOTONIC transform of the confidence leaves AURC unchanged. This means:

  * P1 (tuned confidence threshold) and P2 (isotonic-calibrated threshold) share
    the SAME risk-coverage ranking as raw confidence (calibration is monotonic)
    -> identical AURC. Calibration changes the *probabilities*, not the *order*.
  * The UOP over-reach penalty can only differ from a threshold baseline if it is
    NON-monotonic, i.e. it demotes very-high-confidence answers to BELOW the cap.
    That non-monotonic re-ranking is the ONLY thing that can move AURC, and it
    helps IFF extreme confidence is anti-predictive of correctness.

So the real, honest test is: does penalizing over-confidence at the UOP cap
G* = sqrt(1 - e^-2) ~= 0.92987 improve selective prediction, and is that
specific cap special vs. randomly scrambled cap positions (ablation)?

Policies
--------
P0  answer-all (no abstention).
P1  tuned confidence threshold (grid-searched on train, evaluated on test).
P2  isotonic-calibrated probability, tuned threshold (train) / test.
P3  UOP: over-reach penalty at the Radiant Cap G*, tuned threshold / test.
P3-scramble  UOP with randomly scrambled cap (ablation of the specific value).
"""
import os, json, math
import numpy as np
from sklearn.isotonic import IsotonicRegression

HERE = os.path.dirname(os.path.abspath(__file__))
PRED = os.path.join(HERE, "predictions.jsonl")
RES = os.path.join(HERE, "results.json")

CAP = math.sqrt(1 - math.exp(-2))  # 0.92987... Radiant Cap (Born-shaped form)


def load():
    conf, corr = [], []
    for line in open(PRED):
        o = json.loads(line)
        if o.get("error"):
            continue
        conf.append(o["confidence"] / 100.0)
        corr.append(int(o["is_correct"]))
    return np.array(conf, float), np.array(corr, int)


def risk_coverage_aurc(score, correct):
    order = np.argsort(-score, kind="stable")
    c = correct[order]
    n = len(c)
    risk = 1.0 - np.cumsum(c) / np.arange(1, n + 1)
    return float(np.mean(risk))


def selective_acc_at_coverage(score, correct, coverages=(0.1, 0.2, 0.5, 0.8, 1.0)):
    order = np.argsort(-score, kind="stable")
    c = correct[order]
    n = len(c)
    return {cov: float(np.mean(c[:max(1, int(round(cov * n)))])) for cov in coverages}


def uop_score(conf, cap, lam=2.0):
    """UOP over-reach-penalized retained score: monotone rise up to the cap,
    quadratic over-reach penalty above it (non-monotone -> demotes over-confident
    answers below the cap). Below cap identical to raw confidence."""
    s = conf.astype(float).copy()
    over = conf > cap
    s[over] = cap - lam * (conf[over] - cap) ** 2
    return s


def calibration_error(conf, correct, bins=10):
    edges = np.linspace(0, 1, bins + 1)
    ece, n = 0.0, len(conf)
    for b in range(bins):
        lo, hi = edges[b], edges[b + 1]
        m = (conf >= lo) & (conf < hi) if b < bins - 1 else (conf >= lo) & (conf <= hi)
        if m.sum():
            ece += (m.sum() / n) * abs(correct[m].mean() - conf[m].mean())
    return float(ece)


def utility(correct, answer_mask, cost):
    """Asymmetric selective utility: +1 correct, -cost wrong, 0 abstain; mean over all."""
    ans = answer_mask
    u = np.where(correct == 1, 1.0, -cost)
    return float(np.sum(u[ans]) / len(correct))


def best_threshold_utility(score_tr, corr_tr, score_te, corr_te, cost):
    """Grid-search the answer-threshold on train, report test utility + coverage."""
    grid = np.unique(np.concatenate([score_tr, [score_tr.min() - 1e-9]]))
    best_t, best_u = None, -1e9
    for t in grid:
        u = utility(corr_tr, score_tr >= t, cost)
        if u > best_u:
            best_u, best_t = u, t
    mask_te = score_te >= best_t
    return {
        "cost": cost,
        "threshold": float(best_t),
        "test_utility": utility(corr_te, mask_te, cost),
        "test_coverage": float(mask_te.mean()),
        "test_selective_acc": float(corr_te[mask_te].mean()) if mask_te.any() else float("nan"),
    }


def main():
    conf, corr = load()
    n = len(conf)
    rng = np.random.default_rng(20260704)

    # train/test split for threshold-tuning policies
    idx = rng.permutation(n)
    tr, te = idx[: n // 2], idx[n // 2:]

    iso = IsotonicRegression(out_of_bounds="clip", y_min=0, y_max=1)
    iso.fit(conf[tr], corr[tr])
    cal = iso.predict(conf)

    uop = uop_score(conf, CAP)

    res = {
        "n": n,
        "overall_accuracy": float(corr.mean()),
        "mean_confidence": float(conf.mean()),
        "ece_raw": calibration_error(conf, corr),
        "ece_isotonic": calibration_error(cal, corr),
        "cap_G_star": CAP,
        "n_above_cap": int((conf > CAP).sum()),
        # ---- AURC (ranking metric; lower better) ----
        "aurc_P1_raw_threshold": risk_coverage_aurc(conf, corr),
        "aurc_P2_isotonic": risk_coverage_aurc(cal, corr),
        "aurc_P3_uop": risk_coverage_aurc(uop, corr),
        # ---- scrambled-cap ablation ----
    }
    res["aurc_P3_minus_baseline"] = res["aurc_P3_uop"] - res["aurc_P1_raw_threshold"]
    res["uop_better_than_baseline"] = bool(res["aurc_P3_uop"] < res["aurc_P1_raw_threshold"])

    caps = np.linspace(0.5, 0.999, 200)
    scr = np.array([risk_coverage_aurc(uop_score(conf, c0), corr) for c0 in caps])
    res["scrambled_cap_aurc_min"] = float(scr.min())
    res["scrambled_cap_aurc_mean"] = float(scr.mean())
    res["scrambled_cap_aurc_max"] = float(scr.max())
    res["frac_scrambled_caps_better_than_G_star"] = float((scr < res["aurc_P3_uop"]).mean())

    # mechanism: is extreme confidence anti-predictive? (needed for UOP to help)
    hi = conf >= 0.95
    res["high_conf_tail_>=0.95_accuracy"] = float(corr[hi].mean()) if hi.sum() else None
    res["high_conf_tail_n"] = int(hi.sum())
    res["extreme_conf_is_anti_predictive"] = bool(
        hi.sum() and corr[hi].mean() < corr.mean())

    # selective accuracy curves
    res["selective_acc_baseline"] = selective_acc_at_coverage(conf, corr)
    res["selective_acc_uop"] = selective_acc_at_coverage(uop, corr)

    # ---- asymmetric-cost DECISION comparison (test split) ----
    decisions = {}
    for cost in (2.0, 4.0, 9.0):
        decisions[f"cost_{cost:g}"] = {
            "P0_answer_all": {
                "test_utility": utility(corr[te], np.ones(len(te), bool), cost),
                "test_coverage": 1.0,
            },
            "P1_raw_threshold": best_threshold_utility(conf[tr], corr[tr], conf[te], corr[te], cost),
            "P2_isotonic": best_threshold_utility(cal[tr], corr[tr], cal[te], corr[te], cost),
            "P3_uop": best_threshold_utility(uop[tr], corr[tr], uop[te], corr[te], cost),
        }
    res["asymmetric_cost_decisions"] = decisions

    json.dump(res, open(RES, "w"), indent=2)
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
