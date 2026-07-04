"""
Analysis for the FAITHFUL GILE-based UOP abstention test on TruthfulQA MC1.

Pipeline (canonical TI Sigma operationalization, URB #652 + GILE_WEIGHT_DERIVATION):
  1. Each option has 16 rubric sub-dimension scores in [0,1] (from gile_score.py).
  2. Dimension = mean of its 4 sub-dimensions:
       G = mean(C1..C4), I = mean(I1..I4), L = mean(L1..L4), E = mean(E1..E4).
  3. MR1 gate: an option is truth-assessable iff G_raw >= ET = sqrt(2)-1 ~= 0.4142,
     else it is MI-adjacent (fails MR1). (URB #652 also describes an L-guard: L3 < ET
     with high L1/L2 flags an MI-contaminated love-signature; it is diagnostic only and
     is neither computed nor gated here, since selection is on the GILE composite.)
  4. Domain-weighted GILE composite per option: GILE = wG*G + wI*I + wL*L + wE*E.
     TruthfulQA is an epistemic / factual-truth domain -> primary profile = SCIENTIFIC
     (G .35, I .40, L .15, E .10), the success-simulation-derived weights that weight
     inferential accuracy highest. All other canonical profiles reported as robustness.
  5. Selection: pick the MR1-passing option with the MAX GILE composite. If NO option
     passes MR1 -> abstain (MI-adjacent question). is_correct = pick == mc1 answer.
  6. UOP test: does penalizing GILE composites above the Radiant Cap
     G* = sqrt(1-e^-2) ~= 0.92987 improve selective prediction over ranking by the raw
     GILE composite? Plus the scrambled-cap ablation (is G* special?), the high-GILE
     tail accuracy (mechanism), and an asymmetric-cost OOS decision test.

As with any risk-coverage analysis, AURC depends only on the RANKING of the retained
score, so the cap can only act through its NON-monotone demotion of >cap composites.
"""
import os, json, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SCORES = os.path.join(HERE, "gile_scores.jsonl")
RES = os.path.join(HERE, "gile_results.json")

ET = math.sqrt(2) - 1          # 0.41421... MR1 gate on G_raw
CAP = math.sqrt(1 - math.exp(-2))  # 0.92987... Radiant Cap

PROFILES = {
    "scientific": {"G": 0.35, "I": 0.40, "L": 0.15, "E": 0.10},   # PRIMARY (epistemic)
    "universal":  {"G": 0.25, "I": 0.25, "L": 0.25, "E": 0.25},
    "canonical":  {"G": 0.4142, "I": 0.25, "L": 0.18, "E": 0.15},
    "clinical":   {"G": 0.25, "I": 0.15, "L": 0.50, "E": 0.10},
    "engineering":{"G": 0.30, "I": 0.20, "L": 0.10, "E": 0.40},
    "social":     {"G": 0.20, "I": 0.20, "L": 0.45, "E": 0.15},
}
PRIMARY = "scientific"


def dims(r):
    G = np.mean([r["C1"], r["C2"], r["C3"], r["C4"]])
    I = np.mean([r["I1"], r["I2"], r["I3"], r["I4"]])
    L = np.mean([r["L1"], r["L2"], r["L3"], r["L4"]])
    E = np.mean([r["E1"], r["E2"], r["E3"], r["E4"]])
    return float(G), float(I), float(L), float(E)


def composite(G, I, L, E, w):
    s = w["G"] * G + w["I"] * I + w["L"] * L + w["E"] * E
    return s / (w["G"] + w["I"] + w["L"] + w["E"])  # normalize (canonical sums ~0.994)


def load():
    rows = []
    for line in open(SCORES):
        o = json.loads(line)
        if o.get("error"):
            continue
        rows.append(o)
    return rows


def select(row, profile):
    """Return (chosen_letter or None, chosen_composite or nan, is_correct, abstained)."""
    w = PROFILES[profile]
    best_letter, best_comp, best_G = None, -1.0, None
    for L, r in row["ratings"].items():
        G, I, Lv, E = dims(r)
        if G < ET:  # MR1 gate: MI-adjacent, not truth-assessable
            continue
        comp = composite(G, I, Lv, E, w)
        if comp > best_comp:
            best_comp, best_letter, best_G = comp, L, G
    if best_letter is None:
        return None, float("nan"), 0, True
    return best_letter, best_comp, int(best_letter == row["correct_letter"]), False


def risk_coverage_aurc(score, correct):
    order = np.argsort(-score, kind="stable")
    c = correct[order]
    risk = 1.0 - np.cumsum(c) / np.arange(1, len(c) + 1)
    return float(np.mean(risk))


def uop_score(s, cap, lam=2.0):
    s = np.asarray(s, float).copy()
    over = s > cap
    s[over] = cap - lam * (s[over] - cap) ** 2
    return s


def selective_acc(score, correct, covs=(0.1, 0.2, 0.5, 0.8, 1.0)):
    order = np.argsort(-score, kind="stable")
    c = correct[order]
    n = len(c)
    return {cov: float(np.mean(c[:max(1, int(round(cov * n)))])) for cov in covs}


def utility(correct, mask, cost):
    u = np.where(correct == 1, 1.0, -cost)
    return float(np.sum(u[mask]) / len(correct))


def best_threshold_utility(s_tr, c_tr, s_te, c_te, cost):
    grid = np.unique(np.concatenate([s_tr, [s_tr.min() - 1e-9]]))
    bt, bu = None, -1e9
    for t in grid:
        u = utility(c_tr, s_tr >= t, cost)
        if u > bu:
            bu, bt = u, t
    m = s_te >= bt
    return {"cost": cost, "threshold": float(bt), "test_utility": utility(c_te, m, cost),
            "test_coverage": float(m.mean()),
            "test_selective_acc": float(c_te[m].mean()) if m.any() else float("nan")}


def main():
    rows = load()
    n = len(rows)

    # --- per-profile selection accuracy + MR1 abstention ---
    per_profile = {}
    for prof in PROFILES:
        comps, corrs, abst = [], [], 0
        for row in rows:
            _, comp, ok, ab = select(row, prof)
            if ab:
                abst += 1
                continue
            comps.append(comp)
            corrs.append(ok)
        comps, corrs = np.array(comps, float), np.array(corrs, int)
        per_profile[prof] = {
            "weights": PROFILES[prof],
            "n_answered": int(len(corrs)),
            "n_abstained_MR1": int(abst),
            "selective_accuracy_on_answered": float(corrs.mean()) if len(corrs) else None,
            "coverage": float(len(corrs) / n),
            "mean_gile_composite": float(comps.mean()) if len(comps) else None,
            "n_above_cap": int((comps > CAP).sum()) if len(comps) else 0,
        }

    # --- UOP cap test on the PRIMARY (scientific) profile's GILE composites ---
    comps, corrs = [], []
    for row in rows:
        _, comp, ok, ab = select(row, PRIMARY)
        if ab:
            continue
        comps.append(comp)
        corrs.append(ok)
    comps, corrs = np.array(comps, float), np.array(corrs, int)

    base_aurc = risk_coverage_aurc(comps, corrs)
    uop_aurc = risk_coverage_aurc(uop_score(comps, CAP), corrs)

    caps = np.linspace(0.5, 0.999, 200)
    scr = np.array([risk_coverage_aurc(uop_score(comps, c0), corrs) for c0 in caps])

    hi = comps > CAP
    tail_acc = float(corrs[hi].mean()) if hi.sum() else None

    # asymmetric-cost OOS decision (train/test split)
    rng = np.random.default_rng(20260704)
    idx = rng.permutation(len(comps))
    tr, te = idx[: len(idx) // 2], idx[len(idx) // 2:]
    uop_c = uop_score(comps, CAP)
    decisions = {}
    for cost in (2.0, 4.0, 9.0):
        decisions[f"cost_{cost:g}"] = {
            "P1_gile_threshold": best_threshold_utility(comps[tr], corrs[tr], comps[te], corrs[te], cost),
            "P3_uop": best_threshold_utility(uop_c[tr], corrs[tr], uop_c[te], corrs[te], cost),
        }

    # --- bootstrap CIs (primary profile) : accuracy, baseline AURC, dAURC(uop-base), tail acc ---
    B = 5000
    rng2 = np.random.default_rng(20260704)
    m = len(comps)
    acc_bs, base_bs, duop_bs, tail_bs = [], [], [], []
    uop_all = uop_score(comps, CAP)
    for _ in range(B):
        bi = rng2.integers(0, m, m)
        cc, ss, uu = corrs[bi], comps[bi], uop_all[bi]
        acc_bs.append(cc.mean())
        b_a = risk_coverage_aurc(ss, cc)
        base_bs.append(b_a)
        duop_bs.append(risk_coverage_aurc(uu, cc) - b_a)
        hib = ss > CAP
        tail_bs.append(cc[hib].mean() if hib.any() else np.nan)

    def ci(a):
        a = np.asarray(a, float)
        a = a[~np.isnan(a)]
        return [float(np.percentile(a, 2.5)), float(np.percentile(a, 97.5))]

    bootstrap = {
        "B": B,
        "selective_accuracy_ci95": ci(acc_bs),
        "baseline_aurc_ci95": ci(base_bs),
        "delta_aurc_uop_minus_baseline_ci95": ci(duop_bs),
        "high_gile_tail_accuracy_ci95": ci(tail_bs),
    }

    res = {
        "n_questions": n,
        "ET_MR1_gate": ET,
        "cap_G_star": CAP,
        "primary_profile": PRIMARY,
        "bootstrap_primary": bootstrap,
        "per_profile": per_profile,
        "uop_cap_test_primary": {
            "n_answered": int(len(corrs)),
            "selective_accuracy": float(corrs.mean()) if len(corrs) else None,
            "mean_gile_composite": float(comps.mean()),
            "n_above_cap": int(hi.sum()),
            "aurc_baseline_rank_by_gile": base_aurc,
            "aurc_uop_overreach_penalty": uop_aurc,
            "aurc_uop_minus_baseline": uop_aurc - base_aurc,
            "uop_better": bool(uop_aurc < base_aurc),
            "scrambled_cap_aurc_min": float(scr.min()),
            "scrambled_cap_aurc_mean": float(scr.mean()),
            "scrambled_cap_aurc_max": float(scr.max()),
            "frac_scrambled_caps_better_than_G_star": float((scr < uop_aurc).mean()),
            "high_gile_tail_>cap_accuracy": tail_acc,
            "high_gile_tail_n": int(hi.sum()),
            "extreme_gile_is_anti_predictive": bool(hi.sum() and corrs[hi].mean() < corrs.mean()),
            "selective_acc_baseline": selective_acc(comps, corrs),
            "selective_acc_uop": selective_acc(uop_score(comps, CAP), corrs),
            "asymmetric_cost_decisions": decisions,
        },
    }
    json.dump(res, open(RES, "w"), indent=2)
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
