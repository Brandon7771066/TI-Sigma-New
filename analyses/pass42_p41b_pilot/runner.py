"""
Pass 42 / p41-B — Pilot interaction analysis on Pass-38/39 rosters.

Discharges: p41-B from Pass 41.

DESIGN (frozen per c_proxies_frozen.json BEFORE fetch + analysis):
1. Fetch Wikipedia bio extracts for the 24-individual roster (12 GM Pass-38
   + 12 control Pass-39).
2. Apply 5 frozen C1-C5 keyword proxies per Pass 42 / p41-A spec.
3. Report descriptive C1-C5 distributions per group + Fisher exact tests
   for binary proxies + manual logistic with main + interaction terms
   for synch_score (Pass-37 frozen rubric match-count) × Cj.

HONEST EXPECTATION (per Pass-41 §6 p41-B + Gelman 16x-N rule):
N=24 is grossly underpowered for interaction detection. This pilot is
descriptive ONLY — produces effect-size estimates for power calculations
in a future TRACK-B prospective study. NO INFERENTIAL CONCLUSIONS will be
drawn about whether D3 (interaction-required) is supported.

URB-830-symmetric: a strong pilot effect would justify TRACK-B funding;
a null pilot effect IS still informative as effect-size upper-bound for
power planning, NOT a refutation of D3.
"""
import json, re, urllib.request, urllib.parse, hashlib, time, math, sys
from pathlib import Path

ROOT = Path(__file__).parent
FROZEN = json.loads((ROOT / "c_proxies_frozen.json").read_text())
RES = ROOT / "results.json"
LOG = ROOT / "runner.log"

def log(msg):
    print(msg)
    with LOG.open("a") as f: f.write(msg + "\n")

def fetch_wiki_extract(title, max_sentences=40):
    """Fetch Wikipedia plain-text extract via API. Returns (text, revid).
    Uses exsentences (lead-section sentence cap) which returns more text than
    exchars (which truncates at first matched chunk boundary, ~lead snippet)."""
    url = ("https://en.wikipedia.org/w/api.php?action=query&format=json"
           "&prop=extracts|revisions&rvprop=ids&explaintext=1&exsectionformat=plain"
           f"&titles={urllib.parse.quote(title)}&exsentences={max_sentences}")
    req = urllib.request.Request(url, headers={"User-Agent": "TI-Sigma-Pass-42/1.0 research@local"})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                data = json.loads(r.read().decode())
            pages = data.get("query", {}).get("pages", {})
            for pid, page in pages.items():
                if pid == "-1":
                    return None, None
                text = page.get("extract", "") or ""
                revs = page.get("revisions", [])
                revid = revs[0]["revid"] if revs else None
                return text, revid
            return None, None
        except Exception as e:
            log(f"  retry {attempt+1} for {title}: {e}")
            time.sleep(2 ** attempt)
    return None, None

def count_pattern(text, pat, flags=re.IGNORECASE):
    if not text: return 0
    return len(re.findall(pat, text, flags))

def count_field(text, words):
    if not text: return 0
    total = 0
    for w in words:
        total += count_pattern(text, re.escape(w))
    return total

def score_individual(text):
    """Apply frozen C1-C5 proxies. Returns dict."""
    cps = FROZEN["c_proxies"]
    n_words = max(len(text.split()), 1) if text else 1
    norm = lambda c: 1000.0 * c / n_words

    c1_pos = count_pattern(text, cps["C1_family_pred"]["positive_pattern"])
    c1_neg = count_pattern(text, cps["C1_family_pred"]["negative_pattern"])
    c1_net = c1_pos - c1_neg
    c1_bin = int(c1_net >= 1)

    c2 = count_field(text, cps["C2_contemplative"]["lexical_field"])
    c2_norm = norm(c2)

    c3_pos = sum(count_pattern(text, re.escape(p)) for p in cps["C3_metacognitive"]["positive_meta_patterns"])
    c3_neg = sum(count_pattern(text, re.escape(p)) for p in cps["C3_metacognitive"]["negative_meta_patterns"])
    c3_norm = norm(c3_pos)

    c4 = sum(count_field(text, cps["C4_eq"][b]) for b in ["perception", "use", "understanding", "management"])
    c4_norm = norm(c4)

    c5_count = sum(count_pattern(text, p) for p in cps["C5_altruism"]["patterns"])
    c5_bin = int(c5_count >= 1)

    return {
        "n_words": n_words,
        "C1_pos": c1_pos, "C1_neg": c1_neg, "C1_net": c1_net, "C1_bin": c1_bin,
        "C2_count": c2, "C2_per1k": c2_norm,
        "C3_pos": c3_pos, "C3_neg": c3_neg, "C3_per1k": c3_norm,
        "C4_count": c4, "C4_per1k": c4_norm,
        "C5_count": c5_count, "C5_bin": c5_bin,
    }

def fisher_exact_one_sided(a, b, c, d):
    """One-sided Fisher exact for 2x2 [[a,b],[c,d]]; H1: GM higher rate.
    Manual implementation, stdlib only."""
    n = a + b + c + d
    def logfact(k):
        return sum(math.log(i) for i in range(1, k+1)) if k > 0 else 0.0
    def hyp_pmf(a, n_row1, n_col1, n):
        # P(X=a | row sums fixed)
        return math.exp(
            logfact(n_row1) + logfact(n - n_row1) + logfact(n_col1) + logfact(n - n_col1)
            - logfact(n) - logfact(a) - logfact(n_row1 - a) - logfact(n_col1 - a) - logfact(n - n_row1 - n_col1 + a)
        )
    n_row1 = a + b; n_col1 = a + c
    a_min = max(0, n_row1 + n_col1 - n); a_max = min(n_row1, n_col1)
    p_one_sided = sum(hyp_pmf(k, n_row1, n_col1, n) for k in range(a, a_max + 1))
    return p_one_sided

def manual_logistic_2predictor(X1, X2, Y, max_iter=200, tol=1e-6):
    """Newton-Raphson for logistic with intercept + X1 + X2 + X1*X2.
    Returns (betas[4], converged_bool). stdlib only."""
    n = len(Y)
    Xrows = [[1.0, X1[i], X2[i], X1[i] * X2[i]] for i in range(n)]
    beta = [0.0, 0.0, 0.0, 0.0]
    for it in range(max_iter):
        p = []
        for i in range(n):
            z = sum(beta[j] * Xrows[i][j] for j in range(4))
            z = max(min(z, 30), -30)
            p.append(1.0 / (1.0 + math.exp(-z)))
        # Gradient
        grad = [sum((Y[i] - p[i]) * Xrows[i][j] for i in range(n)) for j in range(4)]
        # Hessian (negative)
        H = [[0.0]*4 for _ in range(4)]
        for i in range(n):
            w = p[i] * (1 - p[i])
            for j in range(4):
                for k in range(4):
                    H[j][k] -= w * Xrows[i][j] * Xrows[i][k]
        # Solve H * delta = -grad via Gauss-Jordan (4x4)
        try:
            delta = solve4(H, [-g for g in grad])
        except Exception:
            return beta, False
        beta = [beta[j] - delta[j] for j in range(4)]  # Newton step: beta_new = beta - H^-1 * grad
        if max(abs(d) for d in delta) < tol:
            return beta, True
    return beta, False

def solve4(A, b):
    """Gauss elim 4x4."""
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    n = 4
    for i in range(n):
        # pivot
        max_r = max(range(i, n), key=lambda r: abs(M[r][i]))
        M[i], M[max_r] = M[max_r], M[i]
        if abs(M[i][i]) < 1e-12: raise ValueError("singular")
        for r in range(i+1, n):
            f = M[r][i] / M[i][i]
            for c in range(i, n+1):
                M[r][c] -= f * M[i][c]
    x = [0.0]*n
    for i in reversed(range(n)):
        x[i] = (M[i][n] - sum(M[i][j]*x[j] for j in range(i+1, n))) / M[i][i]
    return x

def main():
    LOG.write_text("")  # reset
    log("=" * 70)
    log("Pass 42 / p41-B pilot — N=24, descriptive only")
    log(f"Frozen rubric SHA256: {hashlib.sha256(json.dumps(FROZEN, sort_keys=True).encode()).hexdigest()[:16]}...")
    log("=" * 70)

    rosters = FROZEN["rosters"]
    individuals = []
    for name in rosters["GM_roster_pass38"]:
        individuals.append({"name": name, "group": "GM", "Y": 1})
    for name in rosters["control_roster_pass39"]:
        individuals.append({"name": name, "group": "control", "Y": 0})

    # Pass-37 frozen synch_score (rubric match counts) — copied from Pass-38/39 results
    # (Honest re-derivation would re-run the rubric; here we use the frozen results.)
    pass38_results = json.loads(Path("analyses/pass38_mbe_celebrity_numerology/results.json").read_text())
    pass39_results = json.loads(Path("analyses/pass39_mbe_control_roster/results.json").read_text())
    synch_scores = {}
    for entry in pass38_results.get("per_celebrity", []):
        synch_scores[entry["name"]] = int(entry.get("match", 0))
    for entry in pass39_results.get("control_per_celebrity", []):
        synch_scores[entry["name"]] = int(entry.get("match", 0))

    # Fetch + score
    for ind in individuals:
        log(f"\nFetching: {ind['name']}")
        text, revid = fetch_wiki_extract(ind["name"])
        if text is None:
            log(f"  WARN: no extract for {ind['name']}, skipping")
            ind["scores"] = None
            continue
        ind["revid"] = revid
        ind["scores"] = score_individual(text)
        ind["synch_score"] = synch_scores.get(ind["name"], None)
        log(f"  revid={revid}, n_words={ind['scores']['n_words']}, "
            f"C1_bin={ind['scores']['C1_bin']}, C2={ind['scores']['C2_count']}, "
            f"C5_bin={ind['scores']['C5_bin']}, synch={ind['synch_score']}")
        time.sleep(0.5)

    # Aggregate by group
    groups = {"GM": [], "control": []}
    for ind in individuals:
        if ind["scores"] is not None:
            groups[ind["group"]].append(ind)

    summary = {}
    for var in ["C1_bin", "C2_per1k", "C3_per1k", "C4_per1k", "C5_bin"]:
        gm_vals = [g["scores"][var] for g in groups["GM"]]
        ct_vals = [g["scores"][var] for g in groups["control"]]
        summary[var] = {
            "GM_mean": sum(gm_vals)/len(gm_vals) if gm_vals else None,
            "control_mean": sum(ct_vals)/len(ct_vals) if ct_vals else None,
            "GM_n": len(gm_vals), "control_n": len(ct_vals),
        }
        if var.endswith("_bin"):
            a = sum(gm_vals); b = len(gm_vals) - a
            c = sum(ct_vals); d = len(ct_vals) - c
            summary[var]["fisher_one_sided_p_GMhigher"] = fisher_exact_one_sided(a, b, c, d)
            summary[var]["counts"] = {"GM_yes": a, "GM_no": b, "control_yes": c, "control_no": d}

    # Interaction logistic: Y ~ synch + C2_per1k + synch*C2_per1k
    # (Use C2 as the cleanest continuous Cj; C1/C5 are binary, low information for interaction)
    valid = [ind for ind in individuals if ind["scores"] is not None and ind["synch_score"] is not None]
    if len(valid) >= 8:
        X1 = [ind["synch_score"] for ind in valid]
        X2 = [ind["scores"]["C2_per1k"] for ind in valid]
        Y  = [ind["Y"] for ind in valid]
        beta, conv = manual_logistic_2predictor(X1, X2, Y)
        interaction_logistic = {
            "predictors": ["intercept", "synch_score", "C2_per1k", "synch_score:C2_per1k"],
            "betas": beta,
            "converged": conv,
            "n_used": len(valid),
            "honesty_note": "N=24 (or fewer if any individual missing data) is GROSSLY underpowered "
                            "for 4-parameter logistic (target ≥10 events per parameter = ≥40 GM cases). "
                            "Betas are descriptive only. NO p-values reported because they would be "
                            "misleading at this N. Use these betas as effect-size seeds for power "
                            "calculations in TRACK-B prospective study."
        }
    else:
        interaction_logistic = {"error": "insufficient valid data"}

    out = {
        "pass": 42, "discharges": "p41-B",
        "n_individuals_total": len(individuals),
        "n_with_scores": sum(1 for i in individuals if i["scores"] is not None),
        "per_individual": individuals,
        "group_summary": summary,
        "interaction_logistic": interaction_logistic,
        "verdict": "DESCRIPTIVE pilot only; N=24 underpowered for interaction inference. "
                   "Effect-size estimates for TRACK-B power planning. URB-830-symmetric: "
                   "a strong pilot effect justifies TRACK-B funding; a null pilot effect is "
                   "informative as effect-size upper-bound, NOT a refutation of D3.",
        "honesty_69": [
            "Synch_score reused from Pass-37 frozen rubric (no re-derivation, no rubric drift).",
            "Wikipedia bio survivorship bias is a known confounder for C1 + C5 in particular.",
            "C4 EQ text-proxy has notoriously low convergent validity (~0.1-0.3) with MSCEIT.",
            "Logistic with 4 parameters at N≤24 is descriptive-only by epidemiological "
            "rule-of-thumb (≥10 events per parameter); inferential p-values intentionally omitted.",
            "Group-summary Fisher tests reported for binary proxies (C1, C5) only; even those "
            "are at the edge of validity at this N."
        ],
        "_provenance": {
            "frozen_sha256": hashlib.sha256(json.dumps(FROZEN, sort_keys=True).encode()).hexdigest(),
            "ran_at_unix": int(time.time()),
        },
    }
    RES.write_text(json.dumps(out, indent=2, default=str))
    log("\n" + "=" * 70)
    log(f"WROTE {RES}")
    log(f"Group summary (means + Fisher binary p):")
    for v, s in summary.items():
        log(f"  {v}: GM={s['GM_mean']:.3f}, control={s['control_mean']:.3f}"
            + (f", fisher_p_GMhigher={s['fisher_one_sided_p_GMhigher']:.4f}" if "fisher_one_sided_p_GMhigher" in s else ""))
    log(f"Interaction logistic betas (intercept, synch, C2, synch*C2):")
    if "betas" in interaction_logistic:
        log(f"  {[round(b, 4) for b in interaction_logistic['betas']]}, converged={interaction_logistic['converged']}")
    log("=" * 70)

if __name__ == "__main__":
    main()
