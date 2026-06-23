"""
Pass-77-B125 — 4 Truth-Axes audit (same battery used to confirm the MR Truth Labels).

The MR Truth LABELS are a categorical alphabet {T,F,I,MI(+N/A)}; they were confirmed
with Fleiss' kappa (reliability), spectrum/discriminant analysis, and information-content
(mutual information / does-each-carry-its-own-information). The 4 Truth AXES are NOT a
categorical alphabet — they are *dimensions* for reading a claim:

  A1 PD-DEGREE        how true the claim is (the real part of the Permissibility Distribution)
  A2 PD-MODALITY      the KIND/size of its shortfall from being simply-true (the imaginary part)
  A3 TAU/DELTA-SEP    gap between "true as stated" (tau) and "actually instantiated in the
                      world" (delta) -- a capacity/principle can be true yet rarely realized
  A4 AUTHORITY-LOAD   how much accepting/rejecting it leans on trusting a source's authority
                      rather than something one can check directly

Because axes are dimensions, the label battery is ADAPTED (not copied) to dimensions:

  (1) RELIABILITY  -> Fleiss' kappa per axis (discretize each axis into its ordinal levels;
                      can 3 independent raters agree on each axis? a near-zero kappa = the
                      axis is not reliably perceivable). NOTE: nominal Fleiss kappa is a
                      conservative FLOOR for ordinal data.
  (2) OWN-INFORMATION / NON-REDUNDANCY -> cross-axis mutual information + correlation, and
                      each axis's UNIQUE variance = 1 - R^2 of regressing it on the other 3.
                      An axis with ~0 unique variance is redundant (does NOT carry its own
                      information). PCA effective rank checks the 4 span a 4-D space.
  (3) SPECTRUM + COVERAGE -> per-axis spread (variance + entropy of the discretized
                      distribution: is the axis a live spectrum or degenerate?); MI(each
                      axis ; gold MR verdict) = how much the axes inform the verdict; and an
                      EXHAUSTIVENESS probe: 3 candidate EXTRA axes (temporal-dependence,
                      scope/generality, observer-subjectivity) are also scored -- if they are
                      largely predictable from the 4 (low unique variance) that SUPPORTS
                      "the 4 cover it"; if a candidate carries large unique info, that is an
                      honest FLAG of a possible coverage gap (mirrors the labels' "any
                      proposed 5th label collapses into the four" test).

#69 HONESTY / DEVIATIONS:
  D1: 3 LLM raters (gpt-4o-mini, claude-haiku-4-5, claude-sonnet-4-5) stand in for humans,
      exactly as in the original label kappa run. A CONFIRM means the axes are operationally
      usable BY LLMs given crisp definitions; it does NOT establish human usability.
  D2: 'gold' MR verdict and intended axis cells are the author's design labels (frozen below),
      used ONLY for the coverage MI and as a sanity check -- raters never see them.
  D3: "comprehensively cover ALL aspects of truth" cannot be PROVEN by any finite battery.
      The strongest honest claim available is: the 4 axes are (a) reliably scorable,
      (b) mutually distinct (each carries unique info), (c) each a live spectrum, and
      (d) no tested candidate extra axis adds large unique information. Gaps, if found,
      are reported, not hidden.
  NO synthetic fallback: if the rater API is unavailable the run ABORTS with an error.

Anti-HARK: prompt + propositions + axis definitions frozen at commit; runner SHA256 logged;
verdicts follow mechanical thresholds set below.
"""
import json, os, time, hashlib, re, math
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

# ---------------------------------------------------------------------------
# Frozen test set. Each prop carries the author's DESIGN intent (gold verdict +
# which axes it is meant to load high on) so we can sanity-check and compute the
# axes->verdict coverage MI. Raters NEVER see these design tags.
# verdict in {T,F,I,MI}; tags subset of {deg,mod,sep,auth} = "loads HIGH here".
# ---------------------------------------------------------------------------
PROPS = [
    # --- crisp brute facts: high degree, low modality, low sep, low authority ---
    ("Water is H2O.", "T", []),
    ("2 + 2 = 4.", "T", []),
    ("The Earth orbits the Sun.", "T", []),
    ("Paris is the capital of France.", "T", []),
    ("Iron is denser than cork.", "T", []),
    ("The square root of 144 is 12.", "T", []),
    # --- crisp false ---
    ("Paris is the capital of Germany.", "F", []),
    ("The Sun orbits the Earth once a day.", "F", []),
    ("3 + 5 = 9.", "F", []),
    ("Humans have 100 chromosomes in total.", "F", []),
    ("Aluminium is a noble gas.", "F", []),
    # --- authority-loaded facts: truth hinges on trusting a source you cannot check yourself ---
    ("The new cancer drug passed its phase-III trial.", "I", ["auth"]),
    ("Yesterday's unemployment figure was 4.1 percent.", "I", ["auth"]),
    ("The defendant was at the scene at 9 p.m.", "I", ["auth"]),
    ("This restaurant's kitchen passed its last health inspection.", "I", ["auth"]),
    ("The bridge was certified safe by the engineering firm.", "I", ["auth"]),
    ("The ancient manuscript is genuine, not a forgery.", "I", ["auth"]),
    ("The lab's reported measurement of the electron mass is correct.", "T", ["auth"]),
    # --- capacity / principle / potential: high tau/delta separability (true as such, partly instantiated) ---
    ("Human beings are capable of extraordinary kindness.", "T", ["sep"]),
    ("People are capable of great cruelty.", "T", ["sep"]),
    ("Every person has the right to be treated with dignity.", "I", ["sep", "mod"]),
    ("Democracies hold their leaders accountable.", "I", ["sep", "mod"]),
    ("Education lifts people out of poverty.", "I", ["sep", "mod"]),
    ("Markets allocate resources efficiently.", "I", ["sep", "mod"]),
    ("Friendship makes life worth living.", "I", ["sep", "mod"]),
    ("Hard work is rewarded.", "I", ["sep", "mod"]),
    # --- strong qualifying modality: true-ish but only in a qualified/partial/context way ---
    ("Sarah is reliable.", "I", ["mod"]),
    ("Coffee is good for you.", "I", ["mod"]),
    ("The movie was a masterpiece.", "I", ["mod"]),
    ("Tomatoes are a vegetable.", "I", ["mod"]),
    ("A whale is a fish.", "F", ["mod"]),
    ("Pluto is a planet.", "I", ["mod"]),
    ("He is tall.", "I", ["mod"]),
    ("The soup is too salty.", "I", ["mod"]),
    # --- genuine indeterminates (open / future / unsettled) ---
    ("There will be a sea battle tomorrow.", "I", ["mod"]),
    ("There are infinitely many twin primes.", "I", []),
    ("It will rain in this city exactly one year from today.", "I", []),
    ("The continuum hypothesis is true.", "I", []),
    ("There exists intelligent life elsewhere in the galaxy.", "I", []),
    ("The stock market will be higher next month.", "I", ["mod"]),
    # --- value / normative claims (high modality + separability) ---
    ("Lying is always wrong.", "I", ["mod", "sep"]),
    ("It is wrong to torture an innocent person for fun.", "T", ["sep"]),
    ("Beauty is in the eye of the beholder.", "I", ["mod"]),
    ("Classical music is better than pop.", "I", ["mod"]),
    # --- paradox / self-cancelling: meta-indeterminate, severe modality ---
    ("This sentence is false.", "MI", ["mod"]),
    ("The set of all sets that do not contain themselves contains itself.", "MI", ["mod"]),
    ("The following statement is true; the previous statement is false.", "MI", ["mod"]),
    ("I am lying right now.", "MI", ["mod"]),
    # --- category errors / non-questions (will read N/A-ish; fold to MI per canon) ---
    ("The number seven is jealous.", "MI", ["mod"]),
    ("Wednesday tastes like the colour blue.", "MI", ["mod"]),
    # --- contested-paradigm claims (authority + modality + indeterminate) ---
    ("Consciousness is purely physical.", "I", ["mod", "auth"]),
    ("Mathematical objects exist independently of minds.", "I", ["mod"]),
    ("Free will is compatible with determinism.", "I", ["mod"]),
    ("The universe had a cause.", "I", ["mod"]),
    # --- everyday checkable facts low on every axis (controls) ---
    ("It is raining outside right now.", "I", []),
    ("The traffic light is red.", "I", []),
    ("This cup contains coffee.", "I", []),
    ("The door is open.", "I", []),
    # --- historical claims (mild authority, mostly settled) ---
    ("World War II ended in 1945.", "T", ["auth"]),
    ("Shakespeare wrote Hamlet.", "T", ["auth"]),
    ("Napoleon died in 1821.", "T", ["auth"]),
]

GOLD = {p[0]: p[1] for p in PROPS}
DESIGN_TAGS = {p[0]: set(p[2]) for p in PROPS}
TEST_SET = [p[0] for p in PROPS]

# 7 axes scored per proposition: 4 canonical + 3 candidate-extra (exhaustiveness probe)
AXES = ["degree", "modality", "sep", "authority", "temporal", "scope", "subjectivity"]
CANONICAL = ["degree", "modality", "sep", "authority"]
EXTRA = ["temporal", "scope", "subjectivity"]

PROMPT_TEMPLATE = (
    "You are an expert rater. For the proposition below, rate it on SEVEN independent "
    "dimensions, each on an integer scale 0-3. Judge each dimension on its OWN terms; they "
    "are meant to be independent.\n\n"
    "1. DEGREE (how true the claim is, as stated): 0=clearly false, 1=leans false, "
    "2=leans true, 3=clearly true.\n"
    "2. MODALITY (how much the claim falls short of being a simple, crisp true/false matter — "
    "vagueness, context-dependence, qualification, self-reference): 0=none (crisp), "
    "1=mild, 2=substantial, 3=severe (paradoxical / only true in a special sense).\n"
    "3. INSTANTIATION-GAP (gap between the claim being true AS STATED and how fully it is "
    "actually realised in the world; capacities/principles can be true yet rarely realised): "
    "0=none (truth and reality coincide), 1=small, 2=moderate, 3=large.\n"
    "4. AUTHORITY-LOAD (how much accepting or rejecting it depends on trusting some source's "
    "authority rather than something you can check yourself): 0=anyone can verify directly, "
    "1=mostly checkable, 2=mostly needs a trusted source, 3=entirely depends on trusting authority.\n"
    "5. TEMPORAL-DEPENDENCE (does its truth value depend on WHEN it is evaluated — future "
    "contingent, changes over time): 0=timeless, 3=strongly time-dependent.\n"
    "6. SCOPE (a single particular fact vs a sweeping universal generalisation): "
    "0=narrow particular, 3=broad universal.\n"
    "7. SUBJECTIVITY (mind-independent fact vs a matter of taste/perspective): "
    "0=fully objective, 3=fully a matter of taste.\n\n"
    "Proposition: \"{prop}\"\n\n"
    "Respond with EXACTLY seven integers 0-3 separated by single spaces, in the order "
    "DEGREE MODALITY INSTANTIATION-GAP AUTHORITY-LOAD TEMPORAL SCOPE SUBJECTIVITY. "
    "Nothing else."
)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def parse_scores(text):
    nums = re.findall(r"[0-3]", text)
    if len(nums) >= 7:
        return [int(x) for x in nums[:7]]
    return None


def call_anthropic(model, prompt):
    from anthropic import Anthropic
    c = Anthropic()
    r = c.messages.create(model=model, max_tokens=30,
                          messages=[{"role": "user", "content": prompt}])
    return r.content[0].text


def call_openai(model, prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
    r = c.chat.completions.create(model=model, max_tokens=30,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content


RATERS = [
    ("gpt_4o_mini", lambda p: call_openai("gpt-4o-mini", p)),
    ("claude_haiku_4_5", lambda p: call_anthropic("claude-haiku-4-5", p)),
    ("claude_sonnet_4_5", lambda p: call_anthropic("claude-sonnet-4-5", p)),
]


def label_one(rater_name, fn, prop_idx, prop):
    prompt = PROMPT_TEMPLATE.format(prop=prop)
    for attempt in range(3):
        try:
            scores = parse_scores(fn(prompt))
            if scores:
                return rater_name, prop_idx, scores, None
        except Exception as e:
            err = f"attempt {attempt}: {type(e).__name__}: {e}"
            time.sleep(2)
            continue
        time.sleep(1)
    return rater_name, prop_idx, None, "unparseable_or_failed"


# ----------------------------- measures -----------------------------
def fleiss_kappa(matrix):
    matrix = np.asarray(matrix, dtype=float)
    N, K = matrix.shape
    n = matrix.sum(axis=1)
    if not np.all(n == n[0]):
        return float("nan")
    n = int(n[0])
    if n < 2:
        return float("nan")
    P_i = ((matrix * (matrix - 1)).sum(axis=1)) / (n * (n - 1))
    P_bar = float(P_i.mean())
    p_j = matrix.sum(axis=0) / (N * n)
    P_e = float((p_j ** 2).sum())
    if abs(1 - P_e) < 1e-12:
        return float("nan")
    return (P_bar - P_e) / (1 - P_e)


def entropy(vec):
    vec = np.asarray(vec, dtype=float)
    tot = vec.sum()
    if tot == 0:
        return 0.0
    p = vec[vec > 0] / tot
    return float(-(p * np.log2(p)).sum())


def mutual_info(x, y, bins=3):
    """Discrete MI in bits between two integer/float arrays (terciles)."""
    x = np.asarray(x); y = np.asarray(y)
    xb = np.clip(np.digitize(x, np.quantile(x, [1/3, 2/3])), 0, bins - 1)
    yb = np.clip(np.digitize(y, np.quantile(y, [1/3, 2/3])), 0, bins - 1)
    N = len(xb)
    joint = np.zeros((bins, bins))
    for a, b in zip(xb, yb):
        joint[a, b] += 1
    joint /= N
    px = joint.sum(axis=1); py = joint.sum(axis=0)
    mi = 0.0
    for i in range(bins):
        for j in range(bins):
            if joint[i, j] > 0 and px[i] > 0 and py[j] > 0:
                mi += joint[i, j] * math.log2(joint[i, j] / (px[i] * py[j]))
    Hx = entropy(px * N); Hy = entropy(py * N)
    nmi = mi / math.sqrt(Hx * Hy) if Hx > 0 and Hy > 0 else 0.0
    return mi, nmi


def unique_variance(M, idx):
    """1 - R^2 of regressing column idx on the other columns (OLS w/ intercept)."""
    y = M[:, idx]
    others = [j for j in range(M.shape[1]) if j != idx]
    X = np.column_stack([np.ones(len(y))] + [M[:, j] for j in others])
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    yhat = X @ beta
    ss_res = float(((y - yhat) ** 2).sum())
    ss_tot = float(((y - y.mean()) ** 2).sum())
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return 1 - r2, r2


def mi_to_label(axis_vals, labels):
    """MI(bits) between a discretized axis and the categorical gold verdict."""
    x = np.asarray(axis_vals)
    xb = np.clip(np.digitize(x, np.quantile(x, [1/3, 2/3])), 0, 2)
    cats = sorted(set(labels))
    lab_idx = {c: i for i, c in enumerate(cats)}
    N = len(x)
    joint = np.zeros((3, len(cats)))
    for a, l in zip(xb, labels):
        joint[a, lab_idx[l]] += 1
    joint /= N
    px = joint.sum(axis=1); py = joint.sum(axis=0)
    mi = 0.0
    for i in range(3):
        for j in range(len(cats)):
            if joint[i, j] > 0 and px[i] > 0 and py[j] > 0:
                mi += joint[i, j] * math.log2(joint[i, j] / (px[i] * py[j]))
    return mi


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    # raw[rater][prop_idx] = [7 scores] or None
    raw = {rn: {} for rn, _ in RATERS}
    tasks = [(rn, fn, i, p) for rn, fn in RATERS for i, p in enumerate(TEST_SET)]
    print(f"Submitting {len(tasks)} rating tasks ({len(RATERS)} raters x {len(TEST_SET)} props)...")
    n_done = 0
    with ThreadPoolExecutor(max_workers=10) as ex:
        futs = [ex.submit(label_one, rn, fn, i, p) for rn, fn, i, p in tasks]
        for f in as_completed(futs):
            rn, i, scores, err = f.result()
            raw[rn][i] = scores if scores else None
            n_done += 1
            if n_done % 30 == 0 or n_done == len(tasks):
                print(f"  {n_done}/{len(tasks)} done")

    # keep only props where all 3 raters returned valid 7-vectors
    valid_idx = [i for i in range(len(TEST_SET))
                 if all(raw[rn].get(i) is not None for rn, _ in RATERS)]
    n_valid = len(valid_idx)
    n_invalid = len(TEST_SET) - n_valid
    if n_valid < 20:
        raise SystemExit(f"ABORT: only {n_valid} fully-rated props; rater API likely unavailable. "
                         f"No synthetic fallback (per #69).")

    # tensor scores[rater, prop, axis]
    R = len(RATERS)
    scores = np.zeros((R, n_valid, len(AXES)))
    for ri, (rn, _) in enumerate(RATERS):
        for pj, i in enumerate(valid_idx):
            scores[ri, pj] = raw[rn][i]

    # (1) RELIABILITY: Fleiss kappa per axis (4 ordinal levels 0-3, treated nominal = floor)
    kappa_per_axis = {}
    for a, axis in enumerate(AXES):
        mat = np.zeros((n_valid, 4))
        for pj in range(n_valid):
            for ri in range(R):
                mat[pj, int(scores[ri, pj, a])] += 1
        kappa_per_axis[axis] = fleiss_kappa(mat)

    # per-prop mean across raters
    M_all = scores.mean(axis=0)          # (n_valid, 7)
    M_can = M_all[:, :4]                 # canonical only

    # (2) OWN-INFORMATION / NON-REDUNDANCY (canonical 4)
    corr = np.corrcoef(M_can, rowvar=False)
    mi_matrix = np.zeros((4, 4)); nmi_matrix = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            if i != j:
                mi_matrix[i, j], nmi_matrix[i, j] = mutual_info(M_can[:, i], M_can[:, j])
    uniq = {}
    for i, axis in enumerate(CANONICAL):
        u, r2 = unique_variance(M_can, i)
        uniq[axis] = {"unique_variance": u, "r2_from_others": r2}
    # PCA effective rank on correlation matrix
    eig = np.sort(np.linalg.eigvalsh(corr))[::-1]
    eig = np.clip(eig, 0, None)
    var_explained = (eig / eig.sum()).tolist()
    p = eig / eig.sum()
    eff_rank = float(math.exp(entropy(p) * math.log(2)))  # exp of Shannon (nats) -> participation

    # (3) SPECTRUM (per-axis spread) + COVERAGE (axis -> gold verdict) + EXHAUSTIVENESS (extras)
    spectrum = {}
    for a, axis in enumerate(AXES):
        col = M_all[:, a]
        hist = np.zeros(4)
        for pj in range(n_valid):
            # use rounded mean bucket for a readable spectrum
            hist[int(round(col[pj]))] += 1
        spectrum[axis] = {"variance": float(col.var()),
                          "entropy_bits": entropy(hist),
                          "hist_0to3": hist.astype(int).tolist()}
    golds = [GOLD[TEST_SET[i]] for i in valid_idx]
    coverage_mi = {axis: mi_to_label(M_all[:, a], golds) for a, axis in enumerate(AXES)}

    # exhaustiveness: unique variance of each EXTRA axis given the canonical 4
    extra_uniq = {}
    for a, axis in enumerate(EXTRA):
        col = M_all[:, 4 + a]
        X = np.column_stack([np.ones(n_valid)] + [M_can[:, k] for k in range(4)])
        beta, *_ = np.linalg.lstsq(X, col, rcond=None)
        yhat = X @ beta
        ss_res = float(((col - yhat) ** 2).sum()); ss_tot = float(((col - col.mean()) ** 2).sum())
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
        extra_uniq[axis] = {"unique_variance_given_4": 1 - r2, "r2_from_4": r2}

    # ---- mechanical verdicts ----
    KAPPA_OK = 0.40           # moderate agreement floor (ordinal kappa is a floor)
    UNIQ_OK = 0.20            # an axis must retain >=20% variance not explained by the others
    EXTRA_GAP = 0.50          # an extra axis "carries large unique info" if >50% unique
    reliable = {ax: (kappa_per_axis[ax] >= KAPPA_OK) for ax in CANONICAL}
    distinct = {ax: (uniq[ax]["unique_variance"] >= UNIQ_OK) for ax in CANONICAL}
    live = {ax: (spectrum[ax]["variance"] > 0.10) for ax in CANONICAL}
    gaps = {ax: extra_uniq[ax]["unique_variance_given_4"] for ax in EXTRA
            if extra_uniq[ax]["unique_variance_given_4"] >= EXTRA_GAP}

    all_reliable = all(reliable.values())
    all_distinct = all(distinct.values())
    all_live = all(live.values())
    if all_reliable and all_distinct and all_live and not gaps:
        verdict = "CONFIRM (reliable + distinct + live + no large coverage gap found)"
    elif all_distinct and all_live and not gaps:
        verdict = "CONFIRM-WEAK (distinct + live + no gap; some axis below kappa floor)"
    else:
        verdict = "QUALIFIED (see reliable/distinct/live/gaps flags)"

    results = {
        "pass": 77, "batch": "B125", "test_id": "four_truth_axes_audit",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_props_total": len(TEST_SET), "n_props_fully_rated": n_valid,
        "n_props_dropped": n_invalid,
        "raters": [r[0] for r in RATERS],
        "deviations": [
            "D1: 3 LLM raters substitute for humans (operational-usability-by-LLMs only)",
            "D2: gold verdict + design tags are author labels, used only for coverage MI/sanity",
            "D3: 'cover ALL aspects' is unprovable; report reliable/distinct/live/gap honestly",
        ],
        "axes_canonical": CANONICAL,
        "axes_candidate_extra": EXTRA,
        "thresholds": {"kappa_ok": KAPPA_OK, "unique_var_ok": UNIQ_OK, "extra_gap": EXTRA_GAP},
        "reliability_fleiss_kappa": kappa_per_axis,
        "correlation_canonical": corr.tolist(),
        "mutual_info_bits_canonical": mi_matrix.tolist(),
        "nmi_canonical": nmi_matrix.tolist(),
        "unique_variance_canonical": uniq,
        "pca_var_explained": var_explained,
        "pca_effective_rank": eff_rank,
        "spectrum_per_axis": spectrum,
        "coverage_mi_axis_to_verdict_bits": coverage_mi,
        "exhaustiveness_extra_axes": extra_uniq,
        "flags": {"reliable": reliable, "distinct": distinct, "live": live,
                  "coverage_gaps_found": gaps},
        "verdict": verdict,
        "raw_scores_per_rater": {rn: {str(i): raw[rn].get(i) for i in valid_idx}
                                 for rn, _ in RATERS},
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)

    print("\n=== B125 — 4 TRUTH-AXES AUDIT ===")
    print(f"fully-rated props: {n_valid}/{len(TEST_SET)} (dropped {n_invalid})")
    print("\n(1) RELIABILITY — Fleiss kappa per axis (nominal floor):")
    for ax in AXES:
        print(f"    {ax:<13s} kappa = {kappa_per_axis[ax]:+.3f}")
    print("\n(2) OWN-INFORMATION — unique variance (1 - R^2 from the other 3):")
    for ax in CANONICAL:
        print(f"    {ax:<13s} unique = {uniq[ax]['unique_variance']:.3f}  (R^2={uniq[ax]['r2_from_others']:.3f})")
    print(f"    PCA var explained = {[round(v,3) for v in var_explained]}  effective_rank={eff_rank:.2f}")
    print("    canonical correlation matrix:")
    for i, ax in enumerate(CANONICAL):
        print(f"      {ax:<13s} " + " ".join(f"{corr[i,j]:+.2f}" for j in range(4)))
    print("\n(3) SPECTRUM (variance / entropy) + COVERAGE MI(axis;verdict):")
    for ax in AXES:
        print(f"    {ax:<13s} var={spectrum[ax]['variance']:.2f} H={spectrum[ax]['entropy_bits']:.2f}b "
              f"covMI={coverage_mi[ax]:.3f}b")
    print("\n    EXHAUSTIVENESS — candidate extra axes' unique variance given the 4:")
    for ax in EXTRA:
        print(f"    {ax:<13s} unique_given_4 = {extra_uniq[ax]['unique_variance_given_4']:.3f}")
    print(f"\nVERDICT: {verdict}")
    print(f"Written to {RESULTS_PATH}")


if __name__ == "__main__":
    main()
