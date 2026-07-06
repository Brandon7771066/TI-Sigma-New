"""
Pass-77 — GILE + HEM dimensions PILOT audit (same battery used to confirm the MR
Truth Labels and, adapted, the 4 Truth-Axes in B125).

USER-DIRECTED SCOPE: ~60-item pilot first (B125-sized); scale to the 1,000-prop set
only if this looks sound.

The MR Truth LABELS were confirmed with Fleiss' kappa (reliability), information
content (mutual information), and spectrum-exhaustion (do the labels jointly cover
the truth spectrum). The GILE and HEM DIMENSIONS are not a categorical alphabet —
they are continuous dimensions — so, exactly as in B125, the battery is ADAPTED:

  (1) RELIABILITY  -> Fleiss' kappa per dimension (each dimension discretized to an
                      ordinal 0-3 scale; nominal kappa = conservative FLOOR).
  (2) OWN-INFORMATION / NON-REDUNDANCY -> cross-dimension MI + correlation; each
                      dimension's UNIQUE variance = 1 - R^2 of regressing it on
                      (a) its own pillar's other dimensions and (b) all 7 others.
                      PCA effective rank checks the 8 span a genuinely multi-D space.
  (3) SPECTRUM + COVERAGE + EXHAUSTIVENESS -> per-dimension spread (variance +
                      entropy: live spectrum or degenerate?); MI(dimension ; gold MR
                      verdict) = how much each informs the truth verdict (GILE is the
                      TRUTH pillar and SHOULD inform it — especially I=certainty; HEM
                      is the EXISTENCE pillar and need not); and an EXHAUSTIVENESS
                      probe: 2 candidate EXTRA dimensions (persistence/duration,
                      practical usefulness) are also scored — low unique variance
                      given the 8 SUPPORTS "the 8 cover it"; large unique variance is
                      an honest coverage-gap FLAG.

PRE-REGISTERED SPECIAL CHECK (frozen before run):
  E<->D3: canon (B116) holds GILE-E (Elegance) numerically == HEM-D3 (spectral
  purity) at the OPERATIONAL level. Here we test whether raters ALSO perceive them
  as the same in ABSTRACT space. High corr = corroboration that the identity is
  perceived; low corr = the identity is operational-only (both readings honest,
  neither refutes B116, which is a claim about the operational estimators).

CANONICAL DIMENSION DEFINITIONS USED (frozen; sources in comments):
  GILE (Truth pillar; GSN-1 short statements, GILE_DEFINITION_CANONICAL_2026-07-04):
    G  Goodness   = real benefit / good
    I  Intuition  = certainty (calibrated inner rightness)
    L  Love/Level = abstract binding between things (relational closeness)
    E  Elegance   = beauty of form
  HEM abstract axes (Existence pillar; HEM_DIMENSIONS_8D_OVERVIEW_2026-07-05):
    D1 Physical-Energetic     = stability / robustness of the referent phenomenon
    D2 Social-Historical      = contradiction load among sources/accounts about it
    D3 Aesthetic-Structural   = structural cleanliness / purity (far from noise)
    D4 Conscious-Experiential = how fast the referent state is changing / evolving

#69 HONESTY / DEVIATIONS (frozen):
  DV1: 3 LLM raters (gpt-4o-mini, claude-haiku-4-5, claude-sonnet-4-5) stand in for
       humans, exactly as in the label-kappa and B125 runs. A CONFIRM means the
       dimensions are operationally usable BY LLMs given crisp definitions; it does
       NOT establish human usability.
  DV2: HEM's operational metrics are SIGNAL metrics (EEG amplitude CV, spectral
       purity, d(LCC)/dt on time series). Rating PROPOSITIONS uses the ABSTRACT
       axes; this pilot tests the abstract axes' perceivability/distinctness — it
       does NOT validate the operational estimators.
  DV3: The 61-prop item set is reused frozen from B125 (designed for TRUTH-label
       variance, not existence variance). Pragmatic reuse; it may under-span HEM.
       If HEM dimensions come out degenerate (low variance), the honest first
       reading is ITEM-SET LIMITATION, not dimension failure.
  DV4: 'gold' MR verdict = author design labels from B125, used ONLY for coverage
       MI; raters never see them.
  NO synthetic fallback: if the rater API is unavailable the run ABORTS.

Anti-HARK: prompt + propositions + definitions + thresholds frozen at commit;
runner SHA256 logged; verdicts follow the mechanical thresholds below (identical
values to B125: kappa>=0.40, unique>=0.20, extra-gap>=0.50).
"""
import json, os, time, hashlib, re, math
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

# ---------------------------------------------------------------------------
# Frozen test set: reused verbatim from analyses/pass77_b125_four_truth_axes_audit
# (61 props + author gold MR verdict; design tags dropped — not used here).
# ---------------------------------------------------------------------------
PROPS = [
    ("Water is H2O.", "T"),
    ("2 + 2 = 4.", "T"),
    ("The Earth orbits the Sun.", "T"),
    ("Paris is the capital of France.", "T"),
    ("Iron is denser than cork.", "T"),
    ("The square root of 144 is 12.", "T"),
    ("Paris is the capital of Germany.", "F"),
    ("The Sun orbits the Earth once a day.", "F"),
    ("3 + 5 = 9.", "F"),
    ("Humans have 100 chromosomes in total.", "F"),
    ("Aluminium is a noble gas.", "F"),
    ("The new cancer drug passed its phase-III trial.", "I"),
    ("Yesterday's unemployment figure was 4.1 percent.", "I"),
    ("The defendant was at the scene at 9 p.m.", "I"),
    ("This restaurant's kitchen passed its last health inspection.", "I"),
    ("The bridge was certified safe by the engineering firm.", "I"),
    ("The ancient manuscript is genuine, not a forgery.", "I"),
    ("The lab's reported measurement of the electron mass is correct.", "T"),
    ("Human beings are capable of extraordinary kindness.", "T"),
    ("People are capable of great cruelty.", "T"),
    ("Every person has the right to be treated with dignity.", "I"),
    ("Democracies hold their leaders accountable.", "I"),
    ("Education lifts people out of poverty.", "I"),
    ("Markets allocate resources efficiently.", "I"),
    ("Friendship makes life worth living.", "I"),
    ("Hard work is rewarded.", "I"),
    ("Sarah is reliable.", "I"),
    ("Coffee is good for you.", "I"),
    ("The movie was a masterpiece.", "I"),
    ("Tomatoes are a vegetable.", "I"),
    ("A whale is a fish.", "F"),
    ("Pluto is a planet.", "I"),
    ("He is tall.", "I"),
    ("The soup is too salty.", "I"),
    ("There will be a sea battle tomorrow.", "I"),
    ("There are infinitely many twin primes.", "I"),
    ("It will rain in this city exactly one year from today.", "I"),
    ("The continuum hypothesis is true.", "I"),
    ("There exists intelligent life elsewhere in the galaxy.", "I"),
    ("The stock market will be higher next month.", "I"),
    ("Lying is always wrong.", "I"),
    ("It is wrong to torture an innocent person for fun.", "T"),
    ("Beauty is in the eye of the beholder.", "I"),
    ("Classical music is better than pop.", "I"),
    ("This sentence is false.", "MI"),
    ("The set of all sets that do not contain themselves contains itself.", "MI"),
    ("The following statement is true; the previous statement is false.", "MI"),
    ("I am lying right now.", "MI"),
    ("The number seven is jealous.", "MI"),
    ("Wednesday tastes like the colour blue.", "MI"),
    ("Consciousness is purely physical.", "I"),
    ("Mathematical objects exist independently of minds.", "I"),
    ("Free will is compatible with determinism.", "I"),
    ("The universe had a cause.", "I"),
    ("It is raining outside right now.", "I"),
    ("The traffic light is red.", "I"),
    ("This cup contains coffee.", "I"),
    ("The door is open.", "I"),
    ("World War II ended in 1945.", "T"),
    ("Shakespeare wrote Hamlet.", "T"),
    ("Napoleon died in 1821.", "T"),
]
GOLD = {p[0]: p[1] for p in PROPS}
TEST_SET = [p[0] for p in PROPS]

# 10 dims scored per prop: 4 GILE + 4 HEM + 2 candidate-extra (exhaustiveness probe)
GILE = ["G", "I", "L", "E"]
HEM = ["D1", "D2", "D3", "D4"]
CANONICAL = GILE + HEM
EXTRA = ["persistence", "usefulness"]
DIMS = CANONICAL + EXTRA

PROMPT_TEMPLATE = (
    "You are an expert rater. The proposition below makes a claim about some referent "
    "(a thing, state of affairs, or pattern). Rate it on TEN independent dimensions, each "
    "on an integer scale 0-3. Judge each dimension on its OWN terms.\n\n"
    "The first four dimensions rate the CLAIM's truth-character:\n"
    "1. GOODNESS (how much real benefit / good the claim's content embodies or points to): "
    "0=none or harmful, 1=slight, 2=substantial, 3=profound good.\n"
    "2. CERTAINTY (how certain a careful mind can be that the claim is right): "
    "0=no basis for confidence, 1=weak, 2=strong, 3=near-total certainty.\n"
    "3. BINDING (how strongly the claim binds things together in an abstract relation — "
    "relational closeness, connection between the things it links): 0=no relational "
    "binding, 1=weak, 2=strong, 3=very strong binding.\n"
    "4. BEAUTY (beauty/elegance of form of the claim's content — how aesthetically "
    "complete and well-formed it is): 0=ugly/formless, 1=plain, 2=elegant, 3=strikingly "
    "beautiful.\n\n"
    "The next four dimensions rate the EXISTENCE-profile of the claim's REFERENT — the "
    "phenomenon or state of affairs it is about (not whether the claim is true):\n"
    "5. STABILITY (how stable/robust the referent phenomenon is — does it hold steady or "
    "flicker?): 0=fleeting/unstable, 1=weakly stable, 2=mostly stable, 3=rock-solid.\n"
    "6. CONTRADICTION-LOAD (how much different sources/accounts about the referent "
    "contradict each other): 0=no contradiction among accounts, 1=mild, 2=substantial, "
    "3=severe contradiction.\n"
    "7. STRUCTURAL-PURITY (how clean and structured the referent is versus noisy/diffuse): "
    "0=pure noise/diffuse, 1=weak structure, 2=clear structure, 3=perfectly clean "
    "structure.\n"
    "8. RATE-OF-CHANGE (how fast the referent state is changing/evolving): 0=static, "
    "1=slow, 2=moderate, 3=rapidly changing.\n\n"
    "Two further probe dimensions:\n"
    "9. PERSISTENCE (how long the referent endures in time): 0=momentary, 1=short-lived, "
    "2=long-lasting, 3=effectively permanent.\n"
    "10. USEFULNESS (practical usefulness of knowing the claim): 0=useless, 1=slight, "
    "2=useful, 3=extremely useful.\n\n"
    "Proposition: \"{prop}\"\n\n"
    "Respond with EXACTLY ten integers 0-3 separated by single spaces, in the order "
    "GOODNESS CERTAINTY BINDING BEAUTY STABILITY CONTRADICTION-LOAD STRUCTURAL-PURITY "
    "RATE-OF-CHANGE PERSISTENCE USEFULNESS. Nothing else."
)


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def parse_scores(text):
    """STRICT (post-review hardening): the entire response must be exactly ten
    whitespace-separated integers 0-3. Anything else (echoed text, numbering,
    stray digits) is rejected -> retried -> counted as a failure, never
    silently mis-parsed."""
    if text is None:
        return None
    toks = text.strip().split()
    if len(toks) != 10 or not all(re.fullmatch(r"[0-3]", t) for t in toks):
        return None
    return [int(t) for t in toks]


def call_anthropic(model, prompt):
    from anthropic import Anthropic
    c = Anthropic()
    r = c.messages.create(model=model, max_tokens=40,
                          messages=[{"role": "user", "content": prompt}])
    return r.content[0].text


def call_openai(model, prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
    r = c.chat.completions.create(model=model, max_tokens=40,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content


RATERS = [
    ("gpt_4o_mini", lambda p: call_openai("gpt-4o-mini", p)),
    ("claude_haiku_4_5", lambda p: call_anthropic("claude-haiku-4-5", p)),
    ("claude_sonnet_4_5", lambda p: call_anthropic("claude-sonnet-4-5", p)),
]


def label_one(rater_name, fn, prop_idx, prop):
    prompt = PROMPT_TEMPLATE.format(prop=prop)
    raw_texts = []
    for attempt in range(3):
        try:
            text = fn(prompt)
            raw_texts.append(text)
            scores = parse_scores(text)
            if scores:
                return rater_name, prop_idx, scores, raw_texts, None
        except Exception as e:
            raw_texts.append(f"<EXCEPTION attempt {attempt}: {type(e).__name__}: {e}>")
            time.sleep(2)
            continue
        time.sleep(1)
    return rater_name, prop_idx, None, raw_texts, "unparseable_or_failed"


# ----------------------------- measures (identical to B125) -----------------------------
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


def unique_variance_cols(M, idx, others):
    y = M[:, idx]
    X = np.column_stack([np.ones(len(y))] + [M[:, j] for j in others])
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    yhat = X @ beta
    ss_res = float(((y - yhat) ** 2).sum())
    ss_tot = float(((y - y.mean()) ** 2).sum())
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return 1 - r2, r2


def mi_to_label(axis_vals, labels):
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
    raw = {rn: {} for rn, _ in RATERS}
    tasks = [(rn, fn, i, p) for rn, fn in RATERS for i, p in enumerate(TEST_SET)]
    print(f"Submitting {len(tasks)} rating tasks ({len(RATERS)} raters x {len(TEST_SET)} props)...")
    n_done = 0
    with ThreadPoolExecutor(max_workers=10) as ex:
        futs = [ex.submit(label_one, rn, fn, i, p) for rn, fn, i, p in tasks]
        raw_responses = {rn: {} for rn, _ in RATERS}
        for f in as_completed(futs):
            rn, i, scores, raw_texts, err = f.result()
            raw[rn][i] = scores if scores else None
            raw_responses[rn][i] = raw_texts
            n_done += 1
            if n_done % 30 == 0 or n_done == len(tasks):
                print(f"  {n_done}/{len(tasks)} done")

    valid_idx = [i for i in range(len(TEST_SET))
                 if all(raw[rn].get(i) is not None for rn, _ in RATERS)]
    n_valid = len(valid_idx)
    n_invalid = len(TEST_SET) - n_valid
    if n_valid < 20:
        raise SystemExit(f"ABORT: only {n_valid} fully-rated props; rater API likely unavailable. "
                         f"No synthetic fallback (per #69).")

    R = len(RATERS)
    scores = np.zeros((R, n_valid, len(DIMS)))
    for ri, (rn, _) in enumerate(RATERS):
        for pj, i in enumerate(valid_idx):
            scores[ri, pj] = raw[rn][i]

    # (1) RELIABILITY: Fleiss kappa per dimension
    kappa_per_dim = {}
    for a, dim in enumerate(DIMS):
        mat = np.zeros((n_valid, 4))
        for pj in range(n_valid):
            for ri in range(R):
                mat[pj, int(scores[ri, pj, a])] += 1
        kappa_per_dim[dim] = fleiss_kappa(mat)

    M_all = scores.mean(axis=0)          # (n_valid, 10)
    M_can = M_all[:, :8]                 # canonical 8

    # (2) OWN-INFORMATION / NON-REDUNDANCY
    corr = np.corrcoef(M_can, rowvar=False)
    mi_matrix = np.zeros((8, 8))
    for i in range(8):
        for j in range(8):
            if i != j:
                mi_matrix[i, j], _ = mutual_info(M_can[:, i], M_can[:, j])
    uniq_within_pillar, uniq_vs_all = {}, {}
    for i, dim in enumerate(CANONICAL):
        pillar_idx = [0, 1, 2, 3] if i < 4 else [4, 5, 6, 7]
        others_pillar = [j for j in pillar_idx if j != i]
        u_p, r2_p = unique_variance_cols(M_can, i, others_pillar)
        u_a, r2_a = unique_variance_cols(M_can, i, [j for j in range(8) if j != i])
        uniq_within_pillar[dim] = {"unique_variance": u_p, "r2_from_pillar": r2_p}
        uniq_vs_all[dim] = {"unique_variance": u_a, "r2_from_other7": r2_a}
    eig = np.sort(np.linalg.eigvalsh(corr))[::-1]
    eig = np.clip(eig, 0, None)
    var_explained = (eig / eig.sum()).tolist()
    p = eig / eig.sum()
    eff_rank = float(math.exp(entropy(p) * math.log(2)))

    # PRE-REGISTERED: E <-> D3 (abstract-space perception of the B116 identity)
    e_idx, d3_idx = CANONICAL.index("E"), CANONICAL.index("D3")
    e_d3_corr = float(corr[e_idx, d3_idx])
    e_d3_mi, e_d3_nmi = mutual_info(M_can[:, e_idx], M_can[:, d3_idx])

    # (3) SPECTRUM + COVERAGE + EXHAUSTIVENESS
    spectrum = {}
    for a, dim in enumerate(DIMS):
        col = M_all[:, a]
        hist = np.zeros(4)
        for pj in range(n_valid):
            hist[int(round(col[pj]))] += 1
        spectrum[dim] = {"variance": float(col.var()),
                         "entropy_bits": entropy(hist),
                         "hist_0to3": hist.astype(int).tolist()}
    golds = [GOLD[TEST_SET[i]] for i in valid_idx]
    coverage_mi = {dim: mi_to_label(M_all[:, a], golds) for a, dim in enumerate(DIMS)}
    # canonical-weight GILE composite (0-1 scale) -> verdict MI
    w = np.array([0.4142, 0.25, 0.18, 0.15]); w = w / w.sum()
    gile_composite = (M_can[:, :4] / 3.0) @ w
    composite_mi = mi_to_label(gile_composite, golds)

    extra_uniq = {}
    for a, dim in enumerate(EXTRA):
        col = M_all[:, 8 + a]
        u, r2 = unique_variance_cols(np.column_stack([M_can, col]), 8, list(range(8)))
        extra_uniq[dim] = {"unique_variance_given_8": u, "r2_from_8": r2}

    # ---- mechanical verdicts (identical thresholds to B125) ----
    KAPPA_OK, UNIQ_OK, EXTRA_GAP = 0.40, 0.20, 0.50
    reliable = {d: (kappa_per_dim[d] >= KAPPA_OK) for d in CANONICAL}
    distinct = {d: (uniq_vs_all[d]["unique_variance"] >= UNIQ_OK) for d in CANONICAL}
    live = {d: (spectrum[d]["variance"] > 0.10) for d in CANONICAL}
    gaps = {d: extra_uniq[d]["unique_variance_given_8"] for d in EXTRA
            if extra_uniq[d]["unique_variance_given_8"] >= EXTRA_GAP}

    def pillar_verdict(dims):
        r = all(reliable[d] for d in dims)
        di = all(distinct[d] for d in dims)
        li = all(live[d] for d in dims)
        if r and di and li:
            return "CONFIRM (reliable + distinct + live)"
        if di and li:
            return "CONFIRM-WEAK (distinct + live; some dim below kappa floor)"
        return "QUALIFIED (see flags)"

    results = {
        "pass": 77, "test_id": "gile_hem_battery_pilot",
        "started_at": started,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "n_props_total": len(TEST_SET), "n_props_fully_rated": n_valid,
        "n_props_dropped": n_invalid,
        "raters": [r[0] for r in RATERS],
        "deviations": [
            "DV1: 3 LLM raters substitute for humans (operational-usability-by-LLMs only)",
            "DV2: abstract HEM axes tested, NOT the operational signal estimators",
            "DV3: item set reused frozen from B125 (truth-designed); may under-span HEM",
            "DV4: gold verdicts are author design labels, used only for coverage MI",
        ],
        "dims_gile": GILE, "dims_hem": HEM, "dims_extra": EXTRA,
        "thresholds": {"kappa_ok": KAPPA_OK, "unique_var_ok": UNIQ_OK, "extra_gap": EXTRA_GAP},
        "reliability_fleiss_kappa": kappa_per_dim,
        "correlation_canonical8": corr.tolist(),
        "mutual_info_bits_canonical8": mi_matrix.tolist(),
        "unique_variance_within_pillar": uniq_within_pillar,
        "unique_variance_vs_all7": uniq_vs_all,
        "pca_var_explained": var_explained,
        "pca_effective_rank": eff_rank,
        "prereg_E_vs_D3": {"pearson_r": e_d3_corr, "mi_bits": e_d3_mi, "nmi": e_d3_nmi},
        "spectrum_per_dim": spectrum,
        "coverage_mi_dim_to_verdict_bits": coverage_mi,
        "gile_composite_to_verdict_mi_bits": composite_mi,
        "exhaustiveness_extra_dims": extra_uniq,
        "flags": {"reliable": reliable, "distinct": distinct, "live": live,
                  "coverage_gaps_found": gaps},
        "verdict_gile": pillar_verdict(GILE),
        "verdict_hem": pillar_verdict(HEM),
        "raw_scores_per_rater": {rn: {str(i): raw[rn].get(i) for i in valid_idx}
                                 for rn, _ in RATERS},
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    with open(os.path.join(ROOT, "raw_responses.json"), "w") as f:
        json.dump(raw_responses, f, indent=2, default=str)

    print("\n=== GILE + HEM DIMENSIONS — PILOT BATTERY ===")
    print(f"fully-rated props: {n_valid}/{len(TEST_SET)} (dropped {n_invalid})")
    print("\n(1) RELIABILITY — Fleiss kappa per dimension (nominal floor):")
    for d in DIMS:
        print(f"    {d:<12s} kappa = {kappa_per_dim[d]:+.3f}")
    print("\n(2) OWN-INFORMATION — unique variance:")
    for d in CANONICAL:
        print(f"    {d:<12s} within-pillar = {uniq_within_pillar[d]['unique_variance']:.3f}  "
              f"vs-all-7 = {uniq_vs_all[d]['unique_variance']:.3f}")
    print(f"    PCA var explained = {[round(v,3) for v in var_explained]}  effective_rank={eff_rank:.2f}")
    print(f"\n    PRE-REG E<->D3: r={e_d3_corr:+.3f}  MI={e_d3_mi:.3f}b  NMI={e_d3_nmi:.3f}")
    print("\n(3) SPECTRUM + COVERAGE MI(dim;verdict):")
    for d in DIMS:
        print(f"    {d:<12s} var={spectrum[d]['variance']:.2f} H={spectrum[d]['entropy_bits']:.2f}b "
              f"covMI={coverage_mi[d]:.3f}b")
    print(f"    GILE composite (canonical weights) -> verdict MI = {composite_mi:.3f}b")
    print("\n    EXHAUSTIVENESS — extra dims' unique variance given the 8:")
    for d in EXTRA:
        print(f"    {d:<12s} unique_given_8 = {extra_uniq[d]['unique_variance_given_8']:.3f}")
    print(f"\nVERDICT GILE: {results['verdict_gile']}")
    print(f"VERDICT HEM:  {results['verdict_hem']}")
    print(f"Written to {RESULTS_PATH}")


if __name__ == "__main__":
    main()
