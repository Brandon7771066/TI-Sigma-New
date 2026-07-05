"""
Phase I LCC/OET on open dialogue corpora — RIGOROUS ADAPTATION of the user-provided scaffold.

Tests whether reciprocal adaptive synchronization (RAS) in multi-turn conversations
predicts conversational OUTCOMES better than simple semantic similarity.

    RAS = sqrt(P_A->B * P_B->A)

Faithful to the user's scaffold (C=semantic_alignment, S=adaptation_slope,
predictive-gain-based directional P, L_add/L_geo/L_hybrid, candidate thresholds),
PLUS the confound-control rigor this corpus requires (see honesty rails below).

HONESTY RAILS (per corpus #69 / EVD-1 and prior LCC negatives):
  * The naive statistic is always confoundable. Prediction #1 is RELATIVE: RAS must
    beat an adjacent-turn-similarity-only matched control (C). We test that directly
    with cross-validated OOS outcome prediction, not just marginal correlations.
  * Cross-conversation SURROGATE null isolates reciprocal coupling from generic
    predictability / common-input.
  * A SYNTHETIC positive/negative control validates the METHOD before we trust a
    null on real data (a null must mean "no effect", not "broken harness").
  * Candidate CONSTANTS (prediction #4) are tested ONLY if prediction #1 passes (gate-first).
  * Whatever comes out is reported honestly.

ENVIRONMENT DEVIATIONS FROM THE SCAFFOLD (stated for honesty):
  * `datasets` library does not resolve in this env (uv/py3.14 marker conflict), so
    data is fetched directly from Hugging Face auto-converted parquet over HTTP.
  * The scaffold's DailyDialog / Chatbot-Arena / LMSYS datasets are BLOCKED here:
    daily_dialog was renamed/removed, its mirror runs arbitrary code (no parquet),
    and lmsys/chatbot_arena_conversations + LMSYS-Chat-1M are GATED (need an HF token
    this env lacks). We substitute UNGATED, outcome-bearing, multi-turn human<->AI sets:
      - Anthropic/hh-rlhf        (chosen vs rejected human preference; paired)
      - lmsys/mt_bench_human_judgments (real human winner votes; two full branches)
  * Embeddings use TF-IDF + TruncatedSVD (LSA), NOT sentence-transformers/MiniLM
    (torch not installed). This is a lexical-semantic PROXY. It is adequate for the
    RELATIVE prediction (RAS-vs-C in a shared space) but a MiniLM rerun is the
    natural next step. Absolute magnitudes are proxy-dependent; do not over-read them.
"""

import argparse
import json
import os
from dataclasses import dataclass
from typing import List, Dict, Any, Optional, Tuple

import numpy as np
import pandas as pd
from scipy import stats
from sklearn.linear_model import Ridge, LogisticRegression
from sklearn.metrics import mean_squared_error, roc_auc_score
from sklearn.model_selection import StratifiedKFold, GroupKFold
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import make_pipeline
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD

RNG = np.random.default_rng(20260705)
PHI = (1 + np.sqrt(5)) / 2

THRESHOLDS = {
    "sqrt2_minus_1_recursive_onset": np.sqrt(2) - 1,
    "golden_orthogonal_C_balanced_onset": 1 / (np.sqrt(2) * PHI),
    "sync_0_6_stable_bidirectional": 0.6,
    "sqrt2_over_2_majority_structure": np.sqrt(2) / 2,
    "classical_0_75_separable_ceiling": 0.75,
    "CHSH_cos2_pi8_nonseparable": np.cos(np.pi / 8) ** 2,
    "Radiant_Cap_UOP": np.sqrt(1 - np.exp(-2)),
}

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


# =========================================================================
# Conversation container
# =========================================================================
@dataclass
class Turn:
    speaker: str
    text: str


# =========================================================================
# Embeddings: LSA (TF-IDF + TruncatedSVD). Proxy for MiniLM (see header).
# =========================================================================
class LSAEmbedder:
    def __init__(self, dim: int = 256):
        self.dim = dim
        self.vec = None
        self.svd = None

    def fit(self, corpus: List[str]):
        self.vec = TfidfVectorizer(max_features=40000, ngram_range=(1, 2),
                                   min_df=2, sublinear_tf=True)
        X = self.vec.fit_transform(corpus)
        k = min(self.dim, X.shape[1] - 1, max(2, len(corpus) - 1))
        self.svd = TruncatedSVD(n_components=k, random_state=0)
        self.svd.fit(X)
        return self

    def transform(self, texts: List[str]) -> np.ndarray:
        X = self.vec.transform(texts)
        Z = self.svd.transform(X)
        n = np.linalg.norm(Z, axis=1, keepdims=True) + 1e-12
        return Z / n


# =========================================================================
# LCC metrics (faithful to scaffold)
# =========================================================================
def cosine(a, b):
    return float(np.dot(a, b) / ((np.linalg.norm(a) * np.linalg.norm(b)) + 1e-12))


def semantic_alignment(emb: np.ndarray) -> float:
    if len(emb) < 2:
        return np.nan
    return float(np.nanmean([cosine(emb[i], emb[i + 1]) for i in range(len(emb) - 1)]))


def adaptation_slope(emb: np.ndarray) -> float:
    if len(emb) < 4:
        return np.nan
    vals = np.array([cosine(emb[i], emb[i + 1]) for i in range(len(emb) - 1)])
    if np.std(vals) == 0:
        return 0.0
    slope = np.polyfit(np.arange(len(vals)), vals, 1)[0]
    return float(1 / (1 + np.exp(-10 * slope)))


def predictive_gain_direction(emb, speakers, source, target, min_samples=3):
    """Does source's last state improve prediction of target's next state beyond
    target's own last state? Leave-one-out OOS to survive tiny per-conversation N."""
    rows_self, rows_cross, y = [], [], []
    last = {}
    for i, spk in enumerate(speakers):
        if spk == target and source in last and target in last:
            rows_self.append(last[target])
            rows_cross.append(np.concatenate([last[target], last[source]]))
            y.append(emb[i])
        last[spk] = emb[i]
    n = len(y)
    if n < min_samples:
        return np.nan
    Xs, Xc, Y = np.vstack(rows_self), np.vstack(rows_cross), np.vstack(y)

    def cv_mse(X):
        # LOO for tiny N (stable), single holdout for larger N (fast). Same OOS logic.
        if n <= 6:
            errs = []
            for k in range(n):
                tr = [j for j in range(n) if j != k]
                m = make_pipeline(StandardScaler(with_mean=True, with_std=False),
                                  Ridge(alpha=5.0)).fit(X[tr], Y[tr])
                errs.append(mean_squared_error(Y[k:k + 1], m.predict(X[k:k + 1])))
            return float(np.mean(errs))
        cut = int(n * 0.7)
        m = make_pipeline(StandardScaler(with_mean=True, with_std=False),
                          Ridge(alpha=5.0)).fit(X[:cut], Y[:cut])
        return float(mean_squared_error(Y[cut:], m.predict(X[cut:])))

    e_self, e_cross = cv_mse(Xs), cv_mse(Xc)
    if e_self <= 0:
        return np.nan
    return float(max(0.0, (e_self - e_cross) / e_self))


def compute_lcc(turns: List[Turn], emb: np.ndarray) -> Dict[str, float]:
    spk = [t.speaker for t in turns]
    C = semantic_alignment(emb)
    S = adaptation_slope(emb)
    p_ab = predictive_gain_direction(emb, spk, "A", "B")
    p_ba = predictive_gain_direction(emb, spk, "B", "A")
    P = np.nan if (np.isnan(p_ab) or np.isnan(p_ba)) else float(np.sqrt(p_ab * p_ba))
    usable = [x for x in [C, S, P] if not np.isnan(x)]
    L_add = float(np.mean(usable)) if usable else np.nan
    if usable:
        L_geo = float(np.prod([max(x, 1e-6) for x in usable]) ** (1 / len(usable)))
        L_hybrid = 0.5 * L_add + 0.5 * L_geo
    else:
        L_geo = L_hybrid = np.nan
    return dict(C=C, S=S, P_A_to_B=p_ab, P_B_to_A=p_ba, RAS=P,
                L_add=L_add, L_geo=L_geo, L_hybrid=L_hybrid, n_turns=len(turns))


# =========================================================================
# Parsers
# =========================================================================
def parse_hh_string(s: str) -> List[Turn]:
    """hh-rlhf: '\\n\\nHuman: ... \\n\\nAssistant: ...' -> turns (A=Human, B=Assistant)."""
    parts, cur_role, buf = [], None, []
    tokens = s.replace("\n\nHuman:", "\x00H\x00").replace("\n\nAssistant:", "\x00A\x00")
    for chunk in tokens.split("\x00"):
        if chunk == "H":
            if cur_role:
                parts.append((cur_role, "".join(buf).strip())); buf = []
            cur_role = "A"
        elif chunk == "A":
            if cur_role:
                parts.append((cur_role, "".join(buf).strip())); buf = []
            cur_role = "B"
        else:
            buf.append(chunk)
    if cur_role and buf:
        parts.append((cur_role, "".join(buf).strip()))
    return [Turn(r, t) for r, t in parts if t]


def parse_role_list(conv) -> List[Turn]:
    """mt_bench: list of {content, role}; role user->A, assistant->B."""
    out = []
    for m in conv:
        role = m.get("role")
        spk = "A" if role in ("user", "human") else "B"
        c = (m.get("content") or "").strip()
        if c:
            out.append(Turn(spk, c))
    return out


# =========================================================================
# Outcome tests
# =========================================================================
def paired_wilcoxon(chosen: pd.DataFrame, rejected: pd.DataFrame, cols) -> pd.DataFrame:
    rows = []
    for c in cols:
        d = (chosen[c].values - rejected[c].values)
        d = d[~np.isnan(d)]
        if len(d) < 20 or np.allclose(d, 0):
            rows.append(dict(metric=c, n=len(d), median_diff=np.nan, W_p=np.nan,
                             frac_chosen_higher=np.nan)); continue
        try:
            W, p = stats.wilcoxon(d, zero_method="wilcox")
        except Exception:
            p = np.nan
        rows.append(dict(metric=c, n=int(len(d)), median_diff=float(np.median(d)),
                         W_p=float(p),
                         frac_chosen_higher=float(np.mean(d > 0))))
    return pd.DataFrame(rows)


def cv_outcome_auc(feat_win, feat_lose, feature_sets: Dict[str, list]) -> pd.DataFrame:
    """Paired->pointwise binary outcome. For each feature set, 5-fold CV OOS AUC of
    predicting winner(1)/loser(0). Matched control = 'C_only' vs sets adding RAS/hybrid."""
    # pair_id ties each winner row to its own loser row so GroupKFold keeps both
    # members of a prompt-pair in the SAME fold (no pair-level leakage across folds).
    Xw = feat_win.copy(); Xw["y"] = 1; Xw["pair_id"] = np.arange(len(Xw))
    Xl = feat_lose.copy(); Xl["y"] = 0; Xl["pair_id"] = np.arange(len(Xl))
    D = pd.concat([Xw, Xl], ignore_index=True)
    rows = []
    for name, cols in feature_sets.items():
        sub = D[cols + ["y", "pair_id"]].dropna()
        n_groups = sub["pair_id"].nunique()
        if len(sub) < 60 or sub["y"].nunique() < 2 or n_groups < 5:
            rows.append(dict(feature_set=name, n=len(sub), cv_auc=np.nan)); continue
        X = sub[cols].values; y = sub["y"].values; groups = sub["pair_id"].values
        aucs = []
        gkf = GroupKFold(n_splits=5)
        for tr, te in gkf.split(X, y, groups):
            if len(np.unique(y[tr])) < 2 or len(np.unique(y[te])) < 2:
                continue
            m = make_pipeline(StandardScaler(), LogisticRegression(max_iter=1000))
            m.fit(X[tr], y[tr])
            try:
                aucs.append(roc_auc_score(y[te], m.predict_proba(X[te])[:, 1]))
            except Exception:
                pass
        rows.append(dict(feature_set=name, n=int(len(sub)),
                         cv_auc=float(np.mean(aucs)) if aucs else np.nan))
    return pd.DataFrame(rows)


def surrogate_ras_null(convs: List[Tuple[List[Turn], np.ndarray]], n_surr=60) -> Dict[str, float]:
    """Cross-conversation surrogate: pair A-turns of one conv with B-turns of another
    (matched turn counts), recompute RAS. Real>surrogate => reciprocal coupling beyond
    generic predictability/common-input."""
    real = np.array([compute_lcc(t, e)["RAS"] for t, e in convs], dtype=float)
    real = real[~np.isnan(real)]
    if len(real) < 20:
        return dict(real_mean=np.nan, surr_mean=np.nan, p_real_gt_surr=np.nan, n=len(real))
    surr_means = []
    idx = np.arange(len(convs))
    for _ in range(n_surr):
        vals = []
        for _ in range(min(30, len(convs))):
            i, j = RNG.choice(idx, 2, replace=False)
            ti, ei = convs[i]; tj, ej = convs[j]
            # build a chimera: A turns from conv i, B turns from conv j, interleaved
            a = [(t, e) for t, e in zip(ti, ei) if t.speaker == "A"]
            b = [(t, e) for t, e in zip(tj, ej) if t.speaker == "B"]
            m = min(len(a), len(b))
            if m < 3:
                continue
            merged, me = [], []
            for k in range(m):
                merged.append(a[k][0]); me.append(a[k][1])
                merged.append(b[k][0]); me.append(b[k][1])
            r = compute_lcc(merged, np.vstack(me))["RAS"]
            if not np.isnan(r):
                vals.append(r)
        if vals:
            surr_means.append(np.mean(vals))
    surr = np.array(surr_means)
    p = float(np.mean(surr >= real.mean())) if len(surr) else np.nan
    return dict(real_mean=float(real.mean()),
                surr_mean=float(surr.mean()) if len(surr) else np.nan,
                p_real_gt_surr=p, n=int(len(real)))


# =========================================================================
# Synthetic method-validation (positive / negative controls)
# =========================================================================
def synthetic_control(dim=32, n_conv=80, n_turns=10, mode="reciprocal"):
    """Generate embedding sequences. reciprocal: B_t depends on A_{t-1} AND A_t depends
    on B_{t-1} (true bidirectional coupling). common: both driven by shared latent
    (no direct edge). independent: pure AR noise. Method must flag reciprocal only."""
    convs = []
    for _ in range(n_conv):
        A = np.zeros((n_turns, dim)); B = np.zeros((n_turns, dim))
        latent = RNG.standard_normal((n_turns, dim))
        A[0] = RNG.standard_normal(dim); B[0] = RNG.standard_normal(dim)
        for t in range(1, n_turns):
            if mode == "reciprocal":
                A[t] = 0.5 * A[t - 1] + 0.5 * B[t - 1] + 0.3 * RNG.standard_normal(dim)
                B[t] = 0.5 * B[t - 1] + 0.5 * A[t - 1] + 0.3 * RNG.standard_normal(dim)
            elif mode == "common":
                A[t] = 0.4 * A[t - 1] + 0.6 * latent[t] + 0.3 * RNG.standard_normal(dim)
                B[t] = 0.4 * B[t - 1] + 0.6 * latent[t] + 0.3 * RNG.standard_normal(dim)
            else:  # independent
                A[t] = 0.5 * A[t - 1] + 0.5 * RNG.standard_normal(dim)
                B[t] = 0.5 * B[t - 1] + 0.5 * RNG.standard_normal(dim)
        turns, emb = [], []
        for t in range(n_turns):
            turns.append(Turn("A", f"a{t}")); emb.append(A[t])
            turns.append(Turn("B", f"b{t}")); emb.append(B[t])
        e = np.vstack(emb); e = e / (np.linalg.norm(e, axis=1, keepdims=True) + 1e-12)
        convs.append((turns, e))
    return convs


# =========================================================================
# Runners
# =========================================================================
def build_convs(list_of_turnlists, embedder):
    all_txt = [t.text for turns in list_of_turnlists for t in turns]
    embedder.fit(all_txt)
    out = []
    for turns in list_of_turnlists:
        if len(turns) < 4:
            out.append(None); continue
        e = embedder.transform([t.text for t in turns])
        out.append((turns, e))
    return out


def metrics_df(convs):
    rows = []
    for c in convs:
        if c is None:
            rows.append({k: np.nan for k in
                         ["C", "S", "P_A_to_B", "P_B_to_A", "RAS", "L_add", "L_geo", "L_hybrid", "n_turns"]})
        else:
            rows.append(compute_lcc(*c))
    return pd.DataFrame(rows)


def run_hh(max_pairs: int):
    hh = pd.read_parquet(os.path.join(DATA_DIR, "hh_test.parquet"))
    hh = hh.iloc[:max_pairs]
    chosen = [parse_hh_string(s) for s in hh["chosen"]]
    rejected = [parse_hh_string(s) for s in hh["rejected"]]
    emb = LSAEmbedder(256)
    all_lists = chosen + rejected
    all_txt = [t.text for turns in all_lists for t in turns]
    emb.fit(all_txt)

    def to_convs(lists):
        out = []
        for turns in lists:
            if len(turns) < 4:
                out.append(None)
            else:
                out.append((turns, emb.transform([t.text for t in turns])))
        return out

    cc, rc = to_convs(chosen), to_convs(rejected)
    dc, dr = metrics_df(cc), metrics_df(rc)
    keep = (~dc["RAS"].isna()) & (~dr["RAS"].isna())
    dc2, dr2 = dc[keep].reset_index(drop=True), dr[keep].reset_index(drop=True)
    cols = ["C", "S", "RAS", "L_add", "L_geo", "L_hybrid"]
    wil = paired_wilcoxon(dc2, dr2, cols)
    fsets = {"C_only": ["C"], "C+RAS": ["C", "RAS"], "L_hybrid_only": ["L_hybrid"],
             "L_add_only": ["L_add"], "all": ["C", "S", "RAS"]}
    auc = cv_outcome_auc(dc2, dr2, fsets)
    surr = surrogate_ras_null([c for c in cc if c is not None][:150], n_surr=25)
    return dict(name="hh-rlhf", n_pairs_usable=int(keep.sum()),
                wilcoxon=wil, cv_auc=auc, surrogate=surr)


def run_mtbench():
    mt = pd.read_parquet(os.path.join(DATA_DIR, "mtbench_human.parquet"))
    mt = mt[mt["winner"].isin(["model_a", "model_b"])].reset_index(drop=True)
    if len(mt) > 900:
        mt = mt.sample(n=900, random_state=0).reset_index(drop=True)
    win_lists, lose_lists = [], []
    for _, r in mt.iterrows():
        ca, cb = parse_role_list(r["conversation_a"]), parse_role_list(r["conversation_b"])
        if r["winner"] == "model_a":
            win_lists.append(ca); lose_lists.append(cb)
        else:
            win_lists.append(cb); lose_lists.append(ca)
    emb = LSAEmbedder(256)
    emb.fit([t.text for L in (win_lists + lose_lists) for t in L])

    def to_convs(lists):
        return [((turns, emb.transform([t.text for t in turns])) if len(turns) >= 4 else None)
                for turns in lists]

    wc, lc = to_convs(win_lists), to_convs(lose_lists)
    dw, dl = metrics_df(wc), metrics_df(lc)
    keep = (~dw["RAS"].isna()) & (~dl["RAS"].isna())
    dw2, dl2 = dw[keep].reset_index(drop=True), dl[keep].reset_index(drop=True)
    cols = ["C", "S", "RAS", "L_add", "L_geo", "L_hybrid"]
    wil = paired_wilcoxon(dw2, dl2, cols)
    fsets = {"C_only": ["C"], "C+RAS": ["C", "RAS"], "L_hybrid_only": ["L_hybrid"],
             "L_add_only": ["L_add"], "all": ["C", "S", "RAS"]}
    auc = cv_outcome_auc(dw2, dl2, fsets)
    surr = surrogate_ras_null([c for c in wc if c is not None][:150], n_surr=25)
    return dict(name="mt_bench_human", n_pairs_usable=int(keep.sum()),
                wilcoxon=wil, cv_auc=auc, surrogate=surr)


def run_synthetic():
    out = {}
    for mode in ["reciprocal", "common", "independent"]:
        convs = synthetic_control(mode=mode)
        r = surrogate_ras_null(convs, n_surr=25)
        out[mode] = r
        print(f"  {mode:12s}: real_mean={r['real_mean']:.4f} surr_mean={r['surr_mean']:.4f} "
              f"p(real>=surr)={r['p_real_gt_surr']:.3f}  n={r['n']}", flush=True)
    return out


def _fmt(d):
    if isinstance(d, pd.DataFrame):
        return d.to_string(index=False)
    return json.dumps(d, indent=2, default=float)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max_pairs", type=int, default=3000)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__), "results.json"))
    args = ap.parse_args()

    print("=" * 70); print("SYNTHETIC METHOD-VALIDATION (positive/negative controls)"); print("=" * 70, flush=True)
    syn = run_synthetic()

    results = {"synthetic": syn, "datasets": {}}

    for label, runner in (("hh-rlhf", lambda: run_hh(args.max_pairs)), ("mt_bench", run_mtbench)):
        print(f"\n[running dataset stage: {label} ...]", flush=True)
        res = runner()
        results["datasets"][res["name"]] = {
            "n_pairs_usable": res["n_pairs_usable"],
            "wilcoxon": res["wilcoxon"].to_dict(orient="records"),
            "cv_auc": res["cv_auc"].to_dict(orient="records"),
            "surrogate": res["surrogate"],
        }
        print("\n" + "=" * 70); print(f"DATASET: {res['name']}  (usable paired convs = {res['n_pairs_usable']})"); print("=" * 70)
        print("[Prediction #1/#2] Paired Wilcoxon on (winner - loser) metric:")
        print(_fmt(res["wilcoxon"]))
        print("\n[Prediction #1 matched-control] 5-fold CV OOS AUC (winner vs loser):")
        print(_fmt(res["cv_auc"]))
        print("\n[Confound control] Cross-conversation surrogate RAS null:")
        print(_fmt(res["surrogate"]))

    with open(args.out, "w") as f:
        json.dump(results, f, indent=2, default=float)
    print(f"\nSaved: {args.out}")


if __name__ == "__main__":
    main()
