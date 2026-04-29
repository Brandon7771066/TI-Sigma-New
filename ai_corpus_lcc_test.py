"""URB #806 — AI-Corpus LCC Test

Tests whether the AI-generated TI Sigma corpus (1100+ papers in papers/)
obeys LCC dynamics with a meaningful C_EMERICK threshold.

Operationalization (corpus-as-AI-output):
  Each paper is a token stream the AI produced through Brandon's
  collaborative workflow. Pairs of papers fall into three conditions
  based on observable inter-paper structure:

  STRONG:   A cites B by URB-number, AND both share a topic cluster
            (cluster determined by Jaccard-overlap of distinctive 4-grams,
            independently of citation graph). Predicted: HIGH LCC.

  WEAK:     A cites B by URB-number, BUT they belong to different
            topic clusters. Predicted: MIDDLE LCC.

  INDEPENDENT: Neither A cites B nor B cites A, AND they are in
            different topic clusters. Predicted: LOW LCC, near zero.

We then test:
  1. Mean LCC ordering: STRONG > WEAK > INDEPENDENT (predicted).
  2. ROC-AUC for STRONG-vs-INDEPENDENT discrimination.
  3. Fraction of STRONG pairs above C_EMERICK = 1/(phi*sqrt(2)) ~= 0.4370.

Form B LCC, sigma=5.0, max_lag=15. Tokens = simple lowercase word indices
into a vocabulary of the top-K most-frequent words across the whole corpus
(K=1024). T=300 token segments per paper, segment from paper midpoint.
"""

import json
import math
import os
import re
import time
from collections import Counter, defaultdict

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PHI = (1.0 + 5.0**0.5) / 2.0
C_EMERICK = 1.0 / (PHI * 2.0**0.5)
PAPERS_DIR = "papers"
T_SEG = 300
VOCAB_K = 1024
SIGMA = 5.0
MAX_LAG = 15
MIN_PAPER_TOKENS = 600
SEED = 2026


def lcc_resonance_form_b(a: np.ndarray, b: np.ndarray, sigma: float = SIGMA, max_lag: int = MAX_LAG) -> float:
    """Form B per URB #800 §4: sign-preserving max over |tau| <= 3*sigma of rho(tau)*W(tau)."""
    a = (a - a.mean()) / (a.std() + 1e-12)
    b = (b - b.mean()) / (b.std() + 1e-12)
    n = len(a)
    best = 0.0
    for tau in range(-max_lag, max_lag + 1):
        if tau >= 0:
            x = a[: n - tau]
            y = b[tau:]
        else:
            x = a[-tau:]
            y = b[: n + tau]
        if len(x) < 2:
            continue
        rho = float(np.dot(x, y) / len(x))
        w = math.exp(-(tau * tau) / (2.0 * sigma * sigma))
        v = rho * w
        if abs(v) > abs(best):
            best = v
    return best


def tokenize(text: str) -> list[str]:
    return re.findall(r"[a-z0-9]+", text.lower())


def load_corpus(papers_dir: str = PAPERS_DIR) -> dict[str, list[str]]:
    """Returns {paper_basename: list[token]} for all .md files with enough tokens."""
    out = {}
    for fname in sorted(os.listdir(papers_dir)):
        if not fname.endswith(".md"):
            continue
        path = os.path.join(papers_dir, fname)
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                txt = f.read()
        except Exception:
            continue
        toks = tokenize(txt)
        if len(toks) >= MIN_PAPER_TOKENS:
            out[fname] = toks
    return out


def build_vocab(corpus: dict[str, list[str]], k: int = VOCAB_K) -> dict[str, int]:
    """Top-K most-frequent tokens across whole corpus, mapped to integer ids 1..k.
    OOV words map to id 0."""
    counts: Counter[str] = Counter()
    for toks in corpus.values():
        counts.update(toks)
    vocab = {tok: i + 1 for i, (tok, _) in enumerate(counts.most_common(k))}
    return vocab


def to_int_stream(toks: list[str], vocab: dict[str, int]) -> np.ndarray:
    return np.array([vocab.get(t, 0) for t in toks], dtype=np.float64)


def midpoint_segment(stream: np.ndarray, t_seg: int = T_SEG) -> np.ndarray:
    n = len(stream)
    if n < t_seg:
        return np.zeros(0, dtype=np.float64)
    mid = n // 2
    a = max(0, mid - t_seg // 2)
    return stream[a : a + t_seg].astype(np.float64)


def parse_urb_number(fname: str) -> int | None:
    m = re.match(r"(?i)urb[_ ]?(\d+)[_\.]", fname)
    if m:
        return int(m.group(1))
    return None


def find_citations(text: str) -> set[int]:
    """Return set of URB numbers cited in this paper.
    Matches: 'URB #800', 'URB_800', 'URBs #801', 'urb 800', 'urb800', etc.
    """
    cites = set()
    for m in re.finditer(r"(?i)\burb[s]?[_\s#]*?(\d{2,4})\b", text):
        try:
            n = int(m.group(1))
            if 1 <= n <= 9999:
                cites.add(n)
        except ValueError:
            pass
    return cites


def build_citation_graph(papers_dir: str, corpus: dict[str, list[str]]) -> tuple[dict[int, str], dict[int, set[int]]]:
    """
    Returns:
      urb_to_fname: {urb_number: paper_basename} for papers we could parse
      cite_graph: {urb_number: set[urb_number]} of citations from -> to
    """
    urb_to_fname: dict[int, str] = {}
    for fname in corpus:
        n = parse_urb_number(fname)
        if n is not None:
            urb_to_fname[n] = fname
    cite_graph: dict[int, set[int]] = defaultdict(set)
    for urb_n, fname in urb_to_fname.items():
        path = os.path.join(papers_dir, fname)
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                txt = f.read()
        except Exception:
            continue
        cites = find_citations(txt)
        cites.discard(urb_n)
        cite_graph[urb_n] = cites & set(urb_to_fname.keys())
    return urb_to_fname, dict(cite_graph)


def topic_signature(toks: list[str], top_n: int = 30) -> set[str]:
    """Distinctive content words for clustering."""
    stop = {
        "the","of","and","a","to","in","is","that","this","it","for","on","with","as","by",
        "an","be","are","at","or","not","we","but","from","which","can","has","have","its",
        "if","then","also","more","one","only","most","such","each","all","any","other",
        "some","into","than","both","very","may","two","three","four","five","six","new","no",
        "do","so","up","you","he","she","they","i","my","your","our","their","what","when",
        "where","how","why","who","will","would","should","could","been","were","was","being",
        "use","used","using","there","these","those","here","data","results","figure","table",
        "section","paper","urb","note","fig","tbl","ref","et","al","page","p","pp","vol","no",
    }
    counts = Counter(t for t in toks if t not in stop and len(t) > 3)
    return set(t for t, _ in counts.most_common(top_n))


def topic_cluster_distance(sig_a: set[str], sig_b: set[str]) -> float:
    """Jaccard distance on top-30 distinctive content words. 0 = same topic, 1 = totally different."""
    inter = len(sig_a & sig_b)
    union = len(sig_a | sig_b)
    if union == 0:
        return 1.0
    return 1.0 - inter / union


def sample_pairs(corpus, urb_to_fname, cite_graph, signatures, n_per_cond: int, rng: np.random.Generator):
    """Sample STRONG / WEAK / INDEPENDENT pairs by reference + topic structure."""
    urb_nums = list(urb_to_fname.keys())
    edges = [(a, b) for a in cite_graph for b in cite_graph[a]]

    strong, weak, indep = [], [], []
    for a, b in edges:
        d = topic_cluster_distance(signatures[urb_to_fname[a]], signatures[urb_to_fname[b]])
        if d <= 0.85:  # share at least some distinctive vocab
            strong.append((a, b))
        else:
            weak.append((a, b))

    cited_set = set()
    for a in cite_graph:
        cited_set.add(a)
        for b in cite_graph[a]:
            cited_set.add(b)

    attempts, max_attempts = 0, n_per_cond * 200
    while len(indep) < n_per_cond and attempts < max_attempts:
        attempts += 1
        a, b = rng.choice(urb_nums, size=2, replace=False)
        if int(b) in cite_graph.get(int(a), set()):
            continue
        if int(a) in cite_graph.get(int(b), set()):
            continue
        d = topic_cluster_distance(signatures[urb_to_fname[int(a)]], signatures[urb_to_fname[int(b)]])
        if d >= 0.95:  # essentially no shared distinctive vocab
            indep.append((int(a), int(b)))

    rng.shuffle(strong)
    rng.shuffle(weak)
    rng.shuffle(indep)
    return strong[:n_per_cond], weak[:n_per_cond], indep[:n_per_cond]


def lcc_for_pair(a_fname, b_fname, int_streams):
    sa = midpoint_segment(int_streams[a_fname])
    sb = midpoint_segment(int_streams[b_fname])
    if len(sa) < T_SEG or len(sb) < T_SEG:
        return None
    return lcc_resonance_form_b(sa, sb)


def roc_auc_one_sided(scores_pos: np.ndarray, scores_neg: np.ndarray) -> float:
    n_pos, n_neg = len(scores_pos), len(scores_neg)
    if n_pos == 0 or n_neg == 0:
        return float("nan")
    all_scores = np.concatenate([scores_pos, scores_neg])
    all_labels = np.concatenate([np.ones(n_pos), np.zeros(n_neg)])
    order = np.argsort(-all_scores, kind="mergesort")
    sorted_labels = all_labels[order]
    tp_cum = np.cumsum(sorted_labels)
    fp_cum = np.cumsum(1 - sorted_labels)
    tpr = tp_cum / n_pos
    fpr = fp_cum / n_neg
    tpr = np.concatenate([[0.0], tpr])
    fpr = np.concatenate([[0.0], fpr])
    return float(np.trapz(tpr, fpr))


def main():
    t0 = time.time()
    rng = np.random.default_rng(SEED)
    print(f"[{time.time()-t0:.1f}s] Loading papers/ ...")
    corpus = load_corpus(PAPERS_DIR)
    print(f"  loaded {len(corpus)} papers (>= {MIN_PAPER_TOKENS} tokens each)")

    print(f"[{time.time()-t0:.1f}s] Building vocab (top {VOCAB_K}) ...")
    vocab = build_vocab(corpus, VOCAB_K)
    int_streams = {fn: to_int_stream(toks, vocab) for fn, toks in corpus.items()}

    print(f"[{time.time()-t0:.1f}s] Building citation graph ...")
    urb_to_fname, cite_graph = build_citation_graph(PAPERS_DIR, corpus)
    n_edges = sum(len(v) for v in cite_graph.values())
    print(f"  parsed {len(urb_to_fname)} URB-numbered papers; {n_edges} citation edges")

    print(f"[{time.time()-t0:.1f}s] Building topic signatures ...")
    signatures = {fn: topic_signature(toks) for fn, toks in corpus.items()}

    print(f"[{time.time()-t0:.1f}s] Sampling pair conditions ...")
    n_per_cond = 100
    strong, weak, indep = sample_pairs(corpus, urb_to_fname, cite_graph, signatures, n_per_cond, rng)
    print(f"  STRONG={len(strong)}  WEAK={len(weak)}  INDEPENDENT={len(indep)}")

    print(f"[{time.time()-t0:.1f}s] Computing LCC for all pairs ...")
    cond_lcc = {"strong": [], "weak": [], "independent": []}
    for cond_name, pairs in (("strong", strong), ("weak", weak), ("independent", indep)):
        for a, b in pairs:
            r = lcc_for_pair(urb_to_fname[a], urb_to_fname[b], int_streams)
            if r is not None:
                cond_lcc[cond_name].append(r)

    summary = {}
    for k, vals in cond_lcc.items():
        arr = np.array(vals, dtype=np.float64)
        summary[k] = {
            "n": int(len(arr)),
            "mean": float(arr.mean()) if len(arr) else float("nan"),
            "std": float(arr.std()) if len(arr) else float("nan"),
            "median": float(np.median(arr)) if len(arr) else float("nan"),
            "frac_above_C_EMERICK": float((arr >= C_EMERICK).mean()) if len(arr) else float("nan"),
        }

    auc_strong_vs_indep = roc_auc_one_sided(
        np.array(cond_lcc["strong"]),
        np.array(cond_lcc["independent"]),
    )
    auc_weak_vs_indep = roc_auc_one_sided(
        np.array(cond_lcc["weak"]),
        np.array(cond_lcc["independent"]),
    )

    print(f"\n[{time.time()-t0:.1f}s] === RESULTS ===")
    print(f"C_EMERICK = {C_EMERICK:.5f}")
    for k in ("strong", "weak", "independent"):
        s = summary[k]
        print(
            f"  {k:>11}  n={s['n']:>3}  mean={s['mean']:+.4f}  std={s['std']:.4f}  "
            f"median={s['median']:+.4f}  frac>=C_E={s['frac_above_C_EMERICK']*100:5.1f}%"
        )
    print(f"  ROC-AUC strong vs independent: {auc_strong_vs_indep:.3f}")
    print(f"  ROC-AUC weak   vs independent: {auc_weak_vs_indep:.3f}")

    report = {
        "C_EMERICK": C_EMERICK,
        "vocab_size": VOCAB_K,
        "T_seg": T_SEG,
        "sigma": SIGMA,
        "max_lag": MAX_LAG,
        "n_papers_used": len(corpus),
        "n_urb_papers": len(urb_to_fname),
        "n_citation_edges": n_edges,
        "n_per_cond_target": n_per_cond,
        "summary": summary,
        "auc_strong_vs_independent": auc_strong_vs_indep,
        "auc_weak_vs_independent": auc_weak_vs_indep,
        "wall_time_s": float(time.time() - t0),
    }
    with open("ai_corpus_lcc_test_report.json", "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))
    bins = np.linspace(-0.4, 1.0, 35)
    for cond_name, color in (("independent", "tab:gray"), ("weak", "tab:orange"), ("strong", "tab:blue")):
        axes[0].hist(cond_lcc[cond_name], bins=bins, alpha=0.55, label=f"{cond_name} (n={len(cond_lcc[cond_name])})", color=color)
    axes[0].axvline(C_EMERICK, color="red", linestyle="--", label=f"C_EMERICK={C_EMERICK:.4f}")
    axes[0].set_xlabel("Pairwise LCC (Form B)")
    axes[0].set_ylabel("count")
    axes[0].set_title("AI-corpus pairwise LCC by condition")
    axes[0].legend()

    fracs = [summary[k]["frac_above_C_EMERICK"] * 100 for k in ("strong", "weak", "independent")]
    axes[1].bar(["strong", "weak", "indep"], fracs, color=["tab:blue", "tab:orange", "tab:gray"])
    axes[1].set_ylabel("% pairs with LCC >= C_EMERICK")
    axes[1].set_title("Fraction above C_EMERICK by condition")
    for i, v in enumerate(fracs):
        axes[1].text(i, v + 1, f"{v:.1f}%", ha="center")

    plt.tight_layout()
    plt.savefig("ai_corpus_lcc_test.png", dpi=120)
    plt.close()
    print(f"\n[{time.time()-t0:.1f}s] wrote ai_corpus_lcc_test_report.json + ai_corpus_lcc_test.png")


if __name__ == "__main__":
    main()
