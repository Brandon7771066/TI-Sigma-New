"""
Papers Browser - Unified tab for all papers, downloads, cross-references, graphs.

Scans papers/, root-level *.md/*.tex/*.pdf, and attached_assets/ at runtime;
categorizes by URB number / topic prefix / date; provides per-file download;
renders URB cross-reference graph and category counts.
"""

import os
import re
import io
import datetime as dt
from collections import defaultdict, Counter
from pathlib import Path

import streamlit as st

st.set_page_config(page_title="Papers Browser", page_icon="📚", layout="wide")

PAPER_EXTS = {".md", ".pdf", ".tex", ".docx", ".txt"}
ROOT = Path(".")
SCAN_DIRS = [Path("papers"), Path("attached_assets")]
ROOT_GLOBS = ["*.md", "*.tex", "*.pdf"]

URB_RE = re.compile(r"URB[_\s#]?(\d{3,4})", re.IGNORECASE)
DATE_RE = re.compile(r"(20\d{2}[-_]\d{2}[-_]\d{2})")
ACRONYM_RE = re.compile(r"\b([A-Z]{2,6}(?:[-_][A-Z0-9]{1,4})?)\b")
TI_SIGMA_RE = re.compile(r"TI[\s\-_]?(?:Sigma|σ|Σ)|tralse[\s\-_]?informationalism", re.IGNORECASE)

# Stop-word acronyms (common English / formatting noise)
ACRONYM_STOP = {
    "THE", "AND", "OR", "NOT", "IS", "ARE", "WAS", "WERE", "BE", "HAS", "HAD",
    "DO", "DOES", "DID", "OF", "ON", "IN", "AT", "TO", "BY", "FOR", "FROM",
    "WITH", "AS", "AN", "A", "I", "II", "III", "IV", "V", "VI", "VII", "VIII",
    "IX", "X", "XI", "XII", "MD", "PHD", "DR", "MR", "MS", "MRS", "JR", "SR",
    "USA", "US", "UK", "EU", "AM", "PM", "ET", "PT", "EST", "PST", "UTC",
    "GMT", "CST", "MST", "API", "URL", "URI", "HTML", "CSS", "JS", "TS",
    "PDF", "MD", "TEX", "TXT", "CSV", "JSON", "XML", "YAML", "PNG", "JPG",
    "JPEG", "GIF", "ZIP", "TAR", "GZ", "OK", "NO", "YES", "TBD", "TODO",
    "FIXME", "WIP", "N", "M", "L", "K", "J", "P", "Q", "R", "S", "T",
}

# TI Sigma field taxonomy: keyword -> field
TI_SIGMA_FIELDS = {
    "Mathematics": [
        "riemann", "navier", "yang-mills", "yang_mills", "p=np", "hodge",
        "birch", "millennium", "hopf", "e8", "e_8", " lie ", "leech",
        "moonshine", "j-invariant", "j_invariant", "zeta", "ζ",
        "berry-keating", "berry_keating", "ubki", "uop", "twa", "wave algebra",
        "metacausal", "fractal harmonic", "fhs", "monster",
    ],
    "Physics / EM / Biophoton": [
        "biophoton", "electromagnetic", " em ", "em-dna", "em_dna", "popp",
        "photon", "polariz", "near-field", "far-field", "rf ", "phase-lock",
        "h_bfg", "field geometry", "thermodynamic",
    ],
    "Philosophy / Foundations": [
        "gile", "tralse", "intentionality", "asymmetric-standard", "asymmetric_standard",
        " mr ", "myrion", "myrion resolution", "bok", "verisyn", "being theorem",
        "five-valued", "5-valued", "double tralse", "dt immunity", "dpes",
        "self-containment", "validity criterion", "uop ", "ontolog",
    ],
    "Computation / Logic": [
        "ticl", "ternary", "arc-agi", "arc_agi", "lean4", "lean ", "hypercomputer",
        "tsc", "polycrystalline bec", "bec ", "sat solver", "sat-solver",
        "ti computing", "ti-computing", "5-valued logic", "five-valued logic",
        "quantum collapse simulator", "ternary computation",
    ],
    "Biology / Neuroscience": [
        "dna", "biopsychosignature", " bps ", "bps_", "mendi", "biowell",
        "polar h10", "oura", "gdv", "fnirs", "eeg", "hrv", "ssvep", " faah ",
        "telomere", "mitochond", "cpg", "epigenet", "fingerprint",
    ],
    "Consciousness / Psi": [
        " lcc ", "lcc_", "telepathy", " gcp ", "global consciousness",
        " psi ", "divination", "intention", "resonance", "mood amplifier",
        "mood-amplifier", "mre", "i-cell", "i_cell", "myceli", "chakra",
        "meridian", "psi-signature", "anchor",
    ],
    "Markets / Finance": [
        " gsa ", "gsa_", "grand stock algorithm", "stock", "alpaca",
        "kalshi", "collective2", "prediction market", "prediction-market",
        "ti framework", "ti-framework", "trading",
    ],
    "Bio-integration / Wellness": [
        "biowell", "biofeedback", "wellbeing", "wellness", "biometric",
        " gdv ", "ai-bio", "rescreen", "psi score", "chakra", "meridian",
    ],
}

TOPIC_PREFIXES = {
    "URB_": "URB Research Bulletins",
    "PHASE_": "Phase Experiments",
    "BPS_": "Biopsychosignature (BPS)",
    "BIOPHOTON": "Biophoton / EM-DNA (URB #826)",
    "BIOWELL": "Biowell",
    "MENDI": "Mendi fNIRS",
    "POLAR": "Polar H10",
    "BOK_": "BOK / Verisyn / Hopf",
    "TWA_": "Tralse Wave Algebra",
    "MOONSHINE": "Monster / Moonshine",
    "RIEMANN": "Riemann Hypothesis",
    "NAVIER": "Navier-Stokes",
    "MILLENNIUM": "Millennium Prize Problems",
    "LCC_": "LCC Telepathy / Resonance",
    "GCP_": "Global Consciousness Project",
    "GSA_": "Grand Stock Algorithm",
    "GILE": "GILE Framework",
    "TI_SIGMA": "TI Sigma",
    "TICL": "TICL Computing Language",
    "ARC_": "ARC-AGI",
    "TRALSE": "Tralse / Five-Valued Logic",
    "BINARY_TRALSE": "Binary Tralse Dialectic",
    "AGENT_LOCKED": "Agent-Locked Predictions",
    "PRIVACY": "Privacy / Compliance",
    "ZENODO": "Zenodo Submissions",
    "BRANDON": "Brandon Personal",
}


@st.cache_data(ttl=300)
def scan_papers():
    """Walk file system once, return list of file metadata dicts."""
    files = []
    for d in SCAN_DIRS:
        if not d.exists():
            continue
        for p in d.rglob("*"):
            if p.is_file() and p.suffix.lower() in PAPER_EXTS:
                files.append(_describe(p))
    for g in ROOT_GLOBS:
        for p in ROOT.glob(g):
            if p.is_file():
                files.append(_describe(p))
    return files


def _describe(p: Path):
    try:
        size = p.stat().st_size
        mtime = dt.datetime.fromtimestamp(p.stat().st_mtime)
    except OSError:
        size, mtime = 0, dt.datetime.fromtimestamp(0)
    name = p.name
    urb_match = URB_RE.search(name)
    urb_num = int(urb_match.group(1)) if urb_match else None
    date_match = DATE_RE.search(name)
    paper_date = date_match.group(1).replace("_", "-") if date_match else None
    topic = _topic_for(name)
    return {
        "path": str(p),
        "name": name,
        "ext": p.suffix.lower(),
        "size": size,
        "mtime": mtime,
        "urb": urb_num,
        "date": paper_date,
        "topic": topic,
    }


def _topic_for(name: str) -> str:
    upper = name.upper()
    for prefix, label in TOPIC_PREFIXES.items():
        if upper.startswith(prefix):
            return label
    if "URB" in upper and URB_RE.search(name):
        return "URB Research Bulletins"
    return "Other / Uncategorized"


@st.cache_data(ttl=300)
def scan_ti_sigma_atlas(files):
    """Identify TI Sigma papers and tag each with all matching fields.

    Returns: (ti_files, by_field) where by_field maps field_name -> list of files.
    """
    ti_files = []
    by_field = defaultdict(list)
    for f in files:
        if f["ext"] not in {".md", ".tex", ".txt"}:
            continue
        try:
            content = Path(f["path"]).read_text(errors="ignore")[:200_000]
        except OSError:
            continue
        # Identify TI-Sigma-related papers (name match OR content match)
        is_ti = bool(TI_SIGMA_RE.search(f["name"])) or bool(TI_SIGMA_RE.search(content))
        if not is_ti:
            continue
        haystack = (f["name"] + " " + content).lower()
        matched_fields = []
        for field, kws in TI_SIGMA_FIELDS.items():
            if any(kw in haystack for kw in kws):
                matched_fields.append(field)
                by_field[field].append(f)
        if not matched_fields:
            by_field["Uncategorized TI Sigma"].append(f)
            matched_fields = ["Uncategorized TI Sigma"]
        ti_files.append({**f, "ti_fields": matched_fields})
    return ti_files, by_field


@st.cache_data(ttl=300)
def extract_acronyms_index(files, max_files: int = 600, max_bytes: int = 80_000):
    """Auto-extract acronyms from .md/.tex/.txt content. Returns Counter + per-acronym
    file list (top 5 example files per acronym)."""
    counts = Counter()
    examples = defaultdict(list)
    scanned = 0
    for f in files:
        if scanned >= max_files:
            break
        if f["ext"] not in {".md", ".tex", ".txt"}:
            continue
        try:
            content = Path(f["path"]).read_text(errors="ignore")[:max_bytes]
        except OSError:
            continue
        scanned += 1
        seen_in_file = set()
        for m in ACRONYM_RE.finditer(content):
            acr = m.group(1)
            if acr in ACRONYM_STOP:
                continue
            counts[acr] += 1
            if acr not in seen_in_file:
                seen_in_file.add(acr)
                if len(examples[acr]) < 5:
                    examples[acr].append(f["name"])
    return counts, dict(examples), scanned


@st.cache_data(ttl=300)
def build_urb_graph(files):
    """Parse markdown files for 'URB #N' cross-references; return edges."""
    edges = defaultdict(int)
    nodes = set()
    for f in files:
        if f["ext"] != ".md" or f["urb"] is None:
            continue
        src = f["urb"]
        nodes.add(src)
        try:
            content = Path(f["path"]).read_text(errors="ignore")
        except OSError:
            continue
        for m in URB_RE.finditer(content):
            tgt = int(m.group(1))
            if tgt != src:
                edges[(src, tgt)] += 1
                nodes.add(tgt)
    return nodes, edges


def fmt_size(n):
    for u in ["B", "KB", "MB", "GB"]:
        if n < 1024:
            return f"{n:.1f}{u}"
        n /= 1024
    return f"{n:.1f}TB"


# --- UI ---

st.title("📚 Papers Browser")
st.caption(
    "Unified index of all research documents. Scan / search / download / "
    "view URB cross-reference graph. asymmetric-standards #69."
)

with st.spinner("Scanning filesystem..."):
    files = scan_papers()

if not files:
    st.error("No papers found. Check that `papers/` exists.")
    st.stop()

# --- Top metrics ---
c1, c2, c3, c4 = st.columns(4)
c1.metric("Total documents", f"{len(files):,}")
c2.metric("Markdown (.md)", sum(1 for f in files if f["ext"] == ".md"))
c3.metric("PDF (.pdf)", sum(1 for f in files if f["ext"] == ".pdf"))
c4.metric("URB papers", sum(1 for f in files if f["urb"] is not None))

# --- Sidebar filters ---
st.sidebar.header("Filters")
search = st.sidebar.text_input("Filename search (substring, case-insensitive)").strip().lower()

ext_options = sorted({f["ext"] for f in files})
ext_filter = st.sidebar.multiselect("File type", ext_options, default=ext_options)

topics = sorted({f["topic"] for f in files})
topic_filter = st.sidebar.multiselect("Topic", topics, default=[])
if not topic_filter:
    topic_filter = topics

date_filter = st.sidebar.date_input("Modified after", value=None)

sort_by = st.sidebar.selectbox(
    "Sort by", ["Modified (newest)", "Name", "URB number", "Size"]
)


def matches(f):
    if search and search not in f["name"].lower():
        return False
    if f["ext"] not in ext_filter:
        return False
    if f["topic"] not in topic_filter:
        return False
    if date_filter and f["mtime"].date() < date_filter:
        return False
    return True


filtered = [f for f in files if matches(f)]
if sort_by == "Modified (newest)":
    filtered.sort(key=lambda f: f["mtime"], reverse=True)
elif sort_by == "Name":
    filtered.sort(key=lambda f: f["name"].lower())
elif sort_by == "URB number":
    filtered.sort(key=lambda f: (f["urb"] is None, f["urb"] or 0), reverse=True)
elif sort_by == "Size":
    filtered.sort(key=lambda f: f["size"], reverse=True)

st.write(f"**{len(filtered):,}** documents match current filters")

# --- Tabs ---
(
    tab_browse,
    tab_urb,
    tab_topics,
    tab_ti_sigma,
    tab_index,
    tab_graph,
    tab_timeline,
) = st.tabs([
    "Browse & Download",
    "URBs by Number",
    "By Topic",
    "TI Sigma Atlas",
    "Index & Acronyms",
    "Cross-Reference Graph",
    "Timeline",
])

with tab_browse:
    st.subheader("All matching documents")
    page_size = 50
    total_pages = (len(filtered) - 1) // page_size + 1 if filtered else 1
    page = st.number_input("Page", 1, max(1, total_pages), 1)
    chunk = filtered[(page - 1) * page_size: page * page_size]
    for f in chunk:
        with st.container(border=True):
            top, bot = st.columns([4, 1])
            with top:
                urb_badge = f"`URB #{f['urb']}` " if f["urb"] else ""
                st.markdown(f"**{urb_badge}{f['name']}**")
                st.caption(
                    f"Topic: {f['topic']} · {f['ext']} · "
                    f"{fmt_size(f['size'])} · "
                    f"modified {f['mtime'].strftime('%Y-%m-%d %H:%M')}"
                    + (f" · paper date {f['date']}" if f["date"] else "")
                )
                st.caption(f"`{f['path']}`")
            with bot:
                try:
                    with open(f["path"], "rb") as fh:
                        st.download_button(
                            "Download",
                            data=fh.read(),
                            file_name=f["name"],
                            key=f"dl_{f['path']}",
                            use_container_width=True,
                        )
                except OSError:
                    st.caption("(unreadable)")

with tab_urb:
    st.subheader("URBs by number")
    urb_files = [f for f in filtered if f["urb"] is not None]
    by_urb = defaultdict(list)
    for f in urb_files:
        by_urb[f["urb"]].append(f)
    for urb_num in sorted(by_urb.keys(), reverse=True):
        with st.expander(
            f"URB #{urb_num} — {len(by_urb[urb_num])} document(s)",
            expanded=(urb_num >= 826),
        ):
            for f in sorted(by_urb[urb_num], key=lambda x: x["mtime"], reverse=True):
                cols = st.columns([5, 1])
                cols[0].write(f"`{f['name']}` · {fmt_size(f['size'])} · {f['mtime'].strftime('%Y-%m-%d')}")
                try:
                    with open(f["path"], "rb") as fh:
                        cols[1].download_button(
                            "↓",
                            data=fh.read(),
                            file_name=f["name"],
                            key=f"urb_dl_{f['path']}",
                        )
                except OSError:
                    cols[1].caption("(err)")

with tab_topics:
    st.subheader("By topic")
    topic_counts = Counter(f["topic"] for f in filtered)
    st.bar_chart(topic_counts)
    by_topic = defaultdict(list)
    for f in filtered:
        by_topic[f["topic"]].append(f)
    for topic in sorted(by_topic.keys(), key=lambda t: -len(by_topic[t])):
        with st.expander(f"{topic} — {len(by_topic[topic])} document(s)"):
            for f in sorted(by_topic[topic], key=lambda x: x["mtime"], reverse=True)[:50]:
                cols = st.columns([5, 1])
                cols[0].write(f"`{f['name']}` · {fmt_size(f['size'])} · {f['mtime'].strftime('%Y-%m-%d')}")
                try:
                    with open(f["path"], "rb") as fh:
                        cols[1].download_button(
                            "↓",
                            data=fh.read(),
                            file_name=f["name"],
                            key=f"topic_dl_{f['path']}",
                        )
                except OSError:
                    cols[1].caption("(err)")
            if len(by_topic[topic]) > 50:
                st.caption(f"...and {len(by_topic[topic]) - 50} more (use Browse tab)")

with tab_ti_sigma:
    st.subheader("TI Sigma Atlas — concepts, theories, and proofs across fields")
    st.caption(
        "Auto-tagged. A paper is included if its filename or first 200KB of "
        "content references TI Sigma / Tralse Informationalism. Each paper is "
        "cross-listed in every field whose keywords appear in it."
    )
    with st.spinner("Scanning TI Sigma corpus..."):
        ti_files, by_field = scan_ti_sigma_atlas(files)
    if not ti_files:
        st.info("No TI Sigma references found.")
    else:
        a, b, c = st.columns(3)
        a.metric("TI Sigma documents", len(ti_files))
        b.metric("Fields covered", len([k for k, v in by_field.items() if v]))
        c.metric("Cross-listings (field tags)", sum(len(v) for v in by_field.values()))
        # Field-count chart
        field_counts = {k: len(v) for k, v in by_field.items() if v}
        st.bar_chart(field_counts)
        # Per-field expanders
        for field in sorted(by_field.keys(), key=lambda k: -len(by_field[k])):
            entries = by_field[field]
            if not entries:
                continue
            with st.expander(f"{field} — {len(entries)} document(s)"):
                # Sub-categorize within field by topic prefix
                by_subtopic = defaultdict(list)
                for f in entries:
                    by_subtopic[f["topic"]].append(f)
                for sub in sorted(by_subtopic.keys()):
                    st.markdown(f"**{sub}** ({len(by_subtopic[sub])})")
                    for f in sorted(by_subtopic[sub], key=lambda x: x["mtime"], reverse=True)[:30]:
                        cols = st.columns([5, 1])
                        urb = f"`URB #{f['urb']}` " if f["urb"] else ""
                        cols[0].write(f"{urb}`{f['name']}` · {fmt_size(f['size'])} · {f['mtime'].strftime('%Y-%m-%d')}")
                        try:
                            with open(f["path"], "rb") as fh:
                                cols[1].download_button(
                                    "↓",
                                    data=fh.read(),
                                    file_name=f["name"],
                                    key=f"tisigma_dl_{field}_{f['path']}",
                                )
                        except OSError:
                            cols[1].caption("(err)")
                    if len(by_subtopic[sub]) > 30:
                        st.caption(f"...and {len(by_subtopic[sub]) - 30} more")

with tab_index:
    st.subheader("Continually-updated Index & Acronym Glossary")
    st.caption(
        "Refreshes every 5 minutes (cached). Subcategory counts are scoped to the "
        "current sidebar filters. Acronym extraction scans up to the first ~80KB of "
        "the most recent 600 markdown / TeX / text files."
    )

    # Subcategory index
    st.markdown("### Subcategory index (filtered)")
    idx_cols = st.columns(2)
    with idx_cols[0]:
        st.markdown("**By topic prefix**")
        topic_idx = Counter(f["topic"] for f in filtered)
        for t, c in sorted(topic_idx.items(), key=lambda kv: -kv[1]):
            st.write(f"- {t} — **{c}**")
    with idx_cols[1]:
        st.markdown("**By file extension**")
        ext_idx = Counter(f["ext"] for f in filtered)
        for e, c in sorted(ext_idx.items(), key=lambda kv: -kv[1]):
            st.write(f"- `{e}` — **{c}**")
        st.markdown("**By URB-status**")
        with_urb = sum(1 for f in filtered if f["urb"] is not None)
        st.write(f"- has URB number — **{with_urb}**")
        st.write(f"- no URB number — **{len(filtered) - with_urb}**")

    # TI Sigma sub-index
    st.markdown("### TI Sigma field index (full corpus)")
    ti_files, by_field = scan_ti_sigma_atlas(files)
    for field in sorted(by_field.keys(), key=lambda k: -len(by_field[k])):
        if by_field[field]:
            st.write(f"- {field} — **{len(by_field[field])}**")

    # Acronyms
    st.markdown("### Acronym glossary (auto-extracted, top 200)")
    with st.spinner("Extracting acronyms..."):
        ac_counts, ac_examples, n_scanned = extract_acronyms_index(files)
    st.caption(f"Scanned {n_scanned} text-format files. {len(ac_counts)} unique acronyms found.")
    search_acr = st.text_input("Filter acronyms (substring)").strip().upper()
    top = ac_counts.most_common(500)
    if search_acr:
        top = [(a, c) for a, c in top if search_acr in a]
    top = top[:200]
    if not top:
        st.info("No acronyms match.")
    else:
        for acr, cnt in top:
            with st.expander(f"**{acr}** — {cnt} occurrence(s)"):
                exs = ac_examples.get(acr, [])
                if exs:
                    st.write("Example files:")
                    for ex in exs:
                        st.write(f"- `{ex}`")
                else:
                    st.caption("(no examples cached)")

with tab_graph:
    st.subheader("URB cross-reference graph")
    st.caption(
        "Edge from URB A → URB B means A's text mentions B. "
        "Auto-extracted from .md content."
    )
    nodes, edges = build_urb_graph(files)
    if not edges:
        st.info("No URB cross-references found in scanned files.")
    else:
        min_urb = st.slider(
            "Show URBs from #", min(nodes), max(nodes), max(min(nodes), max(nodes) - 30)
        )
        active_nodes = {n for n in nodes if n >= min_urb}
        active_edges = {(s, t): w for (s, t), w in edges.items() if s in active_nodes and t in active_nodes}
        dot_lines = ["digraph URB {", '  rankdir=LR;', '  node [shape=box, style=filled, fillcolor="#FFF0F5"];']
        for n in sorted(active_nodes):
            color = "#FFD6E5" if n >= 826 else "#FFF0F5"
            dot_lines.append(f'  "URB {n}" [fillcolor="{color}"];')
        for (s, t), w in sorted(active_edges.items()):
            penwidth = min(1 + w / 3, 4)
            dot_lines.append(f'  "URB {s}" -> "URB {t}" [penwidth={penwidth:.1f}];')
        dot_lines.append("}")
        st.graphviz_chart("\n".join(dot_lines), use_container_width=True)
        st.caption(
            f"Showing {len(active_nodes)} URBs and {len(active_edges)} cross-references "
            f"(of {len(nodes)} URBs and {len(edges)} edges total)."
        )

with tab_timeline:
    st.subheader("Documents over time (by file mtime)")
    by_month = Counter(f["mtime"].strftime("%Y-%m") for f in filtered)
    st.bar_chart(dict(sorted(by_month.items())))
    st.subheader("Recent activity (top 30)")
    for f in sorted(filtered, key=lambda x: x["mtime"], reverse=True)[:30]:
        st.write(
            f"{f['mtime'].strftime('%Y-%m-%d %H:%M')} · "
            f"`{f['name']}` · {f['topic']}"
        )

st.divider()
st.caption(
    "Cross-references: `papers/URB_828_BPS_STACKING_HYPOTHESIS.md`, "
    "`papers/BPS_TERM_INTRODUCTION_2026-05-01.md`, "
    "`papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md`, "
    "`PIPELINE.md`"
)
