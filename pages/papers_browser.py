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
tab_browse, tab_urb, tab_topics, tab_graph, tab_timeline = st.tabs([
    "Browse & Download",
    "URBs by Number",
    "By Topic",
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
