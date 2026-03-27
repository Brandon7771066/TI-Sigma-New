"""
TI Sigma Paper Classification Hub
Streamlit page for reviewing, editing, and exporting paper classifications.
"""
import streamlit as st
import pandas as pd
from pathlib import Path
from paper_classifier import (
    init_classification_db,
    get_all_classifications,
    upsert_classification,
    update_field,
    run_batch_classification,
    get_researchgate_list,
    get_arxiv_list,
    get_zenodo_privacy_map,
    get_summary_counts,
    PAPERS_DIR,
)

RADICALITY_LABELS = {
    1: "1 — Mainstream",
    2: "2 — Heterodox/Citable",
    3: "3 — Speculative",
    4: "4 — Paradigm-Challenging",
    5: "5 — Novel Framework",
}

JOURNAL_TIER_OPTIONS = [
    "top_tier",
    "mid_tier",
    "fringe_peer_reviewed",
    "zenodo_only",
]

ZENODO_STATUS_OPTIONS = ["unpublished", "published", "private"]

DOMAIN_OPTIONS = [
    "consciousness", "physics", "mathematics", "philosophy", "psychology",
    "neuroscience", "biology", "finance", "computing", "quantum",
    "music_sound", "psychology_clinical", "social_theory", "spirituality",
    "language", "ecology", "information_theory",
]


def render():
    st.title("📄 Paper Classification Hub")

    init_classification_db()
    counts = get_summary_counts()

    st.caption(
        f"Classify and route {counts['total_papers']} TI Sigma papers "
        "across ResearchGate, arXiv, and Zenodo."
    )

    # First-load auto-classification: run once silently if papers exist but none classified
    if counts["classified"] == 0 and counts["total_papers"] > 0:
        if not st.session_state.get("_auto_classify_done"):
            st.session_state["_auto_classify_done"] = True
            with st.spinner(f"First run: classifying {counts['total_papers']} papers..."):
                run_batch_classification(force=False)
            st.rerun()

    col1, col2, col3, col4, col5 = st.columns(5)
    col1.metric("Total Papers", counts["total_papers"])
    col2.metric("Classified", counts["classified"],
                f"{counts['unclassified']} unclassified" if counts["unclassified"] else "all done")
    col3.metric("ResearchGate-Ready", counts["researchgate"], "Radicality 1-2")
    col4.metric("arXiv-Eligible", counts["arxiv"], "Radicality 1-3")
    col5.metric("Zenodo Private", counts["zenodo_private"], "Radicality 5")

    st.divider()

    tab_classify, tab_review, tab_rg, tab_arxiv, tab_zenodo = st.tabs([
        "🤖 AI Classify",
        "📋 Review & Edit",
        "🔬 ResearchGate List",
        "📐 arXiv Checklist",
        "🔒 Zenodo Privacy Map",
    ])

    with tab_classify:
        _render_classify_tab(counts)

    with tab_review:
        _render_review_tab()

    with tab_rg:
        _render_researchgate_tab()

    with tab_arxiv:
        _render_arxiv_tab()

    with tab_zenodo:
        _render_zenodo_tab()


def _render_classify_tab(counts: dict):
    st.subheader("Auto-Classification Engine")

    unclassified = counts["unclassified"]
    classified   = counts["classified"]
    total        = counts["total_papers"]

    if classified > 0:
        st.progress(classified / max(total, 1),
                    text=f"{classified}/{total} papers classified")

    col1, col2 = st.columns(2)
    with col1:
        st.info(
            f"**{unclassified} papers** have not been classified yet.\n\n"
            "The classifier reads each paper's filename, title, and first 1,500 characters "
            "of content, then applies a keyword/heuristic engine to assign:\n"
            "radicality (1-5), formal proof flag, journal tier, domain tags, "
            "and platform assignment.\n\n"
            "**Cost: Free — no API calls needed.** Runs entirely offline."
        )
    with col2:
        st.success(
            "**Keyword Engine**\n\n"
            "Classification uses a curated ruleset built specifically for the TI Sigma corpus. "
            "TI-specific terms (LCC, GILE, TRALSE, MR gates, BOK, etc.) push papers to "
            "radicality 4-5. Conventional empirical terms push toward 1-2. "
            "You can always adjust any classification manually in the Review tab.\n\n"
            "Already-classified papers are skipped automatically."
        )

    col_a, col_b = st.columns(2)
    with col_a:
        if st.button("🚀 Classify Unclassified Papers",
                     type="primary",
                     disabled=(unclassified == 0),
                     use_container_width=True):
            _run_classification(force=False)

    with col_b:
        if st.button("🔄 Re-classify ALL Papers",
                     type="secondary",
                     use_container_width=True):
            if st.session_state.get("reclassify_confirm"):
                _run_classification(force=True)
                st.session_state["reclassify_confirm"] = False
            else:
                st.session_state["reclassify_confirm"] = True
                st.warning("Click again to confirm re-classifying ALL papers (overwrites manual edits).")

    st.subheader("Radicality Rubric Reference")
    st.markdown("""
| Score | Label | Description | Venue |
|-------|-------|-------------|-------|
| **1** | Mainstream | Standard empirical science, no TI-specific claims | Nature, Science, Frontiers |
| **2** | Heterodox/Citable | Challenges conventions but uses recognized data | Mid-tier, consciousness journals |
| **3** | Speculative | PSI, quantum consciousness, partial empirical grounding | Neuroquantology, fringe peer-reviewed |
| **4** | Paradigm-Challenging | TI Sigma as fundamental law (LCC, GILE, PD zones) | Zenodo public primarily |
| **5** | Novel Framework | No mainstream acceptance pathway (CCC substrate, afterlife, etc.) | Zenodo private only |
    """)

    st.subheader("Publication Funnel")
    st.markdown("""
```
ResearchGate (radicality 1-2) ──► Entry point for conventional scientists
         │
         ▼
arXiv (radicality 1-3) ──────────► Preprint archive, math/physics/cs/philosophy
         │
         ▼
Zenodo Public (radicality 1-4) ──► Full TI Sigma framework, DOI-stamped
         │
         ▼
Zenodo Private (radicality 5) ───► Frontier work, invitation-only sharing
```
    """)


def _run_classification(force: bool):
    progress_bar = st.progress(0, text="Preparing batch classification...")
    status_text  = st.empty()

    def update_progress(done, total):
        pct = done / max(total, 1)
        progress_bar.progress(pct, text=f"Classifying paper {done}/{total}...")
        status_text.info(f"Processing batch... {done}/{total} papers")

    with st.spinner("Running AI classification..."):
        result = run_batch_classification(force=force, progress_fn=update_progress)

    progress_bar.progress(1.0, text="Classification complete!")
    status_text.empty()
    st.success(
        f"Done! **{result['classified']}** classified, "
        f"**{result['skipped']}** skipped (already done), "
        f"**{result['failed']}** used fallback defaults."
    )
    st.rerun()


def _render_review_tab():
    st.subheader("Review & Edit All Classifications")
    st.caption("Edit radicality, journal tier, formal proof, or Zenodo status directly in the table, then click Save Changes.")

    rows = get_all_classifications()
    if not rows:
        st.warning("No papers classified yet. Run classification first.")
        return

    df_full = pd.DataFrame(rows)

    col1, col2, col3 = st.columns(3)
    with col1:
        rad_filter = st.multiselect(
            "Radicality", options=[1, 2, 3, 4, 5],
            default=[1, 2, 3, 4, 5],
            format_func=lambda x: RADICALITY_LABELS.get(x, str(x))
        )
    with col2:
        tier_filter = st.multiselect(
            "Journal Tier", options=JOURNAL_TIER_OPTIONS,
            default=JOURNAL_TIER_OPTIONS
        )
    with col3:
        domain_filter = st.text_input("Filter by domain tag (partial match)", "")

    df = df_full.copy()
    if rad_filter:
        df = df[df["radicality_score"].isin(rad_filter)]
    if tier_filter:
        df = df[df["journal_tier"].isin(tier_filter)]
    if domain_filter:
        df = df[df["domain_tags"].apply(
            lambda tags: any(domain_filter.lower() in (t or "").lower()
                             for t in (tags or []))
        )]

    df["domains"]   = df["domain_tags"].apply(lambda t: ", ".join(t) if t else "")
    df["platforms"] = df["platform_assignment"].apply(lambda t: ", ".join(t) if t else "")
    df["zenodo_doi"] = df["zenodo_doi"].fillna("")
    df["user_notes"] = df["user_notes"].fillna("")

    EDIT_COLS = ["filename", "title", "radicality_score", "has_formal_proof",
                 "journal_tier", "zenodo_status", "zenodo_doi", "user_notes",
                 "domains", "platforms"]

    col_config = {
        "filename":       st.column_config.TextColumn("File", disabled=True),
        "title":          st.column_config.TextColumn("Title", disabled=True),
        "radicality_score": st.column_config.SelectboxColumn(
            "Radicality", options=[1, 2, 3, 4, 5], required=True),
        "has_formal_proof": st.column_config.CheckboxColumn("Formal Proof"),
        "journal_tier":   st.column_config.SelectboxColumn(
            "Journal Tier", options=JOURNAL_TIER_OPTIONS, required=True),
        "zenodo_status":  st.column_config.SelectboxColumn(
            "Zenodo Status", options=ZENODO_STATUS_OPTIONS, required=True),
        "zenodo_doi":     st.column_config.TextColumn("Zenodo DOI"),
        "user_notes":     st.column_config.TextColumn("Notes"),
        "domains":        st.column_config.TextColumn("Domains", disabled=True),
        "platforms":      st.column_config.TextColumn("Platforms", disabled=True),
    }

    edited = st.data_editor(
        df[EDIT_COLS],
        column_config=col_config,
        use_container_width=True,
        height=460,
        num_rows="fixed",
        key="paper_editor",
    )

    st.caption(f"Showing {len(df)} of {len(df_full)} papers — edit any cell, then click Save below.")

    if st.button("💾 Save All Changes", type="primary"):
        from paper_classifier import build_assignment
        saved = 0
        original = {r["filename"]: r for r in rows}
        for _, row in edited.iterrows():
            fname = row["filename"]
            orig  = original.get(fname, {})
            new_rad    = int(row["radicality_score"])
            new_tier   = row["journal_tier"]
            new_proof  = bool(row["has_formal_proof"])
            new_status = row["zenodo_status"]
            new_doi    = row.get("zenodo_doi") or None
            new_notes  = row.get("user_notes") or None
            domains    = orig.get("domain_tags") or []
            new_plat   = build_assignment(new_rad, domains)
            updated = {
                "filename":            fname,
                "title":               orig.get("title"),
                "radicality_score":    new_rad,
                "has_formal_proof":    new_proof,
                "journal_tier":        new_tier,
                "platform_assignment": new_plat,
                "domain_tags":         domains,
                "zenodo_doi":          new_doi,
                "zenodo_status":       new_status,
                "user_notes":          new_notes,
            }
            upsert_classification(updated)
            saved += 1
        st.success(f"Saved {saved} papers.")
        st.rerun()

    st.divider()
    st.subheader("Edit Domain Tags for One Paper")
    st.caption("Domain tags affect platform routing — use this to refine arXiv eligibility.")

    all_files = sorted([r["filename"] for r in rows])
    selected = st.selectbox("Select paper to edit domains", all_files, index=0, key="domain_edit_sel")
    paper = next((r for r in rows if r["filename"] == selected), None)
    if not paper:
        return

    existing_domains = paper.get("domain_tags") or []
    with st.form("domain_edit_form"):
        new_domains = st.multiselect(
            "Domain Tags",
            options=DOMAIN_OPTIONS,
            default=[d for d in existing_domains if d in DOMAIN_OPTIONS]
        )
        if st.form_submit_button("💾 Save Domain Tags"):
            from paper_classifier import build_assignment
            new_plat = build_assignment(int(paper.get("radicality_score") or 3), new_domains)
            upsert_classification({
                "filename":            selected,
                "title":               paper.get("title"),
                "radicality_score":    paper.get("radicality_score"),
                "has_formal_proof":    paper.get("has_formal_proof"),
                "journal_tier":        paper.get("journal_tier"),
                "platform_assignment": new_plat,
                "domain_tags":         new_domains,
                "zenodo_status":       paper.get("zenodo_status"),
            })
            st.success(f"Domain tags saved. Platform: {', '.join(new_plat)}")
            st.rerun()


def _render_researchgate_tab():
    st.subheader("ResearchGate Import List")
    st.info(
        "ResearchGate has no API. To add papers:\n"
        "1. Go to researchgate.net → Add Research → Import from DOI\n"
        "2. Paste each DOI below one at a time\n"
        "3. ResearchGate fetches metadata automatically from Zenodo\n\n"
        "**Only radicality 1-2 papers are shown here** — these are most likely to be "
        "accepted by conventional scientists browsing ResearchGate."
    )

    papers = get_researchgate_list()

    if not papers:
        st.warning("No radicality 1-2 papers classified yet. Run AI classification first.")
        return

    st.metric("Papers ready for ResearchGate", len(papers))

    all_dois  = [p["zenodo_doi"] for p in papers if p.get("zenodo_doi")]
    all_titles = [p["title"] for p in papers]

    col1, col2 = st.columns(2)
    with col1:
        doi_text = "\n".join(all_dois)
        st.text_area("DOI List (copy → paste into ResearchGate import)", doi_text, height=200)
    with col2:
        titles_text = "\n".join([
            f"{p['title']} | {p.get('zenodo_doi', 'no DOI')} | Rad {p['radicality_score']}"
            for p in papers
        ])
        st.text_area("Full list with titles", titles_text, height=200)

    st.divider()

    df = pd.DataFrame(papers)
    df["radicality"] = df["radicality_score"].map(RADICALITY_LABELS)
    df["doi_link"]   = df["zenodo_doi"].apply(lambda d: f"https://doi.org/{d}" if d else "No DOI yet")
    df["domains"]    = df["domain_tags"].apply(lambda t: ", ".join(t) if t else "—")

    st.dataframe(
        df[["title", "radicality", "journal_tier", "domains", "doi_link"]].rename(columns={
            "title": "Title", "radicality": "Radicality",
            "journal_tier": "Journal Tier", "domains": "Domains", "doi_link": "DOI Link"
        }),
        use_container_width=True
    )

    st.caption(
        "**Tip:** Upload to Zenodo first (if not already), then import the DOI to ResearchGate. "
        "Papers with no DOI need Zenodo upload before ResearchGate import."
    )


def _render_arxiv_tab():
    st.subheader("arXiv Submission Checklist")
    st.info(
        "**arXiv requires manual web submission at arxiv.org.**\n\n"
        "⚠️ First-time submitters often need an endorsement from an existing arXiv author. "
        "Contact someone in your target category to endorse you, or submit to a category "
        "where TI Sigma already has presence.\n\n"
        "Papers below are radicality 1-3 and suitable for arXiv preprint categories."
    )

    st.warning(
        "**Endorsement Note:** arXiv's endorsement system means your first submission in each "
        "category requires approval from an established arXiv author. "
        "Suggested categories are shown per paper."
    )

    papers = get_arxiv_list()

    if not papers:
        st.warning("No eligible papers classified yet. Run AI classification first.")
        return

    st.metric("Papers eligible for arXiv", len(papers))

    df = pd.DataFrame(papers)
    df["radicality"] = df["radicality_score"].map(RADICALITY_LABELS)
    df["domains"]    = df["domain_tags"].apply(lambda t: ", ".join(t) if t else "—")
    df["doi_link"]   = df["zenodo_doi"].apply(lambda d: f"https://doi.org/{d}" if d else "—")

    category_filter = st.multiselect(
        "Filter by arXiv category",
        options=sorted(df["arxiv_category"].unique().tolist()),
        default=[]
    )

    filtered_df = df if not category_filter else df[df["arxiv_category"].isin(category_filter)]

    st.dataframe(
        filtered_df[["title", "radicality", "arxiv_category", "domains", "doi_link"]].rename(columns={
            "title": "Title", "radicality": "Radicality",
            "arxiv_category": "arXiv Category",
            "domains": "Domains", "doi_link": "Zenodo DOI"
        }),
        use_container_width=True, height=450
    )

    st.subheader("Submission Steps")
    st.markdown("""
1. **Create arXiv account** at arxiv.org/user/register
2. **Request endorsement** — contact a researcher in your target category
3. **Prepare LaTeX or PDF** — arXiv prefers LaTeX; PDF is accepted
4. **Submit** — upload your paper, fill metadata, choose category
5. **Link to Zenodo** — add your Zenodo DOI in the arXiv "related identifiers" field
6. **Cross-list** — you can cross-list to multiple categories (e.g., `physics.gen-ph` AND `q-bio.NC`)
    """)


def _render_zenodo_tab():
    st.subheader("Zenodo Privacy Map")
    st.info(
        "Papers with **radicality 5** represent the frontier of TI Sigma — entirely novel framework "
        "claims with no current mainstream acceptance pathway. These should be marked **Private** "
        "on Zenodo and shared only with specific researchers you trust.\n\n"
        "If a paper below is currently Public on Zenodo, you should update its access rights at zenodo.org."
    )

    papers = get_zenodo_privacy_map()

    if not papers:
        st.success("No radicality-5 papers classified yet — nothing needs to be made private.")
        return

    already_private = [p for p in papers if p.get("zenodo_status") == "private"]
    should_private  = [p for p in papers if p.get("zenodo_status") != "private"]

    col1, col2 = st.columns(2)
    col1.metric("Radicality-5 Papers", len(papers))
    col2.metric("Currently Marked Public/Unpublished", len(should_private),
                "⚠️ Should be Private" if should_private else "✅ All set")

    if should_private:
        st.warning(f"**{len(should_private)} papers** should be moved to Private on Zenodo.")
        df = pd.DataFrame(should_private)
        df["doi_link"] = df["zenodo_doi"].apply(
            lambda d: f"https://doi.org/{d}" if d else "Not on Zenodo yet"
        )
        st.dataframe(
            df[["filename", "title", "zenodo_status", "doi_link"]].rename(columns={
                "filename": "File", "title": "Title",
                "zenodo_status": "Current Status", "doi_link": "Zenodo DOI"
            }),
            use_container_width=True
        )

        st.subheader("How to Make a Zenodo Record Private")
        st.markdown("""
1. Go to **zenodo.org** → log in → **My Uploads**
2. Find the record by DOI or title
3. Click **Edit** on the published record
4. Under **Access** → change from "Open Access" to **"Closed Access"** or **"Restricted"**
5. Add a note: *"Available upon request. Contact: brandon@blissgene.com"*
6. Save and publish the new version
        """)

    if already_private:
        st.success(f"✅ {len(already_private)} papers already marked as Private in this system.")
        df2 = pd.DataFrame(already_private)
        st.dataframe(df2[["filename", "title"]].rename(columns={
            "filename": "File", "title": "Title"
        }), use_container_width=True)

    st.divider()
    st.subheader("All Radicality Scores — Distribution")

    all_rows = get_all_classifications()
    if all_rows:
        df_all = pd.DataFrame(all_rows)
        counts = df_all["radicality_score"].value_counts().sort_index()
        chart_df = pd.DataFrame({
            "Radicality": [RADICALITY_LABELS.get(k, str(k)) for k in counts.index],
            "Count": counts.values
        })
        st.bar_chart(chart_df.set_index("Radicality"))
