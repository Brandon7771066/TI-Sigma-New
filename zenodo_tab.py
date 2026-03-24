"""
TI Sigma — Zenodo Publication Manager Tab
Batch upload, versioning, status dashboard.
"""
import streamlit as st
import threading
import time
from pathlib import Path
from datetime import datetime


def show_zenodo_manager():
    st.markdown("## 📤 Zenodo Publication Manager")
    st.markdown("Manage the TI Sigma corpus on [Zenodo](https://zenodo.org) — batch upload, version existing records, track all publications.")

    # ── Init ──────────────────────────────────────────────────────────────────
    try:
        from zenodo_pipeline import (
            init_zenodo_db, get_stats, get_upload_status,
            get_priority_queue, get_all_urb_mds, run_batch,
            list_depositions, upload_paper, update_existing_record,
            PUBLISHED_RECORDS, PAPERS_DIR, md_to_pdf
        )
        import os
        if not os.environ.get("ZENODO_TOKEN"):
            st.error("ZENODO_TOKEN not found in environment secrets.")
            return
        init_zenodo_db()
    except Exception as e:
        st.error(f"Pipeline init failed: {e}")
        return

    # ── Stats Banner ──────────────────────────────────────────────────────────
    stats = get_stats()
    c1, c2, c3, c4, c5 = st.columns(5)
    c1.metric("Local Papers", stats["total_local"])
    c2.metric("Published on Zenodo", stats["published"])
    c3.metric("DOI Records (Live)", stats["live_records"])
    c4.metric("Pending Upload", stats["pending"])
    c5.metric("URB Corpus", stats["corpus_urbs"])

    st.markdown("---")

    # ── Tabs ──────────────────────────────────────────────────────────────────
    zt1, zt2, zt3, zt4 = st.tabs([
        "🚀 Batch Upload",
        "🔄 Update Existing Records",
        "📊 Upload Status",
        "🔍 Live Zenodo Records"
    ])

    # ─────────────────────────────────────────────────────────────────────────
    # TAB 1 — BATCH UPLOAD
    # ─────────────────────────────────────────────────────────────────────────
    with zt1:
        st.markdown("### Batch Upload New Papers")

        upload_mode = st.radio("Queue selection", [
            "Priority Batch 1 (URBs #505–508 + 12 core papers)",
            "All URB papers (164 files, sorted by number)",
            "Custom — pick specific papers"
        ], horizontal=True)

        if upload_mode.startswith("Priority"):
            queue = get_priority_queue()
        elif upload_mode.startswith("All URB"):
            queue = get_all_urb_mds()
        else:
            all_mds = sorted(PAPERS_DIR.glob("*.md"))
            chosen = st.multiselect(
                "Select papers to upload",
                [p.name for p in all_mds],
                default=[]
            )
            queue = [PAPERS_DIR / c for c in chosen]

        st.info(f"Queue contains **{len(queue)} papers**. Papers already uploaded will be skipped automatically.")

        from zenodo_pipeline import get_already_uploaded
        already = get_already_uploaded()
        remaining = [p for p in queue if Path(p).name not in already]
        st.write(f"Already uploaded: **{len(already)}** | To upload this run: **{min(len(remaining), 10)}** (capped at 10 per run)")

        max_per_run = st.slider("Max uploads per run", 1, 25, 5)

        col_go, col_dry = st.columns(2)
        dry_run = col_dry.checkbox("Dry run (generate PDFs only, don't upload)", value=False)

        if col_go.button("🚀 Run Batch Upload", type="primary"):
            if not remaining:
                st.success("Nothing left to upload in this queue!")
            else:
                todo = remaining[:max_per_run]
                prog = st.progress(0)
                log_area = st.empty()
                results = {"uploaded": [], "failed": [], "pdf_only": []}

                for i, paper in enumerate(todo):
                    paper = Path(paper)
                    prog.progress((i + 1) / len(todo))
                    log_area.info(f"Processing {i+1}/{len(todo)}: {paper.name}")

                    # Always generate PDF
                    pdf_path = paper.with_suffix(".pdf")
                    if not pdf_path.exists():
                        ok = md_to_pdf(paper, pdf_path)
                        if not ok:
                            results["failed"].append({"file": paper.name, "reason": "PDF generation failed"})
                            continue

                    if dry_run:
                        results["pdf_only"].append(paper.name)
                        continue

                    r = upload_paper(paper, batch_num=1)
                    if r["status"] == "ok":
                        results["uploaded"].append({
                            "file": paper.name,
                            "doi": r.get("doi", "pending"),
                            "title": r.get("title", "")[:60]
                        })
                    else:
                        results["failed"].append({"file": paper.name, "reason": r.get("reason", "")[:100]})
                    time.sleep(0.3)

                prog.progress(1.0)
                log_area.empty()

                if results["uploaded"]:
                    st.success(f"✅ Uploaded {len(results['uploaded'])} papers!")
                    for u in results["uploaded"]:
                        st.write(f"  • **{u['file']}** — DOI: `{u['doi']}`")

                if results["pdf_only"]:
                    st.info(f"📄 Generated {len(results['pdf_only'])} PDFs (dry run mode)")

                if results["failed"]:
                    st.warning(f"⚠️ {len(results['failed'])} failed:")
                    for f in results["failed"]:
                        st.write(f"  • {f['file']}: {f['reason']}")

    # ─────────────────────────────────────────────────────────────────────────
    # TAB 2 — UPDATE EXISTING RECORDS
    # ─────────────────────────────────────────────────────────────────────────
    with zt2:
        st.markdown("### Update Existing Published Records")
        st.info("These 4 records already have DOIs. Creating a new version preserves the DOI while updating the content and metadata.")

        record_options = {
            f"18916599 — TI Sigma: Five Formally Verified Theorems": 18916599,
            f"18930175 — Proofs For TI Sigma Meta-Theory": 18930175,
            f"18929980 — Software Involving Entrainment Via LCC": 18929980,
            f"18930896 — LCC Supplants Probability Theory": 18930896,
        }

        selected_label = st.selectbox("Select record to update", list(record_options.keys()))
        selected_id = record_options[selected_label]

        st.markdown("**Attach replacement files:**")
        file_options = sorted(PAPERS_DIR.glob("*.pdf"))
        chosen_files = st.multiselect(
            "Choose PDFs to include in new version",
            [p.name for p in file_options],
            default=[]
        )

        extra_mds = sorted(PAPERS_DIR.glob("*.md"))
        chosen_mds = st.multiselect(
            "Also include markdown files",
            [p.name for p in extra_mds],
            default=[]
        )

        new_title = st.text_input("New title (leave blank to keep existing)", "")
        new_desc  = st.text_area("New description (leave blank to keep existing)", "", height=80)

        if st.button("🔄 Create New Version & Publish", type="primary"):
            if not chosen_files and not chosen_mds:
                st.warning("Please select at least one file to include.")
            else:
                from zenodo_pipeline import build_metadata, update_existing_record
                files = ([PAPERS_DIR / f for f in chosen_files] +
                         [PAPERS_DIR / m for m in chosen_mds])
                files = [f for f in files if f.exists()]
                meta = build_metadata(
                    new_title or selected_label.split("—")[-1].strip(),
                    new_desc or "Updated version of TI Sigma research paper."
                ) if (new_title or new_desc) else None

                with st.spinner("Creating new version..."):
                    result = update_existing_record(selected_id, files, meta)

                if result["status"] == "ok":
                    st.success(f"✅ New version published! New ID: {result['new_id']} | DOI: {result['doi']}")
                else:
                    st.error(f"Failed: {result['reason']}")

    # ─────────────────────────────────────────────────────────────────────────
    # TAB 3 — UPLOAD STATUS
    # ─────────────────────────────────────────────────────────────────────────
    with zt3:
        st.markdown("### Upload Status Dashboard")

        rows = get_upload_status()
        if not rows:
            st.info("No uploads tracked yet. Run a batch upload to get started.")
        else:
            import pandas as pd
            df = pd.DataFrame(rows, columns=[
                "Filename", "Title", "Zenodo ID", "DOI", "Status", "Batch", "Uploaded At", "Notes"
            ])
            published_df = df[df["Status"] == "published"]
            failed_df    = df[df["Status"] == "failed"]

            st.metric("Total tracked", len(df))
            col_a, col_b = st.columns(2)
            col_a.metric("Published ✅", len(published_df))
            col_b.metric("Failed ⚠️", len(failed_df))

            st.markdown("#### Published Papers")
            if not published_df.empty:
                st.dataframe(published_df[["Filename", "Title", "DOI", "Uploaded At"]],
                             use_container_width=True)

            if not failed_df.empty:
                st.markdown("#### Failed Uploads")
                st.dataframe(failed_df[["Filename", "Notes"]], use_container_width=True)

        # PDF inventory
        st.markdown("---")
        st.markdown("#### Local Paper Inventory")
        pdf_count = len(list(PAPERS_DIR.glob("*.pdf")))
        md_count  = len(list(PAPERS_DIR.glob("*.md")))
        urb_count = len(list(PAPERS_DIR.glob("URB_*.md")))
        ci, cj, ck = st.columns(3)
        ci.metric("Markdown papers", md_count)
        cj.metric("PDF papers", pdf_count)
        ck.metric("URB papers (MD)", urb_count)

    # ─────────────────────────────────────────────────────────────────────────
    # TAB 4 — LIVE ZENODO RECORDS
    # ─────────────────────────────────────────────────────────────────────────
    with zt4:
        st.markdown("### Live Zenodo Records")

        if st.button("🔄 Refresh from Zenodo"):
            st.session_state["zenodo_live"] = None

        if "zenodo_live" not in st.session_state or not st.session_state.get("zenodo_live"):
            with st.spinner("Fetching from Zenodo API..."):
                try:
                    recs = list_depositions()
                    st.session_state["zenodo_live"] = recs
                except Exception as e:
                    st.error(f"API error: {e}")
                    return

        recs = st.session_state.get("zenodo_live", [])
        st.success(f"Found **{len(recs)}** records on Zenodo")

        doi_recs   = [r for r in recs if r.get("doi")]
        draft_recs = [r for r in recs if not r.get("doi")]

        if doi_recs:
            st.markdown("#### ✅ Published Records with DOIs")
            for rec in doi_recs:
                with st.expander(f"📄 {rec['title'][:80]}"):
                    st.write(f"**Zenodo ID:** {rec['id']}")
                    st.write(f"**DOI:** {rec.get('doi')}")
                    st.write(f"**State:** {rec.get('state')}")
                    files = rec.get("files", [])
                    if files:
                        st.write(f"**Files:** {[f['filename'] for f in files]}")
                    st.markdown(f"[🔗 View on Zenodo](https://zenodo.org/record/{rec['id']})")

        if draft_recs:
            st.markdown("#### 📝 Unpublished Drafts")
            for rec in draft_recs:
                st.write(f"  • ID:{rec['id']} — {rec['title'][:70]}")

        st.markdown("---")
        st.markdown("#### 🎬 Next Steps: Canva Video Pipeline")
        st.info("""
**Recommended workflow for turning papers into videos:**

1. **Export paper as PDF** — done automatically when uploaded to Zenodo
2. **Upload to Canva** — use "Present and record" or the Canva video editor
3. **Use Canva's AI tools** to auto-generate slide layouts from the PDF content
4. **Record voiceover** or use Canva's text-to-speech for each paper
5. **Export as MP4** and upload to YouTube with the Zenodo DOI in the description

**Best papers to start with (most visual/memorable):**
- URB #505: Unified Telekinesis Equation (has tables + key formula)
- URB #506: i-Completeness Theorem (clean derivation chain)
- URB #507: The 6-Element Basis of Mathematics (the "remove one element" framing is very compelling)
- LCC Supplants Probability Theory (already has a DOI — perfect anchor paper)

**Social proof angle:** Each video description includes the Zenodo DOI link, creating a permanent citable record that can be referenced in patents, papers, and investor materials.
        """)
