"""
Streamlit-integrated PDF download system for TI papers
- On-demand PDF generation (avoids timeouts)
- Individual paper downloads
- All papers ZIP download
- Master catalog download
"""

import streamlit as st
import markdown
from weasyprint import HTML, CSS
from pathlib import Path
import zipfile
from io import BytesIO
import base64

def get_pdf_css():
    """CSS styles for searchable, audio-compatible PDFs"""
    return """
    @page { size: Letter; margin: 1in; }
    body { font-family: Georgia, serif; font-size: 11pt; line-height: 1.6; }
    h1 { font-size: 24pt; font-weight: bold; margin-top: 20pt; }
    h2 { font-size: 18pt; font-weight: bold; margin-top: 18pt; }
    h3 { font-size: 14pt; font-weight: bold; margin-top: 14pt; }
    code { font-family: 'Courier New', monospace; font-size: 9pt; background: #f5f5f5; padding: 2pt 4pt; }
    pre { font-family: 'Courier New', monospace; background: #f5f5f5; padding: 10pt; border-left: 3pt solid #666; }
    table { width: 100%; border-collapse: collapse; margin: 12pt 0; }
    th, td { border: 1pt solid #999; padding: 6pt; }
    th { background: #f0f0f0; font-weight: bold; }
    blockquote { border-left: 3pt solid #999; padding-left: 12pt; color: #555; font-style: italic; }
    """

def markdown_to_pdf_bytes(markdown_content, title="TI Paper"):
    """Convert markdown to PDF bytes (in-memory, fast)"""
    # Convert markdown to HTML
    html_content = markdown.markdown(
        markdown_content,
        extensions=['tables', 'fenced_code', 'nl2br', 'sane_lists']
    )
    
    # Wrap in HTML document
    full_html = f"""
    <!DOCTYPE html>
    <html>
    <head><meta charset="UTF-8"><title>{title}</title></head>
    <body>{html_content}</body>
    </html>
    """
    
    # Generate PDF in memory
    pdf_bytes = HTML(string=full_html).write_pdf(
        stylesheets=[CSS(string=get_pdf_css())]
    )
    
    # Ensure we have bytes
    if pdf_bytes is None:
        raise ValueError("Failed to generate PDF")
    
    return pdf_bytes

def render_pdf_download_dashboard():
    """Main PDF download dashboard for Streamlit"""
    st.header("📄 TI Papers - PDF Downloads")
    
    st.info("""
    **Features:**
    - ✅ Searchable PDFs (Kindle-compatible)
    - ✅ Text-to-speech ready (selectable text)
    - ✅ Professional formatting
    - ✅ Individual downloads or bulk ZIP
    - ✅ Open in new browser tab
    """)
    
    # Get all markdown papers from BOTH directories
    papers_dir = Path("papers")
    research_papers_dir = Path("research_papers")
    
    papers_md = sorted(papers_dir.glob("*.md")) if papers_dir.exists() else []
    research_md = sorted(research_papers_dir.glob("*.md")) if research_papers_dir.exists() else []
    
    # Combine all papers
    all_markdown_files = papers_md + research_md
    
    # Exclude certain files
    exclude = {'README.md', 'TEMPLATE.md', 'RESEARCH_PAPERS_INDEX.md'}
    markdown_files = [f for f in all_markdown_files if f.name not in exclude]
    
    st.success(f"📚 **{len(markdown_files)} papers available**")
    
    # Tab layout
    tab1, tab2, tab3 = st.tabs([
        "📄 Individual Papers",
        "📦 Bulk Download (ZIP)",
        "📚 Master Catalog"
    ])
    
    with tab1:
        st.subheader("Individual Paper Downloads")
        st.caption("Generate and download individual papers as searchable PDFs")

        # --- LIVE SEARCH BAR ---
        search_query = st.text_input("🔍 Search papers by title or keyword", placeholder="e.g. blueprint, tralse, consciousness, URB...")

        if search_query.strip():
            st.markdown(f"### Search results for: *{search_query}*")
            results = []
            for md_path in markdown_files:
                content = md_path.read_text(encoding='utf-8', errors='ignore')
                title = md_path.stem.replace('_', ' ').title()
                for line in content.split('\n'):
                    if line.startswith('# '):
                        title = line[2:].strip()
                        break
                if search_query.lower() in title.lower() or search_query.lower() in content.lower():
                    results.append((md_path, title, content))

            if results:
                st.success(f"Found {len(results)} paper(s) matching '{search_query}'")
                for md_path, title, content in results:
                    col1, col2, col3 = st.columns([4, 1, 1])
                    col1.write(f"**{title}**")
                    if col2.button("👁️ View", key=f"search_view_{md_path.name}"):
                        st.markdown(f"### {title}")
                        st.markdown(content)
                    if col3.button("📥 PDF", key=f"search_dl_{md_path.name}"):
                        with st.spinner(f"Generating PDF..."):
                            try:
                                pdf_bytes = markdown_to_pdf_bytes(content, title)
                                st.download_button(
                                    label="⬇️ Download PDF",
                                    data=pdf_bytes,
                                    file_name=f"{md_path.stem}.pdf",
                                    mime="application/pdf",
                                    key=f"search_download_{md_path.name}"
                                )
                                st.success("✅ PDF ready!")
                            except Exception as e:
                                st.error(f"❌ Error: {e}")
            else:
                st.warning(f"No papers found matching '{search_query}'. Try a different keyword.")

        else:
            # --- BROWSEABLE CATEGORIES ---
            categories = {
                "🔥 LATEST — Feb 2026 Breakthroughs": [
                    ("papers", "DIVINATION_EMPIRICAL_EVIDENCE_REVIEW.md"),
                    ("papers", "UNIVERSAL_REALITY_BLUEPRINT_PERIODIC_TABLE_OF_MATH.md"),
                    ("papers", "INFORMATION_IS_ALL_THERE_IS_TI_PERIODIC_TABLE_V2.md"),
                    ("papers", "PRIMORDIAL_OCTOPUS_SPACE_FROM_SEVEN_CONSTANTS.md"),
                    ("papers", "ORIGIN_OF_EXISTENCE_BREIT_WHEELER_TI_SIGMA.md"),
                    ("papers", "NONLINEAR_NUMBER_LINE.md"),
                    ("papers", "PRIMORDIAL_CONSCIOUSNESS_PHOTONIC_OPTICAL_COMPUTER.md"),
                ],
                "🌟 NEW: Research Papers (Nov 2025)": [
                    ("research_papers", "GRAND_MYRION_COMPUTATION_PAPER.md"),
                    ("research_papers", "EULER_TRALSE_SYNTHESIS.md"),
                    ("research_papers", "BOOTSTRAPPED_FORESIGHT_PAPER.md"),
                    ("research_papers", "LCC_VIRUS_FRAMEWORK_PAPER.md"),
                    ("research_papers", "ANTI_GILE_EVIL_THEORY_PAPER.md"),
                    ("research_papers", "INVITATION_ETHICS_FRAMEWORK_PAPER.md"),
                    ("research_papers", "FREE_WILL_INTENSITY_PARADOX_PAPER.md"),
                    ("research_papers", "RESONANCE_VS_CALCULATION_PAPER.md"),
                    ("research_papers", "TRALSE_EPISTEMOLOGY_PAPER.md"),
                    ("research_papers", "ANIMAL_ICELL_SPIRIT_ANIMALS_PAPER.md"),
                    ("research_papers", "BIOLUMINESCENCE_DIVINE_INDICATOR_PAPER.md"),
                    ("research_papers", "DE_PHOTON_TIME_ICELL_MECHANICS_PAPER.md"),
                ],
                "Core Framework": [
                    ("papers", "CONSTRUCTIVE_DOGMATISM.md"),
                    ("papers", "TRALSEBIT_COMPLETE_THEORY.md"),
                    ("papers", "TI_STATISTICS_COMPLETE_FRAMEWORK.md"),
                    ("papers", "TI_FOR_EVERYONE_COMPLETE_BOOK.md"),
                ],
                "Mathematics": [
                    ("papers", "RIEMANN_HYPOTHESIS_TI_PROOF_v2.md"),
                    ("papers", "RIEMANN_HYPOTHESIS_CONVENTIONAL_PROOF.md"),
                    ("papers", "MONTGOMERY_PAIR_CORRELATION_RIEMANN.md"),
                    ("papers", "GILE_VS_PARETO_DISTRIBUTION.md"),
                ],
                "Consciousness Theory": [
                    ("papers", "CONSCIOUSNESS_SHELL_SOLUTION.md"),
                    ("papers", "ICELL_IWEB_ONTOLOGY_COMPLETE.md"),
                    ("papers", "PN_C_CCC_ME_COMPLETE_ONTOLOGY.md"),
                ],
                "Applications": [
                    ("papers", "PSI_AS_RESONANCE_FIELD_COMPLETE_THEORY.md"),
                    ("papers", "PSI_HEART_COHERENCE_MECHANISM.md"),
                ]
            }

            # Auto-expand the featured section
            for i, (category, file_list) in enumerate(categories.items()):
                expanded = (i == 0)
                with st.expander(f"📁 {category} ({len(file_list)} papers)", expanded=expanded):
                    for item in file_list:
                        # Handle both tuple format (dir, filename) and legacy string format
                        if isinstance(item, tuple):
                            dir_name, filename = item
                            md_path = Path(dir_name) / filename
                        else:
                            filename = item
                            md_path = papers_dir / filename

                        if md_path.exists():
                            with open(md_path, 'r', encoding='utf-8') as f:
                                content = f.read()
                                title = filename.replace('.md', '').replace('_', ' ').title()
                                for line in content.split('\n'):
                                    if line.startswith('# '):
                                        title = line[2:].strip()
                                        break

                            col1, col2, col3 = st.columns([4, 1, 1])
                            col1.write(f"**{title}**")

                            if col2.button("👁️ View", key=f"view_{filename}"):
                                st.markdown(f"### {title}")
                                st.markdown(content)

                            if col3.button("📥 PDF", key=f"dl_{filename}"):
                                with st.spinner(f"Generating {title}..."):
                                    try:
                                        pdf_bytes = markdown_to_pdf_bytes(content, title)
                                        st.download_button(
                                            label="⬇️ Download PDF",
                                            data=pdf_bytes,
                                            file_name=f"{filename.replace('.md', '')}.pdf",
                                            mime="application/pdf",
                                            key=f"download_{filename}"
                                        )
                                        st.success("✅ PDF ready!")
                                    except Exception as e:
                                        st.error(f"❌ Error: {e}")
    
    with tab2:
        st.subheader("Bulk Download - All Papers ZIP")
        st.caption("Download all papers as PDFs in a single ZIP file")
        
        if st.button("📦 Generate ZIP of All Papers", type="primary"):
            with st.spinner(f"Generating {len(markdown_files)} PDFs..."):
                try:
                    # Create ZIP in memory
                    zip_buffer = BytesIO()
                    
                    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                        progress_bar = st.progress(0)
                        status_text = st.empty()
                        
                        for idx, md_path in enumerate(markdown_files):
                            # Read markdown
                            with open(md_path, 'r', encoding='utf-8') as f:
                                content = f.read()
                            
                            # Extract title
                            title = md_path.stem.replace('_', ' ').title()
                            for line in content.split('\n'):
                                if line.startswith('# '):
                                    title = line[2:].strip()
                                    break
                            
                            status_text.text(f"Processing {idx+1}/{len(markdown_files)}: {title[:50]}...")
                            
                            # Generate PDF
                            pdf_bytes = markdown_to_pdf_bytes(content, title)
                            
                            # Add to ZIP
                            zipf.writestr(f"{md_path.stem}.pdf", pdf_bytes)
                            
                            progress_bar.progress((idx + 1) / len(markdown_files))
                    
                    # Offer download
                    zip_buffer.seek(0)
                    st.download_button(
                        label="⬇️ Download ZIP Archive",
                        data=zip_buffer.getvalue(),
                        file_name="TI_ALL_PAPERS.zip",
                        mime="application/zip",
                        type="primary"
                    )
                    
                    st.success(f"✅ Generated {len(markdown_files)} PDFs in ZIP!")
                    
                except Exception as e:
                    st.error(f"❌ Error generating ZIP: {e}")
    
    with tab3:
        st.subheader("Master Catalog - Combined PDF")
        st.caption("All papers combined into single searchable PDF with table of contents")
        
        if st.button("📚 Generate Master Catalog", type="primary"):
            with st.spinner("Combining all papers into master catalog..."):
                try:
                    # Build combined markdown
                    toc_lines = ["# Transcendent Intelligence Framework", "", "## Complete Paper Catalog", "", "**Brandon Emerick - November 2025**", "", "---", "", "## Table of Contents", ""]
                    
                    combined_content = ""
                    
                    for idx, md_path in enumerate(markdown_files, 1):
                        # Read paper
                        with open(md_path, 'r', encoding='utf-8') as f:
                            content = f.read()
                        
                        # Extract title
                        title = md_path.stem.replace('_', ' ').title()
                        for line in content.split('\n'):
                            if line.startswith('# '):
                                title = line[2:].strip()
                                break
                        
                        # Add to TOC
                        toc_lines.append(f"{idx}. {title}")
                        
                        # Add to combined content
                        if idx > 1:
                            combined_content += "\n\n---\n\n"
                        
                        combined_content += f"# {idx}. {title}\n\n"
                        combined_content += content.replace(f"# {title}", "")
                    
                    # Combine TOC and content
                    full_markdown = "\n".join(toc_lines) + "\n\n---\n\n" + combined_content
                    
                    # Generate master PDF
                    pdf_bytes = markdown_to_pdf_bytes(full_markdown, "TI Framework - Complete Catalog")
                    
                    st.download_button(
                        label="⬇️ Download Master Catalog PDF",
                        data=pdf_bytes,
                        file_name="TI_COMPLETE_CATALOG.pdf",
                        mime="application/pdf",
                        type="primary"
                    )
                    
                    st.success(f"✅ Master catalog generated ({len(markdown_files)} papers)!")
                    
                except Exception as e:
                    st.error(f"❌ Error generating master catalog: {e}")

if __name__ == "__main__":
    render_pdf_download_dashboard()
