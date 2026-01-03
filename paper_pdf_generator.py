"""
Paper PDF Generator - Convert Markdown Research Papers to PDFs
Generates professional PDFs from markdown files in papers/ directory
"""

from weasyprint import HTML
import markdown
import glob
import os
from datetime import datetime
from typing import Optional, Dict, List, Any
import zipfile
import io


def generate_pdf_for_paper(markdown_path: str, output_path: Optional[str] = None) -> bytes:
    """
    Convert a markdown paper to PDF with professional styling
    
    Args:
        markdown_path: Path to markdown file
        output_path: Optional output path to save PDF. If None, returns bytes only
        
    Returns:
        PDF bytes
    """
    
    # Read markdown content
    with open(markdown_path, 'r', encoding='utf-8') as f:
        md_content = f.read()
    
    # Convert markdown to HTML
    html_body = markdown.markdown(
        md_content,
        extensions=['extra', 'codehilite', 'tables', 'toc']
    )
    
    # Extract title (first # heading or filename)
    title = os.path.basename(markdown_path).replace('.md', '').replace('_', ' ').title()
    for line in md_content.split('\n'):
        if line.startswith('# '):
            title = line.replace('# ', '').strip()
            break
    
    # Create full HTML with styling
    html_content = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>{title}</title>
    <style>
        @page {{
            size: A4;
            margin: 2.5cm 2cm;
            @top-center {{
                content: "{title}";
                font-size: 10pt;
                color: #666;
            }}
            @bottom-center {{
                content: "Page " counter(page) " of " counter(pages);
                font-size: 10pt;
                color: #666;
            }}
        }}
        
        body {{
            font-family: 'Georgia', 'Times New Roman', serif;
            line-height: 1.6;
            color: #333;
            font-size: 11pt;
        }}
        
        h1 {{
            color: #1a1a1a;
            border-bottom: 3px solid #4CAF50;
            padding-bottom: 10px;
            margin-top: 30px;
            margin-bottom: 20px;
            font-size: 24pt;
            page-break-before: auto;
            page-break-after: avoid;
        }}
        
        h2 {{
            color: #2c3e50;
            border-bottom: 2px solid #3498db;
            padding-bottom: 5px;
            margin-top: 25px;
            margin-bottom: 15px;
            font-size: 18pt;
            page-break-after: avoid;
        }}
        
        h3 {{
            color: #34495e;
            margin-top: 20px;
            margin-bottom: 12px;
            font-size: 14pt;
            page-break-after: avoid;
        }}
        
        h4 {{
            color: #555;
            margin-top: 15px;
            margin-bottom: 10px;
            font-size: 12pt;
        }}
        
        p {{
            margin: 10px 0;
            text-align: justify;
            orphans: 3;
            widows: 3;
        }}
        
        code {{
            background: #f4f4f4;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Courier New', monospace;
            font-size: 10pt;
        }}
        
        pre {{
            background: #2d2d2d;
            color: #f8f8f2;
            padding: 15px;
            border-radius: 5px;
            overflow-x: auto;
            margin: 15px 0;
            page-break-inside: avoid;
        }}
        
        pre code {{
            background: transparent;
            padding: 0;
            color: inherit;
        }}
        
        blockquote {{
            border-left: 4px solid #4CAF50;
            padding-left: 20px;
            margin: 15px 0;
            color: #555;
            font-style: italic;
            background: #f9f9f9;
            padding: 10px 20px;
        }}
        
        table {{
            border-collapse: collapse;
            width: 100%;
            margin: 15px 0;
            page-break-inside: avoid;
        }}
        
        th, td {{
            border: 1px solid #ddd;
            padding: 10px;
            text-align: left;
        }}
        
        th {{
            background: #4CAF50;
            color: white;
            font-weight: bold;
        }}
        
        tr:nth-child(even) {{
            background: #f9f9f9;
        }}
        
        ul, ol {{
            margin: 10px 0;
            padding-left: 30px;
        }}
        
        li {{
            margin: 5px 0;
        }}
        
        strong {{
            color: #1a1a1a;
            font-weight: bold;
        }}
        
        em {{
            font-style: italic;
            color: #555;
        }}
        
        .header {{
            text-align: center;
            margin-bottom: 40px;
            padding: 20px;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            border-radius: 10px;
        }}
        
        .header h1 {{
            color: white;
            border: none;
            margin: 0;
            padding: 0;
        }}
        
        .metadata {{
            text-align: center;
            color: #eee;
            margin-top: 10px;
            font-size: 10pt;
        }}
        
        .footer {{
            margin-top: 50px;
            padding-top: 20px;
            border-top: 2px solid #ddd;
            text-align: center;
            color: #666;
            font-size: 9pt;
        }}
        
        a {{
            color: #3498db;
            text-decoration: none;
        }}
        
        a:hover {{
            text-decoration: underline;
        }}
        
        hr {{
            border: none;
            border-top: 1px solid #ddd;
            margin: 30px 0;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>{title}</h1>
        <div class="metadata">
            <p><strong>TI-UOP Research Platform</strong></p>
            <p>Generated: {datetime.now().strftime("%B %d, %Y")}</p>
            <p>Brandon Sorbom © {datetime.now().year}</p>
        </div>
    </div>
    
    {html_body}
    
    <div class="footer">
        <p><strong>TI-UOP Framework</strong> - Tralse Information - Universal Operations Platform</p>
        <p>Consciousness Mathematics & Quantum Information Theory</p>
        <p><em>This paper represents novel research in consciousness-based physics and mathematics</em></p>
    </div>
</body>
</html>
"""
    
    # Generate PDF
    pdf_bytes = HTML(string=html_content).write_pdf()
    
    # Optionally save to file
    if output_path:
        with open(output_path, 'wb') as f:
            f.write(pdf_bytes)
    
    return pdf_bytes


def generate_all_paper_pdfs(papers_dir: str = "papers", force_regenerate: bool = False) -> Dict[str, str]:
    """
    Generate PDFs for all markdown files in papers directory
    
    Args:
        papers_dir: Directory containing markdown papers
        force_regenerate: If True, regenerate even if PDF exists
        
    Returns:
        Dictionary mapping paper names to PDF paths
    """
    
    pdf_dir = os.path.join(papers_dir, "pdfs")
    os.makedirs(pdf_dir, exist_ok=True)
    
    pdf_paths = {}
    generated_count = 0
    skipped_count = 0
    
    # Find all markdown files
    markdown_files = glob.glob(os.path.join(papers_dir, "*.md"))
    
    print(f"Found {len(markdown_files)} markdown papers in {papers_dir}/")
    
    for md_path in markdown_files:
        # Generate PDF filename
        base_name = os.path.basename(md_path).replace(".md", "")
        pdf_name = f"{base_name}.pdf"
        pdf_path = os.path.join(pdf_dir, pdf_name)
        
        # Check if already exists
        if os.path.exists(pdf_path) and not force_regenerate:
            print(f"  ⏭️  Skipping {base_name} (PDF exists)")
            pdf_paths[base_name] = pdf_path
            skipped_count += 1
            continue
        
        try:
            # Generate PDF
            print(f"  📄 Generating PDF for {base_name}...")
            pdf_bytes = generate_pdf_for_paper(md_path, pdf_path)
            pdf_paths[base_name] = pdf_path
            generated_count += 1
            print(f"  ✅ Generated {pdf_name} ({len(pdf_bytes):,} bytes)")
        
        except Exception as e:
            print(f"  ❌ Error generating PDF for {base_name}: {e}")
    
    print(f"\n✅ Complete! Generated {generated_count} PDFs, skipped {skipped_count}")
    return pdf_paths


def create_papers_zip(papers_dir: str = "papers", output_path: str = "papers/all_papers.zip", 
                      batch_num: int = None, batch_size: int = 10) -> bytes:
    """
    Create a ZIP archive of all paper PDFs (or a batch)
    
    Args:
        papers_dir: Directory containing papers
        output_path: Path for output ZIP file
        batch_num: If specified, create only this batch (1-indexed)
        batch_size: Number of papers per batch (default 10)
        
    Returns:
        ZIP bytes
    """
    
    pdf_dir = os.path.join(papers_dir, "pdfs")
    
    # Get all PDFs
    all_pdf_files = sorted(glob.glob(os.path.join(pdf_dir, "*.pdf")))
    
    # Select batch if specified
    if batch_num is not None:
        start_idx = (batch_num - 1) * batch_size
        end_idx = start_idx + batch_size
        pdf_files = all_pdf_files[start_idx:end_idx]
    else:
        pdf_files = all_pdf_files
    
    # Create ZIP in memory
    zip_buffer = io.BytesIO()
    
    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zip_file:
        # Add selected PDFs
        for pdf_path in pdf_files:
            pdf_name = os.path.basename(pdf_path)
            zip_file.write(pdf_path, pdf_name)
        
        # Add markdown files too (only for full archive)
        if batch_num is None:
            md_files = glob.glob(os.path.join(papers_dir, "*.md"))
            for md_path in md_files:
                md_name = os.path.basename(md_path)
                zip_file.write(md_path, f"markdown/{md_name}")
    
    zip_bytes = zip_buffer.getvalue()
    
    # Optionally save to file
    if output_path:
        with open(output_path, 'wb') as f:
            f.write(zip_bytes)
    
    return zip_bytes


def get_batch_info(papers_dir: str = "papers", batch_size: int = 10) -> Dict[str, Any]:
    """Get information about paper batches"""
    pdf_dir = os.path.join(papers_dir, "pdfs")
    pdf_files = glob.glob(os.path.join(pdf_dir, "*.pdf")) if os.path.exists(pdf_dir) else []
    
    total_papers = len(pdf_files)
    total_batches = (total_papers + batch_size - 1) // batch_size  # Ceiling division
    
    return {
        "total_papers": total_papers,
        "batch_size": batch_size,
        "total_batches": total_batches,
        "papers_per_batch": batch_size
    }


def get_paper_stats(papers_dir: str = "papers") -> Dict[str, any]:
    """Get statistics about papers"""
    
    markdown_files = glob.glob(os.path.join(papers_dir, "*.md"))
    pdf_dir = os.path.join(papers_dir, "pdfs")
    pdf_files = glob.glob(os.path.join(pdf_dir, "*.pdf")) if os.path.exists(pdf_dir) else []
    
    total_md_size = sum(os.path.getsize(f) for f in markdown_files)
    total_pdf_size = sum(os.path.getsize(f) for f in pdf_files) if pdf_files else 0
    
    return {
        "total_papers": len(markdown_files),
        "total_pdfs": len(pdf_files),
        "total_md_size_mb": total_md_size / (1024 * 1024),
        "total_pdf_size_mb": total_pdf_size / (1024 * 1024),
        "papers_missing_pdf": len(markdown_files) - len(pdf_files)
    }


if __name__ == "__main__":
    # Command-line usage
    import sys
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "all":
            print("🚀 Generating PDFs for all papers...")
            generate_all_paper_pdfs(force_regenerate=True)
        elif sys.argv[1] == "zip":
            print("📦 Creating ZIP archive...")
            zip_bytes = create_papers_zip()
            print(f"✅ Created all_papers.zip ({len(zip_bytes):,} bytes)")
        elif sys.argv[1] == "stats":
            stats = get_paper_stats()
            print(f"\n📊 Paper Statistics:")
            print(f"  Total papers (MD): {stats['total_papers']}")
            print(f"  Total PDFs: {stats['total_pdfs']}")
            print(f"  Missing PDFs: {stats['papers_missing_pdf']}")
            print(f"  MD size: {stats['total_md_size_mb']:.2f} MB")
            print(f"  PDF size: {stats['total_pdf_size_mb']:.2f} MB")
        else:
            # Generate single paper
            pdf_bytes = generate_pdf_for_paper(sys.argv[1])
            print(f"✅ Generated PDF ({len(pdf_bytes):,} bytes)")
    else:
        # Default: generate all
        print("Usage: python paper_pdf_generator.py [all|zip|stats|<file.md>]")
        print("\nGenerating all PDFs by default...")
        generate_all_paper_pdfs()
