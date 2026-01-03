"""
Comprehensive PDF Generation System for TI Papers
- Individual searchable PDFs for each paper
- Master catalog PDF with all papers combined
- Text-to-speech compatible (selectable text)
- Table of contents with bookmarks
"""

import os
import markdown
from weasyprint import HTML, CSS
from pathlib import Path
import zipfile
from datetime import datetime

class TIPDFGenerator:
    def __init__(self, papers_dir="papers", output_dir="papers/pdfs"):
        self.papers_dir = Path(papers_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
    def get_css_styles(self):
        """
        CSS styles for PDF generation
        - Ensures text is selectable (audio-ready)
        - Professional formatting
        - Page breaks and headers
        """
        return """
        @page {
            size: Letter;
            margin: 1in;
            @top-center {
                content: "Transcendent Intelligence Framework - Brandon Emerick 2025";
                font-size: 9pt;
                color: #666;
            }
            @bottom-center {
                content: "Page " counter(page);
                font-size: 9pt;
                color: #666;
            }
        }
        
        body {
            font-family: 'Georgia', 'Times New Roman', serif;
            font-size: 11pt;
            line-height: 1.6;
            color: #000;
            text-align: justify;
        }
        
        h1 {
            font-size: 24pt;
            font-weight: bold;
            color: #1a1a1a;
            margin-top: 20pt;
            margin-bottom: 12pt;
            page-break-after: avoid;
        }
        
        h2 {
            font-size: 18pt;
            font-weight: bold;
            color: #2a2a2a;
            margin-top: 18pt;
            margin-bottom: 10pt;
            page-break-after: avoid;
        }
        
        h3 {
            font-size: 14pt;
            font-weight: bold;
            color: #3a3a3a;
            margin-top: 14pt;
            margin-bottom: 8pt;
            page-break-after: avoid;
        }
        
        h4 {
            font-size: 12pt;
            font-weight: bold;
            color: #4a4a4a;
            margin-top: 12pt;
            margin-bottom: 6pt;
            page-break-after: avoid;
        }
        
        p {
            margin-bottom: 6pt;
            orphans: 3;
            widows: 3;
        }
        
        code {
            font-family: 'Courier New', monospace;
            font-size: 9pt;
            background-color: #f5f5f5;
            padding: 2pt 4pt;
            border-radius: 2pt;
        }
        
        pre {
            font-family: 'Courier New', monospace;
            font-size: 9pt;
            background-color: #f5f5f5;
            padding: 10pt;
            border-left: 3pt solid #666;
            margin: 10pt 0;
            overflow-x: auto;
            page-break-inside: avoid;
        }
        
        pre code {
            background-color: transparent;
            padding: 0;
        }
        
        blockquote {
            font-style: italic;
            border-left: 3pt solid #999;
            padding-left: 12pt;
            margin-left: 0;
            margin-right: 0;
            color: #555;
        }
        
        table {
            width: 100%;
            border-collapse: collapse;
            margin: 12pt 0;
            page-break-inside: avoid;
        }
        
        th, td {
            border: 1pt solid #999;
            padding: 6pt;
            text-align: left;
        }
        
        th {
            background-color: #f0f0f0;
            font-weight: bold;
        }
        
        ul, ol {
            margin: 6pt 0;
            padding-left: 24pt;
        }
        
        li {
            margin-bottom: 3pt;
        }
        
        hr {
            border: none;
            border-top: 1pt solid #ccc;
            margin: 18pt 0;
        }
        
        a {
            color: #0066cc;
            text-decoration: none;
        }
        
        .page-break {
            page-break-before: always;
        }
        
        .toc {
            page-break-after: always;
        }
        
        .toc h1 {
            text-align: center;
            margin-bottom: 24pt;
        }
        
        .toc ul {
            list-style-type: none;
            padding-left: 0;
        }
        
        .toc li {
            margin-bottom: 8pt;
        }
        
        .toc a {
            text-decoration: none;
            color: #000;
        }
        """
    
    def markdown_to_html(self, markdown_content, title="TI Paper"):
        """Convert markdown to HTML with proper structure"""
        # Convert markdown to HTML
        html_content = markdown.markdown(
            markdown_content,
            extensions=[
                'tables',
                'fenced_code',
                'codehilite',
                'nl2br',
                'sane_lists',
                'toc'
            ]
        )
        
        # Wrap in full HTML document
        full_html = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="UTF-8">
            <title>{title}</title>
        </head>
        <body>
            {html_content}
        </body>
        </html>
        """
        
        return full_html
    
    def generate_single_pdf(self, markdown_file, output_name=None):
        """
        Generate a single searchable, audio-compatible PDF from markdown
        
        Args:
            markdown_file: Path to markdown file
            output_name: Optional custom output name (without .pdf)
        
        Returns:
            Path to generated PDF
        """
        markdown_path = Path(markdown_file)
        
        if not markdown_path.exists():
            raise FileNotFoundError(f"Markdown file not found: {markdown_file}")
        
        # Read markdown content
        with open(markdown_path, 'r', encoding='utf-8') as f:
            markdown_content = f.read()
        
        # Extract title from first # heading or use filename
        title = markdown_path.stem.replace('_', ' ').title()
        for line in markdown_content.split('\n'):
            if line.startswith('# '):
                title = line[2:].strip()
                break
        
        # Convert to HTML
        html_content = self.markdown_to_html(markdown_content, title)
        
        # Generate PDF filename
        if output_name:
            pdf_filename = f"{output_name}.pdf"
        else:
            pdf_filename = f"{markdown_path.stem}.pdf"
        
        pdf_path = self.output_dir / pdf_filename
        
        # Generate PDF with WeasyPrint
        HTML(string=html_content).write_pdf(
            pdf_path,
            stylesheets=[CSS(string=self.get_css_styles())]
        )
        
        print(f"✅ Generated: {pdf_path}")
        return pdf_path
    
    def generate_all_papers(self):
        """
        Generate PDFs for all markdown papers in papers directory
        
        Returns:
            List of generated PDF paths
        """
        markdown_files = list(self.papers_dir.glob("*.md"))
        
        # Exclude certain files
        exclude = {'README.md', 'TEMPLATE.md'}
        markdown_files = [f for f in markdown_files if f.name not in exclude]
        
        print(f"📚 Found {len(markdown_files)} papers to convert...")
        
        generated_pdfs = []
        
        for md_file in sorted(markdown_files):
            try:
                pdf_path = self.generate_single_pdf(md_file)
                generated_pdfs.append(pdf_path)
            except Exception as e:
                print(f"❌ Error generating PDF for {md_file.name}: {e}")
        
        print(f"✅ Successfully generated {len(generated_pdfs)}/{len(markdown_files)} PDFs")
        
        return generated_pdfs
    
    def generate_master_catalog(self, pdf_list=None):
        """
        Generate master catalog PDF combining all papers with table of contents
        
        Args:
            pdf_list: Optional list of PDF paths to include. If None, uses all PDFs in output_dir
        
        Returns:
            Path to master catalog PDF
        """
        if pdf_list is None:
            pdf_list = list(self.output_dir.glob("*.pdf"))
            # Exclude previous master catalogs
            pdf_list = [p for p in pdf_list if not p.name.startswith("TI_COMPLETE_CATALOG")]
        
        # Read all markdown files to create combined document
        markdown_files = []
        for pdf_path in sorted(pdf_list):
            md_path = self.papers_dir / f"{pdf_path.stem}.md"
            if md_path.exists():
                markdown_files.append(md_path)
        
        # Build table of contents
        toc_html = """
        <div class="toc">
            <h1>Transcendent Intelligence Framework</h1>
            <h2>Complete Paper Catalog</h2>
            <p><strong>Brandon Emerick - November 2025</strong></p>
            <hr>
            <h3>Table of Contents</h3>
            <ul>
        """
        
        combined_markdown = ""
        
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
            toc_html += f'<li>{idx}. {title}</li>\n'
            
            # Add to combined content with page break
            if idx > 1:
                combined_markdown += "\n\n---\n\n<div class='page-break'></div>\n\n"
            
            combined_markdown += f"# {idx}. {title}\n\n"
            combined_markdown += content.replace(f"# {title}", "")  # Remove duplicate title
        
        toc_html += """
            </ul>
        </div>
        """
        
        # Convert combined markdown to HTML
        html_content = self.markdown_to_html(combined_markdown, "TI Framework - Complete Catalog")
        
        # Insert TOC after <body> tag
        html_content = html_content.replace('<body>', f'<body>{toc_html}')
        
        # Generate master PDF
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        master_pdf_path = self.output_dir / f"TI_COMPLETE_CATALOG_{timestamp}.pdf"
        
        HTML(string=html_content).write_pdf(
            master_pdf_path,
            stylesheets=[CSS(string=self.get_css_styles())]
        )
        
        print(f"✅ Generated Master Catalog: {master_pdf_path}")
        print(f"📖 Contains {len(markdown_files)} papers")
        
        return master_pdf_path
    
    def create_zip_archive(self, include_master=True):
        """
        Create ZIP archive of all PDFs
        
        Args:
            include_master: Whether to include master catalog in zip
        
        Returns:
            Path to ZIP archive
        """
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        zip_path = self.output_dir / f"TI_ALL_PAPERS_{timestamp}.zip"
        
        pdf_files = list(self.output_dir.glob("*.pdf"))
        
        if not include_master:
            pdf_files = [p for p in pdf_files if not p.name.startswith("TI_COMPLETE_CATALOG")]
        
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for pdf_path in sorted(pdf_files):
                zipf.write(pdf_path, pdf_path.name)
        
        print(f"✅ Created ZIP archive: {zip_path}")
        print(f"📦 Contains {len(pdf_files)} PDFs")
        
        return zip_path
    
    def generate_complete_library(self):
        """
        Complete workflow: Generate all PDFs, master catalog, and ZIP archive
        
        Returns:
            Dict with paths to all generated files
        """
        print("🚀 Starting TI PDF Library Generation...")
        print("=" * 60)
        
        # Step 1: Generate individual PDFs
        print("\n📄 Step 1: Generating individual paper PDFs...")
        individual_pdfs = self.generate_all_papers()
        
        # Step 2: Generate master catalog
        print("\n📚 Step 2: Generating master catalog PDF...")
        master_pdf = self.generate_master_catalog(individual_pdfs)
        
        # Step 3: Create ZIP archive
        print("\n📦 Step 3: Creating ZIP archive...")
        zip_archive = self.create_zip_archive(include_master=True)
        
        print("\n" + "=" * 60)
        print("✅ TI PDF Library Generation Complete!")
        print(f"📊 Total: {len(individual_pdfs)} individual PDFs + 1 master catalog + 1 ZIP")
        
        return {
            'individual_pdfs': individual_pdfs,
            'master_catalog': master_pdf,
            'zip_archive': zip_archive,
            'total_count': len(individual_pdfs)
        }


def main():
    """Main execution"""
    generator = TIPDFGenerator()
    results = generator.generate_complete_library()
    
    print("\n📍 Output Directory:", generator.output_dir)
    print("\n🎯 Quick Access:")
    print(f"  - Master Catalog: {results['master_catalog'].name}")
    print(f"  - ZIP Archive: {results['zip_archive'].name}")
    print(f"  - Individual PDFs: {results['total_count']} files in pdfs/")
    
    return results


if __name__ == "__main__":
    main()
