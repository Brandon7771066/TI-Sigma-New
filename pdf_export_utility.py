import markdown
from weasyprint import HTML, CSS
import re
from pathlib import Path

def clean_markdown_for_pdf(md_content):
    """Remove excessive asterisks and format for professional PDF"""
    
    # Remove excessive bold/italic markdown (keep single * for emphasis)
    cleaned = re.sub(r'\*\*\*\*+', '**', md_content)
    cleaned = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', cleaned)
    cleaned = re.sub(r'\*([^*]+)\*', r'<em>\1</em>', cleaned)
    
    # Keep headings but remove excessive markdown
    cleaned = re.sub(r'#{6,}', '######', cleaned)
    
    return cleaned

def markdown_to_pdf(md_file_path, output_pdf_path):
    """Convert markdown file to APA-style PDF"""
    
    # Read markdown content
    with open(md_file_path, 'r', encoding='utf-8') as f:
        md_content = f.read()
    
    # Clean up excessive formatting
    cleaned_md = clean_markdown_for_pdf(md_content)
    
    # Convert markdown to HTML
    html_content = markdown.markdown(
        cleaned_md,
        extensions=['tables', 'fenced_code', 'nl2br']
    )
    
    # APA-style CSS
    apa_css = """
    @page {
        size: Letter;
        margin: 1in;
        @bottom-right {
            content: counter(page);
        }
    }
    
    body {
        font-family: "Times New Roman", Times, serif;
        font-size: 12pt;
        line-height: 2.0;
        text-align: left;
        color: #000;
    }
    
    h1 {
        font-size: 14pt;
        font-weight: bold;
        text-align: center;
        margin-top: 0;
        margin-bottom: 24pt;
        page-break-after: avoid;
    }
    
    h2 {
        font-size: 12pt;
        font-weight: bold;
        margin-top: 24pt;
        margin-bottom: 12pt;
        page-break-after: avoid;
    }
    
    h3 {
        font-size: 12pt;
        font-weight: bold;
        font-style: italic;
        margin-top: 12pt;
        margin-bottom: 12pt;
        page-break-after: avoid;
    }
    
    h4 {
        font-size: 12pt;
        font-weight: normal;
        font-style: italic;
        margin-top: 12pt;
        margin-bottom: 12pt;
        text-indent: 0.5in;
        page-break-after: avoid;
    }
    
    p {
        margin-top: 0;
        margin-bottom: 12pt;
        text-indent: 0.5in;
        text-align: left;
    }
    
    ul, ol {
        margin-left: 0.5in;
        margin-bottom: 12pt;
    }
    
    table {
        width: 100%;
        border-collapse: collapse;
        margin: 12pt 0;
        font-size: 11pt;
    }
    
    th {
        border-top: 2px solid #000;
        border-bottom: 1px solid #000;
        padding: 6pt;
        text-align: left;
        font-weight: bold;
    }
    
    td {
        border-bottom: 1px solid #ccc;
        padding: 6pt;
        text-align: left;
    }
    
    tr:last-child td {
        border-bottom: 2px solid #000;
    }
    
    strong {
        font-weight: bold;
    }
    
    em {
        font-style: italic;
    }
    
    blockquote {
        margin-left: 0.5in;
        margin-right: 0.5in;
        font-style: italic;
    }
    
    hr {
        border: none;
        border-top: 1px solid #000;
        margin: 24pt 0;
    }
    
    code {
        font-family: "Courier New", Courier, monospace;
        font-size: 10pt;
        background-color: #f5f5f5;
        padding: 2pt 4pt;
    }
    
    pre {
        font-family: "Courier New", Courier, monospace;
        font-size: 10pt;
        background-color: #f5f5f5;
        padding: 12pt;
        overflow-x: auto;
        margin: 12pt 0;
    }
    """
    
    # Wrap in HTML document
    full_html = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="utf-8">
        <style>{apa_css}</style>
    </head>
    <body>
        {html_content}
    </body>
    </html>
    """
    
    # Generate PDF
    HTML(string=full_html).write_pdf(output_pdf_path)
    
    return output_pdf_path

def export_all_papers():
    """Export all research papers to PDF"""
    
    papers_dir = Path("papers")
    pdf_output_dir = papers_dir / "pdfs"
    pdf_output_dir.mkdir(exist_ok=True)
    
    # Papers to export (note: space in "MYR ION" is intentional - matches actual filename)
    papers = [
        ("CCC_ABSOLUTE_TIME_THEORY_TIME_ARTICLE.md", "CCC_Absolute_Time_Theory_TIME_Article.pdf"),
        ("INDEPENDENT_EVENTS_DONT_EXIST_IN_PROBABILITY.md", "Independent_Events_Dont_Exist_In_Probability.pdf"),
        ("NEURAL_ACTIVITY_AND_LANGUAGE_AS_MYR ION_RESOLUTIONS.md", "Neural_Activity_And_Language_As_Myrion_Resolutions.pdf"),
        ("FREE_WILL_SWEET_SPOT_TWO_THIRDS_DETERMINED.md", "Free_Will_Sweet_Spot_Two_Thirds_Determined.pdf"),
    ]
    
    results = []
    for md_filename, pdf_filename in papers:
        md_path = papers_dir / md_filename
        pdf_path = pdf_output_dir / pdf_filename
        
        if md_path.exists():
            try:
                markdown_to_pdf(str(md_path), str(pdf_path))
                results.append(f"✅ {pdf_filename}")
                print(f"✅ Created: {pdf_path}")
            except Exception as e:
                results.append(f"❌ {pdf_filename}: {e}")
                print(f"❌ Error creating {pdf_filename}: {e}")
        else:
            results.append(f"⚠️ {md_filename} not found")
            print(f"⚠️ {md_filename} not found")
    
    return results

if __name__ == "__main__":
    print("🔄 Exporting research papers to PDF...")
    print("=" * 60)
    results = export_all_papers()
    print("=" * 60)
    print("\n📊 EXPORT SUMMARY:")
    for result in results:
        print(result)
    print("\n✨ PDF export complete!")
