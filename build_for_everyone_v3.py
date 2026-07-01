"""
Build 'TI Sigma For Everyone V3' PDF from the living book/ chapter sources.
Assembles book/ch00_*..ch27_* in order and renders to a styled PDF.
"""
import os
import glob
import datetime
import markdown
from weasyprint import HTML, CSS

BOOK_DIR = "book"
OUT_DIR = "papers/pdfs"
os.makedirs(OUT_DIR, exist_ok=True)
OUT_PDF = os.path.join(OUT_DIR, "TI_SIGMA_FOR_EVERYONE_V3.pdf")

TITLE = "TI Sigma For Everyone"
SUBTITLE = "V3"


def collect_chapters():
    files = sorted(glob.glob(os.path.join(BOOK_DIR, "ch[0-9][0-9]_*.md")))
    if not files:
        raise SystemExit("No chapter files found in book/")
    return files


def build_markdown(files):
    parts = []
    for i, path in enumerate(files):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read().strip()
        if i > 0:
            parts.append('\n\n<div class="page-break"></div>\n\n')
        parts.append(content)
    return "\n\n".join(parts)


CSS_STR = '''
@page {
    margin: 1in;
    size: letter;
    @bottom-center { content: counter(page); font-size: 10px; color: #666; }
}
body {
    font-family: Georgia, serif;
    font-size: 11pt;
    line-height: 1.6;
    color: #333;
    max-width: 100%;
}
h1 {
    font-size: 24pt; color: #1a1a2e;
    border-bottom: 3px solid #4a4a8a; padding-bottom: 10px;
    margin-top: 30px; page-break-after: avoid;
}
h2 {
    font-size: 18pt; color: #2a2a4e; margin-top: 25px;
    border-bottom: 1px solid #ccc; padding-bottom: 5px; page-break-after: avoid;
}
h3 { font-size: 14pt; color: #3a3a5e; margin-top: 20px; page-break-after: avoid; }
h4 { font-size: 12pt; color: #3a3a5e; margin-top: 16px; page-break-after: avoid; }
p { margin: 8px 0; text-align: justify; }
blockquote {
    border-left: 4px solid #4a4a8a; margin: 12px 0; padding: 6px 16px;
    background: #f6f6fb; color: #222; font-style: italic;
}
code {
    font-family: "DejaVu Sans Mono", monospace; font-size: 9.5pt;
    background: #f0f0f4; padding: 1px 4px; border-radius: 3px;
}
pre {
    background: #f0f0f4; padding: 10px; border-radius: 5px;
    overflow-x: auto; font-size: 9pt; page-break-inside: avoid;
}
pre code { background: none; padding: 0; }
table { border-collapse: collapse; width: 100%; margin: 12px 0; font-size: 9.5pt; }
th, td { border: 1px solid #bbb; padding: 6px 8px; text-align: left; }
th { background: #e8e8f2; }
ul, ol { margin: 8px 0 8px 22px; }
li { margin: 4px 0; }
hr { border: none; border-top: 1px solid #ccc; margin: 20px 0; }
.page-break { page-break-before: always; }
h1 { page-break-before: always; }
.title-page h1 { page-break-before: avoid; }
'''

TITLE_PAGE = f'''
<div class="title-page" style="text-align:center; margin-top:180px;">
  <h1 style="font-size:34pt; border:none;">{TITLE}</h1>
  <p style="font-size:16pt; color:#4a4a8a; font-style:italic;">An Accessible Guide to Tralse Informationalism</p>
  <p style="font-size:20pt; color:#1a1a2e; margin-top:30px;"><strong>{SUBTITLE}</strong></p>
  <p style="font-size:13pt; margin-top:40px;">Brandon Charles Emerick</p>
  <p style="font-size:11pt; color:#666;">Compiled {datetime.date.today().isoformat()}</p>
</div>
<div class="page-break"></div>
'''


def main():
    files = collect_chapters()
    print(f"Assembling {len(files)} chapters:")
    for p in files:
        print("  -", os.path.basename(p))
    combined_md = build_markdown(files)
    body_html = markdown.markdown(
        combined_md, extensions=["tables", "fenced_code", "toc", "sane_lists"]
    )
    full_html = f"<html><head><meta charset='utf-8'></head><body>{TITLE_PAGE}{body_html}</body></html>"
    HTML(string=full_html).write_pdf(OUT_PDF, stylesheets=[CSS(string=CSS_STR)])
    size = os.path.getsize(OUT_PDF)
    print(f"\nWrote {OUT_PDF} ({size:,} bytes)")


if __name__ == "__main__":
    main()
