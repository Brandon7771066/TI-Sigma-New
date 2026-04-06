"""
Generate downloadable PDF proofs for each Millennium Prize problem + Collatz.
Uses pure Python — no external dependencies required.
Output: static/pdfs/*.pdf
"""

import os
import re
import struct
import textwrap
import zlib

os.makedirs("static/pdfs", exist_ok=True)


# ── Minimal pure-Python PDF writer ─────────────────────────────────────────

class PDFWriter:
    """Minimal multi-page PDF generator using built-in Python only."""

    PAGE_W = 612   # US Letter points
    PAGE_H = 792
    MARGIN = 54    # 0.75 inch
    BODY_W = PAGE_W - 2 * MARGIN
    LINE_H_BODY = 14
    LINE_H_H1   = 22
    LINE_H_H2   = 18
    LINE_H_H3   = 15
    FONT_BODY   = 11
    FONT_H1     = 18
    FONT_H2     = 14
    FONT_H3     = 12

    def __init__(self):
        self._objects = []   # list of (id, bytes)
        self._pages   = []   # list of page object ids
        # IDs 1-4 are reserved: 1=Catalog, 2=Pages, 3=Font/Regular, 4=Font/Bold
        self._obj_id  = 5

    def _alloc_id(self):
        oid = self._obj_id
        self._obj_id += 1
        return oid

    def _add_obj(self, content: bytes):
        oid = self._alloc_id()
        self._objects.append((oid, content))
        return oid

    def _encode(self, text: str) -> str:
        """Escape PDF string and convert non-ASCII to '?'."""
        out = []
        for ch in text:
            if ord(ch) > 127:
                out.append('?')
            elif ch == '(':
                out.append(r'\(')
            elif ch == ')':
                out.append(r'\)')
            elif ch == '\\':
                out.append(r'\\')
            else:
                out.append(ch)
        return ''.join(out)

    def add_page(self, lines):
        """
        lines: list of (style, text)
          style: 'h1', 'h2', 'h3', 'body', 'code', 'blank'
        """
        stream_parts = []
        y = self.PAGE_H - self.MARGIN

        def emit(text, font, size, line_h, bold=False):
            nonlocal y
            if y < self.MARGIN + line_h:
                return False   # no room
            fname = "/F2" if bold else "/F1"
            stream_parts.append(f"BT {fname} {size} Tf {self.MARGIN} {y:.1f} Td ({self._encode(text)}) Tj ET")
            y -= line_h
            return True

        for style, text in lines:
            if style == 'blank':
                y -= self.LINE_H_BODY * 0.5
                continue
            if style == 'h1':
                y -= 4
                emit(text, "/F2", self.FONT_H1, self.LINE_H_H1, bold=True)
                y -= 4
            elif style == 'h2':
                y -= 3
                emit(text, "/F2", self.FONT_H2, self.LINE_H_H2, bold=True)
                y -= 2
            elif style == 'h3':
                y -= 2
                emit(text, "/F2", self.FONT_H3, self.LINE_H_H3, bold=True)
                y -= 1
            elif style in ('body', 'code'):
                char_w = self.FONT_BODY * 0.5 if style == 'code' else self.FONT_BODY * 0.52
                wrap_w = int(self.BODY_W / char_w)
                wrapped = textwrap.wrap(text, width=wrap_w) if text.strip() else ['']
                for wline in wrapped:
                    if y < self.MARGIN + self.LINE_H_BODY:
                        break
                    emit(wline, "/F1", self.FONT_BODY, self.LINE_H_BODY)

        stream_bytes = "\n".join(stream_parts).encode('latin-1', errors='replace')
        # compress
        compressed = zlib.compress(stream_bytes)

        stream_oid = self._add_obj(
            f"<< /Length {len(compressed)} /Filter /FlateDecode >>\nstream\n".encode()
            + compressed
            + b"\nendstream"
        )
        page_oid = self._add_obj(
            f"<< /Type /Page /Parent 2 0 R "
            f"/MediaBox [0 0 {self.PAGE_W} {self.PAGE_H}] "
            f"/Contents {stream_oid} 0 R "
            f"/Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> >>".encode()
        )
        self._pages.append(page_oid)

    def build(self) -> bytes:
        """Assemble and return the complete PDF bytes."""
        # Reserve obj ids 1 (catalog), 2 (pages), 3 (font regular), 4 (font bold)
        # They are written first — we manage manually
        body = b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n"
        offsets = {}

        def write_obj(oid, content: bytes):
            nonlocal body
            offsets[oid] = len(body)
            body += f"{oid} 0 obj\n".encode() + content + b"\nendobj\n"

        page_refs = " ".join(f"{p} 0 R" for p in self._pages)

        # Object 1: Catalog
        write_obj(1, b"<< /Type /Catalog /Pages 2 0 R >>")
        # Object 2: Pages
        write_obj(2, f"<< /Type /Pages /Kids [{page_refs}] /Count {len(self._pages)} >>".encode())
        # Object 3: Regular font (Helvetica)
        write_obj(3, b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica "
                     b"/Encoding /WinAnsiEncoding >>")
        # Object 4: Bold font
        write_obj(4, b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold "
                     b"/Encoding /WinAnsiEncoding >>")

        # Write remaining objects
        for oid, content in self._objects:
            write_obj(oid, content)

        # xref — each entry MUST be exactly 20 bytes (PDF spec §7.5.4)
        xref_offset = len(body)
        all_ids = sorted(offsets.keys())
        max_id = max(all_ids)
        body += f"xref\n0 {max_id + 1}\n".encode()
        # Free object 0
        body += b"0000000000 65535 f \r\n"
        for i in range(1, max_id + 1):
            if i in offsets:
                body += f"{offsets[i]:010d} 00000 n \r\n".encode()
            else:
                body += b"0000000000 65535 f \r\n"

        body += (
            f"trailer\n<< /Size {max_id + 1} /Root 1 0 R >>\n"
            f"startxref\n{xref_offset}\n%%EOF\n"
        ).encode()

        return body


# ── Markdown → lines parser ─────────────────────────────────────────────────

def md_to_lines(md_text: str):
    """Convert markdown to list of (style, text) tuples for PDFWriter."""
    lines = []
    in_code = False
    for raw in md_text.split('\n'):
        stripped = raw.strip()

        # Code fences
        if stripped.startswith('```'):
            in_code = not in_code
            continue
        if in_code:
            lines.append(('code', raw.rstrip()))
            continue

        # Headers
        m = re.match(r'^(#{1,3})\s+(.*)', stripped)
        if m:
            level = len(m.group(1))
            text  = m.group(2).strip()
            # strip markdown bold/italic from headers
            text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
            text = re.sub(r'\*(.+?)\*', r'\1', text)
            style = {1: 'h1', 2: 'h2', 3: 'h3'}[min(level, 3)]
            lines.append(('blank', ''))
            lines.append((style, text))
            continue

        # Blank lines
        if not stripped:
            lines.append(('blank', ''))
            continue

        # Strip common markdown inline formatting
        text = re.sub(r'\*\*(.+?)\*\*', r'\1', stripped)
        text = re.sub(r'\*(.+?)\*',   r'\1', text)
        text = re.sub(r'`(.+?)`',     r'\1', text)
        text = re.sub(r'\[(.+?)\]\(.+?\)', r'\1', text)
        text = re.sub(r'^[-*]\s+', '• ', text)
        text = re.sub(r'^\d+\.\s+', '', text)
        text = re.sub(r'^>\s+', '  ', text)
        lines.append(('body', text))

    return lines


def lean4_to_lines(lean_text: str):
    """Convert Lean4 source to readable lines for PDF."""
    lines = []
    in_comment = False
    for raw in lean_text.split('\n'):
        stripped = raw.strip()
        if stripped.startswith('/-'):
            in_comment = True
        if in_comment:
            # Clean up comment markers
            text = raw.replace('/-', '').replace('-/', '').replace('--', '').strip()
            if text.startswith('=') or text.startswith('-'):
                continue
            if text:
                if text.isupper() and len(text) > 4:
                    lines.append(('h3', text.title()))
                else:
                    lines.append(('body', text))
        else:
            # Show key theorem statements
            if any(kw in stripped for kw in ('theorem ', 'lemma ', 'def ', 'axiom ')):
                lines.append(('code', stripped[:120]))
        if '-/' in raw:
            in_comment = False
    return lines


def build_pdf_from_md(md_path: str, fallback_lean: str = None) -> bytes:
    try:
        with open(md_path, 'r', encoding='utf-8', errors='replace') as f:
            content = f.read()
        all_lines = md_to_lines(content)
    except FileNotFoundError:
        if fallback_lean:
            with open(fallback_lean, 'r', encoding='utf-8', errors='replace') as f:
                content = f.read()
            all_lines = lean4_to_lines(content)
        else:
            all_lines = [('h1', 'Proof not found'), ('body', 'File missing.')]

    writer = PDFWriter()
    LINES_PER_PAGE = 48

    # Paginate
    page_lines = []
    line_count  = 0

    for style, text in all_lines:
        cost = 1
        if style == 'h1':   cost = 3
        elif style == 'h2': cost = 2
        elif style == 'h3': cost = 2

        if line_count + cost > LINES_PER_PAGE and page_lines:
            writer.add_page(page_lines)
            page_lines = []
            line_count  = 0

        page_lines.append((style, text))
        line_count += cost

    if page_lines:
        writer.add_page(page_lines)

    return writer.build()


# ── Define the 7 proofs ─────────────────────────────────────────────────────

PROOFS = [
    {
        "filename": "Collatz_Nu2_Countdown_Theorem.pdf",
        "md":       "papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md",
        "lean":     "lean4/Collatz.lean",
    },
    {
        "filename": "Riemann_Hypothesis_TI_Sigma.pdf",
        "md":       "papers/RIEMANN_HYPOTHESIS_TI_PROOF_v2.md",
        "lean":     "lean4/RiemannUOP.lean",
    },
    {
        "filename": "P_vs_NP_Creation_Verification_Asymmetry.pdf",
        "md":       "papers/P_VS_NP_CONVENTIONAL_PROOF.md",
        "lean":     "lean4/PvsNP.lean",
    },
    {
        "filename": "Yang_Mills_Mass_Gap_Being_Dual.pdf",
        "md":       None,
        "lean":     "lean4/YangMills.lean",
    },
    {
        "filename": "Navier_Stokes_Smoothness_Vern.pdf",
        "md":       None,
        "lean":     "lean4/NavierStokes.lean",
    },
    {
        "filename": "Hodge_Conjecture_Vern_Cohomology.pdf",
        "md":       None,
        "lean":     "lean4/Hodge.lean",
    },
    {
        "filename": "Birch_Swinnerton_Dyer_Being_Theorem.pdf",
        "md":       None,
        "lean":     "lean4/BSD.lean",
    },
]


def generate_all():
    for proof in PROOFS:
        path = f"static/pdfs/{proof['filename']}"
        md   = proof.get("md")
        lean = proof.get("lean")

        # Choose source
        if md and os.path.exists(md):
            src_md   = md
            src_lean = lean
        else:
            src_md   = None
            src_lean = lean

        print(f"Generating {proof['filename']} ...", end=" ")
        try:
            pdf_bytes = build_pdf_from_md(src_md or "__missing__", src_lean)
            with open(path, 'wb') as f:
                f.write(pdf_bytes)
            print(f"OK ({len(pdf_bytes):,} bytes)")
        except Exception as e:
            print(f"ERROR: {e}")

    print("\nDone. PDFs written to static/pdfs/")


if __name__ == "__main__":
    generate_all()
