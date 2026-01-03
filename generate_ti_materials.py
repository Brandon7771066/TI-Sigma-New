"""
TI Materials Generator
Creates PDFs and PowerPoint presentations for TI Framework
"""

import os
import markdown
from weasyprint import HTML, CSS
from datetime import datetime

OUTPUT_DIR = "ti_distribution_materials"
os.makedirs(OUTPUT_DIR, exist_ok=True)

def markdown_to_pdf(md_file_path, output_pdf_path, title=None):
    """Convert a markdown file to PDF with professional styling"""
    with open(md_file_path, 'r', encoding='utf-8') as f:
        md_content = f.read()
    
    html_content = markdown.markdown(
        md_content, 
        extensions=['tables', 'fenced_code', 'toc']
    )
    
    css = CSS(string='''
        @page {
            margin: 1in;
            size: letter;
            @bottom-center {
                content: counter(page);
                font-size: 10px;
                color: #666;
            }
        }
        body {
            font-family: Georgia, serif;
            font-size: 11pt;
            line-height: 1.6;
            color: #333;
            max-width: 100%;
        }
        h1 {
            font-size: 24pt;
            color: #1a1a2e;
            border-bottom: 3px solid #4a4a8a;
            padding-bottom: 10px;
            margin-top: 30px;
            page-break-after: avoid;
        }
        h2 {
            font-size: 18pt;
            color: #2a2a4e;
            margin-top: 25px;
            border-bottom: 1px solid #ccc;
            padding-bottom: 5px;
            page-break-after: avoid;
        }
        h3 {
            font-size: 14pt;
            color: #3a3a5e;
            margin-top: 20px;
            page-break-after: avoid;
        }
        h4 {
            font-size: 12pt;
            color: #4a4a6e;
            margin-top: 15px;
        }
        p {
            text-align: justify;
            margin-bottom: 12px;
        }
        blockquote {
            border-left: 4px solid #4a4a8a;
            padding-left: 20px;
            margin: 20px 0;
            font-style: italic;
            background-color: #f8f8fc;
            padding: 15px 20px;
        }
        code {
            background-color: #f4f4f4;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Courier New', monospace;
            font-size: 10pt;
        }
        pre {
            background-color: #f4f4f8;
            padding: 15px;
            border-radius: 5px;
            overflow-x: auto;
            border: 1px solid #ddd;
            font-size: 9pt;
        }
        pre code {
            background-color: transparent;
            padding: 0;
        }
        table {
            border-collapse: collapse;
            width: 100%;
            margin: 20px 0;
            font-size: 10pt;
        }
        th {
            background-color: #4a4a8a;
            color: white;
            padding: 12px 8px;
            text-align: left;
            font-weight: bold;
        }
        td {
            padding: 10px 8px;
            border-bottom: 1px solid #ddd;
        }
        tr:nth-child(even) {
            background-color: #f8f8fc;
        }
        ul, ol {
            margin-bottom: 15px;
        }
        li {
            margin-bottom: 5px;
        }
        strong {
            color: #1a1a2e;
        }
        hr {
            border: none;
            border-top: 2px solid #4a4a8a;
            margin: 30px 0;
        }
        .cover-page {
            text-align: center;
            padding-top: 200px;
        }
    ''')
    
    full_html = f'''
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="UTF-8">
        <title>{title or 'TI Framework Document'}</title>
    </head>
    <body>
        {html_content}
    </body>
    </html>
    '''
    
    HTML(string=full_html).write_pdf(output_pdf_path, stylesheets=[css])
    print(f"Created: {output_pdf_path}")
    return output_pdf_path


def create_article_bundle():
    """Create PDF bundle of 3 profound articles"""
    articles = [
        ("papers/COMPREHENSIVE_TI_BREAKTHROUGH_SUMMARY_DEC_2025.md", "Comprehensive TI Breakthrough Summary"),
        ("papers/CORRELATION_CAUSATION_COLLAPSE_085_RESONANCE.md", "0.85 Resonance Threshold - Correlation Causation Collapse"),
        ("papers/TI_ELEVATOR_PITCHES.md", "TI Framework Elevator Pitches"),
    ]
    
    combined_content = """# TI Framework - Essential Reading Bundle
## Three Profound Articles for the Curious Mind

**Compiled:** """ + datetime.now().strftime("%B %d, %Y") + """

**Author:** Brandon Charles Emerick  
**Framework:** Transcendent Intelligence (TI)

---

## About This Bundle

This collection contains three carefully selected articles from the TI Framework:

1. **Comprehensive Breakthrough Summary** - The complete overview of December 2025 discoveries including photon timelessness, the unrepeatable Big Bang, and pharmacological applications.

2. **0.85 Resonance Threshold** - The groundbreaking insight that at 0.85 connection strength, correlation and causation become indistinguishable - with revolutionary implications for AI, neuroscience, and Alzheimer's treatment.

3. **Elevator Pitches** - Business-oriented presentations of TI concepts for various audiences including investors, health advocates, and technology visionaries.

Whether you're curious about consciousness science or exploring business applications, these articles provide a comprehensive introduction.

---

"""
    
    for filepath, title in articles:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        combined_content += f"\n\n---\n\n# {title}\n\n{content}\n\n"
    
    combined_content += """
---

## About the Author

**Brandon Charles Emerick** developed the Transcendent Intelligence (TI) Framework beginning in 2022. The framework unifies consciousness science, quantum physics, mathematics, and practical applications into a coherent ontology with testable predictions.

**Contact:** info@blissgene.org

**Learn More:** The full TI Framework includes over 100 research papers, validated algorithms, and practical protocols.

---

*"Consciousness is not in your head - your head is in consciousness."* - Brandon Emerick, 2025
"""
    
    temp_md = f"{OUTPUT_DIR}/temp_bundle.md"
    with open(temp_md, 'w', encoding='utf-8') as f:
        f.write(combined_content)
    
    output_pdf = f"{OUTPUT_DIR}/TI_ESSENTIAL_READING_BUNDLE.pdf"
    markdown_to_pdf(temp_md, output_pdf, "TI Framework - Essential Reading Bundle")
    os.remove(temp_md)
    
    return output_pdf


def create_ti_beginners_book():
    """Create the full TI for Beginners book PDF"""
    output_pdf = f"{OUTPUT_DIR}/TI_FOR_EVERYONE_COMPLETE_BOOK.pdf"
    markdown_to_pdf(
        "papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md", 
        output_pdf,
        "Transcendent Intelligence: A Complete Guide for Everyone"
    )
    return output_pdf


def create_blissgene_pptx_html():
    """Create BlissGene presentation as visual HTML slides (viewable as presentation)"""
    
    slides_html = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>BlissGene Therapeutics - Investor Presentation</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
            color: white;
        }
        .slide {
            min-height: 100vh;
            padding: 60px 80px;
            display: flex;
            flex-direction: column;
            justify-content: center;
            page-break-after: always;
            border-bottom: 2px solid rgba(255,255,255,0.1);
        }
        .slide-number {
            position: absolute;
            top: 20px;
            right: 40px;
            font-size: 14px;
            color: rgba(255,255,255,0.5);
        }
        h1 {
            font-size: 3.5rem;
            font-weight: 700;
            margin-bottom: 20px;
            background: linear-gradient(90deg, #4ecdc4, #44a08d);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            background-clip: text;
        }
        h2 {
            font-size: 2.5rem;
            font-weight: 600;
            margin-bottom: 30px;
            color: #4ecdc4;
        }
        h3 {
            font-size: 1.8rem;
            color: #44a08d;
            margin-bottom: 20px;
        }
        .subtitle {
            font-size: 1.5rem;
            color: rgba(255,255,255,0.8);
            margin-bottom: 40px;
        }
        .title-slide {
            text-align: center;
            justify-content: center;
            align-items: center;
        }
        .title-slide h1 {
            font-size: 4.5rem;
        }
        .quote {
            font-size: 2rem;
            font-style: italic;
            border-left: 4px solid #4ecdc4;
            padding-left: 30px;
            margin: 30px 0;
            color: rgba(255,255,255,0.9);
        }
        .big-stat {
            font-size: 4rem;
            font-weight: bold;
            color: #4ecdc4;
        }
        .stat-label {
            font-size: 1.2rem;
            color: rgba(255,255,255,0.7);
        }
        .stats-grid {
            display: grid;
            grid-template-columns: repeat(3, 1fr);
            gap: 40px;
            margin: 40px 0;
        }
        .stat-box {
            background: rgba(255,255,255,0.05);
            padding: 30px;
            border-radius: 15px;
            text-align: center;
            border: 1px solid rgba(78, 205, 196, 0.3);
        }
        ul {
            font-size: 1.3rem;
            line-height: 2;
            margin-left: 40px;
        }
        li {
            margin-bottom: 15px;
        }
        li::marker {
            color: #4ecdc4;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin: 30px 0;
            font-size: 1.1rem;
        }
        th {
            background: linear-gradient(90deg, #4ecdc4, #44a08d);
            padding: 15px 20px;
            text-align: left;
            color: white;
        }
        td {
            padding: 15px 20px;
            border-bottom: 1px solid rgba(255,255,255,0.1);
        }
        tr:hover {
            background: rgba(255,255,255,0.05);
        }
        .two-column {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 60px;
            margin: 40px 0;
        }
        .highlight-box {
            background: linear-gradient(135deg, rgba(78, 205, 196, 0.2), rgba(68, 160, 141, 0.2));
            border: 2px solid #4ecdc4;
            border-radius: 20px;
            padding: 40px;
            margin: 30px 0;
        }
        .cta {
            background: linear-gradient(90deg, #4ecdc4, #44a08d);
            color: white;
            padding: 20px 40px;
            border-radius: 50px;
            font-size: 1.3rem;
            font-weight: bold;
            display: inline-block;
            margin-top: 30px;
        }
        .timeline {
            position: relative;
            padding-left: 40px;
        }
        .timeline::before {
            content: '';
            position: absolute;
            left: 10px;
            top: 0;
            bottom: 0;
            width: 4px;
            background: linear-gradient(180deg, #4ecdc4, #44a08d);
        }
        .timeline-item {
            position: relative;
            margin-bottom: 30px;
            padding-left: 30px;
        }
        .timeline-item::before {
            content: '';
            position: absolute;
            left: -36px;
            top: 5px;
            width: 16px;
            height: 16px;
            background: #4ecdc4;
            border-radius: 50%;
        }
        .timeline-date {
            color: #4ecdc4;
            font-weight: bold;
            font-size: 1.1rem;
        }
        .logo {
            font-size: 5rem;
            margin-bottom: 20px;
        }
        .footer-info {
            margin-top: auto;
            padding-top: 40px;
            text-align: center;
            color: rgba(255,255,255,0.6);
            font-size: 1rem;
        }
        @media print {
            .slide {
                page-break-after: always;
                height: 100vh;
            }
        }
    </style>
</head>
<body>

<!-- Slide 1: Title -->
<div class="slide title-slide">
    <div class="logo">🧬</div>
    <h1>BlissGene Therapeutics</h1>
    <p class="subtitle">Eliminating Human Suffering Through Precision Gene Therapy</p>
    <p style="margin-top: 60px; color: rgba(255,255,255,0.6);">
        Investor Presentation | December 2025<br>
        info@blissgene.org
    </p>
</div>

<!-- Slide 2: The Inspiration -->
<div class="slide">
    <h2>The Inspiration</h2>
    <div class="quote">
        "Imagine a life where you felt minimal pain, anxiety, or fear."
    </div>
    <div class="highlight-box">
        <h3>Jo Cameron - A Real Person with Extraordinary Genetics</h3>
        <div class="stats-grid">
            <div class="stat-box">
                <div class="big-stat">76</div>
                <div class="stat-label">Years Completely Pain-Free</div>
            </div>
            <div class="stat-box">
                <div class="big-stat">0</div>
                <div class="stat-label">Painkillers Ever Needed</div>
            </div>
            <div class="stat-box">
                <div class="big-stat">2x</div>
                <div class="stat-label">Normal Anandamide Levels</div>
            </div>
        </div>
        <p style="font-size: 1.2rem; text-align: center; margin-top: 20px;">
            Burns, broken bones, surgeries - all without anesthesia or distress.
        </p>
    </div>
</div>

<!-- Slide 3: The Problem -->
<div class="slide">
    <h2>The Problem: Massive Unmet Need</h2>
    <div class="stats-grid">
        <div class="stat-box">
            <div class="big-stat">50M+</div>
            <div class="stat-label">Americans with Chronic Pain</div>
        </div>
        <div class="stat-box">
            <div class="big-stat">40M</div>
            <div class="stat-label">Americans with Anxiety</div>
        </div>
        <div class="stat-box">
            <div class="big-stat">17.3M</div>
            <div class="stat-label">Major Depression Cases</div>
        </div>
    </div>
    <h3 style="margin-top: 40px;">Current Treatments Fail</h3>
    <ul>
        <li>Trial-and-error medication approaches</li>
        <li>Opioid crisis with addiction risk</li>
        <li>Significant side effects</li>
        <li>Limited efficacy for many patients</li>
        <li><strong>No treatments targeting root cause</strong></li>
    </ul>
    <div class="highlight-box" style="text-align: center; margin-top: 40px;">
        <div class="big-stat">$500B+</div>
        <div class="stat-label">US Chronic Pain Market Size</div>
    </div>
</div>

<!-- Slide 4: The Science -->
<div class="slide">
    <h2>The Science: 2023 UCL Breakthrough</h2>
    <h3>Published in Brain Journal</h3>
    <div class="two-column">
        <div>
            <h3>The Discovery</h3>
            <ul>
                <li><strong>FAAH</strong> enzyme breaks down endocannabinoids</li>
                <li><strong>FAAH-OUT</strong> is newly discovered lncRNA regulating FAAH</li>
                <li>Jo Cameron has <strong>8.1 kb microdeletion</strong></li>
                <li>Result: Reduced FAAH = Elevated Anandamide</li>
            </ul>
        </div>
        <div>
            <h3>Why FAAH-OUT?</h3>
            <ul>
                <li>Small molecule FAAH inhibitors <strong>failed trials</strong></li>
                <li>FAAH-OUT is <strong>human-validated</strong></li>
                <li>Affects <strong>1,145 genes</strong></li>
                <li>Includes WNT16 (healing) & BDNF (mood)</li>
            </ul>
        </div>
    </div>
    <div class="quote" style="margin-top: 40px;">
        "Given the current failure of small molecule inhibitors of FAAH as human analgesics, our findings validate FAAH-OUT regulation as a new route to develop pain treatments."
        <br><span style="font-size: 1rem; color: rgba(255,255,255,0.6);">- Mikaeili et al., Brain, 2023</span>
    </div>
</div>

<!-- Slide 5: Our Solution -->
<div class="slide">
    <h2>Our Solution: Targeted FAAH-OUT Knockdown</h2>
    <table>
        <tr>
            <th>Approach</th>
            <th>Mechanism</th>
            <th>Duration</th>
        </tr>
        <tr>
            <td><strong>siRNA Therapy</strong></td>
            <td>Temporary knockdown of FAAH-OUT expression</td>
            <td>Weeks to months (reversible)</td>
        </tr>
        <tr>
            <td><strong>CRISPR-Cas</strong></td>
            <td>Permanent deletion mimicking Jo Cameron's mutation</td>
            <td>Permanent</td>
        </tr>
    </table>
    <div class="highlight-box">
        <h3>Unique Advantage</h3>
        <p style="font-size: 1.3rem;">
            Patients can <strong>try temporary therapy first</strong> before committing to permanent CRISPR solution.
        </p>
        <p style="font-size: 1.1rem; color: rgba(255,255,255,0.7); margin-top: 15px;">
            Unprecedented patient choice in gene therapy!
        </p>
    </div>
    <h3 style="margin-top: 30px;">Delivery Strategy</h3>
    <ul>
        <li>Lipid Nanoparticle (LNP) delivery - proven technology (mRNA vaccines)</li>
        <li>Targeted delivery to specific brain regions</li>
    </ul>
</div>

<!-- Slide 6: Market Opportunity -->
<div class="slide">
    <h2>Market Opportunity</h2>
    <table>
        <tr>
            <th>Market</th>
            <th>Size</th>
            <th>Description</th>
        </tr>
        <tr>
            <td><strong>TAM</strong></td>
            <td style="color: #4ecdc4; font-size: 1.5rem;">$350B</td>
            <td>Chronic Pain + Anxiety + MDD (~67M patients)</td>
        </tr>
        <tr>
            <td><strong>SAM</strong></td>
            <td style="color: #4ecdc4; font-size: 1.5rem;">$250B</td>
            <td>Chronic Pain Only (50M patients)</td>
        </tr>
        <tr>
            <td><strong>SOM</strong></td>
            <td style="color: #4ecdc4; font-size: 1.5rem;">$50B</td>
            <td>Neuropathic Pain Subset (10M patients)</td>
        </tr>
    </table>
    <div class="highlight-box" style="margin-top: 40px;">
        <h3>Competitive Landscape</h3>
        <p style="font-size: 1.2rem;">
            <strong>No other company targets FAAH-OUT specifically</strong> with both temporary and permanent solutions.
        </p>
        <ul style="margin-top: 20px;">
            <li>Traditional pain management - addictive, side effects</li>
            <li>FAAH inhibitor drugs - failed in clinical trials</li>
            <li>RNA therapeutics companies - not targeting this pathway</li>
        </ul>
    </div>
</div>

<!-- Slide 7: Leadership Team -->
<div class="slide">
    <h2>Leadership Team</h2>
    <div class="two-column">
        <div>
            <h3>Executive Team</h3>
            <div style="margin: 20px 0; padding: 20px; background: rgba(255,255,255,0.05); border-radius: 10px;">
                <strong style="font-size: 1.3rem;">Brandon Emerick</strong><br>
                <span style="color: #4ecdc4;">CEO & Founder</span><br>
                <span style="color: rgba(255,255,255,0.7);">Cognitive Science & Business Administration</span>
            </div>
            <div style="margin: 20px 0; padding: 20px; background: rgba(255,255,255,0.05); border-radius: 10px;">
                <strong style="font-size: 1.3rem;">Qurrat Ain, PhD</strong><br>
                <span style="color: #4ecdc4;">COO</span><br>
                <span style="color: rgba(255,255,255,0.7);">Research Leadership & Operations</span>
            </div>
            <div style="margin: 20px 0; padding: 20px; background: rgba(255,255,255,0.05); border-radius: 10px;">
                <strong style="font-size: 1.3rem;">Valerio Embrione, PhD</strong><br>
                <span style="color: #4ecdc4;">VP & Chief Scientific Officer</span><br>
                <span style="color: rgba(255,255,255,0.7);">Scientific Strategy & Research Direction</span>
            </div>
        </div>
        <div>
            <h3>Scientific Advisory Board</h3>
            <ul style="font-size: 1.2rem; line-height: 2.5;">
                <li>Neena Pyzocha, PhD - Advisor</li>
                <li>Irfan Ullah, PhD - Advisor</li>
                <li>Zaki Ullah, PhD - Advisor</li>
                <li>Mayuri Bhattacharya - Marketing Consultant</li>
            </ul>
        </div>
    </div>
</div>

<!-- Slide 8: Development Roadmap -->
<div class="slide">
    <h2>Development Roadmap</h2>
    <div class="timeline" style="margin-top: 40px;">
        <div class="timeline-item">
            <div class="timeline-date">July 2024</div>
            <div>BlissGene Incorporated</div>
        </div>
        <div class="timeline-item">
            <div class="timeline-date">Q1 2025</div>
            <div>Secure Seed Funding</div>
        </div>
        <div class="timeline-item">
            <div class="timeline-date">Q3 2025</div>
            <div>Begin Preclinical Research</div>
        </div>
        <div class="timeline-item">
            <div class="timeline-date">Q3 2027</div>
            <div>Start IND-Enabling Studies</div>
        </div>
        <div class="timeline-item">
            <div class="timeline-date">Q3 2029</div>
            <div>IND Application</div>
        </div>
        <div class="timeline-item">
            <div class="timeline-date">Q3 2030</div>
            <div>Phase I Clinical Trials</div>
        </div>
    </div>
    <table style="margin-top: 40px;">
        <tr>
            <th>Phase</th>
            <th>Duration</th>
            <th>Activities</th>
        </tr>
        <tr>
            <td>Discovery & Preclinical</td>
            <td>2-3 years</td>
            <td>Target validation, siRNA/CRISPR optimization</td>
        </tr>
        <tr>
            <td>IND-Enabling</td>
            <td>1-2 years</td>
            <td>GLP toxicology, ADME studies, CMC development</td>
        </tr>
        <tr>
            <td>IND & Phase I Prep</td>
            <td>1-2 years</td>
            <td>FDA submission, site selection, trial planning</td>
        </tr>
    </table>
</div>

<!-- Slide 9: The Ask -->
<div class="slide">
    <h2>The Ask</h2>
    <div class="highlight-box" style="text-align: center;">
        <h3>Seed Round</h3>
        <div class="big-stat" style="font-size: 5rem;">$1,000,000</div>
    </div>
    <h3 style="margin-top: 40px;">Use of Funds</h3>
    <div class="stats-grid">
        <div class="stat-box">
            <div class="big-stat" style="font-size: 2.5rem;">40%</div>
            <div class="stat-label">Preclinical R&D</div>
        </div>
        <div class="stat-box">
            <div class="big-stat" style="font-size: 2.5rem;">25%</div>
            <div class="stat-label">Team Expansion</div>
        </div>
        <div class="stat-box">
            <div class="big-stat" style="font-size: 2.5rem;">15%</div>
            <div class="stat-label">Equipment & Lab</div>
        </div>
    </div>
    <div class="stats-grid" style="margin-top: 20px;">
        <div class="stat-box">
            <div class="big-stat" style="font-size: 2.5rem;">10%</div>
            <div class="stat-label">IP & Legal</div>
        </div>
        <div class="stat-box">
            <div class="big-stat" style="font-size: 2.5rem;">10%</div>
            <div class="stat-label">Operations</div>
        </div>
    </div>
    <div style="text-align: center; margin-top: 40px;">
        <h3>Exit Strategy</h3>
        <p style="font-size: 1.2rem;">
            Partnership or acquisition by major pharma during clinical trials<br>
            (Following Alnylam, Arrowhead RNA therapeutics playbook)
        </p>
    </div>
</div>

<!-- Slide 10: Why Now -->
<div class="slide">
    <h2>Why Now?</h2>
    <div class="two-column">
        <div>
            <h3>Scientific Timing</h3>
            <ul>
                <li><strong>2023 breakthrough</strong> - UCL published mechanism</li>
                <li>FAAH-OUT validated as target</li>
                <li>RNA/CRISPR delivery mature</li>
                <li>NHP models available</li>
            </ul>
        </div>
        <div>
            <h3>Market Timing</h3>
            <ul>
                <li>Opioid crisis creates urgent need</li>
                <li>RNA therapeutics gaining FDA acceptance</li>
                <li>No competitors targeting FAAH-OUT</li>
                <li>First-mover advantage available</li>
            </ul>
        </div>
    </div>
    <div class="highlight-box" style="margin-top: 50px;">
        <div class="quote" style="text-align: center; border: none; padding: 0;">
            "With an investment of just $1 million and a few minor changes to our genome, we can become a pain-free and happy species."
            <br><br>
            <span style="font-size: 1rem; color: #4ecdc4;">- Brandon Emerick, CEO</span>
        </div>
    </div>
</div>

<!-- Slide 11: Thank You -->
<div class="slide title-slide">
    <div class="logo">🧬</div>
    <h1>Join Us in Eliminating Human Suffering</h1>
    <div style="margin-top: 60px;">
        <p style="font-size: 1.5rem; margin: 10px 0;">🌐 blissgene.org</p>
        <p style="font-size: 1.5rem; margin: 10px 0;">📧 info@blissgene.org</p>
        <p style="font-size: 1.5rem; margin: 10px 0;">📱 860-483-1425</p>
    </div>
    <p class="footer-info" style="margin-top: 80px;">
        BlissGene Therapeutics | Incorporated July 19, 2024
    </p>
</div>

<!-- Slide 12: Appendix -->
<div class="slide">
    <h2>Appendix: Key Research References</h2>
    <div style="font-size: 1.1rem; line-height: 2;">
        <p><strong>1. Habib et al., 2019</strong></p>
        <p style="margin-left: 20px; color: rgba(255,255,255,0.7);">Original discovery of Jo Cameron case - British Journal of Anaesthesia</p>
        
        <p style="margin-top: 30px;"><strong>2. Mikaeili et al., 2023</strong></p>
        <p style="margin-left: 20px; color: rgba(255,255,255,0.7);">Molecular basis of FAAH-OUT - Brain, Volume 146, Issue 9</p>
        <p style="margin-left: 20px; color: #4ecdc4;">DOI: 10.1093/brain/awad098 | PMC10473560</p>
        
        <p style="margin-top: 30px;"><strong>UCL Study Key Findings:</strong></p>
        <ul style="margin-left: 40px; color: rgba(255,255,255,0.8);">
            <li>FAAH-OUT regulates FAAH via DNMT1-dependent DNA methylation</li>
            <li>797 genes upregulated, 348 downregulated</li>
            <li>WNT16 increased (wound healing)</li>
            <li>BDNF altered (mood elevation)</li>
            <li>ACKR3 modified (opioid regulation)</li>
        </ul>
    </div>
</div>

</body>
</html>
'''
    
    output_html = f"{OUTPUT_DIR}/BlissGene_Investor_Presentation.html"
    with open(output_html, 'w', encoding='utf-8') as f:
        f.write(slides_html)
    print(f"Created: {output_html}")
    
    css = CSS(string='''
        @page {
            size: 11in 8.5in landscape;
            margin: 0;
        }
        .slide {
            page-break-after: always;
            height: 8.5in;
            width: 11in;
            padding: 40px 60px;
        }
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
        }
    ''')
    
    output_pdf = f"{OUTPUT_DIR}/BlissGene_Investor_Presentation.pdf"
    HTML(string=slides_html).write_pdf(output_pdf, stylesheets=[css])
    print(f"Created: {output_pdf}")
    
    return output_pdf, output_html


if __name__ == "__main__":
    print("=" * 60)
    print("TI Materials Generator")
    print("=" * 60)
    print()
    
    print("1. Creating TI Essential Reading Bundle PDF...")
    bundle_pdf = create_article_bundle()
    print()
    
    print("2. Creating TI For Everyone Complete Book PDF...")
    book_pdf = create_ti_beginners_book()
    print()
    
    print("3. Creating BlissGene Investor Presentation...")
    pptx_pdf, pptx_html = create_blissgene_pptx_html()
    print()
    
    print("=" * 60)
    print("All materials created successfully!")
    print("=" * 60)
    print(f"\nOutput directory: {OUTPUT_DIR}/")
    print("\nFiles created:")
    print(f"  1. {bundle_pdf}")
    print(f"  2. {book_pdf}")
    print(f"  3. {pptx_pdf}")
    print(f"  4. {pptx_html}")
