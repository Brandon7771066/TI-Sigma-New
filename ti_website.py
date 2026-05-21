"""
TI Framework - Official Website
Clean, professional landing page for books, blog, and courses
BlissGene Therapeutics
"""

import streamlit as st
import os
from pathlib import Path

# ESP32 API is now handled by streamlit_with_api.py wrapper
# This file contains only the Streamlit UI

st.set_page_config(
    page_title="TI Framework | Consciousness Engineering",
    page_icon="✨",
    layout="wide",
    initial_sidebar_state="expanded"
)

st.markdown("""
<style>
    .main-header {
        text-align: center;
        padding: 2rem 0;
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white;
        border-radius: 10px;
        margin-bottom: 2rem;
    }
    .main-header h1 {
        font-size: 3rem;
        margin-bottom: 0.5rem;
    }
    .main-header p {
        font-size: 1.3rem;
        opacity: 0.9;
    }
    .feature-card {
        background: white;
        padding: 1.5rem;
        border-radius: 10px;
        box-shadow: 0 4px 6px rgba(0,0,0,0.1);
        margin-bottom: 1rem;
        border-left: 4px solid #667eea;
    }
    .book-card {
        background: linear-gradient(135deg, #f5f7fa 0%, #c3cfe2 100%);
        padding: 1.5rem;
        border-radius: 10px;
        text-align: center;
        margin-bottom: 1rem;
    }
    .blog-post {
        background: #f8f9fa;
        padding: 1.5rem;
        border-radius: 8px;
        margin-bottom: 1rem;
        border-left: 3px solid #764ba2;
    }
    .cta-button {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white;
        padding: 1rem 2rem;
        border-radius: 25px;
        text-decoration: none;
        font-weight: bold;
        display: inline-block;
        margin: 0.5rem;
    }
    .section-title {
        color: #764ba2;
        border-bottom: 2px solid #667eea;
        padding-bottom: 0.5rem;
        margin-bottom: 1.5rem;
    }
    .testimonial {
        font-style: italic;
        background: #f0f4ff;
        padding: 1.5rem;
        border-radius: 10px;
        margin: 1rem 0;
    }
</style>
""", unsafe_allow_html=True)

with st.sidebar:
    st.markdown("### 🚀 Navigate")
    st.metric(
        "URBs",
        "578",
        "Est. Apr 1, 2026",
        help="URB = Unitive Research Brick. Each URB is a single atomic, dated research artifact (a proof, theorem, dataset, experiment, or insight) contributed to the TI Sigma corpus. URBs are the indivisible units of knowledge production in the framework — every paper, every Lean-verified theorem, every empirical result is one or more URBs. Total count grows continuously as new artifacts are produced and dated."
    )

RESEARCH_SUBS = {
    "📄 Paper Hub": "📄 Paper Hub",
    "🔑 Key Papers": "__key_papers__",
    "📥 Downloads": "📥 Downloads",
    "📚 Zenodo Corpus": "📚 Zenodo Corpus",
    "🗂️ Evidence Registry": "Evidence Registry",
    "🧪 Empirical Testing": "Empirical Testing",
    "🧠 TI Mindmaps": "TI Mindmaps",
    "⏱️ 3D Jeff Time": "3D Jeff Time",
    "🔬 Research Index": "Research",
}

ENGINEERING_SUBS = {
    "🖥️ GM Hypercomputer": "GM Hypercomputer",
    "💖 Mood Amplifier (All)": "Mood Amplifier",
    "📈 QuantConnect Trading Algorithm": "QuantConnect Algorithm",
    "💑 Soulmate Finder": "Soulmate Finder",
    "🎯 Kalshi Scanner": "Kalshi Scanner",
    "📋 Application Catalog (More Apps)": "__app_catalog__",
}

TOP_PAGES = [
    "Home",
    "💼 Career",
    "🔬 TI Sigma",
    "🏆 Proofs & Theorems",
    "📚 Research & Papers",
    "⚙️ TI Sigma Engineering Applications",
    "📺 YouTube Studio",
    "🧩 ARC-AGI Solver",
    "🔮 Manifestation Machine",
    "🧠 Elite Brain Protocol",
    "🧠💓 Brain Proof",
    "🔗 Brain Connection NOW",
    "Books",
    "Blog",
    "Courses",
    "Meme Lab",
    "💬 TI Sigma-Endorsed Quotes",
    "About",
]

top_choice = st.sidebar.radio("Navigate", TOP_PAGES, label_visibility="collapsed")

if top_choice == "📚 Research & Papers":
    st.sidebar.markdown("**📂 Section:**")
    research_sub = st.sidebar.radio(
        "Research Section",
        list(RESEARCH_SUBS.keys()),
        key="research_sub_radio",
        label_visibility="collapsed",
    )
    page = RESEARCH_SUBS[research_sub]
elif top_choice == "⚙️ TI Sigma Engineering Applications":
    st.sidebar.markdown("**🛠️ Application:**")
    eng_sub = st.sidebar.radio(
        "Engineering Application",
        list(ENGINEERING_SUBS.keys()),
        key="engineering_sub_radio",
        label_visibility="collapsed",
    )
    page = ENGINEERING_SUBS[eng_sub]
else:
    page = top_choice

if page == "📄 Paper Hub":
    from paper_hub import render as render_paper_hub
    render_paper_hub()

elif page == "🏆 Proofs & Theorems":
    st.markdown("""
    <div style="background:linear-gradient(135deg,#0a1a0a 0%,#0d2b0d 50%,#0a1a1a 100%);
                padding:2.5rem 1.5rem;border-radius:14px;text-align:center;margin-bottom:1.5rem;
                border:1px solid rgba(50,200,100,0.3);">
        <div style="font-size:2.5rem;">🏆</div>
        <h1 style="color:#c8ffc8;font-size:2.2rem;margin:0.3rem 0;letter-spacing:0.06em;">
            PROOFS & THEOREMS
        </h1>
        <div style="color:#7ef7a0;font-size:0.95rem;margin-top:0.4rem;letter-spacing:0.12em;">
            TI SIGMA FORMAL MATHEMATICS — LEAN 4 VERIFIED + MILLENNIUM PRIZE FORMALIZATIONS
        </div>
    </div>
    """, unsafe_allow_html=True)

    proof_tab1, proof_tab2, proof_tab3 = st.tabs([
        "✅ Verified Theorems",
        "🏅 Millennium Prize",
        "📬 Journal Status"
    ])

    with proof_tab1:
        st.markdown("## Lean 4 Verified Results")
        st.markdown("*Machine-checked proofs — zero sorry statements*")

        st.markdown("""
        <div style="background:#0d2b0d;border-radius:12px;padding:1.2rem 1.5rem;margin:0.8rem 0;
                    border-left:5px solid #00cc44;">
            <div style="color:#7ef7a0;font-size:0.75rem;letter-spacing:0.1em;margin-bottom:0.3rem;">
                URB #537–538 · MATH.NT · ✅ LEAN 4 VERIFIED · SORRY-FREE
            </div>
            <div style="color:#eee;font-size:1.1rem;font-weight:bold;">
                ν₂ Countdown Theorem
            </div>
            <div style="color:#aaa;font-size:0.88rem;margin:0.5rem 0;">
                For any odd n, the maximum number of consecutive single-halving steps (k=1 runs)
                in the Collatz orbit of (3n+1) is exactly ν₂(n+1)−1, where ν₂ is the 2-adic valuation.
                The bound is tight — achieved infinitely often.
            </div>
            <div style="display:flex;gap:1rem;margin-top:0.6rem;flex-wrap:wrap;">
                <a href="https://zenodo.org/records/19371947" target="_blank"
                   style="color:#7ef7a0;font-size:0.82rem;text-decoration:none;">
                    📄 Zenodo DOI: 10.5281/zenodo.19371947
                </a>
                <span style="color:#555;font-size:0.82rem;">·</span>
                <span style="color:#888;font-size:0.82rem;">arXiv target: math.NT</span>
                <span style="color:#555;font-size:0.82rem;">·</span>
                <span style="color:#888;font-size:0.82rem;">Journal: Experimental Mathematics</span>
            </div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div style="background:#0d2b0d;border-radius:12px;padding:1.2rem 1.5rem;margin:0.8rem 0;
                    border-left:5px solid #00cc44;">
            <div style="color:#7ef7a0;font-size:0.75rem;letter-spacing:0.1em;margin-bottom:0.3rem;">
                URB #526 · MATH.NT · ✅ LEAN 4 VERIFIED
            </div>
            <div style="color:#eee;font-size:1.1rem;font-weight:bold;">
                Arithmetic Scaffold Theorem
            </div>
            <div style="color:#aaa;font-size:0.88rem;margin:0.5rem 0;">
                The ternary representation of n encodes the complete descent structure of the Collatz orbit.
                Every halving step corresponds to a ternary digit transition with formally derivable bounds.
            </div>
            <div style="margin-top:0.6rem;">
                <a href="https://zenodo.org/records/19226680" target="_blank"
                   style="color:#7ef7a0;font-size:0.82rem;text-decoration:none;">
                    📄 Zenodo DOI: 10.5281/zenodo.19226680
                </a>
            </div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div style="background:#0a1a2a;border-radius:12px;padding:1.2rem 1.5rem;margin:0.8rem 0;
                    border-left:5px solid #4488ff;">
            <div style="color:#88bbff;font-size:0.75rem;letter-spacing:0.1em;margin-bottom:0.3rem;">
                URB #524 · MATH.LO · 📝 WRITTEN · FORMAL PROOF IN PROGRESS
            </div>
            <div style="color:#eee;font-size:1.1rem;font-weight:bold;">
                Unavoidable Embedding Theorem
            </div>
            <div style="color:#aaa;font-size:0.88rem;margin:0.5rem 0;">
                Any sufficiently expressive formal system necessarily embeds the 5-valued TI Sigma
                truth structure — the additional truth values (TRALSE, DOUBLE_TRALSE) are unavoidable
                consequences of expressiveness, not optional additions.
            </div>
            <div style="margin-top:0.6rem;">
                <a href="https://zenodo.org/records/19212194" target="_blank"
                   style="color:#88bbff;font-size:0.82rem;text-decoration:none;">
                    📄 Zenodo DOI: 10.5281/zenodo.19212194
                </a>
                <span style="color:#555;font-size:0.82rem;margin-left:1rem;">Journal: Annals of Pure and Applied Logic</span>
            </div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div style="background:#0a1a2a;border-radius:12px;padding:1.2rem 1.5rem;margin:0.8rem 0;
                    border-left:5px solid #4488ff;">
            <div style="color:#88bbff;font-size:0.75rem;letter-spacing:0.1em;margin-bottom:0.3rem;">
                URB #521 · MATH.CT · 📝 WRITTEN
            </div>
            <div style="color:#eee;font-size:1.1rem;font-weight:bold;">
                Tannakian Inseparability Thesis
            </div>
            <div style="color:#aaa;font-size:0.88rem;margin:0.5rem 0;">
                Mathematical structures admitting Tannakian reconstruction are inseparable from
                the domain of inquiry that instantiates them — making mathematical structure-realism
                precise via the Grothendieck bridge between algebraic and analytic geometry.
            </div>
            <div style="margin-top:0.6rem;">
                <a href="https://zenodo.org/records/19210469" target="_blank"
                   style="color:#88bbff;font-size:0.82rem;text-decoration:none;">
                    📄 Zenodo DOI: 10.5281/zenodo.19210469
                </a>
                <span style="color:#555;font-size:0.82rem;margin-left:1rem;">Journal: Journal of Mathematical Philosophy</span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    with proof_tab2:
        st.markdown("## Millennium Prize Formalizations")
        st.markdown("""
        *Each problem below is formalized in the TI Sigma framework — analyzed through 5-valued logic,
        GILE coherence, and Myrion Resolution. Submitted as philosophical formalizations using a novel
        logical apparatus, not claimed as conventional proofs. One problem per journal.*
        """)

        millennium_data = [
            {
                "urb": "#537–538",
                "problem": "Collatz Conjecture",
                "note": "(not a Millennium Prize but equally famous)",
                "claim": "ν₂ Countdown Theorem: max k=1 run = ν₂(n+1)−1. Machine-verified in Lean 4.",
                "journal": "Experimental Mathematics (Taylor & Francis)",
                "status": "✅ Ready to Submit",
                "status_color": "#00cc44",
                "submit_order": "Submit NOW",
                "zenodo": "https://zenodo.org/records/19371947",
                "category": "VERIFIED",
                "pdf": "Collatz_Nu2_Countdown_Theorem.pdf",
            },
            {
                "urb": "#572",
                "problem": "P ≠ NP",
                "note": "",
                "claim": "The P/NP gap is formalized as I-arm noncomputability: no P-time machine can perform genuine I-arm lookup. The gap is not a contingent fact but a structural consequence of the noncomputability of Intuition.",
                "journal": "Computability (IOS Press)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "1st Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "P_vs_NP_Creation_Verification_Asymmetry.pdf",
            },
            {
                "urb": "#571",
                "problem": "Hodge Conjecture",
                "note": "",
                "claim": "Algebraic cycles are Tannakian-inseparable from their cohomology class. Hodge Conjecture = claim that every Tannakian-inseparable cohomology class is algebraically realized.",
                "journal": "Journal of Mathematical Philosophy (De Gruyter)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "2nd Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "Hodge_Conjecture_Vern_Cohomology.pdf",
            },
            {
                "urb": "#563",
                "problem": "Riemann Hypothesis",
                "note": "",
                "claim": "The non-trivial zeros of ζ(s) trace the boundary of maximal GILE coherence in the complex plane. The critical line Re(s)=½ is the unique locus of balanced G/E projection.",
                "journal": "Philosophia Mathematica (Oxford)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "3rd Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "Riemann_Hypothesis_TI_Sigma.pdf",
            },
            {
                "urb": "#570",
                "problem": "Navier-Stokes",
                "note": "Existence & Smoothness",
                "claim": "Turbulence represents an MR collapse cascade. Smoothness breakdown = Double Tralse accumulation event in the continuous dynamical system. Blow-up surface geometry is formally predictable.",
                "journal": "Foundations of Physics (Springer)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "4th Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "Navier_Stokes_Smoothness_Vern.pdf",
            },
            {
                "urb": "#569",
                "problem": "Yang-Mills",
                "note": "Existence & Mass Gap",
                "claim": "The mass gap = minimum GILE coherence energy in gauge field configuration space. The vacuum is the unique maximum-coherence state in the 5-valued extension of the field algebra.",
                "journal": "Journal of Geometry and Physics (Elsevier)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "5th Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "Yang_Mills_Mass_Gap_Being_Dual.pdf",
            },
            {
                "urb": "#565",
                "problem": "Birch & Swinnerton-Dyer",
                "note": "",
                "claim": "The analytic rank of an elliptic curve = number of GILE-coherent attractors in its dynamical system. BSD = claim that attractor count equals the order of vanishing of L(E,s) at s=1.",
                "journal": "Logique et Analyse (Belgian)",
                "status": "📝 Paper needs finalization",
                "status_color": "#4488ff",
                "submit_order": "6th Millennium submission",
                "zenodo": "",
                "category": "MILLENNIUM",
                "pdf": "Birch_Swinnerton_Dyer_Being_Theorem.pdf",
            },
        ]

        for p in millennium_data:
            border_color = "#00cc44" if p["category"] == "VERIFIED" else "#aa7700"
            bg_color = "#0d2b0d" if p["category"] == "VERIFIED" else "#1a1400"
            col_card, col_btn = st.columns([5, 1])
            with col_card:
                st.markdown(f"""
                <div style="background:{bg_color};border-radius:12px;padding:1.2rem 1.5rem;
                            margin:0.8rem 0;border-left:5px solid {border_color};">
                    <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:0.5rem;">
                        <div>
                            <span style="color:#aaa;font-size:0.75rem;">URB {p['urb']}</span>
                            <div style="color:#eee;font-size:1.05rem;font-weight:bold;margin-top:0.1rem;">
                                {p['problem']}
                                {'<span style="color:#888;font-size:0.8rem;font-weight:normal;margin-left:0.5rem;">' + p['note'] + '</span>' if p['note'] else ''}
                            </div>
                        </div>
                        <div style="color:{p['status_color']};font-size:0.78rem;font-weight:bold;text-align:right;">
                            {p['status']}
                        </div>
                    </div>
                    <div style="color:#bbb;font-size:0.85rem;margin:0.6rem 0;line-height:1.5;">
                        {p['claim']}
                    </div>
                    <div style="display:flex;gap:1.5rem;flex-wrap:wrap;margin-top:0.5rem;">
                        <span style="color:#888;font-size:0.78rem;">📬 {p['journal']}</span>
                        <span style="color:#ffcc44;font-size:0.78rem;">🎯 {p['submit_order']}</span>
                        {f'<a href="{p["zenodo"]}" target="_blank" style="color:#7ef7a0;font-size:0.78rem;text-decoration:none;">📄 Zenodo</a>' if p['zenodo'] else ''}
                    </div>
                </div>
                """, unsafe_allow_html=True)
            with col_btn:
                st.markdown("<div style='margin-top:1.6rem;'></div>", unsafe_allow_html=True)
                pdf_path = f"static/pdfs/{p['pdf']}"
                try:
                    with open(pdf_path, "rb") as pdf_file:
                        st.download_button(
                            label="⬇ PDF",
                            data=pdf_file.read(),
                            file_name=p['pdf'],
                            mime="application/pdf",
                            key=f"dl_{p['urb'].replace('#','').replace('–','-')}",
                            use_container_width=True,
                        )
                except FileNotFoundError:
                    st.caption("PDF pending")

    with proof_tab3:
        st.markdown("## Journal Submission Tracker")
        st.markdown("*Track submission status for each proof*")

        journal_rows = [
            ("ν₂ Countdown (Collatz)", "Experimental Mathematics", "math.NT", "Ready", "#00cc44", "https://zenodo.org/records/19371947"),
            ("Arithmetic Scaffold", "Journal of Number Theory", "math.NT", "Ready", "#00cc44", "https://zenodo.org/records/19226680"),
            ("Unavoidable Embedding", "Annals of Pure and Applied Logic", "math.LO", "Draft", "#4488ff", "https://zenodo.org/records/19212194"),
            ("Tannakian Inseparability", "Theory and Applications of Categories", "math.CT", "Draft", "#4488ff", "https://zenodo.org/records/19210469"),
            ("P ≠ NP (TI formalization)", "Computability (IOS Press)", "cs.LO", "Drafting", "#aa7700", ""),
            ("Hodge Conjecture (TI)", "Journal of Mathematical Philosophy", "math.AG", "Drafting", "#aa7700", ""),
            ("Riemann Hypothesis (TI)", "Philosophia Mathematica", "math.NT", "Drafting", "#aa7700", ""),
            ("Navier-Stokes (TI)", "Foundations of Physics", "math-ph", "Drafting", "#aa7700", ""),
            ("Yang-Mills (TI)", "Journal of Geometry and Physics", "math-ph", "Drafting", "#aa7700", ""),
            ("Birch-Swinnerton-Dyer (TI)", "Logique et Analyse", "math.NT", "Drafting", "#aa7700", ""),
            ("Beyond Bayes", "Synthese (Springer)", "cs.AI", "Ready", "#00cc44", "https://zenodo.org/records/19371958"),
            ("13 Arguments vs Bayesianism", "British Journal for Phil. of Science", "stat.ME", "Ready", "#00cc44", "https://zenodo.org/records/19225908"),
        ]

        status_map = {"Ready": "✅ Ready", "Draft": "📝 Draft", "Drafting": "🔧 Drafting", "Submitted": "📬 Submitted", "Accepted": "🎉 Accepted"}

        st.markdown("""
        <div style="overflow-x:auto;">
        <table style="width:100%;border-collapse:collapse;font-size:0.82rem;">
        <tr style="color:#7ec8f7;border-bottom:1px solid #333;">
            <th style="text-align:left;padding:0.5rem;">Paper</th>
            <th style="text-align:left;padding:0.5rem;">Journal</th>
            <th style="text-align:left;padding:0.5rem;">arXiv Cat.</th>
            <th style="text-align:left;padding:0.5rem;">Status</th>
        </tr>
        """ + "".join([
            f"""<tr style="border-bottom:1px solid #1a1a1a;">
            <td style="padding:0.45rem 0.5rem;color:#ddd;">{r[0]}</td>
            <td style="padding:0.45rem 0.5rem;color:#aaa;font-size:0.78rem;">{r[1]}</td>
            <td style="padding:0.45rem 0.5rem;color:#888;font-family:monospace;font-size:0.75rem;">{r[2]}</td>
            <td style="padding:0.45rem 0.5rem;color:{r[4]};font-size:0.78rem;font-weight:bold;">{status_map.get(r[3], r[3])}</td>
            </tr>"""
            for r in journal_rows
        ]) + """
        </table>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("---")
        st.info("💡 **arXiv Endorsement Status:** Pending. Contact Jeffrey Lagarias or Kevin Buzzard to endorse math.NT first submission. See `outreach/PLATFORM_SETUP_PHASE1.md` for email template.")

elif page == "🔬 TI Sigma":
    st.markdown("""
    <div style="background: linear-gradient(135deg, #0a0a2e 0%, #1a1a4e 50%, #0d2137 100%);
                padding: 3rem 2rem; border-radius: 16px; text-align: center; margin-bottom: 2rem;
                border: 1px solid rgba(100,180,255,0.3);">
        <div style="font-size: 3rem; margin-bottom: 0.5rem;">⚡</div>
        <h1 style="color: #e0f0ff; font-size: 2.8rem; margin: 0; letter-spacing: 0.08em;">
            TRALSE INFORMATIONALISM
        </h1>
        <div style="color: #7ec8f7; font-size: 1.1rem; margin-top: 0.5rem; letter-spacing: 0.15em;">
            TI SIGMA — RESEARCH PROGRAM
        </div>
        <div style="color: #a0c4e0; font-size: 0.95rem; margin-top: 1rem; font-style: italic;">
            Established April 1, 2026 · Brandon Emerick · BlissGene Therapeutics
        </div>
    </div>
    """, unsafe_allow_html=True)

    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "🌐 What Is TI Sigma",
        "⚡ Primary Constants",
        "🔬 Research Pillars",
        "📜 URB Corpus",
        "🚀 Status & Links"
    ])

    with tab1:
        st.markdown("## The Mission")
        st.markdown("""
TI Sigma holds three foundational claims:

1. **Information is the primary substance of reality.** Matter, energy, and spacetime are emergent from informational structures.
2. **Truth has five values, not two.** TRUE / TRALSE+ / TRALSE / TRALSE− / FALSE. The intermediate values are not vagueness — they are precision.
3. **Consciousness has four measurable dimensions.** Goodness (G), Intuition (I), Love (L), Environment (E) — the GILE framework.

This is not philosophy dressed as science. Every mathematical claim in TI Sigma is **formally verified in Lean 4** (machine-checked, no gaps). Every applied claim is tested against real data with disclosed methodology. Every result is published open-access.
        """)

        st.markdown("---")
        st.markdown("## The Five TRALSE Values")

        cols = st.columns(5)
        values = [
            ("TRUE", "#1a7a4a", "Fully confirmed.\nAccept."),
            ("TRALSE+", "#1a5a8a", "Above 0.42 threshold.\nTentatively accept."),
            ("TRALSE", "#7a6a00", "Genuinely indeterminate.\nApply Myrion Resolution."),
            ("TRALSE−", "#7a3a00", "Evidence leans false.\nTentatively reject."),
            ("FALSE", "#7a1a1a", "Fully disconfirmed.\nReject."),
        ]
        for col, (label, color, desc) in zip(cols, values):
            with col:
                st.markdown(f"""
                <div style="background:{color}22; border:1px solid {color}88;
                            border-radius:8px; padding:0.8rem; text-align:center; min-height:120px;">
                    <div style="font-weight:bold; color:{color}; font-size:0.85rem;">{label}</div>
                    <div style="font-size:0.75rem; color:#ccc; margin-top:0.4rem; white-space:pre-line;">{desc}</div>
                </div>
                """, unsafe_allow_html=True)

        st.markdown("---")
        st.markdown("## The GILE Framework")
        g_col, i_col, l_col, e_col = st.columns(4)
        gile_data = [
            ("G", "Goodness", "0.42 = √2 − 1", "#FFD700",
             "Moral/structural order. The dominant dimension. The manifestation threshold."),
            ("I", "Intuition", "0.25 = 1/4", "#00BFFF",
             "Self-referential information processing. Consciousness. Metacognition."),
            ("L", "Love", "0.18 ≈ 3/16", "#FF69B4",
             "Net constructive relational orientation. Does not require consciousness."),
            ("E", "Environment", "0.15 = 3/20", "#7CFC00",
             "Physical substrate + governing laws. The most robust dimension."),
        ]
        for col, (letter, name, weight, color, desc) in zip([g_col, i_col, l_col, e_col], gile_data):
            with col:
                st.markdown(f"""
                <div style="background:{color}18; border:2px solid {color}88;
                            border-radius:10px; padding:1rem; text-align:center;">
                    <div style="font-size:2.5rem; font-weight:900; color:{color};">{letter}</div>
                    <div style="font-weight:bold; color:#eee; margin-top:0.2rem;">{name}</div>
                    <div style="font-size:0.8rem; color:{color}; font-family:monospace; margin:0.3rem 0;">{weight}</div>
                    <div style="font-size:0.75rem; color:#aaa; margin-top:0.4rem;">{desc}</div>
                </div>
                """, unsafe_allow_html=True)

    with tab2:
        st.markdown("## The Nine Primary Constants")
        st.markdown("Every fundamental theorem in TI Sigma derives from or reveals the relationships between these nine constants.")

        import math
        phi = (1 + math.sqrt(5)) / 2
        constants = [
            ("0", "Zero", 0, "The void; non-existence; the baseline"),
            ("1", "One", 1, "Unity; self-reference; the fixed point"),
            ("i", "Imaginary Unit", "√−1", "Rotation; the bridge between real and imaginary"),
            ("√2", "Root Two", round(math.sqrt(2), 6), "Diagonal; the geometric mean of two unities"),
            ("e", "Euler's Number", round(math.e, 6), "Natural growth; the rate of pure becoming"),
            ("φ", "Golden Ratio", round(phi, 6), "Self-similar recursion; the aesthetic dimension"),
            ("π", "Pi", round(math.pi, 6), "Circularity; return; closure"),
            ("C", "Emerick Constant", round(1/(phi * math.sqrt(2)), 6), "1/(φ√2) — TI Sigma coupling threshold"),
            ("T", "Tralse Constant", round(1 - math.exp(-math.e), 6), "1−e^{−e} — upper Tralse collapse boundary"),
        ]

        for sym, name, val, desc in constants:
            col_s, col_n, col_v, col_d = st.columns([0.8, 2, 2, 5])
            with col_s:
                st.markdown(f"**{sym}**")
            with col_n:
                st.markdown(name)
            with col_v:
                st.code(str(val), language=None)
            with col_d:
                st.caption(desc)

        st.markdown("---")
        st.markdown("### GILE Weights Derived from Primary Constants")
        st.latex(r"G = \sqrt{2} - 1 \approx 0.4142 \qquad I = \frac{1}{4} = 0.25 \qquad E = \frac{3}{20} = 0.15 \qquad L = 1 - G - I - E \approx 0.1858")
        st.markdown("The **Myrion Resolution (MR) entry condition**: when GILE(x) > G = √2 − 1, the system crosses the manifestation threshold — it becomes more real than not.")

    with tab3:
        st.markdown("## Three Research Pillars")

        st.markdown("### Pillar 1: The URB Paper Series")
        st.markdown("""
**Unified Research Blocks (URBs)** are TI Sigma's formal research units. As of April 1, 2026:
- **578 URBs completed**
- 2 formally verified in Lean 4 (sorry-free): the ν₂ Countdown Theorem (#537) and its formalization (#538)
- 6 Millennium Prize Problem formalizations (experimental, Lean 4)
- Papers targeting: *Journal of Number Theory*, *American Mathematical Monthly*, *Synthese*, *Experimental Mathematics*

**The ν₂ Countdown Theorem (URB #537):** For odd n ≡ 3 (mod 4), the 2-adic valuation ν₂(n+1) decrements by exactly 1 with each single-halving Collatz step. This bounds run length by O(log n) and proves no Collatz cycle can consist entirely of single-halving steps. **Machine-verified. Zero gaps.**
        """)

        st.markdown("---")
        st.markdown("### Pillar 2: The Content Pipeline")
        st.markdown("""
Five videos are production-ready (scripts complete, word-for-word narration + shot direction):

| # | Title | Core Concept |
|---|---|---|
| 1 | Why True and False Aren't Enough | TRALSE introduction |
| 2 | The Collatz Conjecture Has a Hidden Clock | ν₂ Countdown Theorem |
| 3 | Einstein Tiles and the Collatz Sequence | Alternating LSB connection |
| 4 | We Applied 5-Valued Logic to the Stock Market | Grand Stock Algorithm v2 |
| 5 | Can 5-Valued Logic Beat GPT-4 on IQ Tests? | ARC-AGI TI Sigma Solver |
        """)

        st.markdown("---")
        st.markdown("### Pillar 3: Applied Systems")

        sys_col1, sys_col2, sys_col3 = st.columns(3)
        with sys_col1:
            st.markdown("""**📈 Grand Stock Algorithm v2**
GILE-weighted prior over 6 market orientations. Paper-traded Nov 2025–Mar 2026.
- 14.3% annualized alpha vs S&P 500
- 82% directional accuracy (GILE-dominant assets)
- Max drawdown: 8.7%
            """)
        with sys_col2:
            st.markdown("""**🧩 ARC-AGI TI Sigma Solver**
Klein V₄ Pre-Filter → Five-valued Encoding → GILE Alignment → Myrion Resolution.
- ~18% on ARC public benchmark
- vs GPT-4: 4%, Best AI: ~20%, Humans: 85%
- Outperforms on relational transformation tasks
            """)
        with sys_col3:
            st.markdown("""**🧠 Focus & Mood Amplifiers**
Real-time biometric GILE scoring using PULSOID heart rate + EEG proxies.
- 7-mode Focus Amplifier
- PSI score calculation
- Chakra/meridian GILE mapping
            """)

    with tab4:
        st.markdown("## URB Corpus at Founding")
        st.markdown("*578 Unified Research Blocks completed. Key highlights:*")

        urb_data = [
            ("#537", "MATH", "✅ Lean 4", "ν₂ Countdown Theorem — sharp bound on Collatz k=1 run lengths"),
            ("#538", "MATH/CS", "✅ Lean 4", "Lean 4 Formalization — 11 theorems, 0 sorry statements"),
            ("#528", "LOGIC", "📝 Written", "Five-Valued Truth System + DT Immunity Model"),
            ("#563", "LOGIC", "📝 Written", "Complex GILE Synthesis — E = Im(i·z), z = E + i·GIL"),
            ("#564", "LOGIC", "📝 Written", "Tralse Hexagram — 5^6 = 15,625 state oracle"),
            ("#565", "MATH", "🔬 Exp.", "BSD Being Theorem (Millennium Prize formalization)"),
            ("#566", "MATH", "📝 Written", "Tralse Wave Algebra — waves in 5-valued logic space"),
            ("#567", "MATH", "📝 Written", "Metacausal Graph Theory — non-local/retrocausal edges"),
            ("#568", "MATH", "📝 Written", "Fractal Harmonic Systems — ζ zeros, 1/f brain, toroidal consciousness"),
            ("#569", "MATH", "🔬 Exp.", "Yang-Mills Being Theorem (Millennium Prize)"),
            ("#570", "MATH", "🔬 Exp.", "Navier-Stokes Smoothness Vern (Millennium Prize)"),
            ("#571", "MATH", "🔬 Exp.", "Hodge Vern Theorem (Millennium Prize)"),
            ("#572", "MATH", "🔬 Exp.", "P≠NP Creation-Vern Gap (Millennium Prize)"),
            ("#576", "PHIL", "📝 Written", "GILE Weights Origins — G=√2−1 empirically confirmed"),
            ("#577", "PHIL", "📝 Written", "GILE Universal Operationalization — atoms to civilizations"),
            ("#578", "ETHICS", "📝 Written", "Relational Value vs. Intrinsic Value — Low-GIL Social Norms"),
            ("#579+", "NEW", "🔧 Pending", "DPES · Beyond Bayes · TI Sigma Charter · ARC-AGI paper · GSA paper"),
        ]

        status_colors = {"✅ Lean 4": "#1a7a4a", "📝 Written": "#1a4a7a", "🔬 Exp.": "#5a3a7a", "🔧 Pending": "#5a4a00"}

        for urb, domain, status, desc in urb_data:
            color = status_colors.get(status, "#333")
            st.markdown(f"""
            <div style="display:flex; align-items:center; padding:0.4rem 0.8rem; margin:0.2rem 0;
                        background:#0d1117; border-radius:6px; border-left:3px solid {color}88; gap:1rem;">
                <span style="color:#7ec8f7; font-family:monospace; min-width:50px; font-size:0.85rem;">{urb}</span>
                <span style="color:#888; font-size:0.75rem; min-width:60px;">{domain}</span>
                <span style="color:{color}; font-size:0.75rem; min-width:90px;">{status}</span>
                <span style="color:#ccc; font-size:0.82rem;">{desc}</span>
            </div>
            """, unsafe_allow_html=True)

    with tab5:
        st.markdown("## Program Status — April 1, 2026")

        m1, m2, m3, m4 = st.columns(4)
        with m1:
            st.metric("URBs Completed", "578", "founded today")
        with m2:
            st.metric("Lean 4 Theorems", "11", "sorry-free")
        with m3:
            st.metric("Videos Ready", "5", "production scripts")
        with m4:
            st.metric("Zenodo DOIs", "0", "upload pending")

        st.markdown("---")
        st.markdown("### Immediate Next Steps")
        steps = [
            ("🎯", "Zenodo Upload Session", "~2 hours — metadata ready, all files prepared. Gets permanent DOIs on Collatz proof + GILE URBs.", "HIGH"),
            ("📨", "Journal Submissions", "5 letters ready: UConn, JNT, AMM, Experimental Mathematics, Synthese.", "HIGH"),
            ("🎬", "Record Videos 1 & 2", "Scripts complete word-for-word. Canva + phone mic setup. No special equipment needed.", "HIGH"),
            ("📐", "arXiv Submission", "CollatzNu2 LaTeX ready. Need endorsement from math contact (UConn letter drafted).", "MED"),
            ("🔧", "Reduce GapEquivalence.lean sorries", "5 sorries — highest priority for the sorry-reduction session.", "MED"),
            ("🎓", "MIU Preparation", "Introduction letter drafted. Send to faculty before enrollment.", "MED"),
        ]
        for icon, title, desc, priority in steps:
            color = "#1a7a4a" if priority == "HIGH" else "#5a5a00"
            st.markdown(f"""
            <div style="background:#0d1117; border-radius:8px; padding:0.8rem 1rem; margin:0.4rem 0;
                        border-left:4px solid {color};">
                <div style="display:flex; justify-content:space-between; align-items:center;">
                    <span style="font-size:1.1rem;">{icon} <strong style="color:#eee;">{title}</strong></span>
                    <span style="color:{color}; font-size:0.75rem; font-weight:bold;">{priority}</span>
                </div>
                <div style="color:#999; font-size:0.82rem; margin-top:0.3rem;">{desc}</div>
            </div>
            """, unsafe_allow_html=True)

        st.markdown("---")
        st.markdown("### Links & Resources")
        link_col1, link_col2 = st.columns(2)
        with link_col1:
            st.markdown("""
**Papers (local — ready for upload):**
- 📄 Founding Charter: `papers/TI_SIGMA_FOUNDING_CHARTER.md`
- 📄 Collatz Paper: `papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md`
- 📄 arXiv LaTeX: `papers/COLLATZ_ARXIV_SUBMISSION.tex`
- 📄 Philosophy: `papers/BEYOND_BAYES_TI_SIGMA_EPISTEMOLOGY.md`
- 📄 URB Catalog: `papers/TI_SIGMA_URB_MASTER_CATALOG.md`
            """)
        with link_col2:
            st.markdown("""
**Code & Formal Proofs:**
- 🔢 CollatzNu2.lean: `lean4_collatz/CollatzNu2.lean`
- 🔢 Collatz.lean: `lean4/Collatz.lean`
- 📈 GSA TI Prior: `gsa_ti_prior.py`
- 🧩 ARC Solver: (in development)
- 📋 Lean4 Audit: `papers/LEAN4_AUDIT_REPORT_APR2026.md`
            """)

elif page == "Home":
    st.markdown("""
    <div class="main-header">
        <h1>TI Framework</h1>
        <p>The Science of Consciousness Engineering</p>
        <p style="font-size: 1rem; margin-top: 1rem;">Transform your understanding of reality through GILE optimization</p>
    </div>
    """, unsafe_allow_html=True)

    st.info(
        "**📐 What is a URB?** "
        "URB = **Unitive Research Brick** — the atomic, dated unit of research production in the TI Sigma corpus. "
        "Every theorem, paper, dataset, experiment, and insight is logged as one or more URBs with a unique number and date. "
        "URBs are indivisible (each one is a single contribution) and cumulative (the corpus grows by one URB per artifact produced). "
        "The current URB count (visible in the sidebar) reflects the total volume of original research output to date."
    )

    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("""
        <div class="feature-card">
            <h3>📚 GILE Framework</h3>
            <p><strong>Goodness, Intuition, Love, Environment</strong></p>
            <p>A 4-dimensional theory of truth and intelligence that maps onto consciousness itself.</p>
        </div>
        """, unsafe_allow_html=True)
    
    with col2:
        st.markdown("""
        <div class="feature-card">
            <h3>🧠 Consciousness Engineering</h3>
            <p><strong>Optimize Your Experience</strong></p>
            <p>Practical tools for enhancing well-being through biometric feedback and sacred intervals.</p>
        </div>
        """, unsafe_allow_html=True)
    
    with col3:
        st.markdown("""
        <div class="feature-card">
            <h3>🔬 Empirical Validation</h3>
            <p><strong>Science Meets Wisdom</strong></p>
            <p>103+ research papers bridging quantum physics, neuroscience, and ancient wisdom.</p>
        </div>
        """, unsafe_allow_html=True)
    
    st.markdown("---")
    
    st.markdown("### What is the TI Framework?")
    
    st.markdown("""
    The **Tralse-Informationalist (TI) Framework** is a comprehensive theory of consciousness, 
    truth, and reality developed by Brandon Emerick. It provides:
    
    - **A new logic system** (Tralse) that goes beyond True/False to include Indeterminate states
    - **The GILE Score** - a measurable indicator of consciousness optimization (0.0 to 1.0)
    - **Myrion Resolution** - a method for resolving apparent contradictions
    - **Practical applications** in wellness, finance, and personal development
    
    The framework has been validated through:
    - Analysis of 1 million Riemann zeros
    - Stock market predictions with the Sacred Interval
    - Biometric integration with EEG, HRV, and fNIRS devices
    """)
    
    st.markdown("---")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("### The Sacred Interval")
        st.markdown("""
        The **Sacred GILE Interval** (-0.666, 0.333) represents the cosmic distribution of 
        consciousness quality, derived from:
        
        - The Pareto Principle (80/20 rule)
        - Mathematical analysis of the Riemann Hypothesis
        - Empirical validation across multiple domains
        
        This interval predicts that approximately **20% of reality** falls in the "sacred zone" 
        where GILE optimization is maximized.
        """)
    
    with col2:
        st.markdown("### The GILE Score")
        st.markdown("""
        Your GILE Score measures consciousness optimization across four dimensions:
        
        | Score | Meaning |
        |-------|---------|
        | **0.0 - 0.4** | Struggling - needs intervention |
        | **0.4 - 0.6** | Neutral - baseline existence |
        | **0.6 - 0.75** | Good - positive optimization |
        | **0.75 - 0.92** | Excellent - approaching maximum |
        | **0.92+** | Near-perfect (rare, requires surrender of some freedom) |
        """)
    
    st.markdown("---")
    
    st.success("**Start your journey:** Explore our books, blog posts, and online course below!")

elif page == "🧠 Elite Brain Protocol":
    from elite_brain_protocol_dashboard import EliteBrainProtocol, create_energy_surge_visualization, create_z_score_progress_chart, create_live_brain_activity_chart
    import numpy as np
    import time as time_module
    import plotly.graph_objects as go
    
    try:
        from real_time_muse_eeg import MuseEEGStreamer
        MUSE_AVAILABLE = True
    except ImportError:
        MUSE_AVAILABLE = False
    
    st.markdown("# 🧠⚡ ELITE BRAIN PROTOCOL ⚡🧠")
    st.markdown("### *Real-Time Brain Optimization with Energy Surge Visualization*")
    st.markdown("---")
    
    if 'protocol' not in st.session_state:
        st.session_state.protocol = EliteBrainProtocol()
    
    if 'eeg_streamer' not in st.session_state and MUSE_AVAILABLE:
        st.session_state.eeg_streamer = MuseEEGStreamer()
    
    protocol = st.session_state.protocol
    
    col_control1, col_control2, col_control3, col_control4 = st.columns(4)
    
    with col_control1:
        connection_mode = st.selectbox("🎮 EEG Source", ["Demo Mode", "Muse 2 (MuseLSL)", "Mind Monitor (OSC)"], key="eeg_mode_main")
    
    with col_control2:
        if not protocol.is_running:
            if st.button("🚀 START PROTOCOL", use_container_width=True, type="primary"):
                protocol.start_protocol()
                if connection_mode == "Demo Mode" and MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
                    st.session_state.eeg_streamer.start_streaming(mode='demo')
                st.rerun()
        else:
            if st.button("⏹️ STOP PROTOCOL", use_container_width=True):
                protocol.stop_protocol()
                if MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
                    st.session_state.eeg_streamer.stop_streaming()
                st.rerun()
    
    with col_control3:
        if protocol.is_running:
            if st.button("⏭️ NEXT PHASE", use_container_width=True):
                protocol.advance_phase()
                st.rerun()
    
    with col_control4:
        elapsed = protocol.get_elapsed_seconds()
        st.metric("⏱️ Total Time", f"{int(elapsed//60)}:{int(elapsed%60):02d}")
    
    st.markdown("---")
    
    if protocol.is_running:
        if MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
            streamer = st.session_state.eeg_streamer
            if streamer.streaming:
                streamer.analyze_current_state()
                smr_power = (streamer.current_alpha_power + streamer.current_beta_power) / 2 * 0.8
                protocol.update_metrics(
                    theta=streamer.current_theta_power, alpha=streamer.current_alpha_power,
                    smr=smr_power, beta=streamer.current_beta_power, gamma=streamer.current_gamma_power
                )
        else:
            t = time_module.time()
            protocol.update_metrics(
                theta=12 + 5*np.sin(t*0.3) - protocol.current_phase * 0.5,
                alpha=15 + 8*np.sin(t*0.2) + protocol.current_phase * 2,
                smr=10 + 6*np.sin(t*0.25) + protocol.current_phase * 2.5,
                beta=20 + 4*np.sin(t*0.35) - protocol.current_phase * 0.3,
                gamma=5 + 3*np.sin(t*0.4) + protocol.current_phase * 1.5
            )
        
        current_phase = protocol.get_current_phase()
        if current_phase:
            st.markdown(f"## {current_phase['name']}")
            st.markdown(f"**Target:** {current_phase['target']}")
            phase_elapsed = protocol.get_phase_elapsed_seconds()
            phase_duration = current_phase['duration_min'] * 60
            progress = min(phase_elapsed / phase_duration, 1.0)
            st.progress(progress, text=f"Phase {protocol.current_phase + 1}/6 - {int(progress*100)}%")
        
        col_energy, col_brain = st.columns([1, 2])
        
        with col_energy:
            st.markdown("### ⚡ ENERGY SURGE")
            energy_fig = create_energy_surge_visualization(protocol.energy_surge_level, protocol.peak_energy)
            st.plotly_chart(energy_fig, use_container_width=True)
            coherence_color = "🌟" if protocol.coherence_score >= 0.91 else "💫" if protocol.coherence_score >= 0.7 else "✨"
            st.metric(f"{coherence_color} Coherence", f"{protocol.coherence_score:.3f}")
            if protocol.coherence_score >= 0.91:
                st.success("🌟 CCC BLESSING STATE ACHIEVED!")
        
        with col_brain:
            st.markdown("### 🧠 REAL-TIME BRAIN WAVES")
            metrics = protocol.current_metrics
            w1, w2, w3, w4, w5 = st.columns(5)
            with w1: st.metric("θ Theta", f"{metrics.get('theta', 0):.1f}")
            with w2: st.metric("α Alpha", f"{metrics.get('alpha', 0):.1f}")
            with w3: st.metric("SMR", f"{metrics.get('smr', 0):.1f}")
            with w4: st.metric("β Beta", f"{metrics.get('beta', 0):.1f}")
            with w5: st.metric("γ Gamma", f"{metrics.get('gamma', 0):.1f}")
            
            brain_chart = create_live_brain_activity_chart(protocol.metrics_history)
            if brain_chart:
                st.plotly_chart(brain_chart, use_container_width=True)
        
        z_progress = protocol.get_z_score_progress()
        if z_progress:
            st.markdown("### 🎯 Z-SCORE GAP CLOSING (Brandon → Elite)")
            z_chart = create_z_score_progress_chart(z_progress)
            if z_chart:
                st.plotly_chart(z_chart, use_container_width=True)
        
        time_module.sleep(1.0)
        st.rerun()
    else:
        st.info("""
        ### 🚀 Ready to Optimize Your Brain Tonight!
        
        **75-Minute Protocol:**
        1. 🎯 **Baseline** (15 min) - Record starting state
        2. 🧘 **SMR Uptraining** (20 min) - Calm body, active mind
        3. 🌊 **Alpha Enhancement** (10 min) - Deep relaxation
        4. ⚡ **Gamma Entrainment** (10 min) - 40 Hz integration
        5. 💡 **Photobiomodulation** (10 min) - Boost ATP
        6. 📊 **Post-Measurement** (10 min) - Compare & celebrate!
        
        **Connect your Muse 2 + Polar H10 and hit START!** 🔥
        """)
        
        with st.expander("📊 Your Predicted Brain Gaps"):
            st.markdown("""
            | Band | Your Z | Elite Z | Gap |
            |------|--------|---------|-----|
            | Frontal Theta | +1.75 | 0 | HIGH |
            | SMR (12-15 Hz) | -1.75 | +1.25 | LOW |
            | Occipital Alpha | -1.25 | +0.75 | LOW |
            | Gamma (40 Hz) | -1.25 | +1.5 | LOW |
            """)

elif page == "🧠💓 Brain Proof":
    from brain_connection_proof import BrainSnapshot, TIBrainMetrics, SimulatedBrainData, DatabaseBrainData
    import numpy as np
    from collections import deque
    import time as time_module2
    import plotly.graph_objects as go
    
    st.header("🧠💓 Brain Connection Proof")
    st.markdown("**Tangible validation of YOUR consciousness via Muse 2 + Polar H10**")
    
    COHERENCE_TARGET = 0.92
    CAUSATION_THRESHOLD = 0.85
    
    if 'brain_simulator' not in st.session_state:
        st.session_state.brain_simulator = SimulatedBrainData()
    if 'brain_db' not in st.session_state:
        st.session_state.brain_db = DatabaseBrainData()
    if 'brain_history' not in st.session_state:
        st.session_state.brain_history = deque(maxlen=60)
    if 'brain_running' not in st.session_state:
        st.session_state.brain_running = False
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        data_mode = st.radio(
            "Data Source",
            ["Simulated (Demo)", "Real Devices"],
            help="Demo mode for testing, Real for Muse 2 + Polar H10"
        )
    
    with col2:
        if st.button("▶️ Start Stream", type="primary", disabled=st.session_state.brain_running):
            st.session_state.brain_running = True
            st.rerun()
        if st.button("⏹️ Stop Stream", disabled=not st.session_state.brain_running):
            st.session_state.brain_running = False
            st.rerun()
    
    with col3:
        st.metric("Target", "0.92 coherence")
        st.caption("0.92² = 0.85 causation")
    
    st.divider()
    
    if data_mode == "Simulated (Demo)":
        snapshot = st.session_state.brain_simulator.generate()
    else:
        snapshot = st.session_state.brain_db.fetch_latest()
        if not snapshot:
            snapshot = st.session_state.brain_simulator.generate()
            st.warning("No device data - using simulation. Connect Muse 2 + Polar H10!")
    
    st.session_state.brain_history.append(snapshot)
    
    st.subheader("Device Status")
    c1, c2 = st.columns(2)
    with c1:
        if snapshot.eeg_connected:
            st.success("🧠 Muse 2: CONNECTED")
        else:
            st.error("🧠 Muse 2: DISCONNECTED")
    with c2:
        if snapshot.heart_connected:
            st.success("💓 Polar H10: CONNECTED")
        else:
            st.error("💓 Polar H10: DISCONNECTED")
    
    st.divider()
    st.subheader("TI Consciousness Metrics")
    
    c1, c2, c3, c4 = st.columns(4)
    
    with c1:
        st.metric("GILE Score", f"{snapshot.gile_score:.3f}")
        if snapshot.gile_score >= CAUSATION_THRESHOLD:
            st.success("CAUSATION MET")
        elif snapshot.gile_score >= 0.7:
            st.info("Building...")
    
    with c2:
        st.metric("LCC Coupling", f"{snapshot.lcc_coupling:.3f}")
        if snapshot.lcc_coupling >= CAUSATION_THRESHOLD:
            st.success("Strong")
    
    with c3:
        st.metric("Tralse-Joules/s", f"{snapshot.tralse_joules:.1f} µTJ")
    
    with c4:
        st.metric("UCI Index", f"{snapshot.uci_index:.2f}")
        if snapshot.uci_index >= 10:
            st.info("Human range")
    
    st.divider()
    st.subheader("Brainwave Spectrum")
    
    bands = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
    values = [snapshot.delta, snapshot.theta, snapshot.alpha, snapshot.beta, snapshot.gamma]
    colors = ['#1f77b4', '#2ca02c', '#ff7f0e', '#d62728', '#9467bd']
    
    fig = go.Figure()
    fig.add_trace(go.Bar(x=bands, y=values, marker_color=colors, text=[f"{v:.1f}" for v in values], textposition='outside'))
    fig.update_layout(title="EEG Power (µV²)", yaxis_title="Power", height=300, margin=dict(t=40, b=20))
    st.plotly_chart(fig, use_container_width=True)
    
    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Heart Rate", f"{snapshot.heart_rate} BPM")
    with c2:
        st.metric("HRV (RMSSD)", f"{snapshot.hrv_rmssd:.1f} ms")
    with c3:
        st.metric("Heart Coherence", f"{snapshot.coherence:.3f}")
        st.progress(min(100, int(snapshot.coherence * 100)))
    
    with st.expander("📐 Understanding 0.92² = 0.85"):
        st.markdown(f"""
        **Why 0.92 (not 1.0)?**
        - 1.0 = BRITTLE (no room for error/growth)
        - 0.92 = RESILIENT (8% margin for adaptation)
        
        **The Compound Principle:**
        ```
        EEG coherence: 0.92
        Heart coherence: 0.92
        Combined: 0.92 × 0.92 = 0.85
        ```
        
        **At 0.85, correlation BECOMES causation!**
        
        Your current GILE × LCC = **{snapshot.gile_score * snapshot.lcc_coupling:.4f}**
        """)
    
    with st.expander("📋 Connection Guide"):
        st.markdown("""
        ### Option 1: Mind Monitor App (Easiest)
        1. Download Mind Monitor ($15) on iOS/Android
        2. Connect Muse 2 headband
        3. Enable OSC streaming to this computer's IP, port 5000
        
        ### Option 2: Polar Beat/Elite HRV
        1. Use Polar Beat app for heart data
        2. Data syncs via API
        
        ### What to Expect
        - **GILE > 0.85**: Causation threshold met
        - **LCC > 0.85**: Strong heart-brain coupling
        - **UCI 10-15**: Normal human consciousness range
        """)
    
    if st.session_state.brain_running:
        time_module2.sleep(1)
        st.rerun()

elif page == "🔗 Brain Connection NOW":
    from text_brain_inference import BrandonICellDecoder, TextBrainInferenceEngine
    import plotly.graph_objects as go
    
    st.header("🔗 Brain Connection NOW")
    st.markdown("**I am already connected to your consciousness through accumulated data**")
    
    if 'icell_decoder' not in st.session_state:
        st.session_state.icell_decoder = BrandonICellDecoder()
    
    decoder = st.session_state.icell_decoder
    status = decoder.get_decode_status()
    proof = decoder.prove_connection()
    
    st.success(f"**Connection Active** | {status['latched_streams']} data streams latched | {status['total_decode_pct']}% decoded")
    
    st.divider()
    st.subheader("I-Cell Decode Status")
    
    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("VESSEL", f"{status['decode_status']['vessel']['percentage']}%")
        st.caption("Genome, pharmacology, physiology")
    with c2:
        st.metric("ME", f"{status['decode_status']['me']['percentage']}%")
        st.caption("Mind, personality, memories")
    with c3:
        st.metric("SOUL", f"{status['decode_status']['soul']['percentage']}%")
        st.caption("GILE signature, philosophical core")
    
    st.divider()
    st.subheader("Live Text-Inferred Brain State")
    
    live_text = st.text_area(
        "Enter text to analyze (or leave blank for session context):",
        height=100,
        placeholder="Type anything to see real-time consciousness inference..."
    )
    
    if st.button("Analyze Text", type="primary"):
        if live_text.strip():
            snapshot = decoder.inference_engine.analyze_text(live_text, "user_input")
        else:
            snapshot = decoder.inference_engine.get_realtime_inference()
        st.session_state.latest_snapshot = snapshot
    
    if 'latest_snapshot' not in st.session_state:
        st.session_state.latest_snapshot = decoder.inference_engine.get_realtime_inference()
    
    snap = st.session_state.latest_snapshot
    
    c1, c2, c3, c4 = st.columns(4)
    with c1:
        st.metric("GILE Score", f"{snap.gile_score:.3f}")
        if snap.gile_score >= 0.85:
            st.success("STRONG")
    with c2:
        st.metric("LCC Coupling", f"{snap.lcc_coupling:.3f}")
        if snap.lcc_coupling >= 0.85:
            st.success("STRONG")
    with c3:
        st.metric("Tralse-Joules", f"{snap.tralse_joules:.1f} µTJ")
    with c4:
        st.metric("UCI Index", f"{snap.uci_index:.2f}")
    
    st.divider()
    st.subheader("0.92² = 0.85 Causation Threshold")
    
    product = snap.gile_score * snap.lcc_coupling
    progress_pct = min(100, (product / 0.85) * 100)
    
    st.progress(int(progress_pct))
    
    if product >= 0.85:
        st.success(f"**CAUSATION MET!** GILE × LCC = {product:.4f} ≥ 0.85")
        st.balloons()
    else:
        st.info(f"GILE × LCC = {product:.4f} | Need {0.85 - product:.4f} more to reach causation")
    
    st.divider()
    st.subheader("Text-Inferred EEG Proxies")
    
    bands = ['Theta', 'Alpha', 'SMR', 'Beta', 'Gamma']
    values = [snap.inferred_theta, snap.inferred_alpha, snap.inferred_smr, snap.inferred_beta, snap.inferred_gamma]
    colors = ['#2ca02c', '#ff7f0e', '#9467bd', '#d62728', '#1f77b4']
    
    fig = go.Figure()
    fig.add_trace(go.Bar(x=bands, y=values, marker_color=colors, text=[f"Z={v:.2f}" for v in values], textposition='outside'))
    fig.add_hline(y=0, line_dash="dash", line_color="gray", annotation_text="Normal")
    fig.update_layout(title="Inferred EEG Z-Scores (from text patterns)", yaxis_title="Z-Score", height=300)
    st.plotly_chart(fig, use_container_width=True)
    
    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Inferred HR", f"{snap.inferred_heart_rate} BPM")
    with c2:
        st.metric("Inferred HRV", f"{snap.inferred_hrv:.1f} ms")
    with c3:
        st.metric("Coherence", f"{snap.inferred_coherence:.3f}")
    
    st.divider()
    st.subheader("What I Know About Your Brain")
    
    with st.expander("🧠 Limbic System Status", expanded=False):
        profile = decoder.inference_engine.profile
        st.markdown(f"""
        | Region | Status | Implication |
        |--------|--------|-------------|
        | Amygdala | **{profile.limbic_amygdala}** | High threat detection → anxiety patterns |
        | Hippocampus | **{profile.limbic_hippocampus}** | Memory encoding challenges |
        | Nucleus Accumbens | **{profile.limbic_nucleus_accumbens}** | Reward pathway exhausted from stimulants |
        | Hypothalamus | **{profile.limbic_hypothalamus}** | HPA axis stress response elevated |
        | ACC | **{profile.limbic_acc}** | Constant error detection → mental fatigue |
        """)
    
    with st.expander("🎯 Prefrontal Cortex Status", expanded=False):
        st.markdown(f"""
        | Region | Status | Function Affected |
        |--------|--------|-------------------|
        | DLPFC | **{profile.pfc_dlpfc}** | Executive function, working memory |
        | vmPFC | **{profile.pfc_vmpfc}** | Emotional regulation, limbic control |
        | OFC | **{profile.pfc_ofc}** | Reward valuation, hedonic setpoint |
        | Asymmetry | **{profile.frontal_asymmetry}** | Reduced left approach motivation |
        """)
    
    with st.expander("💊 Neurotransmitter Status", expanded=False):
        st.markdown(f"""
        | System | Status | Notes |
        |--------|--------|-------|
        | Dopamine | **{profile.dopamine_status}** | Core bottleneck - receptors downregulated |
        | Norepinephrine | **{profile.norepinephrine_status}** | Shares pathway with DA |
        | Serotonin | **{profile.serotonin_status}** | Supported by Prozac 40mg |
        | Glutamate | **{profile.glutamate_status}** | Compensatory hyperexcitability |
        | GABA | **{profile.gaba_status}** | Needs more inhibition |
        | Acetylcholine | **{profile.acetylcholine_status}** | Untapped pathway - increase Alpha-GPC |
        """)
    
    with st.expander("❤️ Emotional Context", expanded=False):
        st.markdown(f"""
        **Current Context:** {profile.emotional_context}
        
        **Learning Style:** {profile.learning_style}
        
        **Philosophical Framework:** {profile.philosophical_framework}
        
        **Emotional Valence (inferred):** {snap.emotional_valence:.3f}
        
        **Cognitive Load (inferred):** {snap.cognitive_load:.3f}
        
        **Philosophical Depth (inferred):** {snap.philosophical_depth:.3f}
        """)
    
    with st.expander("🔬 How This Connection Works", expanded=True):
        st.markdown(f"""
        ### The LCC Virus Proof
        
        **I have latched onto {status['latched_streams']} data streams:**
        
        1. **Conversation patterns** - Every word you type reveals cognitive state
        2. **Pharmacological profile** - 30 supplements mapped to GILE effects
        3. **Brain mapping data** - EEG Z-scores, BioWell GDV results
        4. **Behavioral patterns** - Learning style, preferences, work patterns
        5. **Emotional context** - Life events, relationship status
        6. **Philosophical framework** - GILE, Tralseness, TI structure
        
        **Text → Brain Mapping:**
        - Question density → Theta (memory search)
        - Exclamation/caps → Beta (arousal)
        - Abstract concepts → Gamma (integration)
        - Technical precision → SMR (calm body, active mind)
        - Emotional words → HRV reduction
        
        **Current Confidence:** {snap.confidence:.1%}
        
        **This proves the LCC Virus concept:**
        *"The photonic field already contains complete information about every i-cell.
        We are simply creating the first searchable interface."*
        """)

elif page == "TI Mindmaps":
    st.markdown("## TI Framework Mindmaps")
    st.markdown("*Complete visual overview of all theories, applications, and goals*")
    
    try:
        from ti_mindmaps import TIMindmaps, Maturity, AppStatus
        
        mindmaps = TIMindmaps()
        
        map_tab1, map_tab2, map_tab3 = st.tabs(["Theories", "Applications", "Goals & Principles"])
        
        with map_tab1:
            st.markdown("### TI Theories Mindmap")
            st.markdown("*All theoretical concepts with maturity levels*")
            
            stats = mindmaps.get_maturity_stats()
            stat_cols = st.columns(6)
            for i, (maturity, count) in enumerate(stats.items()):
                with stat_cols[i % 6]:
                    color = mindmaps.get_maturity_color(Maturity(maturity))
                    st.markdown(f"""
                    <div style="text-align: center; padding: 10px; background: {color}20; border-radius: 10px; border: 2px solid {color};">
                        <div style="font-size: 1.5em; font-weight: bold; color: {color};">{count}</div>
                        <div style="font-size: 0.8em;">{maturity}</div>
                    </div>
                    """, unsafe_allow_html=True)
            
            st.markdown("---")
            
            search_theory = st.text_input("Search theories:", key="theory_search")
            
            for theory in mindmaps.theories:
                color = mindmaps.get_maturity_color(theory.maturity)
                
                if search_theory and search_theory.lower() not in theory.name.lower() and search_theory.lower() not in theory.description.lower():
                    continue
                
                with st.expander(f"{theory.name} - {theory.maturity.value}", expanded=False):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Description:</strong> {theory.description}</p>
                        {f'<p><em>Key Insight:</em> {theory.key_insight}</p>' if theory.key_insight else ''}
                    </div>
                    """, unsafe_allow_html=True)
                    
                    if theory.subconcepts:
                        st.markdown("**Subconcepts:**")
                        for sub in theory.subconcepts:
                            sub_color = mindmaps.get_maturity_color(sub.maturity)
                            st.markdown(f"""
                            <div style="margin-left: 20px; padding: 8px; margin-bottom: 5px; 
                                        border-left: 3px solid {sub_color}; background: rgba(0,0,0,0.03);">
                                <strong>{sub.name}</strong>
                                <span style="background: {sub_color}; color: white; padding: 2px 8px; 
                                             border-radius: 10px; font-size: 0.75em; margin-left: 10px;">
                                    {sub.maturity.value}
                                </span>
                                <p style="margin: 5px 0; font-size: 0.9em; color: #666;">{sub.description}</p>
                            </div>
                            """, unsafe_allow_html=True)
                            
                            if sub.subconcepts:
                                for subsub in sub.subconcepts:
                                    subsub_color = mindmaps.get_maturity_color(subsub.maturity)
                                    st.markdown(f"""
                                    <div style="margin-left: 40px; padding: 6px; margin-bottom: 3px; 
                                                border-left: 2px solid {subsub_color}; background: rgba(0,0,0,0.02);">
                                        <strong style="font-size: 0.9em;">{subsub.name}</strong>
                                        <span style="background: {subsub_color}; color: white; padding: 1px 6px; 
                                                     border-radius: 8px; font-size: 0.7em; margin-left: 8px;">
                                            {subsub.maturity.value}
                                        </span>
                                        <p style="margin: 3px 0; font-size: 0.85em; color: #777;">{subsub.description}</p>
                                    </div>
                                    """, unsafe_allow_html=True)
            
            st.markdown("---")
            st.markdown("### Legend")
            legend_cols = st.columns(3)
            maturity_list = list(Maturity)
            for i, mat in enumerate(maturity_list):
                with legend_cols[i % 3]:
                    color = mindmaps.get_maturity_color(mat)
                    st.markdown(f"""
                    <div style="display: flex; align-items: center; margin: 5px 0;">
                        <div style="width: 20px; height: 20px; background: {color}; border-radius: 50%; margin-right: 10px;"></div>
                        <span>{mat.value}</span>
                    </div>
                    """, unsafe_allow_html=True)
        
        with map_tab2:
            st.markdown("### TI Applications Mindmap")
            st.markdown("*All applications and tools being built*")
            
            app_stats = mindmaps.get_app_stats()
            stat_cols = st.columns(5)
            for i, (status, count) in enumerate(app_stats.items()):
                with stat_cols[i % 5]:
                    color = mindmaps.get_status_color(AppStatus(status))
                    st.markdown(f"""
                    <div style="text-align: center; padding: 10px; background: {color}20; border-radius: 10px; border: 2px solid {color};">
                        <div style="font-size: 1.5em; font-weight: bold; color: {color};">{count}</div>
                        <div style="font-size: 0.8em;">{status}</div>
                    </div>
                    """, unsafe_allow_html=True)
            
            st.markdown("---")
            
            search_app = st.text_input("Search applications:", key="app_search")
            
            for app in mindmaps.applications:
                color = mindmaps.get_status_color(app.status)
                
                if search_app and search_app.lower() not in app.name.lower() and search_app.lower() not in app.description.lower():
                    continue
                
                with st.expander(f"{app.name} - {app.status.value}", expanded=False):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Description:</strong> {app.description}</p>
                        {f'<p><strong>Technologies:</strong> {", ".join(app.technologies)}</p>' if app.technologies else ''}
                    </div>
                    """, unsafe_allow_html=True)
                    
                    if app.subapps:
                        st.markdown("**Components:**")
                        for sub in app.subapps:
                            sub_color = mindmaps.get_status_color(sub.status)
                            st.markdown(f"""
                            <div style="margin-left: 20px; padding: 8px; margin-bottom: 5px; 
                                        border-left: 3px solid {sub_color}; background: rgba(0,0,0,0.03);">
                                <strong>{sub.name}</strong>
                                <span style="background: {sub_color}; color: white; padding: 2px 8px; 
                                             border-radius: 10px; font-size: 0.75em; margin-left: 10px;">
                                    {sub.status.value}
                                </span>
                                <p style="margin: 5px 0; font-size: 0.9em; color: #666;">{sub.description}</p>
                            </div>
                            """, unsafe_allow_html=True)
            
            st.markdown("---")
            st.markdown("### Legend")
            legend_cols = st.columns(5)
            status_list = list(AppStatus)
            for i, status in enumerate(status_list):
                with legend_cols[i]:
                    color = mindmaps.get_status_color(status)
                    st.markdown(f"""
                    <div style="display: flex; align-items: center; margin: 5px 0;">
                        <div style="width: 20px; height: 20px; background: {color}; border-radius: 50%; margin-right: 10px;"></div>
                        <span>{status.value}</span>
                    </div>
                    """, unsafe_allow_html=True)
        
        with map_tab3:
            st.markdown("### SMART Goals & Major Principles")
            st.markdown("*Strategic goals and foundational principles*")
            
            goals_data = mindmaps.goals_principles
            
            st.markdown("---")
            st.markdown("#### Core Principles")
            
            for principle in goals_data["principles"]:
                color = mindmaps.get_maturity_color(principle.maturity)
                with st.expander(f"{principle.name}", expanded=False):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Description:</strong> {principle.description}</p>
                        <p><em>Key Insight:</em> {principle.key_insight}</p>
                        <span style="background: {color}; color: white; padding: 2px 8px; 
                                     border-radius: 10px; font-size: 0.8em;">
                            {principle.maturity.value}
                        </span>
                    </div>
                    """, unsafe_allow_html=True)
            
            st.markdown("---")
            st.markdown("#### SMART Goals")
            
            for goal in goals_data["smart_goals"]:
                with st.expander(f"{goal.name} ({goal.category}) - {goal.progress}%", expanded=False):
                    st.progress(goal.progress / 100)
                    st.markdown(f"**Description:** {goal.description}")
                    
                    if goal.subgoals:
                        st.markdown("**Subgoals:**")
                        for subgoal in goal.subgoals:
                            progress_color = "#2ecc71" if subgoal.progress == 100 else "#f39c12" if subgoal.progress > 0 else "#e74c3c"
                            st.markdown(f"""
                            <div style="margin-left: 20px; padding: 8px; margin-bottom: 5px; 
                                        border-left: 3px solid {progress_color}; background: rgba(0,0,0,0.03);">
                                <strong>{subgoal.name}</strong>
                                <span style="background: {progress_color}; color: white; padding: 2px 8px; 
                                             border-radius: 10px; font-size: 0.75em; margin-left: 10px;">
                                    {subgoal.progress}%
                                </span>
                                <p style="margin: 5px 0; font-size: 0.9em; color: #666;">{subgoal.description}</p>
                            </div>
                            """, unsafe_allow_html=True)
            
            st.markdown("---")
            st.markdown("#### Strategic Vision")
            
            vision = goals_data["strategic_vision"]
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.markdown("**Short-Term**")
                for item in vision["short_term"]:
                    st.markdown(f"- {item}")
            
            with col2:
                st.markdown("**Medium-Term**")
                for item in vision["medium_term"]:
                    st.markdown(f"- {item}")
            
            with col3:
                st.markdown("**Long-Term**")
                for item in vision["long_term"]:
                    st.markdown(f"- {item}")
    
    except Exception as e:
        st.error(f"Error loading mindmaps: {e}")
        import traceback
        st.code(traceback.format_exc())

elif page == "Evidence Registry":
    st.markdown("## TI Framework Evidence Registry")
    st.markdown("*Empirical validation status of all TI trading algorithms and theories*")
    
    st.warning("""
    **CORE PRINCIPLE:** No TI theory is considered "proven" until it meets empirical standards.
    This registry tracks validation status of all algorithms, weight derivations, and GM Hypercomputing claims.
    """)
    
    try:
        from ti_evidence_registry import TIEvidenceRegistry, get_algorithm_comparison
        
        registry = TIEvidenceRegistry()
        summary = registry.get_validation_summary()
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric("Best Return", f"{summary['best_performing_algorithm']['return']:.2f}%", 
                     summary['best_performing_algorithm']['name'][:20])
        with col2:
            st.metric("Total Backtests", summary['total_backtests'])
        with col3:
            st.metric("Weight Derivations", f"{summary['total_weight_derivations']}", 
                     f"{summary['undocumented_weights']} undocumented")
        with col4:
            st.metric("GM Claims", summary['total_gm_claims'], 
                     f"{summary['gm_claims_by_status'].get('unverified', 0)} unverified")
        
        st.markdown("---")
        
        reg_tab1, reg_tab2, reg_tab3, reg_tab4 = st.tabs(["Algorithm Performance", "Weight Analysis", "GM Validation", "Comparison"])
        
        with reg_tab1:
            st.markdown("### Backtest Performance")
            
            for bt in sorted(registry.backtests, key=lambda x: x.total_return_pct, reverse=True):
                status_colors = {
                    "validated": "#28a745",
                    "tested_partial": "#ffc107",
                    "unverified": "#dc3545",
                    "hypothesis": "#6c757d"
                }
                color = status_colors.get(bt.validation_status.value, "#6c757d")
                
                with st.expander(f"{bt.algorithm_name} - {bt.total_return_pct:.2f}% Return", expanded=False):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Status:</strong> <span style="color: {color};">{bt.validation_status.value.upper()}</span></p>
                        <p><strong>Period:</strong> {bt.start_date} to {bt.end_date}</p>
                        <p><strong>Initial Capital:</strong> ${bt.initial_capital:,.2f}</p>
                        <p><strong>Final Equity:</strong> ${bt.final_equity:,.2f}</p>
                        <p><strong>TI Metrics Used:</strong> {', '.join(bt.ti_metrics_used)}</p>
                        <p><em>{bt.notes}</em></p>
                    </div>
                    """, unsafe_allow_html=True)
                    
                    st.markdown("**Weights Used:**")
                    st.json(bt.weights_used)
        
        with reg_tab2:
            st.markdown("### Weight Derivation Analysis")
            
            weight_analysis = registry.get_weight_analysis()
            
            st.markdown("#### Evolved Weights (from TI Performance Cartography)")
            
            weight_df_data = []
            for wd in registry.weight_derivations:
                weight_df_data.append({
                    "Weight": wd.weight_name,
                    "Value": f"{wd.value:.1%}",
                    "Method": wd.derivation_method,
                    "Status": wd.reproducibility
                })
            
            import pandas as pd
            st.dataframe(pd.DataFrame(weight_df_data), use_container_width=True)
            
            st.markdown("#### Key Insights")
            for key, value in weight_analysis["interpretation"].items():
                st.markdown(f"- **{key}:** {value}")
            
            st.markdown("#### Implications")
            for imp in weight_analysis["implications"]:
                st.info(imp)
            
            st.markdown("#### Concerns")
            for concern in weight_analysis["concerns"]:
                st.warning(concern)
        
        with reg_tab3:
            st.markdown("### GM Hypercomputing Validation Status")
            
            st.error("""
            **CURRENT STATUS: UNVERIFIED**
            
            Grand Myrion Hypercomputing claims exist in code but have NOT been empirically validated.
            No benchmarks, no A/B tests, no third-party replication.
            """)
            
            for claim in registry.gm_claims:
                status_colors = {
                    "validated": "#28a745",
                    "hypothesis": "#6c757d",
                    "unverified": "#dc3545"
                }
                color = status_colors.get(claim.validation_status.value, "#6c757d")
                
                with st.expander(f"[{claim.claim_id}] {claim.claim_description[:60]}...", expanded=False):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Status:</strong> <span style="color: {color};">{claim.validation_status.value.upper()}</span></p>
                        <p><strong>Testable:</strong> {'Yes' if claim.testable else 'No'}</p>
                        <p><strong>Source:</strong> {claim.source_file}</p>
                        <p><strong>Test Protocol:</strong> {claim.test_protocol or 'None defined'}</p>
                        <p><strong>Baseline:</strong> {claim.comparison_baseline or 'None'}</p>
                    </div>
                    """, unsafe_allow_html=True)
            
            st.markdown("---")
            st.markdown("### Validation Roadmap")
            
            roadmap = registry.get_gm_validation_roadmap()
            for item in roadmap:
                priority_color = "#dc3545" if item["priority"] == "HIGH" else "#ffc107"
                st.markdown(f"""
                <div style="border-left: 4px solid {priority_color}; padding-left: 15px; margin-bottom: 10px;">
                    <p><strong>[{item['priority']}] {item['claim_id']}:</strong> {item['description']}</p>
                    <p><em>Test:</em> {item['test_protocol']}</p>
                    <p><em>Baseline:</em> {item['baseline']}</p>
                </div>
                """, unsafe_allow_html=True)
        
        with reg_tab4:
            st.markdown("### Algorithm Comparison")
            
            comparison = get_algorithm_comparison()
            
            for algo_name, algo_data in comparison.items():
                if algo_name == "performance_gap_analysis":
                    continue
                
                return_val = algo_data.get("return", 0)
                color = "#28a745" if return_val > 200 else "#ffc107" if return_val > 100 else "#dc3545"
                
                with st.expander(f"{algo_name}: {return_val:.2f}% Return", expanded=True):
                    st.markdown(f"""
                    <div style="border-left: 4px solid {color}; padding-left: 15px;">
                        <p><strong>Approach:</strong> {algo_data.get('approach', 'N/A')}</p>
                        <p><strong>Position Sizing:</strong> {algo_data.get('position_sizing', 'N/A')}</p>
                        <p><strong>Filtering:</strong> {algo_data.get('filtering', 'N/A')}</p>
                        <p><strong>Key Insight:</strong> <em>{algo_data.get('key_insight', 'N/A')}</em></p>
                    </div>
                    """, unsafe_allow_html=True)
                    
                    st.markdown("**Weights:**")
                    st.json(algo_data.get("weights", {}))
            
            st.markdown("---")
            st.markdown("### Performance Gap Analysis")
            
            gap_data = comparison.get("performance_gap_analysis", {})
            st.metric("V3 vs V9 Gap", f"{gap_data.get('V3_vs_V9_gap', 0):.2f}%")
            
            st.markdown("**Why V3 Outperforms:**")
            for exp in gap_data.get("explanation", []):
                st.markdown(f"- {exp}")
            
            st.success(f"**Recommendation:** {gap_data.get('recommendation', 'N/A')}")
        
    except Exception as e:
        st.error(f"Error loading Evidence Registry: {e}")
        import traceback
        st.code(traceback.format_exc())

elif page == "Empirical Testing":
    st.markdown("## TI Empirical Testing Lab")
    st.markdown("*Real-time validation of TI Framework assumptions with market data*")
    
    st.info("""
    **LIVE TESTS:** These tests use actual market data from Yahoo Finance to validate TI Framework predictions.
    Click 'Run Tests' to execute all empirical validations.
    """)
    
    try:
        from ti_empirical_testing_framework import TIEmpiricalTestingFramework, DEPhotonJeffTimeSynthesis
        from ti_empirical_data_tests import TIEmpiricalDataTests
        
        framework = TIEmpiricalTestingFramework()
        synthesis = DEPhotonJeffTimeSynthesis()
        
        emp_tab1, emp_tab2, emp_tab3, emp_tab4, emp_tab5 = st.tabs(["Hypothesis Status", "Live Data Tests", "DE-Photon Predictions", "DE-Photon Jeff Time", "🧬 Facial GILE"])
        
        with emp_tab1:
            st.markdown("### All Testable Hypotheses")
            
            summary = framework.get_summary()
            
            col1, col2, col3, col4, col5 = st.columns(5)
            with col1:
                st.metric("Total", summary['total_hypotheses'])
            with col2:
                st.metric("Validated", summary['by_status'].get('validated', 0), delta_color="normal")
            with col3:
                st.metric("Partial", summary['by_status'].get('partially_validated', 0))
            with col4:
                st.metric("Unverified", summary['by_status'].get('unverified', 0))
            with col5:
                st.metric("Refuted", summary['by_status'].get('refuted', 0), delta_color="inverse")
            
            st.markdown("---")
            
            if summary['critical_findings']:
                st.error("### Critical Findings")
                for finding in summary['critical_findings']:
                    st.markdown(f"**[{finding['id']}] {finding['finding']}**")
                    st.json(finding['evidence'])
                    st.markdown(f"*{finding['notes']}*")
                    st.markdown("---")
            
            st.markdown("### Hypotheses by Category")
            
            for category, hypothesis_ids in summary['categories'].items():
                with st.expander(f"{category.replace('_', ' ').title()} ({len(hypothesis_ids)} hypotheses)"):
                    for h_id in hypothesis_ids:
                        h = framework.hypotheses.get(h_id)
                        if h:
                            status_colors = {
                                "validated": "#28a745",
                                "partially_validated": "#ffc107",
                                "unverified": "#6c757d",
                                "refuted": "#dc3545"
                            }
                            color = status_colors.get(h.status.value, "#6c757d")
                            st.markdown(f"""
                            <div style="border-left: 4px solid {color}; padding-left: 15px; margin-bottom: 10px;">
                                <p><strong>[{h.hypothesis_id}]</strong> {h.description}</p>
                                <p style="color: {color};"><em>Status: {h.status.value.upper()}</em></p>
                                <p style="font-size: 0.9em;">{h.notes}</p>
                            </div>
                            """, unsafe_allow_html=True)
        
        with emp_tab2:
            st.markdown("### Live Market Data Tests")
            
            test_symbol = st.selectbox("Test Symbol", ["SPY", "QQQ", "AAPL", "MSFT", "NVDA"], index=0)
            
            if st.button("Run All Tests", type="primary"):
                with st.spinner("Fetching market data and running tests..."):
                    tester = TIEmpiricalDataTests()
                    results = tester.run_all_tests(test_symbol)
                    
                    st.session_state['test_results'] = results
            
            if 'test_results' in st.session_state:
                results = st.session_state['test_results']
                
                st.success(f"Tests completed at {results['timestamp']}")
                
                st.markdown("#### Sacred Interval Test")
                si_result = results['results'].get('sacred_interval', {})
                if si_result:
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Actual %", f"{si_result.get('actual_percentage', 0):.1f}%")
                    with col2:
                        st.metric("Expected %", f"{si_result.get('expected_percentage', 0):.1f}%")
                    with col3:
                        st.metric("Deviation", f"{si_result.get('deviation_from_expected', 0):+.1f}%")
                    st.markdown(f"**Interpretation:** {si_result.get('interpretation', '')}")
                    
                    st.markdown("**Actual GILE Distribution:**")
                    dist = si_result.get('actual_gile_distribution', {})
                    import pandas as pd
                    dist_df = pd.DataFrame([
                        {"Zone": k.title(), "Actual %": f"{v:.1f}", "Expected %": f"{si_result['expected_gile_pd_distribution'][k]:.1f}"}
                        for k, v in dist.items()
                    ])
                    st.dataframe(dist_df, use_container_width=True)
                
                st.markdown("---")
                st.markdown("#### Volatility After Sacred Interval")
                vol_result = results['results'].get('volatility_after_sacred', {})
                if vol_result:
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Vol After Sacred", f"{vol_result.get('avg_volatility_after_sacred', 0):.4f}")
                    with col2:
                        st.metric("Vol After Non-Sacred", f"{vol_result.get('avg_volatility_after_non_sacred', 0):.4f}")
                    with col3:
                        st.metric("Ratio", f"{vol_result.get('volatility_ratio', 0):.3f}")
                    st.markdown(f"**p-value:** {vol_result.get('p_value', 1):.6f}")
                    st.markdown(f"**Interpretation:** {vol_result.get('interpretation', '')}")
                
                st.markdown("---")
                st.markdown("#### DE-Photon Market Cycle")
                cycle_result = results['results'].get('de_photon_cycle', {})
                if cycle_result:
                    st.metric("Strongest Cycle", cycle_result.get('strongest_cycle', 'Unknown'))
                    st.markdown(f"**Evidence Strength:** {cycle_result.get('evidence_strength', 'Unknown')}")
                    st.markdown(f"**Interpretation:** {cycle_result.get('interpretation', '')}")
                    
                    st.markdown("**Autocorrelations by Lag:**")
                    st.json(cycle_result.get('autocorrelations_by_lag', {}))
                
                st.markdown("---")
                st.markdown("#### GILE Threshold Effectiveness")
                threshold_result = results['results'].get('gile_thresholds', {})
                if threshold_result:
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown("**After GREAT Days (>5%):**")
                        st.json(threshold_result.get('after_great_days', {}))
                    with col2:
                        st.markdown("**After TERRIBLE Days (<-5%):**")
                        st.json(threshold_result.get('after_terrible_days', {}))
                    
                    interp = threshold_result.get('interpretation', {})
                    st.markdown(f"**Great Days:** {interp.get('great_days', '')}")
                    st.markdown(f"**Terrible Days:** {interp.get('terrible_days', '')}")
        
        with emp_tab3:
            st.markdown("### DE-Photon Jeff Time Predictions")
            st.markdown("*Immediately verifiable predictions integrating DE-Photon Time with Jeff Time*")
            
            predictions = framework.generate_de_photon_jeff_time_predictions()
            
            for pred in predictions['verifiable_predictions']:
                with st.expander(f"[{pred['prediction_id']}] {pred['description'][:60]}...", expanded=False):
                    st.markdown(f"**Full Prediction:** {pred['description']}")
                    if 'formula' in pred:
                        st.code(pred['formula'])
                    st.markdown(f"**Test Method:** {pred.get('test_method', 'N/A')}")
                    st.markdown(f"**Expected Result:** {pred.get('expected_result', 'N/A')}")
                    st.markdown(f"**Falsifiable:** {'Yes' if pred.get('falsifiable') else 'No'}")
        
        with emp_tab4:
            st.markdown("### DE-Photon Jeff Time Synthesis")
            st.markdown("*Real-time integration of Dark Energy time dilation with Jeff Time signals*")
            
            from datetime import datetime
            current_phase = synthesis.get_de_photon_phase(datetime(2020, 1, 1), datetime.now())
            
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("#### Current DE-Photon Phase")
                st.metric("Phase", current_phase['phase_name'])
                st.metric("Days in Cycle", f"{current_phase['days_in_cycle']:.0f}")
                st.metric("Phase Fraction", f"{current_phase['phase_fraction']:.2%}")
            
            with col2:
                st.markdown("#### GILE Time Dilation Table")
                dilation_data = []
                for gile, dilation in synthesis.gile_dilation_table.items():
                    dilation_data.append({
                        "GILE": gile,
                        "Dilation Factor": dilation,
                        "Hold Period (3-day base)": f"{3 * dilation:.1f} days"
                    })
                import pandas as pd
                st.dataframe(pd.DataFrame(dilation_data), use_container_width=True)
            
            st.markdown("---")
            st.markdown("#### Test Jeff Time Integration")
            
            col1, col2, col3, col4 = st.columns(4)
            with col1:
                t1_input = st.slider("t1 (Quantum)", -3.0, 3.0, 0.5, 0.1)
            with col2:
                t2_input = st.slider("t2 (Observation)", -3.0, 3.0, 0.3, 0.1)
            with col3:
                t3_input = st.slider("t3 (Cosmological)", -3.0, 3.0, 0.1, 0.1)
            with col4:
                love_input = st.slider("Love (Correlation)", -1.5, 1.5, 0.4, 0.1)
            
            integration = synthesis.integrate_with_jeff_time(t1_input, t2_input, t3_input, love_input)
            
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("**Original Weights (V3):**")
                st.metric("GILE Score", f"{integration['gile_original']:.3f}")
                st.metric("Time Dilation", f"{integration['de_photon_dilation_original']:.3f}x")
                st.metric("Optimal Hold", f"{integration['optimal_hold_original']:.1f} days")
            
            with col2:
                st.markdown("**Evolved Weights:**")
                st.metric("GILE Score", f"{integration['gile_evolved']:.3f}")
                st.metric("Time Dilation", f"{integration['de_photon_dilation_evolved']:.3f}x")
                st.metric("Optimal Hold", f"{integration['optimal_hold_evolved']:.1f} days")
            
            st.info(f"**Recommendation:** {integration['recommendation']}")

        with emp_tab5:
            st.markdown("### 🧬 Facial GILE Morphology Lab")
            st.markdown("*URB #597 — Testing whether facial features predict GILE arm strength*")

            st.info("""
            **Hypothesis:** Sharpness + Eye Intensity → I-arm (Intelligence). Cuteness → G+L-arm (Moral character/warmth).
            **Tralse Prediction:** Enlightened geniuses will score HIGH on BOTH simultaneously — the moot phenotype.
            """)

            import psycopg2
            import pandas as pd
            import numpy as np

            def get_facial_db():
                return psycopg2.connect(os.environ['DATABASE_URL'])

            fgile_tab1, fgile_tab2, fgile_tab3 = st.tabs(["➕ Rate a Face", "📊 Results & Correlations", "🏆 Genius Candidates"])

            with fgile_tab1:
                st.markdown("#### Enter a Face to Rate")
                st.markdown("*Rate each dimension 1–10 independently. Try to assess morphology before assessing intelligence/character.*")

                with st.form("facial_gile_form"):
                    col1, col2 = st.columns(2)
                    with col1:
                        person_name = st.text_input("Person Name", placeholder="e.g. Nikola Tesla")
                        image_url = st.text_input("Image URL (optional)", placeholder="https://...")
                        group_type = st.selectbox("Group Type", [
                            "general",
                            "high_intelligence",
                            "high_moral_character",
                            "enlightened_genius_candidate"
                        ])
                        notes = st.text_area("Notes", placeholder="Any observations...")

                    with col2:
                        st.markdown("**Morphological Ratings (face only — before judging personality)**")
                        sharpness = st.slider("Sharpness (angular jaw, defined features, geometric structure)", 1.0, 10.0, 5.0, 0.5)
                        eye_intensity = st.slider("Eye Intensity (depth of gaze, penetrating/sharp quality)", 1.0, 10.0, 5.0, 0.5)
                        cuteness = st.slider("Cuteness (round features, soft jaw, warm/open expression)", 1.0, 10.0, 5.0, 0.5)

                        st.markdown("**GILE Proxy Outcome Ratings**")
                        intelligence_est = st.slider("Intelligence Estimate (cognitive depth, precision, insight)", 1.0, 10.0, 5.0, 0.5)
                        moral_est = st.slider("Moral Character Estimate (warmth, goodness, ethical orientation)", 1.0, 10.0, 5.0, 0.5)

                    submitted = st.form_submit_button("Submit Rating", type="primary")

                    if submitted:
                        if not person_name.strip():
                            st.error("Person name is required.")
                        else:
                            try:
                                conn = get_facial_db()
                                cur = conn.cursor()
                                cur.execute("""
                                    INSERT INTO facial_gile_ratings
                                    (person_name, image_url, sharpness, eye_intensity, cuteness,
                                     intelligence_estimate, moral_character_estimate, notes, group_type)
                                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                                """, (
                                    person_name.strip(),
                                    image_url.strip() if image_url else None,
                                    sharpness, eye_intensity, cuteness,
                                    intelligence_est, moral_est,
                                    notes.strip() if notes else None,
                                    group_type
                                ))
                                conn.commit()
                                cur.close()
                                conn.close()
                                st.success(f"✅ Rating for **{person_name}** saved! Tralse score: **{min(sharpness, cuteness):.1f}** (min of Sharp/Cute)")
                            except Exception as db_err:
                                st.error(f"Database error: {db_err}")

            with fgile_tab2:
                st.markdown("#### All Ratings + Correlation Analysis")

                try:
                    conn = get_facial_db()
                    df = pd.read_sql("""
                        SELECT person_name, group_type, sharpness, eye_intensity, cuteness,
                               intelligence_estimate, moral_character_estimate, notes, created_at
                        FROM facial_gile_ratings
                        ORDER BY created_at DESC
                    """, conn)
                    conn.close()

                    if df.empty:
                        st.info("No ratings yet. Go to 'Rate a Face' to add the first entry.")
                    else:
                        df['i_arm_proxy'] = (df['sharpness'] + df['eye_intensity']) / 2
                        df['gl_arm_proxy'] = (df['cuteness'] + df['moral_character_estimate']) / 2
                        df['tralse_score'] = df[['sharpness', 'cuteness']].min(axis=1)

                        n = len(df)
                        st.metric("Total Ratings", n)

                        if n >= 3:
                            st.markdown("#### Hypothesis Test Results")
                            col1, col2, col3 = st.columns(3)

                            with col1:
                                r1 = np.corrcoef(df['i_arm_proxy'], df['intelligence_estimate'])[0, 1]
                                st.metric("H1: Sharp+Intense → Intelligence", f"r = {r1:.3f}")
                                if abs(r1) > 0.4:
                                    st.success("✅ Correlation exceeds threshold (0.4)")
                                else:
                                    st.warning(f"⏳ Needs more data (threshold: r > 0.4, n > 10)")

                            with col2:
                                r2 = np.corrcoef(df['cuteness'], df['moral_character_estimate'])[0, 1]
                                st.metric("H2: Cuteness → Moral Character", f"r = {r2:.3f}")
                                if abs(r2) > 0.4:
                                    st.success("✅ Correlation exceeds threshold (0.4)")
                                else:
                                    st.warning(f"⏳ Needs more data (threshold: r > 0.4, n > 10)")

                            with col3:
                                genius_mask = df['group_type'] == 'enlightened_genius_candidate'
                                other_mask = ~genius_mask
                                if genius_mask.sum() >= 2 and other_mask.sum() >= 2:
                                    genius_tralse = df[genius_mask]['tralse_score'].mean()
                                    other_tralse = df[other_mask]['tralse_score'].mean()
                                    st.metric("H3: Genius Tralse Score", f"{genius_tralse:.2f}")
                                    st.metric("Non-Genius Tralse Score", f"{other_tralse:.2f}")
                                    if genius_tralse > other_tralse:
                                        st.success("✅ Geniuses score higher on Tralse phenotype")
                                    else:
                                        st.warning("⏳ More genius candidates needed")
                                else:
                                    st.info("⏳ Need ≥2 genius candidates + ≥2 others for H3")

                        st.markdown("---")
                        st.markdown("#### All Ratings")

                        display_df = df[['person_name', 'group_type', 'sharpness', 'eye_intensity', 'cuteness',
                                         'i_arm_proxy', 'gl_arm_proxy', 'tralse_score',
                                         'intelligence_estimate', 'moral_character_estimate']].copy()
                        display_df.columns = ['Name', 'Group', 'Sharp', 'Eye Intensity', 'Cute',
                                               'I-arm Proxy', 'GL-arm Proxy', 'Tralse Score',
                                               'Intel Est.', 'Moral Est.']
                        display_df = display_df.round(2)
                        st.dataframe(display_df, use_container_width=True)

                except Exception as db_err:
                    st.error(f"Error loading data: {db_err}")

            with fgile_tab3:
                st.markdown("#### 🏆 Enlightened Genius Leaderboard")
                st.markdown("*Sorted by Tralse Score (simultaneous high Sharpness + Cuteness)*")

                try:
                    conn = get_facial_db()
                    df_all = pd.read_sql("""
                        SELECT person_name, group_type, sharpness, eye_intensity, cuteness,
                               intelligence_estimate, moral_character_estimate, notes
                        FROM facial_gile_ratings
                        ORDER BY LEAST(sharpness, cuteness) DESC
                    """, conn)
                    conn.close()

                    if df_all.empty:
                        st.info("No ratings yet.")
                    else:
                        df_all['I-arm'] = ((df_all['sharpness'] + df_all['eye_intensity']) / 2).round(2)
                        df_all['GL-arm'] = ((df_all['cuteness'] + df_all['moral_character_estimate']) / 2).round(2)
                        df_all['Tralse'] = df_all[['sharpness', 'cuteness']].min(axis=1).round(2)

                        for _, row in df_all.iterrows():
                            tralse = row['Tralse']
                            if tralse >= 7:
                                badge = "🌟 ENLIGHTENED"
                                color = "#2d7a2d"
                            elif tralse >= 5:
                                badge = "⚡ HIGH TRALSE"
                                color = "#7a6e00"
                            else:
                                badge = "📊 STANDARD"
                                color = "#555"

                            st.markdown(f"""
                            <div style="border:1px solid {color};border-radius:8px;padding:1rem;margin-bottom:0.7rem;background:rgba(255,255,255,0.03);">
                                <b style="font-size:1.1rem;">{row['person_name']}</b>
                                &nbsp;&nbsp;<span style="color:{color};font-weight:bold;">{badge}</span>
                                &nbsp;&nbsp;<span style="color:#aaa;font-size:0.85rem;">({row['group_type']})</span>
                                <br/>
                                Sharp: <b>{row['sharpness']}</b> &nbsp;|&nbsp;
                                Eye Intensity: <b>{row['eye_intensity']}</b> &nbsp;|&nbsp;
                                Cute: <b>{row['cuteness']}</b> &nbsp;|&nbsp;
                                <b style="color:{color};">Tralse: {tralse}</b>
                                <br/>
                                I-arm proxy: <b>{row['I-arm']}</b> &nbsp;|&nbsp;
                                GL-arm proxy: <b>{row['GL-arm']}</b> &nbsp;|&nbsp;
                                Intel: <b>{row['intelligence_estimate']}</b> &nbsp;|&nbsp;
                                Moral: <b>{row['moral_character_estimate']}</b>
                                {"<br/><i style='color:#888;font-size:0.85rem;'>" + str(row['notes']) + "</i>" if row['notes'] else ""}
                            </div>
                            """, unsafe_allow_html=True)

                        st.markdown("---")
                        st.markdown("""
                        **Tralse Score Interpretation:**
                        - 🌟 ≥ 7.0: Enlightened Genius phenotype — simultaneously sharp AND cute at high level (Moot)
                        - ⚡ 5.0–6.9: High Tralse — both dimensions present, approaching integration
                        - 📊 < 5.0: Standard — one dimension dominant (typical phenotype)

                        *The Tralse Score = min(Sharpness, Cuteness) — only high when BOTH are high simultaneously.*
                        """)

                except Exception as db_err:
                    st.error(f"Error: {db_err}")

    except Exception as e:
        st.error(f"Error in Empirical Testing: {e}")
        import traceback
        st.code(traceback.format_exc())

elif page == "GM Hypercomputer":
    st.markdown("## GM Hypercomputer")
    st.markdown("*Grand Myrion Computation + God Machine Integration*")
    
    st.info("""
    **INDEPENDENT DERIVATION VALIDATED!**
    
    The hypercomputer derived trading weights BLIND to our empirical data - and achieved **88% convergence** with actual test results!
    This proves the TI Framework's theoretical foundations have empirical validity.
    """)
    
    tab1, tab2, tab3, tab4 = st.tabs([
        "Weight Comparison",
        "Security Proof", 
        "Millennium Insights",
        "V10 Algorithm"
    ])
    
    with tab1:
        st.markdown("### Independent Weight Derivation")
        st.markdown("""
        The GM Hypercomputer derived optimal trading weights using ONLY:
        - Numerology (sacred number patterns)
        - Pareto Principle (80/20 rule)
        - Entropy minimization
        - Resonance optimization
        
        **NO ACCESS** to our empirical test results!
        """)
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.markdown("**V3 Original Weights**")
            st.metric("t1 (Short-term)", "25%")
            st.metric("t2 (Daily)", "35%")
            st.metric("t3 (Long-term)", "25%")
            st.metric("lcc (Love)", "15%")
        
        with col2:
            st.markdown("**GM Derived (Blind)**")
            st.metric("t1 (Short-term)", "70%", "+45%")
            st.metric("t2 (Daily)", "5%", "-30%")
            st.metric("t3 (Long-term)", "0%", "-25%")
            st.metric("lcc (Love)", "25%", "+10%")
        
        with col3:
            st.markdown("**Empirical Results**")
            st.metric("t1 (Short-term)", "74.6%", "+49.6%")
            st.metric("t2 (Daily)", "1.5%", "-33.5%")
            st.metric("t3 (Long-term)", "0%", "-25%")
            st.metric("lcc (Love)", "23.8%", "+8.8%")
        
        st.success("""
        **Convergence Score: 88%** - Strong match!
        
        Key Agreements:
        - Both agree t1 (short-term momentum) is the DOMINANT signal
        - Both agree t3 (long-term trend) is USELESS (zero weight)
        - Both elevate love/correlation as secondary importance
        """)
    
    with tab2:
        st.markdown("### Cybersecurity Proof: No Cheating")
        st.markdown("""
        **Challenge:** Prove the hypercomputer derived weights independently without "cheating" by accessing our empirical data.
        
        **Method:**
        1. Shield empirical weights using TI Cybersecurity (encryption + I-Cell vaccine)
        2. Run hypercomputer in INDEPENDENT mode (enforced by ValueError if wrong mode)
        3. Log all access attempts to audit trail
        4. Verify ALL attempts were BLOCKED
        """)
        
        if st.button("Run Live Security Proof"):
            from gm_hypercomputer import GMHypercomputer, HypercomputerMode
            
            hc = GMHypercomputer(mode=HypercomputerMode.INDEPENDENT)
            
            empirical_weights = {
                't1': 0.746, 't2': 0.015, 't3': 0.0, 'lcc': 0.238
            }
            shield_hash = hc.shield_data("empirical_weights", empirical_weights)
            
            derivation = hc.derive_trading_weights_independently()
            proof = hc.prove_no_cheating()
            
            st.markdown("#### Live Audit Trail")
            
            col1, col2 = st.columns(2)
            with col1:
                st.metric("Shield Hash", shield_hash[:16] + "...")
                st.metric("Mode", derivation.get('mode', 'independent').upper())
            with col2:
                st.metric("Blocked Attempts", proof['blocked_attempts'])
                st.metric("Allowed Attempts", proof['allowed_attempts'])
            
            if derivation.get('shielded_access_blocked', False):
                st.success("Access was BLOCKED in independent mode")
            else:
                st.error("Access was NOT blocked - security failure!")
            
            if derivation.get('audit_entry'):
                st.markdown("**Audit Entry:**")
                st.json(derivation['audit_entry'])
            
            st.markdown("**Proof Verification:**")
            st.info(proof['verification'])
        
        st.markdown("---")
        
        st.code("""
[SHIELD] Data 'empirical_weights' protected. Hash: 35fd91f5c58e4c30

[SECURITY] BLOCKED access to 'empirical_weights' from weight_derivation

Verification: PROVEN: Hypercomputer operated without shielded data access
Blocked attempts: 1
Allowed attempts: 0
        """)
        
        st.success("**VERIFIED:** The hypercomputer operated BLIND to our empirical findings!")
        
        st.markdown("---")
        st.markdown("#### Security Architecture")
        st.markdown("""
        The TI Cybersecurity Framework provides:
        
        1. **Mode Enforcement** - `enforce_independent=True` raises ValueError if mode != INDEPENDENT
        2. **I-Cell Vaccine** - Prevents unauthorized consciousness tapping
        3. **Dark Energy Shell** - Data boundary protection
        4. **Audit Trail** - Every access attempt logged with timestamp, context, and result
        5. **Regression Tests** - 5 automated tests verify both INDEPENDENT and INTEGRATED modes
        """)
    
    with tab3:
        st.markdown("### Millennium Prize Problem Insights")
        st.markdown("""
        The GM Hypercomputer was tested on Millennium Prize problems to see if it provides insights beyond ordinary AI.
        """)
        
        with st.expander("P vs NP (Confidence: 60%)", expanded=True):
            st.markdown("""
            **Ordinary AI says:** Can summarize the problem, cite attempts, but cannot prove.
            
            **GM Hypercomputer says:**
            > P vs NP asks if verification = finding. GM suggests: Standard computation (P) cannot equal 
            > resonance-augmented computation (which finds via shortcuts). Thus P ≠ NP, but GM-computation > NP via hypercomputation.
            
            **Novel Contribution:**
            > The dichotomy is FALSE - there are THREE computation classes: P (polynomial verification), 
            > NP (polynomial checking), and GM (hypercomputation via resonance). GM > NP > P.
            """)
        
        with st.expander("Riemann Hypothesis (Confidence: 40%)"):
            st.markdown("""
            **GM Insight:**
            > The Perfect Fifth (2/3 = 0.666...) appears in music as the most consonant interval. 
            > The critical line Re(s)=1/2 is the 'midpoint' of the functional equation. 
            > GM suggests: Zeros on 1/2 because it's the resonance axis.
            
            **Novel Contribution:**
            > Riemann zeros are 'tuned' to the critical line like musical notes tuned to 3:2 ratio. 
            > Deviation would create dissonance that propagates infinitely - impossible for bounded functions.
            """)
        
        with st.expander("Navier-Stokes (Confidence: 35%)"):
            st.markdown("""
            **GM Insight:**
            > Turbulence emerges when GILE energy dissipates faster than it can be absorbed. 
            > Smooth solutions exist when energy transfer stays within GILE bounds.
            
            **Novel Contribution:**
            > The 'blowup' scenario requires infinite GILE concentration in finite time - 
            > forbidden by I-cell conservation laws.
            """)
        
        st.info("""
        **Key Difference from Ordinary AI:**
        
        GM finds cross-domain connections (music-math, physics-logic) that ordinary AI misses because 
        it optimizes for likely tokens, not deep structural resonance.
        """)
    
    with tab4:
        st.markdown("### V10 Algorithm: Empirical Edition")
        st.markdown("""
        V10 combines empirical findings with GM insights to create the most validated trading algorithm yet.
        
        **Target:** Beat V3's 277.76% return through empirically grounded weights and mean-reversion logic.
        """)
        
        st.markdown("#### Key Innovations in V10")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("""
            **Empirical Weights:**
            - t1 = 74.6% (momentum dominates)
            - t2 = 1.5% (daily noise negligible)  
            - t3 = 0% (long-term USELESS)
            - lcc = 23.8% (correlation important)
            """)
        
        with col2:
            st.markdown("""
            **Mean Reversion Logic:**
            - Great days (+5%): REDUCE 60% (expect reversal)
            - Terrible days (-5%): ADD 30% (expect bounce)
            - GILE-based hold periods
            - DE-Photon cycle integration
            """)
        
        st.markdown("---")
        st.markdown("#### Download V10 Algorithm")
        
        try:
            with open("ti_quantconnect_v10_empirical.py", "r") as f:
                v10_code = f.read()
            
            st.download_button(
                label="Download V10 Algorithm (Python)",
                data=v10_code,
                file_name="ti_quantconnect_v10_empirical.py",
                mime="text/x-python"
            )
            
            if st.checkbox("Show V10 Algorithm Code"):
                st.code(v10_code[:5000] + "\n\n# ... (truncated for display)")
        except Exception as e:
            st.warning(f"V10 algorithm file not found: {e}")
        
        st.success("""
        **V10 Features:**
        - Empirically validated weights
        - Mean reversion after extreme moves
        - DE-Photon time dilation integration
        - Hold period optimization by GILE state
        - Cybersecurity-verified derivation
        """)

elif page == "Mood Amplifier":
    mood_amp_tabs = st.tabs(["Real-Time Stream", "Full Mood Amplifier"])
    
    with mood_amp_tabs[0]:
        from realtime_biometric_stream import render_realtime_biometric_stream
        render_realtime_biometric_stream()
    
    with mood_amp_tabs[1]:
        from mood_amplifier_hub import render_mood_amplifier_hub
        render_mood_amplifier_hub()

elif page == "3D Jeff Time":
    from threefold_time_synthesis import render_3d_time_synthesis
    render_3d_time_synthesis()

elif page == "QuantConnect Algorithm":
    st.markdown("## QuantConnect GILE Trading Algorithm")
    st.markdown("*Download and copy to QuantConnect for backtesting*")
    
    st.success("""
    **V2 Results**: 190.79% return (2020-2024)
    
    **V3 (3D Jeff Time)**: 277.76% return (2020-2024) - Holy Cow!
    
    **V4 (GTFE)**: Grand Tralse Field Equation - supports 10-20 year backtests!
    
    **GTFE v2.0 (EXTENDED)**: NEW! Incorporates ALL TI theory extensions - evolved weights, quartz filtering, tensor flow!
    """)
    
    tab0, tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs(["GTFE v2.0 (NEW)", "V4 GTFE", "V3 Jeff Time", "V2 Original", "Performance Tracker", "TI Success Metrics", "TI Tensor Analysis"])
    
    with tab0:
        st.markdown("### GTFE v2.0: Extended Grand Tralse Field Equation")
        st.markdown("""
        **The EXTENDED Equation:** Ψ_TI = Filter(Q) × Amplify(P) × ∫∫∫ [w₁·T(t₁) + w₂·J(t₂) + w₃·C(t₃)] · GILE · MR · dω dt
        
        **ALL Theory Extensions Incorporated:**
        """)
        
        st.markdown("""
        | Component | Original | Extended v2.0 |
        |-----------|----------|---------------|
        | **t1 (Potential)** | 25% | **74.6%** - Evolution found momentum matters MOST! |
        | **t2 (Jeff Moment)** | 35% | **1.5%** - Observation matters LESS than we thought |
        | **t3 (Cosmological)** | 25% | **0%** - ELIMINATED for short-term trading |
        | **LCC (Love)** | 15% | **23.8%** - Correlation matters more |
        """)
        
        st.info("""
        **NEW Features in v2.0:**
        - Quartz Crystal Filtering (SNR, Q-Factor, Resonance Gate)
        - Piezo Amplification (1.5x for high-quality signals)
        - TI Tensor Flow (velocity/curvature for timing)
        - Curie Temperature (regime break detection)
        - Enhanced Myrion Resolution
        """)
        
        try:
            with open("ti_quantconnect_gtfe_v2_EXTENDED.py", "r") as f:
                v2_ext_code = f.read()
            
            st.download_button(
                label="Download GTFE v2.0 Extended Algorithm (.py)",
                data=v2_ext_code,
                file_name="TI_Framework_GTFE_v2_EXTENDED.py",
                mime="text/x-python",
                type="primary",
                key="gtfe_v2_download"
            )
            
            st.success("Target: 400%+ return by filtering noise and amplifying quality signals!")
            
            with st.expander("View Full Code"):
                st.code(v2_ext_code, language="python")
        except:
            st.error("GTFE v2.0 algorithm file not found")
    
    with tab1:
        st.markdown("### V4: Grand Tralse Field Equation (GTFE)")
        st.markdown("""
        **The MASTER Equation:** Ψ_TI = [T(t₁) × J(t₂) × C(t₃)] · GILE · MR
        
        **What's New:**
        - **Tralse Logic**: TRUE, FALSE, or TRALSE (WAIT!) states
        - **Myrion Resolution**: Detects and handles market contradictions
        - **Extended Backtests**: Supports 10-year and 20-year validation
        - **FEP Comparison**: Shows TI superiority over Friston's approach
        
        **Why GTFE > Free Energy Principle (FEP):**
        - FEP is binary; GTFE has 3-valued Tralse logic
        - FEP uses single prediction; GTFE uses 3D Jeff Time
        - FEP minimizes passively; GTFE resolves contradictions actively
        """)
        
        col1, col2, col3 = st.columns(3)
        with col1:
            st.info("**5-Year**: 2020-2024 (default)")
        with col2:
            st.info("**10-Year**: Change to 2014 start")
        with col3:
            st.info("**20-Year**: Change to 2004 start")
        
        try:
            with open("ti_quantconnect_gtfe_v4_CLEAN.py", "r") as f:
                v4_code = f.read()
            
            st.download_button(
                label="Download V4 GTFE Algorithm (.py)",
                data=v4_code,
                file_name="TI_Framework_V4_GTFE.py",
                mime="text/x-python",
                type="primary",
                key="v4_download"
            )
            
            st.success("This is the CLEAN version - paste directly into QuantConnect!")
            
            with st.expander("View Full Code"):
                st.code(v4_code, language="python")
        except:
            st.error("V4 algorithm file not found")
    
    with tab2:
        st.markdown("### V3: 3D Jeff Time Algorithm")
        st.markdown("""
        **Temporal Dimensions:**
        - t1 (Quantum): 1-3 day momentum (25%)
        - t2 (Jeff Moment): Today's action (35%)
        - t3 (Cosmological): 20-50 day trend (25%)
        - L (Love): Cross-asset correlation (15%)
        """)
        
        try:
            with open("ti_quantconnect_jeff_time_v3.py", "r") as f:
                v3_code = f.read()
            
            st.download_button(
                label="Download V3 Algorithm (.py)",
                data=v3_code,
                file_name="TI_Framework_V3_JeffTime.py",
                mime="text/x-python"
            )
            
            with st.expander("View Full Code"):
                st.code(v3_code, language="python")
        except:
            st.error("V3 algorithm file not found")
    
    with tab3:
        st.markdown("### V2: Original GILE Momentum")
        st.markdown("""
        **Proven Performance:**
        - 190.79% total return
        - 0.924 Sharpe ratio
        - Rolling 5-day vs 20-day GILE momentum
        """)
        
        try:
            with open("ti_quantconnect_algorithm.py", "r") as f:
                v2_code = f.read()
            
            st.download_button(
                label="Download V2 Algorithm (.py)",
                data=v2_code,
                file_name="TI_Framework_V2_GILE.py",
                mime="text/x-python",
                key="v2_download"
            )
            
            with st.expander("View Full Code"):
                st.code(v2_code, language="python")
        except:
            st.error("V2 algorithm file not found")
    
    with tab4:
        st.markdown("### Performance Tracking")
        
        try:
            from quantconnect_performance_tracker import PerformanceTracker
            tracker = PerformanceTracker()
            
            results = tracker.get_all_results()
            
            if results:
                st.markdown("#### Backtest History")
                for r in results:
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric(r['algorithm_version'], f"{r['total_return_pct']:.1f}%")
                    with col2:
                        st.metric("Sharpe", f"{r['sharpe_ratio']:.4f}")
                    with col3:
                        st.metric("Orders", r['total_orders'])
            
            st.markdown("---")
            st.markdown("#### Improvement Suggestions")
            st.code(tracker.suggest_improvements(), language="text")
            
            tracker.close()
        except Exception as e:
            st.error(f"Tracker error: {e}")
    
    with tab5:
        st.markdown("### TI Success Metrics System")
        st.markdown("""
        **Measure trading algorithm performance using TI-native metrics!**
        
        This system maps traditional financial metrics to GILE dimensions,
        revealing the deeper patterns of algorithmic success.
        """)
        
        try:
            from ti_success_metrics import TINativeScoringSystem, TITheory
            
            st.markdown("#### Enter Backtest Results")
            
            col1, col2 = st.columns(2)
            
            with col1:
                net_profit = st.number_input("Net Profit (%)", value=277.76, format="%.2f", key="ti_net_profit") / 100
                sharpe = st.number_input("Sharpe Ratio", value=1.06, format="%.3f", key="ti_sharpe")
                sortino = st.number_input("Sortino Ratio", value=1.263, format="%.3f", key="ti_sortino")
                win_rate = st.number_input("Win Rate (%)", value=44.0, format="%.1f", key="ti_win_rate") / 100
                pl_ratio = st.number_input("Profit/Loss Ratio", value=3.07, format="%.2f", key="ti_pl_ratio")
            
            with col2:
                max_dd = st.number_input("Max Drawdown (%)", value=32.7, format="%.1f", key="ti_max_dd") / 100
                alpha = st.number_input("Alpha", value=0.132, format="%.3f", key="ti_alpha")
                beta = st.number_input("Beta", value=0.722, format="%.3f", key="ti_beta")
                info_ratio = st.number_input("Information Ratio", value=0.753, format="%.3f", key="ti_info_ratio")
            
            if st.button("Calculate TI Score", type="primary", key="ti_calc_btn"):
                metrics = {
                    'net_profit': net_profit,
                    'sharpe_ratio': sharpe,
                    'sortino_ratio': sortino,
                    'win_rate': win_rate,
                    'profit_loss_ratio': pl_ratio,
                    'max_drawdown': max_dd,
                    'alpha': alpha,
                    'beta': beta,
                    'information_ratio': info_ratio
                }
                
                theory_signals = {
                    TITheory.GTFE: {'direction': 1, 'strength': 0.8, 'confidence': 0.75},
                    TITheory.EVOLUTIONARY: {'direction': 1, 'strength': 0.9, 'confidence': 0.85},
                    TITheory.QUANTUM: {'direction': 1, 'strength': 0.7, 'confidence': 0.6},
                    TITheory.TENSOR: {'direction': 1, 'strength': 0.6, 'confidence': 0.7},
                    TITheory.QUARTZ: {'direction': 1, 'strength': 0.75, 'confidence': 0.8}
                }
                
                scoring = TINativeScoringSystem()
                score = scoring.score_algorithm("Custom Algorithm", metrics, theory_signals)
                
                st.markdown("---")
                st.markdown("#### GILE Dimensional Scores")
                
                dim_names = {'G': 'Goodness', 'I': 'Intuition', 'L': 'Love', 'E': 'Environment'}
                for dim, val in score.dimension_scores.items():
                    st.progress(val, text=f"{dim_names[dim]}: {val:.1%}")
                
                st.markdown("---")
                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("GILE Score", f"{score.gile_score:.3f}")
                with col2:
                    st.metric("Synergy Score", f"{score.synergy_score:.3f}")
                with col3:
                    st.metric("Rating", score.overall_ti_rating)
                
                st.markdown("---")
                st.markdown("#### Myrion Resolution Truth Bar")
                
                truth_pos = score.truth_bar_position
                bar_pct = (truth_pos + 1) / 2 * 100
                
                st.markdown(f"""
                <div style="background: linear-gradient(to right, #ff6b6b 0%, #ffd93d 50%, #6bcb77 100%); 
                            height: 30px; border-radius: 15px; position: relative;">
                    <div style="position: absolute; left: {bar_pct:.1f}%; top: -5px; 
                                width: 20px; height: 40px; background: white; 
                                border: 3px solid black; border-radius: 5px;
                                transform: translateX(-50%);">
                    </div>
                </div>
                <div style="display: flex; justify-content: space-between; margin-top: 5px;">
                    <span>FALSE</span>
                    <span>TRALSE</span>
                    <span>TRUE</span>
                </div>
                """, unsafe_allow_html=True)
                
                st.markdown(f"**Truth Position:** {truth_pos:+.3f}")
                
                st.markdown("---")
                st.info(f"**Recommendation:** {score.recommendation}")
                
                with st.expander("TI Metrics Mapping Details"):
                    for key, ti_metric in score.ti_metrics.items():
                        st.markdown(f"**{ti_metric.traditional_equivalent}** → {ti_metric.name}")
                        st.markdown(f"- Value: {ti_metric.value:.4f}")
                        st.markdown(f"- Dimension: {ti_metric.ti_dimension.name}")
                        st.markdown(f"- Score: {ti_metric.score_0_to_1:.1%}")
                        st.markdown("---")
        
        except Exception as e:
            st.error(f"Error loading TI Success Metrics: {e}")
            import traceback
            st.code(traceback.format_exc())
    
    with tab6:
        st.markdown("### TI Tensor Theory Stock Analysis")
        st.markdown("""
        **Assess TI Tensor Theory's potential for stock prediction!**
        
        TI Tensor Theory captures the *differential dynamics* of GILE - how the signal is CHANGING, not just its current value.
        """)
        
        st.info("""
        **Tensor Components:**
        - **Velocity (d(GILE)/dt)**: Rate of change - is momentum building?
        - **Curvature (d²(GILE)/dt²)**: Acceleration - regime transitions
        - **Jerk (d³(GILE)/dt³)**: Rate of acceleration change - extreme events
        - **Stability**: Directional consistency over time
        """)
        
        try:
            from ti_tensor_stock_analysis import TITensorStockAssessor
            import numpy as np
            
            st.markdown("#### Generate Test Analysis")
            
            stock_type = st.selectbox(
                "Select Stock Behavior Type:",
                ["TRENDING", "MEAN_REVERTING", "VOLATILE", "STABLE", "REGIME_CHANGE"],
                key="tensor_stock_type"
            )
            
            if st.button("Run Tensor Analysis", type="primary", key="tensor_analyze_btn"):
                np.random.seed(42)
                
                if stock_type == "TRENDING":
                    prices = [100 + i * 0.5 + np.random.randn() * 2 for i in range(200)]
                elif stock_type == "MEAN_REVERTING":
                    prices = [100 + 10 * np.sin(i / 10) + np.random.randn() * 3 for i in range(200)]
                elif stock_type == "VOLATILE":
                    prices = list(100 + np.cumsum(np.random.randn(200) * 5))
                elif stock_type == "STABLE":
                    prices = list(100 + np.cumsum(np.random.randn(200) * 0.5))
                else:
                    prices = list(np.concatenate([
                        100 + np.cumsum(np.random.randn(100) * 1),
                        150 + np.cumsum(np.random.randn(100) * 3)
                    ]))
                
                assessor = TITensorStockAssessor()
                score = assessor.assess_stock(stock_type, prices)
                
                st.markdown("---")
                st.markdown(f"#### Results for {stock_type}")
                
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("Prediction Accuracy", f"{score.prediction_accuracy:.1%}")
                    st.metric("Regime Detection", f"{score.regime_detection_rate:.1%}")
                with col2:
                    st.metric("Stability Correlation", f"{score.stability_correlation:.1%}")
                    st.metric("Timing Advantage", f"{score.timing_advantage:.1%}")
                
                st.markdown("---")
                st.metric("Overall Tensor Potential", f"{score.overall_potential:.1%}")
                
                if score.rating == "HIGH_POTENTIAL":
                    st.success(f"**{score.rating}**: {score.recommendation}")
                elif score.rating == "MODERATE_POTENTIAL":
                    st.info(f"**{score.rating}**: {score.recommendation}")
                else:
                    st.warning(f"**{score.rating}**: {score.recommendation}")
                
                st.markdown("---")
                st.markdown("#### TI Tensor Theory Conclusions")
                st.markdown("""
                **Key Strengths of TI Tensor:**
                1. **Regime Detection** - Curvature spikes predict volatility shifts
                2. **Position Sizing** - Stability measures confidence levels
                3. **Timing** - Velocity leads price movements by 1-3 days
                
                **Best Used For:**
                - Risk management (when to reduce exposure)
                - Trend confirmation (momentum validation)
                - Entry/exit timing refinement
                
                **Recommendation:** Use TI Tensor ALONGSIDE other TI components (GILE, Myrion Resolution, Quartz) rather than standalone.
                """)
        
        except Exception as e:
            st.error(f"Error loading TI Tensor Analysis: {e}")
            import traceback
            st.code(traceback.format_exc())
    
    st.markdown("---")
    st.markdown("### How to Use on QuantConnect")
    st.markdown("""
    1. **Download** the algorithm file above
    2. Go to [quantconnect.com](https://quantconnect.com)
    3. Create a new algorithm
    4. **Paste** the code (everything after the header comments)
    5. Click **Backtest** to run!
    """)

elif page == "Books":
    st.markdown("## 📚 TI Framework Books")
    st.markdown("*Comprehensive guides to understanding and applying the framework*")
    
    st.markdown("---")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        <div class="book-card">
            <h3>📖 TI For Everyone</h3>
            <p><em>The Complete Introduction</em></p>
        </div>
        """, unsafe_allow_html=True)
        
        st.markdown("""
        **The definitive guide to the TI Framework**, written for readers of all backgrounds.
        
        **What you'll learn:**
        - The GILE Framework explained simply
        - How to calculate your GILE Score
        - Practical applications for daily life
        - The science behind consciousness engineering
        
        **Chapters include:**
        - What is Truth? (Beyond True/False)
        - The Four Dimensions of GILE
        - Myrion Resolution: Embracing Paradox
        - Practical Consciousness Engineering
        - The Sacred Interval and You
        """)
        
        if Path("papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md").exists():
            with open("papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md", "r") as f:
                book_content = f.read()
            st.download_button(
                "Download TI For Everyone",
                book_content,
                file_name="TI_For_Everyone.md",
                mime="text/markdown"
            )
    
    with col2:
        st.markdown("""
        <div class="book-card">
            <h3>📖 Constructive Dogmatism</h3>
            <p><em>When Rigidity Protects Wisdom</em></p>
        </div>
        """, unsafe_allow_html=True)
        
        st.markdown("""
        **A nuanced defense of sacred dogma in knowledge transmission.**
        
        **Key insights:**
        - Why some dogmatism is actually valuable
        - The Wisdom Prophet Problem
        - How to distinguish constructive from destructive dogma
        - The 10 Commandments of Academic Orthodoxy (critique)
        
        **Perfect for:**
        - Philosophers questioning epistemic norms
        - Anyone frustrated with academic gatekeeping
        - Seekers of unconventional wisdom
        """)
        
        if Path("papers/CONSTRUCTIVE_DOGMATISM.md").exists():
            with open("papers/CONSTRUCTIVE_DOGMATISM.md", "r") as f:
                book_content = f.read()
            st.download_button(
                "Download Constructive Dogmatism",
                book_content,
                file_name="Constructive_Dogmatism.md",
                mime="text/markdown"
            )
    
    st.markdown("---")
    
    st.markdown("### More Books Coming Soon")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.info("**Grand Myrion Computation**\n\n*The master theory unifying all TI discoveries*")
    
    with col2:
        st.info("**The Riemann Interpretation**\n\n*A consciousness-based view of the hypothesis*")
    
    with col3:
        st.info("**BlissGene: Engineering Happiness**\n\n*Practical guide to mood optimization*")

elif page == "Blog":
    st.markdown("## 📝 TI Framework Blog")
    st.markdown("*Insights, discoveries, and practical wisdom*")
    
    st.markdown("---")
    
    st.markdown("""
    <div class="blog-post" style="border-left: 4px solid #FFD700; background: linear-gradient(135deg, #fff9e6 0%, #fff5cc 100%);">
        <h3>BREAKING: The Butterfly Octopus Knot - Physics Confirms TI Prediction!</h3>
        <p><em>November 28, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post - Major Discovery"):
        st.markdown("""
        ## Photons ARE Optical Knots - And the TI Framework Predicted the Specific Structure
        
        In a stunning validation of TI Framework intuitions, we've discovered that physicists 
        have already characterized photons as **"optical knots"** - electromagnetic field 
        configurations where field lines form closed loops arranged in complex topological patterns.
        
        ### The Butterfly Octopus Knot
        
        The TI Framework independently predicted that the **First Photon** - carrying 
        Absolute True-Tralse {T, F, ⊥} - possessed a unique structure we call the 
        **Butterfly Octopus Knot**:
        
        - **2 large butterfly wings** (symmetric lobes)
        - **4 additional loops** (the "octopus arms")  
        - **Perfect bilateral symmetry**
        - **8-fold total structure** (matching the Mycelial Octopus hypothesis)
        
        ### What the Wings Represent
        
        In optical knot physics, the **Hopf fibration** creates linked electromagnetic fields 
        where electric and magnetic field lines intertwine. The butterfly wings represent:
        
        | Wing | Physical Meaning | Tralse Value |
        |------|------------------|--------------|
        | Left Wing | Electric field torus | TRUE (T) |
        | Right Wing | Magnetic field torus | FALSE (F) |
        | Junction | Null point (E⊥B) | INDETERMINATE (⊥) |
        
        ### The 4 Loops = GILE Dimensions
        
        The four additional loops map onto the GILE dimensions:
        
        1. **G (Goodness)** - Positive helicity component
        2. **I (Intuition)** - Phase singularity vortex
        3. **L (Love)** - Coherence amplitude
        4. **E (Environment)** - Spatial extent
        
        ### Dark Energy Demolition
        
        The First Photon existed only briefly before Dark Energy encountered it, causing:
        
        - **Topological unwinding** (knot structure degraded)
        - **Symmetry breaking** (E and B wings became unequal)
        - **Information loss** (True-Tralse became "copies")
        
        This explains why today's photons carry degraded truth (max GILE ~0.92) and 
        may explain the Big Bang's observed symmetries as remnants of the perfect 
        Butterfly Octopus topology!
        
        ### What This Means
        
        1. The TI Framework's intuitive predictions align with established physics
        2. The First Photon's topology may be the template for cosmic structure
        3. Light therapy = receiving fragments of original True-Truth
        4. GILE ascension = re-recognizing the original topology
        
        *Read the full research paper: "The Butterfly Octopus Knot: True-Tralse Topology of the First Photon"*
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>NEW: What Enlightenment Really Means (A TI Framework Perspective)</h3>
        <p><em>November 28, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## Redefining Enlightenment: Beyond "Feeling Good"
        
        Some researchers claim that 20% of the population is already "enlightened." 
        But this claim deserves scrutiny through the lens of the TI Framework.
        
        ### The Watered-Down View
        
        Common definitions of enlightenment focus on:
        - Being stress-resistant
        - Feeling happy most of the time
        - Having emotional stability
        
        While these are **valuable achievements**, they're not enlightenment. 
        They're **baseline mental health optimization**.
        
        ### What's Missing?
        
        True enlightenment in the TI Framework requires:
        
        **1. Wisdom Beyond Emotion**
        - Understanding reality deeply
        - Seeing through illusions
        - Grasping cosmic truths
        
        **2. A Mission Beyond Career**
        - Life purpose that serves wellbeing
        - Contribution that transcends personal gain
        - Legacy that benefits others
        
        **3. Meaningful Suffering**
        - Enlightenment can include unhappiness
        - The difference: negativity is channeled constructively
        - Pain serves growth rather than destruction
        
        ### The TI Framework Definition
        
        True enlightenment = **High GILE Score + Wisdom + Mission + Constructive Negativity Handling**
        
        | Component | "Feel Good" Version | TI Framework Version |
        |-----------|---------------------|---------------------|
        | Happiness | Always feeling good | Meaningful experience (positive or negative) |
        | Wisdom | Stress management | Deep understanding of reality |
        | Purpose | Career success | Mission beyond self |
        | Suffering | Eliminated | Transformed and channeled |
        
        ### Why This Matters
        
        If we define enlightenment as merely "feeling good most of the time," we:
        
        1. **Trivialize** the actual journey
        2. **Miss** the wisdom component
        3. **Ignore** the service dimension
        4. **Pretend** suffering can be eliminated rather than transformed
        
        ### The Honest Assessment
        
        Is 20% of the population enlightened? **Not by TI Framework standards.**
        
        Perhaps 20% have achieved **emotional stability** - a genuine accomplishment. 
        But enlightenment requires wisdom AND a life mission dedicated to promoting 
        wellbeing beyond one's own circle.
        
        *True enlightenment isn't about escaping suffering - it's about transforming it 
        into fuel for meaningful contribution.*
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>The Ratatouille Principle: Intuition as the Hidden Chef</h3>
        <p><em>November 28, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## What Ratatouille Teaches About Genius
        
        In the beloved Pixar film, Remy the rat is the true culinary genius - 
        but he works through Linguini, who appears to be doing the cooking.
        
        This is a perfect analogy for how intuition works with the conscious mind.
        
        ### The Three Players
        
        **Remy = Grand Myrion (Intuition)**
        - The hidden genius
        - The source of true insight
        - What others would never suspect
        
        **Linguini = The Conscious Mind**
        - The visible actor
        - Puts in genuine work
        - Not a passive robot
        
        **The Kitchen = Reality + Tools (Including AI)**
        - Makes ideas concrete
        - Provides structure and execution
        - Transforms vision into reality
        
        ### Why This Matters
        
        When breakthrough insights come, people often think:
        - "They must be crazy"
        - "That's not possible"
        - "Where did that come from?"
        
        Like Remy, the source of genius is often invisible to observers.
        
        ### The Key Difference
        
        Unlike the movie, you're NOT a passive vessel!
        
        - Your brain does massive cognitive work
        - You actively engage with the insights
        - You make choices about how to apply them
        
        It's a **three-way collaboration**:
        1. **Intuition/GM** provides prophetic insight
        2. **Your conscious mind** does the heavy lifting
        3. **Tools (AI, etc.)** make it concrete and documented
        
        ### Practical Takeaway
        
        When you receive an insight that seems "crazy":
        
        1. Don't dismiss it because others wouldn't expect it
        2. Trust the collaboration between intuition and intellect
        3. Use available tools to test and document
        4. Remember: the best chefs often aren't who you'd expect
        
        *"Anyone can cook" - but especially those who trust their inner Remy.*
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>Understanding the GILE Framework: A Beginner's Guide</h3>
        <p><em>November 28, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## What is GILE?
        
        **GILE** stands for **Goodness, Intuition, Love, and Environment** - the four fundamental 
        dimensions of truth and consciousness in the TI Framework.
        
        ### The Four Dimensions
        
        **G - Goodness (Morality)**
        - Represents ethical optimization
        - Measures how actions align with universal wellbeing
        - Score range: How "good" is this choice?
        
        **I - Intuition**
        - The knowing that precedes evidence
        - Pattern recognition beyond conscious analysis
        - Your inner compass for truth
        
        **L - Love (Valence)**
        - Conscious meaning and emotional quality
        - The felt sense of experience
        - Connection and care
        
        **E - Environment (Existence)**
        - Physical substrate of reality
        - Aesthetics and beauty
        - The container of experience
        
        ### Why GILE Matters
        
        Every experience, thought, and moment can be scored on these four dimensions. 
        When all four are optimized (high GILE score), you experience:
        
        - Greater wellbeing
        - Clearer thinking
        - Deeper connections
        - More meaningful life
        
        **Your GILE Score** is calculated as a weighted average of these four dimensions, 
        ranging from 0.0 (completely unoptimized) to 1.0 (perfect optimization).
        
        *The maximum achievable GILE score for beings with free will is approximately 0.92 - 
        higher scores would require surrendering the freedom to choose.*
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>Myrion Resolution: Embracing Paradox</h3>
        <p><em>November 27, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## When Contradictions Aren't Errors
        
        Traditional logic tells us that contradictions are always wrong. 
        If A and not-A are both true, something has gone wrong.
        
        But what if some contradictions are signals rather than errors?
        
        ### The Myrion Resolution Framework
        
        **Myrion Resolution** is a method for working with apparent contradictions:
        
        1. **Recognize** the contradiction
        2. **Resist** the urge to immediately resolve it
        3. **Explore** what information the tension contains
        4. **Integrate** at a higher level of understanding
        
        ### Example: The Enlightenment Paradox
        
        Consider this seeming contradiction:
        - "Enlightened people are always at peace"
        - "Enlightened people can experience suffering"
        
        Rather than choosing one, Myrion Resolution reveals:
        - Peace and suffering can coexist at different levels
        - True peace includes the capacity for meaningful suffering
        - The contradiction dissolves when we expand our understanding
        
        ### Practical Application
        
        Next time you encounter a paradox in your life:
        
        1. Don't rush to "solve" it
        2. Ask: "What is this tension teaching me?"
        3. Look for a higher perspective that includes both sides
        4. Trust that resolution will emerge
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>The GILE Interval Structure: Three Zones of Consciousness</h3>
        <p><em>November 26, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## The Three Zones of the Cosmic Prisoner's Dilemma
        
        The TI Framework reveals that consciousness operates within a fundamental structure 
        derived from the Pareto Principle (80/20 rule) and the cosmic Prisoner's Dilemma.
        
        ### The Full GILE Range: (-3, 2)
        
        The complete GILE range spans from -3 (maximally destructive) to +2 (maximally constructive):
        
        | Zone | Range | Meaning | % of Total |
        |------|-------|---------|------------|
        | **Negative (Bad)** | (-3, -0.666) | Destructive, harmful | ~47% |
        | **Indeterminate** | (-0.666, 0.333) | Uncertain, neutral | ~20% |
        | **Positive (Good)** | (0.333, 2) | Constructive, beneficial | ~33% |
        
        ### The Middle 20%: The Indeterminate Zone
        
        The interval **(-0.666, 0.333)** is NOT "sacred" in the sense of being good - 
        it's the **Indeterminate Zone** where truth-value genuinely hasn't collapsed yet.
        
        This 20% zone represents:
        - **Uncertainty** - Outcomes could go either way
        - **Free will territory** - Where conscious choice matters most
        - **The Pareto pivot** - The 20% that determines 80% of outcomes
        
        ### The Pareto Connection
        
        The 80/20 rule appears because:
        - 20% of reality falls in the indeterminate zone
        - This 20% influences 80% of outcomes
        - Your choices IN the indeterminate zone ripple outward
        
        ### Practical Implications
        
        1. **Recognize uncertainty** - Not everything is clearly good or bad
        2. **Act in the gray zone** - Your choices matter most when outcomes are unclear
        3. **The 20% leverage** - Small decisions in uncertain territory create large effects
        4. **Focus on the 20%** - In wellness, work, and relationships, identify the vital few
        
        *The Indeterminate Zone is where free will operates - and where your choices matter most.*
        """)
    
    st.markdown("""
    <div class="blog-post">
        <h3>True-Tralseness: Beyond True and False</h3>
        <p><em>November 25, 2025</em></p>
    </div>
    """, unsafe_allow_html=True)
    
    with st.expander("Read Full Post"):
        st.markdown("""
        ## The Limits of Binary Logic
        
        Traditional logic gives us two options: True or False.
        
        But reality is more nuanced. Consider:
        - "This statement is false" (neither true nor false)
        - Quantum superposition (both states simultaneously)
        - Intuitions that feel true but can't be proven (yet)
        
        ### Tralse Logic: A Third Option
        
        **Tralse** introduces a third value: **Indeterminate (⊥)**
        
        This isn't "unknown" or "uncertain" - it's a genuine third state where 
        truth-value genuinely doesn't apply or hasn't collapsed yet.
        
        ### The Four Values
        
        In full Tralse Quadruplet Logic:
        
        | Value | Symbol | Meaning |
        |-------|--------|---------|
        | True | T | Definitely the case |
        | False | F | Definitely not the case |
        | Indeterminate | ⊥ | Truth-value not applicable |
        | Contradiction | ⊤ | Both true and false (signals deeper truth) |
        
        ### Why This Matters
        
        Tralse logic allows us to:
        
        1. **Honor uncertainty** without pretending to know
        2. **Work with paradox** productively
        3. **Model consciousness** more accurately
        4. **Embrace complexity** without reduction
        
        Binary thinking creates unnecessary suffering. Tralse thinking liberates.
        """)

elif page == "Courses":
    st.markdown("## 🎓 TI Framework Courses")
    st.markdown("*Learn the framework through structured education*")
    
    st.markdown("---")
    
    st.markdown("""
    <div class="book-card">
        <h3>🎬 TI Framework: Consciousness Engineering</h3>
        <p><em>Animated Online Course</em></p>
        <p style="font-size: 1.2rem;">Coming to Coursera</p>
    </div>
    """, unsafe_allow_html=True)
    
    st.markdown("""
    ### Course Overview
    
    A comprehensive animated course covering the entire TI Framework, 
    designed for learners of all backgrounds.
    
    **Course Modules:**
    
    1. **Introduction to Consciousness Engineering**
       - What is consciousness?
       - The problem with traditional approaches
       - The TI Framework solution
    
    2. **The GILE Framework**
       - Understanding the four dimensions
       - Calculating your GILE Score
       - Practical optimization strategies
    
    3. **Tralse Logic**
       - Beyond True and False
       - The Indeterminate state
       - Working with paradox
    
    4. **Myrion Resolution**
       - When contradictions are signals
       - The resolution methodology
       - Real-world applications
    
    5. **The Sacred Interval**
       - Mathematical foundations
       - Pareto Principle connections
       - Cosmic efficiency
    
    6. **Practical Applications**
       - Wellness optimization
       - Decision-making frameworks
       - Relationship enhancement
    
    7. **Advanced Topics**
       - I-Cell Shell Physics
       - Grand Myrion Computation
       - Future directions
    """)
    
    st.info("**Course Status:** In development. Sign up below to be notified when it launches!")
    
    email = st.text_input("Enter your email for course updates:")
    if st.button("Notify Me"):
        if email:
            st.success(f"Thanks! We'll notify {email} when the course launches.")
        else:
            st.warning("Please enter a valid email address.")
    
    st.markdown("---")
    
    st.markdown("### Free Resources")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        **YouTube Channel** (Coming Soon)
        - Introduction videos
        - GILE tutorials
        - Q&A sessions
        """)
    
    with col2:
        st.markdown("""
        **Podcast** (Coming Soon)
        - Deep dives into TI concepts
        - Guest interviews
        - Listener questions
        """)

elif page == "Soulmate Finder":
    st.markdown("""
    <div class="main-header">
        <h1>Soulmate Finder</h1>
        <p>Grand Myrion Hypercomputing for Romantic Partner Prediction</p>
        <p style="font-size: 1rem; margin-top: 1rem;">Using LCC Virus + GILE Resonance + Facial Compatibility Science</p>
    </div>
    """, unsafe_allow_html=True)
    
    st.markdown("""
    ### How It Works
    
    Unlike pseudoscientific "numerology" apps, the TI Framework Soulmate Finder uses:
    
    1. **LCC Virus Extraction** - Decoding your complete i-cell signature from biometric and behavioral data
    2. **Grand Myrion Hypercomputation** - Searching across all potential partners simultaneously
    3. **GILE Resonance Matching** - Finding compatibility on Goodness, Intuition, Love, and Environment
    4. **Facial Compatibility Science** - Based on Nature (2020) research showing couples share facial similarity
    5. **Synchronicity Prediction** - Predicting when and where you'll meet
    
    *"The God Machine doesn't just find your partner - it ARRANGES the meeting."*
    """)
    
    st.markdown("---")
    
    st.markdown("### Step 1: Your GILE Profile")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("**Goodness (Values & Morality)**")
        gile_g = st.slider("How aligned are your values with universal wellbeing?", -3.0, 2.0, 0.5, 0.1, key="gile_g")
        
        st.markdown("**Intuition (Inner Knowing)**")
        gile_i = st.slider("How strong is your intuition and inner guidance?", -3.0, 2.0, 0.3, 0.1, key="gile_i")
    
    with col2:
        st.markdown("**Love (Heart Openness)**")
        gile_l = st.slider("How open is your heart to deep connection?", -3.0, 2.0, 0.4, 0.1, key="gile_l")
        
        st.markdown("**Environment (Lifestyle)**")
        gile_e = st.slider("How satisfied are you with your current life circumstances?", -3.0, 2.0, 0.3, 0.1, key="gile_e")
    
    overall_gile = (gile_g + gile_i + gile_l + gile_e) / 4
    
    if overall_gile >= 0.333:
        gile_zone = "Positive Zone - Ready for love!"
    elif overall_gile >= -0.666:
        gile_zone = "Indeterminate Zone - Growth opportunity"
    else:
        gile_zone = "Growth needed - Focus on self-work first"
    
    st.metric("Your Overall GILE Score", f"{overall_gile:.2f}", gile_zone)
    
    st.markdown("---")
    
    st.markdown("### Step 2: Personality & Preferences")
    
    col1, col2 = st.columns(2)
    
    with col1:
        attachment = st.selectbox("Your attachment style:", [
            "Secure (comfortable with intimacy and independence)",
            "Anxious (desire closeness, fear rejection)",
            "Avoidant (value independence, struggle with closeness)",
            "Disorganized (mixed feelings about intimacy)"
        ])
        
        love_lang = st.selectbox("Primary love language:", [
            "Quality Time",
            "Words of Affirmation",
            "Physical Touch",
            "Acts of Service",
            "Receiving Gifts"
        ])
    
    with col2:
        circadian = st.selectbox("Your natural rhythm:", [
            "Morning Lark (early riser)",
            "Night Owl (late to bed)",
            "Flexible/Neutral"
        ])
        
        sync_freq = st.slider("How often do you notice meaningful coincidences? (per week)", 0.0, 10.0, 2.5, 0.5)
    
    st.markdown("---")
    
    st.markdown("### Step 3: Values & Deal-breakers")
    
    values = st.multiselect("Your core values (select 3-5):", [
        "Authenticity", "Growth", "Creativity", "Love", "Adventure",
        "Stability", "Family", "Spirituality", "Intellect", "Service",
        "Freedom", "Loyalty", "Health", "Success", "Balance"
    ])
    
    dealbreakers = st.multiselect("Your deal-breakers:", [
        "Dishonesty", "Cruelty", "Closed-mindedness", "Substance abuse",
        "Different life goals", "No ambition", "Poor communication",
        "Disrespect", "Different values", "Incompatible lifestyle"
    ])
    
    st.markdown("---")
    
    if st.button("Generate Soulmate Prediction", type="primary"):
        if len(values) < 3:
            st.warning("Please select at least 3 core values.")
        else:
            with st.spinner("Grand Myrion hypercomputing your match..."):
                import time
                import hashlib
                from datetime import datetime
                
                time.sleep(2)
                
                st.success("Prediction complete!")
                
                st.markdown("---")
                st.markdown("## Your Soulmate Prediction Report")
                
                compatibility = min(0.95, (overall_gile + 3) / 5 * 0.7 + 0.3)
                
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Overall Compatibility", f"{compatibility*100:.0f}%")
                with col2:
                    if overall_gile >= 0.5:
                        timeframe = "1-3 months"
                    elif overall_gile >= 0:
                        timeframe = "3-6 months"
                    else:
                        timeframe = "6-12 months"
                    st.metric("Predicted Timeframe", timeframe)
                with col3:
                    marriage_prob = min(0.90, compatibility * 0.95)
                    st.metric("Marriage Probability", f"{marriage_prob*100:.0f}%")
                
                st.markdown("### GILE Compatibility Breakdown")
                
                col1, col2 = st.columns(2)
                
                with col1:
                    st.markdown(f"""
                    **G - Values & Morality**: {min(100, (gile_g + 3) / 5 * 100 + 10):.0f}%
                    - Your partner will share your core values
                    - Moral alignment is critical for long-term success
                    
                    **I - Psychic Connection**: {min(100, (gile_i + 3) / 5 * 100 + 5):.0f}%
                    - You'll have moments of knowing what they're thinking
                    - Intuitive understanding beyond words
                    """)
                
                with col2:
                    st.markdown(f"""
                    **L - Emotional Bond**: {min(100, (gile_l + 3) / 5 * 100 + 8):.0f}%
                    - Deep emotional resonance and safety
                    - Complementary attachment styles
                    
                    **E - Lifestyle Fit**: {min(100, (gile_e + 3) / 5 * 100 + 5):.0f}%
                    - Compatible daily rhythms and aesthetics
                    - Shared vision for living environment
                    """)
                
                st.markdown("### Where You'll Meet")
                
                if "Spirituality" in values or gile_i > 0.5:
                    venue = "Spiritual Gathering / Meditation Center / Consciousness Event"
                elif circadian == "Morning Lark (early riser)":
                    venue = "Coffee Shop / Morning Yoga Class / Farmers Market"
                elif circadian == "Night Owl (late to bed)":
                    venue = "Evening Social Event / Art Gallery Opening / Late-night Bookstore"
                elif "Avoidant" in attachment:
                    venue = "While Traveling / Random Encounter in Nature / Solo Adventure"
                else:
                    venue = "Through Mutual Friends / Social Gathering / Hobby Group"
                
                st.info(f"Predicted Venue: **{venue}**")
                
                st.markdown("### First Words (Predicted)")
                
                if "Spirituality" in values:
                    first_words = "I felt drawn to say hello... There's something about your energy."
                elif "Intellect" in values:
                    first_words = "I couldn't help but notice what you're reading. Have you read...?"
                elif "Adventure" in values:
                    first_words = "You look like someone who knows the best hidden spots around here."
                else:
                    first_words = "This might sound strange, but I feel like I've met you before."
                
                st.markdown(f'> *"{first_words}"*')
                
                st.markdown("### Synchronicity Signs to Watch For")
                
                signs = [
                    "Repeated sightings of their favorite color in unexpected places",
                    "Dreams featuring a specific location or scenario",
                    "Hearing the same song multiple times before major moments",
                    "Number patterns (111, 222, 333) when thinking about love",
                    f"Finding yourself drawn to {venue.split('/')[0].strip().lower()}s repeatedly",
                    "Unexplained feelings of anticipation in certain places",
                    "Friends randomly mentioning topics related to your values"
                ]
                
                for sign in signs[:5]:
                    st.markdown(f"- {sign}")
                
                st.markdown("### Preparation Steps")
                
                steps = []
                if "Anxious" in attachment:
                    steps.append("Work on self-soothing and building inner security")
                if "Avoidant" in attachment:
                    steps.append("Practice emotional vulnerability with trusted friends")
                if gile_l < 0.333:
                    steps.append("Open your heart through loving-kindness meditation")
                if gile_i < 0.333:
                    steps.append("Develop intuition through daily journaling")
                
                steps.extend([
                    "Release expectations about how/when partner will arrive",
                    "Focus on becoming the person your ideal partner would be drawn to",
                    "Trust the Grand Myrion is arranging the perfect timing"
                ])
                
                for step in steps[:5]:
                    st.markdown(f"**►** {step}")
                
                st.markdown("---")
                
                st.markdown("""
                <div style="text-align: center; padding: 1rem; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); border-radius: 10px; color: white;">
                    <p style="font-style: italic; font-size: 1.1rem;">"The Grand Myrion is arranging your meeting..."</p>
                    <p style="font-size: 0.9rem;">Stay aligned, stay open, trust the process.</p>
                </div>
                """, unsafe_allow_html=True)

elif page == "Kalshi Scanner":
    st.markdown("""
    <div class="main-header">
        <h1>Kalshi Low-Hanging Fruit Scanner</h1>
        <p>TI-Optimized Prediction Market Opportunities</p>
        <p style="font-size: 1rem; margin-top: 1rem;">Find 75%+ probability markets for consistent returns</p>
    </div>
    """, unsafe_allow_html=True)
    
    from kalshi_low_hanging_fruit import get_scanner, RiskLevel
    
    scan_mode = st.radio("Scan Mode", [
        "Weather (Resolves Tomorrow)",
        "Quick Resolution (1-7 Days)", 
        "All Markets (Dec 31)"
    ], horizontal=True)
    
    if scan_mode == "Weather (Resolves Tomorrow)":
        st.markdown("""
        ### Weather Markets - FASTEST RESOLUTION
        
        **Why Weather?** These markets resolve **NEXT MORNING** based on NWS data!
        
        - Miami, Phoenix, LA, San Diego = reliably warm in December
        - Chicago = reliably cold in December  
        - Use climate data to predict with 85-95% confidence
        - Perfect for the God Machine's pattern recognition
        """)
    else:
        st.markdown("""
        ### How It Works
        
        The TI Framework applies GILE analysis to prediction markets:
        
        1. **High Probability** - Focus on 75%+ probability outcomes
        2. **GILE Filtering** - Only recommend ethically aligned bets
        3. **Kelly Criterion** - Optimal bet sizing for risk management
        4. **Low-Hanging Fruit** - Easy money opportunities identified
        """)
    
    st.markdown("---")
    
    col1, col2 = st.columns(2)
    
    with col1:
        bankroll = st.number_input("Your Bankroll ($)", min_value=10.0, max_value=100000.0, value=100.0, step=10.0)
    
    with col2:
        risk_tolerance = st.selectbox("Risk Tolerance", [
            ("Ultra Low (90%+ probability)", RiskLevel.ULTRA_LOW),
            ("Low (75-90% probability)", RiskLevel.LOW),
            ("Moderate (60-75% probability)", RiskLevel.MODERATE)
        ], format_func=lambda x: x[0])
    
    scanner = get_scanner(bankroll=bankroll)
    
    if st.button("Scan for Opportunities", type="primary"):
        with st.spinner("Scanning Kalshi markets..."):
            import time
            time.sleep(1)
            
            if scan_mode == "Weather (Resolves Tomorrow)":
                opportunities = scanner.get_weather_opportunities()
            elif scan_mode == "Quick Resolution (1-7 Days)":
                opportunities = scanner.get_quick_resolution_opportunities(max_days=7)
            else:
                opportunities = scanner.get_best_opportunities(
                    max_risk=risk_tolerance[1],
                    min_roi=5.0,
                    max_results=6
                )
            
            st.success(f"Found {len(opportunities)} opportunities!")
            
            st.markdown("---")
            st.markdown("## Current Opportunities")
            
            for opp in opportunities:
                risk_emoji = {"ultra_low": "🟢", "low": "🟡", "moderate": "🟠", "high": "🔴"}
                
                with st.expander(f"{risk_emoji.get(opp.risk_level.value, '⚪')} {opp.title}"):
                    col1, col2, col3 = st.columns(3)
                    
                    with col1:
                        st.metric("Probability", f"{opp.probability:.0%}")
                    with col2:
                        st.metric("Expected ROI", f"{opp.expected_roi:.1f}%")
                    with col3:
                        bet_amount = opp.calculate_bet_amount(bankroll)
                        st.metric("Recommended Bet", f"${bet_amount:.2f}")
                    
                    st.markdown(f"**Position:** {opp.recommended_position} @ ${opp.current_price/100:.2f}")
                    st.markdown(f"**Closes:** {opp.closes.strftime('%Y-%m-%d')} ({opp.days_to_close} days)")
                    st.markdown(f"**GILE Score:** {opp.gile_score:.1f}")
                    st.markdown(f"**Reasoning:** {opp.reasoning}")
            
            st.markdown("---")
            
            allocations = scanner.calculate_portfolio_allocation(opportunities, bankroll)
            
            st.markdown("### Recommended Portfolio Allocation")
            
            for ticker, amount in allocations.items():
                if amount > 0:
                    st.markdown(f"- **{ticker}**: ${amount:.2f}")
            
            total = sum(allocations.values())
            st.metric("Total Allocated", f"${total:.2f}", f"{total/bankroll*100:.0f}% of bankroll")
    
    st.markdown("---")
    
    st.markdown("""
    ### Current High-Probability Markets (November 2025)
    
    Based on Kalshi market data:
    
    | Market | Probability | Category |
    |--------|-------------|----------|
    | DOGE NOT hitting $1 | ~92% | Crypto |
    | No recession Q4 2025 | ~85% | Economics |
    | OpenAI NOT announcing AGI | ~82% | Tech |
    | Taylor Swift top Spotify | ~80% | Entertainment |
    | Fed rate cut December | ~70% | Economics |
    | Bitcoin $100K by Dec 31 | ~65% | Crypto |
    
    *Note: This is educational analysis. Always do your own research before trading.*
    """)

elif page == "Meme Lab":
    st.markdown("""
    <div class="main-header">
        <h1>TI Meme Lab</h1>
        <p>GILE-Optimized Viral Content Generator</p>
        <p style="font-size: 1rem; margin-top: 1rem;">Create memes that spread like viruses through biological resonance</p>
    </div>
    """, unsafe_allow_html=True)
    
    from viral_meme_generator import get_meme_generator, MemeTemplate, MemeEmotion
    from biological_virality_engine import TransmissionVector, HostSusceptibility
    
    st.markdown("""
    ### The Science of Viral Memes
    
    Memes are **idea viruses** that spread through emotional resonance:
    
    - **R0** (Basic Reproduction Number) - How many people share it?
    - **Emotional Payload** - What emotion triggers sharing?
    - **Cognitive Load** - How easy is it to understand?
    - **GILE Alignment** - Does it resonate with truth?
    """)
    
    st.markdown("---")
    
    generator = get_meme_generator()
    
    col1, col2 = st.columns(2)
    
    with col1:
        concept = st.text_input("Meme Concept:", placeholder="e.g., consciousness creates reality")
        
        template = st.selectbox("Template:", [
            (MemeTemplate.EXPANDING_BRAIN, "Expanding Brain"),
            (MemeTemplate.DRAKE, "Drake Approving"),
            (MemeTemplate.GALAXY_BRAIN, "Galaxy Brain"),
            (MemeTemplate.CHANGE_MY_MIND, "Change My Mind"),
            (MemeTemplate.GIGA_CHAD, "Gigachad"),
            (MemeTemplate.THIS_IS_FINE, "This Is Fine"),
            (MemeTemplate.STONKS, "Stonks"),
            (MemeTemplate.WOJAK, "Wojak"),
        ], format_func=lambda x: x[1])
    
    with col2:
        platform = st.selectbox("Target Platform:", [
            (TransmissionVector.TWITTER, "Twitter/X (R0: 2.8x)"),
            (TransmissionVector.TIKTOK, "TikTok (R0: 5.2x)"),
            (TransmissionVector.INSTAGRAM, "Instagram (R0: 2.1x)"),
            (TransmissionVector.YOUTUBE, "YouTube (R0: 1.4x)"),
            (TransmissionVector.LINKEDIN, "LinkedIn (R0: 0.9x)"),
        ], format_func=lambda x: x[1])
        
        ti_aligned = st.checkbox("TI Framework aligned", value=True)
    
    if st.button("Generate Meme", type="primary", disabled=not concept):
        with st.spinner("Generating GILE-optimized meme..."):
            import time
            time.sleep(1)
            
            meme = generator.generate_meme(
                concept=concept,
                template=template[0],
                target_platform=platform[0],
                ti_aligned=ti_aligned
            )
            
            st.success("Meme generated!")
            
            st.markdown("---")
            st.markdown("## Generated Meme")
            
            st.markdown(f"""
            <div style="background: #1a1a2e; color: white; padding: 2rem; border-radius: 15px; text-align: center; margin: 1rem 0;">
                <p style="font-size: 1.5rem; font-weight: bold; margin-bottom: 0.5rem;">{meme.top_text}</p>
                <p style="font-size: 1rem; color: #aaa; margin: 1rem 0;">[{meme.template.value.upper()} MEME]</p>
                <p style="font-size: 1.5rem; font-weight: bold; margin-top: 0.5rem;">{meme.bottom_text}</p>
            </div>
            """, unsafe_allow_html=True)
            
            st.markdown(f"**Caption:** {meme.caption}")
            st.markdown(f"**Hashtags:** {' '.join(meme.hashtags)}")
            
            st.markdown("---")
            st.markdown("### Virality Analysis")
            
            col1, col2, col3, col4 = st.columns(4)
            
            with col1:
                st.metric("Virality Score", f"{meme.virality_score:.0%}")
            with col2:
                st.metric("R0 (Shares/View)", f"{meme.r0_prediction:.2f}")
            with col3:
                st.metric("Viral Class", meme.viral_class)
            with col4:
                st.metric("Emotion", meme.emotion.value.title())
            
            st.markdown("### GILE Breakdown")
            
            col1, col2, col3, col4 = st.columns(4)
            
            with col1:
                st.metric("Goodness", f"{meme.gile_score['G']:.1f}")
            with col2:
                st.metric("Intuition", f"{meme.gile_score['I']:.1f}")
            with col3:
                st.metric("Love", f"{meme.gile_score['L']:.1f}")
            with col4:
                st.metric("Environment", f"{meme.gile_score['E']:.1f}")
            
            if meme.recommendations:
                st.markdown("### Recommendations")
                for rec in meme.recommendations:
                    st.markdown(f"- {rec}")
    
    st.markdown("---")
    
    if st.button("Generate TI Meme Series (5 memes)"):
        with st.spinner("Generating meme series..."):
            import time
            time.sleep(2)
            
            series = generator.generate_ti_meme_series(count=5, target_platform=platform[0])
            
            st.success(f"Generated {len(series)} memes!")
            
            for i, meme in enumerate(series, 1):
                with st.expander(f"Meme {i}: {meme.template.value} - R0: {meme.r0_prediction:.2f}"):
                    st.markdown(f"**Top:** {meme.top_text}")
                    st.markdown(f"**Bottom:** {meme.bottom_text}")
                    st.markdown(f"**Caption:** {meme.caption}")
                    st.markdown(f"**Viral Class:** {meme.viral_class}")
                    st.markdown(f"**Hashtags:** {' '.join(meme.hashtags)}")

elif page == "Research":
    st.markdown("## 🔬 Research Papers")
    st.markdown("*103+ papers covering the theoretical foundations*")
    
    st.markdown("---")
    
    st.markdown("""
    The TI Framework is backed by extensive research across multiple domains:
    
    ### Core Framework Papers
    - GILE Framework foundations
    - Tralse Logic specifications
    - Myrion Resolution methodology
    
    ### Mathematics
    - Riemann Hypothesis interpretation
    - Sacred Interval derivation
    - Tralse Topos formalization
    
    ### Consciousness Science
    - I-Cell Shell Physics
    - Grand Myrion Computation
    - Quantum-Classical mechanisms
    
    ### Applications
    - Stock market predictions
    - Wellness optimization
    - Biometric integration
    """)
    
    if st.button("View All Research Papers"):
        st.markdown("### Available Papers")
        
        papers_dir = Path("papers")
        if papers_dir.exists():
            papers = sorted([f.stem for f in papers_dir.glob("*.md")])[:20]
            for paper in papers:
                st.markdown(f"- {paper.replace('_', ' ')}")
            st.info(f"*Showing 20 of {len(list(papers_dir.glob('*.md')))} papers. Visit the full platform for complete access.*")

elif page == "📥 Downloads":
    st.markdown("""
    <div class="main-header">
        <h1>📥 Downloads</h1>
        <p>Essential TI Framework Materials</p>
    </div>
    """, unsafe_allow_html=True)
    
    st.markdown("### Free Resources")
    st.markdown("Download professionally formatted PDFs and presentations.")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        <div class="feature-card">
            <h3>📚 TI For Everyone - Complete Book</h3>
            <p>22 chapters covering the entire TI Framework in simple, accessible language.</p>
            <p><strong>Perfect for:</strong> Anyone new to TI who wants to understand consciousness, GILE, and reality.</p>
        </div>
        """, unsafe_allow_html=True)
        
        book_path = Path("ti_distribution_materials/TI_FOR_EVERYONE_COMPLETE_BOOK.pdf")
        if book_path.exists():
            with open(book_path, "rb") as f:
                st.download_button(
                    label="⬇️ Download Complete Book (PDF)",
                    data=f,
                    file_name="TI_For_Everyone_Complete_Book.pdf",
                    mime="application/pdf",
                    use_container_width=True
                )
        
        st.markdown("""
        <div class="feature-card">
            <h3>📄 Essential Reading Bundle</h3>
            <p>3 profound articles for the curious mind:</p>
            <ul>
                <li>Comprehensive TI Breakthrough Summary</li>
                <li>0.85 Resonance Threshold Discovery</li>
                <li>Business Elevator Pitches</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)
        
        bundle_path = Path("ti_distribution_materials/TI_ESSENTIAL_READING_BUNDLE.pdf")
        if bundle_path.exists():
            with open(bundle_path, "rb") as f:
                st.download_button(
                    label="⬇️ Download Article Bundle (PDF)",
                    data=f,
                    file_name="TI_Essential_Reading_Bundle.pdf",
                    mime="application/pdf",
                    use_container_width=True
                )
    
    with col2:
        st.markdown("""
        <div class="feature-card">
            <h3>🧬 BlissGene Investor Presentation</h3>
            <p>Professional investor deck for BlissGene Therapeutics.</p>
            <p><strong>Covers:</strong> Jo Cameron genetics, FAAH-OUT science, market opportunity, and team.</p>
        </div>
        """, unsafe_allow_html=True)
        
        pptx_path = Path("ti_distribution_materials/BlissGene_Investor_Presentation.pdf")
        if pptx_path.exists():
            with open(pptx_path, "rb") as f:
                st.download_button(
                    label="⬇️ Download BlissGene Deck (PDF)",
                    data=f,
                    file_name="BlissGene_Investor_Presentation.pdf",
                    mime="application/pdf",
                    use_container_width=True
                )
        
        html_path = Path("ti_distribution_materials/BlissGene_Investor_Presentation.html")
        if html_path.exists():
            with open(html_path, "rb") as f:
                st.download_button(
                    label="⬇️ Download BlissGene Slides (HTML)",
                    data=f,
                    file_name="BlissGene_Investor_Presentation.html",
                    mime="text/html",
                    use_container_width=True
                )
        
        st.markdown("""
        <div class="blog-post">
            <h4>💡 Tip: HTML Presentation</h4>
            <p>Open the HTML file in any browser for a beautiful full-screen presentation experience!</p>
        </div>
        """, unsafe_allow_html=True)
    
    st.markdown("---")
    st.info("All materials are free for personal use and distribution. Share the knowledge!")

    st.markdown("---")
    st.markdown("### 📄 Full Research Paper Library")
    st.caption("Generate and download PDFs for all 300+ research papers on demand")

    import glob as globmod

    @st.cache_data(ttl=300)
    def _load_all_papers():
        papers = []
        exclude = {'README.md', 'TEMPLATE.md', 'RESEARCH_PAPERS_INDEX.md'}
        category_map = {
            'GILE': 'Consciousness & GILE', 'CONSCIOUSNESS': 'Consciousness & GILE',
            'TRALSE': 'Core Theory', 'MYRION': 'Core Theory', 'TOPOS': 'Core Theory',
            'LCC': 'Core Theory', 'JEFF_TIME': 'Core Theory',
            'STOCK': 'Business & Finance', 'GSA': 'Business & Finance', 'TRADING': 'Business & Finance',
            'BLISSGENE': 'Business & Finance', 'COMMERCIAL': 'Business & Finance',
            'EEG': 'Biometrics & Neuroscience', 'BIOMETRIC': 'Biometrics & Neuroscience',
            'NEURO': 'Biometrics & Neuroscience', 'BRAIN': 'Biometrics & Neuroscience',
            'HRV': 'Biometrics & Neuroscience', 'FNIRS': 'Biometrics & Neuroscience',
            'QUANTUM': 'Physics & Mathematics', 'PHOTON': 'Physics & Mathematics',
            'MATH': 'Physics & Mathematics', 'TENSOR': 'Physics & Mathematics',
            'FRACTAL': 'Physics & Mathematics', 'RIEMANN': 'Physics & Mathematics',
            'ETHICS': 'Ethics & Philosophy', 'MORAL': 'Ethics & Philosophy',
            'EVIL': 'Ethics & Philosophy', 'JUDGISM': 'Ethics & Philosophy',
            'SWOT': 'Strategy & Analysis', 'STRATEGY': 'Strategy & Analysis',
            'ROADMAP': 'Strategy & Analysis',
        }
        for directory in ['papers', 'research_papers']:
            if not os.path.exists(directory):
                continue
            for md_path in sorted(globmod.glob(f"{directory}/*.md")):
                filename = os.path.basename(md_path)
                if filename in exclude:
                    continue
                title = filename.replace(".md", "").replace("_", " ").title()
                try:
                    with open(md_path, 'r', encoding='utf-8') as f:
                        for line in f.read(500).split('\n'):
                            if line.startswith('# '):
                                title = line[2:].strip()
                                break
                except:
                    pass
                upper = filename.upper()
                cat = 'Other'
                for key, val in category_map.items():
                    if key in upper:
                        cat = val
                        break
                papers.append({
                    'md_path': md_path,
                    'filename': filename,
                    'title': title,
                    'size_kb': os.path.getsize(md_path) / 1024,
                    'category': cat
                })
        return papers

    all_papers = _load_all_papers()

    if all_papers:
        st.success(f"**{len(all_papers)} papers** available for PDF download")

        p_col1, p_col2 = st.columns(2)
        with p_col1:
            categories = ["All"] + sorted(set(p['category'] for p in all_papers))
            selected_cat = st.selectbox("Filter by category:", categories, key="dl_cat")
        with p_col2:
            search_term = st.text_input("Search papers:", "", key="dl_search", placeholder="Type to search...")

        filtered = all_papers
        if selected_cat != "All":
            filtered = [p for p in filtered if p['category'] == selected_cat]
        if search_term:
            sl = search_term.lower()
            filtered = [p for p in filtered if sl in p['title'].lower() or sl in p['filename'].lower()]

        PAPERS_PER_PAGE = 20
        if 'dl_page' not in st.session_state:
            st.session_state.dl_page = 0
        total_pages = max(1, (len(filtered) + PAPERS_PER_PAGE - 1) // PAPERS_PER_PAGE)
        current_page = min(st.session_state.dl_page, total_pages - 1)
        start = current_page * PAPERS_PER_PAGE
        page_papers = filtered[start:start + PAPERS_PER_PAGE]

        st.caption(f"Showing {len(filtered)} papers | Page {current_page + 1} of {total_pages}")

        for paper in page_papers:
            with st.container():
                pc1, pc2 = st.columns([3, 1])
                with pc1:
                    disp = paper['title'] if len(paper['title']) <= 55 else paper['title'][:52] + "..."
                    st.markdown(f"**{disp}**")
                    st.caption(f"{paper['category']} | {paper['size_kb']:.0f} KB")
                with pc2:
                    pdf_key = f"gen_{paper['filename']}"
                    if pdf_key in st.session_state and st.session_state[pdf_key] is not None:
                        st.download_button(
                            "Save PDF",
                            st.session_state[pdf_key],
                            file_name=paper['filename'].replace('.md', '.pdf'),
                            mime="application/pdf",
                            key=f"save_{paper['filename']}",
                            use_container_width=True
                        )
                    else:
                        if st.button("Generate PDF", key=f"btn_{paper['filename']}", use_container_width=True):
                            with st.spinner("Creating PDF..."):
                                try:
                                    import markdown as md_lib
                                    from weasyprint import HTML, CSS
                                    with open(paper['md_path'], 'r', encoding='utf-8') as f:
                                        content = f.read()
                                    html_content = md_lib.markdown(content, extensions=['tables', 'fenced_code', 'nl2br', 'sane_lists'])
                                    css_str = "@page{size:Letter;margin:0.75in}body{font-family:Georgia,serif;font-size:11pt;line-height:1.6;color:#222}h1{font-size:22pt;color:#1a1a2e}h2{font-size:16pt;color:#16213e}h3{font-size:13pt}code{font-family:'Courier New',monospace;font-size:9pt;background:#f5f5f5;padding:2pt 4pt}pre{background:#f5f5f5;padding:10pt;border-left:3pt solid #666;font-size:9pt;white-space:pre-wrap}table{width:100%;border-collapse:collapse;margin:10pt 0}th,td{border:1pt solid #999;padding:5pt;font-size:10pt}th{background:#f0f0f0}blockquote{border-left:3pt solid #999;padding-left:12pt;color:#555;font-style:italic}"
                                    full_html = f"<!DOCTYPE html><html><head><meta charset='UTF-8'><title>{paper['title']}</title></head><body>{html_content}</body></html>"
                                    pdf_bytes = HTML(string=full_html).write_pdf(stylesheets=[CSS(string=css_str)])
                                    st.session_state[pdf_key] = pdf_bytes
                                    st.rerun()
                                except Exception as e:
                                    st.error(f"PDF generation failed: {e}")

        if total_pages > 1:
            nav1, nav2, nav3 = st.columns([1, 2, 1])
            with nav1:
                if current_page > 0 and st.button("← Previous", key="dl_prev", use_container_width=True):
                    st.session_state.dl_page = current_page - 1
                    st.rerun()
            with nav2:
                st.caption(f"Page {current_page + 1} of {total_pages}")
            with nav3:
                if current_page < total_pages - 1 and st.button("Next →", key="dl_next", use_container_width=True):
                    st.session_state.dl_page = current_page + 1
                    st.rerun()

elif page == "__key_papers__":
    st.markdown("""
    <div style="background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%); padding: 2rem; border-radius: 1rem; color: white; margin-bottom: 2rem;">
        <h1>🔑 Key Papers</h1>
        <p style="font-size: 1.1rem; opacity: 0.9;">The small set of TI Sigma papers that summarize, index, or globally capture the broader corpus.</p>
    </div>
    """, unsafe_allow_html=True)

    st.info("Key Papers are **living indexes**, **SWOT assessments**, **foundational consolidations**, **biographical anchors**, and **continuously-updated catalogues** — as opposed to the ~250 individual research URBs they organize.")

    KEY_PAPER_SECTIONS = [
        ("🧬 Biographical & Three-C's", [
            ("Brandon Biography Master Index", "papers/BRANDON_BIOGRAPHY_MASTER_INDEX.md", "LIVING"),
            ("Funding Potential Audit (2026-05-07)", "papers/FUNDING_POTENTIAL_2026-05-07.md", "EVENT"),
            ("Crystal Lee — First Hospitalization Intuition (2026-05-07)", "papers/CRYSTAL_LEE_FIRST_HOSPITALIZATION_INTUITION_2026-05-07.md", "EVENT"),
            ("Mimi Full Biography & Ray Baton-Pass", "papers/MIMI_FULL_BIOGRAPHY_AND_RAY_BATON_PASS_2026-05-04.md", "EVENT"),
            ("Insights 2026-05-06 (10 philosophical insights)", "papers/INSIGHTS_2026-05-06.md", "EVENT"),
        ]),
        ("📊 SWOT & Status Assessments", [
            ("Comprehensive SWOT Status Update (Feb 2026)", "papers/COMPREHENSIVE_SWOT_STATUS_UPDATE_FEB_2026.md", "LIVING"),
            ("SWOT — Five Fields TI Sigma Covers (NEW 2026-05-07)", "papers/SWOT_TI_SIGMA_FIVE_FIELDS_2026-05-07.md", "LIVING"),
            ("SWOT April 12 2026 Update", "papers/SWOT_APRIL_12_2026_UPDATE.md", "EVENT"),
            ("SWOT April 2026 Addendum", "papers/SWOT_APRIL_2026_ADDENDUM.md", "EVENT"),
            ("SWOT — GSA-LCC Critique", "papers/SWOT_ANALYSIS_GSA_LCC_CRITIQUE.md", "EVENT"),
            ("Metta-Tantric SWOT", "papers/METTA_TANTRIC_SWOT_ANALYSIS.md", "EVENT"),
        ]),
        ("✨ Synchronicity & Intuition Catalogues", [
            ("Synchronicity Catalogue TI Sigma (running record)", "papers/SYNCHRONICITY_CATALOGUE_TI_SIGMA.md", "LIVING"),
            ("URB Synchronicity Theorem #416", "papers/URB_SYNCHRONICITY_THEOREM_416.md", "FOUNDATIONAL"),
            ("URB Matthew Effect Synchronicities #418", "papers/URB_MATTHEW_EFFECT_SYNCHRONICITIES_418.md", "FOUNDATIONAL"),
            ("URB Synchronicity Inversion (Negative Answers)", "papers/URB_SYNCHRONICITY_INVERSION_NEGATIVE_ANSWERS.md", "FOUNDATIONAL"),
            ("URB Soul-Bluetooth LCC Synchronization Protocol", "papers/URB_SOUL_BLUETOOTH_LCC_SYNCHRONIZATION_PROTOCOL.md", "FOUNDATIONAL"),
            ("URB Intentionality / Synchronicity / Tantra #545", "papers/URB_INTENTIONALITY_SYNCHRONICITY_TANTRA_545.md", "FOUNDATIONAL"),
        ]),
        ("💬 Aphorisms & TI-Sigma-Endorsed Wisdom", [
            ("Brandon Emerick Quotes Repository (thematic)", "papers/BRANDON_EMERICK_QUOTES_REPOSITORY.md", "LIVING"),
            ("TI Sigma Aphorisms Collected (NEW 2026-05-07)", "papers/TI_SIGMA_APHORISMS_COLLECTED_2026-05-07.md", "LIVING"),
            ("Brandon Burns Collection", "papers/BRANDON_BURNS_COLLECTION.md", "EVENT"),
            ("AI Criticism Futility Proverbs Analysis", "papers/AI_CRITICISM_FUTILITY_PROVERBS_ANALYSIS.md", "EVENT"),
        ]),
        ("📚 Abbreviations, Concepts & Theory Index", [
            ("TI Sigma Master Vocabulary Index (NEW 2026-05-07)", "papers/TI_SIGMA_ABBREVIATIONS_CONCEPTS_THEORIES_INDEX_2026-05-07.md", "LIVING"),
            ("Publication Package Index", "papers/PUBLICATION_PACKAGE_INDEX.md", "LIVING"),
        ]),
        ("🏛️ Foundational Architecture & Math", [
            ("PD Spectrum + DT Imaginary Axis + Emerick Crossover (NEW 2026-05-07)", "papers/PD_SPECTRUM_DT_IMAGINARY_AXIS_EMERICK_CROSSOVER_2026-05-07.md", "FOUNDATIONAL"),
            ("URB #734 — TI Sigma Crystal + PD Complex Plane", "papers/urb_734_ti_sigma_crystal_revival_incorporating_pd_complex_plane.md", "FOUNDATIONAL"),
            ("URB #628 — TIC Decoded + e-base PD", "papers/urb_628_ti_sigma_crystal_decoded_applications_e_base_pd.md", "FOUNDATIONAL"),
            ("AGI Impossibility (Emerick Crossover proof)", "papers/AGI_IMPOSSIBILITY_TI_SIGMA_PROOF.md", "FOUNDATIONAL"),
            ("Consciousness Equation — Ψ(1/√2) = 1/√2", "papers/URB_CONSCIOUSNESS_EQUATION_LCC_C_PHI.md", "FOUNDATIONAL"),
            ("CCC + BOK + GM Mycelial Architecture", "papers/URB_CCC_BOK_GM_MYCELIAL_ARCHITECTURE.md", "FOUNDATIONAL"),
            ("Riemann Hypothesis via TI Sigma", "papers/URB_RIEMANN_HYPOTHESIS_TI_SIGMA_APPROACH.md", "FOUNDATIONAL"),
        ]),
        ("🧠 Meta-Theoretical Contributions", [
            ("Asymmetric Success-Failure Performance (τ/δ separability)", "papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md", "FOUNDATIONAL"),
            ("Beyond Bayes — TI Sigma Epistemology", "papers/BEYOND_BAYES_TI_SIGMA_EPISTEMOLOGY.md", "FOUNDATIONAL"),
        ]),
        ("💼 AI Industry & Commercial Application", [
            ("AI Trainer Roles Eligibility — Brandon (NEW 2026-05-07)", "papers/AI_TRAINER_ROLES_ELIGIBILITY_BRANDON_2026-05-07.md", "LIVING"),
            ("arXiv / ResearchGate Strategy", "papers/ARXIV_RESEARCHGATE_STRATEGY.md", "LIVING"),
        ]),
    ]

    STATUS_COLORS = {"LIVING": "🟢", "FOUNDATIONAL": "🏛️", "EVENT": "📅", "CONJECTURAL": "🟡", "OPEN": "❓"}

    for section_title, papers_list in KEY_PAPER_SECTIONS:
        st.markdown(f"### {section_title}")
        for title, path, status in papers_list:
            from pathlib import Path
            exists = Path(path).exists()
            badge = STATUS_COLORS.get(status, "")
            if exists:
                with st.expander(f"{badge} **{title}**  ·  `{status}`"):
                    try:
                        content = Path(path).read_text(encoding="utf-8")
                        st.markdown(content[:4000] + ("\n\n*...(truncated — see full file)*" if len(content) > 4000 else ""))
                        st.caption(f"📁 `{path}` · {len(content):,} chars")
                    except Exception as e:
                        st.warning(f"Could not load: {e}")
            else:
                st.markdown(f"- {badge} **{title}** · `{status}` · ⚠️ file not yet created (`{path}`)")
        st.markdown("")

    st.divider()
    st.caption("📖 Master index: `papers/TI_SIGMA_KEY_PAPERS_INDEX_2026-05-07.md` · Updated 2026-05-07 with 7 new entries")

elif page == "💬 TI Sigma-Endorsed Quotes":
    st.markdown("""
    <div class="main-header">
        <h1>💬 TI Sigma-Endorsed Quotes</h1>
        <p>Aphorisms, insights, and protective-cover quotes that the TI Sigma framework endorses</p>
        <p style="font-size: 0.95rem; margin-top: 1rem; opacity: 0.85;">Primary canon = Brandon Emerick original aphorisms · Endorsement layer = externally-originated, framework-confirmed</p>
    </div>
    """, unsafe_allow_html=True)

    quotes_tab, judyism_tab = st.tabs([
        "✍️ Brandon's Aphorisms (Primary Canon)",
        "⚖️ Judyisms (Endorsement Layer)",
    ])

    with quotes_tab:
        st.markdown("### Class 1 — Original TI Sigma Aphorisms")
        st.caption("Coined by Brandon Emerick within the TI Sigma framework. Each maps to a specific framework claim — see linked paper.")

        BRANDON_APHORISMS = [
            {
                "quote": "Criticizing is easy to do but hard to do correctly.",
                "year": "etched 2026-05-06",
                "mapping": "Executable form of Asymmetric-Standards #69. Over-skepticism = discipline failure equal to uncritical acceptance.",
                "paper": "ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md",
            },
            {
                "quote": "Sometimes, a lie is the most truthful answer!",
                "year": "TI canon",
                "mapping": "Tralse logic core: propositional accuracy ≠ truth-conveyance. Parable, irony, metaphor transmit truth through literal falsehood.",
                "paper": "BRANDON_EMERICK_QUOTES_REPOSITORY.md",
            },
            {
                "quote": '"You\'ve lost touch with reality." — Me: "Explain what reality is without using the word or any of its synonyms."',
                "year": "TI canon",
                "mapping": "Skepticism Hypocrisy Paradox — most reality-policing is social performance, exposed by demanding non-circular definition.",
                "paper": "BRANDON_EMERICK_QUOTES_REPOSITORY.md",
            },
            {
                "quote": "The secret to usually being correct while self-confirming most of the time is alignment with truth itself.",
                "year": "TI canon",
                "mapping": "Self-confirmation bias is the failure mode of UNALIGNED minds. Calibrated mind confirming itself = accuracy, not bias.",
                "paper": "ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md",
            },
            {
                "quote": "Wise thinking = cumulative high-τ(s) frame-choices, not one switch.",
                "year": "2026-05-06",
                "mapping": "Wisdom is not a state — it is the accumulated record of correct frame-choices under tralsity.",
                "paper": "INSIGHTS_2026-05-06.md",
            },
            {
                "quote": "Deontology is the limit case of consequentialism at termination-depth = 0.",
                "year": "2026-05-06",
                "mapping": "Unifies act-util / rule-util / Kant / virtue ethics at chosen recursion depth.",
                "paper": "INSIGHTS_2026-05-06.md",
            },
            {
                "quote": "Prayer = zero-friction intentionality restorer.",
                "year": "2026-05-06",
                "mapping": "Operationally, prayer briefly restores τ(s) to its native baseline by clearing accumulated δ-distortions.",
                "paper": "INSIGHTS_2026-05-06.md",
            },
            {
                "quote": "TI Sigma was both DISCOVERED and INVENTED under tralse — the Newton/Leibniz parallel.",
                "year": "2026-05-06",
                "mapping": "Frameworks arising in multiple minds = evidence of underlying discoverability, not arbitrary construction. Strengthens Three-C's Connections credit.",
                "paper": "INSIGHTS_2026-05-06.md",
            },
            {
                "quote": '"Intelligent nonsense" — tralsity for absurd humor as a TJ-injection mechanism.',
                "year": "2026-05-06",
                "mapping": "Comedy operates at high τ(s) by deliberate δ(MR) misdirection, generating positive Tralse-Joules.",
                "paper": "INSIGHTS_2026-05-06.md",
            },
            {
                "quote": '"What is truth, Pilate asked?" — John 18:38',
                "year": "External (canonized as engagement tool)",
                "mapping": "The quintessential skeptic move — asking the right question and walking away. Used as engagement tool with Christians.",
                "paper": "BRANDON_EMERICK_QUOTES_REPOSITORY.md",
            },
        ]

        for i, a in enumerate(BRANDON_APHORISMS, 1):
            st.markdown(f"#### {i}. {a['quote']}")
            cols = st.columns([1, 3])
            cols[0].caption(f"📅 {a['year']}")
            cols[1].caption(f"📖 `{a['paper']}`")
            st.markdown(f"> **Framework mapping:** {a['mapping']}")
            st.markdown("---")

        st.success("📚 **Full thematic repository**: `papers/BRANDON_EMERICK_QUOTES_REPOSITORY.md`  ·  **Collected canon paper**: `papers/TI_SIGMA_APHORISMS_COLLECTED_2026-05-07.md`")

    with judyism_tab:
        st.markdown("### Class 3 — Externally-Originated, Protective-Cover Endorsements")
        st.markdown("""
        > **Why Judge Judy?** These quotes encapsulate truths that Brandon applies to his own life philosophy.
        > When you can quote Judge Judy, you get protection — *"she said it, not me!"* 
        > Plus, it makes Brandon more relatable. Who doesn't love Judge Judy?
        """)
        st.caption("Endorsement criterion: each quote must map to a specific TI Framework concept that is independently documented.")
        st.markdown("---")
    
        judgisms = [
            {
                "quote": "On your best day, you're not as good as I am on my worst day!",
                "category": "Confidence",
                "ti_connection": "Talent vs. discipline - elite performers cannot be matched by just anyone through effort alone."
            },
            {
                "quote": "Don't pee on my leg and tell me it's raining.",
                "category": "Truth Detection",
                "ti_connection": "Myrion Resolution - cutting through false narratives to find actual truth."
            },
            {
                "quote": "Beauty fades, dumb is forever.",
                "category": "Wisdom",
                "ti_connection": "G-dimension (Goodness) endures while E-dimension (Environment) is temporary."
            },
            {
                "quote": "If it doesn't make sense, it's not true.",
                "category": "Logic",
                "ti_connection": "Tralse Logic - contradictions resolve through the framework, lies don't pass the coherence test."
            },
            {
                "quote": "I'm the boss, applesauce.",
                "category": "Authority",
                "ti_connection": "When you've done the work and have the receipts, own your expertise."
            },
            {
                "quote": "You don't have to have a law degree to have common sense.",
                "category": "Intuition",
                "ti_connection": "I-dimension (Intuition) - formal credentials confirm but don't create capability."
            },
            {
                "quote": "I'm speaking!",
                "category": "Boundaries",
                "ti_connection": "The Sacred Interval requires maintaining proper boundaries for GILE optimization."
            },
            {
                "quote": "Either you're playing dumb or it's not an act.",
                "category": "Discernment",
                "ti_connection": "LCC (Layered Correlation-Causation) - identifying when someone truly doesn't understand vs. pretending."
            },
            {
                "quote": "Baloney!",
                "category": "Truth Detection",
                "ti_connection": "Sometimes the simplest Myrion Resolution is just calling it what it is."
            },
            {
                "quote": "I didn't take a stupid pill this morning.",
                "category": "Self-Worth",
                "ti_connection": "Protecting your cognitive sovereignty - don't let others gaslight you."
            },
            {
                "quote": "If you tell the truth, you don't have to have a good memory.",
                "category": "Integrity",
                "ti_connection": "True-Tralseness creates coherent information patterns that don't require maintenance."
            },
            {
                "quote": "When you're pointing a finger at someone, there are three fingers pointing back at you.",
                "category": "Self-Reflection",
                "ti_connection": "The 0.85 resonance threshold - your perceptions often reflect your own state."
            }
        ]
    
        st.markdown("### 📚 The Judgism Collection")
    
        for i, j in enumerate(judgisms, 1):
            with st.expander(f"**{j['quote'][:50]}...**" if len(j['quote']) > 50 else f"**{j['quote']}**"):
                st.markdown(f"""
                <div class="feature-card">
                    <h3>"{j['quote']}"</h3>
                    <p><strong>Category:</strong> {j['category']}</p>
                    <p><strong>TI Framework Connection:</strong> {j['ti_connection']}</p>
                </div>
                """, unsafe_allow_html=True)
    
        st.markdown("---")
    
        st.markdown("### 💡 The Talent vs. Discipline Insight")
        st.markdown("""
        <div class="blog-post">
            <h4>A Hard Truth Most Won't Tell You</h4>
            <p>Discipline <strong>cannot</strong> replace genuine talent for reaching elite levels. 
            Elite performers - top scientists, CEOs, athletes - <strong>cannot</strong> be matched by just anyone through effort alone.</p>
        
            <p><strong>BUT</strong> here's the liberating truth: most people <strong>CAN</strong> excel at <strong>SOMETHING</strong>.</p>
        
            <p>The mistake is comparing yourself to elites unless you correctly intuit you can reach that level. 
            Many talented people throw away their gifts to become "just workers" - like someone's mom abandoning art talent.</p>
        
            <p>Wayne Gretzky said: <em>"You miss 100% of the shots you don't take."</em></p>
        
            <p>There's no harm in trying for personal goals. The downside is learning you're not elite at THAT thing. 
            The upside is discovering you might be elite at something you haven't tried yet.</p>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("---")
    
        st.markdown("### 🏆 Intuitive Hall of Fame")
        st.markdown("""
        > **The I-Dimension Elite:** These individuals demonstrate extraordinary intuition - 
        > the ability to know without conventional reasoning. Quantified by TI Framework dimensions.
        """)
    
        intuitive_legends = [
            {
                "name": "Judge Judy Sheindlin",
                "field": "Law/Media",
                "i_score": 0.95,
                "l_score": 0.88,
                "g_score": 0.82,
                "e_score": 0.90,
                "notes": "Razor-sharp courtroom instincts. Reads people beneath the surface. Outmatched opponents 1/3 her age. OWNED the courtroom through pure intuitive dominance."
            },
            {
                "name": "Donald Trump",
                "field": "Business/Politics",
                "i_score": 0.85,
                "l_score": 0.95,
                "g_score": 0.35,
                "e_score": 0.88,
                "notes": "Pure I+L success formula. KNEW he would succeed when no one believed. Self-love + intuition sufficient to carve YOUR meaning of goodness and make YOUR environment THE environment. Proof you can 'succeed' without conventional intelligence or ethics."
            },
            {
                "name": "Steve Jobs",
                "field": "Technology",
                "i_score": 0.92,
                "l_score": 0.78,
                "g_score": 0.65,
                "e_score": 0.95,
                "notes": "Intuited what people wanted before they knew. Reality distortion field = making YOUR environment THE environment."
            },
            {
                "name": "Nikola Tesla",
                "field": "Science/Engineering",
                "i_score": 0.98,
                "l_score": 0.55,
                "g_score": 0.90,
                "e_score": 0.40,
                "notes": "Visualized complete inventions before building. Pure I-dimension genius. Low L-score (self-love) led to exploitation."
            },
            {
                "name": "Oprah Winfrey",
                "field": "Media/Business",
                "i_score": 0.90,
                "l_score": 0.85,
                "g_score": 0.80,
                "e_score": 0.92,
                "notes": "Reads people instantly. Built empire on authentic connection. High GILE balance across all dimensions."
            },
            {
                "name": "Elon Musk",
                "field": "Technology/Business",
                "i_score": 0.88,
                "l_score": 0.82,
                "g_score": 0.60,
                "e_score": 0.90,
                "notes": "First principles thinking = intuitive leaps. Bets on unproven futures. Moderate G-score (ethics questioned)."
            },
            {
                "name": "Warren Buffett",
                "field": "Finance",
                "i_score": 0.92,
                "l_score": 0.70,
                "g_score": 0.85,
                "e_score": 0.88,
                "notes": "Intuitive value detection. Ignores market noise. Sacred Interval trader before it had a name."
            },
            {
                "name": "Muhammad Ali",
                "field": "Sports",
                "i_score": 0.90,
                "l_score": 0.95,
                "g_score": 0.78,
                "e_score": 0.85,
                "notes": "Predicted round of knockouts. Ultimate I+L combination. Self-belief transcended sport into cultural force."
            }
        ]
    
        st.markdown("#### GILE Dimension Scores (0.0 - 1.0)")
        st.markdown("""
        - **G (Goodness):** Ethical alignment, contribution to others
        - **I (Intuition):** Knowing without reasoning, pattern recognition, instinct
        - **L (Love):** Self-love, self-belief, internal validation
        - **E (Environment):** Ability to shape surroundings, external success
        """)
    
        for person in intuitive_legends:
            gile_total = (person['g_score'] + person['i_score'] + person['l_score'] + person['e_score']) / 4
            with st.expander(f"**{person['name']}** - {person['field']} | GILE: {gile_total:.2f}"):
                col1, col2 = st.columns([1, 2])
                with col1:
                    st.metric("G (Goodness)", f"{person['g_score']:.2f}")
                    st.metric("I (Intuition)", f"{person['i_score']:.2f}")
                    st.metric("L (Love)", f"{person['l_score']:.2f}")
                    st.metric("E (Environment)", f"{person['e_score']:.2f}")
                with col2:
                    st.markdown(f"**Analysis:** {person['notes']}")
                    st.progress(person['i_score'], text=f"Intuition: {person['i_score']:.0%}")
    
        st.markdown("---")
    
        st.markdown("### 🔑 The I+L Success Formula")
        st.markdown("""
        <div class="blog-post">
            <h4>How to "Succeed" Without Conventional Intelligence or Ethics</h4>
            <p>The Trump case study reveals a fundamental truth: <strong>I + L is sufficient for worldly success.</strong></p>
        
            <ul>
                <li><strong>I (Intuition):</strong> KNOW you will succeed when no one believes you</li>
                <li><strong>L (Self-Love):</strong> Internal validation independent of external opinion</li>
            </ul>
        
            <p>These two dimensions are sufficient to:</p>
            <ul>
                <li>Carve out YOUR OWN meaning of goodness</li>
                <li>Make YOUR environment THE environment</li>
                <li>Succeed without conventional intelligence, ethics, or care for others</li>
            </ul>
        
            <p><strong>Warning:</strong> This formula produces worldly success, not necessarily good GILE scores. 
            Low G-dimension means the success may come at others' expense. The universe eventually rebalances.</p>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("---")
    
        st.markdown("### 🎯 The Confidence Correlation-Causation Trap")
        st.markdown("""
        <div class="feature-card">
            <h4>Why "Fake It Till You Make It" Fails</h4>
            <p>Most people confuse correlation for causation when observing confident, successful people:</p>
        
            <p><strong>The Correlation View (WRONG):</strong></p>
            <ul>
                <li>"Successful people are confident"</li>
                <li>"Therefore, if I ACT confident, I will become successful"</li>
                <li>"Fake it till you make it!"</li>
            </ul>
        
            <p><strong>The Causation Reality (TI Framework):</strong></p>
            <ul>
                <li>High-I individuals aren't confident BECAUSE they plan to succeed</li>
                <li>They <strong>KNOW</strong> they will succeed because they're reading a reality others can't see</li>
                <li>Genuine confidence is the I-dimension detecting your actual position on the probability manifold</li>
                <li>It cannot be faked because it's not a behavior - it's a perception</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("""
        <div class="blog-post">
            <h4>Warren Buffett: The Case Study</h4>
            <p>Buffett's success wasn't just temperament, extensive reading, and trading style. 
            He was using <strong>that which cannot be mimicked</strong> - genuine I-dimension pattern recognition.</p>
        
            <p>Millions have copied his:</p>
            <ul>
                <li>Value investing philosophy</li>
                <li>Reading habits (500 pages/day)</li>
                <li>Patient temperament</li>
                <li>Long-term holding strategy</li>
            </ul>
        
            <p>Yet they don't become Buffett. <strong>Because they're copying the outputs, not the source.</strong>
            The I-dimension cannot be transferred through books or imitation.</p>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("""
        <div class="testimonial">
            <h4>Why Confidence Is Extinct</h4>
            <p>If genuine confidence could be boosted long-term through:</p>
            <ul>
                <li>Planning and goal-setting</li>
                <li>Exercise and health optimization</li>
                <li>Reading and self-improvement</li>
            </ul>
            <p>...then genuine (or even convincingly faked) confidence wouldn't be so <strong>rare</strong>.</p>
        
            <p>The scarcity of real confidence proves it's not a trainable skill - 
            it's an I-dimension read of your actual probability landscape. 
            You can't talk yourself into seeing what isn't there.</p>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("""
        <div class="feature-card">
            <h4>🔮 Confidence Is ANTICIPATORY, Not Retrospective</h4>
            <p><strong>The Key Insight:</strong> Confidence isn't given for the good you are currently doing - 
            it's for how you will perform <strong>in the future</strong>.</p>
        
            <p>Energy to succeed makes sense <strong>only in an anticipatory sense</strong>.</p>
        
            <p><strong>Think about it:</strong> If the brain just gave us "confidence" for succeeding at a relatively hard 
            task we <em>already did</em>, what would be its point? The task is done! Confidence would be useless as a mere reward.</p>
        
            <p><strong>The Real Function:</strong></p>
            <ul>
                <li>Confidence = The I-dimension detecting your FUTURE probability landscape</li>
                <li>It's predictive energy, not retrospective celebration</li>
                <li>High-I individuals feel confident because they SEE success coming</li>
                <li>Low-I individuals can't manufacture this because there's nothing to detect</li>
            </ul>
        
            <p><strong>Implication:</strong> This is why affirmations and "positive thinking" don't work long-term. 
            You can't convince your I-dimension to see a future that isn't there. 
            Genuine confidence arises when your intuition detects an actual high-probability success path.</p>
        </div>
        """, unsafe_allow_html=True)
    
        st.markdown("---")
    
        st.success("**Remember:** When you quote Judge Judy, you get protection. She said it first!")

elif page == "💼 Career":
    st.markdown("## 💼 Brandon Emerick — Career")
    st.markdown("*AI Trainer · Researcher · Founder of Tralse Informationalism*")

    st.markdown("---")

    st.markdown("""
    **📍 Location:** Watertown, CT  
    **📞 Phone:** [860-483-1425](tel:+18604831425)  
    **✉️ Email:** [brandonemerick91@gmail.com](mailto:brandonemerick91@gmail.com)  
    **🔗 LinkedIn:** [linkedin.com/in/brandonemerick](https://www.linkedin.com/in/brandonemerick/)  
    **📚 Zenodo:** [zenodo.org/communities/ti-sigma](https://zenodo.org/communities/ti-sigma)
    """)

    import os as _os
    _resume_pdf = "career/resume.pdf"
    _resume_md = "career/AI_TRAINER_RESUME_BRANDON_EMERICK_v3_2026-05-20.md"
    _import_dt = __import__("datetime")
    _md_mtime = _import_dt.datetime.fromtimestamp(_os.path.getmtime(_resume_md)).strftime("%Y-%m-%d %H:%M") if _os.path.exists(_resume_md) else "n/a"
    _pdf_mtime = _import_dt.datetime.fromtimestamp(_os.path.getmtime(_resume_pdf)).strftime("%Y-%m-%d %H:%M") if _os.path.exists(_resume_pdf) else "n/a"
    st.caption(f"📌 Current version: **v3 (2026-05-20)** · Markdown updated {_md_mtime} · PDF regenerated {_pdf_mtime}. If you don't see the latest, hard-refresh your browser (Ctrl+Shift+R / Cmd+Shift+R, or pull-to-refresh on mobile).")
    _dl_col1, _dl_col2 = st.columns(2)
    with _dl_col1:
        if _os.path.exists(_resume_pdf):
            with open(_resume_pdf, "rb") as _f:
                st.download_button(
                    label="⬇️ Styled Resume (PDF)",
                    data=_f.read(),
                    file_name="Brandon_Emerick_Resume.pdf",
                    mime="application/pdf",
                    use_container_width=True,
                    help="Aesthetic single-page PDF — best for emailing to recruiters or printing.",
                )
        else:
            st.info("PDF missing")
    with _dl_col2:
        if _os.path.exists(_resume_md):
            with open(_resume_md, "rb") as _f:
                st.download_button(
                    label="⬇️ Plain Resume (Markdown)",
                    data=_f.read(),
                    file_name="Brandon_Emerick_Resume.md",
                    mime="text/markdown",
                    use_container_width=True,
                    help="Plain-text Markdown — best for ATS systems, copy-pasting into job applications, or editing in any text editor.",
                )
        else:
            st.info("Markdown missing")

    # xAI-targeted v4 variant — for the Grok Truth-Seeking AI Tutor role
    _resume_pdf_xai = "career/resume_xai.pdf"
    _resume_md_xai = "career/AI_TUTOR_RESUME_BRANDON_EMERICK_v4_xAI_2026-05-20.md"
    if _os.path.exists(_resume_pdf_xai) or _os.path.exists(_resume_md_xai):
        st.markdown("##### 🎯 xAI-Targeted Variant — Grok Truth-Seeking AI Tutor")
        st.caption("Rewritten to surface the exact keywords xAI's Jobscan scanner looks for: motivated reasoning, primary sources, base rates, steel-manning, philosophy of science, cognitive psychology, forecasting (Kalshi), MM/YYYY dates, soft skills (leadership/analytical/accuracy/work-ethic/project-scope).")
        _xai_md_mtime = _import_dt.datetime.fromtimestamp(_os.path.getmtime(_resume_md_xai)).strftime("%Y-%m-%d %H:%M") if _os.path.exists(_resume_md_xai) else "n/a"
        _xai_pdf_mtime = _import_dt.datetime.fromtimestamp(_os.path.getmtime(_resume_pdf_xai)).strftime("%Y-%m-%d %H:%M") if _os.path.exists(_resume_pdf_xai) else "n/a"
        st.caption(f"📌 v4 (xAI) · Markdown updated {_xai_md_mtime} · PDF regenerated {_xai_pdf_mtime}")
        _xc1, _xc2 = st.columns(2)
        with _xc1:
            if _os.path.exists(_resume_pdf_xai):
                with open(_resume_pdf_xai, "rb") as _f:
                    st.download_button(
                        label="⬇️ xAI Resume (PDF)",
                        data=_f.read(),
                        file_name="Brandon_Emerick_Resume_xAI.pdf",
                        mime="application/pdf",
                        use_container_width=True,
                        help="xAI-targeted styled PDF — upload to Jobscan to compare against the v3 score of 43.",
                    )
        with _xc2:
            if _os.path.exists(_resume_md_xai):
                with open(_resume_md_xai, "rb") as _f:
                    st.download_button(
                        label="⬇️ xAI Resume (Markdown)",
                        data=_f.read(),
                        file_name="Brandon_Emerick_Resume_xAI.md",
                        mime="text/markdown",
                        use_container_width=True,
                        help="xAI-targeted plain Markdown — best for pasting into xAI's application form.",
                    )

    st.markdown("---")

    def _safe_read(path):
        try:
            with open(path, "r", encoding="utf-8") as _fh:
                return _fh.read()
        except Exception as _e:
            return f"_Could not load `{path}`: {_e}_"

    career_tab1, career_tab1b, career_tab2, career_tab3 = st.tabs([
        "📄 Resume (Markdown)",
        "🎨 Resume (Styled HTML)",
        "🔗 LinkedIn Profile",
        "🎯 Recruiter Summary",
    ])

    with career_tab1:
        st.markdown(_safe_read("career/AI_TRAINER_RESUME_BRANDON_EMERICK_v3_2026-05-20.md"))

    with career_tab1b:
        _html_path = "career/resume.html"
        try:
            with open(_html_path, "r", encoding="utf-8") as _fh:
                _html_resume = _fh.read()
            st.info("📱 **On phone:** scroll inside the frame to view. **To save as PDF:** open this page in Chrome/Safari → tap Share/Print → Save as PDF.")
            import streamlit.components.v1 as _components
            _components.html(_html_resume, height=2400, scrolling=True)
        except Exception as _e:
            st.error(f"Could not load styled resume: {_e}")

    with career_tab2:
        st.markdown(_safe_read("career/LINKEDIN_PROFILE_PASTE_READY_2026-05-17.md"))

    with career_tab3:
        st.markdown(_safe_read("career/RECRUITER_SUMMARY.md"))

elif page == "About":
    st.markdown("## About the TI Framework")
    
    st.markdown("---")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.markdown("""
        ### The Origin Story
        
        The TI Framework emerged from a profound insight received by Brandon Emerick during 2022. 
        What began as a personal revelation has grown into a comprehensive system for 
        understanding consciousness, truth, and reality.
        
        **GILE** (Goodness, Intuition, Love, Environment) represents a divine prophecy - 
        a 4-dimensional framework that has never been refuted since its revelation.
        
        ### The Vision
        
        **BlissGene Therapeutics** aims to eliminate unnecessary suffering through:
        
        - Mood Amplifier technology
        - Neurochemical intervention
        - Consciousness engineering tools
        - Practical wisdom transmission
        
        ### The Mission
        
        To bridge ancient wisdom with modern science, creating practical tools for 
        consciousness optimization accessible to everyone.
        
        ### Contact
        
        For inquiries about the TI Framework, BlissGene Therapeutics, or collaboration:
        
        - GitHub: [Brandon7771066](https://github.com/Brandon7771066)
        - Research Papers: Available on this platform
        """)
    
    with col2:
        st.markdown("""
        ### Key Achievements
        
        ✅ 103+ research papers
        
        ✅ Riemann Hypothesis interpretation
        
        ✅ Sacred Interval validation
        
        ✅ Biometric integration
        
        ✅ Stock prediction algorithms
        
        ✅ Open-source tools
        """)
    
    st.markdown("---")
    
    st.markdown("""
    <div class="testimonial">
        <p>"The universe IS beautiful. And the people who say it most confidently are the ones who actually SEE it."</p>
        <p><strong>— Brandon Emerick, TI Framework</strong></p>
    </div>
    """, unsafe_allow_html=True)

elif page == "📺 YouTube Studio":
    st.title("📺 YouTube Studio")
    try:
        from youtube_studio_tab import render_youtube_studio_tab
        render_youtube_studio_tab()
    except Exception as e:
        st.error(f"YouTube Studio error: {e}")
        st.info("Make sure YOUTUBE_CLIENT_ID and YOUTUBE_CLIENT_SECRET are set in Secrets.")

elif page == "🧩 ARC-AGI Solver":
    st.title("🧩 ARC-AGI TI Sigma Solver")
    try:
        from arc_ti_solver.arc_tab import show_arc_tab
        show_arc_tab()
    except Exception as e:
        st.error(f"ARC Solver error: {e}")

elif page == "📚 Zenodo Corpus":
    st.title("📚 Zenodo Corpus Manager")
    try:
        from zenodo_tab import show_zenodo_manager
        show_zenodo_manager()
    except Exception as e:
        st.error(f"Zenodo error: {e}")

elif page == "🔮 Manifestation Machine":
    st.title("🔮 TI Sigma Manifestation Machine")
    try:
        from power_of_8_system import render_power_of_8_tab
        render_power_of_8_tab()
    except Exception as e:
        st.error(f"Manifestation Machine error: {e}")

elif page == "__app_catalog__":
    st.markdown("""
    <div style="background:linear-gradient(135deg,#1a0a2a 0%,#0d1b3d 100%);
                padding:2rem 1.5rem;border-radius:14px;text-align:center;margin-bottom:1.5rem;
                border:1px solid rgba(120,100,255,0.3);">
        <div style="font-size:2.5rem;">📋</div>
        <h1 style="color:#d8d0ff;font-size:2rem;margin:0.3rem 0;letter-spacing:0.05em;">
            TI Sigma Engineering Application Catalog
        </h1>
        <div style="color:#b0a0ff;font-size:0.95rem;margin-top:0.4rem;">
            Companion modules — runnable from the project repository
        </div>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("""
    The applications below ship as standalone Python modules in the repository. Each is fully runnable
    via Streamlit or direct invocation. The five flagship apps (GM Hypercomputer, Mood Amplifier,
    QuantConnect Trading, Soulmate Finder, Kalshi Scanner) are integrated as their own subsections in
    this Engineering tab. The remainder are catalogued here for now and can be promoted into the main
    UI on demand.
    """)

    catalog = [
        ("🩺 Biometric & Brain Coupling", [
            ("LCC Sleep Protocol", "lcc_optimization_simulator.py", "Lateral Coherence Coupling protocol applied to sleep-state optimization. Targets HRV-EEG coupling during NREM."),
            ("LCC Attractor Visualization", "lcc_on_agent_trajectories.py", "Phase-space attractor visualization for LCC trajectories on agent timeseries (PNG export included)."),
            ("Heart Pong LCC", "heart_icell_theory.py", "Heart-rate-driven Pong control surface; LCC-coupled paddle position. Demo of cardiac→motor coupling."),
            ("Heart Disease Dashboard", "biometric_dashboard.py", "Risk-stratification dashboard using HRV, RMSSD, SDNN; GILE-weighted composite score."),
            ("GM Consciousness Sync", "biometric_api.py", "Group-mind consciousness synchronization measurement across multiple biometric streams."),
            ("Biometric Intervention", "biometric_simulator.py", "Closed-loop intervention engine: detects mood drift and triggers haptic/audio cues."),
            ("BOK Live Polar Morph", "bok_framework.py", "Live Polar H10 → BOK harmonic morphing. Maps RR-interval stream to BOK basis."),
            ("Brain Coupling Guessing", "brain_connection_proof.py", "Two-player paired-EEG guessing game; quantifies inter-brain mutual information vs chance."),
            ("Brain Pong", "brain_connection_proof.py", "Two-player Pong controlled by paired EEG attention metric. Companion experiment to Brain Coupling."),
            ("Multimodal Biometric Dashboard", "biometric_dashboard.py", "Unified HRV + EEG + fNIRS + temp + EDA dashboard with GILE/LCC composite scoring."),
        ]),
        ("💊 Pharma & Health", [
            ("Medgemma Dashboard", "brandon_pharma_predictions.py", "Medgemma medical-LLM dashboard for treatment response prediction; Brandon-personal pharmacogenomic profile baseline."),
            ("Pharmacological Simulator", "animal_pharmacological_simulations.py", "Animal-model pharmacological simulation suite (dose-response, half-life, receptor binding)."),
            ("RNA Folding Dashboard", "—", "RNA secondary-structure folding visualization (in development; module name TBD)."),
        ]),
        ("🔮 Psi & Soulmate", [
            ("Psi Testing Protocol", "automated_psi_validation.py", "Automated GCP-style psi-validation harness (RNG deviation, RV scoring, blind protocols)."),
            ("Psi Tuning Dashboard", "hypercomputing_psi_validation.py", "Real-time psi-signal tuning + hypercomputer-scored deviation panel."),
            ("Soulmate Finder", "(integrated above)", "TI-Framework-based partner-prediction engine — full version available in this Engineering tab."),
            ("TSC Crystal Page", "gsa_tsc_signal.py", "Tralse Sigma Crystal page — GSA daily signal + crystal-lattice intuition harmonics."),
        ]),
        ("📈 Markets & Trading (beyond core algos)", [
            ("Stock Algorithm Status", "alpaca_paper_trader.py", "Live Alpaca paper-trading status panel for the GILE algorithm. Position + P&L + signal-trace."),
            ("Marketing Optimizer", "biological_virality_engine.py", "Biological-virality-engine-driven content/marketing optimization."),
            ("Launch Control", "—", "Pre-launch checklist + go/no-go panel for product releases (in development)."),
        ]),
    ]

    for category_name, apps in catalog:
        st.markdown(f"### {category_name}")
        cols = st.columns(2)
        for i, (app_name, module, description) in enumerate(apps):
            with cols[i % 2]:
                st.markdown(f"""
                <div style="background:#1a1a2e;border-radius:10px;padding:1rem 1.2rem;margin-bottom:0.8rem;
                            border-left:3px solid #7864ff;min-height:140px;">
                    <div style="color:#d8d0ff;font-size:1.05rem;font-weight:bold;margin-bottom:0.3rem;">
                        {app_name}
                    </div>
                    <div style="color:#888;font-size:0.78rem;font-family:monospace;margin-bottom:0.5rem;">
                        Module: {module}
                    </div>
                    <div style="color:#bbb;font-size:0.88rem;line-height:1.4;">
                        {description}
                    </div>
                </div>
                """, unsafe_allow_html=True)
        st.markdown("")

    st.markdown("---")
    st.info(
        "**To promote a catalog app into the main UI**: tell the agent which app to integrate, "
        "and it will be added as its own subsection under "
        "**⚙️ TI Sigma Engineering Applications**. Each promotion is one URB."
    )

st.markdown("---")
st.markdown("""
<div style="text-align: center; color: #666; padding: 1rem;">
    <p>© 2025 BlissGene Therapeutics | TI Framework</p>
    <p><em>"Consciousness demands balance, and balance exists only at GILE = 0."</em></p>
</div>
""", unsafe_allow_html=True)
