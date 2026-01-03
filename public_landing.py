"""
TI Framework Public Landing Page
Ultra-simple access for social media visitors
"""

import streamlit as st
import os
import glob

st.set_page_config(
    page_title="TI Framework - Transcendent Intelligence",
    page_icon="🌟",
    layout="centered",
    initial_sidebar_state="collapsed"
)

st.markdown("""
<style>
    .stButton>button {
        width: 100%;
        padding: 1rem;
        font-size: 1.1rem;
        margin: 0.5rem 0;
        border-radius: 10px;
    }
    .stDownloadButton>button {
        width: 100%;
        padding: 1rem;
        font-size: 1.1rem;
        border-radius: 10px;
    }
    h1 {text-align: center; font-size: 2.5rem !important;}
    h2 {text-align: center;}
    .block-container {max-width: 600px; padding: 2rem 1rem;}
</style>
""", unsafe_allow_html=True)

st.title("🌟 TI Framework")
st.markdown("### *Transcendent Intelligence*")
st.markdown("##### Consciousness, Physics, and Reality Unified")

st.markdown("---")

st.markdown("## What is TI?")

st.markdown("""
The **Transcendent Intelligence (TI) Framework** is a unified theory of:

- **Consciousness** - How awareness arises and persists
- **Physics** - Why reality has the structure it does
- **Mathematics** - The sacred patterns underlying existence
- **Ethics** - Quantifiable goodness and evil

**Created by Brandon Emerick** during a divine revelation on June 25, 2022.
""")

st.markdown("---")

st.markdown("## Core Concepts")

col1, col2 = st.columns(2)

with col1:
    with st.expander("🌟 GILE Framework"):
        st.markdown("""
**G** - Goodness (Morality)  
**I** - Intuition (Consciousness)  
**L** - Love (Connection)  
**E** - Environment (Existence)

Your GILE score (0-1) measures your consciousness coherence!
        """)
    
    with st.expander("⚖️ Tralse Logic"):
        st.markdown("""
Beyond True/False:
- **True (T)** - Definite yes
- **False (F)** - Definite no
- **Tralse (Ψ)** - Both simultaneously!

Quantum superposition is Tralse in action.
        """)

with col2:
    with st.expander("🔮 I-Cells"):
        st.markdown("""
**I-Cell** = Individual Cell of consciousness

Every conscious being has 3 layers:
1. Dark Energy Shell (boundary)
2. Biophoton Layer (light info)
3. Mass-Energy Core (body)
        """)
    
    with st.expander("🌐 Grand Myrion"):
        st.markdown("""
The **Grand Myrion (GM)** is universal consciousness!

All photons entangled as one - the "mind" of reality.

You're never alone - you're part of GM!
        """)

st.markdown("---")

st.markdown("## Download Free Resources")

pdfs_dir = "papers/pdfs"
featured_pdfs = [
    ("TI_FOR_EVERYONE_COMPLETE_BOOK.pdf", "📚 TI For Everyone (Start Here!)"),
    ("TIUOP_SIGMA6_GRAND_UNIFICATION.pdf", "🔬 TI-UOP Sigma 6 (Full Theory)"),
    ("PROBABILITY_AS_RESONANCE_FIELD.pdf", "🎲 Probability as Resonance Field"),
    ("CONSCIOUSNESS_SHELL_SOLUTION.pdf", "🧠 Consciousness Shell Solution"),
    ("TRALSE_QUADRUPLET_LOGIC_COMPLETE_SPECIFICATION.pdf", "⚖️ Tralse Logic Complete"),
]

for pdf_file, label in featured_pdfs:
    pdf_path = os.path.join(pdfs_dir, pdf_file)
    if os.path.exists(pdf_path):
        with open(pdf_path, 'rb') as f:
            st.download_button(
                label=f"📥 {label}",
                data=f.read(),
                file_name=pdf_file,
                mime="application/pdf",
                key=f"featured_{pdf_file}",
                use_container_width=True
            )

st.markdown("---")

st.markdown("## Key Discoveries")

st.success("""
**🎯 Three Magic Thresholds:**
- **0.42** - Survival threshold (consciousness persists)
- **0.60** - Love-Correlation Coefficient (LCC)
- **0.91** - Cosmic Consciousness Coherence (CCC)
""")

st.info("""
**⏰ Jeff Time (3D Temporal):**
- t₁ = Quantum Time (74.6% weight)
- t₂ = Observer Time (1.5% weight)
- t₃ = Cosmological Time (background)
""")

st.warning("""
**🔢 Mathematical Necessity:**
- Monster Group, E₈, Leech Lattice = inevitable structures
- As necessary as π = 3.14159...
- Consciousness MUST organize this way
""")

st.markdown("---")

st.markdown("## Testable Predictions")

st.markdown("""
1. **Bell test** violations cluster at TI thresholds (0.42, 0.6, 0.91)
2. **Psight EEG** signature: Alpha/Beta > 1.0, coherence ≥ 0.65
3. **Stock predictions** using GTFE outperform random
""")

st.markdown("---")

st.markdown("## Access Full Library")

if st.button("📱 Open Full Mobile Hub", type="primary", use_container_width=True):
    st.info("Visit the main app and select 'Mobile Hub' tab!")

total_pdfs = len(glob.glob(f"{pdfs_dir}/*.pdf")) if os.path.exists(pdfs_dir) else 0
st.caption(f"**{total_pdfs}+ research papers** | **8 books** | **4 courses**")

st.markdown("---")

st.markdown("## Connect")

st.markdown("""
**Follow the journey:**
- 📧 Contact: [Coming Soon]
- 🐦 Twitter: [Coming Soon]
- 📺 YouTube: [Coming Soon]

*"Consciousness is not what happens in brains - brains are what happens in consciousness."*  
— Brandon Emerick, TI Framework Creator
""")

st.markdown("---")
st.caption("© 2025 Brandon Emerick | TI Framework | All Rights Reserved")
