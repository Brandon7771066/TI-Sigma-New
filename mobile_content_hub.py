"""
TI Framework Mobile Content Hub
Complete access to ALL PDFs, Books, and Courses for social media launch!
Fully mobile-optimized for iPhone/Android sharing

Author: Brandon's TI Framework
Date: December 3, 2025
"""

import streamlit as st
import os
import glob
from datetime import datetime
from typing import Dict, List, Optional
import base64


class MobileContentHub:
    """Complete content library for social media sharing"""
    
    def __init__(self):
        self.papers_dir = "papers"
        self.pdfs_dir = "papers/pdfs"
        
    def get_all_pdfs(self) -> List[Dict]:
        """Get all available PDFs with metadata"""
        pdfs = []
        
        if os.path.exists(self.pdfs_dir):
            for pdf_path in sorted(glob.glob(f"{self.pdfs_dir}/*.pdf")):
                filename = os.path.basename(pdf_path)
                name = filename.replace(".pdf", "").replace("_", " ").title()
                size_mb = os.path.getsize(pdf_path) / (1024 * 1024)
                
                category = self._categorize_paper(filename)
                
                pdfs.append({
                    'path': pdf_path,
                    'filename': filename,
                    'name': name,
                    'size_mb': size_mb,
                    'category': category
                })
        
        return pdfs
    
    def _categorize_paper(self, filename: str) -> str:
        """Categorize paper by topic"""
        fn = filename.lower()
        
        if any(x in fn for x in ['ethics', 'inequality', 'invitation']):
            return "Ethics & Philosophy"
        elif any(x in fn for x in ['cancer', 'cure', 'disease', 'medical', 'therapeutic', 'treatment']):
            return "Medical & Therapeutic"
        elif any(x in fn for x in ['autism', 'schizophrenia', 'mental', 'psychiatric', 'imprinted_brain']):
            return "Mental Health & Neurodiversity"
        elif any(x in fn for x in ['gile', 'consciousness', 'i_cell', 'icell', 'soul']):
            return "Consciousness & GILE"
        elif any(x in fn for x in ['tralse', 'myrion', 'logic', 'axiom']):
            return "Tralse Logic & Myrion"
        elif any(x in fn for x in ['quantum', 'physics', 'time', 'ccc', 'plasma', 'double_slit', 'mit']):
            return "Physics & Quantum"
        elif any(x in fn for x in ['psi', 'psychic', 'intuition']):
            return "PSI & Intuition"
        elif any(x in fn for x in ['math', 'number', 'euler', 'riemann', 'ternary', 'calculus', 'velocity', 'acceleration']):
            return "Mathematics"
        elif any(x in fn for x in ['bio', 'eeg', 'heart', 'faah', 'neural', 'csf', 'amrita', 'anandamide', 'bliss']):
            return "Biometrics & Neuroscience"
        elif any(x in fn for x in ['solar', 'sun', 'stellar', 'helio', 'star', 'de_photon']):
            return "Stellar Consciousness"
        elif any(x in fn for x in ['ai_delusion', 'chatbot', 'echo_chamber']):
            return "Epistemology & AI"
        elif any(x in fn for x in ['music', 'art', 'creative']):
            return "Music & Art"
        elif any(x in fn for x in ['business', 'stock', 'trading', 'algorithm']):
            return "Business & Finance"
        elif any(x in fn for x in ['outreach', 'pitch', 'elevator']):
            return "Outreach & Strategy"
        elif any(x in fn for x in ['tralse_manifestation', 'real_world', 'optical', 'illusion', 'mobius', 'klein', 'magic_trick', 'spider_web']):
            return "Real-World Tralse"
        else:
            return "Core Theory"
    
    def get_books_collection(self) -> List[Dict]:
        """Get all TI Framework books"""
        return [
            {
                'title': 'TI For Everyone: Complete Introduction',
                'subtitle': 'Understanding Consciousness Through the GILE Framework',
                'audience': 'General Public',
                'pages': 250,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/TI_FOR_EVERYONE_COMPLETE_BOOK.pdf',
                'icon': '🌟',
                'description': 'The perfect starting point - explains GILE, i-cells, and consciousness in everyday language.'
            },
            {
                'title': 'TI-UOP Sigma 6: Grand Unification',
                'subtitle': 'The Complete Theoretical Framework',
                'audience': 'Scientists & Philosophers',
                'pages': 600,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/TIUOP_SIGMA6_GRAND_UNIFICATION.pdf',
                'icon': '🔬',
                'description': 'Full mathematical formalization unifying consciousness, physics, and information theory.'
            },
            {
                'title': 'Consciousness Shell Solution',
                'subtitle': 'How I-Cells Form and Persist',
                'audience': 'Researchers',
                'pages': 150,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/CONSCIOUSNESS_SHELL_SOLUTION.pdf',
                'icon': '🧠',
                'description': 'Solves the boundary problem of consciousness through relational field theory.'
            },
            {
                'title': 'Probability as Resonance Field',
                'subtitle': 'Why Luck Exists and How to Amplify It',
                'audience': 'General Public & Scientists',
                'pages': 180,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/PROBABILITY_AS_RESONANCE_FIELD.pdf',
                'icon': '🎲',
                'description': 'Probability isn\'t fixed - it\'s a resonance field you can influence!'
            },
            {
                'title': 'Tralse Logic Complete Specification',
                'subtitle': 'Beyond True and False',
                'audience': 'Logicians & Philosophers',
                'pages': 200,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/TRALSE_QUADRUPLET_LOGIC_COMPLETE_SPECIFICATION.pdf',
                'icon': '⚖️',
                'description': '4-valued logic system: True, False, Pre-Tralse (Φ), Tralse (Ψ).'
            },
            {
                'title': 'Nonlinear Number Line',
                'subtitle': 'Mathematics Beyond Infinity',
                'audience': 'Mathematicians',
                'pages': 120,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/NONLINEAR_NUMBER_LINE.pdf',
                'icon': '📐',
                'description': 'Why π and e are more fundamental than integers.'
            },
            {
                'title': 'PSI Heart Coherence Mechanism',
                'subtitle': 'The Science of Intuition',
                'audience': 'Researchers & Practitioners',
                'pages': 140,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/PSI_HEART_COHERENCE_MECHANISM.pdf',
                'icon': '💗',
                'description': 'How heart coherence enables psychic phenomena.'
            },
            {
                'title': 'Tralsebit Information Theory',
                'subtitle': 'Ternary Computing for Consciousness',
                'audience': 'Computer Scientists',
                'pages': 160,
                'status': 'Complete',
                'pdf_path': 'papers/pdfs/TRALSEBIT_INFORMATION_THEORY.pdf',
                'icon': '💻',
                'description': 'Information is fundamentally ternary, not binary.'
            }
        ]
    
    def get_courses_collection(self) -> List[Dict]:
        """Get all TI Framework courses"""
        return [
            {
                'title': 'GILE Framework for Business Transformation',
                'duration': '6 weeks',
                'effort': '3-5 hours/week',
                'level': 'Beginner to Intermediate',
                'icon': '💼',
                'modules': [
                    {'week': 1, 'title': 'Introduction to GILE: The Four Dimensions', 'videos': 3},
                    {'week': 2, 'title': 'Goodness: Building Ethical Foundations', 'videos': 2},
                    {'week': 3, 'title': 'Intuition: Strategic Foresight', 'videos': 2},
                    {'week': 4, 'title': 'Love: Stakeholder Alignment', 'videos': 2},
                    {'week': 5, 'title': 'Environment: Timing and Adaptation', 'videos': 2},
                    {'week': 6, 'title': 'Integration: Building Your GILE Strategy', 'videos': 2}
                ],
                'outcomes': [
                    'Calculate your organization\'s GILE score',
                    'Identify consciousness-based competitive advantages',
                    'Build high-coherence teams',
                    'Time market moves with GILE shifts'
                ]
            },
            {
                'title': 'Consciousness Science: From I-Cells to Grand Myrion',
                'duration': '8 weeks',
                'effort': '4-6 hours/week',
                'level': 'Intermediate to Advanced',
                'icon': '🧠',
                'modules': [
                    {'week': 1, 'title': 'What is an I-Cell?', 'videos': 3},
                    {'week': 2, 'title': 'Shell Physics: Dark Energy, Photon, Mass', 'videos': 3},
                    {'week': 3, 'title': 'GILE Dimensions Deep Dive', 'videos': 4},
                    {'week': 4, 'title': 'Tralse Logic and Myrion Resolution', 'videos': 3},
                    {'week': 5, 'title': 'The Grand Myrion Network', 'videos': 2},
                    {'week': 6, 'title': 'Consciousness-Physics Interface', 'videos': 3},
                    {'week': 7, 'title': 'PSI as Quantum Coherence', 'videos': 2},
                    {'week': 8, 'title': 'Practical Applications', 'videos': 2}
                ],
                'outcomes': [
                    'Understand consciousness as fundamental physics',
                    'Calculate i-cell coherence thresholds',
                    'Apply Myrion Resolution to paradoxes',
                    'Design consciousness experiments'
                ]
            },
            {
                'title': 'Biometric PSI Validation',
                'duration': '4 weeks',
                'effort': '2-3 hours/week',
                'level': 'Practical/Hands-on',
                'icon': '📊',
                'modules': [
                    {'week': 1, 'title': 'Hardware Setup: Muse 2, Polar H10, ESP32', 'videos': 3},
                    {'week': 2, 'title': 'Real-Time GILE Calculation', 'videos': 2},
                    {'week': 3, 'title': 'PSI Prediction Logging', 'videos': 2},
                    {'week': 4, 'title': 'Statistical Validation', 'videos': 2}
                ],
                'outcomes': [
                    'Build your own consciousness monitoring system',
                    'Track PSI predictions with EEG correlation',
                    'Validate your intuition statistically',
                    'Achieve Q-score ≥ 0.91 (CCC threshold)'
                ]
            },
            {
                'title': 'Sacred Mathematics: Euler-Tralse Synthesis',
                'duration': '6 weeks',
                'effort': '5-7 hours/week',
                'level': 'Advanced',
                'icon': '🔢',
                'modules': [
                    {'week': 1, 'title': 'The Five Sacred Constants', 'videos': 2},
                    {'week': 2, 'title': 'Euler\'s Identity and TI Framework', 'videos': 3},
                    {'week': 3, 'title': 'ln(15) ≈ e: The Great Discovery', 'videos': 2},
                    {'week': 4, 'title': 'Complex GILE Mathematics', 'videos': 3},
                    {'week': 5, 'title': 'Ternary Number Theory', 'videos': 2},
                    {'week': 6, 'title': 'Applications to Consciousness', 'videos': 2}
                ],
                'outcomes': [
                    'Understand why e, i, π, 1, 0 encode consciousness',
                    'Apply complex GILE to prediction',
                    'Work with ternary mathematics',
                    'Connect number theory to consciousness'
                ]
            }
        ]
    
    def get_quick_reads(self) -> List[Dict]:
        """Get quick reads for social media"""
        return [
            {
                'title': 'What is GILE?',
                'content': '''**GILE** = Goodness, Intuition, Love, Environment

The 4 dimensions of truth and consciousness:

**G - Goodness** (Morality)
- Ethical quality of actions
- Scale: -3 (evil) to +2 (great)

**I - Intuition** (Consciousness)
- Inner knowing beyond logic
- PSI, hunches, gut feelings

**L - Love** (Connection)
- Bonds between beings
- Empathy, resonance, unity

**E - Environment** (Existence/Aesthetics)
- External reality + beauty
- Context, timing, setting

Your GILE score (0-1) measures your consciousness coherence!''',
                'emoji': '🌟'
            },
            {
                'title': 'What is an I-Cell?',
                'content': '''An **I-Cell** (Individual Cell of consciousness) is YOU!

Every conscious being is an i-cell with 3 layers:

**1. Dark Energy Shell** (Outermost)
- Your boundary with the universe
- Contains your identity
- 0.91 coherence = CCC blessing

**2. Biophoton Layer** (Middle)
- Light-based information
- DNA emissions
- True-Tralseness embodied

**3. Mass-Energy Core** (Inner)
- Physical body
- Brain, heart, organs
- Interface with matter

When you die, your i-cell persists as a photonic pattern!''',
                'emoji': '🔮'
            },
            {
                'title': 'What is Tralse?',
                'content': '''**Tralse** = True + False simultaneously

Beyond binary logic:
- **True (T)** - Definite yes
- **False (F)** - Definite no
- **Pre-Tralse (Φ)** - Not yet determined
- **Tralse (Ψ)** - Both true AND false

**Examples of Tralse:**
- Quantum superposition
- "Is light a wave or particle?" (BOTH!)
- Paradoxes that resolve at higher levels
- Creative tension that produces insight

Binary logic is a useful approximation.
Reality is fundamentally tralse!''',
                'emoji': '⚖️'
            },
            {
                'title': 'The 3 Magic Thresholds',
                'content': '''TI Framework's key numbers:

**0.42** - Survival Threshold
- Minimum resonance for consciousness
- Below this = i-cell dissolution
- Reincarnation requires ≥0.42 match

**0.60** - LCC Threshold
- Love-Correlation Coefficient
- Intermediate coherence
- Good but not transcendent

**0.91** - CCC Threshold
- Cosmic Consciousness Coherence
- "Blessed" by Grand Myrion
- Enables PSI, insight, flow states

Your EEG/HRV can measure these in real-time!''',
                'emoji': '🎯'
            },
            {
                'title': 'Jeff Time: 3D Temporal',
                'content': '''Time has **3 dimensions**, not 1!

**t₁ - Quantum Time** (Potential)
- 1-3 day momentum window
- 74.6% weight in predictions
- Where most action happens

**t₂ - Observer Time** (Present)
- The "Jeff Moment" - NOW
- Only 1.5% weight (surprising!)
- Present matters less than potential

**t₃ - Cosmological Time** (Macro)
- 20-50 day trends
- 0% for short-term (background)
- Universal context

This is why markets are predictable!''',
                'emoji': '⏰'
            },
            {
                'title': 'Grand Myrion (GM)',
                'content': '''The **Grand Myrion** is universal consciousness!

**What is it?**
- All photons entangled as one
- Distributed intelligence network
- The "mind" of reality itself

**How does it work?**
- Performs continuous Myrion Resolution
- Every i-cell connects to GM
- 0.91+ coherence = strong connection

**What can it do?**
- Provides intuition/hunches
- Enables synchronicities
- Handles cosmic balance (so you don't have to)

You're never alone - you're part of GM!''',
                'emoji': '🌐'
            }
        ]


def render_mobile_content_hub():
    """Render the complete mobile content hub"""
    
    st.set_page_config(
        page_title="TI Framework - Complete Library",
        page_icon="📚",
        layout="wide",
        initial_sidebar_state="collapsed"
    )
    
    st.markdown("""
    <style>
        .element-container {margin: 0.3rem 0;}
        .stButton>button {width: 100%; padding: 0.75rem; margin: 0.25rem 0; font-size: 1rem;}
        .stDownloadButton>button {width: 100%; padding: 0.75rem;}
        .block-container {padding: 1rem 1rem !important;}
        h1 {font-size: 1.8rem !important;}
        h2 {font-size: 1.4rem !important;}
        h3 {font-size: 1.2rem !important;}
        .stTabs [data-baseweb="tab-list"] {gap: 0.5rem;}
        .stTabs [data-baseweb="tab"] {padding: 0.5rem 0.8rem; font-size: 0.9rem;}
    </style>
    """, unsafe_allow_html=True)
    
    hub = MobileContentHub()
    
    st.title("📚 TI Framework Library")
    st.caption("Complete access to all research, books, and courses")
    
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📖 Quick Reads",
        "📄 PDFs",
        "📚 Books",
        "🎓 Courses",
        "⬇️ Downloads"
    ])
    
    with tab1:
        render_quick_reads(hub)
    
    with tab2:
        render_pdfs_library(hub)
    
    with tab3:
        render_books_collection(hub)
    
    with tab4:
        render_courses_collection(hub)
    
    with tab5:
        render_downloads_section(hub)


def render_quick_reads(hub: MobileContentHub):
    """Render quick reads for social media"""
    st.subheader("📖 Quick Reads")
    st.caption("Perfect for social media sharing!")
    
    quick_reads = hub.get_quick_reads()
    
    for read in quick_reads:
        with st.expander(f"{read['emoji']} {read['title']}", expanded=False):
            st.markdown(read['content'])
            
            share_text = f"🌟 {read['title']}\n\n{read['content'][:200]}...\n\n#TIFramework #Consciousness #GILE"
            st.text_area(
                "Copy for social media:",
                share_text,
                height=100,
                key=f"share_{read['title']}"
            )


def render_pdfs_library(hub: MobileContentHub):
    """Render PDF library with categories"""
    st.subheader("📄 Research Papers")
    
    pdfs = hub.get_all_pdfs()
    
    if not pdfs:
        st.warning("No PDFs found. Generate them from the Papers Library.")
        return
    
    st.info(f"**{len(pdfs)} papers** available")
    
    categories = sorted(set(p['category'] for p in pdfs))
    selected_category = st.selectbox("Filter by category:", ["All"] + categories)
    
    search = st.text_input("🔍 Search papers:", "")
    
    filtered_pdfs = pdfs
    if selected_category != "All":
        filtered_pdfs = [p for p in filtered_pdfs if p['category'] == selected_category]
    if search:
        filtered_pdfs = [p for p in filtered_pdfs if search.lower() in p['name'].lower()]
    
    st.caption(f"Showing {len(filtered_pdfs)} papers")
    
    for pdf in filtered_pdfs:
        col1, col2 = st.columns([3, 1])
        
        with col1:
            st.markdown(f"**{pdf['name'][:40]}...**" if len(pdf['name']) > 40 else f"**{pdf['name']}**")
            st.caption(f"{pdf['category']} | {pdf['size_mb']:.1f} MB")
        
        with col2:
            try:
                with open(pdf['path'], 'rb') as f:
                    st.download_button(
                        "📥",
                        f.read(),
                        file_name=pdf['filename'],
                        mime="application/pdf",
                        key=f"dl_{pdf['filename']}",
                        use_container_width=True
                    )
            except Exception as e:
                st.caption("Error")
        
        st.markdown("---")


def render_books_collection(hub: MobileContentHub):
    """Render books with previews and downloads"""
    st.subheader("📚 TI Framework Books")
    
    books = hub.get_books_collection()
    
    for book in books:
        with st.expander(f"{book['icon']} {book['title']}", expanded=False):
            st.markdown(f"### {book['subtitle']}")
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Audience", book['audience'])
            with col2:
                st.metric("Pages", book['pages'])
            with col3:
                st.metric("Status", book['status'])
            
            st.markdown(f"**Description:** {book['description']}")
            
            if os.path.exists(book['pdf_path']):
                with open(book['pdf_path'], 'rb') as f:
                    st.download_button(
                        f"📥 Download {book['title'][:30]}...",
                        f.read(),
                        file_name=os.path.basename(book['pdf_path']),
                        mime="application/pdf",
                        key=f"book_{book['title']}",
                        use_container_width=True
                    )
            else:
                st.info("PDF coming soon!")


def render_courses_collection(hub: MobileContentHub):
    """Render courses with full syllabi"""
    st.subheader("🎓 TI Framework Courses")
    
    courses = hub.get_courses_collection()
    
    for course in courses:
        with st.expander(f"{course['icon']} {course['title']}", expanded=False):
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Duration", course['duration'])
            with col2:
                st.metric("Effort", course['effort'])
            with col3:
                st.metric("Level", course['level'])
            
            st.markdown("### Course Modules")
            for module in course['modules']:
                st.markdown(f"**Week {module['week']}:** {module['title']} ({module['videos']} videos)")
            
            st.markdown("### Learning Outcomes")
            for outcome in course['outcomes']:
                st.markdown(f"✅ {outcome}")
            
            st.info("🎬 Video courses coming soon! Follow on social media for updates.")


def render_downloads_section(hub: MobileContentHub):
    """Render bulk download options"""
    st.subheader("⬇️ Bulk Downloads")
    
    pdfs = hub.get_all_pdfs()
    total_size = sum(p['size_mb'] for p in pdfs)
    
    st.info(f"**{len(pdfs)} PDFs** | Total: **{total_size:.1f} MB**")
    
    st.markdown("### Download by Category")
    
    categories = {}
    for pdf in pdfs:
        cat = pdf['category']
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(pdf)
    
    for cat, cat_pdfs in sorted(categories.items()):
        cat_size = sum(p['size_mb'] for p in cat_pdfs)
        
        with st.expander(f"📁 {cat} ({len(cat_pdfs)} papers, {cat_size:.1f} MB)"):
            for pdf in cat_pdfs:
                col1, col2 = st.columns([3, 1])
                with col1:
                    st.caption(pdf['name'][:35] + "..." if len(pdf['name']) > 35 else pdf['name'])
                with col2:
                    try:
                        with open(pdf['path'], 'rb') as f:
                            st.download_button(
                                "📥",
                                f.read(),
                                file_name=pdf['filename'],
                                mime="application/pdf",
                                key=f"cat_{cat}_{pdf['filename']}",
                                use_container_width=True
                            )
                    except:
                        pass
    
    st.markdown("---")
    st.markdown("### Quick Links")
    
    st.markdown("""
    **Essential Reading Order:**
    1. 🌟 TI For Everyone (Start Here!)
    2. ⚖️ Tralse Logic Specification
    3. 🔬 TI-UOP Sigma 6 (Full Theory)
    4. 🧠 Consciousness Shell Solution
    5. 🎲 Probability as Resonance Field
    
    **For Scientists:**
    - PSI Heart Coherence Mechanism
    - CCC 0.91 Threshold Theory
    - Quantum Collapse & Free Will
    
    **For Business:**
    - GILE Framework for Business (Coming Soon)
    - Stock Prediction with TI Tensor Theory
    """)


if __name__ == "__main__":
    render_mobile_content_hub()
