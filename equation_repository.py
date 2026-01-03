"""
Equation Repository App - Specialist App #1
Houses all TWA, HEM, MR equations with LaTeX rendering and interactive calculator
"""

import streamlit as st
import json
from typing import Dict, List
import re

# Page config
st.set_page_config(
    page_title="Equation Repository",
    page_icon="🔢",
    layout="wide"
)

# ============================================================================
# EQUATION DATABASE
# ============================================================================

EQUATIONS = {
    "TWA": {
        "Fuse Operator": {
            "latex": r"\Psi_{AB} = \text{Fuse}(\Psi_A, \Psi_B) = \alpha\Psi_A + \beta\Psi_B + \gamma\Psi_{AB}^{new}",
            "description": "Combines two tralse states into unified state with emergent component",
            "variables": {
                "Ψ_A": "First tralse state",
                "Ψ_B": "Second tralse state",
                "α": "Weight for state A (0-1)",
                "β": "Weight for state B (0-1)",
                "γ": "Emergent synergy coefficient",
                "Ψ_AB^new": "Emergent tralse component"
            },
            "category": "operators",
            "paper": "TWA_COMPLETE_DOCUMENTATION.md"
        },
        "Split Operator": {
            "latex": r"\text{Split}(\Psi_{AB}) \rightarrow \{\Psi_A, \Psi_B\} + \Delta_{residue}",
            "description": "Separates unified tralse state into components with residue",
            "variables": {
                "Ψ_AB": "Unified tralse state",
                "Ψ_A": "First separated component",
                "Ψ_B": "Second separated component",
                "Δ_residue": "Remnant from separation (often ≠ 0)"
            },
            "category": "operators",
            "paper": "TWA_COMPLETE_DOCUMENTATION.md"
        },
        "Rebase Operator": {
            "latex": r"\Psi' = \text{Rebase}(\Psi, \phi_{new}) = R(\phi_{new})\Psi",
            "description": "Transforms tralse state to new reference frame",
            "variables": {
                "Ψ": "Original tralse state",
                "φ_new": "New reference frame",
                "R(φ_new)": "Transformation operator",
                "Ψ'": "Rebased tralse state"
            },
            "category": "operators",
            "paper": "TWA_COMPLETE_DOCUMENTATION.md"
        },
        "Tralse Quadruplet": {
            "latex": r"\Psi = (T, F, \Phi, \Psi) \quad \text{where } T + F + \Phi + \Psi = 1",
            "description": "Four-component tralse state: True, False, Wave, Anti-wave",
            "variables": {
                "T": "True component (0-1)",
                "F": "False component (0-1)",
                "Φ": "Wave component (superposition)",
                "Ψ": "Anti-wave component (complement)"
            },
            "category": "foundations",
            "paper": "TWA_COMPLETE_DOCUMENTATION.md"
        }
    },
    
    "HEM": {
        "6D State Vector": {
            "latex": r"\vec{H} = (V, A, D, W, T, S) \in \mathbb{R}^6",
            "description": "Holistic Existence Matrix (formerly ESS) - six-dimensional consciousness characterization",
            "variables": {
                "V": "Valence (pleasure-displeasure axis)",
                "A": "Arousal (activation level)",
                "D": "Dominance (control-submission)",
                "W": "Wave Coherence (harmonic alignment)",
                "T": "Temporal Binding (time integration)",
                "S": "Spatial Resonance (location binding)"
            },
            "category": "foundations",
            "paper": "Validation_Framework.md"
        },
        "Mood Prediction": {
            "latex": r"P(\text{mood}_{t+1}) = f(\vec{H}_t, \Delta\vec{H}, \text{context})",
            "description": "77% accurate mood shift forecasting using HEM trajectory",
            "variables": {
                "mood_t+1": "Future mood state",
                "H_t": "Current HEM vector",
                "ΔH": "HEM velocity (rate of change)",
                "context": "Environmental factors",
                "f": "Learned prediction function"
            },
            "category": "applications",
            "paper": "Validation_Framework.md"
        },
        "HEM Distance": {
            "latex": r"d(\vec{H}_1, \vec{H}_2) = \sqrt{\sum_{i=1}^{6} w_i(H_{1,i} - H_{2,i})^2}",
            "description": "Weighted Euclidean distance between two HEM states",
            "variables": {
                "H_1": "First HEM state",
                "H_2": "Second HEM state",
                "w_i": "Dimension weight (importance)",
                "d": "Psychological distance"
            },
            "category": "metrics",
            "paper": "Validation_Framework.md"
        }
    },
    
    "MR": {
        "Addition with Synergy": {
            "latex": r"\text{MR}(a) \oplus \text{MR}(b) = \text{MR}(a + b + \Delta_{synergy}, \rho_c)",
            "description": "MR addition accounts for emergent synergy (1+1 can equal 3!)",
            "variables": {
                "a": "First value",
                "b": "Second value",
                "Δ_synergy": "Emergent contribution (positive or negative)",
                "ρ_c": "Combined permissibility"
            },
            "category": "operations",
            "paper": "MR_ARITHMETIC_REVOLUTION.md"
        },
        "Subtraction with Residue": {
            "latex": r"\text{MR}(a) \ominus \text{MR}(b) = \text{MR}(a - b + \Delta_{residue}, \rho_c)",
            "description": "MR subtraction includes residual effects (loss leaves traces!)",
            "variables": {
                "a": "Initial value",
                "b": "Removed value",
                "Δ_residue": "What remains after removal",
                "ρ_c": "Combined permissibility"
            },
            "category": "operations",
            "paper": "MR_ARITHMETIC_REVOLUTION.md"
        },
        "Permissibility Distribution": {
            "latex": r"\rho \in (-3, 2) \quad \text{or} \quad w(x) = \ln(|x| + 1) \text{ for } |x| > 3",
            "description": "MR scale for contradiction resolution, natural log optimal outside bounds",
            "variables": {
                "ρ": "Permissibility value",
                "w(x)": "Weight function for extreme values",
                "x": "Raw permissibility score"
            },
            "category": "foundations",
            "paper": "papers/Myrion_Resolution_Framework.md"
        },
        "Composite MR": {
            "latex": r"\text{MR}_c = 0.4G + 0.25I + 0.25L + 0.1E",
            "description": "GILE-weighted composite Myrion Resolution",
            "variables": {
                "G": "Goodness dimension (-3 to 2)",
                "I": "Intuition dimension (-3 to 2)",
                "L": "Love dimension (-3 to 2)",
                "E": "Environment dimension (-3 to 2)",
                "MR_c": "Overall permissibility"
            },
            "category": "applications",
            "paper": "THREE_TYPES_OF_TRUTH.md"
        }
    },
    
    "I-Cells": {
        "Centralization Law": {
            "latex": r"\text{Centralization}_{\%} \propto \frac{1}{\text{Boundary Porosity}}",
            "description": "Inverse Symmetry Law: More interiority → More centralization",
            "variables": {
                "Centralization_%": "Percentage of cognition in central core",
                "Boundary Porosity": "Openness to external influences"
            },
            "category": "laws",
            "paper": "ICELL_IWEB_ONTOLOGY_COMPLETE.md"
        },
        "GM-Human Inversion": {
            "latex": r"\text{GM: } 33\% \text{ central}, \quad \text{Human: } 65\% \text{ central}",
            "description": "Grand Myrion vs Human centralization ratios (dialectical inversion)",
            "variables": {
                "GM": "Grand Myrion (ultimate i-web)",
                "Human": "Individual i-cell with internal i-web"
            },
            "category": "laws",
            "paper": "ICELL_IWEB_ONTOLOGY_COMPLETE.md"
        },
        "I-Cell Shell": {
            "latex": r"\text{I-Cell} = \{\text{Shell}, \text{Sprout}, \text{Bless}, \text{Heartbeat}, \text{Signature}\}",
            "description": "Five components of sovereign informational cell",
            "variables": {
                "Shell": "Boundary defining self/world",
                "Sprout": "Origin point (actualized by CCC)",
                "Bless": "Sovereignty granted by CCC",
                "Heartbeat": "Rhythmic persistence",
                "Signature": "Unique harmonic identity"
            },
            "category": "foundations",
            "paper": "ICELL_IWEB_ONTOLOGY_COMPLETE.md"
        }
    },
    
    "Music": {
        "Consonance-Goodness": {
            "latex": r"\text{Goodness}(interval) = \frac{1}{\text{numerator} + \text{denominator}}",
            "description": "Simple frequency ratios = Maximum goodness",
            "variables": {
                "interval": "Musical interval (e.g., octave, fifth)",
                "numerator": "Top of frequency ratio",
                "denominator": "Bottom of frequency ratio"
            },
            "category": "GILE",
            "paper": "MUSIC_GILE_FOUNDATIONS.md"
        },
        "Overtone Series": {
            "latex": r"f_n = n \cdot f_0, \quad n = 1, 2, 3, ...",
            "description": "Natural harmonics = Intuition engine (instant knowing)",
            "variables": {
                "f_n": "nth harmonic frequency",
                "f_0": "Fundamental frequency",
                "n": "Harmonic number"
            },
            "category": "GILE",
            "paper": "MUSIC_GILE_FOUNDATIONS.md"
        },
        "Phase Coherence": {
            "latex": r"C_{xy}(f) = \frac{|G_{xy}(f)|^2}{G_{xx}(f) \cdot G_{yy}(f)}",
            "description": "Love = Objective phase alignment (0-1)",
            "variables": {
                "C_xy": "Coherence between signals x and y",
                "G_xy": "Cross-spectral density",
                "G_xx, G_yy": "Auto-spectral densities",
                "f": "Frequency"
            },
            "category": "GILE",
            "paper": "MUSIC_GILE_FOUNDATIONS.md"
        }
    },
    
    "Truth": {
        "Absolute Truth Criterion": {
            "latex": r"\text{Absolute Truth} \iff \text{MR}(\text{all 4 dimensions}) \geq 2.0",
            "description": "CCC-level perfection across Existence, Morality, Meaning, Aesthetics",
            "variables": {
                "MR": "Myrion Resolution score",
                "4 dimensions": "Existence, Morality, Conscious Meaning, Aesthetics"
            },
            "category": "classification",
            "paper": "THREE_TYPES_OF_TRUTH.md"
        },
        "Objective Truth Criterion": {
            "latex": r"\text{Objective Truth} \iff \text{MR}_c > 0 \land \text{measurable}",
            "description": "Tralse-True, including objectively measurable qualia",
            "variables": {
                "MR_c": "Composite MR score",
                "measurable": "Has empirical correlates"
            },
            "category": "classification",
            "paper": "THREE_TYPES_OF_TRUTH.md"
        },
        "Relative Truth Criterion": {
            "latex": r"\text{Relative Truth} \iff \text{MR}_c \leq 0 \land \text{influential}",
            "description": "Tralse-False but held by powerful group (imagination-based)",
            "variables": {
                "MR_c": "Composite MR score",
                "influential": "Held by group with power"
            },
            "category": "classification",
            "paper": "THREE_TYPES_OF_TRUTH.md"
        }
    }
}

# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def render_equation(eq_data: Dict):
    """Render equation with LaTeX and metadata"""
    st.markdown(f"#### {eq_data.get('latex', 'N/A')}")
    st.markdown(f"**Description:** {eq_data.get('description', 'N/A')}")
    
    if 'variables' in eq_data:
        with st.expander("📖 Variable Definitions"):
            for var, definition in eq_data['variables'].items():
                st.markdown(f"- **{var}:** {definition}")
    
    col1, col2 = st.columns(2)
    with col1:
        st.caption(f"📂 Category: {eq_data.get('category', 'N/A')}")
    with col2:
        st.caption(f"📄 Paper: {eq_data.get('paper', 'N/A')}")

def search_equations(query: str) -> List[tuple]:
    """Search equations by keyword"""
    results = []
    query_lower = query.lower()
    
    for category, equations in EQUATIONS.items():
        for name, eq_data in equations.items():
            # Search in name, description, variables
            search_text = f"{name} {eq_data.get('description', '')} "
            search_text += " ".join(eq_data.get('variables', {}).values())
            
            if query_lower in search_text.lower():
                results.append((category, name, eq_data))
    
    return results

# ============================================================================
# MAIN APP
# ============================================================================

def main():
    st.title("🔢 Equation Repository")
    st.markdown("**All TWA, HEM, MR, I-Cell, Music, and Truth equations with LaTeX rendering**")
    
    # Sidebar navigation
    st.sidebar.title("🧭 Navigation")
    
    mode = st.sidebar.radio(
        "Select Mode:",
        ["Browse by Category", "Search Equations", "MR Calculator", "Export Equations"]
    )
    
    # ========================================================================
    # MODE 1: BROWSE BY CATEGORY
    # ========================================================================
    if mode == "Browse by Category":
        st.header("📚 Browse Equations")
        
        # Category selector
        category = st.selectbox(
            "Select Category:",
            list(EQUATIONS.keys())
        )
        
        st.subheader(f"{category} Equations")
        st.markdown("---")
        
        # Display all equations in category
        for eq_name, eq_data in EQUATIONS[category].items():
            with st.container():
                st.markdown(f"### {eq_name}")
                render_equation(eq_data)
                st.markdown("---")
    
    # ========================================================================
    # MODE 2: SEARCH EQUATIONS
    # ========================================================================
    elif mode == "Search Equations":
        st.header("🔍 Search Equations")
        
        query = st.text_input("Enter search term:", placeholder="E.g., synergy, coherence, truth...")
        
        if query:
            results = search_equations(query)
            
            if results:
                st.success(f"Found {len(results)} equations matching '{query}'")
                
                for category, name, eq_data in results:
                    with st.container():
                        st.markdown(f"### [{category}] {name}")
                        render_equation(eq_data)
                        st.markdown("---")
            else:
                st.warning(f"No equations found matching '{query}'")
    
    # ========================================================================
    # MODE 3: MR CALCULATOR
    # ========================================================================
    elif mode == "MR Calculator":
        st.header("🧮 Myrion Resolution Calculator")
        
        st.markdown("""
        Calculate composite MR using GILE weights:
        - **Goodness (G):** 40% weight
        - **Intuition (I):** 25% weight
        - **Love (L):** 25% weight
        - **Environment (E):** 10% weight
        """)
        
        col1, col2 = st.columns(2)
        
        with col1:
            G = st.slider("Goodness (G)", -3.0, 2.0, 0.0, 0.1)
            I = st.slider("Intuition (I)", -3.0, 2.0, 0.0, 0.1)
        
        with col2:
            L = st.slider("Love (L)", -3.0, 2.0, 0.0, 0.1)
            E = st.slider("Environment (E)", -3.0, 2.0, 0.0, 0.1)
        
        # Calculate composite MR
        MR_composite = 0.4 * G + 0.25 * I + 0.25 * L + 0.1 * E
        
        st.markdown("### Results:")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric("Composite MR", f"{MR_composite:.3f}")
        
        with col2:
            if MR_composite > 0:
                st.success("✅ Tralse-True")
            else:
                st.error("❌ Tralse-False")
        
        with col3:
            # Check for Absolute Truth
            if G >= 2.0 and I >= 2.0 and L >= 2.0 and E >= 2.0:
                st.success("⭐ ABSOLUTE TRUTH")
            elif MR_composite > 0:
                st.info("📊 Objective Truth")
            else:
                st.warning("🔄 Relative Truth (if influential)")
        
        # Detailed breakdown
        st.markdown("### Breakdown:")
        st.markdown(f"""
        - **G contribution:** 0.4 × {G:.2f} = {0.4*G:.3f}
        - **I contribution:** 0.25 × {I:.2f} = {0.25*I:.3f}
        - **L contribution:** 0.25 × {L:.2f} = {0.25*L:.3f}
        - **E contribution:** 0.1 × {E:.2f} = {0.1*E:.3f}
        - **Total:** {MR_composite:.3f}
        """)
    
    # ========================================================================
    # MODE 4: EXPORT EQUATIONS
    # ========================================================================
    elif mode == "Export Equations":
        st.header("📤 Export Equations")
        
        st.markdown("Export equations for use in papers")
        
        format_type = st.selectbox(
            "Select Format:",
            ["LaTeX", "Markdown", "JSON"]
        )
        
        category = st.selectbox(
            "Select Category (or All):",
            ["All"] + list(EQUATIONS.keys())
        )
        
        if st.button("Generate Export"):
            if category == "All":
                export_data = EQUATIONS
            else:
                export_data = {category: EQUATIONS[category]}
            
            if format_type == "LaTeX":
                output = "% Equation Repository Export\n\n"
                for cat, equations in export_data.items():
                    output += f"\\section{{{cat}}}\n\n"
                    for name, eq_data in equations.items():
                        output += f"\\subsection{{{name}}}\n"
                        output += f"$${eq_data['latex']}$$\n\n"
                        output += f"{eq_data['description']}\n\n"
            
            elif format_type == "Markdown":
                output = "# Equation Repository Export\n\n"
                for cat, equations in export_data.items():
                    output += f"## {cat}\n\n"
                    for name, eq_data in equations.items():
                        output += f"### {name}\n\n"
                        output += f"$${eq_data['latex']}$$\n\n"
                        output += f"{eq_data['description']}\n\n"
            
            else:  # JSON
                output = json.dumps(export_data, indent=2)
            
            st.code(output, language=format_type.lower())
            
            st.download_button(
                label=f"Download {format_type}",
                data=output,
                file_name=f"equations_export.{format_type.lower()}",
                mime="text/plain"
            )
    
    # ========================================================================
    # FOOTER
    # ========================================================================
    st.sidebar.markdown("---")
    st.sidebar.markdown("### 📊 Statistics")
    total_equations = sum(len(eqs) for eqs in EQUATIONS.values())
    st.sidebar.metric("Total Equations", total_equations)
    st.sidebar.metric("Categories", len(EQUATIONS))
    
    st.sidebar.markdown("---")
    st.sidebar.caption("🔗 Part of GM-Inspired Multi-App Ecosystem (33% Central)")

if __name__ == "__main__":
    main()
