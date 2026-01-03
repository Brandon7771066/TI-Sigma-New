"""
TI Proof Assistant - Sovereign Expert Mathematical Proof System
Uses Tralse Quadruplet Logic (T, F, Φ, Ψ) and TI-UOP Framework
"""

import streamlit as st
from db_utils import db
import json
from datetime import datetime

class TIProofAssistant:
    """Sovereign Expert Proof Assistant with Tralse Logic"""
    
    def __init__(self):
        self.db = db
        
        # Tralse quadruplet logic states
        self.tralse_states = {
            "T": "True (Classical truth)",
            "F": "False (Classical falsity)",
            "Φ": "Phi (Underdetermined - insufficient evidence)",
            "Ψ": "Psi (Overdetermined - contradictory evidence, Myrion resolution needed)"
        }
        
        # Proof strategies
        self.strategies = [
            "Direct Proof",
            "Proof by Contradiction",
            "Proof by Induction",
            "Construction Proof",
            "Myrion Resolution (dialectical synthesis)",
            "TI-UOP Consciousness Framework",
            "Tralse Quadruplet Analysis"
        ]
    
    def evaluate_proposition(self, proposition, evidence):
        """Evaluate proposition using Tralse logic"""
        
        # Count evidence types
        supporting = len([e for e in evidence if e['supports']])
        contradicting = len([e for e in evidence if not e['supports']])
        total = len(evidence)
        
        if total == 0:
            return "Φ", "Underdetermined - no evidence provided"
        
        if supporting > 0 and contradicting > 0:
            # Both supporting and contradicting evidence
            if abs(supporting - contradicting) < 2:
                return "Ψ", f"Overdetermined - {supporting} supporting, {contradicting} contradicting (Myrion resolution needed)"
            elif supporting > contradicting:
                return "T", f"Likely true - {supporting} supporting, {contradicting} contradicting (preponderance of evidence)"
            else:
                return "F", f"Likely false - {supporting} supporting, {contradicting} contradicting (preponderance of evidence)"
        elif supporting > 0:
            return "T", f"True - {supporting} supporting evidence, no contradictions"
        else:
            return "F", f"False - {contradicting} contradicting evidence, no support"
    
    def generate_latex_proof(self, theorem, strategy, steps):
        """Generate LaTeX-formatted proof"""
        
        latex = f"""
\\documentclass{{article}}
\\usepackage{{amsmath}}
\\usepackage{{amsthm}}
\\usepackage{{amssymb}}

\\newtheorem{{theorem}}{{Theorem}}
\\newtheorem{{lemma}}{{Lemma}}

\\begin{{document}}

\\section*{{Proof of: {theorem}}}

\\textbf{{Strategy:}} {strategy}

\\begin{{proof}}
"""
        
        for i, step in enumerate(steps, 1):
            latex += f"\n\\textbf{{Step {i}:}} {step}\n\n"
        
        latex += """
\\end{proof}

\\end{document}
"""
        return latex
    
    def save_proof(self, theorem, strategy, steps, tralse_state, notes):
        """Save proof to database"""
        
        proof_data = {
            "theorem": theorem,
            "strategy": strategy,
            "steps": steps,
            "tralse_state": tralse_state,
            "notes": notes,
            "timestamp": datetime.now().isoformat()
        }
        
        asset_id = self.db.add_asset(
            asset_type="ti_proof",
            source_app="TI Proof Assistant",
            title=theorem,
            content=proof_data,
            tags=["proof", "tralse_logic", "mathematics"]
        )
        
        return asset_id


def render_ti_proof_assistant():
    """Render TI Proof Assistant dashboard"""
    
    st.title("🎓 TI Proof Assistant")
    st.markdown("**Sovereign Expert Approach to Mathematical Proofs**")
    st.markdown("---")
    
    # Initialize
    if 'proof_assistant' not in st.session_state:
        st.session_state.proof_assistant = TIProofAssistant()
    
    assistant = st.session_state.proof_assistant
    
    # Tab navigation
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📝 New Proof",
        "🔍 Tralse Evaluator",
        "📚 Proof Library",
        "📄 LaTeX Export",
        "🏆 Millennium Problems"
    ])
    
    # =========================================================================
    # TAB 1: NEW PROOF
    # =========================================================================
    with tab1:
        st.subheader("📝 Create New Proof")
        
        theorem = st.text_area(
            "Theorem Statement:",
            placeholder="e.g., For all integers n ≥ 1, the sum 1 + 2 + ... + n = n(n+1)/2",
            height=100
        )
        
        strategy = st.selectbox("Proof Strategy:", assistant.strategies)
        
        st.markdown("**Proof Steps:**")
        
        # Dynamic step input
        if 'proof_steps' not in st.session_state:
            st.session_state.proof_steps = [""]
        
        for i, step in enumerate(st.session_state.proof_steps):
            col1, col2 = st.columns([9, 1])
            with col1:
                st.session_state.proof_steps[i] = st.text_area(
                    f"Step {i+1}:",
                    value=step,
                    height=80,
                    key=f"step_{i}"
                )
            with col2:
                if st.button("❌", key=f"del_{i}"):
                    st.session_state.proof_steps.pop(i)
                    st.rerun()
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("➕ Add Step"):
                st.session_state.proof_steps.append("")
                st.rerun()
        
        with col2:
            if st.button("🔄 Clear All"):
                st.session_state.proof_steps = [""]
                st.rerun()
        
        notes = st.text_area("Notes / Comments:", height=100)
        
        st.markdown("---")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            if st.button("💾 Save Proof", use_container_width=True):
                if theorem and st.session_state.proof_steps:
                    asset_id = assistant.save_proof(
                        theorem=theorem,
                        strategy=strategy,
                        steps=st.session_state.proof_steps,
                        tralse_state="T",  # Assumed true if proof constructed
                        notes=notes
                    )
                    st.success(f"✅ Proof saved! Asset ID: {asset_id}")
                else:
                    st.error("❌ Please enter theorem and at least one step")
        
        with col2:
            if st.button("📄 Generate LaTeX", use_container_width=True):
                if theorem and st.session_state.proof_steps:
                    latex = assistant.generate_latex_proof(theorem, strategy, st.session_state.proof_steps)
                    st.code(latex, language="latex")
                    st.download_button(
                        "⬇️ Download LaTeX",
                        latex,
                        file_name="proof.tex",
                        mime="text/plain"
                    )
                else:
                    st.error("❌ Please enter theorem and steps first")
        
        with col3:
            if st.button("🔍 Evaluate", use_container_width=True):
                if theorem:
                    st.info("💡 Tralse evaluation: Use 'Tralse Evaluator' tab to assess evidence")
                else:
                    st.error("❌ Please enter theorem first")
    
    # =========================================================================
    # TAB 2: TRALSE EVALUATOR
    # =========================================================================
    with tab2:
        st.subheader("🔍 Tralse Quadruplet Logic Evaluator")
        
        st.markdown("""
        **Tralse States:**
        - **T (True):** Classical truth - sufficient supporting evidence
        - **F (False):** Classical falsity - sufficient contradicting evidence
        - **Φ (Phi):** Underdetermined - insufficient evidence either way
        - **Ψ (Psi):** Overdetermined - contradictory evidence (Myrion resolution needed)
        """)
        
        proposition = st.text_area("Proposition to Evaluate:", height=100)
        
        st.markdown("**Evidence Collection:**")
        
        if 'evidence' not in st.session_state:
            st.session_state.evidence = []
        
        col1, col2 = st.columns([3, 1])
        with col1:
            evidence_text = st.text_input("Evidence Statement:", key="new_evidence")
        with col2:
            supports = st.checkbox("Supports?", value=True, key="new_supports")
        
        if st.button("➕ Add Evidence"):
            if evidence_text:
                st.session_state.evidence.append({
                    "text": evidence_text,
                    "supports": supports
                })
                st.rerun()
        
        # Display evidence
        if st.session_state.evidence:
            st.markdown("**Current Evidence:**")
            for i, e in enumerate(st.session_state.evidence):
                icon = "✅" if e['supports'] else "❌"
                col1, col2 = st.columns([9, 1])
                with col1:
                    st.markdown(f"{icon} {e['text']}")
                with col2:
                    if st.button("🗑️", key=f"del_ev_{i}"):
                        st.session_state.evidence.pop(i)
                        st.rerun()
        
        st.markdown("---")
        
        if st.button("🔍 Evaluate Proposition", use_container_width=True):
            if proposition and st.session_state.evidence:
                state, reasoning = assistant.evaluate_proposition(proposition, st.session_state.evidence)
                
                # Display result
                st.markdown("### Evaluation Result:")
                
                if state == "T":
                    st.success(f"**State: T (True)**\n\n{reasoning}")
                elif state == "F":
                    st.error(f"**State: F (False)**\n\n{reasoning}")
                elif state == "Φ":
                    st.info(f"**State: Φ (Underdetermined)**\n\n{reasoning}")
                else:  # Ψ
                    st.warning(f"**State: Ψ (Overdetermined)**\n\n{reasoning}")
                    st.markdown("**💡 Myrion Resolution Required:**")
                    st.markdown("""
                    - Identify thesis and antithesis
                    - Find higher-level synthesis
                    - Resolve contradiction through dialectical integration
                    """)
            else:
                st.error("❌ Please enter proposition and evidence")
        
        if st.button("🔄 Clear Evidence"):
            st.session_state.evidence = []
            st.rerun()
    
    # =========================================================================
    # TAB 3: PROOF LIBRARY
    # =========================================================================
    with tab3:
        st.subheader("📚 Saved Proofs")
        
        # Get all saved proofs
        proofs = assistant.db.get_assets_by_type("ti_proof")
        
        if not proofs:
            st.info("📭 No saved proofs yet. Create one in the 'New Proof' tab!")
        else:
            st.caption(f"{len(proofs)} saved proof(s)")
            
            for proof in proofs:
                with st.expander(f"📄 {proof['title']}"):
                    content = proof['content']
                    
                    st.markdown(f"**Strategy:** {content['strategy']}")
                    st.markdown(f"**Tralse State:** {content['tralse_state']}")
                    st.markdown(f"**Date:** {content['timestamp'][:10]}")
                    
                    st.markdown("**Steps:**")
                    for i, step in enumerate(content['steps'], 1):
                        st.markdown(f"{i}. {step}")
                    
                    if content.get('notes'):
                        st.markdown(f"**Notes:** {content['notes']}")
                    
                    latex = assistant.generate_latex_proof(
                        content['theorem'],
                        content['strategy'],
                        content['steps']
                    )
                    st.download_button(
                        "📄 Download LaTeX",
                        latex,
                        file_name=f"proof_{proof['asset_id']}.tex",
                        mime="text/plain",
                        key=f"latex_{proof['asset_id']}",
                        use_container_width=True
                    )
    
    # =========================================================================
    # TAB 4: LATEX EXPORT
    # =========================================================================
    with tab4:
        st.subheader("📄 LaTeX Proof Export")
        st.caption("Generate publication-ready LaTeX proofs")
        
        # Get all saved proofs
        all_proofs = assistant.db.get_assets_by_type("ti_proof")
        
        if not all_proofs:
            st.info("📭 No saved proofs yet. Create one in the 'New Proof' tab!")
        else:
            st.markdown(f"**{len(all_proofs)} proof(s) available for export**")
            
            # Select proof to export
            proof_options = {f"{proof['title']} (ID: {proof['asset_id']})": proof for proof in all_proofs}
            selected_label = st.selectbox("Select Proof:", list(proof_options.keys()))
            
            if selected_label:
                selected_proof = proof_options[selected_label]
                content = selected_proof['content']
                
                st.markdown("---")
                st.markdown("**Preview:**")
                st.markdown(f"**Theorem:** {content['theorem']}")
                st.markdown(f"**Strategy:** {content['strategy']}")
                st.markdown(f"**Steps:** {len(content['steps'])}")
                
                # Generate LaTeX
                latex = assistant.generate_latex_proof(
                    content['theorem'],
                    content['strategy'],
                    content['steps']
                )
                
                col1, col2 = st.columns(2)
                with col1:
                    st.download_button(
                        "📥 Download LaTeX (.tex)",
                        latex,
                        file_name=f"proof_{selected_proof['asset_id']}.tex",
                        mime="text/plain",
                        use_container_width=True
                    )
                with col2:
                    if st.button("📋 Copy to Clipboard", use_container_width=True):
                        st.code(latex, language="latex")
                        st.success("✅ LaTeX code displayed above - copy manually")
                
                # Show LaTeX preview
                with st.expander("👁️ View LaTeX Source"):
                    st.code(latex, language="latex")
    
    # =========================================================================
    # TAB 5: MILLENNIUM PROBLEMS
    # =========================================================================
    with tab5:
        st.subheader("🏆 Millennium Prize Problems")
        st.caption("$1M per problem - TI-UOP approaches")
        
        problems = [
            {
                "name": "P vs NP",
                "description": "Can every problem whose solution can be quickly verified also be quickly solved?",
                "ti_approach": "Use TI-UOP to show consciousness introduces non-computational elements in verification vs. solving",
                "tralse_state": "Ψ"
            },
            {
                "name": "Riemann Hypothesis",
                "description": "All non-trivial zeros of ζ(s) have real part 1/2",
                "ti_approach": "Connect to CCC resonance field - zeros represent consciousness observation points",
                "tralse_state": "Φ"
            },
            {
                "name": "Navier-Stokes Existence",
                "description": "Do smooth solutions always exist for fluid dynamics equations?",
                "ti_approach": "Consciousness creates smooth field - solutions exist where CCC coherence ≥ 0.91",
                "tralse_state": "Φ"
            },
            {
                "name": "Yang-Mills Mass Gap",
                "description": "Prove quantum Yang-Mills theory has positive mass gap",
                "ti_approach": "Mass gap = consciousness intervention threshold in quantum field",
                "tralse_state": "Φ"
            },
            {
                "name": "Birch and Swinnerton-Dyer",
                "description": "Elliptic curve L-functions and rational points",
                "ti_approach": "Rational points = CCC access points in number field",
                "tralse_state": "Φ"
            },
            {
                "name": "Hodge Conjecture",
                "description": "Algebraic cycles on algebraic varieties",
                "ti_approach": "Algebraic cycles represent consciousness observation patterns",
                "tralse_state": "Φ"
            }
        ]
        
        for problem in problems:
            with st.expander(f"🔬 {problem['name']} - State: {problem['tralse_state']}"):
                st.markdown(f"**Classical Description:**\n{problem['description']}")
                st.markdown(f"**TI-UOP Approach:**\n{problem['ti_approach']}")
                st.markdown(f"**Current Tralse State:** {problem['tralse_state']} ({assistant.tralse_states[problem['tralse_state']]})")
                
                if st.button(f"🚀 Start Proof Attempt", key=f"start_{problem['name']}"):
                    st.info(f"💡 Navigate to 'New Proof' tab and use strategy: '{assistant.strategies[5]}' (TI-UOP Framework)")
        
        # About section at bottom
        st.markdown("---")
        with st.expander("ℹ️ About TI Proof Assistant"):
            st.markdown("""
            **Sovereign Expert Approach** | **Tralse Quadruplet Logic (T, F, Φ, Ψ)** | **TI-UOP Framework**
            
            Mathematics isn't discovered - it's **created by consciousness**. CCC generates truth through observer participation.
            
            **Usage:** Create Proof → Evaluate with Tralse → Export LaTeX → Tackle Millennium Problems ($6M prizes)
            """)


if __name__ == "__main__":
    render_ti_proof_assistant()
