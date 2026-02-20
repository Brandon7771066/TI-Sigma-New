"""
RNA 3D Folding Dashboard
===========================
Streamlit dashboard for the Stanford RNA 3D Folding Part 2 Kaggle Competition.
RNA sequence analysis, 3D structure prediction, GILE structural analysis,
and Tralse confidence scoring.
"""

import streamlit as st
import pandas as pd
import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.rna_3d_folding_engine import RNA3DFoldingEngine, COMMON_RNA_MOTIFS


def get_engine():
    if 'rna_engine' not in st.session_state:
        st.session_state['rna_engine'] = RNA3DFoldingEngine(seed=42)
    return st.session_state['rna_engine']


def display_gile_scores(gile_dict):
    cols = st.columns(4)
    color_map = {'G': '🟢', 'I': '🔵', 'L': '🩷', 'E': '🟠'}
    label_map = {'G': 'Goodness/Stability', 'I': 'Information', 'L': 'Function', 'E': 'Physical Validity'}
    for idx, dim in enumerate(['G', 'I', 'L', 'E']):
        with cols[idx]:
            val = gile_dict.get(dim, 0)
            st.metric(f"{color_map[dim]} {dim} ({label_map[dim]})", f"{val:.4f}")


def render_rna_folding_dashboard():
    st.title("🧬 RNA 3D Folding Prediction")
    st.markdown("*Stanford RNA 3D Folding Part 2 — GILE Structural Analysis & Tralse Confidence*")

    tabs = st.tabs([
        "Sequence Analysis",
        "3D Structure Prediction",
        "Sample RNA Library",
        "Competition Strategy",
        "Fractal Analysis",
    ])

    with tabs[0]:
        render_sequence_analysis()
    with tabs[1]:
        render_3d_prediction()
    with tabs[2]:
        render_sample_library()
    with tabs[3]:
        render_competition_strategy()
    with tabs[4]:
        render_fractal_analysis()


def render_sequence_analysis():
    st.header("RNA Sequence Analysis")

    sequence = st.text_input(
        "Enter RNA Sequence",
        value="GCGCAAGCGC",
        help="Use A, C, G, U (or T) characters",
        key="rna_seq_input",
    )

    if st.button("Analyze Sequence", type="primary", key="btn_analyze_seq"):
        try:
            engine = get_engine()
            seq = sequence.upper().replace('T', 'U').strip()

            if not seq or not all(c in 'ACGU' for c in seq):
                st.error("Invalid sequence. Use only A, C, G, U characters.")
                return

            if len(seq) < 4:
                st.error("Sequence must be at least 4 nucleotides long.")
                return

            features = engine.analyze_sequence_features(seq)
            ss = engine.compute_secondary_structure(seq)

            st.session_state['rna_current_seq'] = seq
            st.session_state['rna_features'] = features
            st.session_state['rna_ss'] = ss

            st.markdown("---")
            st.subheader("Sequence Features")

            m1, m2, m3, m4 = st.columns(4)
            with m1:
                st.metric("Length", features['length'])
            with m2:
                st.metric("GC Content", f"{features['gc_content']:.1%}")
            with m3:
                st.metric("Base Pairs", features['num_base_pairs'])
            with m4:
                st.metric("Complexity", f"{features['sequence_complexity']:.3f}")

            st.subheader("Base Composition")
            comp = features['base_composition']
            comp_df = pd.DataFrame({
                'Base': list(comp.keys()),
                'Count': list(comp.values()),
            })
            st.bar_chart(comp_df.set_index('Base'))

            st.subheader("Secondary Structure")
            st.code(f"Sequence:  {seq}\nStructure: {ss['bracket_notation']}", language="text")

            s1, s2, s3 = st.columns(3)
            with s1:
                st.metric("Base Pairs", ss['num_pairs'])
            with s2:
                st.metric("Free Energy", f"{ss['free_energy_estimate']:.1f} kcal/mol")
            with s3:
                st.metric("Pair Ratio", f"{ss['pair_ratio']:.2f}")

            if ss['pairs']:
                with st.expander("Base Pair Details"):
                    pair_data = []
                    for i, j in ss['pairs']:
                        pair_data.append({
                            'Position i': i,
                            'Base i': seq[i],
                            'Position j': j,
                            'Base j': seq[j],
                            'Pair': f"{seq[i]}-{seq[j]}",
                        })
                    st.dataframe(pd.DataFrame(pair_data), use_container_width=True, hide_index=True)

            with st.expander("Additional Features"):
                a1, a2 = st.columns(2)
                with a1:
                    st.metric("Stem-Loops", features.get('stem_loops_detected', 0))
                    st.metric("Pseudoknot Potential", f"{features.get('pseudoknot_potential', 0):.0f}")
                with a2:
                    st.metric("Purine-Rich Regions", features.get('purine_rich_regions', 0))
                    st.metric("Max Purine Run", features.get('max_purine_run', 0))

                if features.get('dinucleotide_frequencies'):
                    st.markdown("**Dinucleotide Frequencies:**")
                    di_df = pd.DataFrame({
                        'Dinucleotide': list(features['dinucleotide_frequencies'].keys()),
                        'Count': list(features['dinucleotide_frequencies'].values()),
                    })
                    st.dataframe(di_df, use_container_width=True, hide_index=True)

        except Exception as e:
            st.error(f"Analysis error: {str(e)}")


def render_3d_prediction():
    st.header("3D Structure Prediction")

    seq = st.session_state.get('rna_current_seq', 'GCGCAAGCGC')
    st.markdown(f"**Current sequence:** `{seq}` ({len(seq)} nt)")

    n_preds = st.slider("Number of predictions", 1, 10, 5, key="rna_n_preds")

    if st.button("Generate 3D Predictions", type="primary", key="btn_3d_pred"):
        try:
            engine = get_engine()

            with st.spinner(f"Generating {n_preds} 3D structure predictions..."):
                coords_list = engine.generate_3d_coordinates(seq, n_predictions=n_preds)

            reference = coords_list[0]
            tm_scores = []
            rmsd_scores = []
            for i, coords in enumerate(coords_list):
                tm = engine.compute_tm_score(coords, reference)
                rmsd = engine.compute_rmsd(coords, reference)
                tm_scores.append(tm)
                rmsd_scores.append(rmsd)

            tralse_results = engine.apply_tralse_confidence(coords_list, tm_scores)

            gile_results = []
            for coords in coords_list:
                gile = engine.gile_structural_analysis(seq, coords)
                gile_results.append(gile)

            st.session_state['rna_predictions'] = {
                'coords': coords_list,
                'tm_scores': tm_scores,
                'rmsd_scores': rmsd_scores,
                'tralse': tralse_results,
                'gile': gile_results,
            }

            st.markdown("---")
            st.subheader("Prediction Results")

            results_rows = []
            for i in range(len(coords_list)):
                tralse = tralse_results[i] if i < len(tralse_results) else {}
                gile = gile_results[i] if i < len(gile_results) else {}
                results_rows.append({
                    'Prediction': i + 1,
                    'TM-score': round(tm_scores[i], 4),
                    'RMSD (Å)': round(rmsd_scores[i], 2),
                    'Confidence': tralse.get('confidence', 0),
                    'Classification': tralse.get('classification', 'unknown'),
                    'GILE Composite': gile.get('gile_composite', 0),
                })
            st.dataframe(pd.DataFrame(results_rows), use_container_width=True, hide_index=True)

            best_idx = max(range(len(tm_scores)), key=lambda i: tm_scores[i])
            st.success(f"🏆 Best prediction: #{best_idx + 1} (TM-score: {tm_scores[best_idx]:.4f})")

            st.markdown("---")
            st.subheader(f"GILE Analysis — Prediction #{best_idx + 1}")
            best_gile = gile_results[best_idx]
            display_gile_scores(best_gile)

            gc1, gc2 = st.columns(2)
            with gc1:
                st.metric("GILE Composite", f"{best_gile['gile_composite']:.4f}")
            with gc2:
                conf_label = "High" if best_gile['tralse_true'] > 0.7 else "Moderate" if best_gile['tralse_true'] > 0.4 else "Low"
                st.metric("Tralse True", f"{best_gile['tralse_true']:.4f} ({conf_label})")

            for i, tralse in enumerate(tralse_results):
                with st.expander(f"Prediction #{i+1} — Tralse Details"):
                    t1, t2, t3 = st.columns(3)
                    with t1:
                        st.metric("Backbone Consistency", f"{tralse.get('backbone_consistency', 0):.4f}")
                    with t2:
                        st.metric("Steric Validity", f"{tralse.get('steric_validity', 0):.4f}")
                    with t3:
                        cls = tralse.get('classification', 'unknown')
                        icon = '✅' if cls == 'high_confidence' else '⚠️' if cls == 'moderate_confidence' else '❌'
                        st.metric("Classification", f"{icon} {cls.replace('_', ' ').title()}")

            st.markdown("---")
            st.subheader("Distance Matrix (Reference)")
            with st.expander("View Distance Matrix"):
                dist_matrix = engine.predict_distance_matrix(seq)
                n = len(seq)
                display_n = min(n, 20)
                labels = [f"{seq[i]}{i}" for i in range(display_n)]
                dist_df = pd.DataFrame(
                    np.round(dist_matrix[:display_n, :display_n], 1),
                    columns=labels, index=labels,
                )
                st.dataframe(dist_df, use_container_width=True)
                st.caption("Values represent predicted inter-residue distances in Ångströms.")

        except Exception as e:
            st.error(f"3D prediction error: {str(e)}")

    preds = st.session_state.get('rna_predictions')
    if preds and not st.session_state.get('_3d_just_ran'):
        st.markdown("---")
        st.info("Previous predictions loaded. Click 'Generate 3D Predictions' to rerun.")


def render_sample_library():
    st.header("Sample RNA Library")
    st.markdown("Pre-loaded RNA sequences with known structural motifs.")

    engine = get_engine()

    try:
        if 'rna_samples' not in st.session_state:
            st.session_state['rna_samples'] = engine.generate_sample_rna_data(n_sequences=15)

        samples = st.session_state['rna_samples']

        sample_df = pd.DataFrame([{
            'ID': s['id'],
            'Sequence': s['sequence'],
            'Length': s['length'],
            'Motif': s['motif_type'],
            'GC Content': f"{s['gc_content']:.1%}",
            'Base Pairs': s['num_pairs'],
            'Free Energy': f"{s['free_energy']:.1f}",
        } for s in samples])
        st.dataframe(sample_df, use_container_width=True, hide_index=True)

        selected_id = st.selectbox(
            "Select a sample to analyze",
            [s['id'] for s in samples],
            format_func=lambda x: f"{x} — {next(s['sequence'] for s in samples if s['id'] == x)} ({next(s['motif_type'] for s in samples if s['id'] == x)})",
            key="rna_sample_select",
        )

        if st.button("Analyze Selected Sample", type="primary", key="btn_sample_analyze"):
            sample = next(s for s in samples if s['id'] == selected_id)
            seq = sample['sequence']

            st.session_state['rna_current_seq'] = seq
            features = engine.analyze_sequence_features(seq)
            ss = engine.compute_secondary_structure(seq)

            st.markdown("---")
            st.subheader(f"Analysis: {selected_id} ({sample['motif_type']})")

            m1, m2, m3, m4 = st.columns(4)
            with m1:
                st.metric("Length", features['length'])
            with m2:
                st.metric("GC Content", f"{features['gc_content']:.1%}")
            with m3:
                st.metric("Base Pairs", features['num_base_pairs'])
            with m4:
                st.metric("Free Energy", f"{ss['free_energy_estimate']:.1f}")

            st.code(f"Sequence:  {seq}\nStructure: {ss['bracket_notation']}", language="text")

            coords_list = engine.generate_3d_coordinates(seq, n_predictions=3)
            gile = engine.gile_structural_analysis(seq, coords_list[0])

            st.subheader("GILE Structural Analysis")
            display_gile_scores(gile)

            g1, g2 = st.columns(2)
            with g1:
                st.metric("GILE Composite", f"{gile['gile_composite']:.4f}")
            with g2:
                st.metric("Fractal Dimension", f"{gile['fractal_dimension']:.4f}")

            st.info(f"💡 This sequence is now loaded. Switch to 'Sequence Analysis' or '3D Structure Prediction' tabs to explore further.")

    except Exception as e:
        st.error(f"Sample library error: {str(e)}")


def render_competition_strategy():
    st.header("Stanford RNA 3D Folding Part 2")

    c1, c2, c3 = st.columns(3)
    with c1:
        st.metric("Deadline", "March 25, 2026")
    with c2:
        st.metric("Prize Pool", "$75,000")
    with c3:
        st.metric("Metric", "TM-score")

    st.markdown("---")
    st.subheader("Competition Overview")
    st.markdown("""
    Predict 3D atomic coordinates of RNA molecules from sequence alone.
    Evaluated using TM-score comparing predicted vs experimental structures.

    **Challenge:** RNA molecules fold into complex 3D structures that determine
    their biological function. Unlike proteins, RNA structure prediction remains
    largely unsolved, making this a frontier problem in computational biology.
    """)

    st.subheader("Our Approach")
    with st.expander("1. Secondary Structure Prediction"):
        st.markdown("""
        - **Nussinov algorithm** for optimal base pair prediction
        - Energy-weighted pairing with canonical (G-C, A-U) and wobble (G-U) pairs
        - Minimum loop length constraints for biological validity
        - Bracket notation output for standard structure representation
        """)
    with st.expander("2. Physics-Based 3D Coordinate Generation"):
        st.markdown("""
        - Backbone trajectory with A-form helix parameters
        - Base pair distance constraints (8.0 Å)
        - Backbone step constraints (3.4 Å)
        - Iterative energy minimization with spring forces
        - Steric clash avoidance via repulsion terms
        """)
    with st.expander("3. GILE Structural Analysis"):
        st.markdown("""
        - **G (Goodness/Stability):** Thermodynamic stability from base pairing and stacking
        - **I (Information):** Sequence complexity and structural information content
        - **L (Love/Function):** Functional potential from catalytic motifs and binding sites
        - **E (Existence/Physical):** Physical validity of 3D coordinates (bond lengths, steric)
        """)
    with st.expander("4. Tralse Confidence Scoring"):
        st.markdown("""
        - Backbone consistency measurement
        - Steric validity assessment
        - TM-score normalization
        - Three-tier confidence: high / moderate / low
        """)
    with st.expander("5. Submission Strategy"):
        st.markdown("""
        - Multiple predictions per sequence (ensemble approach)
        - Best prediction selection by TM-score
        - GILE-weighted confidence for quality ranking
        - Fractal dimension analysis for structural motif detection
        """)

    st.markdown("---")
    st.markdown("🔗 [Kaggle Competition Page](https://www.kaggle.com/competitions/stanford-rna-3d-folding-part-2)")


def render_fractal_analysis():
    st.header("Fractal Analysis")
    st.markdown("Fractal dimension of RNA folding patterns and connection to the TI fractal universe.")

    engine = get_engine()
    seq = st.session_state.get('rna_current_seq', 'GCGCAAGCGC')
    st.markdown(f"**Current sequence:** `{seq}`")

    if st.button("Run Fractal Analysis", type="primary", key="btn_fractal"):
        try:
            with st.spinner("Computing fractal dimensions..."):
                coords_list = engine.generate_3d_coordinates(seq, n_predictions=5)

                fractal_results = []
                for i, coords in enumerate(coords_list):
                    gile = engine.gile_structural_analysis(seq, coords)
                    fractal_dim = gile.get('fractal_dimension', 0)
                    fractal_results.append({
                        'Prediction': i + 1,
                        'Fractal Dimension': round(fractal_dim, 4),
                        'GILE Composite': gile['gile_composite'],
                        'G (Stability)': gile['G'],
                        'I (Information)': gile['I'],
                        'L (Function)': gile['L'],
                        'E (Physical)': gile['E'],
                    })

            st.session_state['rna_fractal_results'] = fractal_results

        except Exception as e:
            st.error(f"Fractal analysis error: {str(e)}")

    fractal_results = st.session_state.get('rna_fractal_results')
    if fractal_results:
        st.markdown("---")
        st.subheader("Fractal Dimensions Across Predictions")
        st.dataframe(pd.DataFrame(fractal_results), use_container_width=True, hide_index=True)

        dims = [r['Fractal Dimension'] for r in fractal_results]
        f1, f2, f3 = st.columns(3)
        with f1:
            st.metric("Mean Fractal Dim", f"{np.mean(dims):.4f}")
        with f2:
            st.metric("Std Fractal Dim", f"{np.std(dims):.4f}")
        with f3:
            st.metric("Range", f"{max(dims) - min(dims):.4f}")

        st.markdown("---")
        st.subheader("TI Fractal Universe Connection")
        st.markdown("""
        In the TI framework, fractal patterns appear at every scale of existence:

        - **Molecular Level:** RNA folding exhibits self-similar patterns. Stem-loops
          nest within larger structures, creating fractal-like hierarchies.
        - **Fractal Dimension Range:**
          - **< 1.2:** Linear/simple structures (low complexity)
          - **1.2 - 1.5:** Moderate folding (typical functional RNA)
          - **1.5 - 1.8:** Complex tertiary structures (ribozymes, riboswitches)
          - **> 1.8:** Highly compact structures (ribosomal RNA)
        - **GILE Connection:** The fractal dimension correlates with the
          I (Information) dimension — more complex folding encodes more
          structural information, reflecting the TI principle that
          existence amplifies through self-referential complexity.
        """)

        chart_df = pd.DataFrame({
            'Prediction': [r['Prediction'] for r in fractal_results],
            'Fractal Dimension': [r['Fractal Dimension'] for r in fractal_results],
            'GILE Composite': [r['GILE Composite'] for r in fractal_results],
        }).set_index('Prediction')
        st.line_chart(chart_df)

    else:
        st.info("Click 'Run Fractal Analysis' to compute fractal dimensions for the current sequence.")
