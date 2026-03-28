"""
ARC-AGI TI Sigma Tab — Streamlit UI
"""

import streamlit as st
import json
import numpy as np
from pathlib import Path


ARC_COLORS = {
    0: "#000000", 1: "#0074D9", 2: "#FF4136", 3: "#2ECC40",
    4: "#FFDC00", 5: "#AAAAAA", 6: "#F012BE", 7: "#FF851B",
    8: "#7FDBFF", 9: "#870C25",
}


def render_grid(grid: list, cell_size: int = 24) -> str:
    """Render ARC grid as HTML table."""
    rows = len(grid)
    cols = len(grid[0]) if grid else 0
    cells = ""
    for row in grid:
        cells += "<tr>"
        for color in row:
            bg = ARC_COLORS.get(color, "#000000")
            cells += f'<td style="width:{cell_size}px;height:{cell_size}px;background:{bg};border:1px solid #333;"></td>'
        cells += "</tr>"
    return f'<table style="border-collapse:collapse;display:inline-block">{cells}</table>'


def show_arc_tab():
    st.header("ARC-AGI TI Sigma Solver")
    st.caption("5-valued logic approach to abstract reasoning — URB #528: Five-Valued Truth + Myrion Resolution")

    col1, col2 = st.columns([2, 1])

    with col2:
        st.subheader("5-Valued Truth")
        st.markdown("""
        **Three positional (ternary) slots:**
        - `TRUE` — definitively figure
        - `FALSE` — definitively background
        - `INDETERMINATE` — coherent 50/50 middle;
          held open until context resolves it

        **Two quality designations:**
        - `TRALSE` — imperfection quality; the "grease
          that makes the gears run"; embedded in all
          three positional states; MR processes these
        - `DOUBLE TRALSE` — incoherent contradiction;
          **immediately flagged + discarded**; no storage

        **Key distinction:**
        Indeterminate = *coherent* irreconcilability
        Double Tralse = *incoherent* irreconcilability

        **MR Gate Hierarchy:**
        - MR1: Discards Double Tralse (LCC < 0.8647)
        - MR2: Holds INDETERMINATE (LCC 0.8647-0.9323)
        - MR Radiant: Full causal weight (LCC ≥ 0.9323)
        """)

    with col1:
        tab1, tab2, tab3 = st.tabs(["Solve Single Task", "Batch Benchmark", "Dataset"])

        with tab1:
            st.subheader("Solve a Task")
            uploaded = st.file_uploader(
                "Upload a task JSON file", type=["json"],
                help="Download from: github.com/fchollet/ARC-AGI"
            )

            if uploaded:
                task = json.load(uploaded)
                task_id = uploaded.name.replace(".json", "")

                st.write(f"**Train pairs:** {len(task.get('train', []))} | **Test:** {len(task.get('test', []))}")

                train_pairs = task.get("train", [])
                if train_pairs:
                    st.write("**Training examples:**")
                    cols = st.columns(min(len(train_pairs), 4))
                    for i, pair in enumerate(train_pairs[:4]):
                        with cols[i]:
                            st.caption(f"Example {i+1} — Input")
                            st.markdown(render_grid(pair["input"]), unsafe_allow_html=True)
                            st.caption(f"Example {i+1} — Output")
                            st.markdown(render_grid(pair["output"]), unsafe_allow_html=True)

                if st.button("Solve with TI Sigma", type="primary"):
                    with st.spinner("Running Myrion Resolution..."):
                        try:
                            from arc_ti_solver.solver import TISigmaARCSolver
                            solver = TISigmaARCSolver(task, task_id=task_id)
                            result = solver.solve(verbose=False)

                            st.success("Solution found!")

                            st.subheader("Predictions")
                            for i, pred in enumerate(result["predictions"]):
                                st.write(f"**Test {i+1}**")
                                test_input = task["test"][i]["input"]
                                st.caption("Test Input:")
                                st.markdown(render_grid(test_input), unsafe_allow_html=True)

                                if pred["solutions"]:
                                    best = pred["solutions"][0]
                                    lcc = best["lcc"]
                                    regime = "True-Tralse" if lcc >= 0.85 else "Crossover" if lcc >= 0.7823 else "Coherent"
                                    st.caption(f"Best Prediction (LCC={lcc:.4f} — {regime}):")
                                    st.markdown(render_grid(best["output"]), unsafe_allow_html=True)
                                    st.caption(f"Transform: `{best['transform']}`")

                            with st.expander("Full LCC Report"):
                                st.code(result["report"])

                            with st.expander("Color Roles (Tralse Analysis)"):
                                from arc_ti_solver import TVALUES
                                for color, tval in result["color_roles"].items():
                                    st.write(f"Color {color} → `{TVALUES[tval]}`")

                        except Exception as e:
                            st.error(f"Solver error: {e}")
                            import traceback
                            st.code(traceback.format_exc())

        with tab2:
            st.subheader("Batch Benchmark")
            st.info("Download the ARC dataset first, then run the batch solver.")

            col_a, col_b = st.columns(2)
            with col_a:
                if st.button("Download ARC Dataset (from GitHub)"):
                    with st.spinner("Downloading ~1000 tasks..."):
                        from arc_ti_solver.data_loader import download_arc_dataset
                        d1 = download_arc_dataset("training")
                        d2 = download_arc_dataset("evaluation")
                        n1 = len(list(d1.glob("*.json")))
                        n2 = len(list(d2.glob("*.json")))
                        st.success(f"Downloaded: {n1} training + {n2} evaluation tasks")

            with col_b:
                limit = st.number_input("Tasks to solve", min_value=1, max_value=400, value=20)

            if st.button("Run Benchmark", type="primary"):
                with st.spinner(f"Solving {limit} tasks..."):
                    try:
                        from arc_ti_solver.batch_runner import solve_all, benchmark_report
                        results = solve_all(split="training", limit=limit, max_workers=2)
                        report = benchmark_report(results)
                        st.code(report)

                        lcc_scores = []
                        for r in results.values():
                            for pred in r.get("predictions", []):
                                if pred.get("best"):
                                    lcc_scores.append(pred["best"]["lcc"])

                        if lcc_scores:
                            import pandas as pd
                            df = pd.DataFrame({"LCC": lcc_scores})
                            st.bar_chart(df["LCC"].value_counts(bins=10).sort_index())
                    except Exception as e:
                        st.error(f"Benchmark error: {e}")

        with tab3:
            st.subheader("Dataset Status")
            data_dir = Path("arc_ti_solver/data")
            for split in ["training", "evaluation"]:
                split_dir = data_dir / split
                if split_dir.exists():
                    n = len(list(split_dir.glob("*.json")))
                    st.write(f"**{split}:** {n} tasks downloaded")
                else:
                    st.write(f"**{split}:** not downloaded yet")

            st.divider()
            st.subheader("Competition Links")
            st.markdown("""
            - [ARC Prize 2024 (Kaggle)](https://www.kaggle.com/competitions/arc-prize-2024)
            - [ARC-AGI GitHub](https://github.com/fchollet/ARC-AGI)
            - [Leaderboard](https://arcprize.org/leaderboard)
            """)
