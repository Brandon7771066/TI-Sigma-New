"""
Autonomous LCC Study - Dedicated Page
"""
import streamlit as st

st.set_page_config(
    page_title="Autonomous LCC Study",
    page_icon="🔬",
    layout="wide"
)

st.title("🔬 Autonomous LCC Study")
st.markdown("*Neural-Behavior Correlation Analysis with Real Neuroscience Data*")

from experiments.autonomous_lcc_dashboard import render_autonomous_lcc_dashboard
render_autonomous_lcc_dashboard()
