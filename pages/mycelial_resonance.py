"""
🍄 Mycelial Resonance — Live Closed-Loop Biofeedback (sidebar page)

Embeds the live closed-loop UI served from the ti_website gateway at /mycelial,
so this single page in the Streamlit sidebar always reflects the canonical
implementation in async_gateway.py (state, attractors, generate, log, sessions).
"""
import os
import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mycelial Resonance", page_icon="🍄", layout="wide")

st.title("🍄 Mycelial Resonance")
st.caption(
    "Live closed-loop biofeedback — baseline → calibrated audio → α-peak steering → debrief. "
    "Reads `esp32_biometric_data` and writes results to `mre_live_sessions`."
)

GATEWAY_URL = os.environ.get("TI_GATEWAY_URL", "http://localhost:5000")
EMBED_URL = f"{GATEWAY_URL}/mycelial"

with st.expander("ℹ️ About this page", expanded=False):
    st.markdown(
        """
        This page hosts the canonical **live closed-loop** session UI:

        1. **Pre-flight** — verifies your Muse / Polar bridge is streaming fresh samples.
        2. **🔵 Baseline** — accumulates an α-peak baseline for the configured duration (default 5 min).
        3. **🟢 Steering** — generates a fresh WAV calibrated to your *measured* baseline,
           autoplays it, and tracks live α-peak vs the chosen attractor target with a
           configurable tolerance band.
        4. **📊 Debrief** — writes baseline mean, final mean, drift, time-in-band, and sample
           count to `mre_live_sessions`.

        Defaults: **BLISSFUL_EMPATHIC** attractor (9.5 Hz α/θ + 10 Hz mu overlay), L4 GILE
        harmonic bed enabled, ±0.5 Hz target band.
        """
    )

components.iframe(EMBED_URL, height=1700, scrolling=True)

st.divider()
col1, col2 = st.columns(2)
with col1:
    st.markdown("**Direct link**")
    st.code(EMBED_URL, language=None)
with col2:
    st.markdown("**Static-track fallback**")
    st.caption(
        "If you prefer to generate a WAV manually without running a live session, "
        "use the **Hypercomputer → tab 13** static track generator."
    )
