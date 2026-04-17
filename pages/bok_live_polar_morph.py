"""
🦋🐙 BOK Live Polar Morph — Real-time Butterfly-Octopus Resonance
Driven by your live Polar H10 HRV stream via /api/polar/latest

The BOK r(θ) equation is parameterized by your live biometrics:
- ρ (coherence)  ← Polar coherence score (0-1)
- ϕ (psi-align)  ← Phase derived from RMSSD modulation
- τ (tralse)     ← Heart-rate-based Tralse phase factor
- B/D ratio      ← Wing/arm chirality coupling driven by coherence

When you reach high HRV coherence, the BOK approaches the Verisyn/Myrion limit
(ρ → 1) smoothly, with wing/arm ratio stabilizing near 2.0 (Dirac-massive).
When coherence drops, the BOK fragments — direct visual feedback on your state.
"""
import streamlit as st
import numpy as np
import plotly.graph_objects as go
import requests
import time

st.set_page_config(page_title="BOK Live Morph", page_icon="🦋", layout="wide")

st.title("🦋🐙 BOK Live Morph — Heart-Driven Butterfly-Octopus Resonance")
st.caption(
    "Real-time visualization of the Butterfly-Octopus Knot equation driven by your "
    "live Polar H10 stream. The shape morphs with your heart coherence. "
    "**High coherence → smooth approach to Verisyn/Myrion attractor.**"
)

# ----- BOK equation -----
THETA = np.linspace(0, 2 * np.pi, 1200)

def bok_r(theta, A, B, C, D, k, phi, tau):
    s = theta + phi
    return (
        A * np.exp(np.sin(s))
        - B * np.cos(4 * s)
        + C * np.sin((2 * s - np.pi) / 24.0) ** 5
        + D * np.cos(k * tau * theta)
    )

def measure_wing_arm(r):
    r_pos = np.maximum(r, 0)
    n = len(r_pos)
    wing_idx = [int(t * n / (2 * np.pi)) for t in [np.pi / 4, 3 * np.pi / 4, 5 * np.pi / 4, 7 * np.pi / 4]]
    arm_idx = [int(t * n / (2 * np.pi)) for t in [0, np.pi / 2, np.pi, 3 * np.pi / 2]]
    w = float(np.mean([r_pos[i] for i in wing_idx]))
    a = float(np.mean([r_pos[i] for i in arm_idx]))
    return w, a, (w / a if a > 0.05 else float("nan"))

# ----- Polar fetcher -----
@st.cache_data(ttl=2)
def fetch_polar():
    try:
        r = requests.get("http://127.0.0.1:5000/api/polar/latest", timeout=2)
        if r.ok:
            return r.json()
    except Exception:
        pass
    return None

# ----- Sidebar controls -----
with st.sidebar:
    st.header("Controls")
    refresh_secs = st.slider("Refresh interval (s)", 1, 10, 2)
    A = st.slider("A (envelope)", 0.1, 2.0, 1.0, 0.05)
    C = st.slider("C (sin⁵ modulation)", 0.0, 1.0, 0.3, 0.05)
    show_targets = st.checkbox("Show Verisyn target overlay", True)
    use_demo_pulse = st.checkbox("Demo mode (synthetic pulse if Polar offline)", True)

# ----- Live data -----
data = fetch_polar()
hr = rmssd = coh = None
src = "❌ no data"
if data and isinstance(data, dict) and data.get("heart_rate"):
    hr = data.get("heart_rate")
    rmssd = (data.get("hrv") or {}).get("rmssd")
    coh = (data.get("hrv") or {}).get("coherence")
    src = "✅ live Polar H10"
elif use_demo_pulse:
    t = time.time()
    hr = 72 + 8 * np.sin(t / 5)
    rmssd = 35 + 15 * np.sin(t / 7)
    coh = 0.55 + 0.35 * np.sin(t / 11)
    src = "⚠️ demo pulse (Polar offline)"

# ----- Map biometrics → BOK params -----
if coh is None:
    coh = 0.5
rho = float(np.clip(coh, 0.0, 1.0))                                  # coherence → ρ
phi = float(((rmssd or 30) % 60) / 60.0 * 2 * np.pi - np.pi)          # RMSSD-mod phase → ϕ
tau = float(0.7 + 0.6 * (((hr or 72) - 50) / 50))                     # HR → τ in [~0.7, ~1.4]
# B/D coupling: coherence drives chirality breaking strength toward Dirac-2.0
B = 0.4 + 0.5 * rho
D = 0.6 - 0.3 * rho
k = 8.0

r = bok_r(THETA, A, B, C, D, k, phi, tau)
w, a, ratio = measure_wing_arm(r)

# ----- Layout -----
c1, c2, c3, c4 = st.columns(4)
c1.metric("Source", src)
c2.metric("HR", f"{hr:.0f} bpm" if hr else "—")
c3.metric("RMSSD", f"{rmssd:.1f} ms" if rmssd else "—")
c4.metric("Coherence ρ", f"{rho:.2f}")

c5, c6, c7, c8 = st.columns(4)
c5.metric("ϕ (psi-align)", f"{phi:+.2f} rad")
c6.metric("τ (Tralse)", f"{tau:.2f}")
c7.metric("Wing / Arm", f"{ratio:.3f}" if not np.isnan(ratio) else "—",
          delta=f"{ratio - 2.0:+.2f} from 2.0" if not np.isnan(ratio) else None)
c8.metric("Verisyn distance", f"{abs(1 - rho):.3f}")

# ----- Polar plot -----
fig = go.Figure()
fig.add_trace(go.Scatterpolar(
    r=np.maximum(r, 0), theta=np.degrees(THETA), mode="lines",
    line=dict(color="magenta", width=2.5), name="BOK r(θ)",
))
if show_targets:
    # Verisyn target circle at unit coherence
    fig.add_trace(go.Scatterpolar(
        r=np.full_like(THETA, 1.0), theta=np.degrees(THETA),
        mode="lines", line=dict(color="cyan", width=1, dash="dot"),
        name="Verisyn (ρ=1) target",
    ))
fig.update_layout(
    polar=dict(
        bgcolor="#0a0a14",
        radialaxis=dict(range=[0, 4.5], showticklabels=False, gridcolor="#333"),
        angularaxis=dict(gridcolor="#333"),
    ),
    paper_bgcolor="#0a0a14",
    font=dict(color="white"),
    height=600,
    title=f"BOK Live: ϕ={phi:+.2f}, τ={tau:.2f}, ρ={rho:.2f}, wing/arm={ratio:.2f}",
    showlegend=True,
)
st.plotly_chart(fig, use_container_width=True)

# ----- Coherence-state interpretation -----
if rho > 0.75:
    st.success(f"🔥 **HIGH COHERENCE (ρ={rho:.2f})** — BOK is approaching Verisyn/Myrion. "
               "Wings and arms in Dirac-stable 2:1 ratio. This is your high-G̲ window — "
               "ideal moment for GILE-aligned intention or research insight.")
elif rho > 0.45:
    st.info(f"➡️ **MID COHERENCE (ρ={rho:.2f})** — BOK in transit. Continue heart-focused "
            "breathing (5-6 breaths/min) to drive ρ toward 1.")
else:
    st.warning(f"⚠️ **LOW COHERENCE (ρ={rho:.2f})** — BOK fragmenting. Reset with slow nasal "
               "inhale (4s) / extended exhale (6s). The shape will reorganize as ρ rises.")

# Auto-refresh
time.sleep(refresh_secs)
st.rerun()
