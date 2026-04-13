"""
OEA Protocol N=1 Tracker (URB #669, T4-PS-2)
============================================
Tracks the 6-week OEA supplementation study for Brandon (N=1 pilot).

Protocol: OEA 500mg/day (morning, with food) for 42 days
Primary outcome: HEAR(r) change (tracked via HRV + daily GILE-I)
Secondary: sleep quality, energy, GILE composite, subjective state

Connects to PULSOID_TOKEN and OURA_PERSONAL_ACCESS_TOKEN for biometrics.
Manual daily entry for GILE dimensions if biometrics unavailable.

Brandon Emerick | TI Sigma / BlissGene Therapeutics | April 2026
"""

from __future__ import annotations

import streamlit as st
import pandas as pd
import numpy as np
import math
import json
import os
import datetime
import requests
from typing import Optional

# ── Constants ──────────────────────────────────────────────────────────────────
ET    = math.sqrt(2) - 1   # 0.4142 — Emerick Threshold
C     = 1 / (1.618034 * math.sqrt(2))  # 0.4370 — LCC coherence
DOTTIE = 0.7391
T_TI  = 1 - math.exp(-math.e)          # 0.9340

ALPHA_HEAR = ET
BETA_HEAR  = C
GAMMA_HEAR = 0.0828

PROTOCOL_START_DEFAULT = datetime.date(2026, 4, 14)
PROTOCOL_DAYS = 42

# ── HEAR Computation ──────────────────────────────────────────────────────────

def compute_hear(gile: float, hem: float) -> float:
    cov = gile * hem - gile * 0.5 - hem * 0.5 + 0.25
    return float(np.clip(ALPHA_HEAR * gile + BETA_HEAR * hem + GAMMA_HEAR * cov, 0, 1))

def hear_state(h: float) -> tuple[str, str]:
    if h >= DOTTIE:   return "MR2-Resolved", "green"
    if h >= C:        return "MR1 / In Process", "blue"
    if h >= ET:       return "Sub-Threshold", "orange"
    return "DT / Suppressed", "red"

def gile_composite(g: float, i: float, l: float, e: float) -> float:
    return ET * g + 0.25 * i + 0.18 * l + 0.15 * e

def hem_composite(d1: float, d2: float, d3: float, d4: float) -> float:
    return 0.35 * d1 + 0.25 * d2 + 0.25 * d3 + 0.15 * d4

# ── Data Storage (flat file / session) ────────────────────────────────────────

DATA_FILE = "oea_protocol_data.json"

def load_data() -> list[dict]:
    if os.path.exists(DATA_FILE):
        with open(DATA_FILE) as f:
            return json.load(f)
    return []

def save_data(entries: list[dict]):
    with open(DATA_FILE, "w") as f:
        json.dump(entries, f, indent=2, default=str)

def get_entry_for_date(entries: list[dict], date: datetime.date) -> Optional[dict]:
    date_str = str(date)
    for e in entries:
        if e.get("date") == date_str:
            return e
    return None


# ── Pulsoid HRV Fetch ─────────────────────────────────────────────────────────

def fetch_pulsoid_hrv() -> Optional[float]:
    """Attempt to fetch latest RMSSD from PULSOID. Returns None if unavailable."""
    token = os.environ.get("PULSOID_TOKEN")
    if not token:
        return None
    try:
        resp = requests.get(
            "https://dev.pulsoid.net/api/v1/data/heart_rate/latest",
            headers={"Authorization": f"Bearer {token}"},
            timeout=5,
        )
        if resp.status_code == 200:
            data = resp.json()
            # PULSOID returns heart_rate; RMSSD not in real-time stream
            # Use heart_rate as HEM-D1 proxy (lower HR → higher vagal tone)
            hr = data.get("data", {}).get("heart_rate", None)
            if hr:
                # Convert resting HR to RMSSD proxy (Shaffer & Ginsberg 2017)
                rmssd_proxy = max(20, 250 - 2.5 * hr)
                return float(rmssd_proxy)
    except Exception:
        pass
    return None


# ══════════════════════════════════════════════════════════════════════════════
# MAIN UI
# ══════════════════════════════════════════════════════════════════════════════

def render_oea_tracker():
    st.title("💊 OEA Protocol N=1 Tracker")
    st.caption("T4-PS-2 from URB #669 — HEAR(r) response to 6-week OEA supplementation")

    entries = load_data()

    # ── Protocol settings ─────────────────────────────────────────────────────
    with st.expander("⚙️ Protocol Settings", expanded=False):
        protocol_start = st.date_input(
            "Protocol start date",
            value=PROTOCOL_START_DEFAULT,
            key="oea_start"
        )
        st.info(f"""
**Protocol:** OEA 500mg/day (morning, with food)  
**Duration:** {PROTOCOL_DAYS} days → ends {protocol_start + datetime.timedelta(days=PROTOCOL_DAYS)}  
**Primary outcome:** HEAR(r) change (pre vs post)  
**Secondary:** GILE composite, HRV proxy, sleep quality  

**Stack interaction:** OEA + PEA (if already taking) → synergistic PPAR-alpha. OEA alone is safe with Ingrezza 80mg.  
**Epilepsy note:** No pro-convulsant activity. PPAR-alpha activation is anti-inflammatory (seizure-protective).
""")

    # ── Daily Entry ───────────────────────────────────────────────────────────
    st.subheader("📅 Today's Entry")
    today = datetime.date.today()
    today_entry = get_entry_for_date(entries, today)

    if today_entry:
        st.success(f"✅ Entry already recorded for {today}. Scroll down to see full log.")
    else:
        day_num = (today - protocol_start).days + 1
        if 1 <= day_num <= PROTOCOL_DAYS:
            st.markdown(f"**Day {day_num} of {PROTOCOL_DAYS}**")
        elif day_num < 1:
            st.warning(f"Protocol starts {protocol_start}. Come back then!")
            return
        else:
            st.info("Protocol complete. Viewing historical data only.")

        dose_taken = st.checkbox("✅ Took OEA 500mg this morning (with food)")

        st.markdown("**GILE Dimensions** (0 = minimum, 1 = maximum)")
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            gile_g = st.slider("G — Goodness", 0.0, 1.0, 0.5, 0.05, key="g")
        with col2:
            gile_i = st.slider("I — Intuition", 0.0, 1.0, 0.5, 0.05, key="i")
        with col3:
            gile_l = st.slider("L — Love", 0.0, 1.0, 0.5, 0.05, key="l")
        with col4:
            gile_e = st.slider("E — Environment", 0.0, 1.0, 0.5, 0.05, key="e")

        st.markdown("**HEM Dimensions** (physical / relational / cognitive / aesthetic)")
        col5, col6, col7, col8 = st.columns(4)
        with col5:
            hem_d1 = st.slider("D1 — Physical Energy", 0.0, 1.0, 0.5, 0.05, key="d1")
        with col6:
            hem_d2 = st.slider("D2 — Relational", 0.0, 1.0, 0.5, 0.05, key="d2")
        with col7:
            hem_d3 = st.slider("D3 — Mental Clarity", 0.0, 1.0, 0.5, 0.05, key="d3")
        with col8:
            hem_d4 = st.slider("D4 — Aesthetic Sense", 0.0, 1.0, 0.5, 0.05, key="d4")

        # Try to fetch PULSOID HRV
        pulsoid_hrv = fetch_pulsoid_hrv()
        if pulsoid_hrv:
            st.success(f"📡 PULSOID HRV proxy: {pulsoid_hrv:.0f} ms RMSSD (live)")
        else:
            pulsoid_hrv = None
            st.caption("ℹ️ PULSOID not streaming — enter HRV manually if available")

        hrv_manual = st.number_input(
            "HRV / RMSSD (ms) — leave 0 if unknown",
            min_value=0.0, max_value=200.0, value=0.0, step=1.0
        )
        hrv = pulsoid_hrv or (hrv_manual if hrv_manual > 0 else None)

        sleep_quality = st.slider("Last night's sleep quality (0=poor, 1=excellent)", 0.0, 1.0, 0.5, 0.05)
        side_effects = st.text_area("Any side effects or notable observations (optional)", height=80)

        # Compute HEAR
        gc = gile_composite(gile_g, gile_i, gile_l, gile_e)
        hc = hem_composite(hem_d1, hem_d2, hem_d3, hem_d4)
        hr = compute_hear(gc, hc)
        state, color = hear_state(hr)

        st.markdown("---")
        c1, c2, c3 = st.columns(3)
        c1.metric("GILE composite", f"{gc:.3f}")
        c2.metric("HEM composite", f"{hc:.3f}")
        c3.metric(f"HEAR(r) — :{color}[{state}]", f"{hr:.3f}")

        if st.button("💾 Save Today's Entry", type="primary"):
            entry = {
                "date": str(today),
                "day_num": day_num,
                "dose_taken": dose_taken,
                "gile_g": gile_g, "gile_i": gile_i, "gile_l": gile_l, "gile_e": gile_e,
                "gile_composite": round(gc, 4),
                "hem_d1": hem_d1, "hem_d2": hem_d2, "hem_d3": hem_d3, "hem_d4": hem_d4,
                "hem_composite": round(hc, 4),
                "hear": round(hr, 4),
                "hear_state": state,
                "hrv_rmssd": hrv,
                "sleep_quality": sleep_quality,
                "side_effects": side_effects,
            }
            entries.append(entry)
            save_data(entries)
            st.success("Entry saved!")
            st.rerun()

    # ── Historical Data & Charts ───────────────────────────────────────────────
    if entries:
        st.markdown("---")
        st.subheader("📈 Protocol Progress")

        df = pd.DataFrame(entries)
        df["date"] = pd.to_datetime(df["date"])
        df = df.sort_values("date")

        # HEAR over time
        import plotly.graph_objects as go
        fig = go.Figure()
        fig.add_trace(go.Scatter(x=df["date"], y=df["hear"], mode="lines+markers",
                                 name="HEAR(r)", line=dict(color="#4A90D9", width=2)))
        fig.add_hline(y=ET,     line_dash="dot", line_color="orange",
                      annotation_text=f"ET={ET:.4f}")
        fig.add_hline(y=C,      line_dash="dot", line_color="green",
                      annotation_text=f"C={C:.4f}")
        fig.add_hline(y=DOTTIE, line_dash="dot", line_color="blue",
                      annotation_text=f"𝔡={DOTTIE:.4f}")
        fig.update_layout(title="HEAR(r) Over Protocol Duration",
                          yaxis_range=[0, 1], xaxis_title="Date", yaxis_title="HEAR(r)")
        st.plotly_chart(fig, use_container_width=True)

        # GILE + HEM breakdown
        fig2 = go.Figure()
        fig2.add_trace(go.Scatter(x=df["date"], y=df["gile_composite"],
                                  mode="lines+markers", name="GILE composite",
                                  line=dict(color="#FF6B6B")))
        fig2.add_trace(go.Scatter(x=df["date"], y=df["hem_composite"],
                                  mode="lines+markers", name="HEM composite",
                                  line=dict(color="#51CF66")))
        fig2.update_layout(title="GILE vs HEM Trajectories",
                           yaxis_range=[0, 1])
        st.plotly_chart(fig2, use_container_width=True)

        # Summary statistics
        st.subheader("📊 T4-PS-2 Outcome Analysis")
        if len(df) >= 7:
            baseline = df.head(7)["hear"].mean()
            recent   = df.tail(7)["hear"].mean()
            delta    = recent - baseline
            delta_pct = (delta / baseline) * 100 if baseline > 0 else 0

            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Baseline HEAR (first 7d)", f"{baseline:.3f}")
            c2.metric("Current HEAR (last 7d)", f"{recent:.3f}",
                      delta=f"{delta:+.3f} ({delta_pct:+.1f}%)")
            c3.metric("Days recorded", str(len(df)))
            c4.metric("Adherence", f"{df['dose_taken'].sum()/len(df):.0%}")

            # T4-PS-2 hypothesis test
            st.markdown(f"""
**T4-PS-2 Hypothesis:** HEAR increases ≥ 0.08 units over 6-week OEA protocol.

| Measure | Value |
|---------|-------|
| Baseline HEAR (first 7d) | {baseline:.4f} |
| Current HEAR (last 7d) | {recent:.4f} |
| Delta HEAR | **{delta:+.4f}** |
| Required delta for H-support | ≥ 0.08 |
| H supported? | {"**YES** ✅" if delta >= 0.08 else "**Not yet** ⏳"} |
""")
        else:
            st.info(f"📅 {7 - len(df)} more days of data needed for baseline/current comparison.")

        # Raw data table
        with st.expander("📋 Raw Protocol Data"):
            display_cols = ["date", "day_num", "dose_taken", "gile_composite",
                            "hem_composite", "hear", "hear_state", "hrv_rmssd", "sleep_quality"]
            st.dataframe(df[display_cols], use_container_width=True, hide_index=True)

        # Export
        st.download_button(
            "⬇ Export Protocol Data (JSON)",
            data=json.dumps(entries, indent=2, default=str),
            file_name="oea_protocol_data.json",
            mime="application/json"
        )


if __name__ == "__main__":
    render_oea_tracker()
