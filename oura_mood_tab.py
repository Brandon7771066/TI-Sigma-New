"""
💍 Oura Ring Gen 3 — Mood Amplifier Dashboard Tab
==================================================
Shows all ~50+ ring metrics in a live, auto-refreshing panel.

Data sync: Oura syncs from the ring to the cloud every ~15 min
when Bluetooth is active, or on demand when you open the Oura app.
This tab always shows the latest synced snapshot.

Author: Brandon Emerick (TI Sigma / BlissGene Therapeutics)
Date:   April 6, 2026
"""

import os
import time
import math
import streamlit as st
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from datetime import datetime, date, timedelta
from typing import Optional

from oura_ring_integration import OuraRingIntegration, OuraDailyData, OuraHeartRatePoint


# ── Helpers ────────────────────────────────────────────────────────────────────

def _score_gauge(score: Optional[int], label: str, width: int = 130) -> str:
    """Return a small HTML arc-gauge for a 0-100 score."""
    if score is None:
        val, color = 0, "#555"
    else:
        val = max(0, min(100, score))
        color = "#00cc44" if val >= 85 else "#88dd00" if val >= 70 else "#ffcc00" if val >= 55 else "#ff4444"
    pct = val / 100.0
    # SVG arc (half-circle)
    r = 44
    cx, cy = 55, 55
    circ = math.pi * r           # half circumference
    dash_on  = pct * circ
    dash_off = circ - dash_on
    return f"""
    <div style="text-align:center;width:{width}px;display:inline-block;">
      <svg width="{width}" height="70" viewBox="0 0 110 70">
        <path d="M 11,55 A 44,44 0 0,1 99,55" fill="none" stroke="#333" stroke-width="10" stroke-linecap="round"/>
        <path d="M 11,55 A 44,44 0 0,1 99,55" fill="none" stroke="{color}" stroke-width="10"
              stroke-linecap="round"
              stroke-dasharray="{dash_on:.1f} {dash_off:.1f}"
              transform="rotate(0 {cx} {cy})"/>
        <text x="{cx}" y="{cy-4}" text-anchor="middle" font-size="20" fill="{color}" font-weight="bold">{val if score is not None else '—'}</text>
      </svg>
      <div style="color:#aaa;font-size:0.75rem;margin-top:-8px;">{label}</div>
    </div>"""


def _fmt_dur(secs: Optional[int]) -> str:
    if secs is None or secs == 0:
        return "—"
    h, m = divmod(secs // 60, 60)
    return f"{h}h {m:02d}m"


def _pct(part: Optional[int], total: Optional[int]) -> str:
    if not part or not total:
        return "—"
    return f"{100 * part // total}%"


def _contributor_bar(label: str, value: Optional[int]) -> str:
    """Horizontal bar for a readiness/activity contributor (0-100)."""
    if value is None:
        return ""
    color = "#00cc44" if value >= 85 else "#88dd00" if value >= 70 else "#ffcc00" if value >= 55 else "#ff4444"
    return f"""
    <div style="margin:3px 0;">
      <div style="display:flex;justify-content:space-between;font-size:0.78rem;color:#aaa;">
        <span>{label}</span><span style="color:{color};">{value}</span>
      </div>
      <div style="background:#222;border-radius:4px;height:6px;">
        <div style="background:{color};width:{value}%;height:6px;border-radius:4px;"></div>
      </div>
    </div>"""


# ── Oura client cached in session state ────────────────────────────────────────

def _get_client() -> OuraRingIntegration:
    if "oura_client" not in st.session_state:
        st.session_state.oura_client = OuraRingIntegration()
    return st.session_state.oura_client


def _get_today(oura: OuraRingIntegration, force: bool = False) -> Optional[OuraDailyData]:
    """Cache today's snapshot for 5 minutes."""
    cache_key = "oura_today_cache"
    ts_key    = "oura_today_ts"
    now = time.time()
    if not force and cache_key in st.session_state:
        if now - st.session_state.get(ts_key, 0) < 300:
            return st.session_state[cache_key]
    try:
        snap = oura.get_today_snapshot()
        st.session_state[cache_key] = snap
        st.session_state[ts_key]    = now
        return snap
    except Exception as e:
        st.session_state.setdefault("oura_error", str(e))
        return None


def _get_history(oura: OuraRingIntegration, days: int = 7) -> list:
    cache_key = f"oura_hist_{days}"
    ts_key    = f"oura_hist_ts_{days}"
    now = time.time()
    if cache_key in st.session_state:
        if now - st.session_state.get(ts_key, 0) < 600:
            return st.session_state[cache_key]
    try:
        hist = oura.get_combined_daily_data(
            start_date=(date.today() - timedelta(days=days)).isoformat(),
            end_date=date.today().isoformat(),
        )
        st.session_state[cache_key] = hist
        st.session_state[ts_key]    = now
        return hist
    except Exception:
        return []


def _get_hr(oura: OuraRingIntegration, hours: int = 8) -> list:
    cache_key = f"oura_hr_{hours}"
    ts_key    = f"oura_hr_ts_{hours}"
    now = time.time()
    if cache_key in st.session_state:
        if now - st.session_state.get(ts_key, 0) < 120:
            return st.session_state[cache_key]
    try:
        pts = oura.get_heart_rate(hours_back=hours)
        st.session_state[cache_key] = pts
        st.session_state[ts_key]    = now
        return pts
    except Exception:
        return []


# ── Main Render ────────────────────────────────────────────────────────────────

def render_oura_tab():
    """Full Oura Ring dashboard — call from mood_amplifier_hub.py."""

    oura = _get_client()
    token_set = bool(os.getenv("OURA_PERSONAL_ACCESS_TOKEN"))

    # ── Top header
    st.markdown("""
    <div style="background:linear-gradient(135deg,#0a0a1a,#1a0a2e);
                border-radius:14px;padding:1.2rem 1.6rem;margin-bottom:1rem;
                border:1px solid #2a1a4e;">
      <div style="display:flex;align-items:center;gap:1rem;">
        <span style="font-size:2rem;">💍</span>
        <div>
          <div style="color:#fff;font-size:1.2rem;font-weight:bold;">Oura Ring Gen 3 — Live Dashboard</div>
          <div style="color:#9988cc;font-size:0.82rem;">
            PPG Heart Rate · Sleep Stages · HRV · SpO₂ · Readiness · Stress · Resilience · VO₂ Max
          </div>
        </div>
      </div>
    </div>
    """, unsafe_allow_html=True)

    if not token_set:
        st.error(
            "**Oura Personal Access Token not found.**\n\n"
            "To connect your ring:\n"
            "1. Go to [cloud.ouraring.com/personal-access-tokens](https://cloud.ouraring.com/personal-access-tokens)\n"
            "2. Create a new token\n"
            "3. Add it to Replit Secrets as **`OURA_PERSONAL_ACCESS_TOKEN`**\n\n"
            "*The app will connect instantly once the secret is saved.*"
        )
        _render_demo_mode()
        return

    # ── Control bar
    col_r, col_w, col_sync = st.columns([2, 2, 1])
    with col_r:
        view_days = st.selectbox("History window", [3, 7, 14, 30],
                                 index=1, key="oura_days",
                                 format_func=lambda x: f"Last {x} days")
    with col_w:
        hr_hours = st.selectbox("HR chart window", [2, 4, 8, 12, 24],
                                index=2, key="oura_hr_hours",
                                format_func=lambda x: f"Last {x} hours")
    with col_sync:
        st.markdown("<div style='margin-top:28px;'></div>", unsafe_allow_html=True)
        if st.button("🔄 Sync Now", use_container_width=True, key="oura_sync"):
            for k in list(st.session_state.keys()):
                if k.startswith("oura_") and k not in ("oura_client",):
                    del st.session_state[k]
            st.rerun()

    # ── Fetch data
    today = _get_today(oura)
    history = _get_history(oura, days=view_days)
    hr_points = _get_hr(oura, hours=hr_hours)

    if today is None:
        err = st.session_state.pop("oura_error", "Unknown error")
        st.error(f"Could not fetch data from Oura Cloud: `{err}`")
        return

    # ── TODAY'S SCORES — three gauges
    st.markdown("### Today's Scores")
    gauges_html = (
        _score_gauge(today.readiness_score, "Readiness") +
        "&nbsp;&nbsp;&nbsp;" +
        _score_gauge(today.sleep_score, "Sleep") +
        "&nbsp;&nbsp;&nbsp;" +
        _score_gauge(today.activity_score, "Activity")
    )
    st.markdown(f"<div style='text-align:center;padding:0.5rem 0;'>{gauges_html}</div>",
                unsafe_allow_html=True)

    # ── GILE from Oura
    gile = oura.oura_gile_score(today)
    gile_color = "#00cc44" if gile > 0.5 else "#ffcc00" if gile > 0 else "#ff4444"
    st.markdown(
        f"""<div style="background:#0d1a0d;border:1px solid #1a3a1a;border-radius:10px;
                        padding:0.7rem 1.2rem;margin:0.5rem 0;text-align:center;">
            <span style="color:#aaa;font-size:0.8rem;">Oura → GILE Score &nbsp;</span>
            <span style="color:{gile_color};font-size:1.4rem;font-weight:bold;">{gile:+.3f}</span>
            <span style="color:#888;font-size:0.75rem;"> (scale −2.5 to +2.5)</span>
        </div>""",
        unsafe_allow_html=True,
    )

    st.divider()

    # ── THREE COLUMN LAYOUT: Sleep | Readiness | Activity
    sl_col, rd_col, ac_col = st.columns(3)

    with sl_col:
        st.markdown("#### 🌙 Sleep")
        hrv_display = f"{today.sleep_hrv:.0f} ms" if today.sleep_hrv else "—"
        rhr_display = f"{today.sleep_lowest_hr} bpm" if today.sleep_lowest_hr else "—"
        breath_display = f"{today.sleep_avg_breath:.1f} brpm" if today.sleep_avg_breath else "—"
        st.markdown(f"""
        <div style="background:#0a0a1a;border-radius:10px;padding:1rem;font-size:0.83rem;">
          <div style="display:grid;grid-template-columns:1fr 1fr;gap:0.4rem 1rem;">
            <span style="color:#888;">Total sleep</span>
            <span style="color:#eee;font-weight:bold;">{_fmt_dur(today.total_sleep_duration)}</span>
            <span style="color:#888;">Time in bed</span>
            <span style="color:#eee;">{_fmt_dur(today.time_in_bed)}</span>
            <span style="color:#4499ff;">Deep</span>
            <span style="color:#4499ff;">{_fmt_dur(today.deep_sleep_duration)}</span>
            <span style="color:#9955ff;">REM</span>
            <span style="color:#9955ff;">{_fmt_dur(today.rem_sleep_duration)}</span>
            <span style="color:#66aaff;">Light</span>
            <span style="color:#66aaff;">{_fmt_dur(today.light_sleep_duration)}</span>
            <span style="color:#ff8844;">Awake</span>
            <span style="color:#ff8844;">{_fmt_dur(today.awake_time)}</span>
            <span style="color:#888;">Efficiency</span>
            <span style="color:#eee;">{today.sleep_efficiency or '—'}%</span>
            <span style="color:#888;">Latency</span>
            <span style="color:#eee;">{_fmt_dur(today.sleep_latency)}</span>
            <span style="color:#888;">Restless</span>
            <span style="color:#eee;">{today.restless_periods or '—'} periods</span>
            <span style="color:#00cc88;">HRV (avg)</span>
            <span style="color:#00cc88;font-weight:bold;">{hrv_display}</span>
            <span style="color:#ff6666;">Lowest HR</span>
            <span style="color:#ff6666;">{rhr_display}</span>
            <span style="color:#aaa;">Avg breath</span>
            <span style="color:#aaa;">{breath_display}</span>
            <span style="color:#aaa;">SpO₂</span>
            <span style="color:#aaa;">{f"{today.spo2_average:.1f}%" if today.spo2_average else "—"}</span>
          </div>
        </div>
        """, unsafe_allow_html=True)

    with rd_col:
        st.markdown("#### ⚡ Readiness")
        td = f"{today.temperature_deviation:+.2f}°C" if today.temperature_deviation is not None else "—"
        st.markdown(f"""
        <div style="background:#0a0a1a;border-radius:10px;padding:1rem;">
          <div style="color:#aaa;font-size:0.78rem;margin-bottom:0.6rem;">
            Temp deviation: <span style="color:#eee;">{td}</span> &nbsp;
            Recovery index: <span style="color:#eee;">{today.recovery_index or '—'}</span>
          </div>
          {_contributor_bar("HRV Balance",          today.hrv_balance)}
          {_contributor_bar("Resting HR",           today.resting_heart_rate)}
          {_contributor_bar("Sleep Balance",        today.sleep_balance)}
          {_contributor_bar("Activity Balance",     today.activity_balance)}
          {_contributor_bar("Body Temperature",     today.body_temperature)}
          {_contributor_bar("Recovery Index",       today.recovery_index)}
          {_contributor_bar("Previous Night",       today.previous_night)}
          {_contributor_bar("Previous Day Activity",today.previous_day_activity)}
        </div>
        """, unsafe_allow_html=True)

        # Resilience
        if today.resilience_level:
            lvl_color = {"exceptional": "#00cc44", "strong": "#88dd00",
                         "solid": "#ffcc00", "adequate": "#ff8844",
                         "poor": "#ff4444"}.get(today.resilience_level, "#888")
            st.markdown(f"""
            <div style="background:#0a0a1a;border-radius:10px;padding:0.6rem 1rem;margin-top:0.5rem;">
              <span style="color:#888;font-size:0.78rem;">Resilience: </span>
              <span style="color:{lvl_color};font-weight:bold;">{today.resilience_level.upper()}</span>
            </div>""", unsafe_allow_html=True)

    with ac_col:
        st.markdown("#### 🏃 Activity")
        cal_pct = ""
        if today.active_calories and today.target_calories:
            ratio = today.active_calories / today.target_calories
            cal_pct = f"({100*ratio:.0f}% of target)"
        st.markdown(f"""
        <div style="background:#0a0a1a;border-radius:10px;padding:1rem;font-size:0.83rem;">
          <div style="display:grid;grid-template-columns:1fr 1fr;gap:0.4rem 1rem;">
            <span style="color:#888;">Steps</span>
            <span style="color:#eee;font-weight:bold;">{today.steps:,}" if today.steps else "<span style='color:#555;'>—"}</span>
            <span style="color:#888;">Active cal</span>
            <span style="color:#ffcc44;">{today.active_calories or '—'} kcal {cal_pct}</span>
            <span style="color:#888;">Total cal</span>
            <span style="color:#eee;">{today.total_calories or '—'} kcal</span>
            <span style="color:#888;">Equiv. walk</span>
            <span style="color:#eee;">{f'{today.equivalent_walking_distance/1000:.1f} km' if today.equivalent_walking_distance else '—'}</span>
            <span style="color:#ff6644;">High activity</span>
            <span style="color:#ff6644;">{_fmt_dur(today.high_activity_time)}</span>
            <span style="color:#ffaa44;">Med activity</span>
            <span style="color:#ffaa44;">{_fmt_dur(today.medium_activity_time)}</span>
            <span style="color:#44aaff;">Low activity</span>
            <span style="color:#44aaff;">{_fmt_dur(today.low_activity_time)}</span>
            <span style="color:#888;">Sedentary</span>
            <span style="color:#888;">{_fmt_dur(today.sedentary_time)}</span>
            <span style="color:#888;">Avg MET</span>
            <span style="color:#eee;">{f'{today.average_met:.1f}' if today.average_met else '—'}</span>
            <span style="color:#888;">Inact. alerts</span>
            <span style="color:#eee;">{today.inactivity_alerts or '—'}</span>
          </div>
        </div>""", unsafe_allow_html=True)

        # Stress & VO2 Max
        stress_items = []
        if today.stress_high is not None:
            stress_items.append(f"Stress: {today.stress_high} min")
        if today.recovery_high is not None:
            stress_items.append(f"Recovery: {today.recovery_high} min")
        if today.day_summary:
            stress_items.append(f"Day: {today.day_summary}")
        if today.vo2_max:
            stress_items.append(f"VO₂ Max: {today.vo2_max:.1f}")
        if stress_items:
            st.markdown(
                f"<div style='background:#0a0a1a;border-radius:10px;padding:0.6rem 1rem;"
                f"margin-top:0.5rem;font-size:0.78rem;color:#aaa;'>"
                + " &nbsp;·&nbsp; ".join(stress_items) +
                "</div>", unsafe_allow_html=True)

    st.divider()

    # ── PPG HEART RATE CHART
    st.markdown("#### 💓 PPG Heart Rate (Live from Ring)")
    if hr_points:
        times = [datetime.fromisoformat(p.timestamp.replace('Z', '')) for p in hr_points]
        bpms  = [p.bpm for p in hr_points]
        latest_hr = bpms[-1] if bpms else None
        latest_ts = times[-1].strftime("%H:%M") if times else "—"

        col_hr1, col_hr2, col_hr3 = st.columns([1, 1, 4])
        with col_hr1:
            st.metric("Latest HR", f"{latest_hr} bpm" if latest_hr else "—", help=f"Recorded at {latest_ts}")
        with col_hr2:
            if bpms:
                st.metric("Min / Max", f"{min(bpms)} / {max(bpms)} bpm")
        with col_hr3:
            if bpms:
                import numpy as np
                st.metric("Avg HR", f"{sum(bpms)/len(bpms):.0f} bpm",
                          delta=f"±{float(np.std(bpms)):.1f} SD")

        fig_hr = go.Figure()
        fig_hr.add_trace(go.Scatter(
            x=times, y=bpms,
            mode="lines+markers",
            line=dict(color="#ff4466", width=2),
            marker=dict(size=4, color="#ff4466"),
            fill="tozeroy",
            fillcolor="rgba(255,68,102,0.08)",
            name="HR (bpm)",
        ))
        fig_hr.update_layout(
            height=220,
            margin=dict(l=40, r=20, t=20, b=40),
            paper_bgcolor="rgba(0,0,0,0)",
            plot_bgcolor="rgba(15,15,25,0.8)",
            yaxis=dict(title="bpm", color="#888", gridcolor="#222"),
            xaxis=dict(color="#888", gridcolor="#222"),
            showlegend=False,
        )
        st.plotly_chart(fig_hr, use_container_width=True)
    else:
        st.info("No heart rate data in the selected window. Make sure your ring is synced (open Oura app).")

    st.divider()

    # ── 7-DAY TREND CHARTS
    if history:
        st.markdown(f"#### 📈 {view_days}-Day Trends")

        dates_raw = [d.date for d in history]
        readiness = [d.readiness_score for d in history]
        sleep_sc  = [d.sleep_score for d in history]
        activity  = [d.activity_score for d in history]
        hrv_vals  = [d.sleep_hrv for d in history]
        spo2_vals = [d.spo2_average for d in history]
        steps_v   = [d.steps for d in history]
        gile_v    = [oura.oura_gile_score(d) for d in history]

        fig = make_subplots(
            rows=3, cols=2,
            subplot_titles=(
                "Readiness / Sleep / Activity Scores",
                "GILE Score (Oura → TI Sigma)",
                "Sleep HRV (ms)",
                "SpO₂ (%)",
                "Daily Steps",
                "Sleep Stages Breakdown",
            ),
            vertical_spacing=0.14,
            horizontal_spacing=0.1,
        )

        def _bar(values, color, name, row, col):
            fig.add_trace(go.Bar(x=dates_raw, y=values, name=name,
                                 marker_color=color, opacity=0.85), row=row, col=col)

        def _line(values, color, name, row, col, dash="solid"):
            fig.add_trace(go.Scatter(x=dates_raw, y=values, name=name,
                                     line=dict(color=color, width=2, dash=dash),
                                     mode="lines+markers", marker=dict(size=5)),
                          row=row, col=col)

        # Row 1, Col 1 — scores
        _line(readiness, "#00cc44", "Readiness", 1, 1)
        _line(sleep_sc,  "#9955ff", "Sleep",     1, 1)
        _line(activity,  "#ff8800", "Activity",  1, 1)

        # Row 1, Col 2 — GILE
        gile_colors = ["#00cc44" if g > 0 else "#ff4444" for g in gile_v]
        fig.add_trace(go.Bar(x=dates_raw, y=gile_v, name="GILE",
                             marker_color=gile_colors, opacity=0.85), row=1, col=2)
        fig.add_hline(y=0, line_dash="dot", line_color="#888", row=1, col=2)

        # Row 2, Col 1 — HRV
        _line(hrv_vals, "#00cc88", "HRV ms", 2, 1)

        # Row 2, Col 2 — SpO2
        _line(spo2_vals, "#4499ff", "SpO₂ %", 2, 2)
        fig.update_yaxes(range=[94, 100], row=2, col=2)

        # Row 3, Col 1 — Steps
        _bar(steps_v, "#ffcc44", "Steps", 3, 1)

        # Row 3, Col 2 — Sleep stages stacked bar
        deep_v  = [(d.deep_sleep_duration or 0)//60 for d in history]
        rem_v   = [(d.rem_sleep_duration or 0)//60  for d in history]
        light_v = [(d.light_sleep_duration or 0)//60 for d in history]
        awake_v = [(d.awake_time or 0)//60          for d in history]
        fig.add_trace(go.Bar(x=dates_raw, y=deep_v,  name="Deep",  marker_color="#4499ff",
                             offsetgroup=0), row=3, col=2)
        fig.add_trace(go.Bar(x=dates_raw, y=rem_v,   name="REM",   marker_color="#9955ff",
                             offsetgroup=0, base=deep_v), row=3, col=2)
        light_base = [d + r for d, r in zip(deep_v, rem_v)]
        fig.add_trace(go.Bar(x=dates_raw, y=light_v, name="Light", marker_color="#66aaff",
                             offsetgroup=0, base=light_base), row=3, col=2)

        fig.update_layout(
            height=680,
            showlegend=True,
            barmode="stack",
            legend=dict(orientation="h", yanchor="bottom", y=1.02, font=dict(size=10)),
            margin=dict(l=50, r=20, t=60, b=40),
            paper_bgcolor="rgba(0,0,0,0)",
            plot_bgcolor="rgba(15,15,25,0.8)",
        )
        fig.update_xaxes(color="#888", gridcolor="#222")
        fig.update_yaxes(color="#888", gridcolor="#222")
        st.plotly_chart(fig, use_container_width=True)

    st.divider()

    # ── PSI OPTIMAL WINDOWS
    with st.expander("🎯 Optimal PSI / Decision Windows (High-Recovery Days)", expanded=False):
        try:
            windows = oura.get_optimal_windows(days=30)
            if windows:
                st.markdown("Days where your recovery_quality ≥ 0.70 — best for high-stakes decisions:")
                for w in windows[:10]:
                    color = "#00cc44" if w["recovery_quality"] >= 0.85 else "#88dd00"
                    st.markdown(
                        f"<div style='background:#0a1a0a;border-radius:8px;padding:0.5rem 1rem;"
                        f"margin:0.3rem 0;border-left:4px solid {color};font-size:0.82rem;'>"
                        f"<b style='color:{color};'>{w['date']}</b> &nbsp; "
                        f"Readiness: <b>{w['readiness_score'] or '—'}</b> &nbsp; "
                        f"Sleep: <b>{w['sleep_score'] or '—'}</b> &nbsp; "
                        f"GILE: <b style='color:{color};'>{w['gile_score']:+.3f}</b>"
                        f"</div>", unsafe_allow_html=True)
            else:
                st.info("No high-recovery days in the last 30 days yet.")
        except Exception as e:
            st.warning(f"Could not load optimal windows: {e}")

    # ── SETUP GUIDE
    with st.expander("📖 Sync & Setup Guide", expanded=False):
        st.markdown("""
        ### How Oura Ring Sync Works

        The Oura Gen 3 **does not stream live data** over the internet — it stores everything locally in the ring
        and syncs to the Oura Cloud roughly every 15 minutes when Bluetooth is active.

        **For the freshest data:**
        - Open the **Oura App** on your iPhone → data syncs immediately
        - Keep Bluetooth on → automatic background sync every ~15 min
        - Click **🔄 Sync Now** above to force a re-fetch from the cloud cache

        **Heart Rate specifics (Gen 3 PPG):**
        - **Awake:** ~5-minute intervals via optical PPG
        - **Sleep:** ~30-second intervals (much higher resolution)
        - **During workouts:** continuous via workout mode

        **What this dashboard shows (50+ metrics):**
        | Category | Metrics |
        |----------|---------|
        | Sleep | Score, efficiency, latency, deep/REM/light/awake durations, restless periods, HRV, HR, breathing rate, SpO₂ |
        | Readiness | Score + 8 contributors: HRV balance, resting HR, recovery index, sleep balance, activity balance, body temp, previous night, previous day activity |
        | Activity | Score + 6 contributors, steps, calories, MET, sedentary/active/high time, walking distance |
        | Heart Rate | Continuous PPG — available for any time window |
        | SpO₂ | Overnight average + breathing disturbance index |
        | Stress | High-stress minutes, recovery minutes, day summary label |
        | Resilience | Sleep recovery + daytime recovery + overall level |
        | VO₂ Max | Aerobic capacity estimate |

        **GILE Integration:**
        Oura readiness + sleep + HRV balance feed directly into the TI Sigma GILE score:
        `GILE = 5 × (recovery_quality − 0.5)` where recovery_quality = weighted average of your scores.
        """)


# ── Demo Mode (no token) ───────────────────────────────────────────────────────

def _render_demo_mode():
    """Show a preview of what the dashboard will look like, with placeholder data."""
    st.markdown("---")
    st.markdown("**Preview — what you'll see once connected:**")

    col1, col2, col3 = st.columns(3)
    for col, label, val, color in [
        (col1, "Readiness", 84, "#88dd00"),
        (col2, "Sleep",     91, "#00cc44"),
        (col3, "Activity",  73, "#ffcc00"),
    ]:
        with col:
            st.markdown(
                f"<div style='background:#111;border-radius:10px;padding:1rem;text-align:center;'>"
                f"<div style='color:{color};font-size:2rem;font-weight:bold;'>{val}</div>"
                f"<div style='color:#888;font-size:0.8rem;'>{label}</div>"
                f"</div>", unsafe_allow_html=True)

    import numpy as np
    t = [datetime.now() - timedelta(minutes=5*i) for i in range(48, 0, -1)]
    bpm = [int(62 + 8*np.sin(i*0.2) + np.random.normal(0,1)) for i in range(48)]
    fig = go.Figure(go.Scatter(x=t, y=bpm, mode="lines",
                               line=dict(color="#ff4466", width=2),
                               fill="tozeroy", fillcolor="rgba(255,68,102,0.08)"))
    fig.update_layout(title="Sample PPG Heart Rate (demo data)",
                      height=180, margin=dict(l=40,r=20,t=30,b=30),
                      paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(15,15,25,0.8)",
                      yaxis=dict(color="#888", gridcolor="#222"),
                      xaxis=dict(color="#888", gridcolor="#222"))
    st.plotly_chart(fig, use_container_width=True)
