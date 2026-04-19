"""
Mood Amplifier Live Dashboard

Polls the same /api/biometric_data PostgreSQL table that your Acer's
muse_live_mood_with_bridge.py is POSTing to. Auto-refreshes every 2
seconds. Shows live STATE, alpha/beta/theta, ratios, and a 5-minute
time-series chart so you and the agent can both watch the basin.

Run:  streamlit run mood_amplifier_live_dashboard.py --server.port 3000 --server.headless true
"""
import os
import time
from datetime import datetime, timedelta
import psycopg2
import pandas as pd
import streamlit as st

st.set_page_config(
    page_title="Mood Amplifier Live",
    layout="wide",
    page_icon="🦋",
)

REFRESH_SEC = 2
DEVICE_FILTER = "Muse2-MindMonitor-Acer"


@st.cache_resource
def get_conn():
    return psycopg2.connect(os.environ["DATABASE_URL"])


def fetch_recent(minutes: int = 5) -> pd.DataFrame:
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        """
        SELECT timestamp, alpha, beta, theta, gamma, delta, session_id
        FROM esp32_biometric_data
        WHERE device_id = %s
          AND timestamp > NOW() - INTERVAL '%s minutes'
        ORDER BY timestamp ASC
        """,
        (DEVICE_FILTER, minutes),
    )
    rows = cur.fetchall()
    cur.close()
    df = pd.DataFrame(
        rows,
        columns=["ts", "alpha", "beta", "theta", "gamma", "delta", "session_id"],
    )
    return df


def state_from(alpha: float, beta: float, theta: float):
    ab = alpha / beta if beta else 0.0
    tb = theta / beta if beta else 0.0
    state = "ALERT"
    if ab > 1.5:
        state = "RELAXED"
    if tb > 1.5:
        state = "MEDITATIVE"
    if ab < 0.6 and tb < 0.6:
        state = "FOCUSED"
    return state, ab, tb


STATE_COLORS = {
    "RELAXED": ("#1f8a4c", "🧘"),
    "MEDITATIVE": ("#7c3aed", "💜"),
    "FOCUSED": ("#1d4ed8", "🎯"),
    "ALERT": ("#d97706", "⚡"),
    "NO DATA": ("#6b7280", "⏳"),
}


def big_banner(state: str, ab: float, tb: float):
    color, icon = STATE_COLORS.get(state, STATE_COLORS["NO DATA"])
    st.markdown(
        f"""
        <div style="background:{color};padding:24px;border-radius:12px;
                    text-align:center;color:white;margin-bottom:16px;">
          <div style="font-size:18px;opacity:0.85;">CURRENT BRAIN STATE</div>
          <div style="font-size:64px;font-weight:700;line-height:1.1;">{icon} {state}</div>
          <div style="font-size:16px;opacity:0.85;margin-top:8px;">
            Alpha/Beta = {ab:.2f} &nbsp;&nbsp;|&nbsp;&nbsp; Theta/Beta = {tb:.2f}
          </div>
        </div>
        """,
        unsafe_allow_html=True,
    )


st.title("🦋 Mood Amplifier — Live Session")

df = fetch_recent(5)

if df.empty:
    st.warning(
        "No data yet from your Acer in the last 5 minutes. "
        "Make sure muse_live_mood_with_bridge.py is running and posting OK 201."
    )
    big_banner("NO DATA", 0.0, 0.0)
else:
    last = df.iloc[-1]
    state, ab, tb = state_from(last.alpha, last.beta, last.theta)
    big_banner(state, ab, tb)

    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Alpha", f"{last.alpha:+.3f}")
    c2.metric("Beta", f"{last.beta:+.3f}")
    c3.metric("Theta", f"{last.theta:+.3f}")
    c4.metric("Gamma", f"{last.gamma:+.3f}")

    st.markdown("### 📈 Last 5 Minutes — Brain Bands")
    chart_df = df.set_index("ts")[["alpha", "beta", "theta"]]
    st.line_chart(chart_df, height=280)

    st.markdown("### 📊 Session Info")
    c5, c6, c7, c8 = st.columns(4)
    c5.metric("Rows received", len(df))
    age = (datetime.utcnow() - last.ts.to_pydatetime()).total_seconds()
    c6.metric("Last reading age", f"{age:.1f}s")
    c7.metric("Session ID", str(last.session_id or "—"))
    duration = (df["ts"].iloc[-1] - df["ts"].iloc[0]).total_seconds()
    c8.metric("Session duration", f"{duration/60:.1f} min")

    with st.expander("Raw recent rows"):
        st.dataframe(df.tail(20).iloc[::-1], use_container_width=True)

st.markdown("---")
st.markdown("### 📝 Session Journal")
journal_path = "data/mood_amplifier/live_journal.txt"
os.makedirs(os.path.dirname(journal_path), exist_ok=True)

with st.form("journal_form", clear_on_submit=True):
    note = st.text_input(
        "Add a note in present time (mood, intention, sensation, anything):",
        placeholder="e.g. 'sadness arriving alongside warmth'",
    )
    submitted = st.form_submit_button("Save note")
    if submitted and note.strip():
        with open(journal_path, "a") as f:
            f.write(f"{datetime.utcnow().isoformat()} | {note.strip()}\n")
        st.success("Saved.")

if os.path.exists(journal_path):
    with open(journal_path) as f:
        lines = f.readlines()[-15:]
    if lines:
        st.markdown("**Recent notes:**")
        for ln in reversed(lines):
            st.text(ln.rstrip())

st.caption(f"Auto-refreshing every {REFRESH_SEC}s. Polling device: `{DEVICE_FILTER}`.")

time.sleep(REFRESH_SEC)
st.rerun()
