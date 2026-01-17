"""
Mind Control Pong - Simple Version
"""

import streamlit as st
import numpy as np
import time

st.set_page_config(page_title="Brain Pong", page_icon="🧠", layout="wide")

# Session state
if 'ball_x' not in st.session_state:
    st.session_state.ball_x = 50.0
    st.session_state.ball_y = 50.0
    st.session_state.ball_vx = 2.0
    st.session_state.ball_vy = 1.0
    st.session_state.player_y = 50.0
    st.session_state.ai_y = 50.0
    st.session_state.player_score = 0
    st.session_state.ai_score = 0
    st.session_state.running = False
    st.session_state.L = 0.6
    st.session_state.E = 0.7
    st.session_state.focus_count = 0

st.title("🧠 Mind Control Pong")
st.write("**Click FOCUS to boost your brain power! The paddle will track the ball better with higher L×E.**")

# Controls row
c1, c2, c3, c4 = st.columns(4)

with c1:
    if st.button("▶️ START GAME", use_container_width=True):
        st.session_state.running = True
        st.session_state.ball_x = 50.0
        st.session_state.ball_y = 50.0
        st.session_state.ball_vx = 2.0
        st.session_state.ball_vy = 1.0

with c2:
    if st.button("⏸️ PAUSE", use_container_width=True):
        st.session_state.running = False

with c3:
    if st.button("⚡ FOCUS ⚡", type="primary", use_container_width=True):
        st.session_state.L = min(0.95, st.session_state.L + 0.05)
        st.session_state.E = min(0.95, st.session_state.E + 0.03)
        st.session_state.focus_count += 1

with c4:
    LxE = st.session_state.L * st.session_state.E
    st.metric("L × E", f"{LxE:.2f}")

# Brain metrics
st.write("---")
m1, m2, m3, m4 = st.columns(4)
with m1:
    st.metric("L (Coherence)", f"{st.session_state.L:.2f}")
with m2:
    st.metric("E (Coupling)", f"{st.session_state.E:.2f}")
with m3:
    st.metric("Focus Clicks", st.session_state.focus_count)
with m4:
    if LxE >= 0.85:
        st.success("⚡ CAUSATION!")
    elif LxE >= 0.42:
        st.info("🔗 Connected")
    else:
        st.warning("📊 Building...")

# Game update
if st.session_state.running:
    # Move ball
    st.session_state.ball_x += st.session_state.ball_vx
    st.session_state.ball_y += st.session_state.ball_vy
    
    # Bounce off walls
    if st.session_state.ball_y <= 5 or st.session_state.ball_y >= 95:
        st.session_state.ball_vy *= -1
        st.session_state.ball_y = max(5, min(95, st.session_state.ball_y))
    
    # Player paddle tracks ball (speed based on LxE)
    LxE = st.session_state.L * st.session_state.E
    speed = 2 + int(LxE * 8)
    if st.session_state.player_y < st.session_state.ball_y - 2:
        st.session_state.player_y = min(90, st.session_state.player_y + speed)
    elif st.session_state.player_y > st.session_state.ball_y + 2:
        st.session_state.player_y = max(10, st.session_state.player_y - speed)
    
    # AI paddle
    if st.session_state.ai_y < st.session_state.ball_y - 2:
        st.session_state.ai_y = min(90, st.session_state.ai_y + 2)
    elif st.session_state.ai_y > st.session_state.ball_y + 2:
        st.session_state.ai_y = max(10, st.session_state.ai_y - 2)
    
    # Collisions and scoring
    if st.session_state.ball_x <= 8:
        if abs(st.session_state.ball_y - st.session_state.player_y) < 10:
            st.session_state.ball_vx *= -1.05
            st.session_state.ball_x = 8
        elif st.session_state.ball_x <= 2:
            st.session_state.ai_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.L = max(0.3, st.session_state.L - 0.1)
    
    if st.session_state.ball_x >= 92:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < 10:
            st.session_state.ball_vx *= -1.05
            st.session_state.ball_x = 92
        elif st.session_state.ball_x >= 98:
            st.session_state.player_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.L = min(0.95, st.session_state.L + 0.05)
    
    # Decay
    st.session_state.L = max(0.3, st.session_state.L - 0.003)
    st.session_state.E = max(0.3, st.session_state.E - 0.002)

# Render game
st.write("---")
st.subheader(f"Score: YOU {st.session_state.player_score} - {st.session_state.ai_score} AI")

w, h = 600, 350
py = st.session_state.player_y * h / 100
ay = st.session_state.ai_y * h / 100
bx = st.session_state.ball_x * w / 100
by = st.session_state.ball_y * h / 100

LxE = st.session_state.L * st.session_state.E
pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#00ff88")

svg = f'''
<div style="display:flex;justify-content:center;">
<svg width="{w}" height="{h}" style="background:#1a1a2e;border-radius:10px;border:2px solid #333;">
    <line x1="{w//2}" y1="0" x2="{w//2}" y2="{h}" stroke="#333" stroke-width="2" stroke-dasharray="8,8"/>
    <rect x="15" y="{py-30}" width="10" height="60" fill="{pcolor}" rx="5"/>
    <rect x="{w-25}" y="{ay-30}" width="10" height="60" fill="#ff4466" rx="5"/>
    <circle cx="{bx}" cy="{by}" r="10" fill="white"/>
    <text x="20" y="25" fill="{pcolor}" font-size="14">YOU</text>
    <text x="{w-50}" y="25" fill="#ff4466" font-size="14">AI</text>
</svg>
</div>
'''
st.markdown(svg, unsafe_allow_html=True)

# Auto-refresh when running
if st.session_state.running:
    time.sleep(0.07)
    st.rerun()

# Instructions
with st.expander("How to Play"):
    st.markdown("""
    1. Click **START GAME** to begin
    2. Click **FOCUS** repeatedly to boost your L × E
    3. Higher L × E = faster paddle tracking!
    4. Your paddle automatically follows the ball
    5. Win by scoring 5 points
    
    **The game proves:** Your focus (L × E) directly controls paddle performance!
    """)
