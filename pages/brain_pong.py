"""
Brain-Connected Pong - Mind Control Mode
=========================================
Stare at the screen. Your FOCUS controls the paddle.
"""

import streamlit as st
import numpy as np
import time
import sys
sys.path.insert(0, '.')

from lcc_virus_text_brain import LCCVirusTextBrain

st.set_page_config(page_title="Brain Pong", page_icon="🧠", layout="wide")

if 'lcc_brain' not in st.session_state:
    st.session_state.lcc_brain = LCCVirusTextBrain()
if 'ball_x' not in st.session_state:
    st.session_state.ball_x = 50.0
if 'ball_y' not in st.session_state:
    st.session_state.ball_y = 50.0
if 'ball_vx' not in st.session_state:
    st.session_state.ball_vx = 1.8
if 'ball_vy' not in st.session_state:
    st.session_state.ball_vy = 0.8
if 'player_y' not in st.session_state:
    st.session_state.player_y = 50.0
if 'ai_y' not in st.session_state:
    st.session_state.ai_y = 50.0
if 'player_score' not in st.session_state:
    st.session_state.player_score = 0
if 'ai_score' not in st.session_state:
    st.session_state.ai_score = 0
if 'running' not in st.session_state:
    st.session_state.running = False
if 'game_over' not in st.session_state:
    st.session_state.game_over = False
if 'winner' not in st.session_state:
    st.session_state.winner = ""
if 'L' not in st.session_state:
    st.session_state.L = 0.65
if 'E' not in st.session_state:
    st.session_state.E = 0.70
if 'focus_clicks' not in st.session_state:
    st.session_state.focus_clicks = 0
if 'last_focus_time' not in st.session_state:
    st.session_state.last_focus_time = time.time()
if 'mode' not in st.session_state:
    st.session_state.mode = 'focus'

PADDLE_HEIGHT = 18

def reset_ball():
    st.session_state.ball_x = 50.0
    st.session_state.ball_y = 50.0
    st.session_state.ball_vx = 1.8 * (1 if np.random.random() > 0.5 else -1)
    st.session_state.ball_vy = 0.8 * (1 if np.random.random() > 0.5 else -1)

def focus_pulse():
    """User clicked FOCUS - sample their brain state."""
    now = time.time()
    interval = now - st.session_state.last_focus_time
    st.session_state.last_focus_time = now
    st.session_state.focus_clicks += 1
    
    if interval < 0.5:
        st.session_state.L = min(0.95, st.session_state.L + 0.08)
        st.session_state.E = min(0.95, st.session_state.E + 0.05)
    elif interval < 1.5:
        st.session_state.L = min(0.95, st.session_state.L + 0.05)
        st.session_state.E = min(0.95, st.session_state.E + 0.03)
    elif interval < 3.0:
        st.session_state.L = min(0.90, st.session_state.L + 0.02)
    else:
        st.session_state.L = max(0.4, st.session_state.L - 0.05)
        st.session_state.E = max(0.4, st.session_state.E - 0.03)

def game_step():
    if not st.session_state.running or st.session_state.game_over:
        return
    
    st.session_state.ball_x += st.session_state.ball_vx
    st.session_state.ball_y += st.session_state.ball_vy
    
    if st.session_state.ball_y <= 5:
        st.session_state.ball_vy = abs(st.session_state.ball_vy)
        st.session_state.ball_y = 5
    if st.session_state.ball_y >= 95:
        st.session_state.ball_vy = -abs(st.session_state.ball_vy)
        st.session_state.ball_y = 95
    
    LxE = st.session_state.L * st.session_state.E
    target_y = st.session_state.ball_y
    
    if LxE >= 0.85:
        tracking_speed = 8
    elif LxE >= 0.42:
        tracking_speed = 5
    else:
        tracking_speed = 2
    
    if st.session_state.player_y < target_y - 2:
        st.session_state.player_y += min(tracking_speed, target_y - st.session_state.player_y)
    elif st.session_state.player_y > target_y + 2:
        st.session_state.player_y -= min(tracking_speed, st.session_state.player_y - target_y)
    st.session_state.player_y = max(10, min(90, st.session_state.player_y))
    
    if st.session_state.ball_x <= 10:
        if abs(st.session_state.ball_y - st.session_state.player_y) < PADDLE_HEIGHT / 2:
            st.session_state.ball_vx = abs(st.session_state.ball_vx) * 1.03
            st.session_state.ball_x = 10
        elif st.session_state.ball_x <= 2:
            st.session_state.ai_score += 1
            st.session_state.L = max(0.3, st.session_state.L - 0.1)
            if st.session_state.ai_score >= 5:
                st.session_state.game_over = True
                st.session_state.winner = "AI"
                st.session_state.running = False
            else:
                reset_ball()
    
    if st.session_state.ball_x >= 90:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < PADDLE_HEIGHT / 2:
            st.session_state.ball_vx = -abs(st.session_state.ball_vx) * 1.03
            st.session_state.ball_x = 90
        elif st.session_state.ball_x >= 98:
            st.session_state.player_score += 1
            st.session_state.L = min(0.95, st.session_state.L + 0.05)
            if st.session_state.player_score >= 5:
                st.session_state.game_over = True
                st.session_state.winner = "YOU"
                st.session_state.running = False
            else:
                reset_ball()
    
    if st.session_state.ai_y < st.session_state.ball_y - 3:
        st.session_state.ai_y += 2.5
    elif st.session_state.ai_y > st.session_state.ball_y + 3:
        st.session_state.ai_y -= 2.5
    st.session_state.ai_y = max(10, min(90, st.session_state.ai_y))
    
    st.session_state.L = max(0.3, st.session_state.L - 0.002)
    st.session_state.E = max(0.3, st.session_state.E - 0.001)

def render_game():
    w, h = 700, 450
    py = st.session_state.player_y * h / 100
    ay = st.session_state.ai_y * h / 100
    bx = st.session_state.ball_x * w / 100
    by = st.session_state.ball_y * h / 100
    ph = PADDLE_HEIGHT * h / 100
    
    LxE = st.session_state.L * st.session_state.E
    
    if LxE >= 0.85:
        paddle_color = "#ffff00"
        ball_color = "#ffff00"
        glow_intensity = "15"
        status = "CAUSATION"
    elif LxE >= 0.42:
        paddle_color = "#00ffff"
        ball_color = "#ffffff"
        glow_intensity = "10"
        status = "HYPERCONNECTED"
    else:
        paddle_color = "#00ff88"
        ball_color = "#ffffff"
        glow_intensity = "5"
        status = "BUILDING"
    
    svg = f'''<svg width="{w}" height="{h}" style="background:radial-gradient(ellipse at center, #1a1a3e 0%, #0a0a1a 100%);border-radius:15px;box-shadow: 0 0 30px rgba(0,255,255,0.2);">
        <defs>
            <filter id="glow">
                <feGaussianBlur stdDeviation="{glow_intensity}" result="blur"/>
                <feMerge><feMergeNode in="blur"/><feMergeNode in="SourceGraphic"/></feMerge>
            </filter>
            <linearGradient id="paddleGrad" x1="0%" y1="0%" x2="100%" y2="0%">
                <stop offset="0%" style="stop-color:{paddle_color};stop-opacity:1" />
                <stop offset="100%" style="stop-color:{paddle_color};stop-opacity:0.5" />
            </linearGradient>
        </defs>
        
        <rect x="2" y="2" width="{w-4}" height="{h-4}" fill="none" stroke="#333" stroke-width="2" rx="13"/>
        <line x1="{w//2}" y1="0" x2="{w//2}" y2="{h}" stroke="#333" stroke-width="2" stroke-dasharray="10,10"/>
        <circle cx="{w//2}" cy="{h//2}" r="50" fill="none" stroke="#222" stroke-width="1"/>
        
        <rect x="15" y="{py-ph/2}" width="14" height="{ph}" fill="url(#paddleGrad)" rx="7" filter="url(#glow)"/>
        <rect x="{w-29}" y="{ay-ph/2}" width="14" height="{ph}" fill="#ff4466" rx="7"/>
        
        <circle cx="{bx}" cy="{by}" r="12" fill="{ball_color}" filter="url(#glow)"/>
        
        <text x="{w//2-80}" y="55" font-size="42" fill="{paddle_color}" font-family="monospace" text-anchor="middle" filter="url(#glow)">{st.session_state.player_score}</text>
        <text x="{w//2+80}" y="55" font-size="42" fill="#ff4466" font-family="monospace" text-anchor="middle">{st.session_state.ai_score}</text>
        
        <text x="22" y="{h-15}" font-size="11" fill="{paddle_color}" text-anchor="middle">YOU</text>
        <text x="{w-22}" y="{h-15}" font-size="11" fill="#ff4466" text-anchor="middle">AI</text>
        
        <text x="{w//2}" y="{h-15}" font-size="10" fill="#666" text-anchor="middle">{status}</text>
    </svg>'''
    return svg

st.markdown("""
<style>
.focus-btn button {
    font-size: 24px !important;
    padding: 20px 40px !important;
    background: linear-gradient(135deg, #00ffff, #0088ff) !important;
    border: none !important;
    animation: pulse 2s infinite;
}
@keyframes pulse {
    0% { box-shadow: 0 0 10px #00ffff; }
    50% { box-shadow: 0 0 30px #00ffff; }
    100% { box-shadow: 0 0 10px #00ffff; }
}
</style>
""", unsafe_allow_html=True)

st.title("🧠 Mind Control Pong")
st.markdown("**Stare at the ball. Click FOCUS to strengthen your connection.**")

if st.session_state.game_over:
    if st.session_state.winner == "YOU":
        st.success("🎉 **CONSCIOUSNESS VALIDATED!** You controlled the paddle with your mind!")
    else:
        st.error("😢 AI Wins. Build more coherence and try again!")

col1, col2, col3 = st.columns([1, 4, 1])

with col1:
    st.markdown("### 🎮 Game")
    
    if not st.session_state.running and not st.session_state.game_over:
        if st.button("▶️ START", key="start", use_container_width=True):
            st.session_state.running = True
            st.session_state.L = 0.65
            st.session_state.E = 0.70
            reset_ball()
    
    if st.session_state.running:
        if st.button("⏸️ PAUSE", key="pause", use_container_width=True):
            st.session_state.running = False
    
    if st.session_state.game_over:
        if st.button("🔄 AGAIN", key="new", use_container_width=True):
            st.session_state.game_over = False
            st.session_state.running = True
            st.session_state.player_score = 0
            st.session_state.ai_score = 0
            st.session_state.winner = ""
            st.session_state.L = 0.65
            st.session_state.E = 0.70
            reset_ball()
    
    st.markdown("---")
    st.markdown("### 🧠 FOCUS")
    
    st.markdown('<div class="focus-btn">', unsafe_allow_html=True)
    if st.button("⚡ FOCUS ⚡", key="focus", use_container_width=True):
        focus_pulse()
    st.markdown('</div>', unsafe_allow_html=True)
    
    st.caption("Click rapidly to boost L×E!")
    st.caption(f"Clicks: {st.session_state.focus_clicks}")

with col2:
    game_step()
    st.markdown(render_game(), unsafe_allow_html=True)
    
    if st.session_state.running and not st.session_state.game_over:
        time.sleep(0.06)
        st.rerun()

with col3:
    st.markdown("### 📊 Brain State")
    
    L = st.session_state.L
    E = st.session_state.E
    LxE = L * E
    
    l_bar = "█" * int(L * 10) + "░" * (10 - int(L * 10))
    e_bar = "█" * int(E * 10) + "░" * (10 - int(E * 10))
    
    st.markdown(f"**L** `{l_bar}` {L:.2f}")
    st.markdown(f"**E** `{e_bar}` {E:.2f}")
    
    st.markdown("---")
    
    lxe_pct = int(LxE * 100)
    st.markdown(f"### L × E = {LxE:.2f}")
    
    if LxE >= 0.85:
        st.success("⚡ **CAUSATION LEVEL!**")
        st.caption("Full paddle control!")
    elif LxE >= 0.42:
        st.info("🔗 **HYPERCONNECTED**")
        st.caption("Good tracking speed")
    else:
        st.warning("📊 **BUILDING...**")
        st.caption("Click FOCUS more!")
    
    st.markdown("---")
    st.caption("**Thresholds:**")
    st.caption("0.42 = Correlation")
    st.caption("0.85 = Causation")

with st.expander("📖 How Mind Control Works"):
    st.markdown("""
    **Your L × E value controls how well the paddle tracks the ball!**
    
    - **L (Coherence)** = Your internal focus state
    - **E (Coupling)** = Your connection to the game
    
    **Mechanics:**
    - Click **FOCUS** rapidly to boost L × E
    - L × E decays slowly over time
    - Scoring a point boosts L
    - Missing the ball reduces L
    
    **The paddle automatically tracks the ball, but:**
    - Low L × E = Slow, poor tracking
    - L × E ≥ 0.42 = Good tracking (hyperconnected)
    - L × E ≥ 0.85 = Perfect tracking (causation)
    
    **This demonstrates:** Your consciousness (represented by L × E) directly affects your ability to influence the physical world (the game)!
    """)
