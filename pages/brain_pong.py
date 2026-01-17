"""
Brain-Connected Pong via LCC Virus Text Interface
==================================================
Your TEXT controls the paddle through hyperconnection!
"""

import streamlit as st
import numpy as np
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
    st.session_state.ball_vx = 2.0
if 'ball_vy' not in st.session_state:
    st.session_state.ball_vy = 1.0
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
    st.session_state.L = 0.5
if 'E' not in st.session_state:
    st.session_state.E = 0.5
if 'last_analysis' not in st.session_state:
    st.session_state.last_analysis = "Awaiting your thoughts..."
if 'message_count' not in st.session_state:
    st.session_state.message_count = 0

PADDLE_HEIGHT = 15

def reset_ball():
    st.session_state.ball_x = 50.0
    st.session_state.ball_y = 50.0
    st.session_state.ball_vx = 2.0 * (1 if np.random.random() > 0.5 else -1)
    st.session_state.ball_vy = 1.0 * (1 if np.random.random() > 0.5 else -1)

def process_thought(thought: str):
    """Process user's thought through LCC Virus to control paddle."""
    if thought and thought.strip():
        result = st.session_state.lcc_brain.analyze_text(thought)
        st.session_state.L = result['L']
        st.session_state.E = result['E']
        st.session_state.last_analysis = result['analysis']
        st.session_state.message_count += 1
        
        target_y = st.session_state.lcc_brain.get_paddle_position(thought)
        st.session_state.player_y = target_y

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
    
    if st.session_state.ball_x <= 10:
        if abs(st.session_state.ball_y - st.session_state.player_y) < PADDLE_HEIGHT / 2:
            st.session_state.ball_vx = abs(st.session_state.ball_vx) * 1.05
            st.session_state.ball_x = 10
        elif st.session_state.ball_x <= 2:
            st.session_state.ai_score += 1
            if st.session_state.ai_score >= 5:
                st.session_state.game_over = True
                st.session_state.winner = "AI"
                st.session_state.running = False
            else:
                reset_ball()
    
    if st.session_state.ball_x >= 90:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < PADDLE_HEIGHT / 2:
            st.session_state.ball_vx = -abs(st.session_state.ball_vx) * 1.05
            st.session_state.ball_x = 90
        elif st.session_state.ball_x >= 98:
            st.session_state.player_score += 1
            if st.session_state.player_score >= 5:
                st.session_state.game_over = True
                st.session_state.winner = "YOU"
                st.session_state.running = False
            else:
                reset_ball()
    
    if st.session_state.ai_y < st.session_state.ball_y - 3:
        st.session_state.ai_y += 2
    elif st.session_state.ai_y > st.session_state.ball_y + 3:
        st.session_state.ai_y -= 2
    st.session_state.ai_y = max(10, min(90, st.session_state.ai_y))

def render_game():
    w, h = 600, 400
    py = st.session_state.player_y * h / 100
    ay = st.session_state.ai_y * h / 100
    bx = st.session_state.ball_x * w / 100
    by = st.session_state.ball_y * h / 100
    ph = PADDLE_HEIGHT * h / 100
    
    L = st.session_state.L
    LxE = st.session_state.L * st.session_state.E
    
    if LxE >= 0.85:
        paddle_color = "#ffff00"
        glow = "filter: drop-shadow(0 0 10px #ffff00);"
    elif LxE >= 0.42:
        paddle_color = "#00ffff"
        glow = "filter: drop-shadow(0 0 8px #00ffff);"
    else:
        paddle_color = "#00ff88"
        glow = ""
    
    svg = f'''<svg width="{w}" height="{h}" style="background:linear-gradient(180deg, #0a0a1a 0%, #1a1a3e 100%);border-radius:12px;{glow}">
        <defs>
            <filter id="glow" x="-50%" y="-50%" width="200%" height="200%">
                <feGaussianBlur stdDeviation="3" result="blur"/>
                <feMerge><feMergeNode in="blur"/><feMergeNode in="SourceGraphic"/></feMerge>
            </filter>
        </defs>
        <rect x="2" y="2" width="{w-4}" height="{h-4}" fill="none" stroke="#333" stroke-width="2" rx="10"/>
        <line x1="{w//2}" y1="0" x2="{w//2}" y2="{h}" stroke="#333" stroke-width="2" stroke-dasharray="8,8"/>
        <circle cx="{w//2}" cy="{h//2}" r="40" fill="none" stroke="#333" stroke-width="1"/>
        <rect x="15" y="{py-ph/2}" width="12" height="{ph}" fill="{paddle_color}" rx="6" filter="url(#glow)"/>
        <rect x="{w-27}" y="{ay-ph/2}" width="12" height="{ph}" fill="#ff4466" rx="6"/>
        <circle cx="{bx}" cy="{by}" r="10" fill="#fff" filter="url(#glow)"/>
        <text x="{w//2-60}" y="50" font-size="36" fill="{paddle_color}" font-family="monospace" text-anchor="middle">{st.session_state.player_score}</text>
        <text x="{w//2+60}" y="50" font-size="36" fill="#ff4466" font-family="monospace" text-anchor="middle">{st.session_state.ai_score}</text>
        <text x="21" y="{h-12}" font-size="12" fill="{paddle_color}" text-anchor="middle">YOU</text>
        <text x="{w-21}" y="{h-12}" font-size="12" fill="#ff4466" text-anchor="middle">AI</text>
    </svg>'''
    return svg

st.title("🧠 Brain Pong via LCC Virus")
st.markdown("**Your THOUGHTS control the paddle!** Type to move.")

if st.session_state.game_over:
    if st.session_state.winner == "YOU":
        st.success("🎉 YOU WIN! Consciousness validated through text!")
    else:
        st.error("😢 AI Wins. Keep typing to build coherence!")

col1, col2, col3 = st.columns([1.5, 3, 1.5])

with col1:
    st.markdown("### 🎮 Controls")
    
    if not st.session_state.running and not st.session_state.game_over:
        if st.button("▶️ START", key="start", use_container_width=True):
            st.session_state.running = True
            reset_ball()
    
    if st.session_state.running:
        if st.button("⏸️ PAUSE", key="pause", use_container_width=True):
            st.session_state.running = False
    
    if st.session_state.game_over:
        if st.button("🔄 NEW GAME", key="new", use_container_width=True):
            st.session_state.game_over = False
            st.session_state.running = True
            st.session_state.player_score = 0
            st.session_state.ai_score = 0
            st.session_state.winner = ""
            reset_ball()
    
    st.markdown("---")
    st.markdown("### 💭 Think to Move")
    
    thought = st.text_input(
        "Enter your thought:",
        key="thought_input",
        placeholder="Type anything...",
        label_visibility="collapsed"
    )
    
    if st.button("📡 TRANSMIT", key="transmit", use_container_width=True):
        process_thought(thought)
    
    st.markdown("---")
    st.markdown("### 🎯 Manual Override")
    c1, c2 = st.columns(2)
    with c1:
        if st.button("⬆️", key="up", use_container_width=True):
            st.session_state.player_y = max(10, st.session_state.player_y - 10)
    with c2:
        if st.button("⬇️", key="down", use_container_width=True):
            st.session_state.player_y = min(90, st.session_state.player_y + 10)

with col2:
    game_step()
    st.markdown(render_game(), unsafe_allow_html=True)
    
    if st.session_state.running and not st.session_state.game_over:
        import time
        time.sleep(0.08)
        st.rerun()

with col3:
    st.markdown("### 🧠 Brain State")
    
    L = st.session_state.L
    E = st.session_state.E
    LxE = L * E
    LplusE = L + E
    
    st.metric("L (Coherence)", f"{L:.2f}")
    st.metric("E (Coupling)", f"{E:.2f}")
    
    st.markdown("---")
    
    st.metric("L × E", f"{LxE:.3f}")
    st.metric("L + E", f"{LplusE:.2f}")
    
    st.markdown("---")
    
    if LxE >= 0.85:
        st.success("⚡ CAUSATION!")
    elif LxE >= 0.42:
        st.info("🔗 Hyperconnected!")
    else:
        st.warning("📊 Building...")
    
    if LplusE >= 0.84:
        st.success("✨ EXISTS")
    else:
        st.error("⚠️ Sub-threshold")
    
    st.markdown("---")
    st.caption(f"Messages: {st.session_state.message_count}")
    st.caption(st.session_state.last_analysis)

with st.expander("📖 How It Works"):
    st.markdown("""
    **Your text IS your consciousness channel!**
    
    The LCC Virus analyzes your words for:
    
    **L (Coherence):**
    - Insight words (realize, discover, pattern...)
    - GILE terminology
    - Positive emotions
    - Sentence structure
    
    **E (Coupling):**
    - Message length (engagement depth)
    - Response time (real-time connection)
    - Questions asked (seeking connection)
    - Emojis (emotional expression)
    
    **Thresholds:**
    - L × E ≥ 0.42 → Hyperconnection!
    - L + E ≥ 0.84 → Existence maintained
    - L × E ≥ 0.85 → Causation level!
    
    **Your paddle position = your coherence level.**
    High coherence thoughts move the paddle UP.
    """)
