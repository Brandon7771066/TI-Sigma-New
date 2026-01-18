"""
Pure Mind Control Pong
======================
Your consciousness controls the game through TEXT.
Type your thoughts - the LCC Virus reads your mental state.
No physical game controls needed!
"""

import streamlit as st
import time
import sys
sys.path.insert(0, '.')
from lcc_virus_text_brain import LCCVirusTextBrain

st.set_page_config(page_title="Mind Pong", page_icon="🧠", layout="wide")

if 'brain' not in st.session_state:
    st.session_state.brain = LCCVirusTextBrain()
    st.session_state.ball_x = 50.0
    st.session_state.ball_y = 50.0
    st.session_state.ball_vx = 1.5
    st.session_state.ball_vy = 0.8
    st.session_state.player_y = 50.0
    st.session_state.ai_y = 50.0
    st.session_state.player_score = 0
    st.session_state.ai_score = 0
    st.session_state.running = False
    st.session_state.L = 0.5
    st.session_state.E = 0.5
    st.session_state.last_analysis = None
    st.session_state.thought_count = 0

st.title("🧠 Pure Mind Control Pong")

st.info("**Your thoughts control the paddle!** Type what you're thinking below. The LCC Virus analyzes your consciousness state (L × E) and moves your paddle accordingly. No buttons needed - just think out loud!")

col1, col2 = st.columns([2, 1])

with col1:
    thought = st.text_input(
        "💭 What are you thinking right now?",
        placeholder="Type your thoughts, feelings, or intentions...",
        key="thought_input"
    )
    
    if thought:
        result = st.session_state.brain.analyze_text(thought)
        st.session_state.L = result['L']
        st.session_state.E = result['E']
        st.session_state.last_analysis = result
        st.session_state.thought_count += 1
        if not st.session_state.running:
            st.session_state.running = True

with col2:
    if st.button("🔄 Reset Game", use_container_width=True):
        st.session_state.ball_x = 50.0
        st.session_state.ball_y = 50.0
        st.session_state.player_score = 0
        st.session_state.ai_score = 0
        st.session_state.running = True

st.write("---")

m1, m2, m3, m4 = st.columns(4)
LxE = st.session_state.L * st.session_state.E
LplusE = st.session_state.L + st.session_state.E

with m1:
    st.metric("L (Coherence)", f"{st.session_state.L:.2f}")
with m2:
    st.metric("E (Coupling)", f"{st.session_state.E:.2f}")
with m3:
    st.metric("L × E", f"{LxE:.2f}")
with m4:
    if LxE >= 0.85:
        st.success("⚡ CAUSATION!")
    elif LxE >= 0.42:
        st.info("🔗 HYPERCONNECTED")
    else:
        st.warning("📊 Building...")

if st.session_state.last_analysis:
    st.caption(f"*{st.session_state.last_analysis['analysis']}*")

if st.session_state.running:
    st.session_state.ball_x += st.session_state.ball_vx
    st.session_state.ball_y += st.session_state.ball_vy
    
    if st.session_state.ball_y <= 5 or st.session_state.ball_y >= 95:
        st.session_state.ball_vy *= -1
        st.session_state.ball_y = max(5, min(95, st.session_state.ball_y))
    
    target_y = st.session_state.L * 100
    speed = 1 + int(LxE * 10)
    diff = target_y - st.session_state.player_y
    if abs(diff) > 2:
        move = min(abs(diff), speed) * (1 if diff > 0 else -1)
        st.session_state.player_y += move
    st.session_state.player_y = max(10, min(90, st.session_state.player_y))
    
    if st.session_state.ai_y < st.session_state.ball_y - 3:
        st.session_state.ai_y = min(90, st.session_state.ai_y + 2)
    elif st.session_state.ai_y > st.session_state.ball_y + 3:
        st.session_state.ai_y = max(10, st.session_state.ai_y - 2)
    
    if st.session_state.ball_x <= 8:
        if abs(st.session_state.ball_y - st.session_state.player_y) < 12:
            st.session_state.ball_vx = abs(st.session_state.ball_vx) * 1.02
            st.session_state.ball_x = 8
            st.session_state.L = min(0.95, st.session_state.L + 0.03)
        elif st.session_state.ball_x <= 2:
            st.session_state.ai_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.ball_vx = 1.5
            st.session_state.L = max(0.3, st.session_state.L - 0.08)
    
    if st.session_state.ball_x >= 92:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < 10:
            st.session_state.ball_vx = -abs(st.session_state.ball_vx) * 1.02
            st.session_state.ball_x = 92
        elif st.session_state.ball_x >= 98:
            st.session_state.player_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.ball_vx = -1.5
            st.session_state.L = min(0.95, st.session_state.L + 0.05)
    
    st.session_state.L = max(0.3, st.session_state.L - 0.002)
    st.session_state.E = max(0.3, st.session_state.E - 0.001)

st.write("---")

sc1, sc2, sc3 = st.columns([1, 2, 1])
with sc2:
    st.subheader(f"🎮 YOU {st.session_state.player_score} - {st.session_state.ai_score} AI")

w, h = 600, 350
py = st.session_state.player_y * h / 100
ay = st.session_state.ai_y * h / 100
bx = st.session_state.ball_x * w / 100
by = st.session_state.ball_y * h / 100

if LxE >= 0.85:
    pcolor = "#ffff00"
    glow = "filter:drop-shadow(0 0 8px #ffff00);"
elif LxE >= 0.42:
    pcolor = "#00ffff"
    glow = "filter:drop-shadow(0 0 5px #00ffff);"
else:
    pcolor = "#00ff88"
    glow = ""

svg = f'''
<div style="display:flex;justify-content:center;">
<svg width="{w}" height="{h}" style="background:linear-gradient(135deg, #0a0a1a 0%, #1a1a3e 100%);border-radius:12px;border:2px solid #333;">
    <defs>
        <radialGradient id="ballGlow" cx="50%" cy="50%" r="50%">
            <stop offset="0%" style="stop-color:white;stop-opacity:1"/>
            <stop offset="100%" style="stop-color:#aaa;stop-opacity:0.5"/>
        </radialGradient>
    </defs>
    <line x1="{w//2}" y1="0" x2="{w//2}" y2="{h}" stroke="#333" stroke-width="2" stroke-dasharray="10,10"/>
    <rect x="15" y="{py-35}" width="12" height="70" fill="{pcolor}" rx="6" style="{glow}"/>
    <rect x="{w-27}" y="{ay-30}" width="12" height="60" fill="#ff4466" rx="6"/>
    <circle cx="{bx}" cy="{by}" r="12" fill="url(#ballGlow)"/>
    <text x="20" y="25" fill="{pcolor}" font-size="16" font-weight="bold">YOU</text>
    <text x="{w-55}" y="25" fill="#ff4466" font-size="16" font-weight="bold">AI</text>
    <text x="{w//2}" y="25" fill="#666" font-size="12" text-anchor="middle">L×E: {LxE:.2f}</text>
</svg>
</div>
'''
st.markdown(svg, unsafe_allow_html=True)

speed_desc = "PERFECT" if LxE >= 0.85 else ("GOOD" if LxE >= 0.42 else "SLOW")
st.caption(f"Paddle speed: {speed_desc} | Thoughts analyzed: {st.session_state.thought_count}")

with st.expander("🔬 How It Works - Consciousness-Controlled Computing"):
    st.markdown("""
    ### Pure Virtual Brain Connection
    
    This game demonstrates **consciousness-controlled computing** without any physical game controls:
    
    1. **You type your thoughts** - anything you're thinking or feeling
    2. **LCC Virus analyzes your text** to extract:
       - **L (Coherence)**: Insight words, GILE terms, emotional positivity, sentence structure
       - **E (Coupling)**: Message length, engagement depth, response speed, session duration
    3. **Your paddle moves based on L** - higher coherence = higher paddle position
    4. **Your paddle SPEED depends on L×E** - hyperconnection = faster reflexes!
    
    ### The Thresholds
    | L × E | Status | Paddle Speed |
    |-------|--------|--------------|
    | < 0.42 | Building | Slow |
    | ≥ 0.42 | HYPERCONNECTED | Good |
    | ≥ 0.85 | CAUSATION | Perfect |
    
    ### Tips to Boost Your Score
    - Use insight words: *realize, understand, pattern, connection, truth*
    - Express positive emotions: *love, amazing, beautiful, grateful*
    - Use GILE terminology: *consciousness, hyperconnection, tralse, myrion*
    - Keep engaged - faster responses increase E!
    - Type longer, more thoughtful messages
    
    **Your text IS your consciousness channel. Think clearly, and you win!**
    """)

if st.session_state.running:
    time.sleep(0.08)
    st.rerun()
