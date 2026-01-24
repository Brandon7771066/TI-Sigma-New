"""
Pure Mind Control Pong - Improved Stability & Controls
"""

import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mind Pong", page_icon="🧠", layout="wide")

st.title("🧠 Pure Mind Control Pong")
st.info("**Control the paddle with your brain or keyboard!** Higher coherence = better performance.")

if 'L' not in st.session_state:
    st.session_state.L = 0.5
    st.session_state.E = 0.5
    st.session_state.player_score = 0
    st.session_state.ai_score = 0
    st.session_state.ball_x = 50
    st.session_state.ball_y = 50
    st.session_state.ball_vx = 2.5
    st.session_state.ball_vy = 1.5
    st.session_state.player_y = 50
    st.session_state.ai_y = 50
    st.session_state.running = False
    st.session_state.thoughts = 0
    st.session_state.manual_move = 0

INSIGHT_WORDS = {'realize', 'understand', 'insight', 'discover', 'connection', 
                 'pattern', 'truth', 'consciousness', 'love', 'amazing', 
                 'beautiful', 'perfect', 'hyperconnection', 'gile', 'tralse', 
                 'myrion', 'coherence', 'universe', 'existence', 'perfection'}

def analyze_thought(text):
    if not text:
        return 0.5, 0.5
    words = text.lower().split()
    insight_count = sum(1 for w in words if w in INSIGHT_WORDS)
    L = min(0.95, 0.4 + insight_count * 0.08 + len(words) * 0.01)
    E = min(0.95, 0.5 + len(words) * 0.02)
    if '!' in text:
        L = min(0.95, L + 0.05)
    return L, E

col1, col2, col3 = st.columns([2, 1, 1])

with col1:
    thought = st.text_input("💭 What are you thinking?", 
                           placeholder="Type insights, feelings, GILE terms...",
                           key="thought_box")
    
    if thought:
        L, E = analyze_thought(thought)
        st.session_state.L = L
        st.session_state.E = E
        st.session_state.thoughts += 1
        if not st.session_state.running:
            st.session_state.running = True

with col2:
    st.write("**Manual Controls:**")
    btn_col1, btn_col2 = st.columns(2)
    with btn_col1:
        if st.button("⬆️ UP", use_container_width=True, key="up_btn"):
            st.session_state.manual_move = -15
            st.session_state.running = True
    with btn_col2:
        if st.button("⬇️ DOWN", use_container_width=True, key="down_btn"):
            st.session_state.manual_move = 15
            st.session_state.running = True

with col3:
    st.write("**Game Control:**")
    if st.button("▶️ START" if not st.session_state.running else "⏸️ PAUSE", 
                 use_container_width=True, type="primary"):
        st.session_state.running = not st.session_state.running
    if st.button("🔄 RESET", use_container_width=True):
        st.session_state.player_score = 0
        st.session_state.ai_score = 0
        st.session_state.ball_x = 50
        st.session_state.ball_y = 50
        st.session_state.ball_vx = 2.5
        st.session_state.ball_vy = 1.5
        st.session_state.player_y = 50
        st.session_state.ai_y = 50
        st.session_state.running = True

LxE = st.session_state.L * st.session_state.E

c1, c2, c3, c4 = st.columns(4)
with c1:
    st.metric("L (Coherence)", f"{st.session_state.L:.2f}")
with c2:
    st.metric("E (Coupling)", f"{st.session_state.E:.2f}")
with c3:
    st.metric("L × E", f"{LxE:.2f}")
with c4:
    if LxE >= 0.85:
        st.success("⚡ CAUSATION!")
    elif LxE >= 0.42:
        st.info("🔗 HYPERCONNECTED")
    else:
        st.warning("📊 Building...")

if st.session_state.running:
    st.session_state.ball_x += st.session_state.ball_vx
    st.session_state.ball_y += st.session_state.ball_vy
    
    if st.session_state.ball_y <= 5:
        st.session_state.ball_y = 5
        st.session_state.ball_vy = abs(st.session_state.ball_vy)
    elif st.session_state.ball_y >= 95:
        st.session_state.ball_y = 95
        st.session_state.ball_vy = -abs(st.session_state.ball_vy)
    
    if st.session_state.manual_move != 0:
        st.session_state.player_y += st.session_state.manual_move
        st.session_state.player_y = max(10, min(90, st.session_state.player_y))
        st.session_state.manual_move = 0
    else:
        target = st.session_state.L * 100
        speed = 2 + int(LxE * 6)
        if st.session_state.player_y < target - 5:
            st.session_state.player_y = min(90, st.session_state.player_y + speed)
        elif st.session_state.player_y > target + 5:
            st.session_state.player_y = max(10, st.session_state.player_y - speed)
    
    ai_speed = 2.5
    if st.session_state.ai_y < st.session_state.ball_y - 5:
        st.session_state.ai_y = min(90, st.session_state.ai_y + ai_speed)
    elif st.session_state.ai_y > st.session_state.ball_y + 5:
        st.session_state.ai_y = max(10, st.session_state.ai_y - ai_speed)
    
    paddle_half = 15
    if st.session_state.ball_x <= 12:
        if abs(st.session_state.ball_y - st.session_state.player_y) < paddle_half:
            st.session_state.ball_vx = abs(st.session_state.ball_vx) * 1.03
            hit_pos = (st.session_state.ball_y - st.session_state.player_y) / paddle_half
            st.session_state.ball_vy += hit_pos * 0.5
        elif st.session_state.ball_x <= 3:
            st.session_state.ai_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.ball_vx = 2.5
            st.session_state.ball_vy = 1.5
    
    if st.session_state.ball_x >= 88:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < 12:
            st.session_state.ball_vx = -abs(st.session_state.ball_vx) * 1.03
            hit_pos = (st.session_state.ball_y - st.session_state.ai_y) / 12
            st.session_state.ball_vy += hit_pos * 0.5
        elif st.session_state.ball_x >= 97:
            st.session_state.player_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
            st.session_state.ball_vx = -2.5
            st.session_state.ball_vy = 1.5
    
    st.session_state.L = max(0.35, st.session_state.L - 0.001)
    st.session_state.E = max(0.35, st.session_state.E - 0.0005)

st.markdown("---")
st.subheader(f"🎮 YOU {st.session_state.player_score} - {st.session_state.ai_score} AI")

W, H = 600, 350
bx = int(st.session_state.ball_x * W / 100)
by = int(st.session_state.ball_y * H / 100)
py = int(st.session_state.player_y * H / 100)
ay = int(st.session_state.ai_y * H / 100)

pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#44ff88")

py_clamped = max(40, min(H-40, py))
ay_clamped = max(35, min(H-35, ay))
bx_clamped = max(12, min(W-12, bx))
by_clamped = max(12, min(H-12, by))

game_html = f'''
<div style="display:flex;justify-content:center;align-items:center;margin:10px 0;">
<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" style="background:linear-gradient(180deg,#0a0a1a,#1a1a2e);border-radius:12px;border:3px solid #555;">
  <rect x="0" y="0" width="{W}" height="{H}" fill="#0a0a1a"/>
  <line x1="{W//2}" y1="0" x2="{W//2}" y2="{H}" stroke="#333" stroke-width="3" stroke-dasharray="10,8"/>
  <circle cx="{W//2}" cy="{H//2}" r="40" fill="none" stroke="#333" stroke-width="2"/>
  <rect x="20" y="{py_clamped-40}" width="14" height="80" fill="{pcolor}" rx="7" style="filter:drop-shadow(0 0 12px {pcolor});"/>
  <rect x="{W-34}" y="{ay_clamped-35}" width="14" height="70" fill="#ff5566" rx="7" style="filter:drop-shadow(0 0 12px #ff5566);"/>
  <circle cx="{bx_clamped}" cy="{by_clamped}" r="12" fill="white" style="filter:drop-shadow(0 0 15px white);"/>
  <text x="25" y="30" fill="{pcolor}" font-size="16" font-weight="bold" font-family="Arial,sans-serif">YOU</text>
  <text x="{W-55}" y="30" fill="#ff5566" font-size="16" font-weight="bold" font-family="Arial,sans-serif">AI</text>
  <text x="{W//2-50}" y="35" fill="white" font-size="28" font-weight="bold" font-family="Arial,sans-serif">{st.session_state.player_score}</text>
  <text x="{W//2+35}" y="35" fill="white" font-size="28" font-weight="bold" font-family="Arial,sans-serif">{st.session_state.ai_score}</text>
  <text x="{W//2-8}" y="35" fill="#666" font-size="20" font-family="Arial,sans-serif">-</text>
</svg>
</div>
'''
components.html(game_html, height=380)

speed_label = 'PERFECT' if LxE >= 0.85 else 'GOOD' if LxE >= 0.42 else 'SLOW'
st.caption(f"Thoughts analyzed: {st.session_state.thoughts} | Paddle speed: {speed_label} | Use UP/DOWN buttons or type insights!")

with st.expander("💡 How to Play"):
    st.markdown("""
    **Two Ways to Control Your Paddle:**
    
    1. **Manual Control**: Click the ⬆️ UP and ⬇️ DOWN buttons
    2. **Mind Control**: Type insights in the text box - your words affect paddle position!
    
    **Boost your coherence (L) with:**
    - Insight words: *realize, understand, pattern, truth, connection*
    - Positive emotions: *love, amazing, beautiful, perfect*
    - GILE terms: *consciousness, hyperconnection, gile, tralse, myrion*
    - Longer, more thoughtful messages
    - Exclamation marks for emphasis!
    
    **Tips:**
    - Higher L × E = faster paddle speed
    - The paddle follows your L value (higher L = paddle moves up)
    - Type continuously to maintain high coherence!
    """)

if st.session_state.running:
    import time
    time.sleep(0.08)
    st.rerun()
