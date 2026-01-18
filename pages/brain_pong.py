"""
Pure Mind Control Pong - Simple & Robust
"""

import streamlit as st

st.set_page_config(page_title="Mind Pong", page_icon="🧠", layout="wide")

st.title("🧠 Pure Mind Control Pong")
st.info("**Type your thoughts below to control the paddle!** Higher coherence = better performance.")

if 'L' not in st.session_state:
    st.session_state.L = 0.5
    st.session_state.E = 0.5
    st.session_state.player_score = 0
    st.session_state.ai_score = 0
    st.session_state.ball_x = 50
    st.session_state.ball_y = 50
    st.session_state.ball_vx = 2
    st.session_state.ball_vy = 1
    st.session_state.player_y = 50
    st.session_state.ai_y = 50
    st.session_state.running = False
    st.session_state.thoughts = 0

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

col1, col2 = st.columns([3, 1])

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
    if st.button("🔄 Reset", use_container_width=True):
        st.session_state.player_score = 0
        st.session_state.ai_score = 0
        st.session_state.ball_x = 50
        st.session_state.ball_y = 50
        st.session_state.running = True

st.markdown("---")

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
    
    if st.session_state.ball_y <= 5 or st.session_state.ball_y >= 95:
        st.session_state.ball_vy *= -1
    
    target = st.session_state.L * 100
    speed = 1 + int(LxE * 8)
    if st.session_state.player_y < target - 3:
        st.session_state.player_y = min(90, st.session_state.player_y + speed)
    elif st.session_state.player_y > target + 3:
        st.session_state.player_y = max(10, st.session_state.player_y - speed)
    
    if st.session_state.ai_y < st.session_state.ball_y - 3:
        st.session_state.ai_y = min(90, st.session_state.ai_y + 2)
    elif st.session_state.ai_y > st.session_state.ball_y + 3:
        st.session_state.ai_y = max(10, st.session_state.ai_y - 2)
    
    if st.session_state.ball_x <= 10:
        if abs(st.session_state.ball_y - st.session_state.player_y) < 15:
            st.session_state.ball_vx = abs(st.session_state.ball_vx) * 1.02
        elif st.session_state.ball_x <= 2:
            st.session_state.ai_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
    
    if st.session_state.ball_x >= 90:
        if abs(st.session_state.ball_y - st.session_state.ai_y) < 12:
            st.session_state.ball_vx = -abs(st.session_state.ball_vx) * 1.02
        elif st.session_state.ball_x >= 98:
            st.session_state.player_score += 1
            st.session_state.ball_x = 50
            st.session_state.ball_y = 50
    
    st.session_state.L = max(0.35, st.session_state.L - 0.002)
    st.session_state.E = max(0.35, st.session_state.E - 0.001)

st.markdown("---")
st.subheader(f"🎮 YOU {st.session_state.player_score} - {st.session_state.ai_score} AI")

W, H = 500, 300
bx = int(st.session_state.ball_x * W / 100)
by = int(st.session_state.ball_y * H / 100)
py = int(st.session_state.player_y * H / 100)
ay = int(st.session_state.ai_y * H / 100)

pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#44ff88")

py_clamped = max(30, min(H-30, py))
ay_clamped = max(25, min(H-25, ay))
bx_clamped = max(10, min(W-10, bx))
by_clamped = max(10, min(H-10, by))

game_html = f'''
<div style="display:flex;justify-content:center;align-items:center;margin:20px 0;min-height:320px;">
<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" style="background:linear-gradient(180deg,#0a0a1a,#1a1a2e);border-radius:12px;border:2px solid #444;box-shadow:0 4px 20px rgba(0,0,0,0.5);">
  <!-- Court lines -->
  <line x1="{W//2}" y1="0" x2="{W//2}" y2="{H}" stroke="#333" stroke-width="2" stroke-dasharray="8,8"/>
  <rect x="0" y="0" width="{W}" height="4" fill="#222"/>
  <rect x="0" y="{H-4}" width="{W}" height="4" fill="#222"/>
  
  <!-- Player paddle (left) -->
  <rect x="15" y="{py_clamped-30}" width="12" height="60" fill="{pcolor}" rx="6" style="filter:drop-shadow(0 0 8px {pcolor});"/>
  
  <!-- AI paddle (right) -->
  <rect x="{W-27}" y="{ay_clamped-25}" width="12" height="50" fill="#ff5566" rx="6" style="filter:drop-shadow(0 0 8px #ff5566);"/>
  
  <!-- Ball with glow -->
  <circle cx="{bx_clamped}" cy="{by_clamped}" r="10" fill="white" style="filter:drop-shadow(0 0 12px white);"/>
  
  <!-- Labels -->
  <text x="20" y="25" fill="{pcolor}" font-size="14" font-weight="bold" font-family="Arial,sans-serif">YOU</text>
  <text x="{W-45}" y="25" fill="#ff5566" font-size="14" font-weight="bold" font-family="Arial,sans-serif">AI</text>
  
  <!-- Score display -->
  <text x="{W//2-30}" y="30" fill="white" font-size="20" font-weight="bold" font-family="Arial,sans-serif">{st.session_state.player_score}</text>
  <text x="{W//2+20}" y="30" fill="white" font-size="20" font-weight="bold" font-family="Arial,sans-serif">{st.session_state.ai_score}</text>
  <text x="{W//2-5}" y="30" fill="#666" font-size="16" font-family="Arial,sans-serif">-</text>
</svg>
</div>
'''
st.markdown(game_html, unsafe_allow_html=True)

st.caption(f"Thoughts analyzed: {st.session_state.thoughts} | Paddle speed: {'PERFECT' if LxE >= 0.85 else 'GOOD' if LxE >= 0.42 else 'SLOW'}")

with st.expander("💡 How to Play"):
    st.markdown("""
    1. **Type your thoughts** in the text box above
    2. The game analyzes your words for **coherence (L)** and **engagement (E)**
    3. Your paddle position is controlled by **L** 
    4. Your paddle speed depends on **L × E**
    
    **Boost your score with:**
    - Insight words: *realize, understand, pattern, truth, connection*
    - Positive emotions: *love, amazing, beautiful, perfect*
    - GILE terms: *consciousness, hyperconnection, gile, tralse, myrion*
    - Longer, more thoughtful messages
    - Exclamation marks for emphasis!
    """)

if st.session_state.running:
    import time
    time.sleep(0.1)
    st.rerun()
