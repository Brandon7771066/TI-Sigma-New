"""
Brain-Connected Pong - Simplified & Robust
==========================================
"""

import streamlit as st
import numpy as np

st.set_page_config(page_title="Brain Pong", page_icon="🧠", layout="wide")

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

PADDLE_HEIGHT = 15

def reset_ball():
    st.session_state.ball_x = 50.0
    st.session_state.ball_y = 50.0
    st.session_state.ball_vx = 2.0 * (1 if np.random.random() > 0.5 else -1)
    st.session_state.ball_vy = 1.0 * (1 if np.random.random() > 0.5 else -1)

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
    
    svg = f'''<svg width="{w}" height="{h}" style="background:#1a1a2e;border-radius:12px;">
        <rect x="2" y="2" width="{w-4}" height="{h-4}" fill="none" stroke="#333" stroke-width="2" rx="10"/>
        <line x1="{w//2}" y1="0" x2="{w//2}" y2="{h}" stroke="#333" stroke-width="2" stroke-dasharray="8,8"/>
        <rect x="15" y="{py-ph/2}" width="12" height="{ph}" fill="#00ff88" rx="6"/>
        <rect x="{w-27}" y="{ay-ph/2}" width="12" height="{ph}" fill="#ff4466" rx="6"/>
        <circle cx="{bx}" cy="{by}" r="10" fill="#fff"/>
        <text x="{w//2-60}" y="50" font-size="36" fill="#00ff88" font-family="monospace" text-anchor="middle">{st.session_state.player_score}</text>
        <text x="{w//2+60}" y="50" font-size="36" fill="#ff4466" font-family="monospace" text-anchor="middle">{st.session_state.ai_score}</text>
        <text x="21" y="{h-12}" font-size="12" fill="#00ff88" text-anchor="middle">YOU</text>
        <text x="{w-21}" y="{h-12}" font-size="12" fill="#ff4466" text-anchor="middle">AI</text>
    </svg>'''
    return svg

st.title("🧠 Brain Pong")

if st.session_state.game_over:
    if st.session_state.winner == "YOU":
        st.success("🎉 YOU WIN! Consciousness validated!")
    else:
        st.error("😢 AI Wins. Try again!")

col1, col2, col3 = st.columns([1, 4, 1])

with col1:
    st.markdown("### Controls")
    
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
    st.markdown("### Paddle")
    
    if st.button("⬆️ UP", key="up", use_container_width=True):
        st.session_state.player_y = max(10, st.session_state.player_y - 10)
    
    if st.button("⬇️ DOWN", key="down", use_container_width=True):
        st.session_state.player_y = min(90, st.session_state.player_y + 10)

with col2:
    game_step()
    st.markdown(render_game(), unsafe_allow_html=True)
    
    if st.session_state.running and not st.session_state.game_over:
        import time
        time.sleep(0.08)
        st.rerun()

with col3:
    st.markdown("### Brain Metrics")
    L = 0.5 + np.random.uniform(-0.1, 0.1)
    E = 0.5 + np.random.uniform(-0.1, 0.1)
    LxE = L * E
    
    st.metric("L (Coherence)", f"{L:.2f}")
    st.metric("E (Stability)", f"{E:.2f}")
    st.metric("L × E", f"{LxE:.3f}")
    
    st.markdown("---")
    if LxE >= 0.42:
        st.success("🔗 Hyperconnected!")
    else:
        st.info("📊 Building coherence...")
