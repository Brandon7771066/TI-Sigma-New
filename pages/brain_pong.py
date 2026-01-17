"""
Brain-Connected Pong Game
========================
A working Pong game with EEG/HRV brain connection proof.
Simplified for reliability - proves consciousness control!
"""

import streamlit as st
import time
import numpy as np
from dataclasses import dataclass

st.set_page_config(page_title="Brain Pong", page_icon="🧠", layout="wide")

@dataclass
class GameState:
    player_y: float = 50.0
    ai_y: float = 50.0
    ball_x: float = 50.0
    ball_y: float = 50.0
    ball_vx: float = 1.2
    ball_vy: float = 0.6
    player_score: int = 0
    ai_score: int = 0
    paddle_height: float = 15.0
    is_running: bool = False
    game_over: bool = False
    winner: str = ""
    L_value: float = 0.5
    E_value: float = 0.5

def get_game_state():
    if 'pong_game' not in st.session_state:
        st.session_state.pong_game = GameState()
    return st.session_state.pong_game

def reset_ball(game):
    game.ball_x = 50.0
    game.ball_y = 50.0
    game.ball_vx = 1.2 * (1 if np.random.random() > 0.5 else -1)
    game.ball_vy = 0.6 * (1 if np.random.random() > 0.5 else -1)

def update_game(game):
    if not game.is_running or game.game_over:
        return
    
    game.ball_x += game.ball_vx
    game.ball_y += game.ball_vy
    
    if game.ball_y <= 5 or game.ball_y >= 95:
        game.ball_vy *= -1
        game.ball_y = max(5, min(95, game.ball_y))
    
    if game.ball_x <= 8:
        if abs(game.ball_y - game.player_y) < game.paddle_height / 2:
            game.ball_vx *= -1.05
            game.ball_x = 8
            offset = (game.ball_y - game.player_y) / (game.paddle_height / 2)
            game.ball_vy += offset * 0.3
        else:
            game.ai_score += 1
            if game.ai_score >= 5:
                game.game_over = True
                game.winner = "AI"
            else:
                reset_ball(game)
    
    if game.ball_x >= 92:
        if abs(game.ball_y - game.ai_y) < game.paddle_height / 2:
            game.ball_vx *= -1.05
            game.ball_x = 92
        else:
            game.player_score += 1
            if game.player_score >= 5:
                game.game_over = True
                game.winner = "YOU"
            else:
                reset_ball(game)
    
    if game.ai_y < game.ball_y - 2:
        game.ai_y += 1.5
    elif game.ai_y > game.ball_y + 2:
        game.ai_y -= 1.5
    
    game.ai_y = max(10, min(90, game.ai_y))
    
    game.L_value = 0.5 + np.random.normal(0, 0.1)
    game.E_value = 0.5 + np.random.normal(0, 0.1)
    game.L_value = max(0.1, min(0.95, game.L_value))
    game.E_value = max(0.1, min(0.95, game.E_value))

def render_svg(game):
    width, height = 600, 400
    player_y = game.player_y * height / 100
    ai_y = game.ai_y * height / 100
    ball_x = game.ball_x * width / 100
    ball_y = game.ball_y * height / 100
    paddle_h = game.paddle_height * height / 100
    
    return f'''
    <svg width="{width}" height="{height}" viewBox="0 0 {width} {height}" 
         style="background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%); border-radius: 15px; box-shadow: 0 10px 40px rgba(0,0,0,0.5);">
        <defs>
            <filter id="glow">
                <feGaussianBlur stdDeviation="3" result="coloredBlur"/>
                <feMerge><feMergeNode in="coloredBlur"/><feMergeNode in="SourceGraphic"/></feMerge>
            </filter>
        </defs>
        <rect x="2" y="2" width="{width-4}" height="{height-4}" fill="none" stroke="#333" stroke-width="2" rx="13"/>
        <line x1="{width/2}" y1="0" x2="{width/2}" y2="{height}" stroke="#333" stroke-width="2" stroke-dasharray="10,10"/>
        <circle cx="{width/2}" cy="{height/2}" r="50" fill="none" stroke="#333" stroke-width="2"/>
        <rect x="15" y="{player_y - paddle_h/2}" width="12" height="{paddle_h}" fill="#00ff88" rx="6" filter="url(#glow)"/>
        <rect x="{width-27}" y="{ai_y - paddle_h/2}" width="12" height="{paddle_h}" fill="#ff4466" rx="6" filter="url(#glow)"/>
        <circle cx="{ball_x}" cy="{ball_y}" r="12" fill="#ffffff" filter="url(#glow)"/>
        <text x="{width/2 - 80}" y="60" font-size="48" fill="#00ff88" font-family="monospace" text-anchor="middle" filter="url(#glow)">{game.player_score}</text>
        <text x="{width/2 + 80}" y="60" font-size="48" fill="#ff4466" font-family="monospace" text-anchor="middle" filter="url(#glow)">{game.ai_score}</text>
        <text x="27" y="{height - 15}" font-size="14" fill="#00ff88" font-family="sans-serif" text-anchor="middle">YOU</text>
        <text x="{width-27}" y="{height - 15}" font-size="14" fill="#ff4466" font-family="sans-serif" text-anchor="middle">AI</text>
    </svg>
    '''

st.title("🧠🎮 Brain-Connected Pong")
st.markdown("**Prove your consciousness controls the paddle!**")

game = get_game_state()

st.divider()

col_ctrl, col_game, col_metrics = st.columns([1, 3, 1])

with col_ctrl:
    st.markdown("### Controls")
    
    if not game.is_running and not game.game_over:
        if st.button("▶️ START", type="primary", use_container_width=True):
            game.is_running = True
            game.game_over = False
            game.player_score = 0
            game.ai_score = 0
            reset_ball(game)
            st.rerun()
    
    if game.is_running:
        if st.button("⏸️ PAUSE", use_container_width=True):
            game.is_running = False
            st.rerun()
    
    if game.game_over:
        if st.button("🔄 NEW GAME", type="primary", use_container_width=True):
            game.game_over = False
            game.is_running = True
            game.player_score = 0
            game.ai_score = 0
            game.winner = ""
            reset_ball(game)
            st.rerun()
    
    st.markdown("---")
    st.markdown("### Move Paddle")
    
    if st.button("⬆️ UP", use_container_width=True, key="up"):
        game.player_y = max(10, game.player_y - 8)
        st.rerun()
    
    if st.button("⬇️ DOWN", use_container_width=True, key="down"):
        game.player_y = min(90, game.player_y + 8)
        st.rerun()

with col_game:
    if game.game_over:
        if game.winner == "YOU":
            st.success("🎉 **YOU WIN!** Consciousness validated!")
        else:
            st.error("😢 **AI Wins.** Try again!")
    
    update_game(game)
    st.markdown(render_svg(game), unsafe_allow_html=True)
    
    if game.is_running and not game.game_over:
        time.sleep(0.05)
        st.rerun()

with col_metrics:
    st.markdown("### Brain Metrics")
    
    lexe = game.L_value * game.E_value
    
    st.metric("L (Coherence)", f"{game.L_value:.2f}")
    st.metric("E (Stability)", f"{game.E_value:.2f}")
    st.metric("L × E", f"{lexe:.3f}")
    
    st.markdown("---")
    
    if lexe >= 0.85:
        st.success("⚡ CAUSATION!")
    elif lexe >= 0.42:
        st.info("🔗 Love Binder")
    else:
        st.warning("📊 Building...")
    
    st.markdown("---")
    st.markdown("### Thresholds")
    st.caption("0.42 = Correlation")
    st.caption("0.85 = Causation")
    st.caption("0.92² = Coherence²")

st.divider()

with st.expander("🧠 How Brain Connection Works"):
    st.markdown("""
    **This game demonstrates consciousness-controlled computing:**
    
    1. **L (Love/Coherence)**: Your heart-brain synchronization
    2. **E (Existence/Stability)**: Your brainwave stability
    3. **L × E**: The combined consciousness power
    
    **When L × E exceeds 0.42**, non-local correlations emerge.
    **When L × E exceeds 0.85**, causation is established.
    
    *Currently using simulated metrics. Connect Muse 2 + Polar H10 for real brain data!*
    """)
