"""
🫀 HEART COHERENCE PONG - LCC Drop Tower
=========================================
Your heart coherence controls the paddle!
- Coherence increasing/stable = paddle RISES
- Coherence decreasing = paddle FALLS
Like a drop tower powered by your heart-brain connection.
"""

import streamlit as st
import os
import time
import requests
import numpy as np
from collections import deque
from datetime import datetime
import json

st.set_page_config(page_title="Heart Pong LCC", page_icon="🫀", layout="wide")

PULSOID_API_URL = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"

def get_heart_rate(token):
    try:
        headers = {"Authorization": f"Bearer {token}"}
        response = requests.get(PULSOID_API_URL, headers=headers, timeout=5)
        if response.status_code == 200:
            data = response.json()
            return data.get('data', {}).get('heart_rate', 0)
    except:
        pass
    return 0

if 'game_active' not in st.session_state:
    st.session_state.game_active = False
if 'hr_history' not in st.session_state:
    st.session_state.hr_history = []
if 'coherence_history' not in st.session_state:
    st.session_state.coherence_history = []
if 'paddle_y' not in st.session_state:
    st.session_state.paddle_y = 50
if 'ball_x' not in st.session_state:
    st.session_state.ball_x = 50
if 'ball_y' not in st.session_state:
    st.session_state.ball_y = 50
if 'ball_dx' not in st.session_state:
    st.session_state.ball_dx = 2
if 'ball_dy' not in st.session_state:
    st.session_state.ball_dy = 1.5
if 'score' not in st.session_state:
    st.session_state.score = 0
if 'max_height' not in st.session_state:
    st.session_state.max_height = 50
if 'session_data' not in st.session_state:
    st.session_state.session_data = []
if 'prev_coherence' not in st.session_state:
    st.session_state.prev_coherence = 0
if 'goal_hr' not in st.session_state:
    st.session_state.goal_hr = 65

def calculate_coherence(hr_history, goal_hr=65):
    if len(hr_history) < 5:
        return 0.0
    
    recent = hr_history[-20:] if len(hr_history) >= 20 else hr_history
    
    amplitude = np.std(recent)
    regularity = 1.0 / (1.0 + np.std(np.diff(recent)))
    
    rr_intervals = [60000 / hr for hr in recent if hr > 0]
    if len(rr_intervals) >= 5:
        diffs = np.diff(rr_intervals)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        hrv_quality = min(1.0, rmssd / 50.0)
    else:
        hrv_quality = 0.0
    
    coherence = (amplitude * 0.3 + regularity * 0.4 + hrv_quality * 0.3) * 100
    return min(100, max(0, coherence))

def render_game(paddle_y, ball_x, ball_y, coherence, hr, score, max_height):
    tower_pct = paddle_y
    
    if coherence > 85:
        paddle_color = "#00ff88"
        glow = "0 0 20px #00ff88, 0 0 40px #00ff88"
        zone = "QUANTUM ZONE"
    elif coherence > 60:
        paddle_color = "#44aaff"
        glow = "0 0 15px #44aaff"
        zone = "HIGH COHERENCE"
    elif coherence > 30:
        paddle_color = "#ffaa00"
        glow = "0 0 10px #ffaa00"
        zone = "BUILDING"
    else:
        paddle_color = "#ff4444"
        glow = "0 0 5px #ff4444"
        zone = "WARMING UP"

    game_html = f"""
    <div style="display: flex; gap: 20px; justify-content: center; align-items: stretch;">
        <!-- Drop Tower -->
        <div style="width: 120px; height: 500px; background: linear-gradient(to top, #1a0a2e, #0a0a1a); 
                    border: 2px solid #333; border-radius: 10px; position: relative; overflow: hidden;">
            
            <!-- Quantum zone marker at 85% -->
            <div style="position: absolute; bottom: 85%; left: 0; right: 0; height: 2px; 
                        background: #00ff88; opacity: 0.5;"></div>
            <div style="position: absolute; bottom: 86%; right: 5px; color: #00ff88; font-size: 10px; opacity: 0.7;">
                0.85</div>
            
            <!-- Tower fill -->
            <div style="position: absolute; bottom: 0; left: 5px; right: 5px; 
                        height: {tower_pct}%; 
                        background: linear-gradient(to top, {paddle_color}44, {paddle_color});
                        border-radius: 5px 5px 0 0;
                        transition: height 0.3s ease;
                        box-shadow: {glow};">
            </div>
            
            <!-- Max height marker -->
            <div style="position: absolute; bottom: {max_height}%; left: 0; right: 0; 
                        height: 2px; background: gold; opacity: 0.6;"></div>
            
            <!-- Paddle platform -->
            <div style="position: absolute; bottom: {tower_pct}%; left: 2px; right: 2px; 
                        height: 8px; background: {paddle_color}; border-radius: 4px;
                        box-shadow: {glow};
                        transition: bottom 0.3s ease;">
            </div>
            
            <div style="position: absolute; top: 5px; left: 0; right: 0; text-align: center; 
                        color: white; font-size: 11px; font-weight: bold;">
                {tower_pct:.0f}%</div>
        </div>

        <!-- Pong Field -->
        <div style="width: 500px; height: 500px; background: linear-gradient(135deg, #0a0a2e, #1a0a3e); 
                    border: 2px solid #333; border-radius: 10px; position: relative; overflow: hidden;">
            
            <!-- Center line -->
            <div style="position: absolute; left: 50%; top: 0; bottom: 0; width: 2px; 
                        background: repeating-linear-gradient(to bottom, #333 0px, #333 10px, transparent 10px, transparent 20px);">
            </div>
            
            <!-- CHSH threshold line -->
            <div style="position: absolute; left: 0; right: 0; bottom: 85%; height: 1px; 
                        background: #00ff88; opacity: 0.3;"></div>
            
            <!-- Paddle (left side) -->
            <div style="position: absolute; left: 10px; bottom: {paddle_y - 8}%; 
                        width: 15px; height: 80px; background: {paddle_color}; border-radius: 5px;
                        box-shadow: {glow};
                        transition: bottom 0.3s ease;">
            </div>
            
            <!-- Ball -->
            <div style="position: absolute; left: {ball_x}%; bottom: {ball_y}%; 
                        width: 16px; height: 16px; background: white; border-radius: 50%;
                        box-shadow: 0 0 10px white, 0 0 20px {paddle_color};
                        transition: all 0.1s linear;">
            </div>
            
            <!-- Score -->
            <div style="position: absolute; top: 10px; right: 20px; color: white; 
                        font-size: 36px; font-weight: bold; opacity: 0.5;">
                {score}</div>
            
            <!-- Zone label -->
            <div style="position: absolute; bottom: 10px; left: 0; right: 0; text-align: center;
                        color: {paddle_color}; font-size: 14px; font-weight: bold; letter-spacing: 2px;">
                {zone}</div>
        </div>

        <!-- Stats Panel -->
        <div style="width: 200px; padding: 15px; background: linear-gradient(135deg, #0a0a1a, #1a0a2e); 
                    border: 2px solid #333; border-radius: 10px; color: white;">
            <div style="text-align: center; margin-bottom: 15px;">
                <div style="font-size: 48px;">🫀</div>
                <div style="font-size: 36px; font-weight: bold; color: {paddle_color};">{hr}</div>
                <div style="font-size: 12px; opacity: 0.7;">BPM</div>
            </div>
            
            <div style="margin: 10px 0; padding: 10px; background: #ffffff10; border-radius: 8px;">
                <div style="font-size: 11px; opacity: 0.7;">COHERENCE</div>
                <div style="font-size: 24px; font-weight: bold; color: {paddle_color};">{coherence:.1f}%</div>
            </div>
            
            <div style="margin: 10px 0; padding: 10px; background: #ffffff10; border-radius: 8px;">
                <div style="font-size: 11px; opacity: 0.7;">MAX HEIGHT</div>
                <div style="font-size: 24px; font-weight: bold; color: gold;">{max_height:.0f}%</div>
            </div>
            
            <div style="margin: 10px 0; padding: 10px; background: #ffffff10; border-radius: 8px;">
                <div style="font-size: 11px; opacity: 0.7;">SCORE</div>
                <div style="font-size: 24px; font-weight: bold;">{score}</div>
            </div>
            
            <div style="margin-top: 15px; padding: 10px; background: #ffffff08; border-radius: 8px; font-size: 11px; opacity: 0.7;">
                <div>Breathe: 4s in, 6s out</div>
                <div style="margin-top: 5px;">Focus on appreciation</div>
                <div style="margin-top: 5px;">Let rhythm smooth out</div>
            </div>
        </div>
    </div>
    """
    return game_html

st.markdown("""
<style>
    .stApp { background-color: #0a0a1a; }
    h1, h2, h3 { color: white !important; }
    .stMarkdown { color: #cccccc; }
</style>
""", unsafe_allow_html=True)

st.markdown("<h1 style='text-align: center;'>🫀 Heart Coherence Pong</h1>", unsafe_allow_html=True)
st.markdown("<p style='text-align: center; color: #888;'>Your heart coherence controls the paddle. Rise with coherence. Fall when it drops.</p>", unsafe_allow_html=True)

token = os.environ.get('PULSOID_TOKEN')
if not token:
    st.error("PULSOID_TOKEN not set! Please add your Pulsoid API token.")
    st.stop()

col1, col2, col3 = st.columns([1, 2, 1])
with col1:
    goal_hr = st.number_input("Goal HR (BPM)", value=65, min_value=50, max_value=80)
with col2:
    speed = st.select_slider("Game Speed", options=["Slow", "Medium", "Fast"], value="Medium")
with col3:
    rise_rate = st.slider("Rise Sensitivity", 0.5, 3.0, 1.5)

speed_map = {"Slow": 3, "Medium": 2, "Fast": 1}
update_interval = speed_map[speed]

game_placeholder = st.empty()
status_placeholder = st.empty()

start_btn = st.button("🫀 START HEART PONG", type="primary", use_container_width=True)

if start_btn:
    st.session_state.game_active = True
    st.session_state.hr_history = []
    st.session_state.coherence_history = []
    st.session_state.paddle_y = 10
    st.session_state.ball_x = 50
    st.session_state.ball_y = 50
    st.session_state.ball_dx = 1.5
    st.session_state.ball_dy = 1.0
    st.session_state.score = 0
    st.session_state.max_height = 10
    st.session_state.prev_coherence = 0
    st.session_state.session_data = []

if st.session_state.game_active:
    stop_btn = st.button("Stop Game", type="secondary")
    if stop_btn:
        st.session_state.game_active = False
        st.rerun()
    
    for tick in range(600):
        if not st.session_state.game_active:
            break
            
        hr = get_heart_rate(token)
        
        if hr > 0:
            st.session_state.hr_history.append(hr)
            coherence = calculate_coherence(st.session_state.hr_history, goal_hr)
            st.session_state.coherence_history.append(coherence)
            
            prev = st.session_state.prev_coherence
            
            if coherence >= prev - 0.5:
                move = rise_rate * (1 + (coherence - prev) * 0.1)
                st.session_state.paddle_y = min(98, st.session_state.paddle_y + move)
            else:
                drop = abs(prev - coherence) * 0.8
                st.session_state.paddle_y = max(2, st.session_state.paddle_y - drop)
            
            st.session_state.prev_coherence = coherence
            
            if st.session_state.paddle_y > st.session_state.max_height:
                st.session_state.max_height = st.session_state.paddle_y
            
            st.session_state.ball_x += st.session_state.ball_dx
            st.session_state.ball_y += st.session_state.ball_dy
            
            if st.session_state.ball_y >= 95 or st.session_state.ball_y <= 5:
                st.session_state.ball_dy *= -1
            
            if st.session_state.ball_x >= 95:
                st.session_state.ball_dx *= -1
            
            if st.session_state.ball_x <= 8:
                paddle_top = st.session_state.paddle_y + 8
                paddle_bottom = st.session_state.paddle_y - 8
                
                if paddle_bottom <= st.session_state.ball_y <= paddle_top:
                    st.session_state.ball_dx = abs(st.session_state.ball_dx)
                    st.session_state.score += 1
                    
                    if coherence > 85:
                        st.session_state.score += 2
                else:
                    st.session_state.ball_x = 50
                    st.session_state.ball_y = 50
            
            st.session_state.session_data.append({
                'timestamp': datetime.now().isoformat(),
                'hr': hr,
                'coherence': coherence,
                'paddle_y': st.session_state.paddle_y,
                'score': st.session_state.score
            })
            
            html = render_game(
                st.session_state.paddle_y,
                st.session_state.ball_x,
                st.session_state.ball_y,
                coherence,
                hr,
                st.session_state.score,
                st.session_state.max_height
            )
            game_placeholder.markdown(html, unsafe_allow_html=True)
            
            status_placeholder.markdown(
                f"<p style='text-align:center; color:#888; font-size:12px;'>"
                f"Tick {tick+1} | Samples: {len(st.session_state.hr_history)} | "
                f"Tower: {st.session_state.paddle_y:.0f}%</p>",
                unsafe_allow_html=True
            )
        
        time.sleep(update_interval)
    
    st.session_state.game_active = False
    
    if st.session_state.session_data:
        st.markdown("---")
        st.markdown("<h2 style='text-align:center;'>Session Complete!</h2>", unsafe_allow_html=True)
        
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("Final Score", st.session_state.score)
        with col2:
            st.metric("Max Height", f"{st.session_state.max_height:.0f}%")
        with col3:
            avg_coh = np.mean(st.session_state.coherence_history) if st.session_state.coherence_history else 0
            st.metric("Avg Coherence", f"{avg_coh:.1f}%")
        with col4:
            above_85 = np.sum(np.array(st.session_state.coherence_history) > 85) / max(1, len(st.session_state.coherence_history)) * 100
            st.metric("Time > 0.85", f"{above_85:.0f}%")
else:
    demo_html = render_game(50, 50, 50, 0, 0, 0, 50)
    game_placeholder.markdown(demo_html, unsafe_allow_html=True)
    st.markdown("<p style='text-align:center; color:#666;'>Press START to begin your heart coherence training!</p>", unsafe_allow_html=True)
