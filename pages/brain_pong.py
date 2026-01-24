"""
Pure Mental Pong - 100% Thought-Controlled (Fixed Version)
Uses text_area for real-time updates and removes problematic key parameter.
"""

import streamlit as st
import streamlit.components.v1 as components
import hashlib

st.set_page_config(page_title="Mental Pong", page_icon="🧠", layout="wide")

st.title("🧠 Pure Mental Pong")
st.markdown("**Your paddle moves by THOUGHT ALONE.** Type to control your consciousness!")

if 'L' not in st.session_state:
    st.session_state.L = 0.5
    st.session_state.E = 0.5

INSIGHT_WORDS = {
    'up': 0.22, 'high': 0.18, 'above': 0.15, 'top': 0.15, 'rise': 0.15, 'ascend': 0.18,
    'sky': 0.12, 'heaven': 0.15, 'light': 0.12, 'consciousness': 0.18, 'transcend': 0.22,
    'gile': 0.22, 'myrion': 0.18, 'tralse': 0.18, 'love': 0.15, 'truth': 0.12,
    'u': 0.08, 'h': 0.05,
    'down': -0.22, 'low': -0.18, 'below': -0.15, 'bottom': -0.15, 'fall': -0.15, 'descend': -0.18,
    'ground': -0.12, 'earth': -0.10, 'dark': -0.10, 'shadow': -0.12, 'deep': -0.12,
    'd': -0.08, 'l': -0.05,
    'center': 0.0, 'middle': 0.0, 'balance': 0.0, 'neutral': 0.0, 'c': 0.0, 'm': 0.0,
    'reset': 0.0
}

def analyze_thought(text):
    if not text.strip():
        return 0.5, 0.5
    
    if 'reset' in text.lower():
        return 0.5, 0.5
    
    words = text.lower().split()
    position_shift = 0
    power = 0.5
    
    for word in words:
        word_clean = ''.join(c for c in word if c.isalpha())
        if word_clean in INSIGHT_WORDS:
            position_shift += INSIGHT_WORDS[word_clean]
        if word_clean in {'hyperconnection', 'causation', 'radiant', 'quantum', 'entanglement'}:
            power += 0.1
    
    for char in text.lower():
        if char in INSIGHT_WORDS:
            position_shift += INSIGHT_WORDS[char] * 0.3
    
    if '!' in text:
        position_shift *= 1.5
        power += 0.08
    
    L = max(0.05, min(0.95, 0.5 + position_shift))
    E = min(0.95, power + len(words) * 0.02)
    
    return L, E

st.markdown("### 💭 Type Your Consciousness State")

thought = st.text_area(
    "Type words to control paddle (updates as you type):",
    height=80,
    placeholder="Type: 'up up up!' or 'down down' - updates happen when you click outside or press Ctrl+Enter",
    key="thought_box"
)

if thought:
    L, E = analyze_thought(thought)
    st.session_state.L = L
    st.session_state.E = E

L_val = st.session_state.L
E_val = st.session_state.E
LxE = L_val * E_val

col1, col2, col3 = st.columns(3)
with col1:
    if L_val > 0.65:
        st.success(f"⬆️ Position: {L_val:.0%} UP")
    elif L_val < 0.35:
        st.error(f"⬇️ Position: {L_val:.0%} DOWN")
    else:
        st.info(f"○ Position: {L_val:.0%} CENTER")
with col2:
    st.metric("Power (E)", f"{E_val:.0%}")
with col3:
    if LxE >= 0.85:
        st.success("⚡ CAUSATION MODE")
    elif LxE >= 0.42:
        st.info("🔗 CONNECTED")
    else:
        st.warning("📊 Building...")

paddle_target = int((1 - L_val) * 100)
paddle_speed = 4 + int(LxE * 10)

pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#44ff88")

game_html = f'''
<!DOCTYPE html>
<html>
<head>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ background: transparent; display: flex; flex-direction: column; align-items: center; font-family: Arial, sans-serif; }}
canvas {{ border-radius: 12px; border: 3px solid #555; display: block; margin: 10px 0; }}
.controls {{ display: flex; align-items: center; gap: 15px; margin: 10px 0; padding: 10px 20px; background: #1a1a2e; border-radius: 10px; }}
.indicator {{ width: 250px; height: 16px; background: linear-gradient(to right, #ff5566, #ffff00, #00ff88); border-radius: 8px; position: relative; border: 2px solid #444; }}
.marker {{ width: 6px; height: 22px; background: white; border-radius: 3px; position: absolute; top: -3px; box-shadow: 0 0 8px white; }}
.label {{ color: #888; font-size: 12px; }}
</style>
</head>
<body>
<canvas id="pong" width="600" height="320"></canvas>
<div class="controls">
  <span class="label">⬇️ DOWN</span>
  <div class="indicator">
    <div class="marker" style="left: calc({100 - paddle_target}% - 3px);"></div>
  </div>
  <span class="label">UP ⬆️</span>
  <span class="label" style="margin-left: 20px;">Speed: {paddle_speed}</span>
</div>

<script>
const canvas = document.getElementById('pong');
const ctx = canvas.getContext('2d');
const W = 600, H = 320;

const PADDLE_TARGET = {paddle_target} * H / 100;
const PADDLE_SPEED = {paddle_speed};
const PCOLOR = '{pcolor}';

let ball = {{ x: W/2, y: H/2, vx: 4, vy: 2, r: 10 }};
let player = {{ y: H/2, h: 70, x: 25 }};
let ai = {{ y: H/2, h: 55, speed: 2.5, x: W - 25 }};
let score = {{ player: 0, ai: 0 }};

function update() {{
  const diff = PADDLE_TARGET - player.y;
  player.y += Math.sign(diff) * Math.min(PADDLE_SPEED, Math.abs(diff) * 0.15);
  player.y = Math.max(player.h/2 + 5, Math.min(H - player.h/2 - 5, player.y));
  
  const aiTarget = ball.y + ball.vy * 10;
  const aiDiff = aiTarget - ai.y;
  if (Math.abs(aiDiff) > 8) ai.y += Math.sign(aiDiff) * ai.speed;
  ai.y = Math.max(ai.h/2, Math.min(H - ai.h/2, ai.y));
  
  ball.x += ball.vx;
  ball.y += ball.vy;
  
  if (ball.y <= ball.r) {{ ball.y = ball.r; ball.vy = Math.abs(ball.vy); }}
  if (ball.y >= H - ball.r) {{ ball.y = H - ball.r; ball.vy = -Math.abs(ball.vy); }}
  
  if (ball.x <= player.x + 15 && ball.x >= player.x - 5 && ball.vx < 0) {{
    if (Math.abs(ball.y - player.y) < player.h/2 + ball.r) {{
      ball.vx = Math.abs(ball.vx) * 1.03;
      ball.vy += (ball.y - player.y) * 0.08;
      ball.x = player.x + 16;
    }}
  }}
  
  if (ball.x >= ai.x - 15 && ball.x <= ai.x + 5 && ball.vx > 0) {{
    if (Math.abs(ball.y - ai.y) < ai.h/2 + ball.r) {{
      ball.vx = -Math.abs(ball.vx) * 1.03;
      ball.vy += (ball.y - ai.y) * 0.08;
      ball.x = ai.x - 16;
    }}
  }}
  
  if (ball.x < -10) {{
    score.ai++;
    resetBall(-1);
  }}
  if (ball.x > W + 10) {{
    score.player++;
    resetBall(1);
  }}
  
  ball.vx = Math.sign(ball.vx) * Math.min(Math.abs(ball.vx), 12);
  ball.vy = Math.sign(ball.vy) * Math.min(Math.abs(ball.vy), 8);
}}

function resetBall(dir) {{
  ball.x = W/2;
  ball.y = H/2;
  ball.vx = 4 * dir;
  ball.vy = (Math.random() - 0.5) * 3;
}}

function draw() {{
  ctx.fillStyle = '#0a0a1a';
  ctx.fillRect(0, 0, W, H);
  
  ctx.strokeStyle = '#222';
  ctx.lineWidth = 2;
  ctx.setLineDash([10, 8]);
  ctx.beginPath();
  ctx.moveTo(W/2, 0);
  ctx.lineTo(W/2, H);
  ctx.stroke();
  ctx.setLineDash([]);
  
  ctx.beginPath();
  ctx.arc(W/2, H/2, 40, 0, Math.PI * 2);
  ctx.stroke();
  
  ctx.shadowColor = PCOLOR;
  ctx.shadowBlur = 20;
  ctx.fillStyle = PCOLOR;
  roundRect(ctx, player.x - 7, player.y - player.h/2, 14, player.h, 7);
  ctx.fill();
  
  ctx.shadowColor = '#ff5566';
  ctx.fillStyle = '#ff5566';
  roundRect(ctx, ai.x - 7, ai.y - ai.h/2, 14, ai.h, 7);
  ctx.fill();
  
  ctx.shadowColor = 'white';
  ctx.shadowBlur = 15;
  ctx.fillStyle = 'white';
  ctx.beginPath();
  ctx.arc(ball.x, ball.y, ball.r, 0, Math.PI * 2);
  ctx.fill();
  ctx.shadowBlur = 0;
  
  ctx.font = 'bold 14px Arial';
  ctx.fillStyle = PCOLOR;
  ctx.fillText('MIND', 15, 25);
  ctx.fillStyle = '#ff5566';
  ctx.textAlign = 'right';
  ctx.fillText('AI', W - 15, 25);
  ctx.textAlign = 'left';
  
  ctx.font = 'bold 28px Arial';
  ctx.fillStyle = 'white';
  ctx.textAlign = 'center';
  ctx.fillText(score.player + ' : ' + score.ai, W/2, 32);
  ctx.textAlign = 'left';
}}

function roundRect(ctx, x, y, w, h, r) {{
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.lineTo(x + w - r, y);
  ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r);
  ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
  ctx.lineTo(x + r, y + h);
  ctx.quadraticCurveTo(x, y + h, x, y + h - r);
  ctx.lineTo(x, y + r);
  ctx.quadraticCurveTo(x, y, x + r, y);
  ctx.closePath();
}}

function gameLoop() {{
  update();
  draw();
  requestAnimationFrame(gameLoop);
}}

gameLoop();
</script>
</body>
</html>
'''

components.html(game_html, height=430)

with st.expander("🧠 Quick Control Guide", expanded=False):
    st.markdown("""
    **Type words to control paddle position:**
    
    | Quick Keys | Full Words | Effect |
    |------------|------------|--------|
    | `u u u` | up, high, sky, transcend | Paddle UP ⬆️ |
    | `d d d` | down, low, ground, deep | Paddle DOWN ⬇️ |
    | `c` or `m` | center, middle, balance | Paddle CENTER |
    | `reset` | reset | Return to center |
    
    **Pro Tips:**
    - Add `!` for stronger effect: `up up up!`
    - Use TI words for power boost: `gile myrion tralse`
    - Higher L×E = faster paddle response
    - Click outside text area or press Ctrl+Enter to update
    """)

st.caption("🧠 Pure Mental Control - Type your thoughts to move the paddle!")
