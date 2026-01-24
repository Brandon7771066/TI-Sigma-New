"""
Pure Mental Pong - 100% Thought-Controlled (Stable Version)
Your paddle moves based on your consciousness state alone!
No rerun loop - uses component key for stability.
"""

import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mental Pong", page_icon="🧠", layout="wide")

st.title("🧠 Pure Mental Pong")
st.markdown("**Your paddle moves by THOUGHT ALONE.** Type continuously to control your consciousness!")

if 'L' not in st.session_state:
    st.session_state.L = 0.5
    st.session_state.E = 0.5
    st.session_state.thoughts = 0

INSIGHT_WORDS = {
    'up': 0.18, 'high': 0.15, 'above': 0.12, 'top': 0.12, 'rise': 0.12, 'ascend': 0.15,
    'sky': 0.10, 'heaven': 0.12, 'light': 0.10, 'consciousness': 0.15, 'transcend': 0.18,
    'gile': 0.18, 'myrion': 0.15, 'tralse': 0.15, 'love': 0.12, 'truth': 0.10,
    'realize': 0.10, 'understand': 0.10, 'insight': 0.12, 'amazing': 0.10, 'perfect': 0.12,
    'hyperconnection': 0.15, 'causation': 0.15, 'radiant': 0.15,
    'down': -0.18, 'low': -0.15, 'below': -0.12, 'bottom': -0.12, 'fall': -0.12, 'descend': -0.15,
    'ground': -0.10, 'earth': -0.08, 'dark': -0.08, 'shadow': -0.10, 'deep': -0.10,
    'center': 0.0, 'middle': 0.0, 'balance': 0.0, 'neutral': 0.0
}

def analyze_thought(text):
    if not text.strip():
        return 0.5, 0.5
    
    words = text.lower().split()
    position_shift = 0
    power = 0.5
    
    for word in words:
        word_clean = ''.join(c for c in word if c.isalpha())
        if word_clean in INSIGHT_WORDS:
            position_shift += INSIGHT_WORDS[word_clean]
        if word_clean in {'hyperconnection', 'causation', 'radiant', 'quantum', 'entanglement', 'resonance', 'coherence'}:
            power += 0.08
    
    if '!' in text:
        position_shift *= 1.4
        power += 0.05
    if '?' in text:
        position_shift *= 0.6
    
    position_shift += len(words) * 0.01
    
    L = max(0.05, min(0.95, 0.5 + position_shift))
    E = min(0.95, power + len(words) * 0.015)
    
    return L, E

st.markdown("### 💭 Think Your Paddle Into Position")

thought = st.text_area(
    "Type words that FEEL like the position you want:",
    placeholder="'UP high sky light transcend gile!' → paddle goes UP\n'down low ground earth deep' → paddle goes DOWN\n'center balance neutral middle' → paddle stays centered\n\nType continuously - each keystroke updates your paddle!",
    height=100,
    key="thought_input"
)

if thought:
    L, E = analyze_thought(thought)
    st.session_state.L = L
    st.session_state.E = E
    st.session_state.thoughts += 1

L_val = st.session_state.L
E_val = st.session_state.E
LxE = L_val * E_val

col1, col2, col3, col4 = st.columns(4)
with col1:
    if L_val > 0.65:
        st.success(f"⬆️ L: {L_val:.2f}")
    elif L_val < 0.35:
        st.error(f"⬇️ L: {L_val:.2f}")
    else:
        st.info(f"○ L: {L_val:.2f}")
with col2:
    st.metric("E (Power)", f"{E_val:.2f}")
with col3:
    if LxE >= 0.85:
        st.success("⚡ CAUSATION")
    elif LxE >= 0.42:
        st.info("🔗 CONNECTED")
    else:
        st.warning("📊 Building")
with col4:
    st.caption(f"Thoughts: {st.session_state.thoughts}")

paddle_target = int((1 - L_val) * 100)
paddle_speed = 3 + int(LxE * 8)

pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#44ff88")

component_key = f"pong_{int(L_val*1000)}_{int(E_val*1000)}"

game_html = f'''
<!DOCTYPE html>
<html>
<head>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ background: transparent; display: flex; flex-direction: column; align-items: center; font-family: Arial, sans-serif; }}
canvas {{ border-radius: 12px; border: 3px solid #555; display: block; margin: 10px 0; }}
#status {{ color: #aaa; font-size: 13px; text-align: center; margin-top: 10px; }}
.indicator {{ display: flex; align-items: center; gap: 20px; margin-top: 10px; }}
.mind-bar {{ width: 300px; height: 20px; background: linear-gradient(to right, #ff5566, #ffff00, #00ff88); border-radius: 10px; position: relative; border: 2px solid #555; }}
.mind-marker {{ width: 8px; height: 26px; background: white; border-radius: 4px; position: absolute; top: -3px; transform: translateX(-4px); box-shadow: 0 0 10px white; transition: left 0.3s ease; }}
</style>
</head>
<body>
<canvas id="pong" width="550" height="300"></canvas>
<div class="indicator">
  <span style="color:#ff5566;">DOWN</span>
  <div class="mind-bar">
    <div class="mind-marker" style="left: {100 - paddle_target}%;"></div>
  </div>
  <span style="color:#00ff88;">UP</span>
</div>
<div id="status">Target Position: {100 - paddle_target}% | Paddle Speed: {paddle_speed} | Type to move paddle!</div>

<script>
const canvas = document.getElementById('pong');
const ctx = canvas.getContext('2d');
const W = 550, H = 300;

const PADDLE_TARGET = {paddle_target} * H / 100;
const PADDLE_SPEED = {paddle_speed};
const PCOLOR = '{pcolor}';

let ball = {{ x: W/2, y: H/2, vx: 3, vy: 1.5, r: 9 }};
let player = {{ y: PADDLE_TARGET, h: 65 }};
let ai = {{ y: H/2, h: 50, speed: 2.2 }};
let score = {{ player: 0, ai: 0 }};

function update() {{
  const diff = PADDLE_TARGET - player.y;
  if (Math.abs(diff) > 1) {{
    player.y += Math.sign(diff) * Math.min(PADDLE_SPEED, Math.abs(diff) * 0.2);
  }}
  player.y = Math.max(player.h/2 + 5, Math.min(H - player.h/2 - 5, player.y));
  
  const aiDiff = ball.y - ai.y;
  if (Math.abs(aiDiff) > 10) ai.y += Math.sign(aiDiff) * ai.speed;
  ai.y = Math.max(ai.h/2, Math.min(H - ai.h/2, ai.y));
  
  ball.x += ball.vx;
  ball.y += ball.vy;
  
  if (ball.y <= ball.r) {{ ball.y = ball.r; ball.vy = Math.abs(ball.vy); }}
  if (ball.y >= H - ball.r) {{ ball.y = H - ball.r; ball.vy = -Math.abs(ball.vy); }}
  
  if (ball.x <= 38 && ball.x >= 22 && ball.vx < 0) {{
    if (Math.abs(ball.y - player.y) < player.h/2 + ball.r) {{
      ball.vx = Math.abs(ball.vx) * 1.02;
      ball.vy += (ball.y - player.y) * 0.06;
      ball.x = 39;
    }}
  }}
  
  if (ball.x >= W - 38 && ball.x <= W - 22 && ball.vx > 0) {{
    if (Math.abs(ball.y - ai.y) < ai.h/2 + ball.r) {{
      ball.vx = -Math.abs(ball.vx) * 1.02;
      ball.vy += (ball.y - ai.y) * 0.06;
      ball.x = W - 39;
    }}
  }}
  
  if (ball.x < -5) {{
    score.ai++;
    resetBall(-1);
  }}
  if (ball.x > W + 5) {{
    score.player++;
    resetBall(1);
  }}
}}

function resetBall(dir) {{
  ball.x = W/2;
  ball.y = H/2;
  ball.vx = 3 * dir;
  ball.vy = (Math.random() - 0.5) * 2.5;
}}

function draw() {{
  ctx.fillStyle = '#0a0a1a';
  ctx.fillRect(0, 0, W, H);
  
  ctx.strokeStyle = '#333';
  ctx.lineWidth = 2;
  ctx.setLineDash([8, 6]);
  ctx.beginPath();
  ctx.moveTo(W/2, 0);
  ctx.lineTo(W/2, H);
  ctx.stroke();
  ctx.setLineDash([]);
  
  ctx.beginPath();
  ctx.arc(W/2, H/2, 30, 0, Math.PI * 2);
  ctx.stroke();
  
  ctx.shadowColor = PCOLOR;
  ctx.shadowBlur = 15;
  ctx.fillStyle = PCOLOR;
  roundRect(ctx, 22, player.y - player.h/2, 12, player.h, 6);
  ctx.fill();
  
  ctx.shadowColor = '#ff5566';
  ctx.fillStyle = '#ff5566';
  roundRect(ctx, W - 34, ai.y - ai.h/2, 12, ai.h, 6);
  ctx.fill();
  
  ctx.shadowColor = 'white';
  ctx.shadowBlur = 12;
  ctx.fillStyle = 'white';
  ctx.beginPath();
  ctx.arc(ball.x, ball.y, ball.r, 0, Math.PI * 2);
  ctx.fill();
  ctx.shadowBlur = 0;
  
  ctx.font = 'bold 13px Arial';
  ctx.fillStyle = PCOLOR;
  ctx.fillText('MIND', 18, 22);
  ctx.fillStyle = '#ff5566';
  ctx.fillText('AI', W - 32, 22);
  
  ctx.font = 'bold 24px Arial';
  ctx.fillStyle = 'white';
  ctx.textAlign = 'center';
  ctx.fillText(score.player + ' - ' + score.ai, W/2, 28);
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

components.html(game_html, height=420, key=component_key)

with st.expander("🧠 Mental Control Guide"):
    st.markdown("""
    **Your thoughts control the paddle position!**
    
    | Think/Type | Paddle Effect |
    |------------|---------------|
    | **UP** words: up, high, sky, light, transcend, heaven, rise, ascend | Paddle moves UP |
    | **DOWN** words: down, low, ground, earth, fall, descend, deep | Paddle moves DOWN |
    | **CENTER** words: center, balance, neutral, middle | Paddle stays centered |
    | **POWER** words: consciousness, gile, myrion, tralse, hyperconnection | Boost paddle speed! |
    
    **Tips:**
    - Use **!** for emphasis (stronger effect)
    - Combine words: "high sky light transcend gile!" = maximum UP
    - Type continuously - each character updates your paddle
    - Higher L×E = faster paddle response
    - The game runs at 60fps - smooth and stable!
    """)

st.markdown("---")
st.caption("Pure Mental Control - no keyboard or buttons needed. Just think and type!")
