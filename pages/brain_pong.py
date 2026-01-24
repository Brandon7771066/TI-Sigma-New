"""
Pure Mind Control Pong - Client-Side Animation with Mind Control Integration
"""

import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mind Pong", page_icon="🧠", layout="wide")

st.title("🧠 Pure Mind Control Pong")

if 'L' not in st.session_state:
    st.session_state.L = 0.5
    st.session_state.E = 0.5
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

col1, col2, col3 = st.columns([2, 1, 1])

with col1:
    thought = st.text_input("💭 Type insights to control paddle position!", 
                           placeholder="consciousness, love, tralse, myrion...",
                           key="thought_box")
    
    if thought:
        L, E = analyze_thought(thought)
        st.session_state.L = L
        st.session_state.E = E
        st.session_state.thoughts += 1

with col2:
    control_mode = st.radio("Control Mode", ["Mind + Manual", "Manual Only"], 
                            horizontal=True, label_visibility="collapsed")

with col3:
    st.metric("L × E Power", f"{st.session_state.L * st.session_state.E:.2f}")

LxE = st.session_state.L * st.session_state.E
L_value = st.session_state.L
paddle_speed = 4 + int(LxE * 8)
mind_target = int((1 - L_value) * 100)
use_mind = 1 if control_mode == "Mind + Manual" else 0

pcolor = "#ffff00" if LxE >= 0.85 else ("#00ffff" if LxE >= 0.42 else "#44ff88")
state_label = "CAUSATION" if LxE >= 0.85 else ("CONNECTED" if LxE >= 0.42 else "Building")

c1, c2, c3, c4 = st.columns(4)
with c1:
    st.metric("L (Coherence)", f"{L_value:.2f}")
with c2:
    st.metric("E (Coupling)", f"{st.session_state.E:.2f}")
with c3:
    if LxE >= 0.85:
        st.success(f"⚡ {state_label}")
    elif LxE >= 0.42:
        st.info(f"🔗 {state_label}")
    else:
        st.warning(f"📊 {state_label}")
with c4:
    st.caption(f"Thoughts: {st.session_state.thoughts}")

component_key = f"pong_{int(L_value*100)}_{int(st.session_state.E*100)}_{use_mind}"

game_html = f'''
<!DOCTYPE html>
<html>
<head>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ background: transparent; display: flex; flex-direction: column; align-items: center; font-family: Arial, sans-serif; }}
canvas {{ border-radius: 12px; border: 3px solid #555; display: block; }}
#controls {{ display: flex; gap: 15px; margin: 15px 0; }}
.btn {{ padding: 15px 30px; font-size: 18px; font-weight: bold; border: none; border-radius: 8px; cursor: pointer; user-select: none; -webkit-user-select: none; }}
.btn-up, .btn-down {{ background: {pcolor}; color: #000; }}
.btn-pause {{ background: #555; color: white; }}
.btn:active {{ transform: scale(0.95); opacity: 0.8; }}
#info {{ font-size: 13px; color: #888; text-align: center; max-width: 500px; }}
</style>
</head>
<body>
<canvas id="pong" width="600" height="320"></canvas>
<div id="controls">
  <button class="btn btn-up" id="upBtn">⬆️ UP</button>
  <button class="btn btn-pause" id="pauseBtn">⏸️ PAUSE</button>
  <button class="btn btn-down" id="downBtn">⬇️ DOWN</button>
</div>
<div id="info">↑↓ keys or buttons to move | Type insights above to boost speed & control paddle</div>

<script>
const canvas = document.getElementById('pong');
const ctx = canvas.getContext('2d');
const W = 600, H = 320;

const PADDLE_SPEED = {paddle_speed};
const MIND_TARGET = {mind_target} * H / 100;
const USE_MIND = {use_mind};
const PCOLOR = '{pcolor}';

let ball = {{ x: W/2, y: H/2, vx: 3.5, vy: 2, r: 10 }};
let player = {{ y: H/2, h: 70, moving: 0 }};
let ai = {{ y: H/2, h: 55, speed: 2.5 }};
let score = {{ player: 0, ai: 0 }};
let running = true;

document.addEventListener('keydown', (e) => {{
  if (e.key === 'ArrowUp') {{ player.moving = -1; e.preventDefault(); }}
  if (e.key === 'ArrowDown') {{ player.moving = 1; e.preventDefault(); }}
}});
document.addEventListener('keyup', (e) => {{
  if (e.key === 'ArrowUp' && player.moving === -1) player.moving = 0;
  if (e.key === 'ArrowDown' && player.moving === 1) player.moving = 0;
}});

const upBtn = document.getElementById('upBtn');
const downBtn = document.getElementById('downBtn');
const pauseBtn = document.getElementById('pauseBtn');

['mousedown', 'touchstart'].forEach(evt => {{
  upBtn.addEventListener(evt, (e) => {{ e.preventDefault(); player.moving = -1; }});
  downBtn.addEventListener(evt, (e) => {{ e.preventDefault(); player.moving = 1; }});
}});
['mouseup', 'mouseleave', 'touchend', 'touchcancel'].forEach(evt => {{
  upBtn.addEventListener(evt, () => player.moving = 0);
  downBtn.addEventListener(evt, () => player.moving = 0);
}});
pauseBtn.addEventListener('click', () => {{
  running = !running;
  pauseBtn.textContent = running ? '⏸️ PAUSE' : '▶️ PLAY';
}});

function update() {{
  if (!running) return;
  
  if (player.moving !== 0) {{
    player.y += player.moving * PADDLE_SPEED;
  }} else if (USE_MIND) {{
    const diff = MIND_TARGET - player.y;
    if (Math.abs(diff) > 5) {{
      player.y += Math.sign(diff) * Math.min(PADDLE_SPEED * 0.7, Math.abs(diff));
    }}
  }}
  player.y = Math.max(player.h/2 + 5, Math.min(H - player.h/2 - 5, player.y));
  
  const aiDiff = ball.y - ai.y;
  if (Math.abs(aiDiff) > 8) ai.y += Math.sign(aiDiff) * ai.speed;
  ai.y = Math.max(ai.h/2 + 5, Math.min(H - ai.h/2 - 5, ai.y));
  
  ball.x += ball.vx;
  ball.y += ball.vy;
  
  if (ball.y <= ball.r + 5) {{ ball.y = ball.r + 5; ball.vy = Math.abs(ball.vy); }}
  if (ball.y >= H - ball.r - 5) {{ ball.y = H - ball.r - 5; ball.vy = -Math.abs(ball.vy); }}
  
  if (ball.x <= 40 && ball.x >= 25 && ball.vx < 0) {{
    if (Math.abs(ball.y - player.y) < player.h/2 + ball.r) {{
      ball.vx = Math.abs(ball.vx) * 1.03;
      ball.vy += (ball.y - player.y) * 0.08;
      ball.x = 41;
    }}
  }}
  
  if (ball.x >= W - 40 && ball.x <= W - 25 && ball.vx > 0) {{
    if (Math.abs(ball.y - ai.y) < ai.h/2 + ball.r) {{
      ball.vx = -Math.abs(ball.vx) * 1.03;
      ball.vy += (ball.y - ai.y) * 0.08;
      ball.x = W - 41;
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
}}

function resetBall(dir) {{
  ball.x = W/2;
  ball.y = H/2;
  ball.vx = 3.5 * dir;
  ball.vy = (Math.random() - 0.5) * 3;
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
  ctx.arc(W/2, H/2, 35, 0, Math.PI * 2);
  ctx.stroke();
  
  ctx.shadowColor = PCOLOR;
  ctx.shadowBlur = 12;
  ctx.fillStyle = PCOLOR;
  roundRect(ctx, 25, player.y - player.h/2, 12, player.h, 6);
  ctx.fill();
  
  ctx.shadowColor = '#ff5566';
  ctx.fillStyle = '#ff5566';
  roundRect(ctx, W - 37, ai.y - ai.h/2, 12, ai.h, 6);
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
  ctx.fillText('YOU', 22, 25);
  ctx.fillStyle = '#ff5566';
  ctx.fillText('AI', W - 40, 25);
  
  ctx.font = 'bold 26px Arial';
  ctx.fillStyle = 'white';
  ctx.textAlign = 'center';
  ctx.fillText(score.player + ' - ' + score.ai, W/2, 30);
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

components.html(game_html, height=450, key=component_key)

with st.expander("💡 How to Play"):
    st.markdown("""
    **Controls:**
    - **Keyboard**: Hold ↑ or ↓ arrow keys for continuous movement
    - **Buttons**: Hold UP/DOWN buttons (works on mobile too)
    - **Mind Control**: In "Mind + Manual" mode, paddle follows your L value when not pressing keys
    
    **Boost Your Power with GILE Terms:**
    - *consciousness, hyperconnection, gile, tralse, myrion*
    - *love, beautiful, perfect, amazing*
    - *realize, understand, pattern, truth, connection*
    
    **L × E Thresholds:**
    - < 0.42: Building (slow paddle)
    - 0.42-0.85: Connected (good speed)
    - > 0.85: Causation (maximum speed!)
    """)
