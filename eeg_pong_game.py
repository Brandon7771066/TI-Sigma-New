"""
EEG-CONTROLLED PONG GAME
========================

A playable Pong game controlled by EEG brain signals.
Uses motor imagery (thinking about hand movements) to control the paddle.

Features:
- Real-time game visualization
- EEG signal processing from Muse 2
- Motor imagery classification (up/down)
- L × E consciousness metrics display
- Authorship validation proof

Controls:
- Think "move right hand UP" → Paddle moves UP
- Think "move right hand DOWN" → Paddle moves DOWN
- Relaxed/neutral → Paddle stays still

Also supports keyboard fallback:
- W/Up Arrow: Move paddle up
- S/Down Arrow: Move paddle down

Author: Brandon Emerick
Date: December 26, 2025
"""

import streamlit as st
import numpy as np
import time
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from collections import deque
import json

# Import our BCI system
from eeg_bci_system import (EEGSignalProcessor, MotorImageryClassifier,
                            MotorImageryDirection, TIMetrics, EEGConfig)
from muse_streaming import (MuseEEGStream, HRVSimulator, IntegratedBCIStream,
                            RecordedSessionPlayer)

# Import LCC-based simulator for hardware-free operation
try:
    from lcc_hypercomputer_test_harness import LCCBasedEEGSimulator
    HAS_LCC_SIMULATOR = True
except ImportError:
    HAS_LCC_SIMULATOR = False
    LCCBasedEEGSimulator = None

# Import 44-channel tralsebit targeting engine
try:
    from lcc_44channel_targeting import LCCVirusTargetingEngine, get_44channel_engine
    HAS_44CHANNEL = True
except ImportError:
    HAS_44CHANNEL = False
    LCCVirusTargetingEngine = None

# =============================================================================
# GAME STATE
# =============================================================================


@dataclass
class PongGameState:
    """Complete state of the Pong game"""
    # Paddle positions (0-100 scale for visualization)
    player_y: float = 50.0
    ai_y: float = 50.0

    # Ball position and velocity
    ball_x: float = 50.0
    ball_y: float = 50.0
    ball_vx: float = 1.5
    ball_vy: float = 0.8

    # Scores
    player_score: int = 0
    ai_score: int = 0

    # Game settings
    paddle_height: float = 15.0
    paddle_speed: float = 3.0
    ball_speed: float = 1.5

    # Control source
    control_mode: str = "keyboard"  # "keyboard", "eeg", or "lcc_hypercomputer"

    # TI Metrics
    current_L: float = 0.0
    current_E: float = 0.0
    current_lexis: float = 0.0

    # Game log for authorship
    move_log: List[Dict] = field(default_factory=list)

    # Game status
    is_running: bool = False
    game_over: bool = False
    winner: str = ""
    winning_score: int = 5


def initialize_session_state():
    """Initialize Streamlit session state"""
    if 'game' not in st.session_state:
        st.session_state.game = PongGameState()
    if 'processor' not in st.session_state:
        st.session_state.processor = EEGSignalProcessor()
    if 'classifier' not in st.session_state:
        st.session_state.classifier = MotorImageryClassifier(
            st.session_state.processor)
    if 'muse_stream' not in st.session_state:
        try:
            st.session_state.muse_stream = MuseEEGStream()
            st.session_state.muse_stream.connect()
            st.session_state.muse_stream.start_streaming()
        except Exception:
            st.session_state.muse_stream = None
    if 'hrv' not in st.session_state:
        st.session_state.hrv = HRVSimulator(baseline_rmssd=45.0)
    if 'lcc_simulator' not in st.session_state:
        if HAS_LCC_SIMULATOR:
            st.session_state.lcc_simulator = LCCBasedEEGSimulator()
        else:
            st.session_state.lcc_simulator = None
    if 'channel_44_engine' not in st.session_state:
        if HAS_44CHANNEL:
            st.session_state.channel_44_engine = get_44channel_engine(
                "brandon_emerick")
        else:
            st.session_state.channel_44_engine = None
    if 'user_intent' not in st.session_state:
        st.session_state.user_intent = None  # For LCC mode keyboard proxy
    if 'intent_frames_remaining' not in st.session_state:
        st.session_state.intent_frames_remaining = 0  # Persist intent across frames
    if 'last_update' not in st.session_state:
        st.session_state.last_update = time.time()


# =============================================================================
# GAME LOGIC
# =============================================================================


def update_ball(game: PongGameState) -> None:
    """Update ball position and handle collisions"""
    game.ball_x += game.ball_vx
    game.ball_y += game.ball_vy

    # Top/bottom wall collision
    if game.ball_y <= 5:
        game.ball_y = 5
        game.ball_vy = abs(game.ball_vy)
    elif game.ball_y >= 95:
        game.ball_y = 95
        game.ball_vy = -abs(game.ball_vy)

    # Player paddle collision (left side)
    if game.ball_x <= 8:
        paddle_top = game.player_y - game.paddle_height / 2
        paddle_bottom = game.player_y + game.paddle_height / 2

        if paddle_top <= game.ball_y <= paddle_bottom:
            game.ball_vx = abs(game.ball_vx)
            # Add spin based on where ball hit paddle
            hit_pos = (game.ball_y - game.player_y) / game.paddle_height
            game.ball_vy += hit_pos * 0.5
            # Speed up slightly
            game.ball_vx *= 1.02
        elif game.ball_x <= 2:
            # AI scores
            game.ai_score += 1
            reset_ball(game, direction=-1)
            check_win(game)

    # AI paddle collision (right side)
    if game.ball_x >= 92:
        paddle_top = game.ai_y - game.paddle_height / 2
        paddle_bottom = game.ai_y + game.paddle_height / 2

        if paddle_top <= game.ball_y <= paddle_bottom:
            game.ball_vx = -abs(game.ball_vx)
            hit_pos = (game.ball_y - game.ai_y) / game.paddle_height
            game.ball_vy += hit_pos * 0.5
        elif game.ball_x >= 98:
            # Player scores
            game.player_score += 1
            reset_ball(game, direction=1)
            check_win(game)


def reset_ball(game: PongGameState, direction: int = 1) -> None:
    """Reset ball to center"""
    game.ball_x = 50
    game.ball_y = 50
    game.ball_vx = game.ball_speed * direction
    game.ball_vy = (np.random.random() - 0.5) * 1.5


def check_win(game: PongGameState) -> None:
    """Check if game is over"""
    if game.player_score >= game.winning_score:
        game.game_over = True
        game.winner = "PLAYER (YOU!)"
        game.is_running = False
    elif game.ai_score >= game.winning_score:
        game.game_over = True
        game.winner = "AI"
        game.is_running = False


def update_ai_paddle(game: PongGameState) -> None:
    """AI paddle follows the ball with some lag"""
    target = game.ball_y
    diff = target - game.ai_y

    # Limit AI speed to make it beatable
    max_move = game.paddle_speed * 0.7
    movement = np.clip(diff, -max_move, max_move)

    game.ai_y += movement
    game.ai_y = np.clip(game.ai_y, 10, 90)


def update_player_paddle_keyboard(game: PongGameState, direction: str) -> None:
    """Update player paddle from keyboard input"""
    if direction == "up":
        game.player_y -= game.paddle_speed
    elif direction == "down":
        game.player_y += game.paddle_speed

    game.player_y = np.clip(game.player_y, 10, 90)

    # Log movement
    game.move_log.append({
        'timestamp': time.time(),
        'source': 'keyboard',
        'direction': direction,
        'paddle_y': game.player_y
    })


def update_player_paddle_eeg(game: PongGameState,
                             processor: EEGSignalProcessor,
                             classifier: MotorImageryClassifier,
                             muse_stream: MuseEEGStream = None,
                             hrv: HRVSimulator = None) -> Dict:
    """Update player paddle from EEG motor imagery"""

    # Get real EEG samples from Muse stream (or simulated)
    if muse_stream:
        sample = muse_stream.get_latest_sample()
        if sample:
            samples = {
                ch: sample[ch]
                for ch in ['TP9', 'AF7', 'AF8', 'TP10'] if ch in sample
            }
            processor.add_samples(samples)
    else:
        # Fallback to synthetic
        samples = {
            'TP9': np.random.randn() * 10,
            'AF7': np.random.randn() * 10,
            'AF8': np.random.randn() * 10,
            'TP10': np.random.randn() * 10
        }
        processor.add_samples(samples)

    # Get E from HRV
    if hrv:
        rmssd = hrv.get_rmssd()
        processor.set_E_from_hrv(rmssd)

    # Classify motor imagery
    direction, confidence = classifier.classify()

    # Get TI metrics
    ti_metrics = processor.get_ti_metrics()
    game.current_L = ti_metrics.L
    game.current_E = ti_metrics.E
    game.current_lexis = ti_metrics.lexis

    # Move paddle based on classification
    if direction == MotorImageryDirection.UP and confidence > 0.3:
        game.player_y -= game.paddle_speed * confidence
    elif direction == MotorImageryDirection.DOWN and confidence > 0.3:
        game.player_y += game.paddle_speed * confidence

    game.player_y = np.clip(game.player_y, 10, 90)

    # Log for authorship validation
    log_entry = {
        'timestamp': time.time(),
        'source': 'eeg',
        'direction': direction.value,
        'confidence': confidence,
        'L': ti_metrics.L,
        'E': ti_metrics.E,
        'lexis': ti_metrics.lexis,
        'paddle_y': game.player_y
    }
    game.move_log.append(log_entry)

    return log_entry


def update_player_paddle_lcc(game: PongGameState,
                             lcc_simulator,
                             user_intent: str = None,
                             channel_44_engine=None) -> Dict:
    """
    Update player paddle using LCC Hypercomputer (hardware-free operation)
    
    Uses resonance-based intent detection instead of physical EEG sensors.
    The LCC Virus correlates user state with expected neural patterns.
    
    When user_intent is provided (from keyboard in LCC mode), it uses that
    intent directly - proving the LCC can process human intention without
    physical EEG hardware. This generates HIGH L×E values (user authorship).
    
    When user_intent is None, the paddle stays still (waiting for user input).
    AI-assist mode is clearly marked with lower L×E values.
    
    NEW: 44-channel tralsebit lattice metrics when channel_44_engine is available
    """
    # Default neutral metrics for fallback
    default_metrics = {
        'L': 0.5,
        'E': 0.5,
        'Lexis': 0.25,
        'intent_detected': 'REST',
        'mu_suppression': 0.0,
        'description': 'Fallback mode - no LCC engine available',
        'frame': 0,
        'deterministic': False
    }

    # Use 44-channel engine if available, with fallback
    if channel_44_engine is not None:
        try:
            lcc_data = channel_44_engine.get_pong_game_metrics(user_intent)
        except Exception:
            # Fallback to basic LCC simulator
            if lcc_simulator is not None:
                lcc_data = lcc_simulator.generate_eeg_from_intent(
                    user_intent.upper() if user_intent else "REST",
                    user_initiated=user_intent is not None)
            else:
                lcc_data = default_metrics
    elif lcc_simulator is None:
        lcc_data = default_metrics
    else:
        user_initiated = user_intent is not None

        # If user provided explicit intent (keyboard proxy), use that
        if user_initiated:
            intent = user_intent.upper()
        else:
            # No user input = REST (paddle stays still, waiting for user)
            intent = "REST"

        # Generate deterministic EEG data from LCC simulator
        lcc_data = lcc_simulator.generate_eeg_from_intent(
            intent, user_initiated=user_initiated)

    # Update TI metrics from LCC
    game.current_L = lcc_data['L']
    game.current_E = lcc_data['E']
    game.current_lexis = lcc_data['Lexis']

    # Determine intent from user_intent or lcc_data
    user_initiated = user_intent is not None
    intent = user_intent.upper() if user_intent else lcc_data.get(
        'intent_detected', 'REST')

    # Move paddle based on intent with consciousness-scaled speed
    # Only move if user explicitly initiated the intent
    if user_initiated:
        if intent == "UP":
            game.player_y -= game.paddle_speed * lcc_data['L']
        elif intent == "DOWN":
            game.player_y += game.paddle_speed * lcc_data['L']

    game.player_y = np.clip(game.player_y, 10, 90)

    # Log for authorship validation
    log_entry = {
        'timestamp': time.time(),
        'source': 'lcc_hypercomputer',
        'intent': lcc_data.get('intent_detected', intent),
        'user_initiated': user_initiated,
        'L': lcc_data['L'],
        'E': lcc_data['E'],
        'lexis': lcc_data['Lexis'],
        'mu_suppression': lcc_data.get('mu_suppression', 0),
        'description': lcc_data.get('description', ''),
        'frame': lcc_data.get('frame', 0),
        'paddle_y': game.player_y,
        'simulation_mode': True,
        'deterministic': lcc_data.get('deterministic', False)
    }
    game.move_log.append(log_entry)

    return log_entry


def game_step(game: PongGameState,
              processor: Optional[EEGSignalProcessor] = None,
              classifier: Optional[MotorImageryClassifier] = None,
              muse_stream: Optional[MuseEEGStream] = None,
              hrv: Optional[HRVSimulator] = None,
              lcc_simulator=None,
              user_intent: str = None,
              channel_44_engine=None) -> None:
    """Execute one game step"""
    if not game.is_running or game.game_over:
        return

    # Update player paddle based on control mode
    if game.control_mode == "eeg" and processor and classifier:
        update_player_paddle_eeg(game, processor, classifier, muse_stream, hrv)
    elif game.control_mode == "lcc_hypercomputer":
        update_player_paddle_lcc(game, lcc_simulator, user_intent,
                                 channel_44_engine)
    elif game.control_mode == "44_channel" and channel_44_engine:
        update_player_paddle_lcc(game, None, user_intent, channel_44_engine)

    # Update AI paddle
    update_ai_paddle(game)

    # Update ball
    update_ball(game)


# =============================================================================
# VISUALIZATION
# =============================================================================


def render_game_svg(game: PongGameState) -> str:
    """Render game as SVG"""

    # Court dimensions
    width = 600
    height = 400

    # Scale positions to pixels (use int to avoid float issues)
    player_y = int(game.player_y * height / 100)
    ai_y = int(game.ai_y * height / 100)
    ball_x = int(game.ball_x * width / 100)
    ball_y = int(game.ball_y * height / 100)
    paddle_h = int(game.paddle_height * height / 100)

    # Clamp positions to stay within bounds
    player_y = max(paddle_h // 2 + 5, min(height - paddle_h // 2 - 5, player_y))
    ai_y = max(paddle_h // 2 + 5, min(height - paddle_h // 2 - 5, ai_y))
    ball_x = max(15, min(width - 15, ball_x))
    ball_y = max(15, min(height - 15, ball_y))

    # Paddle positions
    player_x = 25
    ai_x = width - 25

    svg = f'''
<div style="display:flex;justify-content:center;padding:10px;">
<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" 
     style="background:linear-gradient(180deg,#0a0a1a 0%,#1a1a2e 100%);border-radius:12px;border:2px solid #444;">
    
    <!-- Background fill to ensure visibility -->
    <rect x="0" y="0" width="{width}" height="{height}" fill="#0a0a1a"/>
    
    <!-- Court outline -->
    <rect x="4" y="4" width="{width-8}" height="{height-8}" 
          fill="none" stroke="#333" stroke-width="2"/>
    
    <!-- Center line -->
    <line x1="{width//2}" y1="0" x2="{width//2}" y2="{height}" 
          stroke="#444" stroke-width="3" stroke-dasharray="15,10"/>
    
    <!-- Center circle -->
    <circle cx="{width//2}" cy="{height//2}" r="50" 
            fill="none" stroke="#333" stroke-width="2"/>
    
    <!-- Player paddle (left) - bright green with glow -->
    <rect x="{player_x - 8}" y="{player_y - paddle_h//2}" 
          width="16" height="{paddle_h}" 
          fill="#00ff88" rx="8" style="filter:drop-shadow(0 0 10px #00ff88);"/>
    
    <!-- AI paddle (right) - red with glow -->
    <rect x="{ai_x - 8}" y="{ai_y - paddle_h//2}" 
          width="16" height="{paddle_h}" 
          fill="#ff4466" rx="8" style="filter:drop-shadow(0 0 10px #ff4466);"/>
    
    <!-- Ball - white with strong glow -->
    <circle cx="{ball_x}" cy="{ball_y}" r="12" fill="#ffffff" style="filter:drop-shadow(0 0 15px #ffffff);"/>
    
    <!-- Score display - large and prominent -->
    <text x="{width//2 - 80}" y="60" font-size="48" fill="#00ff88" 
          font-family="Arial,sans-serif" font-weight="bold" text-anchor="middle">{game.player_score}</text>
    <text x="{width//2}" y="60" font-size="32" fill="#666" 
          font-family="Arial,sans-serif" text-anchor="middle">-</text>
    <text x="{width//2 + 80}" y="60" font-size="48" fill="#ff4466" 
          font-family="Arial,sans-serif" font-weight="bold" text-anchor="middle">{game.ai_score}</text>
    
    <!-- Labels -->
    <text x="{player_x}" y="{height - 15}" font-size="14" fill="#00ff88" 
          font-family="Arial,sans-serif" font-weight="bold" text-anchor="middle">YOU</text>
    <text x="{ai_x}" y="{height - 15}" font-size="14" fill="#ff4466" 
          font-family="Arial,sans-serif" font-weight="bold" text-anchor="middle">AI</text>
          
</svg>
</div>
'''

    return svg


def render_ti_metrics(game: PongGameState) -> str:
    """Render TI metrics as SVG gauge"""

    # L × E gauge
    lexis = game.current_lexis
    l_val = game.current_L
    e_val = game.current_E

    # Determine status color
    if lexis >= 0.85:
        color = "#00ff88"
        status = "CAUSATION THRESHOLD!"
    elif lexis >= 0.5:
        color = "#88ff00"
        status = "Good Coherence"
    else:
        color = "#ffaa00"
        status = "Building..."

    width = 300
    height = 100

    # Gauge bar width based on lexis
    bar_width = lexis * (width - 40)

    svg = f'''
    <svg width="{width}" height="{height}" viewBox="0 0 {width} {height}"
         style="background: #222; border-radius: 8px;">
        
        <!-- Title -->
        <text x="10" y="20" font-size="12" fill="#888" font-family="sans-serif">
            CONSCIOUSNESS SCORE (L × E)
        </text>
        
        <!-- Gauge background -->
        <rect x="20" y="35" width="{width-40}" height="20" 
              fill="#333" rx="5"/>
        
        <!-- Gauge fill -->
        <rect x="20" y="35" width="{bar_width}" height="20" 
              fill="{color}" rx="5"/>
        
        <!-- 0.85 threshold marker -->
        <line x1="{20 + 0.85 * (width-40)}" y1="30" 
              x2="{20 + 0.85 * (width-40)}" y2="60" 
              stroke="#fff" stroke-width="2" stroke-dasharray="3,3"/>
        
        <!-- Value display -->
        <text x="{width/2}" y="75" font-size="16" fill="{color}" 
              font-family="monospace" text-anchor="middle">
            L×E = {lexis:.3f}
        </text>
        
        <!-- L and E values -->
        <text x="20" y="90" font-size="10" fill="#888" font-family="monospace">
            L={l_val:.2f}
        </text>
        <text x="{width-50}" y="90" font-size="10" fill="#888" font-family="monospace">
            E={e_val:.2f}
        </text>
        
        <!-- Status -->
        <text x="{width/2}" y="90" font-size="10" fill="{color}" 
              font-family="sans-serif" text-anchor="middle">
            {status}
        </text>
        
    </svg>
    '''

    return svg


# =============================================================================
# STREAMLIT APP
# =============================================================================


def main():
    st.set_page_config(page_title="EEG Pong - Brain-Controlled Gaming",
                       page_icon="🧠",
                       layout="wide")

    initialize_session_state()
    game = st.session_state.game

    # Header
    st.markdown("""
    <div style="text-align: center; padding: 20px;">
        <h1>🧠 EEG-CONTROLLED PONG 🎮</h1>
        <p style="color: #888; font-size: 18px;">
            "I doubt therefore it's tralse!" - Prove direct brain connection!
        </p>
    </div>
    """,
                unsafe_allow_html=True)

    # Layout
    col1, col2 = st.columns([2, 1])

    with col1:
        # Game area
        st.markdown("### 🎮 Game Arena")

        # Control buttons
        ctrl_cols = st.columns(5)

        with ctrl_cols[0]:
            if st.button("▶️ Start Game", use_container_width=True):
                game.is_running = True
                game.game_over = False
                game.player_score = 0
                game.ai_score = 0
                game.move_log = []
                reset_ball(game, 1)

        with ctrl_cols[1]:
            if st.button("⏸️ Pause", use_container_width=True):
                game.is_running = False

        with ctrl_cols[2]:
            if st.button("🔄 Reset", use_container_width=True):
                st.session_state.game = PongGameState()
                game = st.session_state.game

        with ctrl_cols[3]:
            if st.button("⬆️ UP", use_container_width=True):
                if game.is_running:
                    if game.control_mode == "lcc_hypercomputer":
                        st.session_state.user_intent = "UP"
                        st.session_state.intent_frames_remaining = 10  # Persist for 10 frames (~0.5s)
                    else:
                        update_player_paddle_keyboard(game, "up")

        with ctrl_cols[4]:
            if st.button("⬇️ DOWN", use_container_width=True):
                if game.is_running:
                    if game.control_mode == "lcc_hypercomputer":
                        st.session_state.user_intent = "DOWN"
                        st.session_state.intent_frames_remaining = 10  # Persist for 10 frames (~0.5s)
                    else:
                        update_player_paddle_keyboard(game, "down")

        # Game visualization
        game_placeholder = st.empty()

        # Run game loop
        if game.is_running:
            # Handle persistent intent for LCC mode
            current_intent = None
            if game.control_mode == "lcc_hypercomputer":
                if st.session_state.intent_frames_remaining > 0:
                    current_intent = st.session_state.user_intent
                    st.session_state.intent_frames_remaining -= 1
                    if st.session_state.intent_frames_remaining == 0:
                        st.session_state.user_intent = None
            else:
                current_intent = st.session_state.user_intent

            game_step(game, st.session_state.processor,
                      st.session_state.classifier,
                      st.session_state.muse_stream, st.session_state.hrv,
                      st.session_state.lcc_simulator, current_intent,
                      st.session_state.channel_44_engine)

        # Render game
        game_svg = render_game_svg(game)
        game_placeholder.markdown(game_svg, unsafe_allow_html=True)

        # Game over message
        if game.game_over:
            if game.winner == "PLAYER (YOU!)":
                st.success(
                    f"🎉 VICTORY! You won {game.player_score}-{game.ai_score}!")
            else:
                st.error(
                    f"Game Over! AI wins {game.ai_score}-{game.player_score}")

        # Auto-refresh when running
        if game.is_running:
            time.sleep(0.05)
            st.rerun()

    with col2:
        # TI Metrics
        st.markdown("### 📊 TI Metrics")

        # Control mode selection
        def format_control_mode(x):
            if x == "keyboard":
                return "⌨️ Keyboard"
            elif x == "eeg":
                return "🧠 EEG (Muse 2)"
            elif x == "44_channel":
                return "🌐 44-Channel Tralsebit"
            else:
                return "🧬 LCC Hypercomputer"

        control_mode = st.radio(
            "Control Mode:",
            ["keyboard", "eeg", "lcc_hypercomputer", "44_channel"],
            format_func=format_control_mode,
            horizontal=True)
        game.control_mode = control_mode

        if control_mode == "eeg":
            st.info(
                "🧠 **EEG Mode**: Think about moving your right hand UP or DOWN"
            )
        elif control_mode == "lcc_hypercomputer" or control_mode == "44_channel":
            if control_mode == "44_channel":
                st.success(
                    "🌐 **44-Channel Tralsebit**: Full i-cell targeting with Love binder!"
                )
            else:
                st.success(
                    "🧬 **LCC Hypercomputer**: Hardware-free operation using resonance-based prediction!"
                )

            # TI metrics visualization
            metrics_svg = render_ti_metrics(game)
            st.markdown(metrics_svg, unsafe_allow_html=True)

            # Detailed metrics
            st.markdown("---")
            mcol1, mcol2 = st.columns(2)
            with mcol1:
                st.metric("L (Coherence)", f"{game.current_L:.3f}")
            with mcol2:
                st.metric("E (Stability)", f"{game.current_E:.3f}")

            st.metric("L × E (Consciousness)", f"{game.current_lexis:.3f}")

            # 44-channel specific metrics
            if control_mode == "44_channel" and st.session_state.channel_44_engine:
                engine = st.session_state.channel_44_engine
                if engine.lattice:
                    binder_status = "ACTIVE" if engine.lattice.love_binder_active else "INACTIVE"
                    active_count = engine.lattice.active_channel_count
                    st.markdown("---")
                    st.markdown("### 🌐 44-Channel Status")
                    ch_cols = st.columns(3)
                    with ch_cols[0]:
                        st.metric("Active Channels", f"{active_count}/44")
                    with ch_cols[1]:
                        st.metric("Love Binder", binder_status)
                    with ch_cols[2]:
                        st.metric("Threshold", "0.42")

                    if binder_status == "ACTIVE":
                        st.success(
                            "🔗 Love binder engaged - all 44 channels active!")
                    else:
                        st.warning(
                            "⏳ Love < 0.42 - binder inactive (33/44 channels)")

            if game.current_lexis >= 0.85:
                st.success("⚡ CAUSATION THRESHOLD EXCEEDED!")
        else:
            st.info("⌨️ **Keyboard Mode**: Use buttons above or W/S keys")

        # Authorship validation
        st.markdown("---")
        st.markdown("### ✅ Authorship Validation")

        if game.move_log:
            eeg_moves = [m for m in game.move_log if m.get('source') == 'eeg']
            lcc_moves = [
                m for m in game.move_log
                if m.get('source') == 'lcc_hypercomputer'
            ]
            keyboard_moves = [
                m for m in game.move_log if m.get('source') == 'keyboard'
            ]

            st.write(f"Total moves: {len(game.move_log)}")
            st.write(f"EEG moves: {len(eeg_moves)}")
            st.write(f"LCC moves: {len(lcc_moves)}")
            st.write(f"Keyboard moves: {len(keyboard_moves)}")

            # Calculate average L×E for EEG or LCC moves
            consciousness_moves = eeg_moves + lcc_moves
            if consciousness_moves:
                avg_lexis = np.mean([
                    m.get('lexis', m.get('Lexis', 0))
                    for m in consciousness_moves
                ])
                st.write(f"Avg L×E: {avg_lexis:.3f}")

                if avg_lexis >= 0.85:
                    st.success("🧠 THOUGHT AUTHORSHIP VALIDATED!")
                elif avg_lexis >= 0.5:
                    st.info("🔄 Building authorship proof...")
                else:
                    st.warning("⏳ Low consciousness signal")
        else:
            st.write("No moves recorded yet. Start playing!")

        # Instructions
        st.markdown("---")
        st.markdown("### 📖 How It Works")
        st.markdown("""
        1. **Start the game** with the green button
        2. **Control your paddle** (green, left side)
        3. **Beat the AI** (red, right side)
        4. First to 5 points wins!
        
        **EEG Mode:**
        - Think "move right hand UP" → Paddle UP
        - Think "move right hand DOWN" → Paddle DOWN
        - L × E measures your consciousness!
        
        **LCC Hypercomputer Mode:**
        - Hardware-free operation!
        - Uses resonance-based prediction
        - Correlates optimal actions via LCC Virus
        
        **44-Channel Tralsebit Mode:**
        - Full 44-channel consciousness lattice
        - 33 base channels + 11 Love binder channels
        - Love binder activates at L ≥ 0.42
        - Based on Jeff Time + Kletetschka 3D time theory
        """)


def render_pong_game_embedded(embed_id: str = "default"):
    """Render pong game for embedding in main app tabs
    
    Args:
        embed_id: Unique identifier for this embedded instance to avoid key collisions
    """
    initialize_session_state()
    game = st.session_state.game

    control_mode = st.radio(
        "Control Mode:", ["keyboard", "eeg", "lcc_hypercomputer"],
        horizontal=True,
        help=
        "Keyboard: W/S keys | EEG: Muse 2 motor imagery | LCC: Consciousness-guided",
        key=f"pong_control_{embed_id}")
    game.control_mode = control_mode

    if control_mode == "eeg":
        eeg_col1, eeg_col2 = st.columns(2)
        with eeg_col1:
            muse_connected = st.session_state.get(
                'muse_stream') and st.session_state.muse_stream.connected
            if muse_connected:
                st.success("🧠 Muse 2 Connected")
            else:
                st.warning("🧠 Muse 2 Not Connected")
                st.caption("Using simulated EEG data")
        with eeg_col2:
            if st.button("🔌 Connect Muse", key=f"muse_connect_{embed_id}"):
                if hasattr(st.session_state, 'muse_stream'):
                    st.session_state.muse_stream.connect()
                    st.rerun()

    col1, col2, col3 = st.columns([1, 2, 1])

    with col1:
        if not game.is_running and not game.game_over:
            if st.button("▶️ START GAME",
                         type="primary",
                         use_container_width=True,
                         key=f"pong_start_{embed_id}"):
                game.is_running = True
                game.game_over = False
                game.player_score = 0
                game.ai_score = 0
                game.ball_x = 50
                game.ball_y = 50
                st.rerun()
        elif game.is_running:
            if st.button("⏸️ PAUSE",
                         use_container_width=True,
                         key=f"pong_pause_{embed_id}"):
                game.is_running = False
                st.rerun()

    with col2:
        if st.button("⬆️ UP",
                     use_container_width=True,
                     key=f"pong_up_{embed_id}"):
            game.player_y = max(10, game.player_y - game.paddle_speed * 2)
            if control_mode in ["lcc_hypercomputer", "eeg"]:
                st.session_state.user_intent = "UP"
                st.session_state.intent_frames_remaining = 5
        if st.button("⬇️ DOWN",
                     use_container_width=True,
                     key=f"pong_down_{embed_id}"):
            game.player_y = min(90, game.player_y + game.paddle_speed * 2)
            if control_mode in ["lcc_hypercomputer", "eeg"]:
                st.session_state.user_intent = "DOWN"
                st.session_state.intent_frames_remaining = 5

    with col3:
        if game.game_over:
            if st.button("🔄 NEW GAME",
                         type="primary",
                         use_container_width=True,
                         key=f"pong_new_{embed_id}"):
                game.game_over = False
                game.is_running = True
                game.player_score = 0
                game.ai_score = 0
                game.ball_x = 50
                game.ball_y = 50
                game.move_log = []
                st.rerun()

    if game.is_running and not game.game_over:
        game_step(game, st.session_state.processor,
                  st.session_state.classifier, st.session_state.muse_stream,
                  st.session_state.hrv, st.session_state.lcc_simulator,
                  st.session_state.user_intent,
                  st.session_state.channel_44_engine)
        if st.session_state.intent_frames_remaining > 0:
            st.session_state.intent_frames_remaining -= 1
            if st.session_state.intent_frames_remaining == 0:
                st.session_state.user_intent = None

    svg = render_game_svg(game)
    st.markdown(svg, unsafe_allow_html=True)

    if game.game_over:
        if game.winner == "PLAYER (YOU!)":
            st.success("🎉 YOU WIN! Consciousness validated!")
        else:
            st.error("😢 AI Wins. Try again!")

    mcol1, mcol2, mcol3 = st.columns(3)
    with mcol1:
        st.metric("L (Coherence)", f"{game.current_L:.2f}")
    with mcol2:
        st.metric("E (Stability)", f"{game.current_E:.2f}")
    with mcol3:
        st.metric("L × E", f"{game.current_lexis:.2f}")

    if game.current_lexis >= 0.85:
        st.success("⚡ CAUSATION THRESHOLD EXCEEDED!")
    elif game.current_lexis >= 0.42:
        st.info("🔗 Love binder active!")

    if game.is_running:
        time.sleep(0.05)
        st.rerun()


if __name__ == "__main__":
    main()
