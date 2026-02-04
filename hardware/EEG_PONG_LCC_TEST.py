#!/usr/bin/env python3
"""
EEG PONG - LCC (Luminated Consciousness Correlation) Test
=========================================================
Control Pong with your Muse 2 EEG headband!

PROTOCOL:
1. Phase 1 (WITH MUSE): Play normally, establish control
2. Phase 2 (LCC TEST): Remove Muse, continue playing with intention
3. If paddle still responds -> LCC CONFIRMED!

CONTROLS:
- Alpha dominance = Paddle UP (relaxed state)
- Beta dominance = Paddle DOWN (focused state)

REQUIREMENTS:
pip install pygame-ce bleak numpy

Run: python EEG_PONG_LCC_TEST.py
"""

import pygame
import numpy as np
import time
import csv
import sys
from datetime import datetime
from collections import deque
import threading

# =============================================================================
# GAME SETTINGS
# =============================================================================
SCREEN_WIDTH = 800
SCREEN_HEIGHT = 600
PADDLE_WIDTH = 15
PADDLE_HEIGHT = 100
BALL_SIZE = 15
FPS = 60

# Colors
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0)
RED = (255, 100, 100)
BLUE = (100, 100, 255)
YELLOW = (255, 255, 0)
PURPLE = (200, 100, 255)
CYAN = (0, 255, 255)

# EEG Control Settings
CONTROL_SENSITIVITY = 8
SMOOTHING_WINDOW = 10

# =============================================================================
# GLOBAL STATE
# =============================================================================
class GameState:
    def __init__(self):
        # EEG Data
        self.alpha = 0.0
        self.beta = 0.0
        self.theta = 0.0
        self.gamma = 0.0
        self.delta = 0.0
        
        # Control signal
        self.control_signal = 0.0
        self.control_history = deque(maxlen=SMOOTHING_WINDOW)
        
        # Game state
        self.player_score = 0
        self.ai_score = 0
        self.player_y = SCREEN_HEIGHT // 2
        self.ai_y = SCREEN_HEIGHT // 2
        self.ball_x = SCREEN_WIDTH // 2
        self.ball_y = SCREEN_HEIGHT // 2
        self.ball_dx = 5
        self.ball_dy = 3
        
        # Mode
        self.muse_connected = False
        self.lcc_mode = False
        self.lcc_start_time = None
        self.ble_thread = None
        self.ble_running = False
        
        # Logging
        self.log_data = []
        self.session_start = datetime.now()
        
        # Raw EEG buffer for FFT
        self.eeg_buffer = {
            'TP9': deque(maxlen=256),
            'AF7': deque(maxlen=256),
            'AF8': deque(maxlen=256),
            'TP10': deque(maxlen=256)
        }
        
        # Statistics
        self.total_hits = 0
        self.lcc_hits = 0
        self.last_control_before_lcc = 0.0

state = GameState()

# =============================================================================
# EEG PROCESSING
# =============================================================================
def compute_band_powers(samples, fs=256):
    """Compute band powers from EEG samples using FFT."""
    if len(samples) < 64:
        return {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
    
    samples = np.array(samples)
    samples = samples - np.mean(samples)
    
    window = np.hanning(len(samples))
    samples = samples * window
    
    fft = np.fft.rfft(samples)
    freqs = np.fft.rfftfreq(len(samples), 1/fs)
    power = np.abs(fft) ** 2
    
    bands = {
        'delta': (0.5, 4),
        'theta': (4, 8),
        'alpha': (8, 13),
        'beta': (13, 30),
        'gamma': (30, 50)
    }
    
    band_powers = {}
    for band, (low, high) in bands.items():
        mask = (freqs >= low) & (freqs < high)
        if np.any(mask):
            band_powers[band] = np.log10(np.mean(power[mask]) + 1e-10)
        else:
            band_powers[band] = 0
    
    return band_powers

def update_control_signal():
    """Calculate control signal from EEG bands."""
    af7_powers = compute_band_powers(list(state.eeg_buffer['AF7']))
    af8_powers = compute_band_powers(list(state.eeg_buffer['AF8']))
    
    state.alpha = (af7_powers['alpha'] + af8_powers['alpha']) / 2
    state.beta = (af7_powers['beta'] + af8_powers['beta']) / 2
    state.theta = (af7_powers['theta'] + af8_powers['theta']) / 2
    state.gamma = (af7_powers['gamma'] + af8_powers['gamma']) / 2
    
    if abs(state.beta) > 0.01:
        ab_ratio = state.alpha / (abs(state.beta) + 0.01)
    else:
        ab_ratio = 1.0
    
    raw_signal = (ab_ratio - 1.25) / 1.25
    raw_signal = max(-1, min(1, raw_signal))
    
    state.control_history.append(raw_signal)
    state.control_signal = float(np.mean(list(state.control_history)))

# =============================================================================
# MUSE BLE CONNECTION (Separate Thread)
# =============================================================================
def ble_thread_main():
    """Run BLE in separate thread with its own event loop."""
    import asyncio
    
    try:
        from bleak import BleakClient, BleakScanner
    except ImportError:
        print("bleak not installed!")
        return
    
    # Muse UUIDs
    CONTROL_CHAR = "273e0001-4c4d-454d-96be-f03bac821358"
    EEG_CHAR = "273e0003-4c4d-454d-96be-f03bac821358"
    
    def parse_eeg(data):
        """Parse raw EEG packet from Muse."""
        if len(data) < 12:
            return
        
        try:
            samples = []
            for i in range(12):
                byte_idx = 1 + (i * 3) // 2
                if byte_idx + 1 < len(data):
                    if i % 2 == 0:
                        val = ((data[byte_idx] << 4) | (data[byte_idx + 1] >> 4)) & 0xFFF
                    else:
                        val = ((data[byte_idx] & 0x0F) << 8) | data[byte_idx + 1]
                    uv = (val - 2048) * 0.48828125
                    samples.append(uv)
            
            channels = ['TP9', 'AF7', 'AF8', 'TP10']
            for ch_idx, ch in enumerate(channels):
                for s in range(3):
                    if ch_idx * 3 + s < len(samples):
                        state.eeg_buffer[ch].append(samples[ch_idx * 3 + s])
            
            if len(state.eeg_buffer['AF7']) >= 64:
                update_control_signal()
                
        except Exception as e:
            pass
    
    async def notification_handler(sender, data):
        parse_eeg(bytes(data))
    
    async def connect_and_stream():
        print("Scanning for Muse 2...")
        
        devices = await BleakScanner.discover(timeout=10)
        muse_device = None
        
        for d in devices:
            name = d.name or ""
            if "Muse" in name:
                muse_device = d
                print(f"Found: {name}")
                break
        
        if not muse_device:
            print("No Muse found! Running in DEMO mode.")
            return
        
        try:
            async with BleakClient(muse_device.address) as client:
                print(f"Connected to {muse_device.name}")
                
                await client.write_gatt_char(CONTROL_CHAR, b'\x02\x64\x0a')
                await asyncio.sleep(0.5)
                await client.write_gatt_char(CONTROL_CHAR, b'\x02\x73\x0a')
                
                await client.start_notify(EEG_CHAR, notification_handler)
                
                state.muse_connected = True
                print("EEG streaming started!")
                
                while state.ble_running:
                    await asyncio.sleep(0.1)
                
                await client.write_gatt_char(CONTROL_CHAR, b'\x02\x68\x0a')
                
        except Exception as e:
            print(f"BLE Error: {e}")
        
        state.muse_connected = False
    
    # Create new event loop for this thread
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    
    try:
        loop.run_until_complete(connect_and_stream())
    except Exception as e:
        print(f"BLE thread error: {e}")
    finally:
        loop.close()

def start_ble_thread():
    """Start BLE connection in separate thread."""
    state.ble_running = True
    state.ble_thread = threading.Thread(target=ble_thread_main, daemon=True)
    state.ble_thread.start()

def stop_ble_thread():
    """Stop BLE thread."""
    state.ble_running = False
    if state.ble_thread:
        state.ble_thread.join(timeout=2)

# =============================================================================
# GAME LOGIC
# =============================================================================
def reset_ball():
    """Reset ball to center."""
    state.ball_x = SCREEN_WIDTH // 2
    state.ball_y = SCREEN_HEIGHT // 2
    state.ball_dx = 5 * (1 if np.random.random() > 0.5 else -1)
    state.ball_dy = 3 * (1 if np.random.random() > 0.5 else -1)

def update_game():
    """Update game physics."""
    # Move player paddle based on EEG control
    if state.muse_connected or state.lcc_mode:
        state.player_y -= state.control_signal * CONTROL_SENSITIVITY
    
    state.player_y = max(PADDLE_HEIGHT // 2, min(SCREEN_HEIGHT - PADDLE_HEIGHT // 2, state.player_y))
    
    # AI paddle
    ai_speed = 4
    if state.ball_y < state.ai_y:
        state.ai_y -= ai_speed
    elif state.ball_y > state.ai_y:
        state.ai_y += ai_speed
    state.ai_y = max(PADDLE_HEIGHT // 2, min(SCREEN_HEIGHT - PADDLE_HEIGHT // 2, state.ai_y))
    
    # Move ball
    state.ball_x += state.ball_dx
    state.ball_y += state.ball_dy
    
    # Ball collision with top/bottom
    if state.ball_y <= BALL_SIZE // 2 or state.ball_y >= SCREEN_HEIGHT - BALL_SIZE // 2:
        state.ball_dy *= -1
    
    # Player paddle collision
    if state.ball_x <= PADDLE_WIDTH + BALL_SIZE // 2 + 20:
        if abs(state.ball_y - state.player_y) < PADDLE_HEIGHT // 2 + BALL_SIZE // 2:
            state.ball_dx = abs(state.ball_dx) * 1.05
            state.total_hits += 1
            if state.lcc_mode:
                state.lcc_hits += 1
            log_event("HIT", state.control_signal)
    
    # AI paddle collision
    if state.ball_x >= SCREEN_WIDTH - PADDLE_WIDTH - BALL_SIZE // 2 - 20:
        if abs(state.ball_y - state.ai_y) < PADDLE_HEIGHT // 2 + BALL_SIZE // 2:
            state.ball_dx = -abs(state.ball_dx) * 1.05
    
    # Scoring
    if state.ball_x < 0:
        state.ai_score += 1
        log_event("AI_SCORE", state.control_signal)
        reset_ball()
    elif state.ball_x > SCREEN_WIDTH:
        state.player_score += 1
        log_event("PLAYER_SCORE", state.control_signal)
        reset_ball()

def log_event(event_type, control_value):
    """Log game event for analysis."""
    state.log_data.append({
        'timestamp': datetime.now().isoformat(),
        'event': event_type,
        'control': control_value,
        'alpha': state.alpha,
        'beta': state.beta,
        'theta': state.theta,
        'gamma': state.gamma,
        'muse_connected': state.muse_connected,
        'lcc_mode': state.lcc_mode,
        'player_score': state.player_score,
        'ai_score': state.ai_score
    })

def draw_game(screen, font):
    """Draw game graphics."""
    screen.fill(BLACK)
    
    # Center line
    for y in range(0, SCREEN_HEIGHT, 30):
        pygame.draw.rect(screen, WHITE, (SCREEN_WIDTH // 2 - 2, y, 4, 15))
    
    # Paddles
    paddle_color = PURPLE if state.lcc_mode else (GREEN if state.muse_connected else CYAN)
    pygame.draw.rect(screen, paddle_color, 
                     (20, int(state.player_y) - PADDLE_HEIGHT // 2, PADDLE_WIDTH, PADDLE_HEIGHT))
    pygame.draw.rect(screen, RED, 
                     (SCREEN_WIDTH - 35, int(state.ai_y) - PADDLE_HEIGHT // 2, PADDLE_WIDTH, PADDLE_HEIGHT))
    
    # Ball
    pygame.draw.circle(screen, WHITE, (int(state.ball_x), int(state.ball_y)), BALL_SIZE // 2)
    
    # Scores
    score_text = font.render(f"{state.player_score}  -  {state.ai_score}", True, WHITE)
    screen.blit(score_text, (SCREEN_WIDTH // 2 - score_text.get_width() // 2, 20))
    
    # Mode indicator
    info_y = SCREEN_HEIGHT - 80
    if state.lcc_mode:
        mode_text = font.render("LCC MODE - MUSE REMOVED", True, PURPLE)
    elif state.muse_connected:
        mode_text = font.render("EEG CONTROL ACTIVE", True, GREEN)
    else:
        mode_text = font.render("DEMO MODE (Arrow Keys)", True, CYAN)
    screen.blit(mode_text, (SCREEN_WIDTH // 2 - mode_text.get_width() // 2, info_y - 30))
    
    # Control bar
    bar_width = 300
    bar_height = 20
    bar_x = SCREEN_WIDTH // 2 - bar_width // 2
    
    pygame.draw.rect(screen, (50, 50, 50), (bar_x, info_y, bar_width, bar_height))
    pygame.draw.line(screen, WHITE, (bar_x + bar_width // 2, info_y), 
                     (bar_x + bar_width // 2, info_y + bar_height), 2)
    
    ctrl_x = bar_x + bar_width // 2 + int(state.control_signal * bar_width // 2)
    ctrl_x = max(bar_x + 10, min(bar_x + bar_width - 10, ctrl_x))
    pygame.draw.circle(screen, GREEN if state.control_signal > 0 else RED, 
                       (ctrl_x, info_y + bar_height // 2), 10)
    
    down_text = font.render("DOWN", True, RED)
    up_text = font.render("UP", True, GREEN)
    screen.blit(down_text, (bar_x - 60, info_y))
    screen.blit(up_text, (bar_x + bar_width + 10, info_y))
    
    # Band powers
    small_font = pygame.font.Font(None, 24)
    bands_text = small_font.render(
        f"A:{state.alpha:.1f}  B:{state.beta:.1f}  T:{state.theta:.1f}  G:{state.gamma:.1f}", 
        True, (150, 150, 150))
    screen.blit(bands_text, (SCREEN_WIDTH // 2 - bands_text.get_width() // 2, info_y + 25))
    
    # Instructions
    inst_text = small_font.render("SPACE: LCC Mode  |  R: Reset  |  ESC: Quit", True, (100, 100, 100))
    screen.blit(inst_text, (SCREEN_WIDTH // 2 - inst_text.get_width() // 2, SCREEN_HEIGHT - 20))
    
    # LCC Stats
    if state.lcc_mode and state.lcc_start_time:
        elapsed = (datetime.now() - state.lcc_start_time).total_seconds()
        lcc_text = small_font.render(f"LCC Time: {elapsed:.0f}s  |  LCC Hits: {state.lcc_hits}", True, PURPLE)
        screen.blit(lcc_text, (10, 10))
    
    # Total hits
    hits_text = small_font.render(f"Total Hits: {state.total_hits}", True, (100, 100, 100))
    screen.blit(hits_text, (10, 30 if not state.lcc_mode else 50))

def save_session_log():
    """Save session data to CSV."""
    if not state.log_data:
        print("No events to save.")
        return
    
    filename = f"pong_lcc_session_{state.session_start.strftime('%Y%m%d_%H%M%S')}.csv"
    
    with open(filename, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=state.log_data[0].keys())
        writer.writeheader()
        writer.writerows(state.log_data)
    
    print(f"\nSession saved to: {filename}")
    print(f"Total hits: {state.total_hits}")
    print(f"LCC hits: {state.lcc_hits}")
    print(f"Final score: You {state.player_score} - {state.ai_score} AI")

# =============================================================================
# MAIN
# =============================================================================
def main():
    """Main game loop."""
    pygame.init()
    screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
    pygame.display.set_caption("EEG PONG - LCC Test")
    clock = pygame.time.Clock()
    font = pygame.font.Font(None, 48)
    
    print("\n" + "=" * 60)
    print("    EEG PONG - LUMINATED CONSCIOUSNESS CORRELATION TEST")
    print("=" * 60)
    
    # Start BLE thread
    start_ble_thread()
    
    # Wait a bit for connection
    print("Attempting Muse connection...")
    time.sleep(3)
    
    if not state.muse_connected:
        print("\nNo Muse connected - using DEMO mode (arrow keys)")
    
    print("\nControls:")
    print("  SPACE - Toggle LCC Mode")
    print("  R     - Reset scores")
    print("  ESC   - Quit")
    if not state.muse_connected:
        print("  UP/DOWN - Control paddle (demo mode)")
    print("=" * 60 + "\n")
    
    reset_ball()
    running = True
    
    try:
        while running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key == pygame.K_SPACE:
                        state.lcc_mode = not state.lcc_mode
                        if state.lcc_mode:
                            state.lcc_start_time = datetime.now()
                            state.lcc_hits = 0
                            state.last_control_before_lcc = state.control_signal
                            print("\n*** LCC MODE ON - Remove Muse and play with intention! ***")
                        else:
                            print("\n*** LCC MODE OFF ***")
                            state.lcc_start_time = None
                        log_event("LCC_TOGGLE", state.control_signal)
                    elif event.key == pygame.K_r:
                        state.player_score = 0
                        state.ai_score = 0
                        state.total_hits = 0
                        state.lcc_hits = 0
                        reset_ball()
                        log_event("RESET", 0)
            
            # Demo mode: keyboard control
            if not state.muse_connected and not state.lcc_mode:
                keys = pygame.key.get_pressed()
                if keys[pygame.K_UP]:
                    state.control_signal = 0.8
                elif keys[pygame.K_DOWN]:
                    state.control_signal = -0.8
                else:
                    state.control_signal *= 0.9
            
            # In LCC mode, slowly decay the control signal
            if state.lcc_mode:
                state.control_signal *= 0.998
            
            update_game()
            draw_game(screen, font)
            pygame.display.flip()
            clock.tick(FPS)
    
    finally:
        stop_ble_thread()
        save_session_log()
        pygame.quit()

if __name__ == "__main__":
    main()
