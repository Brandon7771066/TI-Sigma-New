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
- Or use ATTENTION level for smooth control

REQUIREMENTS:
pip install pygame bleak numpy

Run: python EEG_PONG_LCC_TEST.py
"""

import asyncio
import pygame
import numpy as np
import time
import csv
import os
from datetime import datetime
from collections import deque
import threading
import struct

# Try to import bleak for BLE
try:
    from bleak import BleakClient, BleakScanner
    BLEAK_AVAILABLE = True
except ImportError:
    BLEAK_AVAILABLE = False
    print("WARNING: bleak not installed. Run: pip install bleak")

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

# EEG Control Settings
CONTROL_SENSITIVITY = 8  # How fast paddle responds to EEG
SMOOTHING_WINDOW = 10    # Samples to average for smooth control

# Muse 2 BLE UUIDs
MUSE_SERVICE = "0000fe8d-0000-1000-8000-00805f9b34fb"
CONTROL_CHAR = "273e0001-4c4d-454d-96be-f03bac821358"
EEG_CHAR = "273e0003-4c4d-454d-96be-f03bac821358"  # TP9, AF7, AF8, TP10

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
        self.attention = 0.5  # 0-1 scale
        
        # Control signal
        self.control_signal = 0.0  # -1 to 1, negative=down, positive=up
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
        self.lcc_mode = False  # True = Muse removed, testing LCC
        self.lcc_start_time = None
        
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
        self.control_accuracy = []

state = GameState()

# =============================================================================
# EEG PROCESSING
# =============================================================================
def compute_band_powers(samples, fs=256):
    """Compute band powers from EEG samples using FFT."""
    if len(samples) < 64:
        return {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
    
    samples = np.array(samples)
    # Remove DC offset
    samples = samples - np.mean(samples)
    
    # Apply Hanning window
    window = np.hanning(len(samples))
    samples = samples * window
    
    # FFT
    fft = np.fft.rfft(samples)
    freqs = np.fft.rfftfreq(len(samples), 1/fs)
    power = np.abs(fft) ** 2
    
    # Band definitions (Hz)
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
        band_powers[band] = np.log10(np.mean(power[mask]) + 1e-10)
    
    return band_powers

def update_control_signal():
    """Calculate control signal from EEG bands."""
    # Combine frontal channels (AF7, AF8) for attention
    af7_powers = compute_band_powers(list(state.eeg_buffer['AF7']))
    af8_powers = compute_band_powers(list(state.eeg_buffer['AF8']))
    
    # Average frontal
    state.alpha = (af7_powers['alpha'] + af8_powers['alpha']) / 2
    state.beta = (af7_powers['beta'] + af8_powers['beta']) / 2
    state.theta = (af7_powers['theta'] + af8_powers['theta']) / 2
    state.gamma = (af7_powers['gamma'] + af8_powers['gamma']) / 2
    
    # Control method: Alpha/Beta ratio
    # High alpha (relaxed) = move UP
    # High beta (focused) = move DOWN
    if state.beta != 0:
        ab_ratio = state.alpha / (abs(state.beta) + 0.01)
    else:
        ab_ratio = 1.0
    
    # Normalize to -1 to 1 range
    # AB ratio > 2 = very relaxed (up)
    # AB ratio < 0.5 = very focused (down)
    raw_signal = (ab_ratio - 1.25) / 1.25  # Center around 1.25
    raw_signal = max(-1, min(1, raw_signal))  # Clamp
    
    state.control_history.append(raw_signal)
    state.control_signal = np.mean(list(state.control_history))
    
    # Also compute attention (for display)
    state.attention = 0.5 + (state.control_signal * 0.5)

# =============================================================================
# MUSE BLE CONNECTION
# =============================================================================
class MuseConnection:
    def __init__(self):
        self.client = None
        self.running = False
        
    def parse_eeg(self, data):
        """Parse raw EEG packet from Muse."""
        if len(data) < 12:
            return
        
        # Muse sends 12 samples per packet (3 per channel)
        try:
            # First byte is packet counter
            packet_idx = data[0]
            
            # Extract samples (12-bit values packed)
            samples = []
            for i in range(12):
                byte_idx = 1 + (i * 3) // 2
                if byte_idx + 1 < len(data):
                    if i % 2 == 0:
                        val = ((data[byte_idx] << 4) | (data[byte_idx + 1] >> 4)) & 0xFFF
                    else:
                        val = ((data[byte_idx] & 0x0F) << 8) | data[byte_idx + 1]
                    # Convert to microvolts (approximate)
                    uv = (val - 2048) * 0.48828125
                    samples.append(uv)
            
            # Distribute to channels (3 samples each)
            channels = ['TP9', 'AF7', 'AF8', 'TP10']
            for ch_idx, ch in enumerate(channels):
                for s in range(3):
                    if ch_idx * 3 + s < len(samples):
                        state.eeg_buffer[ch].append(samples[ch_idx * 3 + s])
            
            # Update control signal periodically
            if len(state.eeg_buffer['AF7']) >= 64:
                update_control_signal()
                
        except Exception as e:
            pass  # Silently handle parse errors
    
    async def notification_handler(self, sender, data):
        """Handle incoming EEG data."""
        self.parse_eeg(bytes(data))
    
    async def connect(self):
        """Connect to Muse 2."""
        print("Scanning for Muse 2...")
        
        devices = await BleakScanner.discover(timeout=10)
        muse_device = None
        
        for d in devices:
            name = d.name or ""
            if "Muse" in name:
                muse_device = d
                print(f"Found: {name} ({d.address})")
                break
        
        if not muse_device:
            print("No Muse found!")
            return False
        
        try:
            self.client = BleakClient(muse_device.address)
            await self.client.connect()
            print(f"Connected to {muse_device.name}")
            
            # Start streaming
            await self.client.write_gatt_char(CONTROL_CHAR, b'\x02\x64\x0a')  # Start
            await asyncio.sleep(0.5)
            await self.client.write_gatt_char(CONTROL_CHAR, b'\x02\x73\x0a')  # Resume
            
            # Subscribe to EEG
            await self.client.start_notify(EEG_CHAR, self.notification_handler)
            
            state.muse_connected = True
            self.running = True
            print("EEG streaming started!")
            return True
            
        except Exception as e:
            print(f"Connection error: {e}")
            return False
    
    async def disconnect(self):
        """Disconnect from Muse."""
        if self.client and self.client.is_connected:
            try:
                await self.client.write_gatt_char(CONTROL_CHAR, b'\x02\x68\x0a')  # Stop
                await self.client.disconnect()
            except:
                pass
        state.muse_connected = False
        self.running = False

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
        # Control signal: positive = up, negative = down
        state.player_y -= state.control_signal * CONTROL_SENSITIVITY
    
    # Keep paddle in bounds
    state.player_y = max(PADDLE_HEIGHT // 2, min(SCREEN_HEIGHT - PADDLE_HEIGHT // 2, state.player_y))
    
    # AI paddle (simple tracking)
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
    
    # Ball collision with paddles
    # Player paddle (left)
    if state.ball_x <= PADDLE_WIDTH + BALL_SIZE // 2 + 20:
        if abs(state.ball_y - state.player_y) < PADDLE_HEIGHT // 2 + BALL_SIZE // 2:
            state.ball_dx = abs(state.ball_dx)  # Bounce right
            state.ball_dx *= 1.05  # Speed up
            state.total_hits += 1
            if state.lcc_mode:
                state.lcc_hits += 1
            # Log hit
            log_event("HIT", state.control_signal)
    
    # AI paddle (right)
    if state.ball_x >= SCREEN_WIDTH - PADDLE_WIDTH - BALL_SIZE // 2 - 20:
        if abs(state.ball_y - state.ai_y) < PADDLE_HEIGHT // 2 + BALL_SIZE // 2:
            state.ball_dx = -abs(state.ball_dx)  # Bounce left
            state.ball_dx *= 1.05
    
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
    
    # Draw center line
    for y in range(0, SCREEN_HEIGHT, 30):
        pygame.draw.rect(screen, WHITE, (SCREEN_WIDTH // 2 - 2, y, 4, 15))
    
    # Draw paddles
    # Player paddle (left) - color based on mode
    paddle_color = PURPLE if state.lcc_mode else (GREEN if state.muse_connected else WHITE)
    pygame.draw.rect(screen, paddle_color, 
                     (20, state.player_y - PADDLE_HEIGHT // 2, PADDLE_WIDTH, PADDLE_HEIGHT))
    
    # AI paddle (right)
    pygame.draw.rect(screen, RED, 
                     (SCREEN_WIDTH - 35, state.ai_y - PADDLE_HEIGHT // 2, PADDLE_WIDTH, PADDLE_HEIGHT))
    
    # Draw ball
    pygame.draw.circle(screen, WHITE, (int(state.ball_x), int(state.ball_y)), BALL_SIZE // 2)
    
    # Draw scores
    score_text = font.render(f"{state.player_score}  -  {state.ai_score}", True, WHITE)
    screen.blit(score_text, (SCREEN_WIDTH // 2 - score_text.get_width() // 2, 20))
    
    # Draw EEG info bar
    info_y = SCREEN_HEIGHT - 80
    
    # Mode indicator
    if state.lcc_mode:
        mode_text = font.render("⚡ LCC MODE - MUSE REMOVED ⚡", True, PURPLE)
        screen.blit(mode_text, (SCREEN_WIDTH // 2 - mode_text.get_width() // 2, info_y - 30))
    elif state.muse_connected:
        mode_text = font.render("🧠 EEG CONTROL ACTIVE", True, GREEN)
        screen.blit(mode_text, (SCREEN_WIDTH // 2 - mode_text.get_width() // 2, info_y - 30))
    else:
        mode_text = font.render("⌛ Connecting to Muse...", True, YELLOW)
        screen.blit(mode_text, (SCREEN_WIDTH // 2 - mode_text.get_width() // 2, info_y - 30))
    
    # Control signal bar
    bar_width = 300
    bar_height = 20
    bar_x = SCREEN_WIDTH // 2 - bar_width // 2
    
    pygame.draw.rect(screen, (50, 50, 50), (bar_x, info_y, bar_width, bar_height))
    
    # Center marker
    pygame.draw.line(screen, WHITE, (bar_x + bar_width // 2, info_y), 
                     (bar_x + bar_width // 2, info_y + bar_height), 2)
    
    # Control position
    ctrl_x = bar_x + bar_width // 2 + int(state.control_signal * bar_width // 2)
    pygame.draw.circle(screen, GREEN if state.control_signal > 0 else RED, 
                       (ctrl_x, info_y + bar_height // 2), 10)
    
    # Labels
    down_text = font.render("↓ FOCUS", True, RED)
    up_text = font.render("RELAX ↑", True, GREEN)
    screen.blit(down_text, (bar_x - 70, info_y))
    screen.blit(up_text, (bar_x + bar_width + 10, info_y))
    
    # Band powers (small text)
    small_font = pygame.font.Font(None, 24)
    bands_text = small_font.render(
        f"α:{state.alpha:.2f}  β:{state.beta:.2f}  θ:{state.theta:.2f}  γ:{state.gamma:.2f}", 
        True, (150, 150, 150))
    screen.blit(bands_text, (SCREEN_WIDTH // 2 - bands_text.get_width() // 2, info_y + 25))
    
    # Instructions
    inst_text = small_font.render("SPACE: Toggle LCC Mode  |  R: Reset  |  ESC: Quit", True, (100, 100, 100))
    screen.blit(inst_text, (SCREEN_WIDTH // 2 - inst_text.get_width() // 2, SCREEN_HEIGHT - 20))
    
    # LCC Stats (if in LCC mode)
    if state.lcc_mode and state.lcc_start_time:
        elapsed = (datetime.now() - state.lcc_start_time).total_seconds()
        lcc_text = small_font.render(
            f"LCC Time: {elapsed:.0f}s  |  LCC Hits: {state.lcc_hits}", True, PURPLE)
        screen.blit(lcc_text, (10, 10))

def save_session_log():
    """Save session data to CSV."""
    if not state.log_data:
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
# MAIN GAME LOOP
# =============================================================================
async def main():
    """Main game loop."""
    pygame.init()
    screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
    pygame.display.set_caption("EEG PONG - LCC Test")
    clock = pygame.time.Clock()
    font = pygame.font.Font(None, 48)
    
    muse = MuseConnection() if BLEAK_AVAILABLE else None
    
    # Try to connect to Muse
    if muse:
        connected = await muse.connect()
        if not connected:
            print("\nRunning in DEMO mode (no Muse connected)")
            print("Use UP/DOWN arrows to control paddle")
    
    running = True
    demo_mode = not state.muse_connected
    
    reset_ball()
    
    print("\n" + "=" * 50)
    print("EEG PONG - LCC TEST")
    print("=" * 50)
    print("Controls:")
    print("  SPACE - Toggle LCC Mode (remove Muse first!)")
    print("  R     - Reset scores")
    print("  ESC   - Quit and save log")
    if demo_mode:
        print("  UP/DOWN - Manual paddle control (demo mode)")
    print("=" * 50 + "\n")
    
    try:
        while running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key == pygame.K_SPACE:
                        # Toggle LCC mode
                        state.lcc_mode = not state.lcc_mode
                        if state.lcc_mode:
                            state.lcc_start_time = datetime.now()
                            state.lcc_hits = 0
                            print("\n⚡ LCC MODE ACTIVATED - Remove your Muse now! ⚡")
                            print("Continue playing with INTENTION ONLY...")
                        else:
                            print("\n🧠 LCC MODE DEACTIVATED - Normal EEG control")
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
            if demo_mode:
                keys = pygame.key.get_pressed()
                if keys[pygame.K_UP]:
                    state.control_signal = 0.8
                elif keys[pygame.K_DOWN]:
                    state.control_signal = -0.8
                else:
                    state.control_signal *= 0.9  # Decay
            
            # In LCC mode, we keep using the LAST control signal pattern
            # (simulating intention-based control)
            if state.lcc_mode and not demo_mode:
                # Slowly decay control signal in LCC mode
                # This simulates "intention" needing reinforcement
                state.control_signal *= 0.995
            
            update_game()
            draw_game(screen, font)
            pygame.display.flip()
            clock.tick(FPS)
            
            # Allow async operations
            await asyncio.sleep(0.001)
    
    finally:
        if muse:
            await muse.disconnect()
        save_session_log()
        pygame.quit()

# =============================================================================
# ENTRY POINT
# =============================================================================
if __name__ == "__main__":
    print("\n" + "=" * 60)
    print("    EEG PONG - LUMINATED CONSCIOUSNESS CORRELATION TEST")
    print("=" * 60)
    print("\nStarting...")
    
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nGame interrupted.")
    
    print("\nThank you for testing consciousness correlation! 🧠⚡🎮")
