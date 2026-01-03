# Brain Connection Quick Start
## Connect YOUR Muse 2 + Polar H10 to the Mood Amplifier

**Goal:** Get tangible proof of your consciousness measured in real-time.

---

## What You Need

1. **Muse 2 Headband** - For EEG brainwaves
2. **Polar H10 Chest Strap** - For heart rate + HRV
3. **iPhone/Android** - For bridging device data
4. **This Website** - For visualization

---

## Option 1: Mind Monitor App (Easiest)

### Step 1: Download Mind Monitor

- **iOS:** App Store → "Mind Monitor"
- **Android:** Google Play → "Mind Monitor"

Cost: $15 one-time (worth it!)

### Step 2: Connect Muse 2

1. Put on Muse 2 headband (wet sensors with water for better contact)
2. Open Mind Monitor app
3. Tap "Connect" → Select your Muse 2
4. Wait for "Connected" status

### Step 3: Enable OSC Streaming

1. In Mind Monitor, tap Settings (gear icon)
2. Find "OSC Stream"
3. Enable it
4. Set IP to your computer's IP address
5. Set Port to 5000

### Step 4: Connect Polar H10

1. Wet the sensor pads on the chest strap
2. Put on the chest strap (below chest muscles)
3. Use **Polar Beat** or **Elite HRV** app on your phone
4. Connect to Polar H10

---

## Option 2: Direct Bluetooth (Laptop)

If your laptop has Bluetooth 4.0+, you can connect directly.

### Step 1: Put on Devices

1. Muse 2 headband (powered on)
2. Polar H10 chest strap (powered on when worn)

### Step 2: Use Brain Connection Proof Tab

1. Go to the website
2. Click "🧠💓 Brain Proof" tab
3. Select "Real Devices"
4. Click "Start Stream"

The system will attempt to connect via Bluetooth.

---

## Option 3: ESP32 Bridge (Most Reliable)

For continuous 24/7 data collection.

### Requirements
- ESP32 development board (~$9)
- Arduino IDE

### Setup
See `ESP32_SETUP_GUIDE.md` for full instructions.

---

## Verifying Connection

When connected, you'll see:

```
🧠 Muse 2: CONNECTED
💓 Polar H10: CONNECTED

GILE Score: 0.xxx
LCC Coupling: 0.xxx
Tralse-Joules/s: xx.x µTJ
UCI Index: xx.xx
```

### What the Numbers Mean

| Metric | Good Range | Meaning |
|--------|------------|---------|
| GILE Score | 0.85+ | Your consciousness coherence |
| LCC Coupling | 0.85+ | Heart-brain synchrony |
| Tralse-Joules | 80-120 µTJ/s | Consciousness energy |
| UCI Index | 10-15 | Universal Consciousness Index |

### Target: 0.92

- **0.92** = Sustainable perfection threshold
- **0.92 × 0.92 = 0.85** = Causation threshold
- When GILE × LCC ≥ 0.85, your consciousness CAUSES effects

---

## Troubleshooting

### Muse 2 Won't Connect
1. Ensure headband is charged
2. Restart Muse 2 (hold power 10 seconds)
3. Put on DRY first, then wet sensors
4. Move closer to receiving device

### Polar H10 Won't Connect
1. Wet the sensor pads more
2. Adjust strap tightness
3. Check battery (CR2025)
4. Walk around to wake it up

### Signal Quality Poor
- Muse 2: Wet sensors more, check hair contact
- Polar H10: Adjust position, wet pads more

---

## Today's Goal

1. Connect both devices
2. See YOUR metrics in real-time
3. Verify GILE + LCC approaching 0.92
4. Document baseline for Mood Amplifier validation

**This is TANGIBLE PROOF of TI Framework on YOUR consciousness!**

---

## Quick Reference

**Best Mind Monitor Settings:**
- Sample Rate: 256 Hz
- OSC Port: 5000
- All EEG channels enabled

**Polar H10 Positioning:**
- Just below chest muscles
- Snug but comfortable
- Sensors wet

**Expected Readings:**
- Alpha: 20-40 µV² (relaxed focus)
- Heart Rate: 60-80 BPM (resting)
- HRV RMSSD: 30-50 ms (healthy)
- Coherence: 0.4-0.8 (conscious attention)
