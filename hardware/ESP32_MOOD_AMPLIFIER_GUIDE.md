# ESP32 Mood Amplifier BLE Bridge

## Complete Step-by-Step Setup Guide

**Your Devices:**
- Polar H10 C895672B (Heart Rate / HRV)
- Muse-2E34 (EEG)
- Mendi (fNIRS)

---

## STEP 1: Arduino IDE Setup for ESP32

### 1.1 Install ESP32 Board Support

1. Open Arduino IDE
2. Go to **File → Preferences**
3. In "Additional Board Manager URLs", add:
   ```
   https://raw.githubusercontent.com/espressif/arduino-esp32/gh-pages/package_esp32_index.json
   ```
4. Click OK

5. Go to **Tools → Board → Board Manager**
6. Search for "ESP32"
7. Install **"ESP32 by Espressif Systems"** (latest version)

### 1.2 Select Your Board

Since you selected Arduino Nano, you likely have an **ESP32-C3** or similar compact board.

1. Go to **Tools → Board → ESP32 Arduino**
2. Select one of these (try in order):
   - **ESP32C3 Dev Module** (most likely for Nano-sized)
   - **ESP32-S3 Dev Module**
   - **ESP32 Dev Module** (generic)

### 1.3 Select Port

1. Connect ESP32 via USB
2. Go to **Tools → Port**
3. Select the COM port that appears (e.g., COM3, COM4, or /dev/ttyUSB0)

---

## STEP 2: Install Required Libraries

Go to **Sketch → Include Library → Manage Libraries** and install:

1. **NimBLE-Arduino** by h2zero (REQUIRED - better BLE library)
   - Search: "NimBLE"
   - Install latest version

2. **ArduinoJson** by Benoit Blanchon
   - Search: "ArduinoJson"
   - Install version 6.x or 7.x

3. **WiFi** (usually built-in with ESP32)

---

## STEP 3: Configure Your WiFi

Before uploading, you'll need to edit the code with:
- Your WiFi network name (SSID)
- Your WiFi password
- Your Replit server URL (we'll set this up)

---

## STEP 4: Understanding the Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     MOOD AMPLIFIER SYSTEM                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐                    │
│  │ Polar H10│   │ Muse 2   │   │  Mendi   │                    │
│  │  (HRV)   │   │  (EEG)   │   │ (fNIRS)  │                    │
│  └────┬─────┘   └────┬─────┘   └────┬─────┘                    │
│       │              │              │                           │
│       └──────────────┼──────────────┘                           │
│                      │ BLE                                      │
│                      ▼                                          │
│              ┌──────────────┐                                   │
│              │    ESP32     │                                   │
│              │  BLE Bridge  │                                   │
│              └──────┬───────┘                                   │
│                     │ WiFi/HTTP                                 │
│                     ▼                                           │
│              ┌──────────────┐                                   │
│              │   Replit     │                                   │
│              │   Server     │                                   │
│              └──────────────┘                                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## STEP 5: Upload the Code

1. Open the file `ESP32_MoodAmplifier.ino` (created below)
2. Edit WiFi credentials
3. Click **Upload** (→ arrow button)
4. Open **Serial Monitor** (Tools → Serial Monitor)
5. Set baud rate to **115200**
6. Watch for connection status

---

## STEP 6: Testing Connections

### Test 1: Polar H10 (Easiest)
- Put on chest strap
- Wet the electrodes slightly
- The H10 LED will blink when active
- ESP32 should show heart rate data in Serial Monitor

### Test 2: Mendi
- Turn on Mendi headband
- Place on forehead
- Should see fNIRS data streaming

### Test 3: Muse 2
- Turn on Muse (cascading blue lights)
- Make sure NO other apps are connected
- Most complex - may need troubleshooting

---

## STEP 7: Troubleshooting

### "Device not found"
- Make sure device is ON and not connected to another app
- Bring device closer to ESP32
- Try power cycling the device

### "Connection failed"
- Some devices need multiple attempts
- Check if device name matches exactly

### "No data received"
- Heart rate sensors need skin contact
- EEG needs electrode contact
- fNIRS needs forehead placement

### ESP32 keeps rebooting
- Power issue - try different USB cable
- Try powered USB hub

---

## Device-Specific Notes

### Polar H10
- Uses standard Heart Rate Service (0x180D)
- Very reliable connection
- Provides: Heart Rate, RR Intervals (for HRV)

### Muse 2
- Proprietary protocol
- Streams: EEG (4 channels), Accelerometer, Gyroscope
- Complex data parsing required

### Mendi
- Nordic nRF5 based
- Custom service UUID: FC3EABB0-C6C4-49E6-922A-6E551C455AF5
- Streams: fNIRS oxygenation data

---

## Next Steps After Hardware Works

1. ESP32 sends data to Replit server via HTTP POST
2. Replit server calculates GILE scores
3. Data displayed on Streamlit dashboard
4. Mood Amplifier safety validation runs

