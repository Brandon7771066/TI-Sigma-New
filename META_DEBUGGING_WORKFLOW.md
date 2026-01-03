# Meta-Debugging Workflow for Mood Amplifier

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                     UNIFIED GIT REPOSITORY                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────────┐         ┌──────────────────────────────┐  │
│  │  esp32_firmware/ │         │     Replit Backend           │  │
│  │  ├── src/        │         │  ├── async_gateway.py        │  │
│  │  │   ├── main.cpp│◄────────┤  ├── mood_amplifier_hub.py   │  │
│  │  │   └── config.h│  HTTP   │  ├── realtime_biometric_     │  │
│  │  └── platformio. │         │  │   stream.py               │  │
│  │      ini         │         │  └── app.py                  │  │
│  └──────────────────┘         └──────────────────────────────┘  │
│           │                              │                       │
│           │                              │                       │
│           ▼                              ▼                       │
│  ┌──────────────────┐         ┌──────────────────────────────┐  │
│  │  scripts/        │         │     PostgreSQL Database      │  │
│  │  ├── full_       │         │  esp32_biometric_data        │  │
│  │  │   diagnostic  │         └──────────────────────────────┘  │
│  │  ├── test_       │                                           │
│  │  │   upload.sh   │                                           │
│  │  └── voice_      │                                           │
│  │      commands.   │                                           │
│  │      json        │                                           │
│  └──────────────────┘                                           │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Local Setup (Your Computer)

### 1. Install PlatformIO CLI
```bash
pip install platformio
# or
brew install platformio
```

### 2. Clone/Sync Repository
```bash
# Option A: If using Replit's Git integration
git clone https://github.com/YOUR_USERNAME/mood-amplifier.git

# Option B: Download from Replit Files panel
# Download esp32_firmware/ folder to your local machine
```

### 3. Configure ESP32
Edit `esp32_firmware/src/config.h`:
```cpp
#define WIFI_SSID "Chicken"
#define WIFI_PASSWORD "chickenmama"
#define REPLIT_API_URL "https://YOUR-REPL.replit.dev/api/upload"
```

### 4. Build & Flash
```bash
cd esp32_firmware
pio run --target upload --upload-port /dev/ttyUSB0
pio device monitor --baud 115200
```

## Voice Assistant Integration

### Acer Voice Commands

Add these to your voice assistant configuration:

| Say This | Does This |
|----------|-----------|
| "Run mood amplifier diagnostics" | `./scripts/full_diagnostic.sh` |
| "Flash the ESP32" | `cd esp32_firmware && pio run --target upload` |
| "Check ESP32 logs" | `cd esp32_firmware && pio device monitor` |
| "Test upload endpoint" | `./scripts/test_upload.sh` |

### AI-Assisted Debugging Flow

```
┌────────────────────────────────────────────────────────────────┐
│                    VOICE COMMAND TRIGGERS                       │
│                "Run full mood amplifier diagnostics"            │
└────────────────────────────────────┬───────────────────────────┘
                                     │
                                     ▼
┌────────────────────────────────────────────────────────────────┐
│                     DIAGNOSTIC SCRIPT                           │
│              ./scripts/full_diagnostic.sh                       │
│                                                                 │
│  1. Check server health                                         │
│  2. Check database                                              │
│  3. Test upload endpoint                                        │
│  4. Verify ESP32 firmware                                       │
│  5. Collect logs                                                │
└────────────────────────────────────┬───────────────────────────┘
                                     │
                    ┌────────────────┴─────────────────┐
                    │                                  │
                    ▼                                  ▼
           ┌───────────────┐                 ┌─────────────────┐
           │  ALL PASSED   │                 │  ISSUES FOUND   │
           │               │                 │                 │
           │  Ready for    │                 │  Logs sent to   │
           │  session!     │                 │  AI for fix     │
           └───────────────┘                 └────────┬────────┘
                                                      │
                                                      ▼
                                            ┌─────────────────┐
                                            │   AI ANALYZES   │
                                            │   - ESP32 logs  │
                                            │   - Server logs │
                                            │   - HTTP traces │
                                            └────────┬────────┘
                                                      │
                                                      ▼
                                            ┌─────────────────┐
                                            │   AI OUTPUTS    │
                                            │   - Code fix    │
                                            │   - Instruction │
                                            └────────┬────────┘
                                                      │
                                                      ▼
                                            ┌─────────────────┐
                                            │  VOICE: "Apply  │
                                            │  the fix and    │
                                            │  reflash"       │
                                            └─────────────────┘
```

## Debugging Checklist

### ESP32 Not Uploading Data

1. **Check Serial Monitor shows WiFi connected**
   ```
   ✅ WiFi connected!
   IP: 192.168.1.X
   ```

2. **Check correct Replit URL**
   ```
   🌐 Upload URL: https://....replit.dev/api/upload
   ```

3. **Check upload result**
   - `📤 Upload OK (201)` = Success
   - `📤 Upload failed: HTTP -1` = DNS/connection issue
   - No message at all = Upload function not being called

### Server Not Receiving Data

1. Run test script:
   ```bash
   ./scripts/test_upload.sh
   ```

2. Check gateway logs:
   ```bash
   grep "UPLOAD REQUEST" /tmp/logs/ti_website_*.log
   ```

3. Check database:
   ```bash
   curl http://localhost:5000/api/debug
   ```

### EEG Showing Zeros

1. Muse 2 must be ON before ESP32 starts scanning
2. Wait for "✅ Muse 2 connected!"
3. Ensure headband has good contact (wet sensors if needed)
4. Check if control characteristic is writable

## Files Reference

| File | Purpose |
|------|---------|
| `esp32_firmware/src/main.cpp` | ESP32 firmware |
| `esp32_firmware/src/config.h` | WiFi/URL config |
| `esp32_firmware/platformio.ini` | PlatformIO build config |
| `async_gateway.py` | API gateway (port 5000) |
| `scripts/full_diagnostic.sh` | Full system check |
| `scripts/test_upload.sh` | Test upload endpoint |
| `scripts/voice_commands.json` | Voice assistant config |
