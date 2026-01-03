# ESP32 BLE Bridge - Mood Amplifier

Real-time biometric streaming from Muse 2 EEG and Polar H10 HRV to Replit cloud.

## Quick Start

### 1. Install PlatformIO CLI
```bash
# macOS/Linux
pip install platformio

# Or via Homebrew
brew install platformio
```

### 2. Configure Your Settings
Edit `src/config.h`:
```cpp
#define WIFI_SSID "YourWiFiName"
#define WIFI_PASSWORD "YourWiFiPassword"
#define REPLIT_API_URL "https://your-repl.replit.dev/api/upload"
```

### 3. Build & Upload
```bash
cd esp32_firmware

# Build only
pio run

# Build and upload (auto-detects port)
pio run --target upload

# Or specify port manually
pio run --target upload --upload-port /dev/ttyUSB0

# Monitor serial output
pio device monitor --baud 115200
```

### 4. Full Diagnostic Cycle
```bash
# One command: compile, upload, monitor
pio run --target upload && pio device monitor --baud 115200
```

## Voice Command Integration

For Acer voice assistant or similar:

| Voice Command | Action |
|--------------|--------|
| "Flash mood amplifier" | `pio run --target upload` |
| "Check ESP32 logs" | `pio device monitor --baud 115200` |
| "Run diagnostics" | `./scripts/full_diagnostic.sh` |
| "Test upload endpoint" | `./scripts/test_upload.sh` |

## Troubleshooting

### Common Issues

1. **Upload fails**: Check USB cable supports data (not charge-only)
2. **WiFi won't connect**: Verify SSID/password in config.h
3. **BLE devices not found**: Ensure Muse 2 is ON, Polar strap is wet
4. **Server connection refused**: Check Replit URL is correct and server is running

### Debug Commands
```bash
# List available ports
pio device list

# Check ESP32 flash
esptool.py --port /dev/ttyUSB0 flash_id

# Erase flash and start fresh
pio run --target erase
```

## Hardware Setup

- **ESP32**: Any ESP32 DevKit (WROOM, WROVER, etc.)
- **Muse 2**: Bluetooth EEG headband
- **Polar H10**: Bluetooth heart rate strap (wet electrodes!)

## File Structure
```
esp32_firmware/
├── platformio.ini     # PlatformIO config
├── src/
│   ├── main.cpp       # Main firmware code
│   └── config.h       # User configuration
├── include/           # Header files
├── lib/               # External libraries
└── test/              # Unit tests
```
