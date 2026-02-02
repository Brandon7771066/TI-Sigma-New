# ESP32 Biometric Bridge Setup Guide

## The Core Challenge

**Replit runs in the cloud** - it has no Bluetooth hardware. We cannot directly connect to your Muse 2 EEG or Polar H10 from Replit servers.

## The Solution: ESP32 Bridge

The ESP32 microcontroller acts as a **local Bluetooth-to-Internet bridge**:

```
[Muse 2] --BLE--> [ESP32] --HTTP--> [Replit Server] --> [Your Dashboard]
[Polar H10] --BLE-->     |
```

## What You Need

### Hardware Required
1. **ESP32 Development Board** (~$10)
   - ESP32-WROOM-32 or ESP32-DevKitC recommended
   - Must have Bluetooth LE support (all ESP32s do)
   
2. **Your Existing Devices**
   - Muse 2 EEG Headband (already have)
   - Polar H10 Chest Strap (already have)

3. **WiFi Network**
   - 2.4GHz network (ESP32 doesn't support 5GHz)
   - Internet access to reach Replit

### Software Required
1. **Arduino IDE** (https://www.arduino.cc/en/software)
2. **ESP32 Board Package** (installed via Arduino Board Manager)
3. **Required Libraries** (installed via Arduino Library Manager):
   - `BLEDevice.h` (included with ESP32 package)
   - `WiFi.h` (included with ESP32 package)
   - `HTTPClient.h` (included with ESP32 package)

---

## Previous Blockers Identified

### 1. bleak Library Limitation
The Python `bleak` library in `muse2_integration.py` and `polar_h10_real_integration.py` requires:
- Local Bluetooth hardware access
- System-level BLE permissions
- **Neither available in Replit cloud environment**

### 2. No ESP32 Firmware Provided
The gateway endpoint (`/api/upload`) exists and is ready, but there was no ESP32 firmware code to:
- Connect to Muse 2 and Polar H10
- Parse the BLE data
- Forward to Replit

### 3. Device MAC Addresses Needed
BLE connections require knowing the MAC addresses of your specific devices.

---

## Complete Setup Instructions

### Step 1: Find Your Device MAC Addresses

**For Polar H10:**
- Open Polar Beat app → Settings → Connected devices
- Or use a BLE scanner app (nRF Connect)
- Format: `A0:9E:1A:XX:XX:XX`

**For Muse 2:**
- Muse app doesn't show MAC address
- Use nRF Connect app to scan for "Muse-XXXX"
- Note the address shown

### Step 2: Install Arduino IDE and ESP32 Support

1. Download Arduino IDE from https://www.arduino.cc/en/software
2. Go to File → Preferences
3. Add to "Additional Board Manager URLs":
   ```
   https://dl.espressif.com/dl/package_esp32_index.json
   ```
4. Go to Tools → Board → Boards Manager
5. Search "ESP32" and install "esp32 by Espressif Systems"

### Step 3: Flash the ESP32 Firmware

See `ESP32_BRIDGE_FIRMWARE.ino` for the complete code.

Key configuration:
```cpp
// WiFi credentials
const char* ssid = "YOUR_WIFI_SSID";
const char* password = "YOUR_WIFI_PASSWORD";

// Replit server URL
const char* serverUrl = "https://YOUR-REPLIT-URL.replit.app/api/upload";

// Device MAC addresses
const char* polarMac = "A0:9E:1A:XX:XX:XX";  // Your Polar H10
const char* museMac = "XX:XX:XX:XX:XX:XX";   // Your Muse 2
```

### Step 4: Upload and Run

1. Connect ESP32 to computer via USB
2. Select board: Tools → Board → ESP32 Dev Module
3. Select port: Tools → Port → (your ESP32)
4. Click Upload
5. Open Serial Monitor (115200 baud) to see connection status

---

## API Endpoint Details

The Replit server is already configured to receive data at:

```
POST /api/upload
Content-Type: application/json

{
  "hr": 72,              // Heart rate (bpm)
  "rr": 850,             // RR interval (ms)
  "alpha": 0.45,         // EEG alpha power (normalized)
  "theta": 0.30,         // EEG theta power
  "beta": 0.15,          // EEG beta power
  "gamma": 0.10,         // EEG gamma power
  "device": "ESP32",     // Device identifier
  "polar": 1,            // Polar H10 connected (0/1)
  "muse": 1              // Muse 2 connected (0/1)
}
```

Or as query parameters:
```
GET /api/upload?hr=72&rr=850&alpha=0.45&theta=0.30&polar=1&muse=1
```

---

## Troubleshooting

### ESP32 won't connect to WiFi
- Verify 2.4GHz network (not 5GHz)
- Check SSID and password (case-sensitive)
- Try moving closer to router

### Polar H10 not found
- Make sure chest strap is wet (electrodes need moisture)
- Put strap on chest (it won't advertise without skin contact)
- Check MAC address is correct

### Muse 2 not found
- Turn on Muse 2 (touch sensors on forehead)
- Check it's not connected to another device (phone)
- Verify MAC address

### Data not appearing in Replit
- Check ESP32 serial monitor for HTTP responses
- Verify Replit URL is correct
- Test endpoint: `curl "YOUR_URL/api/upload?hr=72&test=1"`

---

## Alternative: Phone Bridge (No ESP32)

If you don't have an ESP32, you can use your phone as a bridge:

1. Connect Muse 2 to Muse app
2. Connect Polar H10 to Polar Beat app
3. Use a Python script on your computer to:
   - Connect to Muse via OSC (Mind Monitor app exports OSC)
   - Read Polar data via Bluetooth
   - Forward to Replit

This requires your computer to have Bluetooth and be running constantly.

---

## Status

| Component | Status |
|-----------|--------|
| Gateway API (`/api/upload`) | READY |
| Database storage | READY |
| Biometric dashboard | READY |
| ESP32 firmware | PROVIDED BELOW |
| Your hardware setup | PENDING |

**Next Step:** Flash the ESP32 firmware and provide your WiFi credentials + device MAC addresses.
