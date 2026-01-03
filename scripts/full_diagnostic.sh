#!/bin/bash
# Full Mood Amplifier Diagnostic
# Voice command: "Run full mood amplifier diagnostics"
# Usage: ./scripts/full_diagnostic.sh

set -e

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  🧠💓 MOOD AMPLIFIER FULL DIAGNOSTIC                         ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Function to print section headers
section() {
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  $1"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
}

# Collect results
ISSUES=()
SUCCESSES=()

section "1. REPLIT SERVER STATUS"
HEALTH=$(curl -s http://localhost:5000/api/health 2>/dev/null || echo '{"error":"failed"}')
if echo "$HEALTH" | grep -q "healthy"; then
    echo "✅ Server: Running on port 5000"
    SUCCESSES+=("Server healthy")
else
    echo "❌ Server: Not responding"
    ISSUES+=("Server not running - restart ti_website workflow")
fi

section "2. DATABASE CONNECTION"
DEBUG=$(curl -s http://localhost:5000/api/debug 2>/dev/null || echo '{"error":"failed"}')
TOTAL=$(echo "$DEBUG" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('total_records', 0))" 2>/dev/null || echo "0")
LAST_AGE=$(echo "$DEBUG" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('last_data_age', 'unknown'))" 2>/dev/null || echo "unknown")

echo "📊 Total biometric records: $TOTAL"
echo "🕐 Last data received: $LAST_AGE"

if [[ "$TOTAL" -gt 0 ]]; then
    SUCCESSES+=("Database has $TOTAL records")
else
    ISSUES+=("Database empty - no uploads received yet")
fi

section "3. UPLOAD ENDPOINT TEST"
TEST_SID="diag_$(date +%s)"
UPLOAD_RESULT=$(curl -s -w "\n%{http_code}" \
    "http://localhost:5000/api/upload?hr=72&alpha=0.5&dev=DIAGNOSTIC&sid=$TEST_SID" \
    2>/dev/null)
HTTP_CODE=$(echo "$UPLOAD_RESULT" | tail -1)

if [[ "$HTTP_CODE" == "201" ]]; then
    echo "✅ Upload endpoint: Working (HTTP 201)"
    SUCCESSES+=("Upload endpoint functional")
else
    echo "❌ Upload endpoint: Failed (HTTP $HTTP_CODE)"
    ISSUES+=("Upload endpoint returning HTTP $HTTP_CODE")
fi

section "4. ESP32 FIRMWARE STATUS"
if [ -f "esp32_firmware/src/main.cpp" ]; then
    echo "✅ Firmware source: Present"
    
    # Check config
    if [ -f "esp32_firmware/src/config.h" ]; then
        WIFI_SET=$(grep "YOUR_WIFI" esp32_firmware/src/config.h | wc -l)
        if [[ "$WIFI_SET" -gt 0 ]]; then
            echo "⚠️  Config: WiFi credentials not set (still has placeholder)"
            ISSUES+=("ESP32 WiFi not configured in config.h")
        else
            echo "✅ Config: WiFi credentials appear to be set"
        fi
    fi
    
    SUCCESSES+=("ESP32 firmware present")
else
    echo "⚠️  Firmware source not found"
    ISSUES+=("ESP32 firmware missing from esp32_firmware/src/")
fi

section "5. PLATFORMIO CHECK"
if command -v pio &> /dev/null; then
    PIO_VERSION=$(pio --version 2>/dev/null)
    echo "✅ PlatformIO: $PIO_VERSION"
    SUCCESSES+=("PlatformIO installed")
else
    echo "⚠️  PlatformIO: Not installed locally"
    echo "   Install: pip install platformio"
    ISSUES+=("PlatformIO not installed (needed for ESP32 flashing)")
fi

section "6. RECENT UPLOADS"
echo "$DEBUG" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    uploads = d.get('recent_uploads', [])
    if uploads:
        for u in uploads[:3]:
            ts = u.get('timestamp', 'unknown')[:19]
            dev = u.get('device', '?')
            hr = u.get('hr', 0)
            alpha = u.get('alpha', 0)
            print(f'  {ts} | {dev:15} | HR={hr:3} Alpha={alpha:.2f}')
    else:
        print('  No recent uploads')
except:
    print('  Unable to parse upload data')
" 2>/dev/null || echo "  Unable to fetch recent uploads"

# Summary
echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  DIAGNOSTIC SUMMARY                                          ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

if [[ ${#SUCCESSES[@]} -gt 0 ]]; then
    echo "✅ WORKING (${#SUCCESSES[@]}):"
    for s in "${SUCCESSES[@]}"; do
        echo "   • $s"
    done
fi

echo ""

if [[ ${#ISSUES[@]} -gt 0 ]]; then
    echo "❌ ISSUES (${#ISSUES[@]}):"
    for i in "${ISSUES[@]}"; do
        echo "   • $i"
    done
    echo ""
    echo "📋 NEXT STEPS:"
    echo "   1. Fix issues listed above"
    echo "   2. Run: ./scripts/test_upload.sh"
    echo "   3. Flash ESP32 and monitor: pio run --target upload && pio device monitor"
else
    echo "🎉 ALL SYSTEMS OPERATIONAL!"
    echo ""
    echo "Ready for Mood Amplifier session."
fi

echo ""
