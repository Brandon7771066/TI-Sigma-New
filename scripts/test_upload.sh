#!/bin/bash
# Test the Replit upload endpoint
# Usage: ./scripts/test_upload.sh

set -e

# Get the Replit URL from environment or use default
REPLIT_URL="${REPLIT_API_URL:-http://localhost:5000/api/upload}"

echo "🔬 Testing Mood Amplifier Upload Endpoint"
echo "==========================================="
echo "URL: $REPLIT_URL"
echo ""

# Test 1: Health check
echo "1️⃣ Health Check..."
HEALTH=$(curl -s -w "\n%{http_code}" http://localhost:5000/api/health 2>/dev/null || echo "failed")
if [[ "$HEALTH" == *"200"* ]]; then
    echo "   ✅ Server is healthy"
else
    echo "   ❌ Server not responding"
    echo "   Try: Restart the ti_website workflow"
    exit 1
fi

# Test 2: Simulated ESP32 upload
echo ""
echo "2️⃣ Simulated ESP32 Upload..."
UPLOAD_RESULT=$(curl -s -w "\n%{http_code}" \
    "http://localhost:5000/api/upload?hr=72&rr=833&rmssd=45.5&coh=0.65&alpha=0.85&beta=0.42&theta=0.55&gamma=0.22&delta=0.33&tp9=150&af7=140&af8=145&tp10=155&muse=1&polar=1&dev=TEST_SCRIPT&sid=test_$(date +%s)" \
    2>/dev/null)

HTTP_CODE=$(echo "$UPLOAD_RESULT" | tail -1)
BODY=$(echo "$UPLOAD_RESULT" | head -n -1)

if [[ "$HTTP_CODE" == "201" ]]; then
    echo "   ✅ Upload successful (HTTP 201)"
    echo "   Response: $BODY"
else
    echo "   ❌ Upload failed (HTTP $HTTP_CODE)"
    echo "   Response: $BODY"
fi

# Test 3: Verify data was stored
echo ""
echo "3️⃣ Verifying Data Storage..."
DEBUG=$(curl -s http://localhost:5000/api/debug 2>/dev/null)
TOTAL=$(echo "$DEBUG" | python3 -c "import sys,json; print(json.load(sys.stdin)['total_records'])" 2>/dev/null || echo "0")
LAST_AGE=$(echo "$DEBUG" | python3 -c "import sys,json; print(json.load(sys.stdin)['last_data_age'])" 2>/dev/null || echo "unknown")

echo "   📊 Total records: $TOTAL"
echo "   🕐 Last upload: $LAST_AGE"

if [[ "$LAST_AGE" == *"second"* ]] || [[ "$LAST_AGE" == *"just now"* ]]; then
    echo "   ✅ Data stored successfully!"
else
    echo "   ⚠️  Data may not have been stored (last upload was $LAST_AGE ago)"
fi

echo ""
echo "==========================================="
echo "✅ Test complete!"
