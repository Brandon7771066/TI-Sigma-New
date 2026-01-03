# 🌉 Mendi Data Bridge - Quick Start Guide

## 📡 **How to Upload Real Mendi Data to Replit**

There are **3 ways** to get your real Mendi fNIRS data into the platform:

---

## **Method 1: HTTP API Upload (Recommended)**

### **Step 1: Check API Status**
The Mendi Data Bridge API runs on port 8000. Check if it's running:
```bash
curl http://localhost:8000/health
```

Expected response:
```json
{
  "status": "healthy",
  "service": "Mendi Data Bridge API",
  "timestamp": "2025-11-23T11:00:00"
}
```

### **Step 2: Install Companion Uploader**
Download `mendi_companion_uploader.py` to your computer.

### **Step 3: Stream Demo Data (Test)**
```bash
python mendi_companion_uploader.py \
  --api-url https://YOUR-REPL-URL:8000 \
  --mode demo \
  --duration 60 \
  --hz 1.0
```

### **Step 4: Upload Real Data from CSV**
If you can export Mendi data as CSV:

**CSV Format:**
```csv
timestamp,hbo2,hbr,signal_quality
2025-11-23T08:30:00,65.3,45.2,0.87
2025-11-23T08:30:01,66.1,44.8,0.89
2025-11-23T08:30:02,64.9,45.5,0.85
```

**Upload:**
```bash
python mendi_companion_uploader.py \
  --api-url https://YOUR-REPL-URL:8000 \
  --mode csv \
  --csv-file my_mendi_data.csv
```

### **Step 5: Manual Entry (Quick Test)**
```bash
python mendi_companion_uploader.py \
  --api-url https://YOUR-REPL-URL:8000 \
  --mode manual
```

Then enter values:
```
Enter HbO2 HbR: 65.3 45.2
Enter HbO2 HbR: 66.1 44.8
Enter HbO2 HbR: quit
```

---

## **Method 2: Direct Database Upload (Alternative)**

If the API isn't working, upload directly to database:

```python
import psycopg2
import os
from datetime import datetime

# Connect to database
conn = psycopg2.connect(os.environ['DATABASE_URL'])
cur = conn.cursor()

# Upload a sample
cur.execute("""
    INSERT INTO mendi_realtime_data 
    (timestamp, hbo2, hbr, total_hb, oxygenation_percent, 
     signal_quality, device_id, session_id, metadata)
    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
""", (
    datetime.now(),
    65.3,  # HbO2
    45.2,  # HbR
    110.5,  # Total Hb
    59.1,   # Oxygenation %
    0.87,   # Quality
    'manual-upload',
    'session-test-001',
    '{}'
))

conn.commit()
cur.close()
conn.close()
print("✅ Data uploaded!")
```

---

## **Method 3: File Upload via Streamlit UI** (Coming Soon)

A file uploader widget in the Streamlit app where you can:
1. Export data from Mendi app
2. Upload CSV/JSON file through browser
3. Data automatically imported to database
4. View in real-time dashboard

---

## **Viewing Your Data**

Once uploaded, view your data in the Streamlit app:
1. Go to **"🔬 Baseline Collection"** tab
2. Select session from dropdown
3. See real-time brain oxygenation graphs
4. Run LCC Optimization on your data!

---

## **API Endpoints Reference**

### Upload Single Sample
```bash
curl -X POST http://localhost:8000/api/mendi/upload \
  -H "Content-Type: application/json" \
  -d '{
    "timestamp": "2025-11-23T08:30:00",
    "hbo2": 65.3,
    "hbr": 45.2,
    "signal_quality": 0.87
  }'
```

### Upload Batch
```bash
curl -X POST http://localhost:8000/api/mendi/upload \
  -H "Content-Type: application/json" \
  -d '{
    "samples": [
      {"timestamp": "2025-11-23T08:30:00", "hbo2": 65.3, "hbr": 45.2},
      {"timestamp": "2025-11-23T08:30:01", "hbo2": 66.1, "hbr": 44.8}
    ]
  }'
```

### Get Latest Data
```bash
curl http://localhost:8000/api/mendi/latest?limit=50
```

### Get All Sessions
```bash
curl http://localhost:8000/api/mendi/sessions
```

---

## **Troubleshooting**

### API Not Responding
1. Check if workflow is running: Look for "mendi_api" in workflows
2. Restart workflow if needed
3. Verify port 8000 is accessible

### Database Connection Errors
- Ensure `DATABASE_URL` environment variable is set
- Check database connection in Replit console

### File Upload Errors
- Verify CSV format matches expected columns
- Check timestamp format: ISO 8601 (YYYY-MM-DDTHH:MM:SS)
- Ensure numeric values for hbo2, hbr

---

## **Next Steps**

Once you have data uploaded:
1. ✅ View real-time fNIRS dashboard
2. ✅ Run LCC Optimization for personalized protocols
3. ✅ Test Mood Amplifier with real brain data
4. ✅ Compare baseline vs treatment measurements

🚀 **Happy brain hacking!**
