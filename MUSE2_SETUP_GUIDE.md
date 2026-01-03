# Muse 2 Integration Setup Guide

## 🚨 Why Muse 2 Cannot Connect Directly in Replit

**The Problem**: Bluetooth LE requires native device access (`/dev/bluetooth`) which **does not exist** in Replit's containerized Linux environment.

**The Error**: `[Errno 2] No such file or directory` when trying to scan for BLE devices.

**The Solution**: Use an **external OSC bridge** running on your phone or laptop.

---

## ✅ Complete Setup Instructions

### Step 1: Install Companion App on Your Phone/Laptop

On a device with Bluetooth (your phone, laptop, etc.):

```bash
# Install dependencies
pip install bleak python-osc

# Download the companion script (already in this repository)
# File: muse2_osc_bridge_companion.py
```

### Step 2: Get Your Replit App IP Address

1. Open your Replit app in browser
2. Find the URL (e.g., `https://your-app.replit.app`)
3. Extract the IP address or use the domain name

### Step 3: Run the Companion App

```bash
python muse2_osc_bridge_companion.py --target-ip your-app.replit.app --target-port 5005
```

The script will:
1. 🔍 Auto-discover your Muse 2 headband
2. 🔗 Connect via Bluetooth LE
3. 📡 Forward EEG data to your Replit app via OSC

### Step 4: Confirm Connection in Streamlit App

Your Streamlit app will show:
- ✅ "Muse 2: OSC Stream Active"
- Real-time EEG data flowing from TP9, AF7, AF8, TP10 channels

---

## 📡 How It Works

```
Your Phone/Laptop                  Replit Cloud
┌──────────────────┐              ┌──────────────────┐
│                  │              │                  │
│  Muse 2 Bridge   │─────OSC─────▶│  Streamlit App   │
│  (companion.py)  │  Port 5005   │                  │
│                  │              │                  │
└────────┬─────────┘              └──────────────────┘
         │
     Bluetooth LE
         │
    ┌────▼────┐
    │ Muse 2  │
    │Headband │
    └─────────┘
```

**OSC (Open Sound Control)**: A network protocol for transmitting sensor data. Perfect for real-time biometric streaming!

---

## 🧪 Alternative: Demo Mode

If you don't want to set up the bridge right now:

1. Navigate to **Mobile Hub** → **Baseline Collection**
2. Check **"Use Demo Mode"**
3. Click **"✨ Generate Demo Baseline"**
4. Test the complete LCC optimization workflow with synthetic data!

---

## 🔧 Troubleshooting

### Companion App: "No Muse device found"
- Ensure Muse 2 is powered on
- Disconnect from Muse app if connected
- Move closer to the device

### Companion App: "Connection failed"
- Try restarting the Muse 2 headband
- Check Bluetooth is enabled on your device
- Try specifying MAC address manually:
  ```bash
  python muse2_osc_bridge_companion.py --target-ip your-app.replit.app --device-address XX:XX:XX:XX:XX:XX
  ```

### Streamlit App: Not receiving data
- Verify companion app shows "📊 Stats: X packets sent"
- Check firewall settings (port 5005 must be open)
- Try using IP address instead of domain name

---

## 📊 Data Flow

Once connected, you'll see real-time EEG data:
- **TP9** (left temporal): Emotional processing
- **AF7** (left frontal): Logical processing  
- **AF8** (right frontal): Creative processing
- **TP10** (right temporal): Spatial processing

All 4 channels stream at **256 Hz** with **12-bit resolution**!

---

## 🎯 Next Steps

After Muse 2 is streaming:
1. Navigate to **Baseline Collection**
2. Click "▶️ Start 60s Baseline"
3. Collect real multi-modal biometric data
4. Generate personalized LCC protocols using YOUR genome!
5. Validate the TI Framework with YOUR consciousness data!

---

## 💡 Future: Native Mobile App

To avoid the companion script, a native mobile app could:
- Connect to Muse 2 directly
- Run the full Streamlit interface locally
- Upload baselines to cloud for analysis

For now, the OSC bridge provides production-ready Muse 2 integration! 🚀
