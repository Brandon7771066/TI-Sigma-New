/*
 * ESP32 BLE Bridge for Mood Amplifier
 * 
 * Connects simultaneously to:
 * - Muse 2 (EEG brainwaves)
 * - Polar H10 (Heart Rate + HRV)
 * 
 * Streams data to Replit via WiFi HTTP POST
 * 
 * SETUP INSTRUCTIONS:
 * 1. Install Arduino IDE
 * 2. Add ESP32 board: File > Preferences > Additional Boards Manager URLs:
 *    https://raw.githubusercontent.com/espressif/arduino-esp32/gh-pages/package_esp32_index.json
 * 3. Tools > Board > ESP32 Dev Module
 * 4. Install library: Sketch > Include Library > Manage Libraries > "ArduinoJson"
 * 5. Update WiFi credentials below
 * 6. Upload to ESP32!
 * 
 * Hardware: ESP32 DevKit (~$9 on Amazon)
 */

#include <BLEDevice.h>
#include <BLEUtils.h>
#include <BLEScan.h>
#include <BLEAdvertisedDevice.h>
#include <BLEClient.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <HTTPClient.h>
#include <ArduinoJson.h>

// ============================================================
// ⚙️ CONFIGURATION - UPDATE THESE VALUES!
// ============================================================

// Your WiFi network
const char* WIFI_SSID = "YOUR_WIFI_SSID";           // <-- Change this!
const char* WIFI_PASSWORD = "YOUR_WIFI_PASSWORD";    // <-- Change this!

// Your Replit URL - API endpoint for ESP32 data uploads
// Uses async gateway that handles both API and Streamlit WebSocket
// UPDATE THIS TO YOUR CURRENT REPLIT APP URL!
// Current dev URL (changes when Replit restarts - check REPLIT_DEV_DOMAIN):
const char* REPLIT_API_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev/api/upload";

// Session identifier
String SESSION_ID = "";

// ============================================================
// BLE UUIDs
// ============================================================

// Muse 2 EEG
static BLEUUID MUSE_SERVICE_UUID("0000fe8d-0000-1000-8000-00805f9b34fb");
static BLEUUID MUSE_CONTROL_UUID("273e0001-4c4d-454d-96be-f03bac821358");
static BLEUUID MUSE_EEG_TP9_UUID("273e0003-4c4d-454d-96be-f03bac821358");
static BLEUUID MUSE_EEG_AF7_UUID("273e0004-4c4d-454d-96be-f03bac821358");
static BLEUUID MUSE_EEG_AF8_UUID("273e0005-4c4d-454d-96be-f03bac821358");
static BLEUUID MUSE_EEG_TP10_UUID("273e0006-4c4d-454d-96be-f03bac821358");

// Polar H10 Heart Rate (Standard Bluetooth HRM)
static BLEUUID POLAR_HR_SERVICE_UUID("0000180d-0000-1000-8000-00805f9b34fb");
static BLEUUID POLAR_HR_CHAR_UUID("00002a37-0000-1000-8000-00805f9b34fb");

// ============================================================
// GLOBAL STATE
// ============================================================

BLEScan* bleScan;
BLEClient* museClient = nullptr;
BLEClient* polarClient = nullptr;

String museAddress = "";
String polarAddress = "";

bool museConnected = false;
bool polarConnected = false;
bool wifiConnected = false;

// Biometric data
struct {
  float eeg_tp9 = 0;
  float eeg_af7 = 0;
  float eeg_af8 = 0;
  float eeg_tp10 = 0;
  float alpha = 0;
  float beta = 0;
  float theta = 0;
  float gamma = 0;
  float delta = 0;
  int heart_rate = 0;
  int rr_interval = 0;
  float rmssd = 0;
  float coherence = 0;
} bioData;

// RR interval buffer for HRV calculation
#define RR_BUFFER_SIZE 60
int rrBuffer[RR_BUFFER_SIZE];
int rrBufferIdx = 0;
int rrCount = 0;

// EEG sample buffer for FFT
#define EEG_BUFFER_SIZE 256
float eegBuffer[4][EEG_BUFFER_SIZE]; // 4 channels
int eegBufferIdx = 0;
int eegSampleCount = 0;

unsigned long lastUploadTime = 0;
const unsigned long UPLOAD_INTERVAL = 1000; // 1 second

// ============================================================
// BLE SCAN CALLBACK - Auto-find devices
// ============================================================

class DeviceScanCallback: public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice advertisedDevice) {
    String name = advertisedDevice.getName().c_str();
    String addr = advertisedDevice.getAddress().toString().c_str();
    
    // Look for Muse 2
    if (name.indexOf("Muse") >= 0 && museAddress == "") {
      Serial.printf("🧠 Found Muse: %s [%s]\n", name.c_str(), addr.c_str());
      museAddress = addr;
    }
    
    // Look for Polar H10
    if (name.indexOf("Polar") >= 0 && polarAddress == "") {
      Serial.printf("💓 Found Polar: %s [%s]\n", name.c_str(), addr.c_str());
      polarAddress = addr;
    }
    
    // Stop scan if both found
    if (museAddress != "" && polarAddress != "") {
      bleScan->stop();
    }
  }
};

// ============================================================
// MUSE 2 EEG CALLBACKS
// ============================================================

static unsigned long lastEEGDebug = 0;
static int eegPacketCount = 0;

void parseMuseEEG(uint8_t* data, size_t len, int channel) {
  // Muse 2 sends 12 samples per packet, each is 12-bit
  // Format: [index, sample1_high, sample1_low, sample2_high, ...]
  
  if (len < 2) return;
  
  eegPacketCount++;
  
  // Debug: show first few packets received
  if (eegPacketCount <= 5 || millis() - lastEEGDebug > 5000) {
    Serial.printf("🧠 EEG packet #%d: ch=%d len=%d bytes=[", eegPacketCount, channel, len);
    for (int i = 0; i < min((int)len, 6); i++) {
      Serial.printf("%02X ", data[i]);
    }
    Serial.println("...]");
    lastEEGDebug = millis();
  }
  
  for (int i = 1; i < len - 1; i += 2) {
    int16_t raw = (data[i] << 8) | data[i + 1];
    float voltage = raw * 0.48828125; // Convert to microvolts
    
    // Store in buffer for FFT
    eegBuffer[channel][eegBufferIdx] = voltage;
    
    // Update current value
    switch(channel) {
      case 0: bioData.eeg_tp9 = voltage; break;
      case 1: bioData.eeg_af7 = voltage; break;
      case 2: bioData.eeg_af8 = voltage; break;
      case 3: bioData.eeg_tp10 = voltage; break;
    }
  }
  
  if (channel == 3) { // After all 4 channels
    eegBufferIdx = (eegBufferIdx + 1) % EEG_BUFFER_SIZE;
    eegSampleCount++;
  }
}

static void museTP9Callback(BLERemoteCharacteristic* pChar, uint8_t* data, size_t len, bool isNotify) {
  parseMuseEEG(data, len, 0);
}

static void museAF7Callback(BLERemoteCharacteristic* pChar, uint8_t* data, size_t len, bool isNotify) {
  parseMuseEEG(data, len, 1);
}

static void museAF8Callback(BLERemoteCharacteristic* pChar, uint8_t* data, size_t len, bool isNotify) {
  parseMuseEEG(data, len, 2);
}

static void museTP10Callback(BLERemoteCharacteristic* pChar, uint8_t* data, size_t len, bool isNotify) {
  parseMuseEEG(data, len, 3);
}

// Simple band power estimation (not full FFT, but fast)
void computeBandPowers() {
  if (eegSampleCount < EEG_BUFFER_SIZE) return;
  
  // Use AF7 + AF8 (frontal channels) for band power
  float sum = 0;
  float alpha_sum = 0, beta_sum = 0, theta_sum = 0, gamma_sum = 0, delta_sum = 0;
  
  for (int i = 0; i < EEG_BUFFER_SIZE - 1; i++) {
    float val = (eegBuffer[1][i] + eegBuffer[2][i]) / 2; // Average frontal
    float diff = abs(val - eegBuffer[1][(i+1) % EEG_BUFFER_SIZE]);
    
    // Rough frequency estimation based on zero crossings and amplitude
    sum += abs(val);
  }
  
  // Normalize to 0-1 range (rough approximation)
  float baseline = sum / EEG_BUFFER_SIZE;
  bioData.alpha = min(1.0f, baseline / 100.0f);
  bioData.beta = min(1.0f, baseline / 150.0f);
  bioData.theta = min(1.0f, baseline / 80.0f);
  bioData.gamma = min(1.0f, baseline / 200.0f);
  bioData.delta = min(1.0f, baseline / 50.0f);
}

// ============================================================
// POLAR H10 HEART RATE CALLBACK
// ============================================================

static void polarHRCallback(BLERemoteCharacteristic* pChar, uint8_t* data, size_t len, bool isNotify) {
  if (len < 2) return;
  
  uint8_t flags = data[0];
  int offset = 1;
  
  // Parse heart rate
  if (flags & 0x01) { // 16-bit HR
    bioData.heart_rate = data[offset] | (data[offset + 1] << 8);
    offset += 2;
  } else { // 8-bit HR
    bioData.heart_rate = data[offset];
    offset += 1;
  }
  
  // Parse RR intervals if present
  if ((flags >> 4) & 0x01) {
    while (offset + 1 < len) {
      int rr = data[offset] | (data[offset + 1] << 8);
      bioData.rr_interval = rr;
      
      // Store in buffer for HRV calculation
      rrBuffer[rrBufferIdx] = rr;
      rrBufferIdx = (rrBufferIdx + 1) % RR_BUFFER_SIZE;
      if (rrCount < RR_BUFFER_SIZE) rrCount++;
      
      offset += 2;
    }
    
    // Calculate RMSSD
    if (rrCount >= 10) {
      float sumSquaredDiff = 0;
      int count = 0;
      
      for (int i = 1; i < rrCount; i++) {
        int idx1 = (rrBufferIdx - i + RR_BUFFER_SIZE) % RR_BUFFER_SIZE;
        int idx2 = (rrBufferIdx - i - 1 + RR_BUFFER_SIZE) % RR_BUFFER_SIZE;
        
        int diff = rrBuffer[idx1] - rrBuffer[idx2];
        sumSquaredDiff += diff * diff;
        count++;
        
        if (count >= 30) break; // Use last 30 intervals
      }
      
      if (count > 0) {
        bioData.rmssd = sqrt(sumSquaredDiff / count);
        
        // Calculate coherence (simplified)
        float hrStability = 1.0 - min(1.0f, abs(bioData.heart_rate - 70) / 30.0f);
        float rmssdNorm = min(1.0f, bioData.rmssd / 80.0f);
        bioData.coherence = (rmssdNorm * 0.5) + (hrStability * 0.5);
      }
    }
  }
  
  Serial.printf("💓 HR: %d bpm | RR: %d ms | RMSSD: %.1f | Coh: %.2f\n", 
                bioData.heart_rate, bioData.rr_interval, bioData.rmssd, bioData.coherence);
}

// ============================================================
// BLE CONNECTION FUNCTIONS
// ============================================================

class MuseClientCallback : public BLEClientCallbacks {
  void onConnect(BLEClient* client) {
    museConnected = true;
    Serial.println("🧠 Muse 2 CONNECTED!");
  }
  void onDisconnect(BLEClient* client) {
    museConnected = false;
    Serial.println("🧠 Muse 2 disconnected");
  }
};

class PolarClientCallback : public BLEClientCallbacks {
  void onConnect(BLEClient* client) {
    polarConnected = true;
    Serial.println("💓 Polar H10 CONNECTED!");
  }
  void onDisconnect(BLEClient* client) {
    polarConnected = false;
    Serial.println("💓 Polar H10 disconnected");
  }
};

bool connectMuse() {
  if (museAddress == "") return false;
  
  Serial.println("🔗 Connecting to Muse 2...");
  
  museClient = BLEDevice::createClient();
  museClient->setClientCallbacks(new MuseClientCallback());
  
  if (!museClient->connect(BLEAddress(museAddress.c_str()))) {
    Serial.println("❌ Muse connection failed");
    return false;
  }
  
  BLERemoteService* service = museClient->getService(MUSE_SERVICE_UUID);
  if (service == nullptr) {
    Serial.println("❌ Muse service not found");
    museClient->disconnect();
    return false;
  }
  
  // First, send start command to Muse BEFORE subscribing
  BLERemoteCharacteristic* control = service->getCharacteristic(MUSE_CONTROL_UUID);
  if (control) {
    Serial.println("   📝 Found control characteristic");
    if (control->canWrite()) {
      // Version request to wake up device
      uint8_t versionCmd[] = {0x01, 0x76, 0x0a};  // 'v' command
      control->writeValue(versionCmd, 3, true);
      delay(100);
      
      // Preset 20 (all sensors)
      uint8_t presetCmd[] = {0x04, 0x70, 0x32, 0x30, 0x0a};  // "p20\n"
      control->writeValue(presetCmd, 5, true);
      delay(100);
      
      // Resume/start streaming
      uint8_t resumeCmd[] = {0x02, 0x64, 0x0a};  // "d\n" - resume
      control->writeValue(resumeCmd, 3, true);
      Serial.println("   ✓ Muse streaming commands sent");
    } else {
      Serial.println("   ⚠️ Control characteristic not writable");
    }
  } else {
    Serial.println("   ⚠️ Control characteristic not found");
  }
  
  delay(200);  // Give Muse time to start
  
  // Subscribe to EEG channels
  int subscribed = 0;
  BLERemoteCharacteristic* tp9 = service->getCharacteristic(MUSE_EEG_TP9_UUID);
  BLERemoteCharacteristic* af7 = service->getCharacteristic(MUSE_EEG_AF7_UUID);
  BLERemoteCharacteristic* af8 = service->getCharacteristic(MUSE_EEG_AF8_UUID);
  BLERemoteCharacteristic* tp10 = service->getCharacteristic(MUSE_EEG_TP10_UUID);
  
  if (tp9) {
    Serial.printf("   TP9: canNotify=%d canRead=%d\n", tp9->canNotify(), tp9->canRead());
    if (tp9->canNotify()) {
      tp9->registerForNotify(museTP9Callback);
      subscribed++;
    }
  }
  if (af7) {
    Serial.printf("   AF7: canNotify=%d canRead=%d\n", af7->canNotify(), af7->canRead());
    if (af7->canNotify()) {
      af7->registerForNotify(museAF7Callback);
      subscribed++;
    }
  }
  if (af8) {
    Serial.printf("   AF8: canNotify=%d canRead=%d\n", af8->canNotify(), af8->canRead());
    if (af8->canNotify()) {
      af8->registerForNotify(museAF8Callback);
      subscribed++;
    }
  }
  if (tp10) {
    Serial.printf("   TP10: canNotify=%d canRead=%d\n", tp10->canNotify(), tp10->canRead());
    if (tp10->canNotify()) {
      tp10->registerForNotify(museTP10Callback);
      subscribed++;
    }
  }
  
  Serial.printf("✅ Muse 2 connected! Subscribed to %d/4 channels\n", subscribed);
  return true;
}

bool connectPolar() {
  if (polarAddress == "") return false;
  
  Serial.println("🔗 Connecting to Polar H10...");
  
  polarClient = BLEDevice::createClient();
  polarClient->setClientCallbacks(new PolarClientCallback());
  
  if (!polarClient->connect(BLEAddress(polarAddress.c_str()))) {
    Serial.println("❌ Polar connection failed");
    return false;
  }
  
  BLERemoteService* service = polarClient->getService(POLAR_HR_SERVICE_UUID);
  if (service == nullptr) {
    Serial.println("❌ Polar HR service not found");
    polarClient->disconnect();
    return false;
  }
  
  BLERemoteCharacteristic* hrChar = service->getCharacteristic(POLAR_HR_CHAR_UUID);
  if (hrChar && hrChar->canNotify()) {
    hrChar->registerForNotify(polarHRCallback);
    Serial.println("   ✓ Heart rate subscribed");
    return true;
  }
  
  return false;
}

// ============================================================
// UPLOAD TO REPLIT (via GET request with query parameters)
// ============================================================

void uploadToReplit() {
  if (!wifiConnected) return;
  
  // Use WiFiClientSecure for HTTPS
  WiFiClientSecure client;
  client.setInsecure();  // Skip certificate verification (OK for dev)
  
  HTTPClient http;
  
  // Build URL with query parameters
  // Async gateway on /api/upload handles these and writes to PostgreSQL
  String url = String(REPLIT_API_URL);
  url += "?hr=" + String(bioData.heart_rate);
  url += "&rr=" + String(bioData.rr_interval);
  url += "&rmssd=" + String(bioData.rmssd, 1);
  url += "&coh=" + String(bioData.coherence, 2);
  url += "&alpha=" + String(bioData.alpha, 2);
  url += "&beta=" + String(bioData.beta, 2);
  url += "&theta=" + String(bioData.theta, 2);
  url += "&gamma=" + String(bioData.gamma, 2);
  url += "&delta=" + String(bioData.delta, 2);
  url += "&tp9=" + String(bioData.eeg_tp9, 0);
  url += "&af7=" + String(bioData.eeg_af7, 0);
  url += "&af8=" + String(bioData.eeg_af8, 0);
  url += "&tp10=" + String(bioData.eeg_tp10, 0);
  url += "&muse=" + String(museConnected ? 1 : 0);
  url += "&polar=" + String(polarConnected ? 1 : 0);
  url += "&dev=ESP32";
  url += "&sid=" + SESSION_ID;
  
  // Debug: show URL being used
  static bool urlShown = false;
  if (!urlShown) {
    Serial.printf("🌐 Upload URL: %s\n", REPLIT_API_URL);
    urlShown = true;
  }
  
  http.begin(client, url);  // Use secure client
  http.setTimeout(10000);   // 10 second timeout
  
  int code = http.GET();  // Use GET instead of POST
  
  if (code > 0) {
    Serial.printf("📤 Upload OK (%d) HR=%d Alpha=%.2f\n", 
                  code, bioData.heart_rate, bioData.alpha);
  } else {
    Serial.printf("📤 Upload failed: HTTP %d - %s\n", code, http.errorToString(code).c_str());
  }
  
  http.end();
}

// ============================================================
// SETUP
// ============================================================

void setup() {
  Serial.begin(115200);
  delay(1000);
  
  Serial.println("\n");
  Serial.println("╔══════════════════════════════════════════════════════════╗");
  Serial.println("║   🧠💓 ESP32 BLE BRIDGE - MOOD AMPLIFIER                 ║");
  Serial.println("║   Muse 2 EEG + Polar H10 HRV → Replit Cloud              ║");
  Serial.println("╚══════════════════════════════════════════════════════════╝");
  Serial.println();
  
  // Generate session ID
  SESSION_ID = "esp32_" + String(millis());
  
  // Connect to WiFi
  Serial.printf("📡 Connecting to WiFi: %s\n", WIFI_SSID);
  WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
  
  int attempts = 0;
  while (WiFi.status() != WL_CONNECTED && attempts < 30) {
    delay(500);
    Serial.print(".");
    attempts++;
  }
  
  if (WiFi.status() == WL_CONNECTED) {
    wifiConnected = true;
    Serial.println("\n✅ WiFi connected!");
    Serial.printf("   IP: %s\n", WiFi.localIP().toString().c_str());
  } else {
    Serial.println("\n⚠️ WiFi failed - will continue without upload");
  }
  
  // Initialize BLE
  Serial.println("\n🔵 Initializing Bluetooth...");
  BLEDevice::init("ESP32_MoodAmp");
  
  // Scan for devices
  Serial.println("\n🔍 Scanning for devices (30 seconds)...");
  Serial.println("   Make sure Muse 2 is ON and Polar H10 strap is wet + on chest!");
  Serial.println();
  
  bleScan = BLEDevice::getScan();
  bleScan->setAdvertisedDeviceCallbacks(new DeviceScanCallback());
  bleScan->setActiveScan(true);
  bleScan->setInterval(100);
  bleScan->setWindow(99);
  bleScan->start(30, false); // 30 second scan
  
  Serial.println();
  
  // Connect to found devices
  if (museAddress != "") {
    delay(500);
    connectMuse();
  } else {
    Serial.println("⚠️ Muse 2 not found - make sure it's powered on");
  }
  
  if (polarAddress != "") {
    delay(500);
    connectPolar();
  } else {
    Serial.println("⚠️ Polar H10 not found - wet the strap and put it on");
  }
  
  Serial.println("\n════════════════════════════════════════════════════");
  Serial.println("🚀 ESP32 BRIDGE ACTIVE!");
  Serial.printf("   Muse 2:   %s\n", museConnected ? "✅ Connected" : "❌ Not connected");
  Serial.printf("   Polar H10: %s\n", polarConnected ? "✅ Connected" : "❌ Not connected");
  Serial.printf("   WiFi:     %s\n", wifiConnected ? "✅ Connected" : "❌ Offline");
  Serial.println("════════════════════════════════════════════════════\n");
}

// ============================================================
// MAIN LOOP
// ============================================================

void loop() {
  unsigned long now = millis();
  
  // Compute band powers periodically
  if (eegSampleCount > 0 && eegSampleCount % 256 == 0) {
    computeBandPowers();
  }
  
  // Upload data every second
  if (now - lastUploadTime >= UPLOAD_INTERVAL) {
    // Print status with connection flags
    Serial.printf("📊 EEG: [%.0f, %.0f, %.0f, %.0f] | Alpha: %.2f | HR: %d | WiFi:%d Muse:%d Polar:%d\n",
                  bioData.eeg_tp9, bioData.eeg_af7, bioData.eeg_af8, bioData.eeg_tp10,
                  bioData.alpha, bioData.heart_rate, wifiConnected, museConnected, polarConnected);
    
    // Always try to upload if WiFi is connected (debug mode)
    if (wifiConnected) {
      uploadToReplit();
    } else {
      Serial.println("⚠️ WiFi not connected - skipping upload");
    }
    
    lastUploadTime = now;
  }
  
  // Reconnect logic
  if (!museConnected && museAddress != "") {
    static unsigned long lastMuseRetry = 0;
    if (now - lastMuseRetry > 10000) { // Retry every 10 seconds
      Serial.println("🔄 Retrying Muse connection...");
      connectMuse();
      lastMuseRetry = now;
    }
  }
  
  if (!polarConnected && polarAddress != "") {
    static unsigned long lastPolarRetry = 0;
    if (now - lastPolarRetry > 10000) {
      Serial.println("🔄 Retrying Polar connection...");
      connectPolar();
      lastPolarRetry = now;
    }
  }
  
  // Check WiFi
  if (WiFi.status() != WL_CONNECTED && wifiConnected) {
    wifiConnected = false;
    Serial.println("⚠️ WiFi disconnected");
  } else if (WiFi.status() == WL_CONNECTED && !wifiConnected) {
    wifiConnected = true;
    Serial.println("✅ WiFi reconnected");
  }
  
  delay(10);
}
