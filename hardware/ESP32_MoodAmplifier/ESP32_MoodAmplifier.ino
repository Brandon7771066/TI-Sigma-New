/*
 * ESP32 MOOD AMPLIFIER BLE BRIDGE
 * ================================
 * Connects to:
 * - Polar H10 C895672B (Heart Rate / HRV)
 * - Muse-2E34 (EEG) 
 * - Mendi (fNIRS)
 * 
 * Sends data to Replit server via WiFi
 * 
 * Created: November 27, 2025 (Thanksgiving Eve - Euler-Tralse Discovery Day!)
 */

#include <NimBLEDevice.h>
#include <WiFi.h>
#include <HTTPClient.h>
#include <ArduinoJson.h>

// ==================== CONFIGURATION ====================
// TODO: Change these to your actual values!

const char* WIFI_SSID = "YOUR_WIFI_NAME";
const char* WIFI_PASSWORD = "YOUR_WIFI_PASSWORD";

// Your Replit server URL (we'll set this up)
const char* SERVER_URL = "https://YOUR_REPLIT_URL/api/biometric-data";

// Device names from your nRF Connect scan
const char* POLAR_H10_NAME = "Polar H10 C895672B";
const char* MUSE_NAME = "Muse-2E34";
const char* MENDI_NAME = "Mendi";

// ==================== BLE UUIDs ====================

// Polar H10 - Standard Heart Rate Service
static NimBLEUUID HR_SERVICE_UUID("180D");
static NimBLEUUID HR_CHARACTERISTIC_UUID("2A37");

// Mendi - Custom Service
static NimBLEUUID MENDI_SERVICE_UUID("FC3EABB0-C6C4-49E6-922A-6E551C455AF5");

// Muse - Control Service
static NimBLEUUID MUSE_SERVICE_UUID("0000FE8D-0000-1000-8000-00805F9B34FB");

// ==================== GLOBAL VARIABLES ====================

NimBLEClient* polarClient = nullptr;
NimBLEClient* mendiClient = nullptr;
NimBLEClient* museClient = nullptr;

bool polarConnected = false;
bool mendiConnected = false;
bool museConnected = false;

// Biometric data storage
struct BiometricData {
  // Polar H10
  uint8_t heartRate = 0;
  uint16_t rrIntervals[10];
  uint8_t rrCount = 0;
  
  // Mendi (fNIRS)
  float oxygenation = 0.0;
  float hemoglobin = 0.0;
  
  // Muse (EEG)
  float eegChannels[4] = {0, 0, 0, 0};  // TP9, AF7, AF8, TP10
  float attention = 0.0;
  float meditation = 0.0;
  
  // Timestamps
  unsigned long lastUpdate = 0;
} bioData;

// ==================== CALLBACK CLASSES ====================

// Heart Rate notification callback
void hrNotifyCallback(NimBLERemoteCharacteristic* pCharacteristic, 
                      uint8_t* pData, size_t length, bool isNotify) {
  if (length >= 2) {
    // First byte contains flags
    uint8_t flags = pData[0];
    
    // Check if heart rate is 8-bit or 16-bit
    if (flags & 0x01) {
      // 16-bit heart rate
      bioData.heartRate = pData[1] | (pData[2] << 8);
    } else {
      // 8-bit heart rate
      bioData.heartRate = pData[1];
    }
    
    // Check for RR intervals (for HRV calculation)
    if (flags & 0x10) {
      int offset = (flags & 0x01) ? 3 : 2;
      bioData.rrCount = 0;
      while (offset + 1 < length && bioData.rrCount < 10) {
        bioData.rrIntervals[bioData.rrCount] = pData[offset] | (pData[offset + 1] << 8);
        bioData.rrCount++;
        offset += 2;
      }
    }
    
    bioData.lastUpdate = millis();
    
    Serial.printf("Heart Rate: %d BPM", bioData.heartRate);
    if (bioData.rrCount > 0) {
      Serial.printf(" | RR Intervals: ");
      for (int i = 0; i < bioData.rrCount; i++) {
        Serial.printf("%d ", bioData.rrIntervals[i]);
      }
    }
    Serial.println();
  }
}

// Mendi notification callback
void mendiNotifyCallback(NimBLERemoteCharacteristic* pCharacteristic,
                         uint8_t* pData, size_t length, bool isNotify) {
  // Mendi data parsing (this may need adjustment based on actual protocol)
  if (length >= 4) {
    // Example parsing - actual format may differ
    bioData.oxygenation = (float)pData[0] + (float)pData[1] / 100.0;
    bioData.hemoglobin = (float)pData[2] + (float)pData[3] / 100.0;
    bioData.lastUpdate = millis();
    
    Serial.printf("Mendi - Oxygenation: %.2f%% | Hemoglobin: %.2f\n", 
                  bioData.oxygenation, bioData.hemoglobin);
  }
}

// Muse notification callback
void museNotifyCallback(NimBLERemoteCharacteristic* pCharacteristic,
                        uint8_t* pData, size_t length, bool isNotify) {
  // Muse data parsing - complex protocol
  // This is simplified - actual Muse parsing is more complex
  if (length >= 8) {
    // Example parsing for EEG channels
    for (int i = 0; i < 4 && i * 2 + 1 < length; i++) {
      bioData.eegChannels[i] = (float)(pData[i * 2] | (pData[i * 2 + 1] << 8)) / 1000.0;
    }
    bioData.lastUpdate = millis();
    
    Serial.printf("Muse EEG - TP9: %.3f | AF7: %.3f | AF8: %.3f | TP10: %.3f\n",
                  bioData.eegChannels[0], bioData.eegChannels[1],
                  bioData.eegChannels[2], bioData.eegChannels[3]);
  }
}

// ==================== CONNECTION FUNCTIONS ====================

bool connectToPolar() {
  Serial.println("Scanning for Polar H10...");
  
  NimBLEScan* pScan = NimBLEDevice::getScan();
  pScan->setActiveScan(true);
  NimBLEScanResults results = pScan->start(5);
  
  for (int i = 0; i < results.getCount(); i++) {
    NimBLEAdvertisedDevice device = results.getDevice(i);
    
    if (device.getName() == POLAR_H10_NAME) {
      Serial.println("Found Polar H10! Connecting...");
      
      polarClient = NimBLEDevice::createClient();
      
      if (polarClient->connect(&device)) {
        Serial.println("Connected to Polar H10!");
        
        // Get Heart Rate Service
        NimBLERemoteService* hrService = polarClient->getService(HR_SERVICE_UUID);
        if (hrService) {
          NimBLERemoteCharacteristic* hrChar = hrService->getCharacteristic(HR_CHARACTERISTIC_UUID);
          if (hrChar && hrChar->canNotify()) {
            hrChar->subscribe(true, hrNotifyCallback);
            Serial.println("Subscribed to Heart Rate notifications!");
            polarConnected = true;
            return true;
          }
        }
      }
    }
  }
  
  Serial.println("Polar H10 not found or connection failed");
  return false;
}

bool connectToMendi() {
  Serial.println("Scanning for Mendi...");
  
  NimBLEScan* pScan = NimBLEDevice::getScan();
  pScan->setActiveScan(true);
  NimBLEScanResults results = pScan->start(5);
  
  for (int i = 0; i < results.getCount(); i++) {
    NimBLEAdvertisedDevice device = results.getDevice(i);
    
    if (device.getName() == MENDI_NAME) {
      Serial.println("Found Mendi! Connecting...");
      
      mendiClient = NimBLEDevice::createClient();
      
      if (mendiClient->connect(&device)) {
        Serial.println("Connected to Mendi!");
        
        // Get Mendi Service
        NimBLERemoteService* mendiService = mendiClient->getService(MENDI_SERVICE_UUID);
        if (mendiService) {
          // Get all characteristics and find the notify one
          std::vector<NimBLERemoteCharacteristic*>* chars = mendiService->getCharacteristics(true);
          for (auto& c : *chars) {
            if (c->canNotify()) {
              c->subscribe(true, mendiNotifyCallback);
              Serial.println("Subscribed to Mendi notifications!");
              mendiConnected = true;
              return true;
            }
          }
        }
      }
    }
  }
  
  Serial.println("Mendi not found or connection failed");
  return false;
}

bool connectToMuse() {
  Serial.println("Scanning for Muse...");
  
  NimBLEScan* pScan = NimBLEDevice::getScan();
  pScan->setActiveScan(true);
  NimBLEScanResults results = pScan->start(5);
  
  for (int i = 0; i < results.getCount(); i++) {
    NimBLEAdvertisedDevice device = results.getDevice(i);
    
    if (device.getName() == MUSE_NAME) {
      Serial.println("Found Muse! Connecting...");
      
      museClient = NimBLEDevice::createClient();
      
      if (museClient->connect(&device)) {
        Serial.println("Connected to Muse!");
        
        // Muse requires specific initialization sequence
        // This is a simplified version - full Muse protocol is complex
        NimBLERemoteService* museService = museClient->getService(MUSE_SERVICE_UUID);
        if (museService) {
          std::vector<NimBLERemoteCharacteristic*>* chars = museService->getCharacteristics(true);
          for (auto& c : *chars) {
            if (c->canNotify()) {
              c->subscribe(true, museNotifyCallback);
              Serial.println("Subscribed to Muse notifications!");
              museConnected = true;
              return true;
            }
          }
        }
      }
    }
  }
  
  Serial.println("Muse not found or connection failed");
  return false;
}

// ==================== WIFI & SERVER FUNCTIONS ====================

void connectWiFi() {
  Serial.printf("Connecting to WiFi: %s\n", WIFI_SSID);
  WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
  
  int attempts = 0;
  while (WiFi.status() != WL_CONNECTED && attempts < 30) {
    delay(500);
    Serial.print(".");
    attempts++;
  }
  
  if (WiFi.status() == WL_CONNECTED) {
    Serial.println("\nWiFi Connected!");
    Serial.printf("IP Address: %s\n", WiFi.localIP().toString().c_str());
  } else {
    Serial.println("\nWiFi Connection Failed!");
  }
}

void sendDataToServer() {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("WiFi not connected, skipping data send");
    return;
  }
  
  HTTPClient http;
  http.begin(SERVER_URL);
  http.addHeader("Content-Type", "application/json");
  
  // Create JSON payload
  StaticJsonDocument<512> doc;
  
  // Polar H10 data
  doc["heart_rate"] = bioData.heartRate;
  JsonArray rrArray = doc.createNestedArray("rr_intervals");
  for (int i = 0; i < bioData.rrCount; i++) {
    rrArray.add(bioData.rrIntervals[i]);
  }
  
  // Mendi data
  doc["oxygenation"] = bioData.oxygenation;
  doc["hemoglobin"] = bioData.hemoglobin;
  
  // Muse data
  JsonArray eegArray = doc.createNestedArray("eeg_channels");
  for (int i = 0; i < 4; i++) {
    eegArray.add(bioData.eegChannels[i]);
  }
  doc["attention"] = bioData.attention;
  doc["meditation"] = bioData.meditation;
  
  // Connection status
  doc["polar_connected"] = polarConnected;
  doc["mendi_connected"] = mendiConnected;
  doc["muse_connected"] = museConnected;
  
  // Timestamp
  doc["timestamp"] = millis();
  
  String jsonString;
  serializeJson(doc, jsonString);
  
  int httpResponseCode = http.POST(jsonString);
  
  if (httpResponseCode > 0) {
    Serial.printf("Data sent! Response: %d\n", httpResponseCode);
  } else {
    Serial.printf("Error sending data: %s\n", http.errorToString(httpResponseCode).c_str());
  }
  
  http.end();
}

// ==================== MAIN FUNCTIONS ====================

void setup() {
  Serial.begin(115200);
  delay(1000);
  
  Serial.println();
  Serial.println("===============================================");
  Serial.println("   ESP32 MOOD AMPLIFIER BLE BRIDGE");
  Serial.println("   Euler-Tralse Discovery Day: 11/27/25");
  Serial.println("===============================================");
  Serial.println();
  
  // Initialize BLE
  Serial.println("Initializing BLE...");
  NimBLEDevice::init("MoodAmplifier");
  
  // Connect to WiFi
  connectWiFi();
  
  Serial.println();
  Serial.println("Starting device connections...");
  Serial.println("-------------------------------");
  
  // Try to connect to each device
  // Start with Polar H10 (most reliable)
  connectToPolar();
  delay(1000);
  
  // Then Mendi
  connectToMendi();
  delay(1000);
  
  // Finally Muse (most complex)
  connectToMuse();
  
  Serial.println();
  Serial.println("===============================================");
  Serial.println("Connection Summary:");
  Serial.printf("  Polar H10: %s\n", polarConnected ? "CONNECTED" : "Not connected");
  Serial.printf("  Mendi:     %s\n", mendiConnected ? "CONNECTED" : "Not connected");
  Serial.printf("  Muse:      %s\n", museConnected ? "CONNECTED" : "Not connected");
  Serial.println("===============================================");
  Serial.println();
  Serial.println("Listening for biometric data...");
  Serial.println();
}

void loop() {
  static unsigned long lastSendTime = 0;
  static unsigned long lastReconnectTime = 0;
  
  // Send data to server every 1 second
  if (millis() - lastSendTime > 1000) {
    if (bioData.lastUpdate > 0) {
      sendDataToServer();
    }
    lastSendTime = millis();
  }
  
  // Try to reconnect disconnected devices every 30 seconds
  if (millis() - lastReconnectTime > 30000) {
    if (!polarConnected) {
      connectToPolar();
    }
    if (!mendiConnected) {
      connectToMendi();
    }
    if (!museConnected) {
      connectToMuse();
    }
    lastReconnectTime = millis();
  }
  
  // Check connection status
  if (polarClient && !polarClient->isConnected()) {
    polarConnected = false;
  }
  if (mendiClient && !mendiClient->isConnected()) {
    mendiConnected = false;
  }
  if (museClient && !museClient->isConnected()) {
    museConnected = false;
  }
  
  delay(10);  // Small delay to prevent watchdog issues
}
