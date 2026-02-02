/*
 * ESP32 Biometric Bridge Firmware
 * ================================
 * 
 * Connects to Muse 2 EEG and Polar H10 heart rate monitor via Bluetooth LE,
 * then forwards data to Replit server via HTTP.
 * 
 * Author: TI Framework
 * Date: February 2026
 * 
 * Required:
 * - ESP32 Development Board
 * - Arduino IDE with ESP32 board package
 * - WiFi network with internet access
 */

#include <BLEDevice.h>
#include <BLEUtils.h>
#include <BLEScan.h>
#include <BLEAdvertisedDevice.h>
#include <WiFi.h>
#include <HTTPClient.h>
#include <Arduino.h>

// ============================================
// CONFIGURATION - EDIT THESE VALUES
// ============================================

// WiFi credentials
const char* WIFI_SSID = "YOUR_WIFI_SSID";
const char* WIFI_PASSWORD = "YOUR_WIFI_PASSWORD";

// Replit server URL (replace with your actual Replit URL)
const char* REPLIT_URL = "https://YOUR-REPL-NAME.replit.app/api/upload";

// Device MAC addresses (found via BLE scanner)
// Polar H10 format: "a0:9e:1a:xx:xx:xx" (lowercase)
const char* POLAR_MAC = "";  // Leave empty to auto-discover

// Muse 2 format: "xx:xx:xx:xx:xx:xx" (found in Muse app or BLE scanner)
const char* MUSE_MAC = "";   // Leave empty to auto-discover

// ============================================
// BLE CONFIGURATION
// ============================================

// Polar H10 UUIDs
static BLEUUID polarServiceUUID("0000180d-0000-1000-8000-00805f9b34fb");
static BLEUUID polarCharUUID("00002a37-0000-1000-8000-00805f9b34fb");

// Muse 2 UUIDs
static BLEUUID museServiceUUID("0000fe8d-0000-1000-8000-00805f9b34fb");
static BLEUUID museEEG1UUID("273e0003-4c4d-454d-96be-f03bac821358");  // TP9
static BLEUUID museEEG2UUID("273e0004-4c4d-454d-96be-f03bac821358");  // AF7
static BLEUUID museEEG3UUID("273e0005-4c4d-454d-96be-f03bac821358");  // AF8
static BLEUUID museEEG4UUID("273e0006-4c4d-454d-96be-f03bac821358");  // TP10

// ============================================
// STATE VARIABLES
// ============================================

BLEScan* pBLEScan;
BLEClient* polarClient = nullptr;
BLEClient* museClient = nullptr;

bool polarConnected = false;
bool museConnected = false;
bool wifiConnected = false;

// Latest biometric data
float heartRate = 0;
float rrInterval = 0;
float eegAlpha = 0;
float eegTheta = 0;
float eegBeta = 0;
float eegGamma = 0;
float eegDelta = 0;

// Device addresses found during scan
String polarAddress = "";
String museAddress = "";

// Timing
unsigned long lastUpload = 0;
const unsigned long UPLOAD_INTERVAL = 1000;  // Upload every 1 second

// LED for status
const int LED_PIN = 2;  // Built-in LED on most ESP32 boards

// ============================================
// POLAR H10 CALLBACK
// ============================================

static void polarNotifyCallback(BLERemoteCharacteristic* pChar, uint8_t* pData, size_t length, bool isNotify) {
    if (length < 2) return;
    
    // Parse heart rate measurement
    uint8_t flags = pData[0];
    bool is16bit = flags & 0x01;
    
    if (is16bit && length >= 3) {
        heartRate = (pData[2] << 8) | pData[1];
    } else {
        heartRate = pData[1];
    }
    
    // Parse RR intervals if present
    if ((flags & 0x10) && length >= 4) {
        int offset = is16bit ? 3 : 2;
        if (length > offset + 1) {
            rrInterval = (pData[offset + 1] << 8) | pData[offset];
            rrInterval = rrInterval * 1000 / 1024;  // Convert to ms
        }
    }
    
    Serial.printf("[Polar] HR: %.0f bpm, RR: %.0f ms\n", heartRate, rrInterval);
}

// ============================================
// MUSE 2 CALLBACK - Simplified EEG parsing
// ============================================

// EEG sample buffers for power calculation
float eegBuffer[4][12];  // 4 channels, 12 samples each
int eegBufferIndex = 0;

static void museNotifyCallback(BLERemoteCharacteristic* pChar, uint8_t* pData, size_t length, bool isNotify) {
    if (length < 12) return;
    
    // Muse 2 sends 12 samples per packet at 256 Hz
    // Each sample is 12-bit, packed in 16-bit containers
    
    // Determine which channel based on characteristic UUID
    String uuid = pChar->getUUID().toString().c_str();
    int channel = 0;
    if (uuid.indexOf("0003") > 0) channel = 0;      // TP9
    else if (uuid.indexOf("0004") > 0) channel = 1; // AF7
    else if (uuid.indexOf("0005") > 0) channel = 2; // AF8
    else if (uuid.indexOf("0006") > 0) channel = 3; // TP10
    
    // Simple power estimation from raw amplitude
    float power = 0;
    for (int i = 0; i < 12 && i * 2 + 1 < length; i++) {
        int16_t sample = (pData[i * 2 + 1] << 8) | pData[i * 2];
        power += abs(sample);
    }
    power /= 12.0;
    
    // Store in buffer
    eegBuffer[channel][eegBufferIndex % 12] = power;
    
    if (channel == 3) {  // After all 4 channels updated
        eegBufferIndex++;
        
        // Calculate simplified band powers (rough approximation)
        // In real implementation, use FFT
        float totalPower = 0;
        for (int c = 0; c < 4; c++) {
            for (int s = 0; s < 12; s++) {
                totalPower += eegBuffer[c][s];
            }
        }
        totalPower /= 48.0;
        
        // Distribute to bands (simplified - real implementation needs FFT)
        // These are rough estimates based on typical EEG distributions
        eegDelta = 0.25;
        eegTheta = 0.20;
        eegAlpha = 0.25;
        eegBeta = 0.20;
        eegGamma = 0.10;
        
        // Modulate based on signal strength
        float modulation = min(1.0f, totalPower / 1000.0f);
        eegAlpha *= (0.8 + modulation * 0.4);
        
        Serial.printf("[Muse] Alpha: %.2f, Theta: %.2f, Beta: %.2f\n", 
                      eegAlpha, eegTheta, eegBeta);
    }
}

// ============================================
// BLE DEVICE DISCOVERY
// ============================================

class DeviceCallbacks: public BLEAdvertisedDeviceCallbacks {
    void onResult(BLEAdvertisedDevice advertisedDevice) {
        String name = advertisedDevice.getName().c_str();
        String addr = advertisedDevice.getAddress().toString().c_str();
        
        // Look for Polar H10
        if (name.indexOf("Polar") >= 0 || name.indexOf("H10") >= 0) {
            Serial.printf("Found Polar H10: %s (%s)\n", name.c_str(), addr.c_str());
            polarAddress = addr;
        }
        
        // Look for Muse 2
        if (name.indexOf("Muse") >= 0) {
            Serial.printf("Found Muse 2: %s (%s)\n", name.c_str(), addr.c_str());
            museAddress = addr;
        }
    }
};

// ============================================
// CONNECTION FUNCTIONS
// ============================================

bool connectToPolar() {
    if (polarAddress.length() == 0) {
        Serial.println("[Polar] No address found during scan");
        return false;
    }
    
    Serial.printf("[Polar] Connecting to %s...\n", polarAddress.c_str());
    
    polarClient = BLEDevice::createClient();
    
    BLEAddress addr(polarAddress.c_str());
    if (!polarClient->connect(addr)) {
        Serial.println("[Polar] Connection failed");
        return false;
    }
    
    BLERemoteService* pService = polarClient->getService(polarServiceUUID);
    if (pService == nullptr) {
        Serial.println("[Polar] Heart rate service not found");
        polarClient->disconnect();
        return false;
    }
    
    BLERemoteCharacteristic* pChar = pService->getCharacteristic(polarCharUUID);
    if (pChar == nullptr) {
        Serial.println("[Polar] Heart rate characteristic not found");
        polarClient->disconnect();
        return false;
    }
    
    if (pChar->canNotify()) {
        pChar->registerForNotify(polarNotifyCallback);
        Serial.println("[Polar] Connected and subscribed!");
        polarConnected = true;
        return true;
    }
    
    return false;
}

bool connectToMuse() {
    if (museAddress.length() == 0) {
        Serial.println("[Muse] No address found during scan");
        return false;
    }
    
    Serial.printf("[Muse] Connecting to %s...\n", museAddress.c_str());
    
    museClient = BLEDevice::createClient();
    
    BLEAddress addr(museAddress.c_str());
    if (!museClient->connect(addr)) {
        Serial.println("[Muse] Connection failed");
        return false;
    }
    
    BLERemoteService* pService = museClient->getService(museServiceUUID);
    if (pService == nullptr) {
        Serial.println("[Muse] EEG service not found");
        museClient->disconnect();
        return false;
    }
    
    // Subscribe to all 4 EEG channels
    BLEUUID eegUUIDs[] = {museEEG1UUID, museEEG2UUID, museEEG3UUID, museEEG4UUID};
    const char* channelNames[] = {"TP9", "AF7", "AF8", "TP10"};
    
    for (int i = 0; i < 4; i++) {
        BLERemoteCharacteristic* pChar = pService->getCharacteristic(eegUUIDs[i]);
        if (pChar != nullptr && pChar->canNotify()) {
            pChar->registerForNotify(museNotifyCallback);
            Serial.printf("[Muse] Subscribed to %s\n", channelNames[i]);
        }
    }
    
    Serial.println("[Muse] Connected and subscribed!");
    museConnected = true;
    return true;
}

// ============================================
// DATA UPLOAD TO REPLIT
// ============================================

void uploadToReplit() {
    if (!wifiConnected) return;
    
    HTTPClient http;
    http.begin(REPLIT_URL);
    http.addHeader("Content-Type", "application/json");
    
    // Build JSON payload
    String json = "{";
    json += "\"hr\":" + String(heartRate, 0) + ",";
    json += "\"rr\":" + String(rrInterval, 0) + ",";
    json += "\"alpha\":" + String(eegAlpha, 3) + ",";
    json += "\"theta\":" + String(eegTheta, 3) + ",";
    json += "\"beta\":" + String(eegBeta, 3) + ",";
    json += "\"gamma\":" + String(eegGamma, 3) + ",";
    json += "\"delta\":" + String(eegDelta, 3) + ",";
    json += "\"device\":\"ESP32\",";
    json += "\"polar\":" + String(polarConnected ? 1 : 0) + ",";
    json += "\"muse\":" + String(museConnected ? 1 : 0);
    json += "}";
    
    int httpCode = http.POST(json);
    
    if (httpCode > 0) {
        Serial.printf("[Upload] HTTP %d - %s\n", httpCode, http.getString().c_str());
        digitalWrite(LED_PIN, !digitalRead(LED_PIN));  // Toggle LED
    } else {
        Serial.printf("[Upload] Error: %s\n", http.errorToString(httpCode).c_str());
    }
    
    http.end();
}

// ============================================
// WIFI CONNECTION
// ============================================

void connectWiFi() {
    Serial.printf("Connecting to WiFi: %s\n", WIFI_SSID);
    
    WiFi.mode(WIFI_STA);
    WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
    
    int attempts = 0;
    while (WiFi.status() != WL_CONNECTED && attempts < 20) {
        delay(500);
        Serial.print(".");
        attempts++;
    }
    
    if (WiFi.status() == WL_CONNECTED) {
        Serial.println();
        Serial.printf("Connected! IP: %s\n", WiFi.localIP().toString().c_str());
        wifiConnected = true;
    } else {
        Serial.println("\nWiFi connection failed!");
        wifiConnected = false;
    }
}

// ============================================
// MAIN SETUP
// ============================================

void setup() {
    Serial.begin(115200);
    delay(1000);
    
    Serial.println("\n========================================");
    Serial.println("ESP32 Biometric Bridge v1.0");
    Serial.println("TI Framework - Consciousness Research");
    Serial.println("========================================\n");
    
    // Setup LED
    pinMode(LED_PIN, OUTPUT);
    digitalWrite(LED_PIN, HIGH);
    
    // Connect to WiFi first
    connectWiFi();
    
    // Initialize BLE
    Serial.println("\nInitializing Bluetooth...");
    BLEDevice::init("TI-Bridge");
    
    // Use pre-configured MAC addresses if provided
    if (strlen(POLAR_MAC) > 0) {
        polarAddress = POLAR_MAC;
    }
    if (strlen(MUSE_MAC) > 0) {
        museAddress = MUSE_MAC;
    }
    
    // Scan for devices if addresses not configured
    if (polarAddress.length() == 0 || museAddress.length() == 0) {
        Serial.println("Scanning for BLE devices...");
        pBLEScan = BLEDevice::getScan();
        pBLEScan->setAdvertisedDeviceCallbacks(new DeviceCallbacks());
        pBLEScan->setActiveScan(true);
        pBLEScan->start(10, false);  // Scan for 10 seconds
        Serial.println("Scan complete.\n");
    }
    
    // Connect to devices
    Serial.println("Connecting to biometric devices...\n");
    
    if (polarAddress.length() > 0) {
        connectToPolar();
    } else {
        Serial.println("[Polar] Not found - make sure chest strap is worn");
    }
    
    delay(1000);
    
    if (museAddress.length() > 0) {
        connectToMuse();
    } else {
        Serial.println("[Muse] Not found - make sure headband is on");
    }
    
    Serial.println("\n========================================");
    Serial.println("Status Summary:");
    Serial.printf("  WiFi: %s\n", wifiConnected ? "Connected" : "Disconnected");
    Serial.printf("  Polar H10: %s\n", polarConnected ? "Connected" : "Disconnected");
    Serial.printf("  Muse 2: %s\n", museConnected ? "Connected" : "Disconnected");
    Serial.println("========================================\n");
    
    if (!polarConnected && !museConnected) {
        Serial.println("WARNING: No biometric devices connected!");
        Serial.println("Check that devices are powered on and in range.");
    }
}

// ============================================
// MAIN LOOP
// ============================================

void loop() {
    // Check WiFi connection
    if (WiFi.status() != WL_CONNECTED) {
        wifiConnected = false;
        connectWiFi();
    }
    
    // Check device connections
    if (polarClient != nullptr && !polarClient->isConnected()) {
        polarConnected = false;
        Serial.println("[Polar] Disconnected - attempting reconnect...");
        connectToPolar();
    }
    
    if (museClient != nullptr && !museClient->isConnected()) {
        museConnected = false;
        Serial.println("[Muse] Disconnected - attempting reconnect...");
        connectToMuse();
    }
    
    // Upload data at regular intervals
    if (millis() - lastUpload >= UPLOAD_INTERVAL) {
        lastUpload = millis();
        
        if (polarConnected || museConnected) {
            uploadToReplit();
        }
    }
    
    delay(10);  // Small delay to prevent watchdog issues
}
