/*
 * ESP32 POLAR H10 TEST
 * ====================
 * Simple test to connect ONLY to Polar H10
 * Start here before trying all three devices!
 * 
 * Created: November 27, 2025
 */

#include <NimBLEDevice.h>

// Your Polar H10 device name
const char* POLAR_H10_NAME = "Polar H10 C895672B";

// Heart Rate Service UUIDs (standard BLE)
static NimBLEUUID HR_SERVICE_UUID("180D");
static NimBLEUUID HR_CHARACTERISTIC_UUID("2A37");

NimBLEClient* pClient = nullptr;
bool connected = false;

// Heart rate data
uint8_t heartRate = 0;
uint16_t rrIntervals[10];
uint8_t rrCount = 0;

// Callback when heart rate data is received
void hrNotifyCallback(NimBLERemoteCharacteristic* pCharacteristic, 
                      uint8_t* pData, size_t length, bool isNotify) {
  if (length >= 2) {
    uint8_t flags = pData[0];
    
    // Parse heart rate (8-bit or 16-bit based on flags)
    if (flags & 0x01) {
      heartRate = pData[1] | (pData[2] << 8);
    } else {
      heartRate = pData[1];
    }
    
    // Parse RR intervals if present (for HRV)
    rrCount = 0;
    if (flags & 0x10) {
      int offset = (flags & 0x01) ? 3 : 2;
      while (offset + 1 < length && rrCount < 10) {
        rrIntervals[rrCount] = pData[offset] | (pData[offset + 1] << 8);
        rrCount++;
        offset += 2;
      }
    }
    
    // Print to Serial Monitor
    Serial.println("----------------------------------------");
    Serial.printf("HEART RATE: %d BPM\n", heartRate);
    
    if (rrCount > 0) {
      Serial.print("RR Intervals (ms): ");
      for (int i = 0; i < rrCount; i++) {
        Serial.printf("%d ", rrIntervals[i]);
      }
      Serial.println();
      
      // Calculate simple HRV (SDNN approximation)
      if (rrCount > 1) {
        float mean = 0;
        for (int i = 0; i < rrCount; i++) {
          mean += rrIntervals[i];
        }
        mean /= rrCount;
        
        float variance = 0;
        for (int i = 0; i < rrCount; i++) {
          variance += (rrIntervals[i] - mean) * (rrIntervals[i] - mean);
        }
        variance /= rrCount;
        float sdnn = sqrt(variance);
        
        Serial.printf("HRV (SDNN): %.1f ms\n", sdnn);
      }
    }
    Serial.println("----------------------------------------");
  }
}

void setup() {
  Serial.begin(115200);
  delay(1000);
  
  Serial.println();
  Serial.println("================================================");
  Serial.println("  ESP32 POLAR H10 TEST");
  Serial.println("  Mood Amplifier BLE Bridge");
  Serial.println("================================================");
  Serial.println();
  
  // Initialize BLE
  Serial.println("[1] Initializing BLE...");
  NimBLEDevice::init("ESP32_H10_Test");
  Serial.println("    BLE Initialized!");
  Serial.println();
  
  // Start scanning
  Serial.println("[2] Scanning for Polar H10...");
  Serial.printf("    Looking for: %s\n", POLAR_H10_NAME);
  Serial.println();
  
  NimBLEScan* pScan = NimBLEDevice::getScan();
  pScan->setActiveScan(true);
  NimBLEScanResults results = pScan->start(10);  // 10 second scan
  
  Serial.printf("    Found %d devices\n", results.getCount());
  
  // Look for Polar H10
  NimBLEAdvertisedDevice* targetDevice = nullptr;
  
  for (int i = 0; i < results.getCount(); i++) {
    NimBLEAdvertisedDevice device = results.getDevice(i);
    String name = device.getName().c_str();
    
    Serial.printf("    [%d] %s\n", i + 1, name.length() > 0 ? name.c_str() : "(no name)");
    
    if (name == POLAR_H10_NAME) {
      Serial.println();
      Serial.println("    *** POLAR H10 FOUND! ***");
      targetDevice = new NimBLEAdvertisedDevice(device);
    }
  }
  
  if (!targetDevice) {
    Serial.println();
    Serial.println("ERROR: Polar H10 not found!");
    Serial.println("Make sure:");
    Serial.println("  - H10 is on your chest (electrodes wet)");
    Serial.println("  - H10 is not connected to phone app");
    Serial.println("  - Device name matches exactly");
    Serial.println();
    Serial.println("Will retry in 30 seconds...");
    return;
  }
  
  Serial.println();
  Serial.println("[3] Connecting to Polar H10...");
  
  pClient = NimBLEDevice::createClient();
  
  if (pClient->connect(targetDevice)) {
    Serial.println("    Connected!");
    
    Serial.println();
    Serial.println("[4] Getting Heart Rate Service...");
    
    NimBLERemoteService* hrService = pClient->getService(HR_SERVICE_UUID);
    
    if (hrService) {
      Serial.println("    Heart Rate Service found!");
      
      Serial.println();
      Serial.println("[5] Subscribing to Heart Rate notifications...");
      
      NimBLERemoteCharacteristic* hrChar = hrService->getCharacteristic(HR_CHARACTERISTIC_UUID);
      
      if (hrChar && hrChar->canNotify()) {
        hrChar->subscribe(true, hrNotifyCallback);
        connected = true;
        
        Serial.println("    Subscribed successfully!");
        Serial.println();
        Serial.println("================================================");
        Serial.println("  SUCCESS! Waiting for heart rate data...");
        Serial.println("  (Make sure H10 has good skin contact)");
        Serial.println("================================================");
        Serial.println();
      } else {
        Serial.println("    ERROR: Could not subscribe to notifications");
      }
    } else {
      Serial.println("    ERROR: Heart Rate Service not found");
    }
  } else {
    Serial.println("    ERROR: Connection failed");
  }
  
  delete targetDevice;
}

void loop() {
  // Check if still connected
  if (pClient && !pClient->isConnected()) {
    if (connected) {
      Serial.println();
      Serial.println("!!! DISCONNECTED !!!");
      Serial.println("Restarting in 5 seconds...");
      connected = false;
      delay(5000);
      ESP.restart();
    }
  }
  
  delay(100);
}
