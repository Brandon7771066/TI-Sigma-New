/*
 * ESP32 Simple Test - Verify board is working
 * Upload this first to confirm serial communication works
 */

void setup() {
  Serial.begin(115200);
  delay(2000);  // Wait for serial to initialize
  
  Serial.println();
  Serial.println("========================================");
  Serial.println("  ESP32 TEST - Board is working!");
  Serial.println("========================================");
  Serial.println();
}

void loop() {
  static int count = 0;
  count++;
  
  Serial.print("Test message #");
  Serial.print(count);
  Serial.println(" - If you see this, your ESP32 works!");
  
  delay(2000);  // Print every 2 seconds
}
