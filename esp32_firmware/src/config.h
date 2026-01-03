/*
 * ESP32 BLE Bridge Configuration
 * ================================
 * Edit these values for your setup
 */

#ifndef CONFIG_H
#define CONFIG_H

// ============================================================
// WiFi Configuration
// ============================================================
#define WIFI_SSID "YOUR_WIFI_SSID"
#define WIFI_PASSWORD "YOUR_WIFI_PASSWORD"

// ============================================================
// Replit Server Configuration  
// ============================================================
// Get this URL from your Replit deployment
// Format: https://YOUR-REPL-NAME.YOUR-USERNAME.repl.co/api/upload
#define REPLIT_API_URL "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev/api/upload"

// ============================================================
// Timing Configuration
// ============================================================
#define UPLOAD_INTERVAL_MS 1000     // Upload every 1 second
#define BLE_SCAN_DURATION 30        // BLE scan duration in seconds
#define RECONNECT_INTERVAL_MS 10000 // Retry connection every 10 seconds
#define HTTP_TIMEOUT_MS 10000       // HTTP request timeout

// ============================================================
// Debug Options
// ============================================================
#define DEBUG_SERIAL true           // Enable serial debug output
#define DEBUG_VERBOSE false         // Extra verbose logging
#define FORCE_UPLOAD true           // Upload even without device connection

#endif
