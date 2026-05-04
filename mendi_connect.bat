@echo off
echo ============================================
echo   Mendi BLE GATT Discovery
echo   MAC: F8:1C:96:82:73:AD
echo ============================================
echo.
echo Make sure the Mendi headband is ON and blinking.
echo Press any key when ready...
pause >nul
echo.
echo Connecting...
python mendi_ble_client.py --discover-gatt --address F8:1C:96:82:73:AD
echo.
echo ============================================
echo   Done! If it worked, look for a JSON file
echo   in data\mendi\ble_discovery\
echo ============================================
echo.
pause
