# TI Platform - Polar H10 Direct BLE Bridge
# Paste into Notepad, save as polar_bridge.py on Desktop, then run:
#   py -m pip install bleak requests
#   py C:\Users\brand\Desktop\polar_bridge.py
import asyncio, requests

SERVER = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"
HR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"

async def main():
    from bleak import BleakScanner, BleakClient
    print("Scanning for Polar H10... (make sure strap is wet and on your body)")
    devices = await BleakScanner.discover(timeout=10)
    polar = next((d for d in devices if d.name and "Polar" in d.name), None)
    if not polar:
        print("ERROR: Polar H10 not found. Check Bluetooth is on and strap is charged.")
        input("Press Enter to exit...")
        return
    print(f"Found: {polar.name} ({polar.address})")

    async with BleakClient(polar.address) as client:
        print("Connected! Streaming HR to TI Platform... (Ctrl+C to stop)")
        count = 0

        def hr_callback(sender, data):
            nonlocal count
            flags = data[0]
            hr = data[1] if flags & 0x01 == 0 else (data[1] | data[2] << 8)
            count += 1
            try:
                r = requests.post(
                    f"{SERVER}/api/upload",
                    json={"hr": hr, "polar": 1, "source": "ble_direct"},
                    timeout=3
                )
                ok = "OK" if r.status_code == 200 else f"ERR {r.status_code}"
                print(f"  HR #{count:04d} | {hr:3d} bpm | {ok}")
            except Exception as e:
                print(f"  HR #{count:04d} | {hr:3d} bpm | SEND FAIL: {e}")

        await client.start_notify(HR_UUID, hr_callback)
        while True:
            await asyncio.sleep(1)

try:
    asyncio.run(main())
except KeyboardInterrupt:
    print("\nStopped.")
