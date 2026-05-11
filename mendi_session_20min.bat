@echo off
REM ===========================================================
REM   Mendi 20-minute structured session — Acer laptop launcher
REM   MAC: F8:1C:96:82:73:AD  (override below if yours differs)
REM ===========================================================

setlocal
set MENDI_MAC=F8:1C:96:82:73:AD
set LABEL=session

REM ── 1. Quick environment check ──────────────────────────────
echo.
echo [1/3] Checking Python + bleak...
py -c "import bleak; print('  bleak OK, version', bleak.__version__)" 2>nul
if errorlevel 1 (
    echo   bleak NOT installed. Installing now...
    py -m pip install bleak requests
    if errorlevel 1 (
        echo   ERROR: pip install failed. Open an Administrator command prompt and run:
        echo       py -m pip install bleak requests
        pause
        exit /b 1
    )
)

REM ── 2. Pre-flight checklist ─────────────────────────────────
echo.
echo [2/3] Pre-flight checklist:
echo.
echo   [ ] Mendi headband powered ON and BLINKING
echo   [ ] Mendi REMOVED from Windows Bluetooth paired devices
echo       (Settings ^> Bluetooth ^& devices ^> Mendi ^> Remove)
echo   [ ] Mendi phone app CLOSED
echo   [ ] Headband seated firmly on forehead, optode flush against skin
echo   [ ] You can sit undisturbed for 20 minutes
echo   [ ] You have a clock or watch visible (script will print timestamps too)
echo.
echo Schedule:
echo    0:00 - 2:00   Baseline (sit still, eyes soft-focus)
echo    2:00 - 3:00   STIM 1: Mental arithmetic (count back from 1000 by 7s)
echo    3:00 - 5:00   Recovery
echo    5:00 - 6:00   STIM 2: Breath-hold (exhale, hold 30-45s)
echo    6:00 -10:00   Recovery / meditation
echo   10:00 -11:00   STIM 3: Mental arithmetic replication (1000 - 13s)
echo   11:00 -13:00   Recovery
echo   13:00 -14:00   STIM 4: Breath-hold replication
echo   14:00 -20:00   Closing meditation
echo.
pause

REM ── 3. Run the session ──────────────────────────────────────
echo.
echo [3/3] Starting session...
echo.
py mendi_session_20min.py --address %MENDI_MAC% --label %LABEL% --duration 1200
if errorlevel 1 (
    echo.
    echo Session ended with errors. Check messages above.
    pause
    exit /b 1
)

echo.
echo Session complete. Output files in data\mendi\sessions\
echo.
pause
endlocal
