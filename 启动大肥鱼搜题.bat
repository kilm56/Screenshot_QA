@echo off
setlocal
cd /d "%~dp0"

if not exist "%~dp0screenshot_qa.py" (
    echo screenshot_qa.py was not found next to this launcher.
    pause
    exit /b 1
)
if not exist "%~dp0ocr_win.ps1" (
    echo ocr_win.ps1 was not found. Keep all files in the same folder.
    pause
    exit /b 1
)

where pythonw >nul 2>nul
if errorlevel 1 (
    echo Python was not found. Install Python 3.10+ and add it to PATH.
    pause
    exit /b 1
)

start "" pythonw "%~dp0screenshot_qa.py"
exit /b 0
