@echo off
setlocal
cd /d "%~dp0"
echo Starting with a console window so errors stay visible...
echo.
python "%~dp0screenshot_qa.py"
echo.
echo The program has exited. Press any key to close.
pause >nul
