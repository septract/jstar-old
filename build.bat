@echo off
rem del .\bin\jstar.exe
rem del .\bin\run_abduct.exe
rem del .\bin\run_logic.exe
rem del .\bin\run_symb.exe
rem del .\bin\test_logic.exe
make build
copy /y .\bin\jstar .\bin\jstar.exe
copy /y .\bin\run_abduct .\bin\run_abduct.exe
copy /y .\bin\run_logic .\bin\run_logic.exe
copy /y .\bin\run_symb .\bin\run_symb.exe
copy /y .\bin\test_logic .\bin\test_logic.exe
