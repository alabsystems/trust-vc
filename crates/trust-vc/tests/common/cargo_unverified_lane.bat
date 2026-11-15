@echo off
rem Copyright 2026 Andrew Yates
rem SPDX-License-Identifier: Apache-2.0
rem Author: Andrew Yates <andrewyates.name@gmail.com>
rem
rem Windows twin of cargo_unverified_lane.sh (see that file for the full
rem rationale): `CARGO` shim that names the UNVERIFIED lane on the nested Targo
rem compile commands trybuild spawns, and passes every other subcommand
rem through untouched. std::process::Command runs .bat/.cmd through cmd.exe on
rem Windows but cannot run a POSIX shell script, so the .sh shim cannot serve
rem here.
rem
rem Invoked by trybuild as: %CARGO% [global options] <subcommand> <args...>
setlocal enabledelayedexpansion
if "%TRUST_VC_NESTED_CARGO%"=="" (
    echo cargo_unverified_lane.bat: TRUST_VC_NESTED_CARGO is unset 1>&2
    exit /b 127
)

rem Find the subcommand: skip the leading global options (and the value of the
rem ones that take a separate value), exactly as the .sh twin does.
set "SUBCOMMAND="
set "SKIPVALUE=0"
for %%a in (%*) do (
    if "!SKIPVALUE!"=="1" (
        set "SKIPVALUE=0"
    ) else (
        set "ARG=%%~a"
        if "!ARG!"=="--color" (set "SKIPVALUE=1") else ^
        if "!ARG!"=="--config" (set "SKIPVALUE=1") else ^
        if "!ARG!"=="--explain" (set "SKIPVALUE=1") else ^
        if "!ARG!"=="-C" (set "SKIPVALUE=1") else ^
        if "!ARG!"=="-Z" (set "SKIPVALUE=1") else ^
        if "!ARG:~0,1!"=="-" (rem another option: keep looking) else ^
        if "!SUBCOMMAND!"=="" (set "SUBCOMMAND=!ARG!")
    )
)

for %%s in (build b check c test t bench run r rustc doc d) do (
    if "!SUBCOMMAND!"=="%%s" (
        "%TRUST_VC_NESTED_CARGO%" --unverified %*
        exit /b !errorlevel!
    )
)
"%TRUST_VC_NESTED_CARGO%" %*
exit /b !errorlevel!
