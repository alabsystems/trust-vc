@echo off
rem Copyright 2026 Andrew Yates
rem SPDX-License-Identifier: Apache-2.0
rem Author: Andrew Yates <andrewyates.name@gmail.com>
rem
rem Windows twin of rustc_no_trust_verify.sh (see that file for the full
rem rationale): RUSTC_WRAPPER shim for trybuild scratch builds that appends
rem `-Ztrust-verify=off` to EVERY rustc invocation, host and target units
rem alike. cargo spawns RUSTC_WRAPPER via std::process::Command, which on
rem Windows can execute .bat/.cmd (through cmd.exe) but not POSIX shell
rem scripts, so the .sh shim cannot be used here.
rem
rem Invoked by cargo as: %RUSTC_WRAPPER% <rustc> <args...>
%* -Ztrust-verify=off
exit /b %errorlevel%
