// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Capture inherited compiler resources before entering an embedded driver.

extern crate rustc_data_structures;

use std::process::ExitCode;

mod builtin_builder;
pub(crate) use builtin_builder::configure_child as configure_builtin_builder;

/// Enter the native role before file opens, workers, argument sidecars or user
/// callbacks. Ordinary compiler entry captures its actual GNU/SDK descriptors;
/// the private builtin-builder role completes in a separate coordinator.
/// `Err(code)` asks the entry point to terminate with that exact code, including
/// a successful coordinator completion. No role grants proof authority.
///
/// # Safety
/// This must be the first operation of the native process entry point. No
/// descriptor-opening operation or arbitrary callback may precede this call.
pub unsafe fn capture_inherited_resources() -> Result<(), ExitCode> {
    // This fixed role probe observes argv only and opens no descriptors.
    // A malformed private request terminates here, never in the compiler.
    if let Some(request) = builtin_builder::request() {
        // SAFETY: this is still the first native-entry operation. This role
        // owns its GNU import and runs no embedded compiler in this process.
        return Err(unsafe { builtin_builder::run(request) });
    }
    let forwarding = builtin_builder::snapshot();
    // SAFETY: the native entry caller guarantees the compiler's early-capture
    // precondition; no descriptor activity precedes this fixed importer here.
    match unsafe { rustc_data_structures::jobserver::capture_early() } {
        Ok(()) => builtin_builder::retain(forwarding),
        Err(error) => {
            eprintln!("error: inherited compiler resource custody unavailable: {error}");
            Err(ExitCode::from(75))
        }
    }
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
extern crate test;

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
pub(crate) fn test_main(tests: &[&test::TestDescAndFn]) {
    // SAFETY: the generated main constructs only static test references before
    // this call. Capture precedes libtest argument handling and worker threads.
    if let Err(exit) = unsafe { capture_inherited_resources() } {
        exit.exit_process();
    }
    // The normal pipeline invokes this same executable for its real erase
    // compiler. Enter that existing role before libtest parses its arguments.
    if std::env::args().nth(1).as_deref() == Some(crate::shim::ERASE_RUN_FLAG) {
        crate::shim::main().exit_process();
    }
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    // A custom test runner returns unit; retain libtest's actual process status.
    result.exit_process();
}
