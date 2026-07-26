//! `trust-vc-driver` — the nightly rustc-driver verification binary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # What this is
//!
//! A thin executable wrapper around [`trust_vc_driver::driver::run`]: it hands
//! the *whole* process argument vector (which is a real `rustc` invocation —
//! `--extern`/`--sysroot`/`-L` for the full dependency graph, exactly as cargo
//! assembled it) to the rustc-driver front end, which compiles the crate, walks
//! its fully type-checked THIR, lowers the scalar Hoare fragment, and verifies
//! each in-fragment function through the real encoder + ay.
//!
//! `driver::run` itself injects `-Zno-steal-thir` and `--cfg trust_vc_driver`
//! (the contract-macro surface bridge) if absent, so the caller need not.
//!
//! # Why a bin (and why nightly-only)
//!
//! The `driver` module does `extern crate rustc_{driver,hir,interface,middle}`
//! behind `feature = "rustc-driver"`, so this binary links the fork toolchain's
//! `rustc_private` libraries. It builds ONLY via
//! `scripts/build-trust-vc-driver.sh bin` (the `-L`/`-Cprefer-dynamic`/DYLD
//! recipe), never a bare `cargo build`. It is excluded from the default
//! (stable) workspace build by `required-features = ["rustc-driver"]`.
//!
//! # Output contract (machine-parseable; consumed by cargo-trust-vc)
//!
//! One line per verification target on **stdout** (rustc's own diagnostics go to
//! stderr, so stdout carries only these records):
//!
//! ```text
//! TRUST_VC_DRIVER_RESULT\t<function>\t<verdict>\t<detail>
//! ```
//!
//! where `<verdict>` is one of `Verified`, `Refuted`, `Unknown`, `Error`,
//! `UnsupportedType`, `UnsupportedContract`. The trailing summary line
//!
//! ```text
//! TRUST_VC_DRIVER_SUMMARY\t<targets>\t<verified>\t<refuted>\t<unknown>\t<error>\t<unsupported>
//! ```
//!
//! lets a consumer confirm it saw the whole record set (no truncation).
//!
//! # Exit status (soundness: fail-closed)
//!
//! Exit `0` iff **no in-fragment function failed to verify** — i.e. no
//! `Refuted`, `Unknown`, or `Error`. Out-of-fragment functions
//! (`UnsupportedType`/`UnsupportedContract`) are fail-closed *skips*, not
//! failures, so they never flip the exit status (they are simply "not
//! credited", mirroring how the syn path drops what it cannot encode). Any
//! definite non-verification of an in-fragment function ⇒ exit `1`.

// This binary does not touch `rustc_private` *items* itself, but *linking* the
// `trust-vc-driver` lib (which pulls in librustc_driver.dylib) requires the
// final artifact — this bin — to opt into `feature(rustc_private)`; without it
// the linker reports "cannot satisfy dependencies so `<std dep>` only shows up
// once". The bin only ever compiles under `required-features = ["rustc-driver"]`
// (always the fork toolchain + `RUSTC_BOOTSTRAP=1`), so the gate mirrors lib.rs.
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use std::io::Write;

use trust_vc_driver::driver::{self, DriverError, DriverResult};
use trust_vc_driver::lower::Outcome;

/// The stable stdout tag for one per-function verdict record.
const RESULT_TAG: &str = "TRUST_VC_DRIVER_RESULT";
/// The stable stdout tag for the trailing summary record.
const SUMMARY_TAG: &str = "TRUST_VC_DRIVER_SUMMARY";

fn main() {
    // Pass the argv through verbatim (argv[0] is the program name, which
    // `rustc_driver` ignores, exactly as `rustc` does). `driver::run` injects
    // `-Zno-steal-thir` and `--cfg trust_vc_driver` if the caller omitted them.
    let args: Vec<String> = std::env::args().collect();
    let results = driver::run(&args);

    let stdout = std::io::stdout();
    let mut out = stdout.lock();

    let mut verified = 0usize;
    let mut refuted = 0usize;
    let mut unknown = 0usize;
    let mut error = 0usize;
    let mut unsupported = 0usize;

    for DriverResult { function, result } in &results {
        let (verdict, detail) = classify(result);
        match verdict {
            "Verified" => verified += 1,
            "Refuted" => refuted += 1,
            "Unknown" => unknown += 1,
            "Error" => error += 1,
            _ => unsupported += 1,
        }
        // Tab-separated; sanitize embedded control chars in `detail` so one
        // record is always exactly one line.
        let _ = writeln!(
            out,
            "{RESULT_TAG}\t{function}\t{verdict}\t{}",
            sanitize(&detail)
        );
    }

    let _ = writeln!(
        out,
        "{SUMMARY_TAG}\t{}\t{verified}\t{refuted}\t{unknown}\t{error}\t{unsupported}",
        results.len()
    );
    let _ = out.flush();

    // Fail-closed: any in-fragment function that did not verify ⇒ non-zero.
    // Unsupported* are skips, never failures.
    let failed = refuted + unknown + error;
    std::process::exit(if failed == 0 { 0 } else { 1 });
}

/// Maps a driver result into `(verdict, detail)`. The verdict strings are the
/// stable wire vocabulary the consumer parses; `detail` is human context only.
fn classify(result: &Result<Outcome, DriverError>) -> (&'static str, String) {
    match result {
        Ok(Outcome::Verified) => ("Verified", String::new()),
        Ok(Outcome::Refuted) => ("Refuted", String::new()),
        Ok(Outcome::Unknown) => ("Unknown", String::new()),
        Ok(Outcome::Error(message)) => ("Error", message.clone()),
        Err(DriverError::UnsupportedType(reason)) => ("UnsupportedType", reason.clone()),
        Err(DriverError::UnsupportedContract(reason)) => ("UnsupportedContract", reason.clone()),
    }
}

/// Collapses any embedded newline/tab/carriage-return in a detail string to a
/// space so a record never spills across the one-line-per-record contract.
fn sanitize(detail: &str) -> String {
    detail
        .chars()
        .map(|c| {
            if c == '\n' || c == '\r' || c == '\t' {
                ' '
            } else {
                c
            }
        })
        .collect()
}
