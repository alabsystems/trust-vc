//! Standalone owned client reader; no solver or verification claim.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // This dedicated process starts no concurrent host work or solver. Its
    // producer compilers return before the one-way Imported transition.
    unsafe { trust_vc_rustc::reader::declaration_staging::standalone_client_main() }
}
