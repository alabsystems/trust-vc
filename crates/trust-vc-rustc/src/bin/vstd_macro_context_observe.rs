//! Standalone native macro-state observation, with no import or proof claim.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // This standalone process starts no background host work. Each compiler
    // call joins its scoped workers before the observation changes VSTD_KIND.
    unsafe { trust_vc_rustc::reader::declaration_staging::macro_context_main() }
}
