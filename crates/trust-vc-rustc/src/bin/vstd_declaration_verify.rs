//! Dedicated owned declaration verification; no saved-observation input.
//!
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // Producer compilers return before the one-way Imported transition. No
    // process macro environment is restored after AY workers can be created.
    unsafe { trust_vc_rustc::reader::declaration_staging::standalone_client_verify_main() }
}
