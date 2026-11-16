// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dedicated live normal owned-client verification. No saved-receipt input.
#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // SAFETY: first native-entry operation, before argument handling, file opens,
    // compiler callbacks, or host worker threads can reuse inherited descriptors.
    if let Err(exit) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return exit;
    }
    // SAFETY: this dedicated process starts no engine/global workers before
    // the staging owner and never restores its one-way Imported context.
    unsafe { trust_vc_rustc::reader::declaration_staging::standalone_client_normal_verify_main() }
}
