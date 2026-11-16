//! Observe genuine foreign compiler declarations without importing proof facts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    // SAFETY: first native-entry operation, before argument handling, file opens,
    // compiler callbacks, or host worker threads can reuse inherited descriptors.
    if let Err(exit) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return exit;
    }
    trust_vc_rustc::metadata_inspect::main()
}
