//! Observe expanded Keep declarations without importing or verifying them.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    trust_vc_rustc::declaration_observe::main()
}
