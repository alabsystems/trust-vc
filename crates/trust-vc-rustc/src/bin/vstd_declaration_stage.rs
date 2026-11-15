//! Genuine native compiler staging, with no verifier or import claim.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    trust_vc_rustc::reader::declaration_staging::main()
}
