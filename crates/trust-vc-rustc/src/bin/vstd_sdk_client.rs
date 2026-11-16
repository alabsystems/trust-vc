// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Private data forwarder for an already live SDK coordinator.
#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // This entry performs no compiler or solver work and creates no owner.
    trust_vc_rustc::native_request_forwarding_main()
}
