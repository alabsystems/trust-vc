// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fresh native SDK owner and serial compiler request coordinator.
#![feature(rustc_private)]
extern crate rustc_driver;

fn main() -> std::process::ExitCode {
    // SAFETY: this is the first native operation, before argv, files or workers
    // can reuse any inherited compiler resource descriptor.
    if let Err(exit) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return exit;
    }
    // This private role is the same actual native coordinator image, not a
    // caller-supplied frontend pin. It only adds ordinary checking constraints
    // and can never enter ClientImports or construct a producer owner.
    match std::env::args().nth(1).as_deref() {
        Some(trust_vc_rustc::shim::ORDINARY_WORKER_FLAG) => {
            return trust_vc_rustc::shim::ordinary_worker_main()
        }
        Some(trust_vc_rustc::shim::ERASE_RUN_FLAG) => return trust_vc_rustc::shim::main(),
        _ => {}
    }
    // SAFETY: the dedicated entry owns all producer/compiler work in this
    // process and joins its data-only runner before ending the SDK owner.
    unsafe { trust_vc_rustc::reader::declaration_staging::standalone_sdk_coordinator_main() }
}
