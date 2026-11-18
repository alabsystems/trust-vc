// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Relay bytes to a live process. A reply is data, never import authority.

use super::*;
use std::os::fd::RawFd;
use std::process::ExitCode;

fn run() -> io::Result<u8> {
    // Resolve and validate the inherited kernel object before any operation
    // that could open a file and reuse an absent numeric locator.
    let raw: RawFd = std::env::var(INHERITED_CONTROL_ENV)
        .map_err(|_| invalid("missing native request channel"))?
        .parse()
        .map_err(|_| invalid("invalid native request channel locator"))?;
    if raw < 3 || unsafe { libc::fcntl(raw, libc::F_GETFD) } < 0 {
        return Err(invalid(
            "native request channel is not an open inherited descriptor",
        ));
    }
    // SAFETY: the single-threaded entry just established that this descriptor
    // is open. It borrows the handle only while validating and duplicating it.
    let client = Client::from_inherited(unsafe { BorrowedFd::borrow_raw(raw) })?;
    let outputs = OutputContext::from_pairs(
        ["TRUST_VC_VERDICT_DIR", "TRUST_VC_DUMP_VCIR"]
            .into_iter()
            .filter_map(|name| std::env::var_os(name).map(|value| (name.into(), value))),
    )?;
    let argv = std::env::args_os().collect::<Vec<_>>();
    let macro_package_name = std::env::var_os("CARGO_PKG_NAME");
    let cargo = CargoContext::capture(&argv, macro_package_name.as_deref());
    let request = Request {
        argv,
        cwd: std::env::current_dir()?.canonicalize()?,
        outputs,
        verusdoc: std::env::var_os("VERUSDOC"),
        cargo,
        macro_package_name,
    };
    let response = client.submit(&request, Duration::from_secs(30))?;
    response.copy_to(&mut io::stdout().lock(), &mut io::stderr().lock())
}

/// Data-only process entry. This deliberately never enters the public
/// verifier, captures compiler resources, or decodes a native SDK reference.
pub fn main() -> ExitCode {
    match run() {
        Ok(exit) => ExitCode::from(exit),
        Err(error) => {
            eprintln!("error: native request forwarding failed: {error}");
            ExitCode::from(75)
        }
    }
}

#[cfg(test)]
mod tests;
