// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Build script for trust-vc-driver.
//!
//! With the `rustc-driver` feature on, the `trust-vc-driver` bin, the lib's
//! unit-test harness and every integration test link the compiler's
//! `librustc_driver-<hash>` dylib from `<sysroot>/lib`. The Trust toolchain
//! resolves `rustc_private` from its own sysroot (no `-L` overlay), but nothing
//! tells the loader where that dylib lives: without help the binaries die with
//! `dyld: Library not loaded: @rpath/librustc_driver-….dylib … no LC_RPATH's
//! found`. This script bakes an rpath to the compiler's lib directory into
//! every linked target (the same approach as `trust-vc-rustc/build.rs`), so no
//! `DYLD_LIBRARY_PATH` and no wrapper script are needed.
//!
//! It also exports that sysroot as `VC_DRIVER_COMPILER_SYSROOT`, so the
//! driver tests hand the driver the sysroot of the very compiler it links,
//! instead of asking whatever `rustc` happens to be on PATH.
//!
//! The sysroot is canonicalized, so a toolchain reached through a symlink bakes
//! in the concrete store directory; a later toolchain update cannot swap a
//! different dylib under the same path.

use std::path::PathBuf;
use std::process::Command;

fn main() -> Result<(), String> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");

    if std::env::var_os("CARGO_FEATURE_RUSTC_DRIVER").is_none() {
        return Ok(());
    }

    // Cargo always sets RUSTC for build scripts; the fallback is the Trust
    // compiler, never a bare `rustc` from PATH.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "trustc".to_string());
    let sysroot = PathBuf::from(run(&rustc, &["--print", "sysroot"])?.trim());
    let sysroot = sysroot.canonicalize().unwrap_or(sysroot);
    let lib = sysroot.join("lib");
    if !lib.is_dir() {
        return Err(format!(
            "compiler lib directory {} does not exist",
            lib.display()
        ));
    }
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() == Ok("unix") {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib.display());
    }
    println!(
        "cargo:rustc-env=VC_DRIVER_COMPILER_SYSROOT={}",
        sysroot.display()
    );
    Ok(())
}

fn run(program: &str, args: &[&str]) -> Result<String, String> {
    let out = Command::new(program)
        .args(args)
        .output()
        .map_err(|e| format!("could not run {program} {args:?}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{program} {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    String::from_utf8(out.stdout)
        .map_err(|e| format!("{program} {args:?} output is not UTF-8: {e}"))
}
