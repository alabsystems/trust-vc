//! Build script for trust-vc-rustc.
//!
//! With the `rustc` feature on, the `rust_verify` binary links the compiler's
//! `librustc_driver-<hash>.dylib`, which lives in `<sysroot>/lib`. The binary is
//! started by upstream's test harness, not by a shell we control, so it cannot
//! rely on `DYLD_LIBRARY_PATH` (macOS also strips `DYLD_*` whenever a command
//! passes through `/usr/bin/env` or `/bin/sh`). This script therefore bakes an
//! rpath to the compiler's lib directory into the binary.
//!
//! The sysroot path is canonicalized, so when the toolchain is reached through
//! a symlink the rpath names the concrete build directory. A later toolchain
//! promotion then cannot swap a different dylib under the same file name.
//!
//! It also records the compiler's commit hash as `VC_SHIM_COMPILER_COMMIT`, which
//! the binary writes into every verdict record.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");

    // Cargo always sets RUSTC for build scripts; the fallback is the Trust
    // compiler, never a bare `rustc` from PATH.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "trustc".to_string());

    let version = run(&rustc, &["-vV"]);
    let commit = version
        .lines()
        .find_map(|l| l.strip_prefix("commit-hash: "))
        .unwrap_or("unknown")
        .trim()
        .to_string();
    println!("cargo:rustc-env=VC_SHIM_COMPILER_COMMIT={commit}");

    if std::env::var_os("CARGO_FEATURE_RUSTC").is_none() {
        return;
    }

    let sysroot = PathBuf::from(run(&rustc, &["--print", "sysroot"]).trim());
    let sysroot = sysroot.canonicalize().unwrap_or(sysroot);
    let lib = sysroot.join("lib");
    if !lib.is_dir() {
        panic!("compiler lib directory {} does not exist", lib.display());
    }
    println!("cargo:rustc-link-arg-bins=-Wl,-rpath,{}", lib.display());
    println!(
        "cargo:rustc-env=VC_SHIM_COMPILER_SYSROOT={}",
        sysroot.display()
    );
}

fn run(program: &str, args: &[&str]) -> String {
    let out = Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("could not run {program} {args:?}: {e}"));
    if !out.status.success() {
        panic!(
            "{program} {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    String::from_utf8(out.stdout).expect("compiler output is UTF-8")
}
