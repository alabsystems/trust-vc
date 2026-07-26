// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Keep `-Zno-trust-verify` pinned in trybuild scratch builds.
//!
//! trybuild (1.0.116, `src/cargo.rs`) launches its scratch `cargo` with
//! `--config=build.rustflags=[..]` and `--config=target.<triple>.rustflags=[..]`.
//! Those CLI config overrides outrank this repo's committed
//! `.cargo/config.toml` `[build] rustflags = ["-Zno-trust-verify"]`, so the
//! scratch build silently drops `-Zno-trust-verify` and the Trust toolchain
//! runs its verification pass over the scratch project's entire dependency
//! graph — which can hang `trustc` at 100% CPU for hours on large deps.
//!
//! Cargo's extra-rustflags precedence is (first match wins):
//! `CARGO_ENCODED_RUSTFLAGS` > `RUSTFLAGS` > `target.<triple>.rustflags` >
//! `build.rustflags`. trybuild `env_remove`s only `RUSTFLAGS` on the child
//! cargo, so `CARGO_ENCODED_RUSTFLAGS` set in this test process is inherited
//! by every scratch cargo invocation and outranks trybuild's `--config`
//! overrides. The flag list below replicates trybuild's own rustflags exactly
//! (`src/rustflags.rs` base set + the `--diagnostic-width=140` extra used on
//! the stderr-compared `build_test`/`build_all_tests` legs) so expected-stderr
//! fixtures stay byte-identical; the only addition is `-Zno-trust-verify`.
//!
//! Rustflags alone are NOT enough: trybuild passes `--target <host-triple>`
//! to its scratch cargo, and with `--target` set cargo applies NO extra
//! rustflags (env or config) to HOST units — build scripts, proc macros, and
//! their transitive deps. `trust_vc` is a proc-macro crate depending on
//! `trust-vc-core` (the entire ay solver stack), so the whole solver graph
//! compiles as HOST units and would still be verified (observed: `autocfg`
//! alone >9 min at 100% CPU). `RUSTC_WRAPPER` is the one stable cargo
//! mechanism that reaches EVERY rustc invocation on both sides, so
//! [`pin_no_trust_verify`] additionally points it at the committed
//! `rustc_no_trust_verify.sh` shim (`.bat` twin on Windows), which appends
//! `-Zno-trust-verify` to each compiler command line. `-Zno-trust-verify` emits no diagnostics, so
//! expected-stderr fixtures are unaffected.

/// Pin `-Zno-trust-verify` for trybuild scratch builds
/// (`CARGO_ENCODED_RUSTFLAGS` for target units + `RUSTC_WRAPPER` shim so host
/// units — proc macros, build scripts, and their deps — are covered too).
///
/// Call this BEFORE constructing `trybuild::TestCases` in every trybuild
/// harness. Only safe in single-`#[test]` harnesses (process-env mutation):
/// the variables are deliberately LEFT set for the trybuild child cargo runs
/// that follow, so they route through the env choke point's
/// `set_persistent_env_var` (serialized write, no restore) rather than a
/// restore-on-drop guard.
pub fn pin_no_trust_verify() {
    // trybuild's own flags, in trybuild's order (src/rustflags.rs, plus the
    // build_test/build_all_tests `--diagnostic-width=140` from src/cargo.rs).
    let mut flags: Vec<&str> = vec!["--cfg", "trybuild", "--verbose", "-A", "dead_code"];
    // Faithful replication of trybuild's cargo-llvm-cov coverage passthrough.
    let outer_rustflags = std::env::var_os("RUSTFLAGS").unwrap_or_default();
    if outer_rustflags
        .to_string_lossy()
        .contains("-C instrument-coverage")
    {
        flags.extend(["-C", "instrument-coverage"]);
    }
    flags.push("--diagnostic-width=140");
    // The one addition: keep the Trust toolchain's verification pass OFF for
    // scratch builds, exactly as the committed `[build] rustflags` does for
    // the main workspace build (trust-vc is the verifier, not a target).
    flags.push("-Zno-trust-verify");
    trust_vc_core::env::set_persistent_env_var("CARGO_ENCODED_RUSTFLAGS", flags.join("\u{1f}"));

    // Host units (proc macros, build scripts, and their deps) receive NO
    // extra rustflags when trybuild passes `--target`, so pin the flag for
    // them via a RUSTC_WRAPPER that appends it to every rustc invocation.
    // Fail loudly if the shim is missing: silently proceeding would re-enable
    // the Trust verification pass over the scratch host dependency graph.
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    // cargo spawns RUSTC_WRAPPER via std::process::Command, which on Windows
    // can execute .bat/.cmd (through cmd.exe) but not POSIX shell scripts, so
    // Windows uses the committed .bat twin of the .sh shim.
    let shim_name = if cfg!(windows) {
        "rustc_no_trust_verify.bat"
    } else {
        "rustc_no_trust_verify.sh"
    };
    let shim = [
        // Included from crates/trust-vc harnesses.
        manifest_dir.join("tests/common").join(shim_name),
        // Included via #[path] from sibling crates (e.g. trust-vc-core).
        manifest_dir
            .join("../trust-vc/tests/common")
            .join(shim_name),
    ]
    .into_iter()
    .find(|p| p.is_file())
    .unwrap_or_else(|| panic!("{shim_name} shim not found near {manifest_dir:?}"));
    let shim = shim
        .canonicalize()
        .unwrap_or_else(|e| panic!("canonicalize {shim_name} shim path: {e}"));
    // canonicalize() on Windows yields a `\\?\`-verbatim path; cmd.exe (the
    // interpreter std::process::Command uses to run .bat files) rejects that
    // prefix, so strip it back to a plain drive path.
    #[cfg(windows)]
    let shim = std::path::PathBuf::from(
        shim.to_str()
            .expect("shim path is valid UTF-8")
            .trim_start_matches(r"\\?\"),
    );
    trust_vc_core::env::set_persistent_env_var("RUSTC_WRAPPER", &shim);
}
