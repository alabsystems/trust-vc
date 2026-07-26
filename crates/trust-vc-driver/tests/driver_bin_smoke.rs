// Smoke + bin-level driver-vs-syn parity witness for the `trust-vc-driver` bin.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// This exercises the *compiled binary* (`src/bin/trust-vc-driver.rs`), not just
// the in-process `driver::run` that `driver_oracle_diff.rs` covers. It runs the
// bin as a subprocess on a minimal scalar-Hoare source, parses the machine
// `TRUST_VC_DRIVER_RESULT` records off stdout, and asserts:
//
//   * the bin emits one record per verification target with the expected verdict
//     (Verified / Refuted / UnsupportedContract);
//   * each in-fragment verdict AGREES with the trusted **syn** path verdict for
//     the equivalent contract (the bin-level parity witness — the driver is a new
//     VC producer, so its verdict must match syn, never prove more);
//   * the process exit status is fail-closed (non-zero when an in-fragment
//     function did not verify).
//
// This is a LOCAL-marker source (`fn requires`/`fn ensures` shims), so it needs
// no external crate: it validates the bin + THIR walker + ay backend end to end.
// The macro→marker surface bridge is validated separately by
// `trust-vc/src/driver_surface_bridge_tests.rs`; composing the two (a real
// `trust_vc::requires!` source) is the cargo `--frontend=driver` increment,
// which needs the target crate's dep graph built with the Trust toolchain.
//
// Feature-gated: empty on the default (stable) build. Run via
// `scripts/build-trust-vc-driver.sh test` (which builds the bin with the
// rustc_private `-L` flags and exports the runtime DYLD path the subprocess
// inherits).
#![cfg(feature = "rustc-driver")]
// Linking the feature-on `trust-vc-driver` lib pulls in `rustc_driver`, which
// this test binary must opt into (same as `driver_oracle_diff.rs`); the build
// script supplies `-Cprefer-dynamic` + `RUSTC_BOOTSTRAP=1` so it resolves.
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_driver::lower::{outcome_from, Outcome};

/// A minimal scalar-Hoare source with local marker shims (so it compiles under
/// the Trust toolchain with no external crate). Mirrors the first three cases of
/// `driver_oracle_diff.rs::SOURCE`.
const SOURCE: &str = r#"
fn requires(_b: bool) {}
fn ensures(_b: bool) {}

fn verify_case(x: u32) -> u32 {
    requires(x < 100);
    let result = x + 1;
    ensures(result == x + 1);
    result
}

fn refute_case(x: u32) -> u32 {
    requires(x < 100);
    let result = x + 1;
    ensures(result == x + 2);
    result
}

fn out_of_fragment_case(n: u32) -> u32 {
    requires(n < 100);
    let mut total = 0u32;
    while total < n { total = total + 1; }
    let result = total;
    ensures(result <= n);
    result
}
"#;

/// Resolves the compiled `trust-vc-driver` binary: cargo sets
/// `CARGO_BIN_EXE_trust-vc-driver` for integration tests when the bin target is
/// built; fall back to the conventional `target/<profile>/` path.
fn driver_bin() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_trust-vc-driver") {
        return PathBuf::from(path);
    }
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-vc-driver -> repo root -> target/debug/trust-vc-driver
    manifest
        .join("../../target/debug/trust-vc-driver")
        .canonicalize()
        .expect("trust-vc-driver bin should exist (build via scripts/build-trust-vc-driver.sh bin)")
}

fn rustc_sysroot() -> String {
    let out = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .expect("run rustc --print sysroot");
    String::from_utf8(out.stdout)
        .expect("utf8 sysroot")
        .trim()
        .to_string()
}

/// Runs the compiled bin on `SOURCE`; returns `(exit_code, verdicts, raw_stdout)`.
/// `verdicts` maps function name -> verdict string as emitted by the bin.
fn run_bin() -> (Option<i32>, HashMap<String, String>, String) {
    let dir = std::env::temp_dir().join(format!("trust_vc_bin_smoke_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let src = dir.join("bin_smoke_src.rs");
    std::fs::write(&src, SOURCE).expect("write source");

    // `driver::run` (inside the bin) injects `-Zno-steal-thir` + `--cfg
    // trust_vc_driver`; the subprocess inherits RUSTC_BOOTSTRAP + DYLD from the
    // build-script `test` environment. We pass the standard rustc args cargo
    // would for a lib crate.
    let output = Command::new(driver_bin())
        .arg(&src)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--crate-name=bin_smoke")
        .arg("--emit=metadata")
        .arg(format!("--out-dir={}", dir.display()))
        .arg("--sysroot")
        .arg(rustc_sysroot())
        .arg("-Awarnings")
        .output()
        .expect("run trust-vc-driver bin");

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let mut verdicts = HashMap::new();
    for line in stdout.lines() {
        let mut cols = line.split('\t');
        if cols.next() == Some("TRUST_VC_DRIVER_RESULT") {
            if let (Some(function), Some(verdict)) = (cols.next(), cols.next()) {
                verdicts.insert(function.to_string(), verdict.to_string());
            }
        }
    }
    std::fs::remove_dir_all(&dir).ok();
    (output.status.code(), verdicts, stdout)
}

/// The trusted syn-path verdict, as the coarse string vocabulary the bin emits.
/// Declares the same two scalar vars and runs under the same exec overflow
/// semantics the driver uses (`verify_exec` == `with_overflow_checks`).
fn syn_verdict(assumes: &[(&str, &str)], asserts: &[(&str, &str)]) -> &'static str {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("result", trust_vc_core::ir::TrustVcType::Uint { width: 32 });
    for (name, cond) in assumes {
        ctx.push_obligation(ProofObligation::assume(*name, *cond));
    }
    for (name, cond) in asserts {
        ctx.push_obligation(ProofObligation::assert(*name, *cond));
    }
    // Map through the driver's own coarse-outcome function so the reference uses
    // exactly the vocabulary the bin emits.
    match outcome_from(&ctx.verify()) {
        Outcome::Verified => "Verified",
        Outcome::Refuted => "Refuted",
        Outcome::Unknown => "Unknown",
        Outcome::Error(_) => "Error",
    }
}

#[test]
fn bin_emits_verdicts_agreeing_with_syn() {
    let (exit, verdicts, stdout) = run_bin();

    // The bin must have produced a record for each verification target.
    assert!(
        verdicts.contains_key("verify_case")
            && verdicts.contains_key("refute_case")
            && verdicts.contains_key("out_of_fragment_case"),
        "bin must emit one record per target; got {verdicts:?}\nstdout={stdout}"
    );

    // --- Trusted syn references (non-degenerate: the two directions differ) ---
    let syn_verify = syn_verdict(
        &[("req", "x < 100"), ("body", "result == x + 1")],
        &[("ens", "result == x + 1")],
    );
    let syn_refute = syn_verdict(
        &[("req", "x < 100"), ("body", "result == x + 1")],
        &[("ens", "result == x + 2")],
    );
    assert_eq!(syn_verify, "Verified", "syn ref: verify_case");
    assert_eq!(syn_refute, "Refuted", "syn ref: refute_case");

    // --- Parity witness: driver (bin) == syn on the in-fragment functions ---
    assert_eq!(
        verdicts["verify_case"], syn_verify,
        "verify_case: bin driver verdict must agree with syn\nstdout={stdout}"
    );
    assert_eq!(
        verdicts["refute_case"], syn_refute,
        "refute_case: bin driver verdict must agree with syn\nstdout={stdout}"
    );

    // Out-of-fragment (a loop) fails closed — never a fabricated verdict.
    assert_eq!(
        verdicts["out_of_fragment_case"], "UnsupportedContract",
        "out_of_fragment_case must fail closed\nstdout={stdout}"
    );

    // Fail-closed exit status: refute_case did not verify ⇒ non-zero.
    assert_eq!(
        exit,
        Some(1),
        "bin must exit non-zero when a target is not Verified"
    );
}
