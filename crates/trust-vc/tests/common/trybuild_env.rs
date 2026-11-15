// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Run trybuild scratch builds in targo's unverified lane.
//!
//! `rust-toolchain.toml` pins `channel = "trust"`, so `$CARGO` in a test
//! process is Targo, and Targo refuses a lane-less compile ("`targo check`
//! refuses to create an implicitly unverified artifact"). trybuild spawns
//! `$CARGO check`/`build` directly with no way to inject a flag, and Targo's
//! nested-lane broker does not cross the process boundary on this platform (it
//! says so: "recursive `$CARGO` invocations must select their own lane"). So
//! [`pin_no_trust_verify`] points `CARGO` at the committed
//! `cargo_unverified_lane.sh` shim (`.bat` twin on Windows), which names the
//! UNVERIFIED lane on compile subcommands and passes
//! `metadata`/`clean`/`generate-lockfile` through untouched. These scratch
//! builds are compile-diagnostic fixtures: they carry no proof claim, and the
//! shim says so rather than leaving the lane implicit.
//!
//! The lane is also what keeps the Trust verification pass off the scratch
//! project's dependency graph (`trust_vc` is a proc macro over the whole ay
//! solver stack, which verification can hold at 100% CPU for hours).
//! `targo --unverified` passes `-Ztrust-verify=off` to every unit it compiles,
//! host units (proc macros, build scripts) included, even under the
//! `--target <host-triple>` that trybuild passes, where cargo applies no extra
//! rustflags to host units. No `CARGO_ENCODED_RUSTFLAGS` or `RUSTC_WRAPPER`
//! off-switch is needed on top, so trybuild keeps its own rustflags and the
//! expected-stderr fixtures see exactly them.

/// Run the trybuild scratch builds that follow in targo's unverified lane,
/// which switches Trust verification off for every scratch unit.
///
/// Call this BEFORE constructing `trybuild::TestCases` in every trybuild
/// harness. Only safe in single-`#[test]` harnesses (process-env mutation):
/// the variables are deliberately LEFT set for the trybuild child cargo runs
/// that follow, so they route through the env choke point's
/// `set_persistent_env_var` (serialized write, no restore) rather than a
/// restore-on-drop guard.
///
/// Targo refuses a lane-less `check`/`build`, and trybuild spawns `$CARGO`
/// with no way to pass `--unverified`. The shim re-spells the compile
/// subcommands in the unverified lane and leaves `metadata`, `clean` and
/// `generate-lockfile` alone, since `--unverified` is valid only on a
/// compilation command. A `$CARGO` that already points at the shim is left as
/// it is. A `$CARGO` that is not Targo is refused rather than passed through,
/// so scratch builds never run on a stock cargo.
pub fn pin_no_trust_verify() {
    let cargo = std::env::var_os("CARGO")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from("targo"));
    let stem = cargo
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default();
    if stem == "cargo_unverified_lane" {
        return;
    }
    assert!(
        stem == "targo" || stem.starts_with("targo-"),
        "$CARGO `{}` is not the Trust toolchain's targo; run trybuild harnesses with \
         `targo --unverified test`",
        cargo.display()
    );

    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let shim_name = if cfg!(windows) {
        "cargo_unverified_lane.bat"
    } else {
        "cargo_unverified_lane.sh"
    };
    // Fail loudly if the shim is missing: proceeding would leave every
    // trybuild scratch compile to die on Targo's lane refusal, and the
    // harness would report that refusal as the fixture's diagnostic.
    let shim = [
        manifest_dir.join("tests/common").join(shim_name),
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
    #[cfg(windows)]
    let shim = std::path::PathBuf::from(
        shim.to_str()
            .expect("shim path is valid UTF-8")
            .trim_start_matches(r"\\?\"),
    );

    trust_vc_core::env::set_persistent_env_var("TRUST_VC_NESTED_CARGO", &cargo);
    trust_vc_core::env::set_persistent_env_var("CARGO", &shim);
}
