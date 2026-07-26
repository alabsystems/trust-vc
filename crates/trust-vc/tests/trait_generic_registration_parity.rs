// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! File-path verdict stability for trait-side A2-generic (Probe 5, integration
//! half): the file-path collector's verdicts on a parameterized-trait fixture
//! are pinned positive AND negative, and re-verification is stable (no order
//! or accumulated-state sensitivity).
//!
//! The catalog surface cannot be exercised from an integration test: the
//! verification entry resets the thread-local trait registry
//! (`context_management` clears `REGISTERED_TRAITS` per run), and production
//! populates it INSIDE the flow (proc-macro `register_traits_from_manifest_scope`
//! / marker extraction). Dual-surface parity is therefore pinned at the layer
//! where both surfaces are observable: the shared parsers (unit tests in
//! `trait_expand`) and the registry merge/dedup (in-crate
//! `verify_macro_tests::thread_local_state` — registering the same
//! parameterized source twice must not duplicate decls, with
//! `generics`/`trait_type_args` participating in equality).

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const FIXTURE: &str = r#"
struct PS1 { x: u64 }

#[trust_vc::trait_spec]
trait ParityGive<A> {
    #[trust_vc::ensures(result == a)]
    fn give(&self, a: A) -> A;
}

#[trust_vc::trait_impl]
impl ParityGive<u64> for PS1 {
    fn give(&self, a: u64) -> u64 { a }
}

#[trust_vc::ensures(true)]
fn parity_pos(s: PS1) {
    trust_vc::assert!(s.give(7u64) == 7u64);
}

#[trust_vc::ensures(true)]
fn parity_neg(s: PS1) {
    trust_vc::assert!(s.give(7u64) == 8u64);
}
"#;

fn write_fixture(label: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_generic_parity_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, FIXTURE).expect("write parity fixture");
    path
}

fn verdict(label: &str, func: &str) -> VerifyResult {
    let path = write_fixture(label);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, func).unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn instantiated_positive_verifies_on_file_path() {
    let result = verdict("pos", "parity_pos");
    assert!(
        matches!(result, VerifyResult::Verified),
        "parity_pos must verify on the file path, got {result:?}"
    );
}

#[test]
fn instantiated_negative_never_verifies_on_file_path() {
    let result = verdict("neg", "parity_neg");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "parity_neg must not verify on the file path, got {result:?}"
    );
}

/// Back-to-back runs over the same source must agree — pins that registration
/// is idempotent under the per-run registry reset and that no cross-run state
/// (VC cache aside) can flip an instantiated-trait verdict.
#[test]
fn reverification_is_stable() {
    let first = verdict("stable_a", "parity_pos");
    let second = verdict("stable_b", "parity_pos");
    assert_eq!(
        matches!(first, VerifyResult::Verified),
        matches!(second, VerifyResult::Verified),
        "re-verification diverged: {first:?} vs {second:?}"
    );
    let neg_again = verdict("stable_c", "parity_neg");
    assert!(
        !matches!(neg_again, VerifyResult::Verified),
        "parity_neg must stay non-verified on re-run, got {neg_again:?}"
    );
}
