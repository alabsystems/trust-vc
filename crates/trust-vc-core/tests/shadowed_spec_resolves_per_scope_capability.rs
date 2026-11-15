// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (opaque_reveal `struct_fn_free_fn_2` port shape,
//! 2026-09-12): a top-level spec fn whose bare name is ALSO declared inside an
//! inline module used to be struck from the catalog for the WHOLE file (both
//! scopes failed closed). The bare spelling now resolves by the scope it is
//! written in: at the file root (the target or a top-level helper) it names the
//! top-level declaration; written inside the shadowing module (the target, or a
//! nested helper applied into the same context) it keeps failing closed, so one
//! solver symbol never carries two definitions.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_sspc_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
#[trust_vc::spec]
fn v() -> bool {
    true
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_identity(x: u64) -> u64 {
    x
}

mod inner {
    #[trust_vc::spec]
    pub fn v() -> bool {
        false
    }

    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn opaque_identity(x: u64) -> u64 {
        x + 1u64
    }

    // A nested helper whose body spells the bare `v` — inside `inner` that is
    // `inner::v`.
    #[trust_vc::spec]
    pub fn wraps_bare_v() -> bool {
        v()
    }

    #[trust_vc::proof]
    #[trust_vc::ensures(result)]
    pub fn bare_shadow() -> bool {
        v()
    }

    pub mod sub {
        #[trust_vc::proof]
        #[trust_vc::ensures(result)]
        pub fn bare_in_submodule() -> bool {
            v()
        }
    }
}

// CONTROL: at the file root the bare `v` is the top-level `v` (true).
#[trust_vc::proof]
#[trust_vc::ensures(result)]
fn root_bare_call_is_top_level() -> bool {
    v()
}

// LIAR: … and `!v()` is refuted there.
#[trust_vc::proof]
#[trust_vc::ensures(result)]
fn root_bare_call_liar() -> bool {
    !v()
}

// CONTROL (the corpus shape): an unqualified reveal of the top-level opaque
// fn, with a same-named nested fn in the file.
#[trust_vc::ensures(true)]
fn unqualified_reveal_with_nested_shadow() {
    let _ = opaque_identity(0u64);
    trust_vc::reveal!(opaque_identity);
    trust_vc::assert!(opaque_identity(4u64) == 4u64);
}

// LIAR: the revealed body is the TOP-LEVEL one (identity), not `x + 1`.
#[trust_vc::ensures(true)]
fn unqualified_reveal_with_nested_shadow_liar() {
    let _ = opaque_identity(0u64);
    trust_vc::reveal!(opaque_identity);
    trust_vc::assert!(opaque_identity(4u64) == 5u64);
}

// FAIL-CLOSED (mixed scopes): a root target applying a nested helper whose
// body spells the bare `v` — that `v` means `inner::v`, a different definition
// for the same solver symbol.
#[trust_vc::proof]
#[trust_vc::ensures(result)]
fn root_target_applies_nested_helper_with_bare_v() -> bool {
    inner::wraps_bare_v() || v()
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        Ok(VerifyResult::Verified) => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        Ok(VerifyResult::Counterexample { .. }) => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_scope_refusal(id: &str, func: &str) {
    let message = match verify(id, func, SRC) {
        Ok(VerifyResult::Error { message }) => message,
        Err(message) => message,
        other => panic!("{func}: expected the shadowed-spelling refusal, got {other:?}"),
    };
    assert!(
        message.contains("shadows the top-level spec function"),
        "{func}: expected the shadowed-spelling refusal, got: {message}"
    );
}

#[test]
fn control_root_bare_call_is_top_level() {
    expect_verified("c1", "root_bare_call_is_top_level");
}

#[test]
fn liar_root_bare_call_is_refuted() {
    expect_counterexample("l1", "root_bare_call_liar");
}

#[test]
fn control_unqualified_reveal_with_nested_shadow_verifies() {
    expect_verified("c2", "unqualified_reveal_with_nested_shadow");
}

#[test]
fn liar_unqualified_reveal_with_nested_shadow_is_refuted() {
    expect_counterexample("l2", "unqualified_reveal_with_nested_shadow_liar");
}

#[test]
fn bare_call_inside_the_shadowing_module_still_fails_closed() {
    expect_scope_refusal("f1", "bare_shadow");
}

#[test]
fn bare_call_inside_a_submodule_of_the_shadowing_module_still_fails_closed() {
    expect_scope_refusal("f2", "bare_in_submodule");
}

#[test]
fn nested_helper_spelling_the_bare_name_still_fails_closed() {
    expect_scope_refusal("f3", "root_target_applies_nested_helper_with_bare_v");
}
