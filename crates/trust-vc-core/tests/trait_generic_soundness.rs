// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for trait-side A2-generic: a parameterized
//! trait (`trait Give<A>`) implemented at a concrete instantiation
//! (`impl Give<u64> for S`) exposes its contract to concrete-receiver callers
//! via Box-bridged Poly slots (`Give__give(Box_S(s), Box_u64(a))`).
//!
//! The cardinal invariant: the instantiated contract is consumable ONLY because
//! every impl remains conformance-checked (see
//! `trait_generic_conformance_soundness.rs`); nothing here may verify a FALSE
//! instantiated fact, leak facts across instantiations or impls, or let a
//! non-instantiable shape (blanket impl, method-own generic, nested TypeParam)
//! resolve. The file-sink pin (`unrelated_true`) guards the fail-closed skip:
//! generic-signature impls must not sink unrelated functions in the file.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/trait_generic_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn assert_verified(func: &str) {
    let v = verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"));
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should verify (instantiated trait contract applies); got {v:?}"
    );
}

/// FALSE or non-instantiable facts must never verify. A hard extraction error
/// is acceptable here (fail-closed), but `Verified` is a cardinal false-verify.
fn assert_not_verified(func: &str) {
    if let Ok(VerifyResult::Verified) = verify_function_from_file(&repro_path(), func) {
        panic!("TRAIT-GENERIC FALSE-VERIFY: `{func}` must not verify")
    }
}

#[test]
fn instantiated_contract_true_fact_verifies() {
    assert_verified("give_pos");
}

#[test]
fn second_instantiation_true_fact_verifies() {
    assert_verified("give_bool_pos");
}

#[test]
fn two_param_binding_order_true_fact_verifies() {
    assert_verified("second_pos");
}

#[test]
fn instantiated_contract_false_fact_not_verified() {
    assert_not_verified("give_neg");
}

#[test]
fn second_instantiation_false_fact_not_verified() {
    assert_not_verified("give_bool_neg");
}

#[test]
fn two_param_binding_order_false_fact_not_verified() {
    assert_not_verified("second_neg");
}

#[test]
fn cross_impl_linking_axioms_do_not_leak() {
    assert_not_verified("cross_neg");
}

#[test]
fn blanket_param_bearing_impl_stays_fail_closed() {
    assert_not_verified("blanket_stays_closed");
}

#[test]
fn method_own_generic_stays_fail_closed() {
    assert_not_verified("own_generic_stays_closed");
}

#[test]
fn nested_type_param_position_stays_fail_closed() {
    assert_not_verified("nested_param_stays_closed");
}

#[test]
fn generic_signature_impls_do_not_sink_the_file() {
    assert_verified("unrelated_true");
}
