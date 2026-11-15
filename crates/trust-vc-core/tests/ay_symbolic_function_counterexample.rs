// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original symbolic-default consumer must show its function witness.

use trust_vc_core::{verify_function_from_file, VerifyResult};

#[test]
fn original_forall_by_refutation_carries_the_published_function_interpretation() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/assert_forall_by.rs");
    let verdict = verify_function_from_file(source.to_str().unwrap(), "forallstmt_test_fail2")
        .expect("the original consumer fixture must extract and verify");
    let VerifyResult::Counterexample {
        model, bindings, ..
    } = verdict
    else {
        panic!("the original false assertion needs its actual counterexample: {verdict:?}");
    };
    let function = bindings
        .iter()
        .find(|binding| binding.raw_name == "f1" || binding.display_name == "f1")
        .expect("the counterexample must include the opaque source function f1");
    assert_eq!(function.ty, "fn(Int) -> Int");
    assert!(!function.value.is_empty());
    let rendered = model.expect("the same function witness must be visible in the counterexample");
    assert!(
        rendered.contains(&function.display_name) && rendered.contains(&function.value),
        "{rendered}"
    );
}
