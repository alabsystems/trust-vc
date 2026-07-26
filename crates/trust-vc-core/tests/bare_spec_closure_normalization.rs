// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end guards for the Verus-faithful *bare* spec-closure surface: a
//! closure passed directly to a ghost-collection combinator (`Set::new`,
//! `Set::filter`, `Set::map`, ...) is normalized to the existing
//! `SpecFn::new(...)` encoding in spec positions only.
//!
//! These mirror `set_new_comprehension.rs` but exercise the bare form
//! (`Set::<int>::new(|i: int| ...)`, `s.filter(|i| ...)`) and confirm:
//!   * (positive) a bare closure verifies identically to the wrapped form;
//!   * (no-double-wrap) an already-`SpecFn::new(...)` argument still verifies;
//!   * (soundness) a property the predicate refutes fails closed — never a
//!     false `Verified`.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/bare_spec_closure_normalization");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// POSITIVE: `Set::<int>::new(|i: int| i >= 0).contains(2)` (bare) verifies —
/// `2` satisfies the predicate.
#[test]
fn bare_set_new_member_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn bare_set_new_member() {
    trust_vc::assert!(Set::<int>::new(|i: int| i >= (0 as int)).contains(2 as int));
}
"#;
    let r = verify(code, "bare_set_new_member");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "bare Set::new predicate-true member should verify, got {r:?}"
    );
}

/// NO-DOUBLE-WRAP: the explicit `SpecFn::new(...)` form still verifies after the
/// normalization is in place (it is not wrapped a second time).
#[test]
fn spec_fn_new_member_still_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn spec_fn_new_member() {
    trust_vc::assert!(Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int))).contains(2 as int));
}
"#;
    let r = verify(code, "spec_fn_new_member");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "explicit SpecFn::new member should still verify, got {r:?}"
    );
}

/// SOUNDNESS: asserting membership of an element the bare predicate EXCLUDES
/// (`0` against `i >= 1`) must NOT verify.
#[test]
fn bare_set_new_member_outside_predicate_fails_closed() {
    let code = r#"
#[trust_vc::ensures(true)]
fn bare_set_new_unsound() {
    trust_vc::assert!(Set::<int>::new(|i: int| i >= (1 as int)).contains(0 as int));
}
"#;
    let r = verify(code, "bare_set_new_unsound");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "bare comprehension predicate-false member must NOT verify, got {r:?}"
    );
}

/// POSITIVE: a bare *untyped* method-combinator closure (`s.filter(|i| i > 0)`)
/// infers its parameter type from the `Set<int>` receiver and verifies.
/// `3 ∈ s` (precondition) and `3 > 0`, so `3 ∈ s.filter(|i| i > 0)`.
#[test]
fn bare_untyped_set_filter_member_verifies() {
    let code = r#"
#[trust_vc::requires(s.contains(3 as int))]
#[trust_vc::ensures(true)]
fn bare_set_filter_member(s: Set<int>) {
    trust_vc::assert!(s.filter(|i| i > (0 as int)).contains(3 as int));
}
"#;
    let r = verify(code, "bare_set_filter_member");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "bare untyped filter member should verify, got {r:?}"
    );
}

/// SOUNDNESS: the same bare filter with a predicate that REFUTES membership
/// (`3 > 5` is false) must NOT verify, even though `3 ∈ s`.
#[test]
fn bare_untyped_set_filter_wrong_predicate_fails_closed() {
    let code = r#"
#[trust_vc::requires(s.contains(3 as int))]
#[trust_vc::ensures(true)]
fn bare_set_filter_unsound(s: Set<int>) {
    trust_vc::assert!(s.filter(|i| i > (5 as int)).contains(3 as int));
}
"#;
    let r = verify(code, "bare_set_filter_unsound");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "filter member excluded by the predicate must NOT verify, got {r:?}"
    );
}
