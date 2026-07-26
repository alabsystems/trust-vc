//! Body-extraction scope-resolution regressions for let-bound ghost-collection
//! comprehensions surviving into proof contexts (GAP1 + GAP2).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These exercise the scoped string-substitution path in
//! `vc_extraction::body_extract`:
//!
//! * GAP1 — `expr_to_scoped_string_inner` now scope-substitutes a closure body
//!   (shadowing the closure params) so a let-bound local referenced inside a
//!   `forall(|..| ..)` closure resolves instead of being emitted unresolved.
//! * GAP2 — `visit_expr_method_call` no longer unconditionally invalidates a
//!   path-ident receiver: a pure ghost-collection combinator (`filter`/`map`)
//!   leaves the receiver unchanged, so a reused `let s = Set::new(..)` survives.
//!   The SOUNDNESS adversarial case proves a genuinely-mutated `Vec` receiver is
//!   still invalidated (no stale pre-mutation state carried forward).

use crate::VerifyResult;

/// Parses `src` as a Rust file, extracts `func`, and verifies it through the
/// real body-extraction + VC pipeline. An extraction error (e.g. the
/// "unresolved variable" failure the GAPs produced) is surfaced as
/// `VerifyResult::Error` so tests can distinguish it from a counterexample.
fn verify_src(src: &str, func: &str) -> VerifyResult {
    let file = syn::parse_file(src).expect("test source should parse as Rust");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item_fn) if item_fn.sig.ident == func => Some(item_fn),
            _ => None,
        })
        .unwrap_or_else(|| panic!("source should define fn `{func}`"));
    crate::extract_verification_conditions_with_file_context(&file, item)
        .map(|vc| vc.verify())
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        })
}

fn assert_verified(src: &str, func: &str) {
    match verify_src(src, func) {
        VerifyResult::Verified => {}
        other => panic!("`{func}` should verify, got {other:?}"),
    }
}

fn assert_not_verified(src: &str, func: &str) {
    // Counterexample, Unknown, or Error are all acceptable fail-closed
    // outcomes for a property that should not be provable.
    if verify_src(src, func) == VerifyResult::Verified {
        panic!("`{func}` must NOT verify but did");
    }
}

// ===========================================================================
// GAP1: a closure body that references an outer let-bound local must
// scope-substitute that local (shadowing the closure params) instead of
// emitting it verbatim/unresolved. The `Set::new(..)` comprehension predicate
// below CAPTURES the let-local `bound`; without the closure arm the rendered
// condition contains an unresolved `bound` and fails to lower.
// ===========================================================================

const GAP1_CAPTURE_TRUE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_closure_body_resolves_captured_let_local() {
    let bound = 3 as int;
    let ge_bound = Set::new(SpecFn::new(|i: int| i >= bound));
    // 5 >= 3, so 5 is a member. Resolving requires substituting `bound -> 3`
    // inside the closure body while leaving the bound param `i` alone.
    trust_vc::assert!(ge_bound.contains(5 as int));
}
"#;

const GAP1_CAPTURE_FALSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_closure_body_captured_let_local_false() {
    let bound = 3 as int;
    let ge_bound = Set::new(SpecFn::new(|i: int| i >= bound));
    // 2 >= 3 is false, so 2 is NOT a member: must fail closed.
    trust_vc::assert!(ge_bound.contains(2 as int));
}
"#;

// Upstream `sets.rs::test1` shape: the `forall |i| ..` body references the
// let-bound comprehension `nonneg`. This exercises GAP1 (body resolution) and
// GAP2 (the `nonneg` binding surviving the `.filter`/`.map` reuse) together.
const GAP1_FORALL_TRUE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_forall_body_resolves_let_bound_comprehension() {
    let nonneg = Set::new(SpecFn::new(|i: int| i >= (0 as int)));
    trust_vc::assert!(forall |i: int| nonneg.contains(i) == (i >= (0 as int)));
}
"#;

const GAP1_FORALL_FALSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_forall_body_wrong_property_is_rejected() {
    let nonneg = Set::new(SpecFn::new(|i: int| i >= (0 as int)));
    trust_vc::assert!(forall |i: int| nonneg.contains(i) == (i > (0 as int)));
}
"#;

#[test]
fn gap1_closure_body_resolves_captured_let_local_verifies() {
    assert_verified(
        GAP1_CAPTURE_TRUE,
        "gap1_closure_body_resolves_captured_let_local",
    );
}

#[test]
fn gap1_closure_body_captured_let_local_false_is_rejected() {
    // Guard: `2 >= 3` is false, so this must fail closed rather than ride an
    // unresolved/vacuous encoding to a false `Verified`.
    assert_not_verified(
        GAP1_CAPTURE_FALSE,
        "gap1_closure_body_captured_let_local_false",
    );
}

#[test]
fn gap1_forall_body_resolves_let_bound_comprehension_verifies() {
    assert_verified(
        GAP1_FORALL_TRUE,
        "gap1_forall_body_resolves_let_bound_comprehension",
    );
}

#[test]
fn gap1_forall_body_wrong_property_is_rejected() {
    // `i > 0` and `i >= 0` differ at `i == 0`, so the equivalence is false.
    assert_not_verified(
        GAP1_FORALL_FALSE,
        "gap1_forall_body_wrong_property_is_rejected",
    );
}

// ===========================================================================
// GAP2 positive: a reused let-bound `Set` across `.filter` then `.map` must
// keep resolving `s` (single use already worked; the second use regressed to
// "unresolved variable s").
// ===========================================================================

const GAP2_SET_REUSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.contains(5 as int))]
#[trust_vc::ensures(true)]
fn gap2_reused_set_filter_then_map(s: Set<int>) {
    let pos1 = s.filter(SpecFn::new(|i: int| i > (0 as int)));
    let pos2 = s.map(SpecFn::new(|i: int| i + (1 as int)));
    // Both reuses of `s` must resolve. `5` is positive, so it survives filter;
    // `5 + 1 = 6` is in the forward image of `map`.
    trust_vc::assert!(pos1.contains(5 as int));
    trust_vc::assert!(pos2.contains(6 as int));
}
"#;

const GAP2_LET_LOCAL_REUSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap2_reused_let_local_set_filter_then_map() {
    let nonneg = Set::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos1 = nonneg.filter(SpecFn::new(|i: int| i > (0 as int)));
    // `nonneg` reused a THIRD time here: if GAP2 did not preserve it across the
    // `.filter` above, this `.map` line would fail extraction with "unresolved
    // variable nonneg". So constructing `pos2` at all is the GAP2 assertion.
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    // `7 >= 0 && 7 > 0`, proved from the comprehension biconditional at the
    // concrete element 7 (filter side). Membership of the *mapped* comprehension
    // (`pos2.contains(1)`, which needs reverse-image witness discovery
    // `x + 1 == 1 => x == 0` through two quantifier layers) is a separate
    // Set::map-over-comprehension completeness item (tracked), not GAP2.
    trust_vc::assert!(pos1.contains(7 as int));
}
"#;

#[test]
fn gap2_reused_set_param_filter_then_map_verifies() {
    assert_verified(GAP2_SET_REUSE, "gap2_reused_set_filter_then_map");
}

#[test]
fn gap2_reused_let_local_set_filter_then_map_verifies() {
    // `nonneg` is a let-local (no declared type), so this also exercises the
    // bind-time ghost-collection inference that targets the relaxation.
    assert_verified(
        GAP2_LET_LOCAL_REUSE,
        "gap2_reused_let_local_set_filter_then_map",
    );
}

// ===========================================================================
// GAP2 SOUNDNESS adversarial (most important): a genuinely-mutated `Vec`
// receiver must NOT carry stale pre-mutation state forward. `Vec::clear`,
// `Vec::pop`, and `Vec::truncate` are in-place mutators that are NOT
// intercepted by the re-binding handlers, so they reach the invalidation site.
// An assertion that would only hold under the STALE (pre-mutation) model must
// fail closed, proving the type-keyed marking still invalidates mutators.
// ===========================================================================

const VEC_CLEAR_STALE: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(true)]
fn vec_clear_must_invalidate_stale_state() {
    let v: Vec<u32> = vec![1u32, 2u32, 3u32];
    v.clear();
    // `clear` empties the vector. Asserting the PRE-clear length would only
    // hold if the stale model were preserved — it must fail closed.
    trust_vc::assert!(v.len() == 3usize);
}
"#;

const VEC_TRUNCATE_STALE: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(true)]
fn vec_truncate_must_invalidate_stale_state() {
    let v: Vec<u32> = vec![10u32, 20u32, 30u32];
    v.truncate(1usize);
    trust_vc::assert!(v.len() == 3usize);
}
"#;

const VEC_POP_STALE: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(true)]
fn vec_pop_must_invalidate_stale_state() {
    let v: Vec<u32> = vec![100u32, 200u32];
    v.pop();
    trust_vc::assert!(v.len() == 2usize);
}
"#;

#[test]
fn vec_clear_must_invalidate_stale_state() {
    // SOUNDNESS: a preserved (stale) model would prove `v.len() == 3` after
    // `clear`. The receiver MUST be invalidated, so this fails closed.
    assert_not_verified(VEC_CLEAR_STALE, "vec_clear_must_invalidate_stale_state");
}

#[test]
fn vec_truncate_must_invalidate_stale_state() {
    assert_not_verified(
        VEC_TRUNCATE_STALE,
        "vec_truncate_must_invalidate_stale_state",
    );
}

#[test]
fn vec_pop_must_invalidate_stale_state() {
    assert_not_verified(VEC_POP_STALE, "vec_pop_must_invalidate_stale_state");
}

// A read-through control: the SAME pre-state assertion DOES hold when no
// mutation occurs between the binding and the read. This rules out the
// possibility that the adversarial cases above merely fail because `Vec::len`
// or `vec!` is unsupported (which would make the test non-discriminating).
const VEC_NO_MUTATION_CONTROL: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(true)]
fn vec_len_without_mutation_holds() {
    let v: Vec<u32> = vec![1u32, 2u32, 3u32];
    trust_vc::assert!(v.len() == 3usize);
}
"#;

#[test]
fn vec_len_without_mutation_holds_control() {
    assert_verified(VEC_NO_MUTATION_CONTROL, "vec_len_without_mutation_holds");
}

// ===========================================================================
// GAP1 SOUNDNESS: capture-avoidance. The GAP1 closure-body substitution must
// NOT capture a free variable of the substituted value under a closure binder
// that reuses its name. Here the comprehension `c`'s model retains the free
// function parameter `p`, and the quantifier rebinds `p`. A naive (capturing)
// substitution collapses membership to `p >= p` (a tautology) and makes the
// FALSE property verify. With capture-avoidance the substitution is skipped
// (fail-closed), so this must NOT verify.
// ===========================================================================

const GAP1_CAPTURE_COLLISION_FALSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_capture_collision_false(p: int) {
    let c = Set::new(SpecFn::new(|x: int| x >= p));
    // forall p. c.contains(p) == (p >= p)  ==  forall p. (p >= param_p) == true
    // ==  forall p. p >= param_p  — FALSE (e.g. p = param_p - 1). Must NOT verify.
    trust_vc::assert!(forall |p: int| c.contains(p) == (p >= p));
}
"#;

// The SAME false property with the quantifier binder alpha-renamed p -> q (no
// name collision). It must ALSO not verify. Together with the colliding case
// this proves alpha-invariance: a sound substitution cannot depend on the
// bound-variable's name, so renaming the binder must not change the verdict.
const GAP1_CAPTURE_ALPHA_RENAMED_FALSE: &str = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::ensures(true)]
fn gap1_capture_alpha_renamed_false(p: int) {
    let c = Set::new(SpecFn::new(|x: int| x >= p));
    trust_vc::assert!(forall |q: int| c.contains(q) == (q >= q));
}
"#;

#[test]
fn gap1_capture_collision_must_not_verify() {
    assert_not_verified(GAP1_CAPTURE_COLLISION_FALSE, "gap1_capture_collision_false");
}

#[test]
fn gap1_capture_alpha_renamed_must_not_verify() {
    assert_not_verified(
        GAP1_CAPTURE_ALPHA_RENAMED_FALSE,
        "gap1_capture_alpha_renamed_false",
    );
}
