// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness + parity regressions for `match`-arm and `if let` scoping of
//! branch-local hypotheses and arithmetic-safety obligations (cluster P0-B).
//!
//! Before this fix, `visit_expr_match` visited each arm body as a bare expression
//! with NO per-arm pattern+guard path condition: a branch-local `assume!` /
//! call-`ensures` leaked UNCONDITIONALLY into straight-line code after the match
//! or into a sibling arm (a catastrophic false `Verified`), arm-body and
//! match-SCRUTINEE arithmetic carried no exec panic-freedom obligation, and an
//! `if let` then-branch threaded no discriminant guard. The fix pushes a
//! conjoined per-arm `pattern && guard && !(earlier arms)` path condition, threads
//! the `if let` discriminant condition, and routes the arm-body + scrutinee
//! arithmetic through the (now branch-guarded) exec arithmetic-safety emitter.
//!
//! Both directions are pinned:
//! * SOUNDNESS — a branch-local `assume!`/call-`ensures` no longer proves a goal
//!   outside the arm; arm-body / scrutinee arithmetic with a feasible panic is a
//!   counterexample, never `Verified`.
//! * NO OVER-REJECTION — a catch-all arm's assert discharges from the negated
//!   earlier patterns; an arm-body / scrutinee arithmetic that is SAFE under the
//!   arm/precondition guard still verifies.

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let item =
        find_function(&file, func).unwrap_or_else(|| panic!("fixture should define fn {func}"));
    extract_verification_conditions_with_file_context(&file, item)
        .map(|vc| vc.verify())
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        })
}

fn assert_verified(code: &str, func: &str) {
    assert_eq!(
        verdict(code, func),
        VerifyResult::Verified,
        "fn {func} should verify"
    );
}

fn assert_not_verified(code: &str, func: &str) {
    let v = verdict(code, func);
    assert_ne!(
        v,
        VerifyResult::Verified,
        "fn {func} must NOT verify (sound fail-closed/counterexample expected), got {v:?}"
    );
}

fn assert_counterexample(code: &str, func: &str) {
    let v = verdict(code, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "fn {func} should produce a counterexample, got {v:?}"
    );
}

// ===========================================================================
// SOUNDNESS — a branch-local `assume!` must not leak past the match.
// ===========================================================================

#[test]
fn assume_in_match_arm_does_not_leak_after_match() {
    // requires(b==0 && sel==0) forces the `0 => a/b` arm — a guaranteed panic.
    assert_not_verified(
        r#"
        fn f(v: u64, a: u64) {
            match v { 0u64 => { trust_vc::assume!(a == 7u64); } _ => {} }
            trust_vc::assert!(a == 7u64);
        }
        "#,
        "f",
    );
}

#[test]
fn assume_in_match_arm_does_not_leak_into_sibling_arm() {
    assert_not_verified(
        r#"
        fn f(v: u64, a: u64) {
            match v {
                0u64 => { trust_vc::assume!(a == 7u64); }
                _ => { trust_vc::assert!(a == 7u64); }
            }
        }
        "#,
        "f",
    );
}

#[test]
fn call_ensures_in_match_arm_does_not_leak_after_match() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(result == 7u64)]
        fn mk(x: u64) -> u64 { 7u64 }
        fn f(v: u64, a: u64) {
            match v { 0u64 => { let _ = mk(a); } _ => {} }
            trust_vc::assert!(a == 7u64);
        }
        "#,
        "f",
    );
}

#[test]
fn assume_in_guarded_match_arm_does_not_leak() {
    // The arm `x if x == 0` is irrefutable+guarded; its selection condition
    // renders as `v == 0`, so the assume is `v == 0 ==> a == 7` and the post-match
    // assert cannot discharge.
    assert_not_verified(
        r#"
        fn f(v: u64, a: u64) {
            match v { x if x == 0u64 => { trust_vc::assume!(a == 7u64); } _ => {} }
            trust_vc::assert!(a == 7u64);
        }
        "#,
        "f",
    );
}

#[test]
fn assume_in_if_let_then_does_not_leak_after_if_let() {
    assert_not_verified(
        r#"
        fn f(opt: Option<u64>, a: u64) {
            if let Some(_w) = opt { trust_vc::assume!(a == 7u64); }
            trust_vc::assert!(a == 7u64);
        }
        "#,
        "f",
    );
}

// ===========================================================================
// SOUNDNESS — arm-body and match-scrutinee arithmetic carry their panic
// obligation under the arm/precondition guard.
// ===========================================================================

#[test]
fn match_arm_division_by_zero_is_counterexample() {
    assert_not_verified(
        r#"
        #[trust_vc::requires(b == 0u64 && sel == 0u64)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64, sel: u64) { let _ = match sel { 0u64 => a / b, _ => 0u64 }; }
        "#,
        "f",
    );
}

#[test]
fn match_scrutinee_division_by_zero_is_counterexample() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) { let _ = match a / b { 0u64 => 1u64, _ => 2u64 }; }
        "#,
        "f",
    );
}

// ===========================================================================
// NO OVER-REJECTION — guarded-safe arms / scrutinees and catch-all asserts.
// ===========================================================================

#[test]
fn match_arm_division_safe_under_arm_guard_verifies() {
    // The `_` arm divides by `sel`, which is non-zero there — must verify.
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, sel: u64) {
            let _ = match sel { 0u64 => 0u64, _ => a / sel };
            trust_vc::assert!(true);
        }
        "#,
        "f",
    );
}

#[test]
fn match_scrutinee_division_safe_under_precondition_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(b != 0u64)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) { let _ = match a / b { 0u64 => 1u64, _ => 2u64 }; }
        "#,
        "f",
    );
}

#[test]
fn catch_all_arm_assert_discharges_from_negated_prior_patterns() {
    // The `_` arm runs only when `v != 0`; its assert must verify from the
    // cumulative negation of the earlier literal pattern.
    assert_verified(
        r#"
        fn f(v: u64) {
            match v {
                0u64 => { trust_vc::assert!(v == 0u64); }
                _ => { trust_vc::assert!(v != 0u64); }
            }
        }
        "#,
        "f",
    );
}

#[test]
fn if_branch_guarded_division_verifies() {
    // Pre-existing over-rejection the branch-guarded arithmetic obligation fixes:
    // `a / sel` only runs when `sel != 0`.
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, sel: u64) { if sel != 0u64 { let _ = a / sel; } trust_vc::assert!(true); }
        "#,
        "f",
    );
}

#[test]
fn assume_in_arm_discharges_matching_arm_assert() {
    // A NON-leak completeness check: the assume IS usable inside its own arm.
    assert_verified(
        r#"
        fn f(v: u64, a: u64) {
            match v {
                0u64 => { trust_vc::assume!(a == 7u64); trust_vc::assert!(a == 7u64); }
                _ => {}
            }
        }
        "#,
        "f",
    );
}

// ---------------------------------------------------------------------------
// Match-arm pattern variables bind to scrutinee FIELD PROJECTIONS
// ---------------------------------------------------------------------------
//
// Previously an arm variable was shadowed opaque (`x` → `"x"`), so an
// obligation inside the arm body (`Some(x) => { assert!(x == 5); }`) failed to
// lower with "unresolved variable `x`". Each arm variable now binds to the
// scrutinee's field projection under the arm's path condition, so the
// obligation resolves and is decided. Sound: the binding is arm-isolated and
// path-guarded, so a wrong claim fails closed (counterexample), never a false
// Verified.

const MATCH_ARM_ENUMS: &str = r#"
    enum Opt { Some(i32), None }
    enum Pair { Two(i32, i32) }
"#;

#[test]
fn match_arm_binding_resolves_and_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            match o {{
                Opt::Some(x) => {{ assert!(x == 5i32); }}
                Opt::None => {{}}
            }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn match_arm_binding_wrong_claim_not_verified() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            match o {{
                Opt::Some(x) => {{ assert!(x == 6i32); }}
                Opt::None => {{}}
            }}
        }}"
    );
    assert_not_verified(&code, "f");
}

#[test]
fn match_arm_two_field_binding_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let p = Pair::Two(3i32, 7i32);
            match p {{
                Pair::Two(a, b) => {{ assert!(a == 3i32); assert!(b == 7i32); }}
            }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn match_arm_two_field_wrong_field_not_verified() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let p = Pair::Two(3i32, 7i32);
            match p {{
                Pair::Two(a, _b) => {{ assert!(a == 7i32); }}
            }}
        }}"
    );
    assert_not_verified(&code, "f");
}

// ---------------------------------------------------------------------------
// `if let` then-branch variables bind to discriminant FIELD PROJECTIONS
// ---------------------------------------------------------------------------
//
// Same fix as the match-arm binding, in `visit_expr_if`: an `if let P = e`
// then-branch variable now binds to the discriminant's field projection under
// the threaded `is-<variant>(e)` path condition, so an obligation in the
// then-branch (`if let Some(x) = o { assert!(x == 5); }`) resolves instead of
// failing to lower with "unresolved variable". The binding is then-branch-local
// (snapshot-restored) and path-guarded, so a wrong claim fails closed.

#[test]
fn if_let_binding_resolves_and_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            if let Opt::Some(x) = o {{ assert!(x == 5i32); }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn if_let_binding_wrong_claim_not_verified() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            if let Opt::Some(x) = o {{ assert!(x == 6i32); }}
        }}"
    );
    assert_not_verified(&code, "f");
}

#[test]
fn if_let_two_field_binding_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let p = Pair::Two(3i32, 7i32);
            if let Pair::Two(a, b) = p {{ assert!(a == 3i32); assert!(b == 7i32); }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn if_let_with_else_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            if let Opt::Some(x) = o {{ assert!(x == 5i32); }} else {{ assert!(true); }}
        }}"
    );
    assert_verified(&code, "f");
}

// ---------------------------------------------------------------------------
// Bare whole-value match-arm binding (`match n { x if x > 3 => .. }`)
// ---------------------------------------------------------------------------
//
// A bare irrefutable binding `x` over a NON-datatype scrutinee (e.g. a scalar)
// has no field projection, so it binds to the scrutinee value itself. Before
// this, only datatype-projected arm variables resolved; a scalar catch-all /
// guarded arm's `x` was shadowed opaque ("unresolved variable"). Sound: the
// binding is arm-isolated and guarded by the arm's path condition (which
// includes the rendered guard), so a wrong claim — or an over-claim beyond what
// the guard grants — fails closed.

#[test]
fn bare_scalar_arm_binding_verifies() {
    let code = r#"
        fn f() {
            let n = 5i32;
            match n {
                x => { assert!(x == 5i32); }
            }
        }
    "#;
    assert_verified(code, "f");
}

#[test]
fn bare_scalar_arm_binding_wrong_not_verified() {
    let code = r#"
        fn f() {
            let n = 5i32;
            match n {
                x => { assert!(x == 6i32); }
            }
        }
    "#;
    assert_not_verified(code, "f");
}

#[test]
fn guarded_scalar_arm_uses_guard_binding() {
    let code = r#"
        fn f() {
            let n = 5i32;
            match n {
                x if x > 3i32 => { assert!(x > 3i32); }
                _ => {}
            }
        }
    "#;
    assert_verified(code, "f");
}

#[test]
fn guarded_scalar_arm_overclaim_not_verified() {
    // The guard grants only `x > 3`; asserting `x > 10` (false at n == 5) must
    // fail closed — the guard binding cannot prove more than the guard grants.
    let code = r#"
        fn f() {
            let n = 5i32;
            match n {
                x if x > 3i32 => { assert!(x > 10i32); }
                _ => {}
            }
        }
    "#;
    assert_not_verified(code, "f");
}

// ---------------------------------------------------------------------------
// `@` bindings in match arms (`n @ Opt::Some(v)`)
// ---------------------------------------------------------------------------
//
// An `@`-binding names the ENTIRE matched value while its subpattern binds
// deeper. `collect_pattern_bindings` previously rejected `Pat::Ident` with a
// subpattern; it now binds the outer name to the base and recurses into the
// subpattern against the same base. The arm's "matches" condition already
// descends into the subpattern (`arm_pattern_match_condition`), so both bindings
// resolve under the correct `is-Some(o)` guard.

#[test]
fn at_binding_subpattern_resolves_and_verifies() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            match o {{
                n @ Opt::Some(v) => {{ assert!(v == 5i32); }}
                Opt::None => {{}}
            }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn at_binding_subpattern_wrong_not_verified() {
    let code = format!(
        "{MATCH_ARM_ENUMS}
        fn f() {{
            let o = Opt::Some(5i32);
            match o {{
                n @ Opt::Some(v) => {{ assert!(v == 6i32); }}
                Opt::None => {{}}
            }}
        }}"
    );
    assert_not_verified(&code, "f");
}

// ---------------------------------------------------------------------------
// Generic datatype accessor selectors resolve (generic enum matches)
// ---------------------------------------------------------------------------
//
// A generic datatype receiver's type string carries its type arguments
// (`GEnum<i32>`), but auto-generated accessor methods (`get_V_field`, `is_V`)
// are keyed on the bare datatype name (`GEnum`). The method dispatch now retries
// the lookup with the generic arguments stripped, so a payload selector in a
// generic enum match arm resolves. Sound: a wrong claim on the payload refutes.

const GENERIC_ENUM: &str = "enum GEnum<T> { V(T), N }";

#[test]
fn generic_enum_match_payload_verifies() {
    let code = format!(
        "{GENERIC_ENUM}
        fn f() {{
            let g = GEnum::<i32>::V(9i32);
            match g {{
                GEnum::V(w) => {{ assert!(w == 9i32); }}
                GEnum::N => {{}}
            }}
        }}"
    );
    assert_verified(&code, "f");
}

// ---------------------------------------------------------------------------
// Or-pattern MERGED binder resolution (`A(x) | B(x) => .. x ..`)
// ---------------------------------------------------------------------------
//
// An or-pattern arm binds the same name in every disjunct, but each disjunct
// projects it from a DIFFERENT variant of the scrutinee. The `Pat::Or` arm of
// `collect_pattern_bindings` merges the per-disjunct projections into a
// first-match `if`/`else` chain over the disjuncts' exact (flat-pattern)
// variant testers, so an obligation in the arm body resolves the binder — and
// can never resolve it to the WRONG disjunct's value. Both directions are
// pinned under BOTH constructor flows: the matching disjunct's true payload
// fact verifies, a false payload fact is a counterexample. Incompatible
// disjunct payload types and nested refutable disjuncts fail closed.

const OR_PATTERN_ENUMS: &str = r#"
    enum E2 { Bar(u64), Qux(u64) }
    enum E3 { Left(u64), Right(u64), Empty }
"#;

#[test]
fn or_pattern_payload_true_fact_verifies_under_qux_flow() {
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f() {{
            match E2::Qux(7u64) {{
                E2::Bar(payload) | E2::Qux(payload) => {{ assert!(payload == 7u64); }}
            }}
        }}"
    );
    // Would NOT verify if the merged binder resolved to the Bar disjunct's
    // (unconstrained) selector value — this pins correct disjunct selection.
    assert_verified(&code, "f");
}

#[test]
fn or_pattern_payload_false_fact_counterexamples_under_qux_flow() {
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f() {{
            match E2::Qux(7u64) {{
                E2::Bar(payload) | E2::Qux(payload) => {{ assert!(payload == 5u64); }}
            }}
        }}"
    );
    // 5 is the OTHER (Bar-flow) payload in the sibling test: when the
    // scrutinee is Qux(7), claiming payload == 5 must refute.
    assert_counterexample(&code, "f");
}

#[test]
fn or_pattern_payload_true_fact_verifies_under_bar_flow() {
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f() {{
            match E2::Bar(5u64) {{
                E2::Bar(payload) | E2::Qux(payload) => {{ assert!(payload == 5u64); }}
            }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn or_pattern_payload_false_fact_counterexamples_under_bar_flow() {
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f() {{
            match E2::Bar(5u64) {{
                E2::Bar(payload) | E2::Qux(payload) => {{ assert!(payload == 7u64); }}
            }}
        }}"
    );
    assert_counterexample(&code, "f");
}

#[test]
fn or_pattern_payload_local_scrutinee_arithmetic_verifies() {
    // The ported match.rs regression shape, over a LOCAL scrutinee: the
    // arm-body arithmetic's overflow obligation must resolve the merged binder
    // (this was the `unresolved variable payload` lowering regression).
    let code = format!(
        "{OR_PATTERN_ENUMS}
        #[trust_vc::ensures(result == 8u64)]
        fn f() -> u64 {{
            let e = E3::Right(7u64);
            match e {{
                E3::Left(payload) | E3::Right(payload) => payload + 1u64,
                E3::Empty => 0u64,
            }}
        }}"
    );
    assert_verified(&code, "f");
}

#[test]
fn or_pattern_payload_unbounded_overflow_not_verified() {
    // A PARAM scrutinee leaves the payload unbounded, so the arm-body
    // arithmetic's overflow obligation is genuine: the merged binder must
    // carry the disjuncts' REAL payload values (u64::MAX + 1 overflows), not a
    // vacuously-provable stand-in.
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f(e: E3) -> u64 {{
            match e {{
                E3::Left(payload) | E3::Right(payload) => payload + 1u64,
                E3::Empty => 0u64,
            }}
        }}"
    );
    assert_not_verified(&code, "f");
}

#[test]
fn or_pattern_incompatible_disjunct_types_fail_closed() {
    // Disjuncts binding DIFFERENT payload types cannot share one merged
    // binder; the merge must fail closed (never mis-typed), leaving the
    // binder unresolved.
    let code = r#"
        enum EMix { A(u64), B(bool) }
        fn f() {
            match EMix::A(3u64) {
                EMix::A(x) | EMix::B(x) => { assert!(x == x); }
            }
        }
    "#;
    assert_not_verified(code, "f");
}

#[test]
fn or_pattern_nested_refutable_disjunct_fails_closed() {
    // A nested REFUTABLE sub-pattern makes the shallow variant tester an
    // over-approximation (`is_A` cannot distinguish `A(B(x))` from `A(C(x))`),
    // so a merged binder could take the wrong disjunct's value; the merge must
    // fail closed instead of claiming the payload fact.
    let code = r#"
        enum Inner { B(u64), C(u64) }
        enum Outer { A(Inner) }
        fn f() {
            let o = Outer::A(Inner::C(5u64));
            match o {
                Outer::A(Inner::B(x)) | Outer::A(Inner::C(x)) => { assert!(x == 3u64); }
            }
        }
    "#;
    assert_not_verified(code, "f");
}

#[test]
fn or_pattern_guarded_arm_assume_does_not_leak() {
    // Rust RETRIES later or-pattern disjuncts when a guard fails for an
    // earlier matching one, so a guard over a multi-disjunct or-pattern is not
    // renderable from one merged binding; the arm must stay unguardable (its
    // assume dropped), never leak the hypothesis past the match.
    let code = format!(
        "{OR_PATTERN_ENUMS}
        fn f(e: E2, a: u64) {{
            match e {{
                E2::Bar(x) | E2::Qux(x) if x == 0u64 => {{ trust_vc::assume!(a == 7u64); }}
                _ => {{}}
            }}
            assert!(a == 7u64);
        }}"
    );
    assert_not_verified(&code, "f");
}

// ---------------------------------------------------------------------------
// Ground-constructor scrutinee projections (`match S(..) { S(a, b) => .. }`)
// ---------------------------------------------------------------------------
//
// A constructor-expression scrutinee is not a declared variable, so
// `local_pattern_base` cannot type it; the ground-constructor fallback types
// it from the constructor itself (struct constructors/literals for any flat
// arm; enum constructors for or-pattern arms only, preserving the pinned
// fail-closed boundary for ordinary variant arms). Both directions pinned.

#[test]
fn ground_tuple_struct_scrutinee_arm_arithmetic_verifies() {
    let code = r#"
        struct SP(u64, u64);
        #[trust_vc::ensures(result == 13u64)]
        fn f() -> u64 {
            match SP(4u64, 9u64) { SP(l, r) => l + r }
        }
    "#;
    assert_verified(code, "f");
}

#[test]
fn ground_tuple_struct_scrutinee_wrong_claim_counterexamples() {
    let code = r#"
        struct SP(u64, u64);
        fn f() {
            match SP(4u64, 9u64) { SP(l, _r) => { assert!(l == 9u64); } }
        }
    "#;
    assert_counterexample(code, "f");
}

#[test]
fn ground_named_struct_scrutinee_arm_arithmetic_verifies() {
    let code = r#"
        struct NP { a: u64, b: u64 }
        #[trust_vc::ensures(result == 13u64)]
        fn f() -> u64 {
            match (NP { a: 4u64, b: 9u64 }) { NP { a, b } => a + b }
        }
    "#;
    assert_verified(code, "f");
}

#[test]
fn generic_enum_match_payload_wrong_not_verified() {
    let code = format!(
        "{GENERIC_ENUM}
        fn f() {{
            let g = GEnum::<i32>::V(9i32);
            match g {{
                GEnum::V(w) => {{ assert!(w == 10i32); }}
                GEnum::N => {{}}
            }}
        }}"
    );
    assert_not_verified(&code, "f");
}
