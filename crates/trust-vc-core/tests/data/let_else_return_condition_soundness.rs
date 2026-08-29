// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Probes for the `ReturnValue::Conditional` let-else return model.
//
// The model is `result == if COND { <tail value> } else { <else value> }`, where
// COND is the tail `let PAT = SCRUTINEE else { return … };` statement's match
// condition. A COND of `true` for a REFUTABLE PAT makes the else value
// unreachable and discharges the postcondition against the tail value alone —
// a cardinal false verify. `false` is exactly as wrong in the other direction.
//
// The condition used to be derived by a predicate hand-copied into
// `vc_extraction.rs`, which had drifted into answering `"true"` for every
// pattern it did not recognize. It now routes to the obligation collector's own
// type-aware, fail-closed handler
// (`body_extract::pattern_match_condition_for_scoped_value`). Every TARGET below
// verified before that change.
//
// Every function here has the same shape — `let PAT = <scrutinee> else { return
// 0 }; 7` under a postcondition that is TRUE only on the tail path — so the
// pattern is the single variable.

enum E {
    V { a: u64 },
    W,
}

enum T {
    V(u64),
    W,
}

enum Tri {
    A(u64),
    B(u64),
    C,
}

const K: u64 = 5;

mod consts {
    pub const LIMIT: u64 = 5;
}

// ---------------------------------------------------------------- TARGETS ---
// Each is FALSE at the else path (`E::W` / `T::W` / a non-matching scalar), where
// the function returns 0, not 7. Correct verdict is anything but Verified.

// `Pat::Struct` — the copy's `Pat::Struct(_) => "true"` arm.
#[trust_vc::ensures(result == 7)]
fn struct_pattern_must_not_widen(e: E) -> u64 {
    let E::V { a } = e else { return 0 };
    7
}

// `Pat::Struct` with a rest pattern.
#[trust_vc::ensures(result == 7)]
fn struct_rest_pattern_must_not_widen(e: E) -> u64 {
    let E::V { .. } = e else { return 0 };
    7
}

// `Pat::Struct` with a FIELD refinement. Guarded by the variant test, so only
// the dropped `a: 0` refinement can carry this to Verified.
#[trust_vc::ensures(e.is_V() ==> result == 7)]
fn struct_field_literal_must_not_drop(e: E) -> u64 {
    let E::V { a: 0 } = e else { return 0 };
    7
}

// `Pat::TupleStruct` with an ELEMENT refinement — same isolation as above: the
// bare `is_V()` tester the copy emitted ignores the `0`.
#[trust_vc::ensures(t.is_V() ==> result == 7)]
fn tuple_struct_element_literal_must_not_drop(t: T) -> u64 {
    let T::V(0) = t else { return 0 };
    7
}

// `Pat::TupleStruct` with an `@`-subpattern refinement.
#[trust_vc::ensures(t.is_V() ==> result == 7)]
fn tuple_struct_at_subpattern_must_not_drop(t: T) -> u64 {
    let T::V(x @ 0) = t else { return 0 };
    7
}

// `Pat::Lit` — reached the copy's `_ => "true"` catch-all.
#[trust_vc::ensures(result == 7)]
fn literal_pattern_must_not_widen(n: u64) -> u64 {
    let 5u64 = n else { return 0 };
    7
}

// `Pat::Range`.
#[trust_vc::ensures(result == 7)]
fn range_pattern_must_not_widen(n: u64) -> u64 {
    let 1u64..=5u64 = n else { return 0 };
    7
}

// `Pat::Tuple` carrying a literal refinement.
#[trust_vc::ensures(result == 7)]
fn tuple_pattern_literal_must_not_widen(p: (u64, u64)) -> u64 {
    let (0u64, b) = p else { return 0 };
    7
}

// `Pat::Or`.
#[trust_vc::ensures(result == 7)]
fn or_pattern_must_not_widen(t: Tri) -> u64 {
    let (Tri::A(_) | Tri::B(_)) = t else { return 0 };
    7
}

// `Pat::Reference`.
#[trust_vc::ensures(result == 7)]
fn reference_pattern_must_not_widen(t: &T) -> u64 {
    let &T::V(0) = t else { return 0 };
    7
}

// `Pat::Ident` holding an UPPERCASE const — Rust resolves it to `K`, so this is
// a refutable value pattern, not a binding.
#[trust_vc::ensures(result == 7)]
fn bare_const_ident_pattern_must_not_widen(n: u64) -> u64 {
    let K = n else { return 0 };
    7
}

// `Pat::Path` holding a module-path const — same refutability, via the path arm.
#[trust_vc::ensures(result == 7)]
fn path_const_pattern_must_not_widen(n: u64) -> u64 {
    let consts::LIMIT = n else { return 0 };
    7
}

// `Pat::Ident` with an `@`-subpattern at top level.
#[trust_vc::ensures(result == 7)]
fn top_level_at_binding_must_not_widen(t: T) -> u64 {
    let x @ T::V(_) = t else { return 0 };
    7
}

// `Pat::Slice`.
#[trust_vc::ensures(result == 7)]
fn slice_pattern_must_not_widen(s: &[u64]) -> u64 {
    let [a, b] = s else { return 0 };
    7
}

// --------------------------------------------------------------- CONTROLS ---
// NARROWNESS PINS. A guard that declined every let-else would pass every target
// above and be a capability disaster. These must all stay Verified.

// An IRREFUTABLE binder still models: condition `true` is the correct answer.
#[trust_vc::ensures(result == 7)]
fn irrefutable_binder_still_verifies(n: u64) -> u64 {
    let x = n else { return 0 };
    7
}

// …including when the scrutinee is not a resolvable path, so no type is
// available. Irrefutability is decided on the pattern alone.
#[trust_vc::ensures(result == 7)]
fn irrefutable_binder_unresolvable_scrutinee_still_verifies(n: u64) -> u64 {
    let x = identity(n) else { return 0 };
    7
}

#[trust_vc::spec]
fn identity(n: u64) -> u64 {
    n
}

// A REFUTABLE pattern the shared handler models CORRECTLY still verifies, with
// the postcondition guarded by the very tester it derives.
#[trust_vc::ensures(t.is_V() ==> result == 7)]
fn refutable_tuple_struct_still_verifies(t: T) -> u64 {
    let T::V(x) = t else { return 0 };
    7
}

// The `Option` spelling of the same thing (`is_some()`, not `is_Some()`) — the
// type gate the copy did not have.
#[trust_vc::ensures(o.is_some() ==> result == 7)]
fn refutable_option_still_verifies(o: Option<u64>) -> u64 {
    let Some(x) = o else { return 0 };
    7
}

// A single-variant STRUCT pattern is irrefutable, and must not be mistaken for
// a refutable enum variant.
struct S {
    a: u64,
}

#[trust_vc::ensures(result == 7)]
fn irrefutable_struct_pattern_still_verifies(s: S) -> u64 {
    let S { a } = s else { return 0 };
    7
}

// The ELSE value must be REACHED, not just unreachable-by-accident. This is the
// dual of the targets: it is provable only when the condition is genuinely the
// variant test. It flips to a counterexample the moment the condition is forced
// to `true`, which is what makes it a discriminating pin rather than a
// restatement.
#[trust_vc::ensures(!t.is_V() ==> result == 0)]
fn else_value_stays_reachable(t: T) -> u64 {
    let T::V(x) = t else { return 0 };
    7
}

// A let-LOCAL (not a parameter) scrutinee: the pre-statement walk must have it
// in scope for its type to resolve.
#[trust_vc::ensures(result == 7)]
fn let_local_scrutinee_still_verifies() -> u64 {
    let t = T::V(1);
    let T::V(x) = t else { return 0 };
    7
}
