// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! #102: named-struct and tuple-struct destructuring of a `let`-LOCAL.
//!
//! `let Pair { a, b } = value;` / `let TupleThing(a, b) = value;` (where `value`
//! is itself a let-local carrying an inferred scoped struct type) previously
//! over-rejected with "unresolved variable" because the destructure base type
//! was resolved ONLY via the VC variable table, which is populated for
//! parameters but not for let-locals.
//!
//! The base now also resolves from the local's inferred scoped struct/enum type
//! name, recovering the SAME `Datatype` the parameter path produces. The
//! destructure therefore binds each pattern variable to a FIELD PROJECTION of
//! the local's own value — never a free/havoc variable — so these guards check
//! BOTH directions: a true field claim verifies, and a wrong field claim
//! produces a counterexample (fail-closed, no false-Verified).

use super::*;

fn verify_src(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let f = find_function(&file, func).unwrap();
    match extract_verification_conditions_with_file_context(&file, f) {
        Ok(vc) => vc.verify(),
        Err(e) => VerifyResult::Error {
            message: e.to_string(),
        },
    }
}

// ---------------------------------------------------------------------------
// Named-struct destructure of a let-local
// ---------------------------------------------------------------------------

/// A true field claim through a named-struct destructure of a let-local
/// verifies.
#[test]
fn named_struct_destructure_let_local_true_verifies() {
    let code = r#"
        struct Pair { a: bool, b: bool }
        fn test() {
            let value = Pair { a: true, b: false };
            let Pair { a: first, b: second } = value;
            assert!(first);
            assert!(!second);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "named-struct destructure of a let-local should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a WRONG field claim through a named-struct destructure must NOT
/// verify (the binding is the field value, so the false claim fails closed).
#[test]
fn named_struct_destructure_let_local_wrong_field_not_verified() {
    let code = r#"
        struct Pair { a: bool, b: bool }
        fn test() {
            let value = Pair { a: true, b: false };
            let Pair { a: first, b: second } = value;
            assert!(second);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "wrong named-struct destructure field claim must not verify, got {:?}",
        verify_src(code, "test")
    );
}

/// A wrong NUMERIC field claim counterexamples (a real model, not just a
/// trivially-false assertion).
#[test]
fn named_struct_destructure_let_local_wrong_numeric_field_counterexamples() {
    let code = r#"
        struct Pair { a: u64, b: u64 }
        fn test() {
            let value = Pair { a: 7u64, b: 9u64 };
            let Pair { a: first, b: second } = value;
            assert!(first == 9u64);
        }
    "#;
    assert!(
        matches!(
            verify_src(code, "test"),
            VerifyResult::Counterexample { .. }
        ),
        "wrong numeric named-struct field claim must counterexample, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Tuple-struct destructure of a let-local
// ---------------------------------------------------------------------------

/// A true field claim through a tuple-struct destructure of a let-local
/// verifies. This also exercises the tuple-struct constructor (`Expr::Call`)
/// arm that records the bound local's scoped struct type.
#[test]
fn tuple_struct_destructure_let_local_true_verifies() {
    let code = r#"
        struct TupleThing(bool, bool);
        fn test() {
            let value = TupleThing(true, false);
            let TupleThing(first, second) = value;
            assert!(first);
            assert!(!second);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "tuple-struct destructure of a let-local should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a WRONG field claim through a tuple-struct destructure must NOT
/// verify.
#[test]
fn tuple_struct_destructure_let_local_wrong_field_not_verified() {
    let code = r#"
        struct TupleThing(bool, bool);
        fn test() {
            let value = TupleThing(true, false);
            let TupleThing(first, second) = value;
            assert!(second);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "wrong tuple-struct destructure field claim must not verify, got {:?}",
        verify_src(code, "test")
    );
}

/// A wrong NUMERIC tuple-struct field claim counterexamples.
#[test]
fn tuple_struct_destructure_let_local_wrong_numeric_field_counterexamples() {
    let code = r#"
        struct TupleThing(u64, u64);
        fn test() {
            let value = TupleThing(7u64, 9u64);
            let TupleThing(first, second) = value;
            assert!(first == 9u64);
        }
    "#;
    assert!(
        matches!(
            verify_src(code, "test"),
            VerifyResult::Counterexample { .. }
        ),
        "wrong numeric tuple-struct field claim must counterexample, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Binds the FIELD VALUE, not a free variable (symbolic source)
// ---------------------------------------------------------------------------

/// The destructured variables must equal the local's actual field projections.
/// With a SYMBOLIC source (a parameter flowing into the let-local), a true
/// "equals the projection" claim can only verify if the binding is the field
/// value — a free/havoc binding would leave the claim unprovable.
#[test]
fn named_struct_destructure_let_local_binds_field_value_symbolic() {
    let code = r#"
        struct Pair { a: u64, b: u64 }
        fn test(p: Pair) {
            let value = Pair { a: p.a, b: p.b };
            let Pair { a: first, b: second } = value;
            assert!(first == p.a);
            assert!(second == p.b);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "destructure must bind the field VALUE (symbolic), got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS dual of the above: claiming a destructured field equals the OTHER
/// field is NOT generally true for a symbolic source, so it must NOT verify
/// (proving the binding is not a free variable that could prove anything).
#[test]
fn named_struct_destructure_let_local_cross_field_symbolic_not_verified() {
    let code = r#"
        struct Pair { a: u64, b: u64 }
        fn test(p: Pair) {
            let value = Pair { a: p.a, b: p.b };
            let Pair { a: first, b: second } = value;
            assert!(first == second);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "cross-field symbolic claim must not verify, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Generic user types
// ---------------------------------------------------------------------------

/// A GENERIC named struct destructured through a turbofished literal
/// (`Pair::<bool, bool> { .. }`) verifies a true claim: named-struct fields are
/// reached via field access (`.a`), which is fully supported. (This is the
/// `generic_named_struct_destructure_currently_error` port shape; the engine now
/// handles it, a sound-gain pin flip owned reclassification-side.)
#[test]
fn generic_named_struct_destructure_let_local_true_verifies() {
    let code = r#"
        struct Pair<A, B> { a: A, b: B }
        fn test() {
            let value = Pair::<bool, bool> { a: true, b: false };
            let Pair { a: first, b: second } = value;
            assert!(first);
            assert!(!second);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "generic named-struct destructure should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// The GENERIC tuple-struct destructure now projects fields by direct tuple
/// field access (`(value).0`) rather than the monomorphized variant selector
/// (`get_TupleThing_0()`, whose type-parameter return sort fails
/// overflow-assumption encoding). Field access resolves the concrete
/// instantiated field type, so a true field claim through a generic tuple-struct
/// destructure of a let-local now VERIFIES. (Was previously pinned fail-closed
/// for the unsupported selector; field access bypasses that gap soundly.)
#[test]
fn generic_tuple_struct_destructure_let_local_true_verifies() {
    let code = r#"
        struct TupleThing<A, B>(A, B);
        fn test() {
            let value = TupleThing::<i32, i32>(3i32, 4i32);
            let TupleThing(first, second) = value;
            assert!(first == 3i32);
            assert!(second == 4i32);
        }
    "#;
    assert_eq!(
        verify_src(code, "test"),
        VerifyResult::Verified,
        "generic tuple-struct destructure should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS companion: a WRONG field claim through the generic tuple-struct
/// destructure must fail closed — the field-access projection is a real
/// projection of the value, so it can never false-Verify.
#[test]
fn generic_tuple_struct_destructure_let_local_wrong_not_verified() {
    let code = r#"
        struct TupleThing<A, B>(A, B);
        fn test() {
            let value = TupleThing::<i32, i32>(3i32, 4i32);
            let TupleThing(first, second) = value;
            assert!(first == 4i32);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "wrong claim through generic tuple-struct destructure must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Enum tuple-variant destructure of a let-local (#102, enum extension)
// ---------------------------------------------------------------------------
//
// `let Enum::Variant(a, b) = value;` (where `value` is a let-local bound to an
// enum-variant constructor `Enum::Variant(..)`) previously over-rejected with
// "unresolved variable" because the local's scoped type was inferred only for
// STRUCT constructors: an enum-variant constructor is a MULTI-segment callee
// path, which the single-segment `expr_path_ident` filter dropped. The scoped
// type now also resolves from the enum named by the constructor's
// second-to-last path segment, so the destructure binds each pattern variable
// to a FIELD PROJECTION of the local's own value. Rust permits an irrefutable
// enum-variant `let` pattern ONLY for a single-variant enum, so the projection
// is total (sound). Guards check BOTH directions.

/// A true field claim through an enum tuple-variant destructure of a let-local
/// verifies.
#[test]
fn enum_variant_destructure_let_local_true_verifies() {
    let code = r#"
        enum BoolPair { Pair(bool, bool) }
        fn test() {
            let value = BoolPair::Pair(true, false);
            let BoolPair::Pair(first, second) = value;
            assert!(first);
            assert!(!second);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "enum-variant destructure of a let-local should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a WRONG field claim through an enum tuple-variant destructure must
/// NOT verify — the binding is the field projection, so a false claim fails
/// closed (never a false-Verified).
#[test]
fn enum_variant_destructure_let_local_wrong_field_not_verified() {
    let code = r#"
        enum BoolPair { Pair(bool, bool) }
        fn test() {
            let value = BoolPair::Pair(true, false);
            let BoolPair::Pair(first, _second) = value;
            assert!(!first);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "enum-variant destructure wrong-field claim must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: field ORDER is preserved (second field is `false`); asserting it
/// is true must fail closed — pins that the projection is not field-swapped.
#[test]
fn enum_variant_destructure_let_local_field_order_not_verified() {
    let code = r#"
        enum BoolPair { Pair(bool, bool) }
        fn test() {
            let value = BoolPair::Pair(true, false);
            let BoolPair::Pair(_first, second) = value;
            assert!(second);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "enum-variant destructure field-order claim must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Plain tuple destructure of a let-local (#102, tuple extension)
// ---------------------------------------------------------------------------
//
// `let (a, b) = t;` (t a tuple-valued local) previously over-rejected with
// "unresolved variable" — `collect_pattern_bindings` had no `Pat::Tuple` arm
// and a tuple is not a registered Datatype, so the base-type path never fired.
// Each plain-ident element now binds to the SCOPED value of the tuple field
// projection `(t).i` (tuple field access is already supported), so the
// destructure binds a real projection of the local's own value. Guards check
// BOTH directions.

/// A true field claim through a plain tuple destructure of a let-local verifies.
#[test]
fn tuple_destructure_let_local_true_verifies() {
    let code = r#"
        fn test() {
            let t = (10i32, 20i32);
            let (a, b) = t;
            assert!(a == 10i32);
            assert!(b == 20i32);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "tuple destructure of a let-local should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a WRONG field claim must NOT verify — the binding is the field
/// projection, so a false claim fails closed (never a false-Verified).
#[test]
fn tuple_destructure_let_local_wrong_field_not_verified() {
    let code = r#"
        fn test() {
            let t = (10i32, 20i32);
            let (a, _b) = t;
            assert!(a == 20i32);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "tuple destructure wrong-field claim must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: field ORDER is preserved — a wildcard-skipped first element does
/// not shift the second; asserting the wrong value for `b` fails closed.
#[test]
fn tuple_destructure_let_local_field_order_not_verified() {
    let code = r#"
        fn test() {
            let t = (10i32, 20i32);
            let (_a, b) = t;
            assert!(b == 10i32);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "tuple destructure field-order claim must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// Nested + trailing-rest tuple destructure of a let-local (#102, tuple ext)
// ---------------------------------------------------------------------------
//
// `let (a, (b, c)) = t;` recurses on the projected base `(t).1`; `let (a, ..)`
// binds the front elements (known indices) and ignores the trailing rest. A
// binding AFTER the rest fails closed (its index would need the tuple arity).

/// Nested tuple destructure binds each leaf to its composed field projection.
#[test]
fn nested_tuple_destructure_let_local_true_verifies() {
    let code = r#"
        fn test() {
            let t = (1i32, (2i32, 3i32));
            let (a, (b, c)) = t;
            assert!(a == 1i32);
            assert!(b == 2i32);
            assert!(c == 3i32);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "nested tuple destructure should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a wrong claim on a NESTED leaf must fail closed.
#[test]
fn nested_tuple_destructure_let_local_wrong_leaf_not_verified() {
    let code = r#"
        fn test() {
            let t = (1i32, (2i32, 3i32));
            let (_a, (_b, c)) = t;
            assert!(c == 2i32);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "nested tuple wrong-leaf claim must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

/// Trailing-rest tuple destructure binds the front element and ignores the rest.
#[test]
fn tuple_rest_destructure_let_local_true_verifies() {
    let code = r#"
        fn test() {
            let t = (1i32, 2i32, 3i32);
            let (a, ..) = t;
            assert!(a == 1i32);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "trailing-rest tuple destructure should verify a true claim, got {:?}",
        verify_src(code, "test")
    );
}

// ---------------------------------------------------------------------------
// #2777 choose.rs: TYPED tuple destructure of a non-path (macro) init
// ---------------------------------------------------------------------------
//
// `let (a, b): (int, int) = choose!(|i, j| i <= j);` parses as
// Pat::Type(Pat::Tuple, ty). Its init is a macro with no projection base, so it
// reaches neither the bare-Pat::Tuple projection path nor local_pattern_base —
// previously the elements were left UNBOUND (unresolved-variable at use). They
// now bind by routing the init through a fresh typed local (the proven
// whole-tuple path `let t: (int,int) = choose!(..); t.0`) and projecting each
// element off it. Guards check BOTH directions.

/// A relation implied by the multi-binder choose witness constraint verifies
/// through the typed tuple destructure.
#[test]
fn typed_tuple_destructure_of_choose_macro_true_verifies() {
    let code = r#"
        fn test() {
            let (a, b): (int, int) = choose!(|i: int, j: int| i <= j);
            assert!(a <= b);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "typed tuple destructure of a choose! result should verify a witness-implied claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a claim that CONTRADICTS the witness constraint (`a > b` against
/// `i <= j`) must fail closed (no false-Verified).
#[test]
fn typed_tuple_destructure_of_choose_macro_contradiction_not_verified() {
    let code = r#"
        fn test() {
            let (a, b): (int, int) = choose!(|i: int, j: int| i <= j);
            assert!(a > b);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "a claim contradicting the choose witness constraint must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

// #2777 cluster 4b: NO-ascription tuple destructure of a multi-binder choose.
// `let (x, y) = choose!(|i: int, j: int| i < j)` has no type ascription, so the
// tuple type (int, int) is recovered from the choose binders and routed through
// the same typed-synthetic-local path.

/// A witness-implied relation verifies through the no-ascription destructure.
#[test]
fn no_ascription_tuple_destructure_of_multi_binder_choose_true_verifies() {
    let code = r#"
        fn test() {
            let (x, y) = choose!(|i: int, j: int| i < j);
            assert!(x < y);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test"), VerifyResult::Verified),
        "no-ascription tuple destructure of a multi-binder choose should verify a witness-implied claim, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: a claim contradicting the witness constraint fails closed.
#[test]
fn no_ascription_tuple_destructure_of_multi_binder_choose_contradiction_not_verified() {
    let code = r#"
        fn test() {
            let (x, y) = choose!(|i: int, j: int| i < j);
            assert!(x >= y);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test"), VerifyResult::Verified),
        "a claim contradicting the no-ascription choose witness constraint must fail closed, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS: bounded ground Hilbert instances are implications, not fabricated
/// witnesses. An empty predicate therefore cannot make its own result true.
#[test]
fn multi_binder_choose_empty_arithmetic_predicate_not_verified() {
    let code = r#"
        fn test() {
            let (x, y): (int, int) = choose!(|i: int, j: int| i < i && j < j);
            assert!(x < x && y < y);
        }
    "#;
    let result = verify_src(code, "test");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "an empty choose predicate must not fabricate a witness, got {result:?}",
    );
}

/// SOUNDNESS: the finite completeness basis does not restrict the Hilbert
/// choice domain. A singleton witness outside {-1, 0, 1} must not let a claim
/// about an unrelated in-basis value verify.
#[test]
fn multi_binder_choose_out_of_basis_witness_does_not_pin_small_value() {
    let code = r#"
        fn test() {
            let (x, y): (int, int) = choose!(|i: int, j: int| i == 10 && j == 20);
            assert!(x == 0 && y == 1);
        }
    "#;
    let result = verify_src(code, "test");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "an out-of-basis witness must not be replaced by a small value, got {result:?}",
    );
}
