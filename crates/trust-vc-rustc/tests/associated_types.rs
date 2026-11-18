//! Ground associated-type identities use the compiler's real scalar values.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) -> common::Run {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["verdict"] == "verified" && f["sites_proved"].as_u64().unwrap_or(0) > 0),
        "{result:?}"
    );
    result
}

fn refused(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|f| f["verdict"] != "verified"),
        "{result:?}"
    );
}

#[test]
fn original_ground_normalization_keeps_true_and_false_range_checks() {
    let result = common::run(
        "assoc_original_ranges",
        "verus! {
        trait T { type X; }
        struct S;
        impl T for S { type X = u8; }
        proof fn test1(x: <S as T>::X) { assert(x < 256); }
        proof fn test2(x: <S as T>::X) { assert(x < 255); }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
    assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
    let functions = result.record["functions"].as_array().unwrap();
    assert!(
        functions.iter().any(|f| f["def_path"] == "test1"
            && f["verdict"] == "verified"
            && f["sites_proved"].as_u64().unwrap_or(0) > 0),
        "{result:?}"
    );
    assert!(
        functions.iter().any(|f| f["def_path"] == "test2"
            && f["verdict"] == "failed"
            && f["sites_failed"] == 1),
        "{result:?}"
    );
}

#[test]
fn native_member_identity_distinguishes_traits_and_implementations() {
    checked(
        "assoc_distinct_members",
        "verus! {
        trait T { type X; }
        trait U { type X; }
        struct S;
        struct B;
        impl T for S { type X = u16; }
        impl U for S { type X = bool; }
        impl T for B { type X = u8; }
        proof fn broad(x: <S as T>::X) { assert(x < 65536); }
        proof fn flag(x: <S as U>::X) { assert(x || !x); }
        proof fn narrow(x: <B as T>::X) { assert(x < 256); }
    }",
    );
    let false_range = common::run(
        "assoc_distinct_false",
        "verus! {
        trait T { type X; }
        struct S;
        impl T for S { type X = u16; }
        proof fn bad(x: <S as T>::X) { assert(x < 256); }
    }",
        &[],
    );
    assert_eq!(
        false_range.outcome(),
        "verification-failed",
        "{false_range:?}"
    );
    assert_eq!(false_range.errors().len(), 1, "{false_range:?}");
}

#[test]
fn member_mode_and_external_attributes_grant_no_eligibility() {
    for (name, declaration, assignment) in [
        ("assoc_spec_decl", "#[verifier::spec]", ""),
        ("assoc_external_decl", "#[verifier::external]", ""),
        ("assoc_spec_assignment", "", "#[verifier::spec]"),
        ("assoc_external_assignment", "", "#[verifier::external]"),
    ] {
        refused(
            name,
            &format!(
                "verus! {{
            trait T {{ {declaration} type X; }}
            struct S;
            impl T for S {{ {assignment} type X = u8; }}
            proof fn test() {{ assert(true); }}
        }}"
            ),
        );
    }
    refused(
        "assoc_external_trait",
        "verus! {
        #[verifier::external] trait T { type X; }
        struct S;
        impl T for S { type X = u8; }
        proof fn test() { assert(true); }
    }",
    );
}

#[test]
fn unsupported_declaration_and_assignment_shapes_stay_refused() {
    for (name, source) in [
        ("assoc_gat", "verus! { trait T { type X<A>; } struct S; impl T for S { type X<A> = u8; } proof fn test() { assert(true); } }"),
        ("assoc_bound", "verus! { trait T { type X: Copy; } struct S; impl T for S { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_mixed", "verus! { trait T { type X; proof fn f(); } struct S; impl T for S { type X = u8; proof fn f() {} } proof fn test() { assert(true); } }"),
        ("assoc_trait_parameter", "verus! { trait T<A> { type X; } struct S; impl T<bool> for S { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_nominal_rhs", "verus! { trait T { type X; } struct S; struct V; impl T for S { type X = V; } proof fn test() { assert(true); } }"),
        ("assoc_generic_impl", "verus! { trait T { type X; } struct S<A>(A); impl<A> T for S<A> { type X = u8; } proof fn test() { assert(true); } }"),
    ] { refused(name, source); }
}

#[test]
fn excluded_sources_and_foreign_traits_grant_no_eligibility() {
    for (name, source) in [
        ("assoc_foreign_self", "verus! { trait T { type X; } impl T for core::num::NonZeroU8 { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_external_self", "verus! { trait T { type X; } #[verifier::external] struct S; impl T for S { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_opaque_self", "verus! { trait T { type X; } #[verifier::external_body] struct S { x: bool } impl T for S { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_parent_external", "verus! { #[verifier::external] mod ignored { pub trait T { type X; } } struct S; impl ignored::T for S { type X = u8; } proof fn test() { assert(true); } }"),
        ("assoc_foreign_trait", "verus! { struct S; impl core::ops::Deref for S { type Target = u8; fn deref(&self) -> &u8 { &0 } } proof fn test() { assert(true); } }"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{name}: {result:?}");
        assert_ne!(result.outcome(), "checked", "{name}: {result:?}");
        assert!(result.record["functions"].as_array().unwrap().iter().all(|f| f["verdict"] != "verified"), "{name}: {result:?}");
    }
}

#[test]
fn original_native_type_dependency_survives_ground_normalization() {
    let cycle = common::run(
        "assoc_cyclic_self",
        "verus! {
        trait T { type X; }
        struct S(<Self as T>::X) where Self: T;
        impl T for S { type X = u8; }
    }",
        &[],
    );
    assert_eq!(cycle.exit, 1, "{cycle:?}");
    assert_eq!(cycle.outcome(), "verus-rejected", "{cycle:?}");
    assert_eq!(cycle.errors().len(), 1, "{cycle:?}");
    assert!(
        cycle.errors()[0]
            .message
            .contains("found a cyclic self-reference in a definition"),
        "{cycle:?}"
    );
    checked(
        "assoc_noncyclic_field",
        "verus! {
        trait T { type X; }
        struct A;
        impl T for A { type X = u8; }
        struct B(<A as T>::X);
        proof fn test(x: <A as T>::X) { assert(x < 256); }
    }",
    );
}

#[test]
fn normalized_arguments_keep_match_modes_and_false_sites() {
    checked(
        "assoc_match_positive",
        "verus! {
        trait T { type X; } struct S; impl T for S { type X = u8; }
        proof fn test(x: <S as T>::X) {
            let y: u8 = match x { 0 => 1, _ => 2 };
            assert(y == 1 || y == 2);
        }
    }",
    );
    let negative = common::run(
        "assoc_match_negative",
        "verus! {
        trait T { type X; } struct S; impl T for S { type X = u8; }
        proof fn test(x: <S as T>::X) {
            let y: u8 = match x { 0 => 1, _ => 2 };
            assert(y == 3);
        }
    }",
        &[],
    );
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert_eq!(negative.errors().len(), 1, "{negative:?}");
    assert!(
        negative.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|function| function["verdict"] == "failed" && function["sites_failed"] == 1),
        "{negative:?}"
    );
}

#[test]
fn native_errors_and_mode_failures_still_prevent_verification() {
    let error = common::run(
        "assoc_rust_error",
        "verus! {
        trait T { type X; } struct S;
        impl T for S { type X = UndefinedType; }
        proof fn test() { assert(true); }
    }",
        &[],
    );
    assert_eq!(error.outcome(), "front-end-rejected", "{error:?}");
    assert!(
        error.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|f| f["verdict"] != "verified"),
        "{error:?}"
    );
    let mode = common::run(
        "assoc_mode_error",
        "verus! {
        trait T { type X; } struct S;
        impl T for S { type X = u8; }
        spec fn hidden() -> u8 { 1 }
        fn bad(x: <S as T>::X) -> u8 { hidden() }
    }",
        &[],
    );
    assert_eq!(mode.outcome(), "verus-rejected", "{mode:?}");
    assert!(
        mode.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|f| f["verdict"] != "verified"),
        "{mode:?}"
    );
}

#[test]
fn generic_projection_pair_checks_positive_and_rejects_cycle() {
    // This original positive program has no assertion sites. Its successful
    // trait-instance call mapping is checked here without inventing proof sites.
    let positive = common::run(
        "assoc_generic_projection_positive",
        include_str!("traits/normalized_projection_bound.rs"),
        &[],
    );
    assert_eq!(positive.exit, 0, "{positive:?}");
    assert_eq!(positive.outcome(), "checked", "{positive:?}");
    assert_eq!(positive.record["erase_exit"], 0, "{positive:?}");
    assert_eq!(positive.record["refused"], false, "{positive:?}");
    assert!(positive.errors().is_empty(), "{positive:?}");
    assert!(
        positive.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{positive:?}"
    );
    let functions = positive.record["functions"].as_array().unwrap();
    for name in ["test", "<bool as T1>::f1", "<S<A> as T3>::f3"] {
        let selected: Vec<_> = functions.iter().filter(|f| f["def_path"] == name).collect();
        assert_eq!(selected.len(), 1, "{name}: {positive:?}");
        assert_eq!(selected[0]["verdict"], "verified", "{name}: {positive:?}");
        assert_eq!(selected[0]["sites_proved"], 0, "{name}: {positive:?}");
        assert_eq!(selected[0]["sites_failed"], 0, "{name}: {positive:?}");
    }
    assert!(
        functions
            .iter()
            .all(|f| f["verdict"] == "verified" || f["verdict"] == "declared"),
        "{positive:?}"
    );
    let vcir = positive
        .vcir
        .as_deref()
        .expect("positive native projection VcIR");
    assert!(
        vcir.contains("test_crate::T1::f1::<projection[T2::X]<T0>>()"),
        "{vcir}"
    );
    assert!(
        vcir.contains("test_crate::S::f3::<[verus_builtin::int]>()"),
        "{vcir}"
    );
    assert!(vcir.contains("call[#1] test_crate::f1()"), "{vcir}");

    // Keep the unchanged cyclic twin as a negative. Success of the positive
    // instance must not grant eligibility to its recursive call graph.
    let cycle = common::run(
        "assoc_generic_projection_cycle",
        include_str!("traits/normalized_projection_bound.twin.rs"),
        &[],
    );
    assert_eq!(cycle.exit, 1, "{cycle:?}");
    assert_ne!(cycle.outcome(), "checked", "{cycle:?}");
    assert!(
        cycle.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|f| f["verdict"] != "verified"),
        "{cycle:?}"
    );
}
