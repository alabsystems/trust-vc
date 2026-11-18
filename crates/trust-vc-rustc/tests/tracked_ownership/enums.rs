//! Real original enum ownership through the verifier and its native checker.
use super::*;

#[test]
fn native_unit_variants_keep_the_new_mode_match_transport() {
    let source = r#"verus! {
enum E<A> { V(A), Empty }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>, tracked a: A) {
    let tracked empty = E::<A>::Empty;
    match empty { E::V(x) => consume(x), E::Empty => {} }
    match e {
        E::V(x) => consume(x),
        E::Empty => consume(a),
    }
}
}"#;
    let result = common::run(
        "owned_original_enum_new_mode",
        source,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    let twin = source.replace(
        "        E::V(x) => consume(x),",
        "        E::V(x) => { consume(x); consume(x); },",
    );
    let result = common::run(
        "owned_original_enum_new_mode_twin",
        &twin,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].code.as_deref(), Some("E0382"), "{result:?}");
    assert!(result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|f| f["verdict"] != "verified"));
}

#[test]
fn original_enum_arms_keep_disjoint_native_moves() {
    pair(
        "owned_original_enum_arms",
        r#"verus! {
enum E<A> { Left(A), Right(A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>) {
    match e {
        E::Left(x) => consume(x),
        E::Right(x) => consume(x),
    }
}
}"#,
        "        E::Left(x) => consume(x),",
        "        E::Left(x) => { consume(x); consume(x); },",
    );
}

#[test]
fn original_enum_constructor_and_variant_field_moves_reach_borrowck() {
    pair(
        "owned_original_enum_ctor",
        r#"verus! {
enum E<A> { Pair(A, A), Single(A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A, tracked b: A) {
    let tracked e = E::Pair(a, b);
    match e {
        E::Pair(x, y) => { consume(x); consume(y); },
        E::Single(x) => consume(x),
    }
}
}"#,
        "        E::Pair(x, y) => { consume(x); consume(y); },",
        "        E::Pair(x, y) => { consume(x); consume(x); },",
    );
}

#[test]
fn original_enum_arm_results_keep_tracked_return_ownership() {
    pair(
        "owned_original_enum_result",
        r#"verus! {
enum E<A> { First(A), Second(A) }
proof fn pick<A>(tracked e: E<A>) -> (tracked r: A) {
    match e { E::First(x) => x, E::Second(x) => x }
}
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>) {
    let tracked chosen = pick(e);
    consume(chosen);
}
}"#,
        "    consume(chosen);",
        "    consume(chosen); consume(chosen);",
    );
}

#[test]
fn native_moves_in_an_enum_arm_remain_unavailable_after_the_join() {
    pair(
        "owned_original_enum_join",
        r#"verus! {
enum E<A> { V(A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>, tracked spare: A) {
    match e { E::V(x) => consume(x) }
    consume(spare);
}
}"#,
        "    consume(spare);",
        "    consume(e);",
    );
}

#[test]
fn enum_erasure_guards_references_and_unchecked_lifetimes_remain_refused() {
    for (name, source, args) in [
        (
            "owned_original_enum_erased_field",
            r#"verus! {
enum E<A> { V(A), Erased(#[verifier::spec] A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>) {
    match e { E::V(x) => consume(x), E::Erased(_) => {} }
}
}"#,
            &[][..],
        ),
        (
            "owned_original_enum_guard",
            r#"verus! {
enum E<A> { V(A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>) {
    match e { E::V(x) if true => consume(x), _ => {} }
}
}"#,
            &[][..],
        ),
        (
            "owned_original_enum_ref_binding",
            r#"verus! {
enum E<A> { V(A) }
proof fn check<A>(tracked e: E<A>) { match e { E::V(ref x) => {} } }
}"#,
            &[][..],
        ),
        (
            "owned_original_enum_record_ctor",
            r#"verus! {
enum E<A> { V { value: A } }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) { let tracked e = E::V { value: a }; consume(e); }
}"#,
            &[][..],
        ),
        (
            "owned_original_enum_no_lifetime",
            r#"verus! {
enum E<A> { V(A) }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked e: E<A>) { match e { E::V(x) => { consume(x); consume(x); } } }
}"#,
            &["--no-lifetime"][..],
        ),
    ] {
        refused(name, source, args);
    }
}
