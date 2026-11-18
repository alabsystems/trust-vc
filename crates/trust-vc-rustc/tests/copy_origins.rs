//! Genuine native Copy bounds, caller instantiation and borrowed value origins.
mod common;

fn checked(name: &str, source: &str) {
    let run = common::run(name, source, &[]);
    assert_eq!(run.exit, 0, "{run:?}");
    assert_eq!(run.outcome(), "checked", "{run:?}");
    assert!(run.errors().is_empty(), "{run:?}");
    let verified = run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|function| function["verdict"] == "verified")
        .collect::<Vec<_>>();
    assert_eq!(verified.len(), 2, "{run:?}");
    assert!(
        verified.iter().all(|function| function["sites_proved"]
            .as_u64()
            .is_some_and(|sites| sites > 0)),
        "{run:?}"
    );
}

#[test]
fn generic_copy_from_shared_storage_preserves_each_result() {
    checked(
        "native_copy_shared",
        r#"verus! {
        fn twice<T: Copy>(input: &T) -> (out: (T, T))
            ensures out.0 == *input, out.1 == *input,
        { (*input, *input) }
        fn caller() {
            let (a, b) = twice(&7u8);
            assert(a == 7); assert(b == 7);
        }
    }"#,
    );
}

#[test]
fn generic_copy_value_does_not_prove_a_false_postcondition() {
    let run = common::run(
        "native_copy_false",
        r#"verus! {
        fn wrong<T: Copy>(input: &T) -> (out: T)
            ensures out != *input,
        { *input }
    }"#,
        &[],
    );
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message == "postcondition not satisfied"),
        "{run:?}"
    );
}

#[test]
fn compound_copy_and_supertrait_bounds_keep_native_caller_obligations() {
    let source = r#"verus! {
        trait NativeCopy: Copy {}
        impl NativeCopy for u16 {}
        fn copy_pair<T: NativeCopy>(input: &(T, T)) -> (out: (T, T))
            ensures out == *input,
        { *input }
        fn caller() {
            let out = copy_pair(&(3u16, 5u16));
            assert(out.0 == 3); assert(out.1 == 5);
        }
    }"#;
    checked("native_copy_compound", source);
    let false_source = source.replace("assert(out.1 == 5)", "assert(out.1 != 5)");
    let failed = common::run("native_copy_compound_false", &false_source, &[]);
    assert_eq!(failed.exit, 1, "{failed:?}");
    assert_eq!(failed.outcome(), "verification-failed", "{failed:?}");
    assert!(
        failed
            .errors()
            .iter()
            .any(|error| error.message == "assertion failed"),
        "{failed:?}"
    );
}

#[test]
fn distinct_copy_parameters_keep_both_obligations_at_the_same_actual_type() {
    checked(
        "native_copy_same_actual",
        r#"verus! {
        fn pair<T: Copy, U: Copy>(first: &T, second: &U) -> (out: (T, U))
            ensures out.0 == *first, out.1 == *second,
        { (*first, *second) }
        fn caller() {
            let out = pair(&3u8, &5u8);
            assert(out.0 == 3); assert(out.1 == 5);
        }
    }"#,
    );
}

#[test]
fn shared_reference_only_forwarding_keeps_the_original_copy_work_context() {
    let source = r#"verus! {
        fn sink<T>(value: T) {}
        fn forward<T: Copy>(input: &T) {
            sink(*input);
            assert(*input == *input);
        }
        fn caller() { forward(&7u8); }
    }"#;
    let run = common::run("native_copy_forward", source, &[]);
    assert_eq!(run.exit, 0, "{run:?}");
    assert_eq!(run.outcome(), "checked", "{run:?}");
    let function = run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "forward")
        .unwrap();
    assert_eq!(function["verdict"], "verified", "{run:?}");
    assert_eq!(function["sites_proved"], 1, "{run:?}");
    let false_source = source.replace("assert(*input == *input)", "assert(*input != *input)");
    let failed = common::run("native_copy_forward_false", &false_source, &[]);
    assert_eq!(failed.exit, 1, "{failed:?}");
    assert_eq!(failed.outcome(), "verification-failed", "{failed:?}");
    assert!(
        failed
            .errors()
            .iter()
            .any(|error| error.message == "assertion failed"),
        "{failed:?}"
    );
}

#[test]
fn a_shared_borrow_does_not_supply_a_missing_copy_bound() {
    let run = common::run(
        "native_copy_missing",
        r#"verus! {
        fn take<T>(input: &T) -> T { *input }
    }"#,
        &[],
    );
    assert_eq!(run.exit, 1, "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.code.as_deref() == Some("E0507")
                || error.message.contains("cannot move out")
                || error.message.contains("abstract-owned-origin")),
        "{run:?}"
    );
    let verified = run.record["functions"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|function| function["verdict"] == "verified")
        .count();
    assert_eq!(verified, 0, "{run:?}");
}

#[test]
fn a_trait_named_copy_does_not_supply_the_native_copy_language_item() {
    let run = common::run(
        "native_copy_shadow",
        r#"verus! {
        mod local { pub trait Copy {} }
        trait NativeCopy: local::Copy {}
        fn take<T: NativeCopy>(input: &T) -> T { *input }
    }"#,
        &[],
    );
    assert_eq!(run.exit, 1, "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.code.as_deref() == Some("E0507")
                || error.message.contains("cannot move out")),
        "{run:?}"
    );
    assert!(
        run.record["functions"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|function| function["verdict"] != "verified"),
        "{run:?}"
    );
}
