//! Ghost redirection retains native identity, executable behavior and false twins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str, consumer: &str, proved: u64) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    let function = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == consumer)
        .unwrap();
    assert_eq!(function["verdict"], "verified", "{result:?}");
    assert_eq!(function["sites_proved"], proved, "{result:?}");
    assert_eq!(function["sites_failed"], 0, "{result:?}");
}

fn assertion_failed(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
    assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
    assert_eq!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .map(|function| function["sites_failed"].as_u64().unwrap_or(0))
            .sum::<u64>(),
        1,
        "{result:?}"
    );
}

fn rejected(name: &str, source: &str, message: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    assert!(
        result
            .errors()
            .iter()
            .any(|error| error.message.contains(message)),
        "{result:?}"
    );
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"),
        "{result:?}"
    );
}

#[test]
fn ghost_redirect_does_not_change_executable_calls_or_add_an_equation() {
    checked(
        "autospec_exec_and_ghost",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        fn actual(x: bool) -> (r: bool) ensures r == x { x }
        fn test() {
            let actual_value = actual(true);
            assert(actual_value);
            assert(!actual(true));
        }
    }",
        "test",
        2,
    );
    assertion_failed(
        "autospec_exec_false",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        fn actual(x: bool) -> (r: bool) ensures r == x { x }
        fn test() { let result = actual(true); assert(!result); }
    }",
    );
    assertion_failed(
        "autospec_ghost_false",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        fn actual(x: bool) -> (r: bool) ensures r == x { x }
        proof fn test() { assert(actual(true)); }
    }",
    );
}

#[test]
fn unchanged_inherent_method_case_and_its_executable_false_twin() {
    // The A40 when_used_as_spec::test1 function bodies, including differing
    // values. The unchanged original harness is a separate replay scope.
    checked(
        "autospec_original_test1",
        "verus! {
        struct S {}
        impl S {
            spec fn f(&self) -> bool { true }
            #[verifier::when_used_as_spec(f)]
            fn g(&self) -> bool { false }
            fn h(&self) {
                self.g();
                assert(self.g());
            }
        }
    }",
        "S::h",
        1,
    );
    assertion_failed(
        "autospec_original_exec_false",
        "verus! {
        struct S {}
        impl S {
            spec fn f(&self) -> bool { true }
            #[verifier::when_used_as_spec(f)]
            fn g(&self) -> bool { false }
            fn h(&self) { let b = self.g(); assert(b); }
        }
    }",
    );
}

#[test]
fn generic_arguments_and_borrowed_operands_keep_their_original_types() {
    checked(
        "autospec_generic",
        "verus! {
        pub open spec fn logical<T>(value: &T) -> bool { true }
        #[verifier::when_used_as_spec(logical)]
        fn actual<T>(value: &T) -> bool { false }
        proof fn test<T>(value: &T) {
            assert(actual::<T>(value));
            assert(actual::<T>(value));
        }
    }",
        "test",
        2,
    );
    assertion_failed(
        "autospec_generic_false",
        "verus! {
        pub open spec fn logical<T>(value: &T) -> bool { false }
        #[verifier::when_used_as_spec(logical)]
        fn actual<T>(value: &T) -> bool { true }
        proof fn test<T>(value: &T) { assert(actual::<T>(value)); }
    }",
    );
}

#[test]
fn executable_operand_effects_happen_once() {
    checked(
        "autospec_effect_once",
        "verus! {
        pub open spec fn logical(value: u8) -> u8 { value }
        #[verifier::when_used_as_spec(logical)]
        fn actual(value: u8) -> (r: u8) ensures r == value { value }
        fn test() {
            let mut count: u8 = 0;
            let result = actual({ count += 1; count });
            assert(count == 1);
            assert(result == 1);
            assert(actual(3) == 3);
        }
    }",
        "test",
        4,
    );
    assertion_failed("autospec_effect_false", "verus! {
        pub open spec fn logical(value: u8) -> u8 { value }
        #[verifier::when_used_as_spec(logical)]
        fn actual(value: u8) -> (r: u8) ensures r == value { value }
        fn test() { let mut count: u8 = 0; let result = actual({ count += 1; count }); assert(count == 2); }
    }");
}

#[test]
fn unused_declarations_still_require_a_real_spec_target_and_signature() {
    for (name, source, message) in [
        ("missing", "verus! { #[verifier::when_used_as_spec(absent)] fn source() -> bool { true } }", "cannot find function referred to in when_used_as_spec"),
        ("wrong_mode", "verus! { fn target() -> bool { true } #[verifier::when_used_as_spec(target)] fn source() -> bool { true } }", "must point from an exec function to a spec function"),
        ("wrong_source", "verus! { spec fn target() -> bool { true } #[verifier::when_used_as_spec(target)] proof fn source() -> bool { true } }", "must point from an exec function to a spec function"),
        ("wrong_args", "verus! { spec fn target(x: int) -> bool { true } #[verifier::when_used_as_spec(target)] fn source(x: u64) -> bool { true } }", "same parameters"),
        ("wrong_return", "verus! { spec fn target() -> bool { true } #[verifier::when_used_as_spec(target)] fn source() -> u8 { 0 } }", "same return types"),
        ("wrong_arity", "verus! { spec fn target(x: bool) -> bool { x } #[verifier::when_used_as_spec(target)] fn source() -> bool { true } }", "same parameters"),
    ] { rejected(&format!("autospec_{name}"), source, message); }
}

#[test]
fn generic_type_names_and_trait_bounds_follow_pinned_a40_well_formedness() {
    // A40 explicitly compares its type-parameter identifier lists, in addition
    // to bound/type correspondence. This is not target selection by name.
    rejected(
        "autospec_type_parameter_name",
        "verus! {
        spec fn target<A>(x: &A) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source<B>(x: &B) -> bool { true }
    }",
        "same type bounds",
    );
    rejected(
        "autospec_missing_bound",
        "verus! {
        spec fn target<T: Copy>(x: &T) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source<T>(x: &T) -> bool { true }
    }",
        "same type bounds",
    );
    checked(
        "autospec_matching_bounds",
        "verus! {
        pub open spec fn target<T: Copy>(x: &T) -> bool { true }
        #[verifier::when_used_as_spec(target)] fn source<T: Copy>(x: &T) -> bool { false }
        proof fn test<T: Copy>(x: &T) { assert(source::<T>(x)); }
    }",
        "test",
        1,
    );
}

#[test]
fn lifetime_alpha_equivalence_preserves_the_real_reference_relationship() {
    checked(
        "autospec_lifetime_alpha",
        "verus! {
        pub open spec fn target<'a>(x: &'a bool) -> &'a bool { x }
        #[verifier::when_used_as_spec(target)] fn source<'b>(x: &'b bool) -> &'b bool { x }
        proof fn test(x: &bool) { assert(*source(x) == *x); }
    }",
        "test",
        1,
    );
    assertion_failed(
        "autospec_lifetime_alpha_false",
        "verus! {
        pub open spec fn target<'a>(x: &'a bool) -> &'a bool { x }
        #[verifier::when_used_as_spec(target)] fn source<'b>(x: &'b bool) -> &'b bool { x }
        proof fn test(x: &bool) { assert(*source(x) != *x); }
    }",
    );
    // This is an explicit native compatibility boundary, not an A40 error:
    // the two functions tie their result to different input lifetimes.
    let result = common::run("autospec_lifetime_relationship", "verus! {
        spec fn target<'a, 'b>(x: &'a bool, y: &'b bool) -> &'b bool { y }
        #[verifier::when_used_as_spec(target)] fn source<'a, 'b>(x: &'a bool, y: &'b bool) -> &'a bool { x }
    }", &[]);
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"),
        "{result:?}"
    );
}

#[test]
fn shared_reference_expressions_retain_their_value_and_false_twin() {
    checked(
        "shared_reference_expression",
        "verus! {
        pub open spec fn select<'a>(b: bool, x: &'a bool, y: &'a bool) -> &'a bool {
            if b { x } else { y }
        }
        proof fn test(x: &bool, y: &bool) {
            assert(*select(true, x, y) == *x);
            assert(*(if true { x } else { y }) == *x);
        }
    }",
        "test",
        2,
    );
    assertion_failed(
        "shared_reference_expression_false",
        "verus! {
        pub open spec fn select<'a>(b: bool, x: &'a bool, y: &'a bool) -> &'a bool {
            if b { x } else { y }
        }
        proof fn test(x: &bool, y: &bool) { assert(*select(true, x, y) != *x); }
    }",
    );
    assertion_failed(
        "shared_reference_conditional_false",
        "verus! {
        proof fn test(x: &bool, y: &bool) { assert(*(if false { x } else { y }) != *y); }
    }",
    );
}

#[test]
fn sibling_identity_visibility_and_conflicting_directives_are_checked() {
    rejected(
        "autospec_reexport_is_not_sibling",
        "verus! {
        mod inner { pub open spec fn target() -> bool { true } }
        use inner::target;
        #[verifier::when_used_as_spec(target)] fn source() -> bool { false }
    }",
        "cannot find function referred to in when_used_as_spec",
    );
    rejected(
        "autospec_visibility",
        "verus! {
        spec fn target() -> bool { true }
        #[verifier::when_used_as_spec(target)] pub fn source() -> bool { false }
    }",
        "more private",
    );
    rejected("autospec_conflict", "verus! {
        spec fn target() -> bool { true }
        #[verifier::allow_in_spec] #[verifier::when_used_as_spec(target)] fn source() -> bool { false }
    }", "both 'when_used_as_spec' and 'allow_in_spec'");
}

#[test]
fn trait_and_mutable_interface_boundaries_do_not_gain_permissions() {
    for (name, source, args) in [
        ("trait", "verus! { trait T { spec fn target() -> bool; #[verifier::when_used_as_spec(target)] fn source() -> bool; } }", &[][..]),
        ("mutable", "verus! { spec fn target(x: &mut bool) -> bool { true } #[verifier::when_used_as_spec(target)] fn source(x: &mut bool) -> bool { true } }", &["-V", "new-mut-ref"][..]),
    ] {
        let result = common::run(&format!("autospec_{name}_boundary"), source, args);
        if name == "trait" {
            assert_eq!(result.outcome(), "refused", "{result:?}");
        } else {
            assert!(matches!(result.outcome().as_str(), "refused" | "verus-rejected"), "{result:?}");
            assert!(!result.errors().is_empty(), "{result:?}");
        }
        assert!(result.record["functions"].as_array().unwrap().iter().all(|function| function["verdict"] != "verified"), "{result:?}");
    }
}

#[test]
fn generated_constant_proxy_names_do_not_create_logical_function_aliases() {
    for (name, declaration) in [
        ("spec", "spec const VALUE: bool = true;"),
        ("dual", "const VALUE: bool = true;"),
    ] {
        let source = format!(
            "verus! {{ {declaration}
            #[verifier::when_used_as_spec(VERUS_UNERASED_PROXY__VALUE)]
            fn actual() -> bool {{ false }}
            proof fn test() {{ assert(actual()); }}
        }}"
        );
        // A40 stores these genuine constant proxies at canonical name VALUE.
        // The prefixed native implementation name is not another logical
        // function. The old selection would have used VALUE's true body here.
        rejected(
            &format!("autospec_generated_constant_proxy_{name}"),
            &source,
            "cannot find function referred to in when_used_as_spec",
        );
    }
}

#[test]
fn an_ordinary_function_with_a_proxy_like_spelling_keeps_its_own_identity() {
    checked(
        "autospec_ordinary_prefix",
        "verus! {
        pub open spec fn VERUS_UNERASED_PROXY__VALUE() -> bool { true }
        #[verifier::when_used_as_spec(VERUS_UNERASED_PROXY__VALUE)]
        fn actual() -> bool { false }
        proof fn test() { assert(actual()); }
    }",
        "test",
        1,
    );
    assertion_failed(
        "autospec_ordinary_prefix_false",
        "verus! {
        pub open spec fn VERUS_UNERASED_PROXY__VALUE() -> bool { false }
        #[verifier::when_used_as_spec(VERUS_UNERASED_PROXY__VALUE)]
        fn actual() -> bool { true }
        proof fn test() { assert(actual()); }
    }",
    );
}

#[test]
fn authenticated_const_function_sources_keep_exec_and_ghost_calls_distinct() {
    checked(
        "autospec_const_function_source",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        const fn actual(x: bool) -> (r: bool) ensures r == x { x }
        fn test() {
            let actual_value = actual(true);
            assert(actual_value);
            assert(!actual(true));
        }
    }",
        "test",
        2,
    );
    assertion_failed(
        "autospec_const_function_exec_false",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        const fn actual(x: bool) -> (r: bool) ensures r == x { x }
        fn test() { let result = actual(true); assert(!result); }
    }",
    );
    assertion_failed(
        "autospec_const_function_ghost_false",
        "verus! {
        pub open spec fn logical(x: bool) -> bool { !x }
        #[verifier::when_used_as_spec(logical)]
        const fn actual(x: bool) -> (r: bool) ensures r == x { x }
        proof fn test() { assert(actual(true)); }
    }",
    );
}

#[test]
fn const_function_sources_use_their_actual_namespace_and_native_identity() {
    checked(
        "autospec_const_function_namespaces",
        "verus! {
        mod a {
            pub open spec fn logical() -> bool { true }
            #[verifier::when_used_as_spec(logical)]
            pub const fn actual() -> bool { false }
        }
        mod b {
            pub open spec fn logical() -> bool { false }
            #[verifier::when_used_as_spec(logical)]
            pub const fn actual() -> bool { true }
        }
        proof fn test() { assert(a::actual()); assert(!b::actual()); }
    }",
        "test",
        2,
    );
    assertion_failed(
        "autospec_const_function_namespace_false",
        "verus! {
        mod a {
            pub open spec fn logical() -> bool { true }
            #[verifier::when_used_as_spec(logical)]
            pub const fn actual() -> bool { false }
        }
        mod b {
            pub open spec fn logical() -> bool { false }
            #[verifier::when_used_as_spec(logical)]
            pub const fn actual() -> bool { true }
        }
        proof fn test() { assert(b::actual()); }
    }",
    );
    checked(
        "autospec_const_function_proxy_looking_source",
        "verus! {
        pub open spec fn logical() -> bool { true }
        #[verifier::when_used_as_spec(logical)]
        const fn VERUS_UNERASED_PROXY__actual() -> bool { false }
        proof fn test() { assert(VERUS_UNERASED_PROXY__actual()); }
    }",
        "test",
        1,
    );
    rejected(
        "autospec_const_function_reexport_target",
        "verus! {
        mod inner { pub open spec fn logical() -> bool { true } }
        use inner::logical;
        #[verifier::when_used_as_spec(logical)] const fn actual() -> bool { false }
    }",
        "cannot find function referred to in when_used_as_spec",
    );
    rejected(
        "autospec_const_function_wrong_result",
        "verus! {
        spec fn logical() -> bool { true }
        #[verifier::when_used_as_spec(logical)] const fn actual() -> u8 { 1 }
    }",
        "same return type",
    );
}

#[test]
fn const_function_source_support_does_not_admit_value_proxy_targets_or_forged_sources() {
    for (name, declaration) in [
        ("exec_const", "exec const VALUE: bool = true;"),
        ("static", "exec static VALUE: bool = true;"),
    ] {
        let source = format!(
            "verus! {{ {declaration}
            #[verifier::when_used_as_spec(VERUS_UNERASED_PROXY__VALUE)]
            const fn actual() -> bool {{ false }}
            proof fn test() {{ assert(actual()); }}
        }}"
        );
        rejected(
            &format!("autospec_const_function_value_proxy_target_{name}"),
            &source,
            "cannot find function referred to in when_used_as_spec",
        );
    }
    let result = common::run(
        "autospec_const_function_forged_source",
        "verus! {
        spec fn logical() -> bool { true }
        #[verus::internal(unerased_proxy)]
        #[verifier::when_used_as_spec(logical)]
        fn VERUS_UNERASED_PROXY__actual() -> bool { false }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "refused", "{result:?}");
    let forged = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "VERUS_UNERASED_PROXY__actual")
        .unwrap();
    assert_eq!(forged["verdict"], "skipped", "{result:?}");
    assert_eq!(forged["tag"], "crate-refused", "{result:?}");
    assert!(forged["sites_proved"].is_null(), "{result:?}");
    assert!(forged["sites_failed"].is_null(), "{result:?}");
    assert_eq!(result.exit, 1, "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .iter()
            .any(|refusal| refusal == "trust-vc refused: attribute: verus::internal(unerased_proxy)"),
        "{result:?}"
    );
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"
                && function["sites_proved"].is_null()
                && function["sites_failed"].is_null()),
        "{result:?}"
    );
}

#[test]
fn copied_const_function_requests_keep_the_canonical_last_request() {
    checked(
        "autospec_const_function_last_valid",
        "verus! {
        pub open spec fn logical() -> bool { true }
        #[verifier::when_used_as_spec(missing)]
        #[verifier::when_used_as_spec(logical)]
        const fn actual() -> bool { false }
        proof fn test() { assert(actual()); }
    }",
        "test",
        1,
    );
    rejected(
        "autospec_const_function_last_invalid",
        "verus! {
        pub open spec fn logical() -> bool { true }
        #[verifier::when_used_as_spec(logical)]
        #[verifier::when_used_as_spec(missing)]
        const fn actual() -> bool { false }
        proof fn test() { assert(actual()); }
    }",
        "cannot find function referred to in when_used_as_spec",
    );
}

#[test]
fn external_requests_without_the_actual_const_function_pair_stay_refused() {
    for (name, source) in [
        (
            "ordinary_external",
            "verus! {
            spec fn logical() -> bool { true }
            #[verifier::external]
            #[verifier::when_used_as_spec(logical)]
            fn actual() -> bool { false }
            proof fn test() { assert(actual()); }
        }",
        ),
        (
            "forged_native_pair",
            "verus! {
            spec fn logical() -> bool { true }
            #[verus::internal(unerased_proxy)]
            fn VERUS_UNERASED_PROXY__actual() -> bool { false }
            #[verifier::external]
            #[verus::internal(uses_unerased_proxy)]
            #[verifier::when_used_as_spec(logical)]
            const fn actual() -> bool { false }
            proof fn test() { assert(actual()); }
        }",
        ),
    ] {
        let result = common::run(&format!("autospec_unowned_external_{name}"), source, &[]);
        if name == "ordinary_external" {
            assert_eq!(result.exit, 1, "{result:?}");
            assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
            let errors = result.errors();
            assert_eq!(errors.len(), 1, "{result:?}");
            assert_eq!(errors[0].code, None, "{result:?}");
            assert!(errors[0].message.contains("cannot use function"), "{result:?}");
            assert!(
                errors[0].message.contains(
                    "which is ignored because it is either declared outside the verus! macro or it is marked as `external`."
                ),
                "{result:?}"
            );
            assert!(
                result.record["functions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|function| function["sites_proved"].as_u64().unwrap_or(0) == 0),
                "{result:?}"
            );
        } else {
            assert_eq!(result.outcome(), "refused", "{result:?}");
            assert!(
                result.record["crate_refusals"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|refusal| {
                        refusal
                            .as_str()
                            .is_some_and(|text| text.contains("on an external item"))
                    }),
                "{result:?}"
            );
        }
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}
