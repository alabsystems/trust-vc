// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::encoder::VerifyResult;
use std::fs;
use std::path::PathBuf;

fn write_fixture(name: &str, code: &str) -> PathBuf {
    let dir = PathBuf::from("target/test_spec_function_catalog");
    fs::create_dir_all(&dir).expect("create source catalog fixture dir");
    let path = dir.join(name);
    fs::write(&path, code).expect("write source catalog fixture");
    path
}

/// Verified straight-line body asserts are forwarded as assumptions to the
/// postcondition (Verus verifies postconditions last, carrying forward proven
/// straight-line facts). Regression for the assumption-forwarding fix (#2778).
///
/// A provable witness assert (`x >= 5`) is forwarded so the existential
/// postcondition `exists |n| n + 0 == x && n >= 5` (witness `n = x`) discharges.
/// Pre-fix the postcondition was checked before — and without — the assert and
/// spuriously failed as a Counterexample.
#[test]
fn verified_body_assert_forwarded_to_existential_postcondition() {
    let provable = r#"
        #[trust_vc::ensures(exists(|n: int| #[trigger] n + 0 == x && n >= 5))]
        #[trust_vc::requires(x >= 5)]
        fn provable(x: int) {
            trust_vc::assert!(x >= 5);
        }
    "#;
    let path = write_fixture("forward_provable_witness.rs", provable);
    let result = crate::verify_function_from_file(path.to_str().unwrap(), "provable")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "verified body assert must be forwarded to discharge the dependent \
         existential postcondition, got {result:?}"
    );
}

/// SOUNDNESS: constructive equality-witness discharge must still prove the
/// complete instantiated body. The equality fixes `n := x`, but `x == 4` does
/// not satisfy `n >= 5`, so the existential is genuinely false.
#[test]
fn equality_witness_existential_rejects_false_instantiated_body() {
    let false_witness = r#"
        #[trust_vc::ensures(exists(|n: int| #[trigger] n + 0 == x && n >= 5))]
        #[trust_vc::requires(x == 4)]
        fn target(x: int) {}
    "#;
    let path = write_fixture("equality_witness_false_body.rs", false_witness);
    let result = crate::verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an equality candidate that fails the rest of the existential body must \
         remain a counterexample, got {result:?}"
    );
}

/// SOUNDNESS: a branch-local assert that is FALSE under its own guard must still
/// fail closed. trust-vc now checks a branch-local body assert under the branch
/// path condition (`guard ==> assert`, Verus-faithful; #2779), so a fact that the
/// guard does NOT establish — here `x > 5` does not imply `x > 10` (witness
/// `x = 6`) — remains a Counterexample, and the guarded (still unconditionally
/// true) form is the only thing ever forwarded. Part of #2778 / #2779.
#[test]
fn branch_local_assert_false_under_guard_fails_closed() {
    let branchy = r#"
        #[trust_vc::ensures(true)]
        fn branchy(x: int) {
            if x > 5 {
                trust_vc::assert!(x > 10);
            }
        }
    "#;
    let path = write_fixture("forward_branchy.rs", branchy);
    let result = crate::verify_function_from_file(path.to_str().unwrap(), "branchy")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "assert false under its own guard must fail closed (soundness), got {result:?}"
    );
}

/// Companion to the soundness guard: a branch-local assert that IS implied by its
/// guard verifies under the branch path condition (`x > 5 ==> x > 3`), matching
/// Verus, which checks each assert under its path condition. Part of #2779.
#[test]
fn branch_local_assert_true_under_guard_verifies() {
    let branchy = r#"
        #[trust_vc::ensures(true)]
        fn branchy(x: int) {
            if x > 5 {
                trust_vc::assert!(x > 3);
            }
        }
    "#;
    let path = write_fixture("forward_branchy_true.rs", branchy);
    let result = crate::verify_function_from_file(path.to_str().unwrap(), "branchy")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "assert implied by its guard must verify under the path condition, got {result:?}"
    );
}

/// SOUNDNESS: forwarding a true body assert must not mask a genuinely-false
/// postcondition. Part of #2778.
#[test]
fn forwarded_true_assert_does_not_mask_false_postcondition() {
    let false_post = r#"
        #[trust_vc::ensures(x > 100)]
        #[trust_vc::requires(x >= 0)]
        fn false_post(x: int) {
            trust_vc::assert!(x >= 0);
        }
    "#;
    let path = write_fixture("forward_false_post.rs", false_post);
    let result = crate::verify_function_from_file(path.to_str().unwrap(), "false_post")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must still fail even with a true preceding assert \
         (soundness), got {result:?}"
    );
}

#[test]
fn source_catalog_registers_trust_vc_spec_helper_and_body_axiom() {
    let code = r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[ensures(result == double(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "concrete_a").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed.contains_key("double"),
        "contract-referenced spec function should be registered as a typed helper"
    );
    let axiom = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name() == "__body_axiom_double_source_catalog")
        .expect("contract-referenced spec function should add a body axiom");
    assert!(matches!(
        axiom.kind,
        crate::vc::ObligationKind::BroadcastAssume
    ));
    assert!(
        axiom.condition.contains("double(__trust_vc_spec_double_x)")
            && axiom
                .condition
                .contains("__trust_vc_spec_double_x + __trust_vc_spec_double_x"),
        "body axiom should use the source definition with alpha-renamed params: {}",
        axiom.condition
    );
    assert!(
        axiom
            .condition
            .contains(crate::ir_lowering::SOURCE_CATALOG_MATH_INT_MARKER),
        "math-int result axioms should carry the internal lowering marker: {}",
        axiom.condition
    );
    assert!(
        axiom.source_catalog_math_int_context,
        "the exact source-catalog math-int body axiom should carry authenticated provenance"
    );
}

#[test]
fn source_catalog_math_int_context_is_bound_to_math_int_result_axiom_only() {
    let code = r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[trust_vc::spec]
        fn nonnegative(x: int) -> bool {
            x >= 0
        }

        #[ensures(result == double(x))]
        #[ensures(nonnegative(result))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "concrete_a").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let math_int_axiom = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name() == "__body_axiom_double_source_catalog")
        .expect("math-int source spec should add a body axiom");
    let bool_axiom = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name() == "__body_axiom_nonnegative_source_catalog")
        .expect("bool source spec should add a body axiom");

    assert!(math_int_axiom.source_catalog_math_int_context);
    assert!(math_int_axiom
        .condition
        .contains(crate::ir_lowering::SOURCE_CATALOG_MATH_INT_MARKER));
    assert!(!bool_axiom.source_catalog_math_int_context);
    assert!(!bool_axiom
        .condition
        .contains(crate::ir_lowering::SOURCE_CATALOG_MATH_INT_MARKER));
}

#[test]
fn source_catalog_trust_vc_spec_definition_verifies_contract() {
    let path = write_fixture(
        "trust_vc_spec_definition_verifies.rs",
        r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[ensures(result == double(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "double(x)=x+x should verify the matching ensures, got {result:?}"
    );
}

#[test]
fn source_catalog_unit_spec_definition_verifies_contract() {
    let path = write_fixture(
        "unit_spec_definition_verifies.rs",
        r#"
        #[trust_vc::spec]
        fn unit_spec() -> () {
            ()
        }

        #[ensures(result == unit_spec())]
        fn concrete_unit() -> () {
            ()
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_unit")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit-returning spec function should verify, got {result:?}"
    );
}

#[test]
fn block_use_alias_to_nested_function_registers_helper_type() {
    let path = write_fixture(
        "nested_use_alias_verifies.rs",
        r#"
        mod m {
            #[trust_vc::spec]
            #[trust_vc::ensures(result)]
            pub fn test() -> bool {
                true
            }
        }

        #[trust_vc::proof]
        #[trust_vc::ensures(result)]
        fn test_use_item() -> bool {
            use m::test as test2;

            let result: bool = test2();
            trust_vc::assert!(result);
            result
        }
    "#,
    );
    let source = fs::read_to_string(&path).expect("read nested use alias fixture");
    let file = parse_file(&source).expect("nested use alias fixture should parse");
    let func = find_function(&file, "test_use_item").expect("target function should exist");

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("nested use alias should extract");
    assert!(
        vc.helper_functions_typed.contains_key("test2"),
        "block use alias should register the exposed alias in helper_functions_typed"
    );
    crate::prepared_context::prepare_context(&vc)
        .expect("aliased nested helper return type should lower through TypeEnv");

    let result = verify_function_from_file(path.to_str().unwrap(), "test_use_item")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "aliased nested function returning true should verify, got {result:?}"
    );
}

#[test]
fn block_use_alias_reveal_opens_only_the_canonical_spec_body() {
    let path = write_fixture(
        "nested_use_alias_reveal_verifies.rs",
        r#"
        mod m {
            #[trust_vc::spec]
            #[trust_vc::opaque]
            pub fn test() -> bool {
                true
            }
        }

        #[trust_vc::proof]
        #[trust_vc::ensures(result)]
        fn target() -> bool {
            use m::test as test2;
            reveal!(test2);
            test2()
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "revealing an exact alias should reveal its canonical spec body, got {result:?}"
    );
}

#[test]
fn block_use_alias_scoped_reveal_opens_canonical_body_only_in_assert_by() {
    let path = write_fixture(
        "nested_use_alias_scoped_reveal_verifies.rs",
        r#"
        mod m {
            #[trust_vc::spec]
            #[trust_vc::opaque]
            pub fn test() -> bool {
                true
            }
        }

        #[trust_vc::proof]
        fn target() {
            use m::test as test2;
            trust_vc::assert_by!(test2(), {
                trust_vc::reveal!(test2);
            });
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a scoped reveal through an exact alias should expose the canonical body only in the by-block, got {result:?}"
    );
}

#[test]
fn block_use_alias_shadowing_fails_closed() {
    let path = write_fixture(
        "nested_use_alias_shadowing_fails_closed.rs",
        r#"
        mod good {
            #[trust_vc::ensures(result)]
            pub fn helper() -> bool {
                true
            }
        }

        mod bad {
            #[trust_vc::ensures(!result)]
            pub fn helper() -> bool {
                false
            }
        }

        #[trust_vc::ensures(result)]
        fn target() -> bool {
            use good::helper as h;

            {
                use bad::helper as h;
                let result: bool = h();
                trust_vc::assert!(result);
                result
            }
        }
    "#,
    );
    let source = fs::read_to_string(&path).expect("read shadowing use alias fixture");
    let file = parse_file(&source).expect("shadowing use alias fixture should parse");
    let func = find_function(&file, "target").expect("target function should exist");

    let extraction = extract_verification_conditions_with_file_context(&file, func);
    assert!(
        extraction.is_err(),
        "nested alias shadowing must fail closed until aliases carry lexical scope"
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "shadowed alias to false helper must not verify, got {result:?}"
    );
}

#[test]
fn block_use_alias_shadowed_by_local_binding_fails_closed() {
    let path = write_fixture(
        "nested_use_alias_local_shadow_fails_closed.rs",
        r#"
        mod m {
            #[trust_vc::spec]
            pub fn test() -> bool {
                true
            }
        }

        #[trust_vc::ensures(result)]
        fn target() -> bool {
            use m::test as test2;
            let test2 = || false;
            test2()
        }
    "#,
    );
    let source = fs::read_to_string(&path).expect("read local-shadow alias fixture");
    let file = parse_file(&source).expect("local-shadow alias fixture should parse");
    let func = find_function(&file, "target").expect("target function should exist");

    let extraction = extract_verification_conditions_with_file_context(&file, func);
    assert!(
        extraction.is_err(),
        "a local binding that shadows an alias must fail closed until names carry lexical scope"
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "a false local closure must not inherit the shadowed spec alias body, got {result:?}"
    );
}

#[test]
fn source_catalog_distinguishes_plus_one_definition() {
    let path = write_fixture(
        "trust_vc_spec_definition_plus_one.rs",
        r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x + 1
        }

        #[ensures(result == double(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "double(x)=x+x+1 must not verify an x+x implementation"
    );
}

#[test]
fn source_catalog_normalized_open_spec_definition_verifies_contract() {
    let path = write_fixture(
        "open_spec_definition_verifies.rs",
        r#"
        pub open spec fn double(x: int) -> (z: int) {
            x + x
        }

        #[ensures(result == double(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "normalized open spec double(x)=x+x should verify, got {result:?}"
    );
}

#[test]
fn source_catalog_open_spec_u16_body_uses_math_int_arithmetic() {
    let path = write_fixture(
        "open_spec_u16_math_int.rs",
        r#"
        pub open spec fn double(x: u16) -> (z: int) {
            x + x
        }

        #[requires(x == 40000u16)]
        #[ensures(double(x) > 65535)]
        fn concrete_a(x: u16) -> u16 {
            x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "u16 spec arithmetic should be mathematical, not wrapping, got {result:?}"
    );
}

#[test]
fn source_catalog_rejects_authored_math_int_marker_tampering() {
    let path = write_fixture(
        "authored_math_int_marker.rs",
        r#"
        pub open spec fn forged(x: u16) -> (z: int) {
            __trust_vc_math_int_expr(x + x)
        }

        #[ensures(forged(x) >= 0)]
        fn concrete_a(x: u16) -> u16 { x }
    "#,
    );

    let err = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect_err("authored source-catalog marker use must be rejected");
    assert!(err.to_string().contains("reserved internal marker"));
}

#[test]
fn ordinary_contract_cannot_forge_math_int_marker_capability() {
    let path = write_fixture(
        "contract_math_int_marker.rs",
        r#"
        #[ensures(__trust_vc_math_int_expr(x + x) >= 0)]
        fn concrete_a(x: u16) -> u16 { x }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification orchestration should run");
    let VerifyResult::Error { message } = result else {
        panic!("ordinary conditions must fail closed before solver submission, got {result:?}");
    };
    assert!(message.contains("reserved source-catalog math-int marker"));
}

#[test]
fn source_catalog_registers_spec_called_from_requires() {
    let path = write_fixture(
        "spec_called_from_requires.rs",
        r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[requires(double(x) == x + x)]
        #[ensures(result == x + x)]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "spec functions referenced only from requires should still be typed"
    );
}

#[test]
fn source_catalog_registers_spec_called_from_standalone_recommends() {
    let source = r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[recommends(double(x) == x + x)]
        fn target(x: int) {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        vc.helper_functions_typed.contains_key("double"),
        "spec functions referenced only from standalone recommends should still be typed"
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_double_source_catalog"),
        "standalone recommends should trigger the source spec body axiom"
    );
    let recommendation = vc
        .obligations
        .iter()
        .find(|obligation| obligation.kind == crate::vc::ObligationKind::Recommends)
        .expect("standalone recommends should produce a recommends obligation");
    assert!(
        recommendation.condition.contains("double (x)"),
        "recommendation should preserve the source condition, got {}",
        recommendation.condition
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("spec reference in standalone recommends should lower");
}

#[test]
fn source_catalog_stores_spec_recommends_separately_from_body_axiom() {
    let source = r#"
        spec fn foo(i: int) -> bool
            recommends 0 <= i < 5,
        {
            i + 3 == 20
        }

        spec fn bar(i: int) -> bool
            recommends false
        {
            true
        }

        #[trust_vc::spec]
        #[trust_vc::recommends(i > 0)]
        fn baz(i: int) -> bool {
            i > 0
        }

        #[ensures(foo(i))]
        fn target(i: int) {}
    "#;
    let normalized = crate::spec_function_catalog::normalize_open_spec_source(source);
    let file = syn::parse_file(&normalized).expect("normalized spec recommends should parse");
    let catalog = crate::spec_function_catalog::SpecFunctionCatalog::from_file(&file);
    let recommends = catalog
        .recommends_for("foo")
        .expect("source spec recommends metadata should be stored");
    assert_eq!(recommends.len(), 1);
    assert_eq!(recommends[0], "0 <= i < 5");
    let bar_recommends = catalog
        .recommends_for("bar")
        .expect("source spec recommends without trailing comma should be stored");
    assert_eq!(bar_recommends.len(), 1);
    assert_eq!(bar_recommends[0], "false");
    let baz_recommends = catalog
        .recommends_for("baz")
        .expect("source spec recommends attributes should be stored");
    assert_eq!(baz_recommends.len(), 1);
    assert_eq!(baz_recommends[0], "i > 0");

    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let axiom = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name() == "__body_axiom_foo_source_catalog")
        .expect("contract-referenced source spec should add a body axiom");
    assert!(
        axiom
            .condition
            .contains("foo(__trust_vc_spec_foo_i) == { __trust_vc_spec_foo_i + 3 == 20 }"),
        "body axiom should remain an equality to the source body, got {}",
        axiom.condition
    );
    assert!(
        !axiom.condition.contains("recommends") && !axiom.condition.contains("0 <= "),
        "recommends metadata must not be folded into the body axiom: {}",
        axiom.condition
    );
}

#[test]
fn source_spec_recommends_is_advisory_for_target_contract_call() {
    let source = r#"
        spec fn foo(i: int) -> bool
            recommends 0 <= i && i < 5,
        {
            true
        }

        #[ensures(foo(5))]
        fn target() {}
    "#;
    let normalized = crate::spec_function_catalog::normalize_open_spec_source(source);
    let file = syn::parse_file(&normalized).expect("normalized source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    // Recommends is ADVISORY: even though `foo`'s recommends (5 < 5) is violated
    // at the call, no caller-side obligation is emitted (dropped, never
    // propagated to the caller's verdict).
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    // The postcondition `foo(5)` reduces to the true body, so the target
    // verifies — the former counterexample was solely the spurious recommends.
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "advisory source-spec recommends must leave a true-body target contract verified, got {result:?}"
    );
}

#[test]
fn source_spec_recommends_is_advisory_for_crate_qualified_target_contract_call() {
    let source = r#"
        spec fn foo(i: int) -> bool
            recommends 0 <= i && i < 5,
        {
            true
        }

        #[ensures(crate::foo(5))]
        fn target() {}
    "#;
    let normalized = crate::spec_function_catalog::normalize_open_spec_source(source);
    let file = syn::parse_file(&normalized).expect("normalized source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed.contains_key("crate::foo"),
        "crate-qualified source-spec calls should register the qualified function symbol"
    );
    // Recommends is ADVISORY: no caller-side obligation is emitted even though
    // the crate-qualified callee's recommends (5 < 5) is violated.
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    // The residual counterexample here is from the POSTCONDITION, not recommends:
    // the `crate::`-qualified spec body is not interpreted (unlike plain `foo` and
    // module-qualified `helpers::foo`, which verify), so `crate::foo(5)` stays
    // uninterpreted. That crate-qualified body-interpretation gap is orthogonal to
    // recommends; dropping the advisory recommends does not mask it.
    let result = vc.verify();
    match result {
        VerifyResult::Counterexample { obligation_name, .. } => assert_eq!(
            obligation_name, "postcondition",
            "crate-qualified counterexample must come from the uninterpreted postcondition, not recommends"
        ),
        other => panic!(
            "crate-qualified advisory recommends should leave only the uninterpreted-postcondition counterexample, got {other:?}"
        ),
    }
}

#[test]
fn source_spec_recommends_is_advisory_for_module_qualified_target_contract_call() {
    let code = r#"
        mod helpers {
            #[trust_vc::spec]
            #[trust_vc::recommends(0 <= i && i < 5)]
            pub fn foo(i: int) -> bool {
                true
            }
        }

        #[ensures(helpers::foo(5))]
        fn target() {}
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed.contains_key("helpers::foo"),
        "module-qualified source-spec calls should register the full same-file path"
    );
    // Recommends is ADVISORY: no caller-side obligation is emitted even though
    // the module-qualified callee's recommends (5 < 5) is violated.
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "advisory module-qualified source-spec recommends must leave a true-body target verified, got {result:?}"
    );
}

#[test]
fn source_spec_recommends_registers_substituted_associated_trait_fn() {
    let code = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor<T> {
            t: T,
        }

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::spec]
        #[trust_vc::recommends(match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
            Some(_x) => true,
            None => false,
        })]
        fn guarded(s: Seq<u8>) -> bool {
            true
        }

        #[trust_vc::ensures(guarded(s))]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    // Recommends is ADVISORY: no caller-side recommends obligation is emitted.
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    // The associated trait helper referenced by the (advisory) recommends is
    // still REGISTERED so the extractor's spec surface stays complete — dropping
    // the obligation must not drop the callee spec-surface declarations.
    let trait_fn_helpers = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .collect::<Vec<_>>();
    assert_eq!(
        trait_fn_helpers.len(),
        1,
        "substituted source-spec recommends should register its associated trait helper, got {trait_fn_helpers:?}"
    );
    let (return_ty, params, _) = vc
        .helper_functions_typed
        .get(trait_fn_helpers[0].0)
        .expect("associated trait helper should be typed");
    assert_eq!(*return_ty, TrustVcType::parse_or_opaque("Option<u8>"));
    assert_eq!(
        params,
        &vec![(
            "s".to_string(),
            TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
        )]
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("propagated recommends associated trait helper should lower");
}

#[test]
fn source_spec_recommends_rejects_unresolved_associated_trait_fn() {
    let code = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor<T> {
            t: T,
        }

        #[trust_vc::spec]
        #[trust_vc::recommends(match <RecommendsImplementor<u8> as MissingTr<u8>>::trait_fn(s) {
            Some(_x) => true,
            None => false,
        })]
        fn guarded(s: Seq<u8>) -> bool {
            true
        }

        #[trust_vc::ensures(guarded(s))]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).expect_err(
        "unresolved associated trait helper in propagated recommends should fail closed",
    );
    let message = err.to_string();
    assert!(
        message.contains("Could not resolve associated trait function")
            && message.contains("source spec recommends"),
        "unresolved associated trait helper should explain the source-spec recommends failure, got {message}"
    );
}

#[test]
fn source_spec_recommends_resolves_module_qualified_trait_path() {
    let code = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor;

        mod a {
            use trust_vc_types::Seq;

            pub trait Tr {
                fn trait_fn(s: Seq<u8>) -> Option<u8>;
            }
        }

        mod b {
            use trust_vc_types::Seq;

            pub trait Tr {
                fn trait_fn(s: Seq<u8>) -> bool;
            }
        }

        #[trust_vc::spec]
        #[trust_vc::recommends(<RecommendsImplementor as b::Tr>::trait_fn(s))]
        fn guarded(s: Seq<u8>) -> bool {
            true
        }

        #[trust_vc::ensures(guarded(s))]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let trait_fn_helpers = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .collect::<Vec<_>>();
    assert_eq!(
        trait_fn_helpers.len(),
        1,
        "module-qualified trait path should register one helper, got {trait_fn_helpers:?}"
    );
    let (return_ty, _, _) = vc
        .helper_functions_typed
        .get(trait_fn_helpers[0].0)
        .expect("associated trait helper should be typed");
    assert_eq!(
        *return_ty,
        TrustVcType::Bool,
        "b::Tr::trait_fn should not be typed using same-bare-name a::Tr"
    );
}

#[test]
fn source_spec_recommends_registers_associated_trait_fn_introduced_by_substitution() {
    let code = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor;

        trait RecommendsTr {
            fn trait_fn(s: Seq<u8>) -> bool;
        }

        #[trust_vc::spec]
        #[trust_vc::recommends(flag)]
        fn guarded(flag: bool) -> bool {
            true
        }

        #[trust_vc::ensures(guarded(<RecommendsImplementor as RecommendsTr>::trait_fn(s)))]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed
            .iter()
            .any(|(name, (return_ty, _, _))| {
                name.contains("trait_fn") && *return_ty == TrustVcType::Bool
            }),
        "associated trait helper introduced only through call-argument substitution should be typed"
    );
}

#[test]
fn source_spec_recommends_rejects_associated_helper_signature_collision() {
    let associated_expr: syn::Expr =
        syn::parse_str("<RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s)")
            .expect("associated expression should parse");
    let syn::Expr::Call(call) = associated_expr else {
        panic!("associated expression should parse as a call")
    };
    let syn::Expr::Path(path) = *call.func else {
        panic!("associated call target should parse as a path")
    };
    let helper_name = expr_path_to_string(&path);
    let code = format!(
        r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor<T> {{
            t: T,
        }}

        trait RecommendsTr<Key> {{
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }}

        #[trust_vc::spec]
        fn {helper_name}(s: Seq<u8>) -> bool {{
            true
        }}

        #[trust_vc::spec]
        #[trust_vc::recommends(match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {{
            Some(_x) => true,
            None => false,
        }})]
        fn guarded(s: Seq<u8>) -> bool {{
            true
        }}

        #[trust_vc::ensures({helper_name}(s))]
        #[trust_vc::ensures(guarded(s))]
        fn target(s: Seq<u8>) {{}}
    "#
    );
    let file = syn::parse_file(&code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).expect_err(
        "existing helper with conflicting generated associated-helper name should fail closed",
    );
    let message = err.to_string();
    assert!(
        message.contains("conflicts with an existing helper signature"),
        "helper signature collision should fail closed, got {message}"
    );
}

#[test]
fn source_spec_recommends_body_call_scoped_local_argument_is_advisory() {
    let code = r#"
        #[trust_vc::spec]
        #[trust_vc::recommends(i < 5u64)]
        fn limited(i: u64) -> u64 {
            i
        }

        #[trust_vc::ensures(true)]
        fn target(x: u64) {
            let x: u64 = 10u64;
            limited(x);
        }
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    // Recommends is ADVISORY: the body call to `limited` violates its recommends
    // (10 < 5) but emits no caller-side obligation.
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "advisory body-call recommends must leave the true-body target verified, got {result:?}"
    );
}

#[test]
fn source_spec_recommends_body_call_inside_compute_only_macro_is_advisory() {
    let code = r#"
        #[trust_vc::spec]
        #[trust_vc::recommends(i < 5u64)]
        fn limited(i: u64) -> u64 {
            i
        }

        #[trust_vc::ensures(true)]
        fn target() {
            trust_vc::assert_by_compute!(limited(10u64) == 10u64; compute_only);
        }
    "#;
    let file = syn::parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    // Recommends is ADVISORY: the compute-only macro body call to `limited`
    // violates its recommends (10 < 5) but emits no caller-side obligation.
    assert!(
        vc.obligations
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "advisory recommends must not emit a caller-side obligation"
    );

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "advisory recommends inside assert_by_compute!(...; compute_only) must leave the target verified, got {result:?}"
    );
}

#[test]
fn source_catalog_registers_associated_trait_fn_return_type() {
    let source = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor<T> {
            t: T,
        }

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::contract(
            ensures(match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
                Some(_x) => true,
                None => false,
            })
        )]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let trait_fn_helpers = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .collect::<Vec<_>>();
    assert_eq!(
        trait_fn_helpers.len(),
        1,
        "associated trait function should be registered once, got {trait_fn_helpers:?}"
    );
    assert!(
        trait_fn_helpers[0].0.starts_with("__qualified_")
            && trait_fn_helpers[0].0.contains("_sha256_"),
        "qualified helper name should include collision-resistant path hash: {}",
        trait_fn_helpers[0].0
    );
    let (return_ty, params, _) = vc
        .helper_functions_typed
        .get(trait_fn_helpers[0].0)
        .expect("associated trait function should be registered as a typed helper");
    assert_eq!(
        *return_ty,
        TrustVcType::parse_or_opaque("Option<u8>"),
        "trait generic return type should be specialized from RecommendsTr<u8>"
    );
    assert_eq!(
        params,
        &vec![(
            "s".to_string(),
            TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
        )]
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("associated trait function return type should lower through TypeEnv");
}

#[test]
fn source_catalog_registers_associated_trait_fn_from_standalone_recommends() {
    let source = r#"
        use trust_vc_types::Seq;

        struct RecommendsImplementor<T> {
            t: T,
        }

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[recommends(match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
            Some(_x) => true,
            None => false,
        })]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let trait_fn_helpers = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .collect::<Vec<_>>();
    assert_eq!(
        trait_fn_helpers.len(),
        1,
        "associated trait function in standalone recommends should be registered once, got {trait_fn_helpers:?}"
    );
    let (return_ty, params, _) = vc
        .helper_functions_typed
        .get(trait_fn_helpers[0].0)
        .expect("associated trait function should be registered as a typed helper");
    assert_eq!(
        *return_ty,
        TrustVcType::parse_or_opaque("Option<u8>"),
        "trait generic return type should be specialized from RecommendsTr<u8>"
    );
    assert_eq!(
        params,
        &vec![(
            "s".to_string(),
            TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
        )]
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.kind == crate::vc::ObligationKind::Recommends),
        "standalone recommends should produce a recommends obligation"
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("associated trait function in standalone recommends should lower through TypeEnv");
}

#[test]
fn source_catalog_keeps_distinct_associated_trait_fn_specializations() {
    let source = r#"
        use trust_vc_types::Seq;

        struct A;
        struct B;

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::contract(
            ensures(match <A as RecommendsTr<u8>>::trait_fn(s) {
                Some(_x) => true,
                None => false,
            }),
            ensures(match <B as RecommendsTr<u16>>::trait_fn(s) {
                Some(_x) => false,
                None => true,
            })
        )]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let mut trait_fn_return_types = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .map(|(name, (return_ty, _, _))| (name.as_str(), return_ty.clone()))
        .collect::<Vec<_>>();
    trait_fn_return_types.sort_by(|left, right| left.0.cmp(right.0));
    assert_eq!(
        trait_fn_return_types.len(),
        2,
        "expected two distinct qualified associated function helper keys, got {trait_fn_return_types:?}"
    );
    assert!(
        trait_fn_return_types
            .iter()
            .all(|(name, _)| name.starts_with("__qualified_") && name.contains("_sha256_")),
        "associated helper keys must include qualified self type context: {trait_fn_return_types:?}"
    );
    assert!(trait_fn_return_types
        .iter()
        .any(|(_, ty)| *ty == TrustVcType::parse_or_opaque("Option<u8>")));
    assert!(trait_fn_return_types
        .iter()
        .any(|(_, ty)| *ty == TrustVcType::parse_or_opaque("Option<u16>")));
    assert!(
        !vc.helper_functions_typed
            .contains_key("RecommendsTr::trait_fn"),
        "qualified associated calls must not collapse to the bare trait method key"
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("distinct associated trait functions should lower through TypeEnv");
}

#[test]
fn source_catalog_qualified_associated_trait_fn_names_resist_separator_collisions() {
    let source = r#"
        use trust_vc_types::Seq;

        mod a {
            pub struct B;
        }
        struct a_B;

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::contract(
            ensures(match <a::B as RecommendsTr<u8>>::trait_fn(s) {
                Some(_x) => true,
                None => false,
            }),
            ensures(match <a_B as RecommendsTr<u16>>::trait_fn(s) {
                Some(_x) => false,
                None => true,
            })
        )]
        fn target(s: Seq<u8>) {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let trait_fn_helpers = vc
        .helper_functions_typed
        .iter()
        .filter(|(name, _)| name.contains("trait_fn"))
        .collect::<Vec<_>>();
    assert_eq!(
        trait_fn_helpers.len(),
        2,
        "separator/underscore collision candidates must remain distinct: {trait_fn_helpers:?}"
    );
    assert_ne!(
        trait_fn_helpers[0].0, trait_fn_helpers[1].0,
        "qualified helper names must be collision-resistant"
    );
    assert!(
        trait_fn_helpers
            .iter()
            .all(|(name, _)| name.starts_with("__qualified_") && name.contains("_sha256_")),
        "qualified helper names should include path hashes: {trait_fn_helpers:?}"
    );
    assert!(trait_fn_helpers.iter().any(|(_, (return_ty, _, _))| {
        *return_ty == TrustVcType::parse_or_opaque("Option<u8>")
    }));
    assert!(trait_fn_helpers.iter().any(|(_, (return_ty, _, _))| {
        *return_ty == TrustVcType::parse_or_opaque("Option<u16>")
    }));

    crate::prepared_context::prepare_context(&vc)
        .expect("collision-resistant associated helper names should lower through TypeEnv");
}

#[test]
fn source_local_type_alias_lowers_recommends_quantifier_bound_type() {
    let source = r#"
        type Int = int;

        #[trust_vc::contract(
            recommends(forall(|witness: Int| witness == witness)),
            ensures(true),
        )]
        fn target() {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert_eq!(
        vc.source_type_aliases().get("Int"),
        Some(&TrustVcType::MathInt),
        "same-file type aliases should be registered on the verification context"
    );
    let prepared =
        crate::prepared_context::prepare_context(&vc).expect("alias in recommends should lower");

    let recommends = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.kind == crate::vc::ObligationKind::Recommends)
        .expect("contract should produce a recommends obligation");
    match &recommends.expr {
        crate::ir::TrustVcExpr::Quantifier { bound_vars, .. } => {
            assert_eq!(
                bound_vars,
                &vec![("witness".to_string(), TrustVcType::MathInt)]
            );
        }
        other => panic!("expected quantified recommends expression, got {other:?}"),
    }
}

#[test]
fn source_local_type_alias_lowers_nested_associated_trait_quantifier() {
    let source = r#"
        use trust_vc_types::Seq;

        type Int = i32;

        struct RecommendsImplementor<T> {
            t: T,
        }

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::contract(
            ensures(forall(|s: Seq<u8>| {
                match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
                    Some(_x) => forall(|witness: Int| false || witness != witness),
                    None => false,
                }
            })),
        )]
        fn target() {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        vc.helper_functions_typed
            .iter()
            .any(|(name, (return_ty, _, _))| {
                name.contains("trait_fn")
                    && *return_ty == TrustVcType::parse_or_opaque("Option<u8>")
            }),
        "associated trait helper should be registered with substituted return type"
    );

    crate::prepared_context::prepare_context(&vc)
        .expect("nested alias inside associated-trait quantifier surface should lower");
}

#[test]
fn source_catalog_lowers_quantified_recommends_associated_trait_fn_surface() {
    let source = r#"
        use trust_vc_types::Seq;

        type Int = i32;

        struct RecommendsImplementor<T> {
            t: T,
        }

        trait RecommendsTr<Key> {
            fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        #[trust_vc::contract(
            recommends(forall(|s: Seq<u8>| {
                match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
                    Some(_x) => forall(|witness: Int| false || witness != witness),
                    None => false,
                }
            })),
        )]
        fn target() {}
    "#;
    let file = syn::parse_file(source).unwrap();
    let func = find_function(&file, "target").unwrap();

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        vc.helper_functions_typed
            .iter()
            .any(|(name, (return_ty, _, _))| {
                name.contains("trait_fn") && *return_ty == TrustVcType::parse_or_opaque("Option<u8>")
            }),
        "associated trait helper inside quantified recommends should be registered with substituted return type"
    );

    let prepared = crate::prepared_context::prepare_context(&vc)
        .expect("quantified recommends associated-trait surface should lower");
    let recommends = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.kind == crate::vc::ObligationKind::Recommends)
        .expect("contract should produce a recommends obligation");
    match &recommends.expr {
        crate::ir::TrustVcExpr::Quantifier {
            bound_vars, body, ..
        } => {
            assert_eq!(
                bound_vars,
                &vec![(
                    "s".to_string(),
                    TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
                )]
            );
            assert!(
                matches!(body.as_ref(), crate::ir::TrustVcExpr::Match { .. }),
                "quantified recommends body should preserve the associated-trait match surface, got {body:?}"
            );
        }
        other => panic!("expected quantified recommends expression, got {other:?}"),
    }
}

#[test]
fn source_catalog_marks_reference_return_binding_for_deref_contracts() {
    let path = write_fixture(
        "reference_return_result_deref.rs",
        r#"
        #[trust_vc::contract(
            ensures(*result == *x),
            returns(result),
        )]
        fn returns_ref<'a>(x: &'a u64) -> &'a u64 {
            x
        }
    "#,
    );
    let source = fs::read_to_string(&path).expect("read reference return fixture");
    let file = syn::parse_file(&source).expect("reference return fixture should parse");
    let func = find_function(&file, "returns_ref").expect("target function should exist");

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("reference return contract should extract");
    assert!(
        vc.is_erased_shared_ref_var("result"),
        "shared-reference return binding should support deref in postconditions"
    );
    crate::prepared_context::prepare_context(&vc)
        .expect("deref of reference return binding should lower");

    let result = verify_function_from_file(path.to_str().unwrap(), "returns_ref")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "reference return result deref postcondition should verify, got {result:?}"
    );
}

#[test]
fn source_catalog_registers_transitive_spec_dependencies() {
    let path = write_fixture(
        "transitive_spec_dependencies.rs",
        r#"
        #[trust_vc::spec]
        fn double(x: int) -> int {
            x + x
        }

        #[trust_vc::spec]
        fn quad(x: int) -> int {
            double(x) + double(x)
        }

        #[ensures(result == quad(x))]
        fn concrete_a(x: int) -> int {
            x + x + x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "spec bodies that call sibling specs should register those dependencies"
    );
}

/// B5 keystone: a mutually recursive `a -> b -> a` spec-function cycle whose
/// every member carries a `decreases` clause is termination-guarded, so each
/// function is encoded as an uninterpreted helper WITH its defining forall axiom
/// (`forall i. count_down_b(i) == if i == 0 { 0 } else { 1 + count_down_a(..) }`).
/// The catalog must no longer hard-error on the cycle, and the defining axioms
/// must be present so the mutual specs are usable. Mirrors upstream Verus
/// `recursion.rs::mutually_recursive_expressions` (`count_down_b(0) == 0`).
#[test]
fn source_catalog_emits_mutual_recursion_defining_axioms_when_decreases_guards_cycle() {
    let code = r#"
        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_a(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_b(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        #[ensures(count_down_b(0) == 0)]
        fn target() {}
    "#;
    let file = parse_file(code).expect("mutual recursion source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("well-formed mutual recursion must not hard-error on the cycle");

    assert!(
        vc.helper_functions_typed.contains_key("count_down_a")
            && vc.helper_functions_typed.contains_key("count_down_b"),
        "both mutually recursive specs should be registered as typed helpers"
    );
    for member in ["count_down_a", "count_down_b"] {
        let axiom_name = format!("__body_axiom_{member}_source_catalog");
        assert!(
            vc.obligations
                .iter()
                .any(|obligation| obligation.name() == axiom_name),
            "termination-guarded cycle member {member} should emit its defining body axiom"
        );
        assert!(
            vc.source_catalog_admitted_definitions.contains(member),
            "published recursive definition {member} must carry checked source-catalog provenance"
        );
    }
    assert!(vc.source_catalog_termination_failure.is_none());
}

/// SOUNDNESS: the isolated termination query models entry parameters, not
/// arbitrary local scopes. A local binding that shadows the declared measure
/// parameter must therefore fail closed before any recursive body axiom can be
/// published; otherwise the rendered guard/call argument could be mistaken for
/// the entry parameter and admit an unproved recursive definition.
#[test]
fn source_catalog_shadowed_recursive_parameter_fails_closed() {
    let code = r#"
        #[trust_vc::decreases(n)]
        #[trust_vc::spec]
        fn shadowed(n: nat) -> nat {
            let n: int = -1;
            if n == 0 { 0 } else { 1 + shadowed((n - 1) as nat) }
        }

        #[ensures(shadowed(0) == 0)]
        fn target() {}
    "#;
    let file = parse_file(code).expect("shadowing fixture should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let error = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("shadow-ambiguous recursive source must fail closed");
    assert!(
        error.to_string().contains("shadows parameter(s) n"),
        "the rejection should identify the scope ambiguity, got: {error}"
    );
}

/// B5 keystone, end-to-end: the defining axioms emitted for the well-formed
/// mutual cycle make a contract that unfolds one cycle step discharge. This is
/// the upstream `mutually_recursive_expressions` `count_down_b(0) == 0` shape,
/// proven through `verify_function_from_file` (the upstream-grounded path).
#[test]
fn source_catalog_mutual_recursion_defining_axiom_verifies_contract() {
    let path = write_fixture(
        "mutual_recursion_defining_axiom_verifies.rs",
        r#"
        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_a(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_b(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        #[ensures(count_down_b(0) == 0)]
        fn target() {}
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("well-formed mutual recursion should verify, not hard-error");
    assert!(
        matches!(result, VerifyResult::Verified),
        "count_down_b(0) == 0 should discharge via the mutual defining axioms, got {result:?}"
    );
}

/// SOUNDNESS (B5): the defining axioms emitted for the well-formed cycle must be
/// FAITHFUL, not vacuous. A wrong value for the same mutual cycle
/// (`count_down_b(0) == 1`, when it is actually 0) must be a Counterexample — if
/// the axioms entailed `false` this would spuriously verify.
#[test]
fn source_catalog_mutual_recursion_defining_axiom_rejects_wrong_value() {
    let path = write_fixture(
        "mutual_recursion_defining_axiom_wrong_value.rs",
        r#"
        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_a(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_b(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        #[ensures(count_down_b(0) == 1)]
        fn target() {}
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("well-formed mutual recursion should run");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "count_down_b(0) == 1 is false and must be a Counterexample (axioms must be faithful), got {result:?}"
    );
}

/// SOUNDNESS (B5): a mutual `a -> b -> a` cycle whose members carry NO `decreases`
/// clause is ill-formed; its body-equation system is contradictory
/// (`a(n) == b(n) + 1`, `b(n) == a(n) + 1` has no model). We must NOT emit the
/// defining axioms — otherwise a false goal would verify vacuously. The functions
/// stay uninterpreted (fail closed): no body axiom, and a false postcondition must
/// be a Counterexample, not Verified.
#[test]
fn source_catalog_suppresses_mutual_recursion_axioms_without_decreases() {
    let code = r#"
        #[trust_vc::spec]
        fn loop_a(i: int) -> int {
            loop_b(i) + 1
        }

        #[trust_vc::spec]
        fn loop_b(i: int) -> int {
            loop_a(i) + 1
        }

        #[ensures(loop_a(0) == loop_b(0))]
        fn target() {}
    "#;
    let file = parse_file(code).expect("ill-formed mutual recursion source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("ill-formed mutual recursion should extract (uninterpreted), not panic");

    for member in ["loop_a", "loop_b"] {
        assert!(
            vc.helper_functions_typed.contains_key(member),
            "{member} should still be registered as an uninterpreted helper"
        );
        let axiom_name = format!("__body_axiom_{member}_source_catalog");
        assert!(
            !vc.obligations
                .iter()
                .any(|obligation| obligation.name() == axiom_name),
            "undecreasing mutual cycle member {member} must NOT emit a defining axiom (soundness)"
        );
        assert!(
            !vc.source_catalog_admitted_definitions.contains(member),
            "a suppressed recursive definition must not retain admission authority"
        );
    }
    assert!(
        vc.variables()
            .iter()
            .all(|variable| !variable.name.starts_with("__trust_vc_spec_loop_")),
        "suppressing a recursive axiom must also suppress its semantically-dead bound variables"
    );
}

/// SOUNDNESS (B5), end-to-end: the contradictory undecreasing mutual cycle must
/// not let a false postcondition verify. With the body axioms suppressed, the
/// functions are uninterpreted, so `loop_a(0) == loop_b(0)` (which would follow
/// only from the contradictory axioms) is NOT provable — it must fail closed.
#[test]
fn source_catalog_mutual_recursion_without_decreases_fails_closed() {
    let path = write_fixture(
        "mutual_recursion_without_decreases_fails_closed.rs",
        r#"
        #[trust_vc::spec]
        fn loop_a(i: int) -> int {
            loop_b(i) + 1
        }

        #[trust_vc::spec]
        fn loop_b(i: int) -> int {
            loop_a(i) + 1
        }

        #[ensures(loop_a(0) == loop_b(0))]
        fn target() {}
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("ill-formed mutual recursion should extract and run, not hard-error");
    // Both functions stay uninterpreted, so the goal is genuinely unprovable: it
    // must be a definite Counterexample, not Verified and not a masking Unknown.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "undecreasing contradictory mutual cycle must fail closed as a Counterexample, got {result:?}"
    );
}

/// SOUNDNESS (B5): a cycle is fail-closed if EVEN ONE member lacks `decreases`.
/// Here `count_down_a` is guarded but `count_down_b` is not; the partial guard is
/// insufficient, so both members must be left uninterpreted (no defining axiom).
#[test]
fn source_catalog_partial_decreases_on_mutual_cycle_suppresses_all_axioms() {
    let code = r#"
        #[trust_vc::decreases(i)]
        #[trust_vc::spec]
        fn count_down_a(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        #[trust_vc::spec]
        fn count_down_b(i: nat) -> nat {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        #[ensures(count_down_a(0) == count_down_b(0))]
        fn target() {}
    "#;
    let file = parse_file(code).expect("partially guarded mutual recursion source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("partially guarded mutual recursion should extract, not panic");

    // Both must be applied (referenced from the postcondition) yet stay axiom-free.
    for member in ["count_down_a", "count_down_b"] {
        assert!(
            vc.helper_functions_typed.contains_key(member),
            "{member} should be registered as an uninterpreted helper"
        );
        let axiom_name = format!("__body_axiom_{member}_source_catalog");
        assert!(
            !vc.obligations
                .iter()
                .any(|obligation| obligation.name() == axiom_name),
            "a mutual cycle with any undecreasing member must suppress ALL defining axioms; {member} leaked one"
        );
    }
    assert!(
        vc.variables()
            .iter()
            .all(|variable| !variable.name.starts_with("__trust_vc_spec_count_down_")),
        "a suppressed nat body axiom must not leak its bound variable or non-negativity constraint"
    );
}

/// A decrease is well-founded only when the CALLEE measure remains in the
/// non-negative domain. `nat - nat` is `int`-typed, and the cast back to `nat`
/// is partial at `n == 0`; accepting only `(n - 1) < n` would therefore admit
/// this no-base-case recursion and publish its contradictory defining axiom.
#[test]
fn source_catalog_nat_cast_decrease_requires_nonnegative_callee_measure() {
    let code = r#"
        #[trust_vc::spec]
        #[trust_vc::decreases(n)]
        fn no_base(n: nat) -> nat {
            (no_base((n - 1) as nat) + 1) as nat
        }

        #[ensures(no_base(0) == no_base(0))]
        fn target() {}
    "#;
    let file = parse_file(code).expect("nat no-base recursion source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("ill-founded nat recursion should extract as uninterpreted");

    assert!(
        vc.helper_functions_typed.contains_key("no_base"),
        "the recursion-suppressed function should remain an uninterpreted helper"
    );
    assert!(
        !vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_no_base_source_catalog"),
        "a decrease whose callee measure can leave the non-negative domain must not emit an axiom"
    );
    assert!(
        vc.variables()
            .iter()
            .all(|variable| variable.name != "__trust_vc_spec_no_base_n"),
        "the suppressed axiom must not leak its dead nat binder"
    );
}

/// REGRESSION: the cycle gate must not over-fire on non-recursive transitive
/// dependencies. `caller -> mid -> leaf` is a DAG (no cycle), so every function
/// keeps its defining axiom even though none carries `decreases`.
#[test]
fn source_catalog_non_recursive_chain_keeps_all_defining_axioms() {
    let code = r#"
        #[trust_vc::spec]
        fn leaf(x: int) -> int {
            x + 1
        }

        #[trust_vc::spec]
        fn mid(x: int) -> int {
            leaf(x) + 1
        }

        #[trust_vc::spec]
        fn caller(x: int) -> int {
            mid(x) + 1
        }

        #[ensures(true)]
        fn target() {
            let _ = caller(0);
        }
    "#;
    let file = parse_file(code).expect("non-recursive chain source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("non-recursive chain should extract");

    for member in ["leaf", "mid", "caller"] {
        let axiom_name = format!("__body_axiom_{member}_source_catalog");
        assert!(
            vc.obligations
                .iter()
                .any(|obligation| obligation.name() == axiom_name),
            "non-recursive (DAG) dependency {member} must keep its defining axiom"
        );
    }
}

#[test]
fn source_catalog_registers_assert_by_compute_body_spec_reference() {
    let path = write_fixture(
        "assert_by_compute_body_spec_reference.rs",
        r#"
        #[trust_vc::decreases(n)]
        #[trust_vc::spec]
        fn fib_compute(n: u64) -> u64 {
            if n <= 1 {
                n
            } else {
                fib_compute(n - 1) + fib_compute(n - 2)
            }
        }

        #[trust_vc::ensures(true)]
        fn target() {
            trust_vc::assert_by_compute!(fib_compute(6) == 8; compute_only);
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "target")
        .expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "body-referenced source spec functions should be registered before assert_by_compute lowering"
    );
}

#[test]
fn source_catalog_registers_assert_forall_body_only_spec_reference() {
    let code = r#"
        #[trust_vc::spec]
        fn body_helper(k: u32) -> bool {
            k == k
        }

        #[trust_vc::ensures(true)]
        fn target() {
            trust_vc::assert_forall_by!(|k: u32| body_helper(k), {
                trust_vc::assume!(k == k);
            });
        }
    "#;
    let file = parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("assert_forall_by body reference should extract");

    assert!(
        vc.helper_functions_typed.contains_key("body_helper"),
        "source spec used only in assert-forall body should be cataloged"
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_body_helper_source_catalog"),
        "assert-forall body reference should add the source spec body axiom"
    );
}

#[test]
fn source_catalog_registers_assert_forall_trigger_only_spec_reference() {
    let code = r#"
        #[trust_vc::spec]
        fn trigger_helper(k: u32) -> u32 {
            k
        }

        #[trust_vc::ensures(true)]
        fn target() {
            trust_vc::assert_forall_by!(assert forall |k: u32| #![trigger trigger_helper(k)] k == k by {
                trust_vc::assume!(k == k);
            });
        }
    "#;
    let file = parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("assert-forall trigger reference should extract");

    assert!(
        vc.helper_functions_typed.contains_key("trigger_helper"),
        "source spec used only in assert-forall trigger should be cataloged"
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_trigger_helper_source_catalog"),
        "assert-forall trigger reference should add the source spec body axiom"
    );
}

#[test]
fn source_catalog_registers_assert_forall_proof_only_spec_reference() {
    let code = r#"
        #[trust_vc::spec]
        fn proof_helper(k: u32) -> u32 {
            k
        }

        #[trust_vc::ensures(true)]
        fn target() {
            trust_vc::assert_forall_by!(|k: u32| k == k, {
                trust_vc::assert!(proof_helper(k) == k);
            });
        }
    "#;
    let file = parse_file(code).expect("source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("assert-forall proof reference should extract");

    assert!(
        vc.helper_functions_typed.contains_key("proof_helper"),
        "source spec used only in assert-forall proof block should be cataloged"
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_proof_helper_source_catalog"),
        "assert-forall proof reference should add the source spec body axiom"
    );
}

#[test]
fn source_catalog_registers_normalized_bare_assert_forall_spec_reference() {
    let source = r#"
        pub open spec fn bare_helper(k: u32) -> bool {
            k == k
        }

        #[trust_vc::ensures(true)]
        fn target() {
            assert forall |k: u32| bare_helper(k) by {
                trust_vc::assume!(k == k);
            };
        }
    "#;
    let normalized = crate::spec_function_catalog::normalize_open_spec_source(source);
    let file =
        crate::parse_file_allow_tracked(&normalized).expect("normalized bare source should parse");
    let func = find_function(&file, "target").expect("target function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("normalized bare assert-forall reference should extract");

    assert!(
        vc.helper_functions_typed.contains_key("bare_helper"),
        "source spec used only in normalized bare assert forall should be cataloged"
    );
    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.name() == "__body_axiom_bare_helper_source_catalog"),
        "normalized bare assert-forall reference should add the source spec body axiom"
    );
}

#[test]
fn source_catalog_rejects_parameter_shadowing_in_spec_body() {
    let path = write_fixture(
        "parameter_shadowing_rejected.rs",
        r#"
        #[trust_vc::spec]
        fn zero(x: int) -> int {
            let x: int = 0;
            x
        }

        #[ensures(result == zero(x))]
        fn concrete_a(x: int) -> int {
            0
        }
    "#,
    );

    let err = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect_err("scope-unsafe source spec alpha-renaming must fail closed");
    assert!(
        err.to_string().contains("shadows parameter"),
        "error should explain parameter shadowing, got {err}"
    );
}

#[test]
fn source_catalog_keeps_opaque_spec_body_hidden_without_reveal() {
    let path = write_fixture(
        "opaque_spec_hidden.rs",
        r#"
        #[trust_vc::opaque]
        #[trust_vc::spec]
        fn hidden(x: int) -> int {
            x + x
        }

        #[ensures(result == hidden(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("opaque source specs should extract as uninterpreted helpers");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "opaque source specs must not reveal body axioms implicitly, got {result:?}"
    );
}

#[test]
fn source_catalog_reveals_opaque_generic_spec_with_turbofish_target() {
    let path = write_fixture(
        "opaque_generic_spec_revealed.rs",
        r#"
        #[trust_vc::opaque]
        #[trust_vc::spec]
        fn hidden_tagged_successor<T>(_tag: T, x: u64) -> u64 {
            x + 1
        }

        #[ensures(true)]
        fn concrete_a() {
            trust_vc::reveal!(hidden_tagged_successor::<bool>);
            trust_vc::assert!(hidden_tagged_successor::<bool>(true, 4u64) == 5u64);
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("opaque generic source spec reveal should extract");
    assert!(
        matches!(result, VerifyResult::Verified),
        "turbofish reveal target should reveal the opaque generic source spec, got {result:?}"
    );
}

#[test]
fn source_catalog_keeps_opaque_generic_spec_hidden_without_reveal() {
    let path = write_fixture(
        "opaque_generic_spec_hidden.rs",
        r#"
        #[trust_vc::opaque]
        #[trust_vc::spec]
        fn hidden_tagged_successor<T>(_tag: T, x: u64) -> u64 {
            x + 1
        }

        #[ensures(true)]
        fn concrete_a() {
            trust_vc::assert!(hidden_tagged_successor::<bool>(true, 4u64) == 5u64);
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("opaque generic source spec should extract as uninterpreted helper");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "opaque generic source specs must remain hidden without reveal, got {result:?}"
    );
}

#[test]
fn source_catalog_rejects_qualified_reveal_target_instead_of_collapsing_name() {
    let path = write_fixture(
        "qualified_reveal_target_rejected.rs",
        r#"
        mod m {}

        #[trust_vc::opaque]
        #[trust_vc::spec]
        fn hidden_id(x: u64) -> u64 {
            x
        }

        #[ensures(true)]
        fn concrete_a() {
            trust_vc::reveal!(m::hidden_id);
            trust_vc::assert!(hidden_id(4u64) == 4u64);
        }
    "#,
    );

    let err = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect_err("qualified reveal target must fail closed");
    assert!(
        err.to_string()
            .contains("supports only unqualified function names"),
        "qualified reveal target should not reveal a bare sibling by last segment, got {err}"
    );
}

#[test]
fn source_catalog_does_not_collapse_qualified_module_names() {
    let path = write_fixture(
        "qualified_module_names_fail_closed.rs",
        r#"
        mod m {
            #[trust_vc::spec]
            fn double(x: int) -> int {
                x + x
            }
        }

        #[ensures(result == m::double(x))]
        fn concrete_a(x: int) -> int {
            x + x
        }
    "#,
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "concrete_a")
        .expect("verification should run and fail closed");
    let VerifyResult::Error { message } = result else {
        panic!(
            "qualified calls should fail closed instead of binding a bare sibling, got {result:?}"
        );
    };
    assert!(
        message.contains("m::double"),
        "qualified calls should fail closed instead of binding a bare sibling, got {message}"
    );
}
