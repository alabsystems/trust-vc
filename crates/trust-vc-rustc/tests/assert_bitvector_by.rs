//! Native isolated-BV assertions and their surrounding mathematical proof.
//!
//! These are prepared controls, not a recorded native qualification. Every
//! successful fixture must be checked; refusal/Unknown is never a positive.

mod common;

fn verified(name: &str, source: &str) -> common::Run {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "verified", "{result:?}");
    assert!(proof["sites_proved"].as_u64().unwrap() > 0, "{result:?}");
    assert_eq!(proof["sites_failed"], 0, "{result:?}");
    result
}

fn failed(name: &str, source: &str, line: usize, message: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "failed", "{result:?}");
    assert_eq!(proof["sites_failed"], 1, "{result:?}");
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].message, message);
    assert_eq!(errors[0].primary_lines, vec![line], "{errors:?}");
}

#[test]
fn isolated_fixed_width_bitwise_proof_and_false_twin() {
    verified(
        "bv_native_u8",
        "verus! {\nproof fn test(x: u8) {\n    assert(x ^ x == 0) by(bit_vector);\n}\n}",
    );
    failed(
        "bv_native_u8_false",
        "verus! {\nproof fn test(x: u8) {\n    assert(x ^ x == 1) by(bit_vector);\n}\n}",
        3,
        "bitvector assertion not satisfied",
    );
}

#[test]
fn full_u128_and_signed_i128_casts_preserve_the_high_bit() {
    verified("bv_native_128", "verus! {\nproof fn test(x: u128) {\n    assert(x ^ x == 0) by(bit_vector);\n    assert((0xffffffffffffffffffffffffffffffffu128 as i128) == -1i128) by(bit_vector);\n}\n}");
    failed("bv_native_128_false", "verus! {\nproof fn test() {\n    assert((0xffffffffffffffffffffffffffffffffu128 as i128) == 1i128) by(bit_vector);\n}\n}", 3, "bitvector assertion not satisfied");
}

#[test]
fn signed_shift_and_unsigned_wide_count_do_not_wrap_the_count() {
    verified("bv_native_shifts", "verus! {\nproof fn test() {\n    assert((-2i8 >> 1u8) == -1i8) by(bit_vector);\n    assert((1u8 >> 256u16) == 0u8) by(bit_vector);\n    assert((1u8 << 256u16) == 0u8) by(bit_vector);\n}\n}");
    failed(
        "bv_native_shift_false",
        "verus! {\nproof fn test() {\n    assert((1u8 >> 256u16) == 1u8) by(bit_vector);\n}\n}",
        3,
        "bitvector assertion not satisfied",
    );
}

#[test]
fn explicit_requires_are_proved_outside_and_are_the_only_isolated_hypotheses() {
    verified("bv_native_explicit_requires", "verus! {\nproof fn test(x: u8) requires x == 3 {\n    verus_builtin::assert_bitvector_by({\n        requires(x == 3);\n        ensures((x & 1) == 1);\n    });\n    assert((x & 1) == 1);\n}\n}");
    failed("bv_native_missing_requires", "verus! {\nproof fn test(x: u8) requires x == 3 {\n    assert((x & 1) == 1) by(bit_vector);\n}\n}", 3, "bitvector assertion not satisfied");
}

#[test]
fn an_unproved_explicit_requires_is_a_surrounding_proof_failure() {
    failed("bv_native_unproved_requires", "verus! {\nproof fn test(x: u8) {\n    verus_builtin::assert_bitvector_by({\n        requires(x == 3);\n        ensures((x & 1) == 1);\n    });\n}\n}", 4, "requires not satisfied");
}

#[test]
fn ensures_without_a_trailing_semicolon_is_still_a_pure_header() {
    verified("bv_native_tail_header", "verus! {\nproof fn test(x: u16) {\n    verus_builtin::assert_bitvector_by({\n        ensures(x | 0 == x)\n    });\n}\n}");
}

#[test]
fn ordinary_integer_continuation_gets_only_the_established_ensures() {
    verified("bv_native_continuation", "verus! {\nproof fn test(x: u8) {\n    assert(x & x == x) by(bit_vector);\n    assert(x & x == x);\n}\n}");
    failed("bv_native_continuation_false", "verus! {\nproof fn test(x: u8) {\n    assert(x & x == x) by(bit_vector);\n    assert(x & x == x + 1);\n}\n}", 4, "assertion failed");
}

#[test]
fn an_ordinary_local_function_with_the_same_spelling_has_no_bv_authority() {
    failed("bv_native_same_spelling", "verus! {\nproof fn assert_bitvector_by() {}\nproof fn test() {\n    assert_bitvector_by();\n    assert(false);\n}\n}", 5, "assertion failed");
}

#[test]
fn proof_blocks_and_explicit_return_values_keep_the_pinned_language_errors() {
    for (name, body, message, code) in [
        (
            "bv_native_proof_body",
            "ensures(true); assert(true);",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
        (
            "bv_native_return_value",
            "ensures(true); 1u8",
            "mismatched types",
            Some("E0308"),
        ),
        (
            "bv_native_explicit_unit_return",
            "ensures(true); ()",
            "assert_bitvector_by cannot contain a return value",
            None,
        ),
        (
            "bv_native_nested_unit_return",
            "ensures(true); { () }",
            "assert_bitvector_by cannot contain a return value",
            None,
        ),
        (
            "bv_native_unit_local_return",
            "ensures(true); let value = (); value",
            "assert_bitvector_by cannot contain a return value",
            None,
        ),
        (
            "bv_native_tail_proof_call",
            "ensures(true); assert(true)",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
        (
            "bv_native_empty_block_tail",
            "ensures(true); {}",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
        (
            "bv_native_return_before_unit",
            "ensures(true); return; ()",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
        (
            "bv_native_divergent_unit_local",
            "ensures(true); { let value: () = return; () }",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
        (
            "bv_native_divergent_tuple_local",
            "ensures(true); { let value: ((),) = (return,); () }",
            "assert_bitvector_by cannot contain a proof block",
            None,
        ),
    ] {
        let source = format!("verus! {{\nproof fn test() {{\n    verus_builtin::assert_bitvector_by({{{body}}});\n}}\n}}");
        let result = common::run(name, &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, message, "{result:?}");
        assert_eq!(errors[0].code.as_deref(), code, "{result:?}");
        assert_eq!(errors[0].primary_lines, vec![3]);
    }
}

#[test]
fn explicit_inline_bodies_use_actual_typed_arguments_in_both_proof_contexts() {
    verified("bv_native_inline", "verus! {\n#[verifier::inline]\nspec fn identity<A>(x: A) -> A { x }\n#[verifier::inline]\nspec fn add_one(x: u8) -> u8 { (x + 1) as u8 }\n#[verifier::inline]\nspec fn add_two(x: u8) -> u8 { add_one(add_one(x)) }\nproof fn test(x: u8) {\n    assert(identity::<u8>(x) ^ x == 0) by(bit_vector);\n    assert(add_two(253u8) == 255u8) by(bit_vector);\n    assert(add_two(253u8) == 255u8);\n}\n}");
    failed("bv_native_inline_false", "verus! {\n#[verifier::inline]\nspec fn identity<A>(x: A) -> A { x }\nproof fn test(x: u8) {\n    assert(identity::<u8>(x) ^ x == 1) by(bit_vector);\n}\n}", 5, "bitvector assertion not satisfied");
}

#[test]
fn unsupported_calls_cannot_borrow_ordinary_uf_definitions_as_bv_assumptions() {
    let result = common::run("bv_native_not_inline", "verus! {\nspec fn identity(x: u8) -> u8 { x }\nproof fn test(x: u8) {\n    assert(identity(x) ^ x == 0) by(bit_vector);\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_ne!(result.outcome(), "checked", "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "refused", "{result:?}");
    assert_eq!(
        proof.get("sites_proved"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    assert_eq!(
        proof.get("sites_failed"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
}

#[test]
fn inline_attributes_retain_mode_visibility_and_body_requirements() {
    for (name, declaration, message) in [
        (
            "bv_inline_wrong_mode",
            "#[verifier::inline] proof fn helper() {}",
            "'inline' is only allowed for 'spec' functions",
        ),
        (
            "bv_inline_closed_public",
            "#[verifier::inline] pub closed spec fn helper() -> u8 { 0 }",
            "'inline' is only allowed for private or 'open spec' functions",
        ),
        (
            "bv_inline_no_body",
            "#[verifier::inline] uninterp spec fn helper() -> u8;",
            "'inline' functions must have a body",
        ),
    ] {
        let source = format!("verus! {{\n{declaration}\nproof fn test() {{ assert(true); }}\n}}");
        let result = common::run(name, &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, message, "{result:?}");
        assert_eq!(errors[0].primary_lines, vec![2], "{result:?}");
    }
}

#[test]
fn inlined_quantifiers_do_not_capture_a_callers_actual_bound_argument() {
    // The exact u8 pair is pinned-reference qualified. It tests independent
    // nested bound variables; it makes no claim about Boolean BV binders.
    let positive = verified("bv_inline_binder_capture_positive", "verus! {\n#[verifier::inline]\nspec fn relational(a: u8) -> bool { forall |b: u8| #[trigger] ((a + b) as u8) == ((b + a) as u8) }\nproof fn test() {\n    assert(forall |a: u8| #[trigger] ((a + 1) as u8) == ((a + 1) as u8) && relational(a)) by(bit_vector);\n}\n}");
    assert_eq!(positive.record["erase_exit"], 0, "{positive:?}");
    assert!(
        positive.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{positive:?}"
    );
    let proof = positive.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["sites_proved"], 1, "{positive:?}");
    assert_eq!(proof["sites_failed"], 0, "{positive:?}");
    failed("bv_inline_binder_capture_false", "verus! {\n#[verifier::inline]\nspec fn relational(a: u8) -> bool { forall |b: u8| #[trigger] ((a + b) as u8) == ((a + a) as u8) }\nproof fn test() {\n    assert(forall |a: u8| #[trigger] ((a + 1) as u8) == ((a + 1) as u8) && relational(a)) by(bit_vector);\n}\n}", 5, "bitvector assertion not satisfied");
}

#[test]
fn syntax_admission_checks_unsupported_operations_even_under_false_guards() {
    let result = common::run("bv_dead_signed_shift", "verus! {\nproof fn test(x: u8, n: i8) {\n    if false { assert((x >> n) == 0) by(bit_vector); }\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_ne!(result.outcome(), "checked", "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "refused", "{result:?}");
    assert_eq!(
        proof.get("sites_proved"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    assert_eq!(
        proof.get("sites_failed"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
}

#[test]
fn finite_transparent_products_and_unit_keep_actual_inline_layouts() {
    verified("bv_inline_product", "verus! {\nstruct Pair { left: u8, right: u8 }\n#[verifier::inline]\nspec fn identity<A>(x: A) -> A { x }\n#[verifier::inline]\nspec fn swap(p: Pair) -> Pair { Pair { left: p.right, right: p.left } }\n#[verifier::inline]\nspec fn unit_arg(x: ()) -> u8 { 0 }\nproof fn test(p: Pair) {\n    assert(identity::<Pair>(swap(swap(p))).left ^ p.left == 0) by(bit_vector);\n    assert(identity::<Pair>(swap(swap(p))).left == p.left);\n    assert(unit_arg(()) == 0) by(bit_vector);\n}\n}");
    failed("bv_inline_product_false", "verus! {\nstruct Pair { left: u8, right: u8 }\n#[verifier::inline]\nspec fn swap(p: Pair) -> Pair { Pair { left: p.right, right: p.left } }\nproof fn test(p: Pair) {\n    assert(swap(p).left ^ p.left == 0) by(bit_vector);\n}\n}", 6, "bitvector assertion not satisfied");
}

#[test]
fn an_unsigned_arithmetic_root_exposed_by_inlining_keeps_its_nat_clip() {
    verified("bv_inline_nat_sum", "verus! {\n#[verifier::inline]\nspec fn sum(x: u8, y: u8) -> int { x + y }\nproof fn test(x: u8, y: u8) {\n    assert((sum(x, y) as nat) == x + y) by(bit_vector);\n}\n}");
    failed("bv_inline_nat_sum_false", "verus! {\n#[verifier::inline]\nspec fn sum(x: u8, y: u8) -> int { x + y }\nproof fn test(x: u8, y: u8) {\n    assert((sum(x, y) as nat) == x + y + 1) by(bit_vector);\n}\n}", 5, "bitvector assertion not satisfied");
}

#[test]
fn actual_primitive_bits_and_bounds_follow_both_complete_word_contexts() {
    verified("bv_pointer_bits", "verus! {\nproof fn test(x: usize) {\n    assert(arch_word_bits() == 32 || arch_word_bits() == 64);\n    assert(usize::BITS == arch_word_bits()) by(bit_vector);\n    assert((x >> usize::BITS) == 0) by(bit_vector);\n    assert(x <= usize::MAX);\n}\n}");
    failed(
        "bv_pointer_host_width_false",
        "verus! {\nproof fn test() {\n    assert(usize::BITS == 64) by(bit_vector);\n}\n}",
        3,
        "bitvector assertion not satisfied (with arch-size set to 32 bits)",
    );
}

#[test]
fn exact_native_global_pointer_directives_select_the_proof_context_not_the_host_abi() {
    // This is the exact native const language consumed by pinned Verus's
    // process_const_early. It is a syntax/query component control, not a
    // claim that arbitrary attached macro/layout helpers are authenticated.
    for (name, bytes, bits) in [
        ("bv_global_pointer_32", 4, 32),
        ("bv_global_pointer_64", 8, 64),
    ] {
        let source = format!("#[verus::internal(size_of)]\nconst _: () = {{ verus_builtin::global_size_of::<usize>({bytes}); }};\nverus! {{\nproof fn test(x: usize) {{\n    assert(usize::BITS == {bits}) by(bit_vector);\n    assert(arch_word_bits() == {bits});\n    assert(x <= usize::MAX);\n}}\n}}");
        verified(name, &source);
    }
}

#[test]
fn global_pointer_directive_duplicates_and_disagreement_keep_pinned_errors() {
    for (name, directives, message, line) in [
        ("bv_global_duplicate", "#[verus::internal(size_of)] const _: () = { verus_builtin::global_size_of::<usize>(8); };\n#[verus::internal(size_of)] const _: () = { verus_builtin::global_size_of::<usize>(8); };", "the size of `usize` can only be set once per crate", 2),
        ("bv_global_conflict", "#[verus::internal(size_of)] const _: () = { verus_builtin::global_size_of::<usize>(4); };\n#[verus::internal(size_of)] const _: () = { verus_builtin::global_size_of::<isize>(8); };", "usize or isize have already been set to 32 bits", 2),
        ("bv_global_bad_size", "#[verus::internal(size_of)] const _: () = { verus_builtin::global_size_of::<usize>(16); };", "usize and isize can be either 32 or 64 bits", 1),
    ] {
        let source = format!("{directives}\nverus! {{ proof fn test() {{ assert(true); }} }}");
        let result = common::run(name, &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert_eq!(result.record.get("erase_exit"), Some(&serde_json::Value::Null), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
        for function in result.record["functions"].as_array().unwrap() {
            assert_ne!(function["verdict"], "verified", "{result:?}");
            assert_eq!(function.get("sites_proved"), Some(&serde_json::Value::Null), "{result:?}");
            assert_eq!(function.get("sites_failed"), Some(&serde_json::Value::Null), "{result:?}");
        }
        assert!(result.raw.is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, message, "{result:?}");
        assert_eq!(errors[0].primary_lines, vec![line], "{result:?}");
    }
}

#[test]
fn a_same_spelling_local_global_size_function_does_not_select_an_architecture() {
    let source = "const fn global_size_of<T>(x: usize) {}\n#[verus::internal(size_of)] const _: () = { global_size_of::<usize>(8); };\nverus! { proof fn test() { assert(usize::BITS == 64) by(bit_vector); } }";
    let result = common::run("bv_counterfeit_global_size", source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_ne!(result.outcome(), "checked", "{result:?}");
    assert!(
        !result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|function| function["def_path"] == "test" && function["verdict"] == "verified"),
        "{result:?}"
    );
}

#[test]
fn ordinary_inline_choices_keep_the_choice_registry_and_stay_outside_bv_queries() {
    // Qualified by the pinned Verus reference: the call is a genuine trigger,
    // and the existence witness is a checked assertion, never an axiom.
    let positive = verified("bv_ordinary_inline_choice", "verus! {\nspec fn is_zero(x: u8) -> bool { x == 0 }\n#[verifier::inline]\nspec fn pick_zero() -> u8 { choose |x: u8| is_zero(x) }\nproof fn test() {\n    assert(is_zero(0));\n    assert(pick_zero() == 0);\n}\n}");
    assert_eq!(positive.record["erase_exit"], 0, "{positive:?}");
    assert!(
        positive.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{positive:?}"
    );
    let proof = positive.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["sites_proved"], 2, "{positive:?}");
    assert_eq!(proof["sites_failed"], 0, "{positive:?}");

    let negative = common::run("bv_ordinary_inline_choice_false", "verus! {\nspec fn is_zero(x: u8) -> bool { x == 0 }\n#[verifier::inline]\nspec fn pick_zero() -> u8 { choose |x: u8| is_zero(x) }\nproof fn test() {\n    assert(is_zero(0));\n    assert(pick_zero() != 0);\n}\n}", &[]);
    assert_eq!(negative.exit, 1, "{negative:?}");
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert_eq!(negative.record["erase_exit"], 0, "{negative:?}");
    assert!(
        negative.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{negative:?}"
    );
    assert!(negative.raw.is_empty(), "{negative:?}");
    let proof = negative.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "failed", "{negative:?}");
    assert_eq!(proof["sites_proved"], 1, "{negative:?}");
    assert_eq!(proof["sites_failed"], 1, "{negative:?}");
    let errors = negative.errors();
    assert_eq!(errors.len(), 1, "{negative:?}");
    assert_eq!(errors[0].message, "assertion failed", "{negative:?}");
    assert_eq!(errors[0].primary_lines, vec![7], "{negative:?}");

    // The same valid choice is intentionally outside the isolated BV
    // fragment, matching the pinned reference's unsupported Choose bind.
    let result = common::run("bv_inline_choice_refusal", "verus! {\nspec fn is_zero(x: u8) -> bool { x == 0 }\n#[verifier::inline]\nspec fn pick_zero() -> u8 { choose |x: u8| is_zero(x) }\nproof fn test() {\n    assert(is_zero(0));\n    assert(pick_zero() == 0) by(bit_vector);\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "refused", "{result:?}");
    assert_eq!(proof["tag"], "bit-vector-expression", "{result:?}");
    assert_eq!(
        proof.get("sites_proved"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    assert_eq!(
        proof.get("sites_failed"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].message, "trust-vc refused: bit-vector-expression: an isolated BV expression requiring unsupported lowering or inlining", "{result:?}");
}

#[test]
fn closed_generic_inline_choices_use_the_actual_domain_and_preserve_false_twins() {
    verified("bv_closed_inline_choice", "verus! {\nspec fn is_x<A>(y: A, x: A) -> bool { y == x }\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| is_x(y, x) }\nproof fn test(x: u8) {\n    assert(is_x::<u8>(x, x));\n    assert(pick::<u8>(x) == x);\n}\n}");
    failed("bv_closed_inline_choice_false", "verus! {\nspec fn is_x<A>(y: A, x: A) -> bool { y == x }\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| is_x(y, x) }\nproof fn test(x: u8) {\n    assert(is_x::<u8>(x, x));\n    assert(pick::<u8>(x) != x);\n}\n}", 7, "assertion failed");
    let result = common::run("bv_closed_inline_choice_still_refused", "verus! {\nspec fn is_x<A>(y: A, x: A) -> bool { y == x }\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| is_x(y, x) }\nproof fn test(x: u8) {\n    assert(is_x::<u8>(x, x));\n    assert(pick::<u8>(x) == x) by(bit_vector);\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "refused", "{result:?}");
    assert_eq!(
        proof.get("sites_proved"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    assert_eq!(
        proof.get("sites_failed"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
}

#[test]
fn closed_generic_inline_quantifiers_keep_bound_types_and_no_binder_capture() {
    // Both programs are qualified against the pinned Verus reference. The
    // witness is checked, and each forall has a real covering call trigger.
    let positive = verified("bv_closed_inline_quant", "verus! {\nspec fn is_x<A>(y: A, x: A) -> bool { y == x }\n#[verifier::inline]\nspec fn reflexive<A>(x: A) -> bool { forall |y: A| #[trigger] is_x(y, x) ==> is_x(x, y) }\nproof fn test(x: u16) {\n    assert(is_x::<u16>(x, x));\n    assert(reflexive::<u16>(x));\n}\n}");
    let proof = positive.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(positive.record["erase_exit"], 0, "{positive:?}");
    assert!(
        positive.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{positive:?}"
    );
    assert_eq!(proof["sites_proved"], 2, "{positive:?}");
    assert_eq!(proof["sites_failed"], 0, "{positive:?}");

    let negative = common::run("bv_closed_inline_quant_false", "verus! {\nspec fn is_x<A>(y: A, x: A) -> bool { y == x }\n#[verifier::inline]\nspec fn all_equal<A>(x: A) -> bool { forall |y: A| #[trigger] is_x(y, x) }\nproof fn test(x: bool) {\n    assert(is_x::<bool>(x, x));\n    assert(all_equal::<bool>(x));\n}\n}", &[]);
    assert_eq!(negative.exit, 1, "{negative:?}");
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert_eq!(negative.record["erase_exit"], 0, "{negative:?}");
    assert!(
        negative.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{negative:?}"
    );
    assert!(negative.raw.is_empty(), "{negative:?}");
    let proof = negative.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "failed", "{negative:?}");
    assert_eq!(proof["sites_proved"], 1, "{negative:?}");
    assert_eq!(proof["sites_failed"], 1, "{negative:?}");
    let errors = negative.errors();
    assert_eq!(errors.len(), 1, "{negative:?}");
    assert_eq!(errors[0].message, "assertion failed");
    assert_eq!(errors[0].primary_lines, vec![7], "{negative:?}");
}

// These are current ownership-boundary discriminators. The local `vstd` alias
// only makes the real macro expansion Rust-resolvable under common's explicit
// verus_no_vstd configuration. It supplies NO foreign library/contract authority
// and is not the mandatory genuine-vstd positive qualification.
fn refused_layout_helper(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let errors = result.errors();
    assert!(!errors.is_empty(), "{result:?}");
    assert!(
        errors.iter().all(|error| error.code.is_none()),
        "a Rust setup/type-resolution error is not this ownership discriminator: {result:?}"
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("size_of_broadcast_proof")),
        "the actual generated/helper marker must reach the reader's refusal path: {result:?}"
    );
}

#[test]
fn a_native_resolvable_whole_global_macro_cannot_silently_drop_its_layout_contract() {
    for (name, body) in [
        (
            "bv_layout_macro_local_positive_shape",
            "assert(usize::BITS == 64) by(bit_vector);",
        ),
        (
            "bv_layout_macro_local_false_shape",
            "assert(usize::BITS == 32) by(bit_vector);",
        ),
    ] {
        let source = format!("extern crate self as vstd;\npub mod layout {{\n    use verus_builtin::*;\n    use verus_builtin_macros::*;\n    verus! {{ pub uninterp spec fn size_of<A>() -> nat; }}\n}}\nverus! {{\n    global size_of usize == 8;\n    proof fn test() {{ {body} }}\n}}");
        refused_layout_helper(name, &source);
    }
}

#[test]
fn copied_layout_helper_spelling_and_marker_do_not_supply_contract_ownership() {
    for (name, helper) in [
        ("bv_layout_helper_same_name", "VERUS_layout_of_usize"),
        ("bv_layout_helper_different_name", "unrelated_contract"),
    ] {
        let source = format!("#[verus::internal(size_of)]\nconst _: () = {{ verus_builtin::global_size_of::<usize>(8); }};\nverus! {{\n    #[verus::internal(size_of_broadcast_proof)]\n    #[verifier::external_body]\n    broadcast proof fn {helper}() ensures false {{}}\n    proof fn test() {{ assert(usize::BITS == 64) by(bit_vector); }}\n}}");
        refused_layout_helper(name, &source);
    }
}

#[test]
fn signed_arithmetic_does_not_acquire_an_unsigned_nat_clip_permission() {
    let result = common::run("bv_inline_signed_nat_refusal", "verus! {\n#[verifier::inline]\nspec fn signed_sum(x: i8, y: i8) -> int { x + y }\nproof fn test(x: i8, y: i8) {\n    assert((signed_sum(x, y) as nat) >= 0) by(bit_vector);\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("actual proof");
    assert_eq!(proof["verdict"], "refused", "{result:?}");
    assert_eq!(
        proof.get("sites_proved"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
    assert_eq!(
        proof.get("sites_failed"),
        Some(&serde_json::Value::Null),
        "{result:?}"
    );
}

#[test]
fn associated_constant_values_follow_their_native_owners() {
    for (name, declaration, condition, false_condition) in [
        ("bv_owned_inherent_bits", "struct Fake; impl Fake { const BITS: u32 = 64; }", "Fake::BITS == 64", "Fake::BITS == 32"),
        ("bv_owned_inherent_max", "struct Fake; impl Fake { const MAX: usize = 0; }", "Fake::MAX == 0", "Fake::MAX == 1"),
        ("bv_owned_trait_bits", "trait HasBits { const BITS: u32; } struct Fake; impl HasBits for Fake { const BITS: u32 = 64; }", "<Fake as HasBits>::BITS == 64", "<Fake as HasBits>::BITS == 32"),
        ("bv_owned_trait_default", "trait HasBits { const BITS: u32 = 17; } struct Fake; impl HasBits for Fake {}", "<Fake as HasBits>::BITS == 17", "<Fake as HasBits>::BITS == 64"),
        ("bv_owned_generic_owner", "struct Holder<A> { value: A } impl<A> Holder<A> { const BITS: u32 = 19; }", "Holder::<u8>::BITS == 19", "Holder::<u8>::BITS == 64"),
        ("bv_owned_generic_selection", "trait HasBits { const BITS: u32; } struct First; struct Second; impl HasBits for First { const BITS: u32 = 3; } impl HasBits for Second { const BITS: u32 = 5; } #[verifier::inline] spec fn bits<A: HasBits>() -> u32 { A::BITS }", "bits::<First>() + bits::<Second>() == 8", "bits::<First>() + bits::<Second>() == 9"),
    ] {
        let source = format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert({condition}) by(bit_vector);\n    assert({condition});\n}}\n}}\n");
        verified(name, &source);
        let twin = format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert({false_condition}) by(bit_vector);\n}}\n}}\n");
        failed(&format!("{name}_false"), &twin, 4, "bitvector assertion not satisfied");
    }
}

#[test]
fn concrete_inline_associated_constants_keep_distinct_ordinary_values() {
    let declaration = "trait HasBits { const BITS: u32; } struct First; struct Second; impl HasBits for First { const BITS: u32 = 3; } impl HasBits for Second { const BITS: u32 = 5; } #[verifier::inline] spec fn bits<A: HasBits>() -> u32 { A::BITS }";
    verified(
        "ordinary_owned_generic_selection",
        &format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert(bits::<First>() == 3);\n    assert(bits::<Second>() == 5);\n    assert(bits::<First>() != bits::<Second>());\n}}\n}}\n"),
    );
    failed(
        "ordinary_owned_generic_selection_false",
        &format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert(bits::<First>() == bits::<Second>());\n}}\n}}\n"),
        4,
        "assertion failed",
    );
}

#[test]
fn associated_constant_initializers_preserve_both_word_contexts() {
    let declaration = "struct Fake; impl Fake { const BITS: u32 = usize::BITS; }";
    verified("bv_owned_word_bits", &format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert(Fake::BITS == usize::BITS) by(bit_vector);\n}}\n}}"));
    failed("bv_owned_word_bits_false", &format!("verus! {{\n{declaration}\nproof fn test() {{\n    assert(Fake::BITS == 64) by(bit_vector);\n}}\n}}"), 4, "bitvector assertion not satisfied (with arch-size set to 32 bits)");
    // A user spelling supplies only its own value, never the primitive rule.
    verified("bv_owned_literal_is_not_word_bits", "verus! {\nstruct Fake; impl Fake { const BITS: u32 = 64; }\nproof fn test() {\n    assert(Fake::BITS == 64) by(bit_vector);\n}\n}");
}

#[test]
fn unowned_associated_constants_do_not_gain_value_authority() {
    for (name, declaration, condition) in [
        ("bv_external_inherent_bits", "struct Fake; impl Fake { const BITS: u32 = 64; }", "Fake::BITS == 64"),
        ("bv_external_trait_bits", "trait HasBits { const BITS: u32; } struct Fake; impl HasBits for Fake { const BITS: u32 = 64; }", "<Fake as HasBits>::BITS == 64"),
    ] {
        let source = format!("{declaration}\nverus! {{ proof fn test() {{ assert({condition}) by(bit_vector); }} }}");
        let result = common::run(name, &source, &[]);
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert_eq!(result.record["erase_exit"], serde_json::Value::Null, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        for function in result.record["functions"].as_array().unwrap() {
            assert_ne!(function["verdict"], "verified", "{result:?}");
            assert_eq!(function.get("sites_proved"), Some(&serde_json::Value::Null), "{result:?}");
        }
        assert!(result.errors().iter().any(|error| error.message.contains("a path to associated constant")), "{result:?}");
    }
}

#[test]
fn original_generic_choices_without_triggers_keep_the_pinned_source_error() {
    for (name, source) in [
        ("bv_original_choice_trigger_positive", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test(x: u8) {\n    assert(pick::<u8>(x) == x);\n}\n}"),
        ("bv_original_choice_trigger_false", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test(x: u8) {\n    assert(pick::<u8>(x) != x);\n}\n}"),
        ("bv_original_choice_trigger_isolated", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test(x: u8) {\n    assert(pick::<u8>(x) == x) by(bit_vector);\n}\n}")
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.");
        assert_eq!(errors[0].primary_lines, vec![3], "{result:?}");
        let pick = result.record["functions"].as_array().unwrap().iter()
            .find(|function| function["def_path"] == "pick").expect("actual generic declaration");
        assert_eq!(pick["verdict"], "rejected", "{result:?}");
        for function in result.record["functions"].as_array().unwrap() {
            assert_ne!(function["verdict"], "verified", "{result:?}");
            assert_eq!(function.get("sites_proved"), Some(&serde_json::Value::Null), "{result:?}");
            assert_eq!(function.get("sites_failed"), Some(&serde_json::Value::Null), "{result:?}");
        }
    }
}

#[test]
fn original_generic_quantifiers_without_triggers_keep_the_pinned_source_error() {
    // These exact original programs are language errors, not a proof pair.
    // Both remain mandatory after reference-grounded positive-fixture repair.
    for (name, declaration, source) in [
        ("bv_original_quantifier_trigger_positive", "reflexive", "verus! {\n#[verifier::inline]\nspec fn reflexive<A>(x: A) -> bool { forall |y: A| y == x ==> x == y }\nproof fn test(x: u16) {\n    assert(reflexive::<u16>(x));\n}\n}"),
        ("bv_original_quantifier_trigger_false", "all_equal", "verus! {\n#[verifier::inline]\nspec fn all_equal<A>(x: A) -> bool { forall |y: A| y == x }\nproof fn test(x: bool) {\n    assert(all_equal::<bool>(x));\n}\n}"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.");
        assert_eq!(errors[0].primary_lines, vec![3], "{result:?}");
        let function = result.record["functions"].as_array().unwrap().iter()
            .find(|function| function["def_path"] == declaration).expect("actual generic declaration");
        assert_eq!(function["verdict"], "rejected", "{result:?}");
        for function in result.record["functions"].as_array().unwrap() {
            assert_ne!(function["verdict"], "verified", "{result:?}");
            assert_eq!(function.get("sites_proved"), Some(&serde_json::Value::Null), "{result:?}");
            assert_eq!(function.get("sites_failed"), Some(&serde_json::Value::Null), "{result:?}");
        }
    }
}

#[test]
fn original_boolean_inline_quantifier_without_triggers_keeps_the_pinned_source_error() {
    // Exact original Source40 failed input. It is a language-negative control,
    // never a valid proof pair or evidence of Boolean binder capture.
    let result = common::run("bv_original_boolean_binder_trigger", "verus! {\n#[verifier::inline]\nspec fn all_implied(a: bool) -> bool { forall |b: bool| a ==> b }\nproof fn test() {\n    assert(forall |a: bool| all_implied(a)) by(bit_vector);\n}\n}", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].message, "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.");
    assert_eq!(errors[0].primary_lines, vec![3], "{result:?}");
    let helper = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "all_implied")
        .expect("actual original declaration");
    assert_eq!(helper["verdict"], "rejected", "{result:?}");
    for function in result.record["functions"].as_array().unwrap() {
        assert_ne!(function["verdict"], "verified", "{result:?}");
        assert_eq!(
            function.get("sites_proved"),
            Some(&serde_json::Value::Null),
            "{result:?}"
        );
        assert_eq!(
            function.get("sites_failed"),
            Some(&serde_json::Value::Null),
            "{result:?}"
        );
    }
}

#[test]
fn original_zero_argument_inline_choices_without_triggers_keep_the_pinned_source_error() {
    // Exact original native20 programs. Both are language errors, and remain
    // strict controls after the reference-grounded positive-fixture repair.
    for (name, source) in [
        ("bv_original_zeroarg_choice_trigger_positive", "verus! {\n#[verifier::inline]\nspec fn pick_zero() -> u8 { choose |x: u8| x == 0 }\nproof fn test() {\n    assert(pick_zero() == 0);\n}\n}"),
        ("bv_original_zeroarg_choice_trigger_isolated", "verus! {\n#[verifier::inline]\nspec fn pick_zero() -> u8 { choose |x: u8| x == 0 }\nproof fn test() {\n    assert(pick_zero() == 0) by(bit_vector);\n}\n}"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.");
        assert_eq!(errors[0].primary_lines, vec![3], "{result:?}");
        let pick = result.record["functions"].as_array().unwrap().iter()
            .find(|function| function["def_path"] == "pick_zero").expect("actual original declaration");
        assert_eq!(pick["verdict"], "rejected", "{result:?}");
        for function in result.record["functions"].as_array().unwrap() {
            assert_ne!(function["verdict"], "verified", "{result:?}");
            assert_eq!(function.get("sites_proved"), Some(&serde_json::Value::Null), "{result:?}");
            assert_eq!(function.get("sites_failed"), Some(&serde_json::Value::Null), "{result:?}");
        }
    }
}
