//! Architecture diagnostic controls. Programs are exact pinned-reference
//! bodies; these new native tests are PREPARED, uncompiled and unrun.
mod common;

fn failed(name: &str, source: &str, messages: &[&str], failed_sites: u64) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "failed", "{result:?}");
    assert_eq!(proof["sites_failed"], failed_sites, "{result:?}");
    let errors = result.errors();
    assert_eq!(
        errors
            .iter()
            .map(|d| d.message.as_str())
            .collect::<Vec<_>>(),
        messages,
        "{result:?}"
    );
    // Every specialized diagnostic retains the SAME original statement span.
    assert!(
        errors
            .iter()
            .all(|d| d.primary_lines == errors[0].primary_lines),
        "{result:?}"
    );
}

#[test]
fn default_independent_and_unused_pointer_keep_base() {
    failed(
        "bv_arch_u8_default",
        "verus! {\nproof fn test(x:u8) { assert(x != x) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
    failed(
        "bv_arch_unused_pointer",
        "verus! {\nproof fn test(unused:usize,x:u8) { assert(x!=x) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
}

#[test]
fn actual_only32() {
    failed(
        "bv_arch_only32",
        "verus! {\nproof fn test() { assert(usize::BITS == 64) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied (with arch-size set to 32 bits)"],
        1,
    );
}

#[test]
fn actual_only64() {
    failed(
        "bv_arch_only64",
        "verus! {\nproof fn test() { assert(usize::BITS == 32) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied (with arch-size set to 64 bits)"],
        1,
    );
}

#[test]
fn fixed_architectures_keep_base() {
    failed("bv_arch_fixed32", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test() { assert(usize::BITS == 64) by(bit_vector); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed64", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test() { assert(usize::BITS == 32) by(bit_vector); }\n}", &["bitvector assertion not satisfied"], 1);
}

#[test]
fn wordbits_u32_reports_both_actual_widths_once_per_source_site() {
    failed(
        "bv_arch_wordbits_u32",
        "verus! {\nproof fn test() { assert(arch_word_bits() == 0u32) by(bit_vector); }\n}",
        &[
            "bitvector assertion not satisfied (with arch-size set to 32 bits)",
            "bitvector assertion not satisfied (with arch-size set to 64 bits)",
        ],
        1,
    );
}

#[test]
fn only_requires_consumption_specializes_whole_assertion() {
    failed("bv_arch_requires_wordbits", "verus! {\nproof fn test() { verus_builtin::assert_bitvector_by({ requires(arch_word_bits()==32 || arch_word_bits()==64); ensures(false); }); }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)","bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
}

#[test]
fn cross_width_multi_ensures_execute32_before64() {
    failed("bv_arch_cross_width", "verus! {\nproof fn test() { verus_builtin::assert_bitvector_by({ ensures([usize::BITS==32, usize::BITS==64]); }); }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)","bitvector assertion not satisfied (with arch-size set to 64 bits)"], 2);
}

#[test]
fn array_header_clauses_keep_pure_spec_mode_for_statements_and_tails() {
    for (index, body) in [
        "verus_builtin::assert_bitvector_by({ requires([true, true]); ensures([true, true]); });",
        "verus_builtin::assert_bitvector_by({ requires([true, true]); ensures([true, true]) });",
    ]
    .into_iter()
    .enumerate()
    {
        let result = common::run(
            &format!("bv_array_header_positive_{index}"),
            &format!("verus! {{ proof fn test() {{ {body} }} }}"),
            &[],
        );
        assert_eq!(result.exit, 0, "{result:?}");
        assert_eq!(result.outcome(), "checked", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(
            result.errors().is_empty() && result.raw.is_empty(),
            "{result:?}"
        );
        assert!(
            result.record["crate_refusals"]
                .as_array()
                .unwrap()
                .is_empty(),
            "{result:?}"
        );
    }
    // Every member remains a pure Spec obligation. Recognizing the array
    // carrier must not hide a later executable call, in either header slot.
    for marker in ["requires", "ensures"] {
        for (index, ending) in [";", ""].into_iter().enumerate() {
            let header = if marker == "requires" {
                if ending.is_empty() {
                    "ensures(true); requires([true, effect()])".into()
                } else {
                    "requires([true, effect()]); ensures(true);".into()
                }
            } else {
                format!("ensures([true, effect()]){ending}")
            };
            let source = format!("verus! {{ fn effect() -> bool {{ true }} proof fn test() {{ verus_builtin::assert_bitvector_by({{ {header} }}); }} }}");
            let result = common::run(
                &format!("bv_array_header_mode_{marker}_{index}"),
                &source,
                &[],
            );
            assert_eq!(result.exit, 1, "{result:?}");
            assert!(result.raw.is_empty(), "{result:?}");
            let errors = result.errors();
            assert_eq!(errors.len(), 1, "{result:?}");
            assert!(
                errors[0].message.starts_with("cannot call function `")
                    && errors[0].message.contains("effect")
                    && errors[0].message.ends_with("` with mode exec"),
                "{result:?}"
            );
        }
    }
}

#[test]
fn effective_literals_inline_and_casts_keep_base() {
    failed(
        "bv_arch_pointer_literal",
        "verus! {\nproof fn test() { assert(0usize==1usize) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
    failed(
        "bv_arch_cast_literal",
        "verus! {\nproof fn test() { assert((0u8 as usize)==1usize) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
    failed("bv_arch_inline_literal", "verus! {\n#[verifier::inline] spec fn id<A>(x:A)->A {x}\nproof fn test() { assert(id::<usize>(0usize)==1usize) by(bit_vector); }\n}", &["bitvector assertion not satisfied"], 1);
    failed(
        "bv_arch_usize_min",
        "verus! {\nproof fn test() { assert(usize::MIN==1usize) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
}

#[test]
fn default_out_of_range_cast_retains_real64_failure() {
    failed(
        "bv_arch_cast_big",
        "verus! {\nproof fn test() { assert((4294967296u64 as usize)==0usize) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied (with arch-size set to 64 bits)"],
        1,
    );
}

#[test]
fn tautological_and_absorbed_requirements_do_not_specialize() {
    failed("bv_arch_requires_only", "verus! {\nproof fn test(x:usize) { verus_builtin::assert_bitvector_by({ requires(x==x); ensures(false); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_absorbed_requirement", "verus! {\nproof fn test(x:usize) { verus_builtin::assert_bitvector_by({ requires(true || x==0); ensures(false); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed(
        "bv_arch_shortcircuit",
        "verus! {\nproof fn test(x:usize) { assert(false && x==0usize) by(bit_vector); }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
}

#[test]
fn unsigned_not_and_quantified_pointer_binder_keep_both_widths() {
    failed(
        "bv_arch_unsigned_not",
        "verus! {\nproof fn test() { assert(!0usize == 0usize) by(bit_vector); }\n}",
        &[
            "bitvector assertion not satisfied (with arch-size set to 32 bits)",
            "bitvector assertion not satisfied (with arch-size set to 64 bits)",
        ],
        1,
    );
    failed("bv_arch_quant_binder", "verus! {\nproof fn test() { assert(forall |x:usize| #[trigger] (x&1)==2) by(bit_vector); }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)","bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
}

#[test]
fn malformed_later_clause_refuses_before_any_success_or_counterexample_site() {
    let result=common::run("bv_arch_malformed_later","verus! {\nproof fn test(x:u8,n:i8) { verus_builtin::assert_bitvector_by({ ensures([false, (x>>n)==0]); }); }\n}",&[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == "test")
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
fn retained_default_pointer_max_remains_an_honest_conversion_refusal() {
    let result=common::run("bv_arch_pointer_max_refusal","verus! {\nproof fn test(x:usize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=usize::MAX]); }); }\n}",&[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == "test")
        .unwrap();
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
}

#[test]
fn fixed_pointer_bounds_use_real_admitted_constants_and_base_diagnostics() {
    failed("bv_arch_fixed32_maxusize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test(x:usize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=usize::MAX]); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed32_minisize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x>=isize::MIN]); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed32_maxisize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=isize::MAX]); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed64_maxusize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test(x:usize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=usize::MAX]); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed64_minisize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x>=isize::MIN]); }); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed64_maxisize", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=isize::MAX]); }); }\n}", &["bitvector assertion not satisfied"], 1);
}

#[test]
fn default_signed_bounds_remain_conversion_refusals_with_no_sites() {
    {
        let result=common::run("bv_arch_default_minisize", "verus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x>=isize::MIN]); }); }\n}", &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        let proof = result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["def_path"] == "test")
            .unwrap();
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
    }
    {
        let result=common::run("bv_arch_default_maxisize", "verus! {\nproof fn test(x:isize) { verus_builtin::assert_bitvector_by({ ensures([false, x<=isize::MAX]); }); }\n}", &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        let proof = result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["def_path"] == "test")
            .unwrap();
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
    }
}

fn verified_sites(name: &str, source: &str, proved: u64) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(
        result.raw.is_empty() && result.errors().is_empty(),
        "{result:?}"
    );
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "verified", "{result:?}");
    assert_eq!(proof["sites_proved"], proved, "{result:?}");
    assert_eq!(proof["sites_failed"], 0, "{result:?}");
}

#[test]
fn isolated_false_under_false_outer_guards_is_a_real_failure() {
    failed(
        "bv_arch_outer_false_bv_false",
        "verus! {\nproof fn test() { if false { assert(false) by(bit_vector); } }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
    failed("bv_arch_nested_dead", "verus! {\nproof fn test() { if false { { if false { assert(false) by(bit_vector); } } } }\n}", &["bitvector assertion not satisfied"], 1);
    failed(
        "bv_arch_dead_local_false",
        "verus! {\nproof fn test() { if false { let x:u8=3; assert(x==0) by(bit_vector); } }\n}",
        &["bitvector assertion not satisfied"],
        1,
    );
}

#[test]
fn genuinely_true_dead_local_query_is_generated_and_proved_once() {
    verified_sites(
        "bv_arch_dead_local_true",
        "verus! {\nproof fn test() { if false { let x:u8=3; assert(x==x) by(bit_vector); } }\n}",
        1,
    );
}

#[test]
fn ordinary_architecture_branches_do_not_supply_isolated_width_permissions() {
    failed("bv_arch_outer_only32", "verus! {\nproof fn test() { if arch_word_bits()==32 { assert(usize::BITS==32) by(bit_vector); } }\n}", &["bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
    failed("bv_arch_outer_only64", "verus! {\nproof fn test() { if arch_word_bits()==64 { assert(usize::BITS==64) by(bit_vector); } }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)"], 1);
    failed("bv_arch_branch_aliased_places", "verus! {\nproof fn test(x:usize) { if arch_word_bits()==32 { let y=x; assert(y==x) by(bit_vector); } }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)","bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
}

#[test]
fn conditional_returns_keep_later_queries_in_default_and_fixed_settings() {
    failed("bv_arch_default_ret32", "verus! {\nproof fn test() { if arch_word_bits()==32 { return; } assert(usize::BITS==64) by(bit_vector); }\n}", &["bitvector assertion not satisfied (with arch-size set to 32 bits)"], 1);
    failed("bv_arch_default_ret64", "verus! {\nproof fn test() { if arch_word_bits()==64 { return; } assert(usize::BITS==32) by(bit_vector); }\n}", &["bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
    failed("bv_arch_fixed32_ret32", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test() { if arch_word_bits()==32 { return; } assert(usize::BITS==64) by(bit_vector); }\n}", &["bitvector assertion not satisfied"], 1);
    failed("bv_arch_fixed64_ret64", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test() { if arch_word_bits()==64 { return; } assert(usize::BITS==32) by(bit_vector); }\n}", &["bitvector assertion not satisfied"], 1);
    verified_sites("bv_arch_fixed64_ret32", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(8); };\nverus! {\nproof fn test() { if arch_word_bits()==32 { return; } assert(usize::BITS==64) by(bit_vector); }\n}", 1);
    verified_sites("bv_arch_fixed32_ret64", "#[verus::internal(size_of)]\nconst _: () = { verus_builtin::global_size_of::<usize>(4); };\nverus! {\nproof fn test() { if arch_word_bits()==64 { return; } assert(usize::BITS==32) by(bit_vector); }\n}", 1);
}

#[test]
fn genuine_sst_return_omission_still_distinguishes_retained_else_queries() {
    verified_sites(
        "bv_arch_after_return",
        "verus! {\nproof fn test() { return; assert(false) by(bit_vector); }\n}",
        0,
    );
    verified_sites("bv_arch_return_before_nested_query", "verus! {\nproof fn test() { if arch_word_bits()==32 { return; assert(false) by(bit_vector); } else { assert(true) by(bit_vector); } }\n}", 1);
    failed("bv_arch_return_else_query", "verus! {\nproof fn test() { if arch_word_bits()==32 { return; } else { assert(usize::BITS==32) by(bit_vector); } }\n}", &["bitvector assertion not satisfied (with arch-size set to 64 bits)"], 1);
}

#[test]
fn dead_outer_conversion_refusal_is_not_suppressed_with_the_query() {
    let result=common::run("bv_arch_outer_false_maximum","verus! {\nproof fn test(x:usize) { if false { assert(x<=usize::MAX) by(bit_vector); } }\n}",&[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == "test")
        .unwrap();
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
}

#[test]
fn native_unary_not_preserves_boolean_and_machine_integer_types() {
    let source = "verus! { proof fn test() { assert(!false); assert(!0u8 == 255u8) by(bit_vector); assert(!0i8 == -1i8) by(bit_vector); assert(!0usize != 0usize) by(bit_vector); } }";
    let result = common::run("native_not_result_types", source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(
        result.errors().is_empty() && result.raw.is_empty(),
        "{result:?}"
    );
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "verified", "{result:?}");
    assert_eq!(proof["sites_proved"], 4, "{result:?}");
    assert_eq!(proof["sites_failed"], 0, "{result:?}");
    failed(
        "native_not_u8_false_twin",
        "verus! { proof fn test() { assert(!0u8 == 0u8) by(bit_vector); } }",
        &["bitvector assertion not satisfied"],
        1,
    );
    failed(
        "native_not_bool_false_twin",
        "verus! { proof fn test() { assert(!true); } }",
        &["assertion failed"],
        1,
    );
}
