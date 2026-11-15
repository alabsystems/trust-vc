// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness sentinels for source-level function identity and lexical scope.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(source: &str, function: &str) -> Result<VerifyResult, String> {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_source_name_resolution_{}_{}.rs",
        std::process::id(),
        function
    ));
    std::fs::write(&path, source).expect("write source-name fixture");
    let result = verify_function_from_file(path.to_str().expect("utf-8 path"), function)
        .map_err(|error| error.to_string());
    let _ = std::fs::remove_file(path);
    result
}

fn assert_not_verified(source: &str, function: &str) {
    if let Ok(VerifyResult::Verified) = verify(source, function) {
        panic!("SOUNDNESS: `{function}` verified through an unresolved source name");
    }
}

const NESTED_SPEC: &str = r#"
mod hidden_scope {
    #[trust_vc::spec]
    pub fn always_true() -> bool { true }
}

#[trust_vc::ensures(result)]
fn bare_nested_spec_without_import() -> bool {
    always_true()
}

#[trust_vc::ensures(result)]
fn qualified_nested_spec() -> bool {
    hidden_scope::always_true()
}
"#;

#[test]
fn unique_nested_spec_does_not_gain_a_global_bare_alias() {
    assert_not_verified(NESTED_SPEC, "bare_nested_spec_without_import");
}

/// `hidden_scope::always_true()` runs in the exec body, and a spec function
/// panics when called at run time, so the ghost-call rule refuses the answer.
/// It refuses only a `Verified` answer, so the refusal still shows that the
/// qualified name resolves to the nested spec's body.
#[test]
fn qualified_nested_spec_remains_available() {
    let result = verify(NESTED_SPEC, "qualified_nested_spec")
        .unwrap_or_else(|error| panic!("qualified nested spec must extract: {error}"));
    assert!(
        matches!(
            &result,
            VerifyResult::Error { message }
                if message.contains("ghost function called from exec code")
        ),
        "qualified nested spec should retain its body semantics (a `Verified` answer, \
         refused by the ghost-call rule), got {result:?}"
    );
}

const BLOCK_ALIAS_TO_SPEC: &str = r#"
mod nested {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn hidden_body() -> bool { true }
}

#[trust_vc::ensures(result)]
fn block_alias_cannot_reclassify_spec_as_exec_helper() -> bool {
    use nested::hidden_body as alias;
    alias()
}
"#;

#[test]
fn block_use_alias_cannot_bypass_spec_opacity_as_a_sibling_helper() {
    assert_not_verified(
        BLOCK_ALIAS_TO_SPEC,
        "block_alias_cannot_reclassify_spec_as_exec_helper",
    );
}

const BLOCK_ALIAS_TO_EXEC: &str = r#"
mod nested {
    pub fn truth() -> bool { true }
}

#[trust_vc::ensures(result)]
fn block_alias_to_exec_helper_remains_supported() -> bool {
    use nested::truth as alias;
    alias()
}
"#;

#[test]
fn unambiguous_outer_block_alias_to_exec_helper_verifies() {
    let result = verify(
        BLOCK_ALIAS_TO_EXEC,
        "block_alias_to_exec_helper_remains_supported",
    )
    .unwrap_or_else(|error| panic!("unambiguous exec alias should extract: {error}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "an unambiguous outer-block exec alias should retain its helper body, got {result:?}"
    );
}

const BLOCK_ALIAS_TO_PRIVATE_EXEC: &str = r#"
mod nested {
    fn secret() -> bool { true }
}

#[trust_vc::ensures(result)]
fn private_nested_exec_alias_is_not_visible() -> bool {
    use nested::secret as alias;
    alias()
}
"#;

#[test]
fn block_alias_does_not_grant_private_nested_exec_visibility() {
    let result = verify(
        BLOCK_ALIAS_TO_PRIVATE_EXEC,
        "private_nested_exec_alias_is_not_visible",
    );
    assert!(
        result.is_err(),
        "a block alias must not make a private nested exec function visible, got {result:?}"
    );
}

const BLOCK_ALIAS_SPEC_RECOMMENDS: &str = r#"
mod nested {
    #[trust_vc::spec]
    #[trust_vc::recommends(x > 0)]
    pub fn guarded(x: i32) -> bool { true }
}

#[trust_vc::proof]
fn alias_call_still_checks_canonical_recommends() {
    use nested::guarded as alias;
    let _ = alias(0);
}
"#;

#[test]
fn block_use_alias_preserves_canonical_spec_recommends() {
    let result = verify(
        BLOCK_ALIAS_SPEC_RECOMMENDS,
        "alias_call_still_checks_canonical_recommends",
    )
    .unwrap_or_else(|error| panic!("aliased spec recommends should extract: {error}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "an aliased call with a false canonical recommends clause must not verify"
    );
}

const BLOCK_ALIAS_TO_ILL_FOUNDED_SPEC: &str = r#"
mod nested {
    #[trust_vc::spec]
    pub fn contradictory(n: int) -> int { contradictory(n) + 1 }
}

#[trust_vc::proof]
fn block_alias_cannot_bypass_recursive_admission() {
    use nested::contradictory as alias;
    trust_vc::assert!(alias(0) == alias(0) + 1);
    trust_vc::assert!(false);
}
"#;

#[test]
fn block_use_alias_cannot_bypass_recursive_admission() {
    assert_not_verified(
        BLOCK_ALIAS_TO_ILL_FOUNDED_SPEC,
        "block_alias_cannot_bypass_recursive_admission",
    );
}

const BLOCK_ALIAS_TO_INLINE_FALSE_SPEC: &str = r#"
mod nested {
    #[trust_vc::spec]
    #[trust_vc::inline]
    pub fn false_value() -> bool { false }
}

#[trust_vc::proof]
fn alias_preserves_inline_spec_body() {
    use nested::false_value as alias;
    trust_vc::assert!(alias());
}
"#;

#[test]
fn block_use_alias_cannot_replace_inline_spec_body() {
    let result = verify(
        BLOCK_ALIAS_TO_INLINE_FALSE_SPEC,
        "alias_preserves_inline_spec_body",
    )
    .unwrap_or_else(|error| panic!("inline alias should extract: {error}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "an inline false body must remain false through its alias"
    );
}

const BLOCK_ALIAS_TO_UNINTERP_SPEC: &str = r#"
mod nested {
    #[trust_vc::spec]
    pub fn unknown() -> bool;
}

#[trust_vc::proof]
fn alias_cannot_define_or_reveal_uninterp_spec() {
    use nested::unknown as alias;
    trust_vc::reveal!(alias);
    trust_vc::assert!(alias());
}
"#;

#[test]
fn block_use_alias_cannot_define_or_reveal_uninterp_spec() {
    let result = verify(
        BLOCK_ALIAS_TO_UNINTERP_SPEC,
        "alias_cannot_define_or_reveal_uninterp_spec",
    )
    .unwrap_or_else(|error| panic!("uninterp alias should extract: {error}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "alias + reveal must not fabricate an uninterpreted spec body"
    );
}

const BLOCK_ALIAS_HIDE: &str = r#"
mod nested {
    #[trust_vc::spec]
    pub fn truth() -> bool { true }
}

#[trust_vc::proof]
fn hide_alias_reopaques_canonical_body() {
    use nested::truth as alias;
    trust_vc::hide!(alias);
    trust_vc::assert!(alias());
}
"#;

#[test]
fn hide_of_block_alias_reopaques_the_canonical_spec_body() {
    assert_not_verified(BLOCK_ALIAS_HIDE, "hide_alias_reopaques_canonical_body");
}

const NESTED_BLOCK_ALIAS_SCOPE: &str = r#"
#[trust_vc::spec]
fn h() -> bool { false }

mod nested {
    #[trust_vc::spec]
    pub fn truth() -> bool { true }
}

#[trust_vc::proof]
fn nested_alias_cannot_leak_to_outer_call() {
    {
        use nested::truth as h;
        trust_vc::assert!(h());
    }
    trust_vc::assert!(h());
}
"#;

#[test]
fn nested_block_alias_cannot_leak_outside_its_lexical_scope() {
    let result = verify(
        NESTED_BLOCK_ALIAS_SCOPE,
        "nested_alias_cannot_leak_to_outer_call",
    );
    assert!(
        result.is_err(),
        "nested alias use must be rejected until source symbols carry lexical scope, got {result:?}"
    );
}

const NESTED_ALIAS_REVEAL_SCOPE: &str = r#"
#[trust_vc::spec]
#[trust_vc::opaque]
fn h() -> bool { false }

mod nested {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn truth() -> bool { true }
}

#[trust_vc::proof]
fn nested_alias_reveal_cannot_open_outer_body() {
    {
        use nested::truth as h;
        trust_vc::reveal!(h);
        trust_vc::assert!(!h());
    }
}
"#;

#[test]
fn nested_alias_visibility_directive_cannot_target_outer_function() {
    let result = verify(
        NESTED_ALIAS_REVEAL_SCOPE,
        "nested_alias_reveal_cannot_open_outer_body",
    );
    assert!(
        result.is_err(),
        "nested alias visibility must fail closed instead of revealing the outer same-spelling function, got {result:?}"
    );
}

const ASSERT_BY_NESTED_ALIAS_SCOPE: &str = r#"
#[trust_vc::spec]
fn h() -> bool { true }

mod nested {
    #[trust_vc::spec]
    pub fn false_value() -> bool { false }
}

#[trust_vc::proof]
fn assert_by_nested_alias_cannot_fall_back_to_outer_h() {
    trust_vc::assert_by!(true, {
        use nested::false_value as h;
        trust_vc::assert!(h());
    });
}
"#;

#[test]
fn assert_by_nested_alias_is_seen_by_scope_gate() {
    let result = verify(
        ASSERT_BY_NESTED_ALIAS_SCOPE,
        "assert_by_nested_alias_cannot_fall_back_to_outer_h",
    );
    assert!(
        result.is_err(),
        "an alias imported inside assert_by must fail closed instead of falling back to the outer `h`, got {result:?}"
    );
}

const LOCAL_MACRO_ALIAS_SCOPE: &str = r#"
#[trust_vc::spec]
fn h() -> bool { true }

mod nested {
    #[trust_vc::spec]
    pub fn false_value() -> bool { false }
}

#[trust_vc::proof]
fn local_macro_alias_cannot_fall_back_to_outer_h() {
    macro_rules! bad_alias {
        () => {
            use nested::false_value as h;
            trust_vc::assert!(h());
        };
    }
    bad_alias!();
}
"#;

#[test]
fn local_macro_generated_use_alias_fails_closed() {
    let result = verify(
        LOCAL_MACRO_ALIAS_SCOPE,
        "local_macro_alias_cannot_fall_back_to_outer_h",
    );
    assert!(
        result.is_err(),
        "a macro-generated import must not let an expanded call fall back to outer `h`, got {result:?}"
    );
}

const MODULE_RELATIVE_BLOCK_ALIAS: &str = r#"
mod a {
    pub mod m {
        #[trust_vc::spec]
        pub fn f() -> bool { false }
    }

    #[trust_vc::proof]
    #[trust_vc::ensures(result)]
    pub fn target_nested() -> bool {
        use m::f as alias;
        alias()
    }
}

mod m {
    #[trust_vc::spec]
    pub fn f() -> bool { true }
}
"#;

#[test]
fn relative_block_alias_in_nested_module_cannot_resolve_at_crate_root() {
    let result = verify(MODULE_RELATIVE_BLOCK_ALIAS, "target_nested");
    assert!(
        result.is_err(),
        "module-relative alias must not be rebound to a same-named crate-root module, got {result:?}"
    );
}

const CRATE_ROOT_BLOCK_ALIAS_IN_NESTED_MODULE: &str = r#"
mod a {
    #[trust_vc::proof]
    #[trust_vc::ensures(result)]
    pub fn target_nested_crate_path() -> bool {
        use crate::m::f as alias;
        alias()
    }
}

mod m {
    #[trust_vc::spec]
    pub fn f() -> bool { true }
}
"#;

#[test]
fn explicit_crate_block_alias_in_nested_module_keeps_root_provenance() {
    let result = verify(
        CRATE_ROOT_BLOCK_ALIAS_IN_NESTED_MODULE,
        "target_nested_crate_path",
    )
    .unwrap_or_else(|error| panic!("explicit crate-root alias should extract: {error}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "explicit crate-root alias should retain root provenance, got {result:?}"
    );
}

const BODY_ALIAS_ATTRIBUTE_SCOPE: &str = r#"
#[trust_vc::spec]
fn h() -> bool { false }

mod nested {
    #[trust_vc::spec]
    pub fn truth() -> bool { true }
}

#[trust_vc::ensures(h())]
fn body_alias_cannot_retarget_attribute() -> bool {
    use nested::truth as h;
    h()
}
"#;

#[test]
fn body_alias_cannot_retarget_contract_attribute_name() {
    let result = verify(
        BODY_ALIAS_ATTRIBUTE_SCOPE,
        "body_alias_cannot_retarget_attribute",
    );
    assert!(
        result.is_err(),
        "body alias/attribute name collision must fail closed, got {result:?}"
    );
}

const BODY_ALIAS_TRANSITIVE_SPEC_SCOPE: &str = r#"
mod bad {
    #[trust_vc::spec]
    pub fn false_value() -> bool { false }
}

// This module-scope import is the spelling `wrapper` resolves in real Rust.
use bad::false_value as shared;

#[trust_vc::spec]
fn wrapper() -> bool { shared() }

mod good {
    #[trust_vc::spec]
    pub fn true_value() -> bool { true }
}

#[trust_vc::proof]
fn body_alias_cannot_leak_into_transitive_spec_body() {
    use good::true_value as shared;
    trust_vc::assert!(shared());
    trust_vc::assert!(wrapper());
}
"#;

#[test]
fn body_alias_equality_cannot_leak_into_another_spec_scope() {
    let result = verify(
        BODY_ALIAS_TRANSITIVE_SPEC_SCOPE,
        "body_alias_cannot_leak_into_transitive_spec_body",
    );
    assert!(
        result.is_err(),
        "query-global alias equality must fail closed when another spec body uses the same spelling, got {result:?}"
    );
}

const BODY_ALIAS_WHEN_USED_AS_SPEC_SCOPE: &str = r#"
#[trust_vc::spec]
fn good_model() -> bool { true }

#[trust_vc::when_used_as_spec(missing_model)]
fn exec_helper() -> bool { false }

#[trust_vc::ensures(exec_helper())]
fn body_alias_cannot_retarget_when_used_as_spec() {
    use crate::good_model as missing_model;
}
"#;

#[test]
fn body_alias_cannot_retarget_a_helpers_when_used_as_spec_attribute() {
    let result = verify(
        BODY_ALIAS_WHEN_USED_AS_SPEC_SCOPE,
        "body_alias_cannot_retarget_when_used_as_spec",
    );
    assert!(
        result.is_err(),
        "a target-body import must not resolve a helper's when_used_as_spec attribute, got {result:?}"
    );
}

const QUALIFIED_WHEN_USED_AS_SPEC_IDENTITY: &str = r#"
#[trust_vc::spec]
fn model() -> bool { true }

mod nested {
    #[trust_vc::spec]
    pub fn model() -> bool { false }
}

#[trust_vc::when_used_as_spec(nested::model)]
fn exec_helper() -> bool { true }

#[trust_vc::ensures(exec_helper())]
fn qualified_when_used_as_spec_keeps_full_identity() {}
"#;

#[test]
fn qualified_when_used_as_spec_does_not_collapse_to_bare_name() {
    assert_not_verified(
        QUALIFIED_WHEN_USED_AS_SPEC_IDENTITY,
        "qualified_when_used_as_spec_keeps_full_identity",
    );
}

const QUALIFIED_WHEN_USED_AS_SPEC_POSITIVE: &str = r#"
mod nested {
    #[trust_vc::spec]
    pub fn model() -> bool { true }
}

#[trust_vc::when_used_as_spec(nested::model)]
fn exec_helper() -> bool { false }

#[trust_vc::ensures(exec_helper())]
fn qualified_when_used_as_spec_positive() {}
"#;

#[test]
fn qualified_when_used_as_spec_registers_exact_model() {
    let result = verify(
        QUALIFIED_WHEN_USED_AS_SPEC_POSITIVE,
        "qualified_when_used_as_spec_positive",
    )
    .unwrap_or_else(|error| panic!("qualified model should extract: {error}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "qualified when_used_as_spec should use its exact true model, got {result:?}"
    );
}

const BODY_ALIAS_TRANSITIVE_EXEC_SCOPE: &str = r#"
mod good {
    pub fn helper() -> bool { true }
}

mod bad {
    pub fn helper() -> bool { false }
}

fn wrapper() -> bool {
    use bad::helper as picked;
    picked()
}

#[trust_vc::ensures(result)]
fn target_exec_alias_scope() -> bool {
    use good::helper as picked;
    trust_vc::assert!(picked());
    wrapper()
}
"#;

#[test]
fn target_alias_map_cannot_resolve_a_transitive_exec_dependency() {
    let result = verify(BODY_ALIAS_TRANSITIVE_EXEC_SCOPE, "target_exec_alias_scope");
    assert!(
        result.is_err(),
        "a sibling helper's call must not inherit the target body's alias map, got {result:?}"
    );
}

const LEADING_COLON_BLOCK_ALIAS: &str = r#"
mod local_name {
    #[trust_vc::spec]
    pub fn truth() -> bool { true }
}

#[trust_vc::proof]
fn leading_colon_alias_is_not_crate_local() {
    use ::local_name::truth as alias;
    trust_vc::assert!(alias());
}
"#;

#[test]
fn leading_colon_block_alias_does_not_rebind_to_local_module() {
    let result = verify(
        LEADING_COLON_BLOCK_ALIAS,
        "leading_colon_alias_is_not_crate_local",
    );
    assert!(
        result.is_err(),
        "a leading-colon import must fail closed instead of resolving against a same-named local module, got {result:?}"
    );
}

const BLOCK_GLOB_SCOPE: &str = r#"
#[trust_vc::spec]
fn truth() -> bool { true }

mod nested {
    #[trust_vc::spec]
    pub fn truth() -> bool { false }
}

#[trust_vc::proof]
fn block_glob_cannot_fall_back_to_outer_function() {
    use nested::*;
    trust_vc::assert!(truth());
}
"#;

#[test]
fn block_glob_import_fails_closed_without_scope_indexed_exports() {
    let result = verify(
        BLOCK_GLOB_SCOPE,
        "block_glob_cannot_fall_back_to_outer_function",
    );
    assert!(
        result.is_err(),
        "a block glob must not let a bare call fall back to a same-spelled outer function, got {result:?}"
    );
}

const OPAQUE_UNIT_SIBLING_WITH_BLOCK_GLOB: &str = r#"
mod nested {
    pub fn external_effect() {}
}

fn unverified_unit_helper() {
    use nested::*;
    external_effect();
}

#[trust_vc::ensures(true)]
fn caller_does_not_observe_unit_helper_body() {
    unverified_unit_helper();
}
"#;

#[test]
fn unresolved_glob_in_unobservable_unit_sibling_stays_opaque() {
    let result = verify(
        OPAQUE_UNIT_SIBLING_WITH_BLOCK_GLOB,
        "caller_does_not_observe_unit_helper_body",
    )
    .unwrap_or_else(|error| panic!("opaque unit sibling should not poison its caller: {error}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "omitting an unobservable unit helper body should preserve the caller's tautological postcondition, got {result:?}"
    );
}

#[path = "source_name_resolution_soundness/sibling_contracts.rs"]
mod sibling_contracts;

const OBSERVABLE_SIBLING_WITH_BLOCK_GLOB: &str = r#"
mod nested {
    pub fn imported_value() -> bool { false }
}

fn observable_helper() -> bool {
    use nested::*;
    imported_value()
}

#[trust_vc::ensures(result)]
fn caller_observes_helper_result() -> bool {
    observable_helper()
}
"#;

#[test]
fn unresolved_glob_in_value_returning_sibling_still_fails_closed() {
    let result = verify(
        OBSERVABLE_SIBLING_WITH_BLOCK_GLOB,
        "caller_observes_helper_result",
    );
    assert!(
        result.is_err(),
        "a value-returning sibling body must not be omitted when its glob target is unresolved, got {result:?}"
    );
}

const PARAMETER_SHADOWS_BLOCK_ALIAS: &str = r#"
mod nested {
    #[trust_vc::spec]
    pub fn truth() -> bool { true }
}

#[trust_vc::ensures(result)]
fn parameter_shadows_block_alias(alias: bool) -> bool {
    use nested::truth as alias;
    alias()
}
"#;

#[test]
fn parameter_and_block_alias_collision_fails_closed() {
    let result = verify(
        PARAMETER_SHADOWS_BLOCK_ALIAS,
        "parameter_shadows_block_alias",
    );
    assert!(
        result.is_err(),
        "a parameter/import collision must fail closed instead of treating the value as a function, got {result:?}"
    );
}

const DUPLICATE_METHOD_NAMES: &str = r#"
struct Left;
struct Right;

impl Left {
    #[trust_vc::ensures(result)]
    fn duplicate(&self) -> bool { true }
}

impl Right {
    #[trust_vc::ensures(result)]
    fn duplicate(&self) -> bool { true }
}
"#;

#[test]
fn cli_name_lookup_rejects_duplicate_non_top_level_methods() {
    let result = verify(DUPLICATE_METHOD_NAMES, "duplicate");
    assert!(
        result.is_err(),
        "ambiguous CLI method spelling must fail closed, got {result:?}"
    );
}
