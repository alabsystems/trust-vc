//! Integration tests for extract_local_variables, choose!/arbitrary! symbolic
//! binding coverage, and wrapper-local/arbitrary no-runtime-capture regressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- extract_local_variables integration tests ---

#[test]
fn test_extract_typed_let_binding() {
    let block: syn::Block = syn::parse_str("{ let x: i32 = 5; }").unwrap();
    let result = extract_local_variables(&block);
    assert!(
        !result.pre_block.is_empty(),
        "Should produce pre_block declarations"
    );
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "Should register variable"
    );
    assert!(
        pre_str.contains("collect_let_binding"),
        "Should add let-binding constraint for literal"
    );
}

#[test]
fn test_extract_untyped_literal_infers_i32() {
    let block: syn::Block = syn::parse_str("{ let x = 42; }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "Should register with inferred type"
    );
    assert!(
        pre_str.contains("\"i32\""),
        "Should infer i32 for unsuffixed integer"
    );
}

#[test]
fn test_extract_untyped_char_literal_infers_char() {
    let block: syn::Block = syn::parse_str("{ let ch = 'a'; }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "char literal should register a variable"
    );
    assert!(
        pre_str.contains("\"char\""),
        "char literal should infer char"
    );
}

#[test]
fn test_extract_string_literal_fails_closed() {
    let block: syn::Block = syn::parse_str("{ let s = \"hello\"; }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("string literals are not yet supported"),
        "string literals should emit a compile_error guard"
    );
    assert!(
        !pre_str.contains("collect_variable"),
        "string literals must not silently register symbolic locals"
    );
}

#[test]
fn test_extract_untyped_variable_ref_infers_from_ref() {
    let block: syn::Block = syn::parse_str("{ let y = x; }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable_from_ref"),
        "Should use ref inference for variable refs"
    );
}

#[test]
fn test_extract_function_call_triggers_runtime_capture() {
    let block: syn::Block = syn::parse_str("{ let result: i32 = foo(5); }").unwrap();
    let result = extract_local_variables(&block);
    // Function call is not encodable, so no let-binding constraint in pre_block
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "Should register variable"
    );
    assert!(
        !pre_str.contains("collect_let_binding"),
        "Should NOT add let-binding for fn call"
    );
    // But the transformed block should have a runtime capture
    let block_str = result.transformed_block.to_string();
    assert!(
        block_str.contains("collect_let_binding_runtime_value"),
        "Transformed block should capture runtime value"
    );
}

#[test]
fn test_extract_deref_let_triggers_runtime_capture() {
    let block: syn::Block = syn::parse_str("{ let value: i32 = *x; }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "Should still register the declared variable"
    );
    assert!(
        !pre_str.contains("collect_let_binding"),
        "Dereference lets should not synthesize symbolic equality against the raw reference"
    );
    let block_str = result.transformed_block.to_string();
    assert!(
        block_str.contains("collect_let_binding_runtime_value"),
        "Dereference lets should fall back to runtime capture"
    );
}

#[test]
fn test_extract_empty_block() {
    let block: syn::Block = syn::parse_str("{ }").unwrap();
    let result = extract_local_variables(&block);
    assert!(
        result.pre_block.is_empty(),
        "Empty block should produce no declarations"
    );
}

#[test]
fn test_extract_non_let_statements_ignored() {
    let block: syn::Block = syn::parse_str("{ foo(); bar(); }").unwrap();
    let result = extract_local_variables(&block);
    assert!(
        result.pre_block.is_empty(),
        "Non-let statements should be ignored"
    );
}

#[test]
fn test_extract_skips_mut_ref_shadow_bindings() {
    let block: syn::Block = syn::parse_str(
        "{ let __trust_vc_mutref_counter_count_0 = counter.count; \
           ::trust_vc_core::verify_macro::collect_variable_runtime(\"__trust_vc_mutref_counter_count_0\", &__trust_vc_mutref_counter_count_0); }",
    )
    .unwrap();
    let result = extract_local_variables(&block);

    assert!(
        result.pre_block.is_empty(),
        "mut-ref synthetic lets should be handled by mut_ref_proof directly"
    );
}

// --- choose! symbolic let-binding regression (#2486) ---

#[test]
fn test_extract_choose_let_stays_symbolic() {
    let block: syn::Block =
        syn::parse_str("{ let w: i32 = trust_vc::choose!(|x: i32| x >= 0); }").unwrap();
    let result = extract_local_variables(&block);
    let pre_str: String = result.pre_block.iter().map(|t| t.to_string()).collect();
    assert!(
        pre_str.contains("collect_variable"),
        "choose let-binding should register the variable"
    );
    assert!(
        pre_str.contains("collect_let_binding"),
        "choose let-binding should add symbolic let-binding constraint"
    );
    let block_str = result.transformed_block.to_string();
    assert!(
        !block_str.contains("collect_let_binding_runtime_value"),
        "choose let-binding must NOT produce runtime capture (it is symbolic)"
    );
}

// --- arbitrary! let-binding: no constraint, no runtime capture (#2518) ---

#[test]
fn test_arbitrary_let_binding_no_constraint() {
    let block: syn::Block = syn::parse_str("{ let x: i32 = trust_vc::arbitrary!(i32); }").unwrap();
    let result = extract_local_variables(&block);
    let block_str = result
        .pre_block
        .iter()
        .map(|t| t.to_string())
        .collect::<String>();
    assert!(
        block_str.contains("collect_variable"),
        "arbitrary let-binding must declare the variable"
    );
    assert!(
        !block_str.contains("collect_let_binding"),
        "arbitrary let-binding must NOT generate collect_let_binding constraint"
    );
    let transformed_str = result.transformed_block.to_string();
    assert!(
        !transformed_str.contains("collect_let_binding_runtime_value"),
        "arbitrary let-binding must NOT produce runtime capture"
    );
}

// --- Wrapper-local no-runtime-capture regressions ---

#[test]
fn test_proph_local_no_runtime_capture() {
    let block: syn::Block = syn::parse_str("{ let p: Proph<u64> = Proph::<u64>::new(); }").unwrap();
    let result = extract_local_variables(&block);
    let pre_block_str = result
        .pre_block
        .iter()
        .map(ToString::to_string)
        .collect::<String>();
    assert!(
        pre_block_str.contains("collect_variable"),
        "Proph let-binding must declare the SMT variable"
    );
    assert!(
        pre_block_str.contains("\"p\""),
        "Proph let-binding must keep the variable name"
    );
    assert!(
        pre_block_str.contains("\"u64\""),
        "Proph let-binding must erase to the inner SMT type"
    );
    let transformed_str = result.transformed_block.to_string();
    assert!(
        !transformed_str.contains("collect_let_binding_runtime_value"),
        "Proph let-binding must skip runtime capture"
    );
    assert!(
        !transformed_str.contains("as i128"),
        "Proph let-binding must not emit primitive casts for wrapper values"
    );
}

#[test]
fn test_ghost_local_no_runtime_capture() {
    let block: syn::Block = syn::parse_str("{ let g: Ghost<u32> = Ghost::new(42); }").unwrap();
    let result = extract_local_variables(&block);
    let pre_block_str = result
        .pre_block
        .iter()
        .map(ToString::to_string)
        .collect::<String>();
    assert!(
        pre_block_str.contains("collect_variable"),
        "Ghost let-binding must declare the SMT variable"
    );
    assert!(
        pre_block_str.contains("\"g\""),
        "Ghost let-binding must keep the variable name"
    );
    assert!(
        pre_block_str.contains("\"u32\""),
        "Ghost let-binding must erase to the inner SMT type"
    );
    let transformed_str = result.transformed_block.to_string();
    assert!(
        !transformed_str.contains("collect_let_binding_runtime_value"),
        "Ghost let-binding must skip runtime capture"
    );
}

#[test]
fn test_tracked_local_no_runtime_capture() {
    let block: syn::Block = syn::parse_str("{ let t: Tracked<u32> = Tracked::new(42); }").unwrap();
    let result = extract_local_variables(&block);
    let pre_block_str = result
        .pre_block
        .iter()
        .map(ToString::to_string)
        .collect::<String>();
    assert!(
        pre_block_str.contains("collect_variable"),
        "Tracked let-binding must declare the SMT variable"
    );
    assert!(
        pre_block_str.contains("\"t\""),
        "Tracked let-binding must keep the variable name"
    );
    assert!(
        pre_block_str.contains("\"u32\""),
        "Tracked let-binding must erase to the inner SMT type"
    );
    let transformed_str = result.transformed_block.to_string();
    assert!(
        !transformed_str.contains("collect_let_binding_runtime_value"),
        "Tracked let-binding must skip runtime capture"
    );
}

#[test]
fn test_qualified_proph_local_no_runtime_capture() {
    let block: syn::Block = syn::parse_str(
        "{ let p: trust_vc_types::Proph<u64> = trust_vc_types::Proph::<u64>::new(); }",
    )
    .unwrap();
    let result = extract_local_variables(&block);
    let pre_block_str = result
        .pre_block
        .iter()
        .map(ToString::to_string)
        .collect::<String>();
    assert!(
        pre_block_str.contains("collect_variable"),
        "qualified Proph let-binding must declare the SMT variable"
    );
    assert!(
        pre_block_str.contains("\"p\""),
        "qualified Proph let-binding must keep the variable name"
    );
    assert!(
        pre_block_str.contains("\"u64\""),
        "qualified Proph let-binding must erase to the inner SMT type"
    );
    let transformed_str = result.transformed_block.to_string();
    assert!(
        !transformed_str.contains("collect_let_binding_runtime_value"),
        "qualified Proph let-binding must skip runtime capture"
    );
    assert!(
        !transformed_str.contains("as i128"),
        "qualified Proph let-binding must not emit primitive casts for wrapper values"
    );
}
