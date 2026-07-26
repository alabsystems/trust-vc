// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use quote::quote;

fn parse_and_expand(attr: TokenStream, item: TokenStream) -> String {
    let input: ItemFn = syn::parse2(item).expect("failed to parse function");
    expand_contract(attr, input).to_string()
}

#[test]
fn test_requires_expands_to_obligation() {
    let result = parse_and_expand(
        quote! { requires(x > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Requires"),
        "should contain Requires obligation, got: {result}"
    );
}

#[test]
fn test_ensures_without_returns_errors() {
    let result = parse_and_expand(
        quote! { ensures(ret > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "ensures without returns should produce compile_error, got: {result}"
    );
    assert!(
        result.contains("requires a returns() clause"),
        "error should explain the fix, got: {result}"
    );
}

#[test]
fn test_multiple_requires_conditions() {
    let result = parse_and_expand(
        quote! { requires(x > 0, x < 100) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    let count = result.matches("ObligationKind :: Requires").count();
    assert!(
        count >= 4,
        "expected at least 4 Requires obligation mentions for 2 conditions, got {count}"
    );
}

#[test]
fn test_requires_and_ensures_without_returns_errors() {
    let result = parse_and_expand(
        quote! { requires(x > 0), ensures(ret > x) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "ensures without returns should produce compile_error even with requires, got: {result}"
    );
}

#[test]
fn test_requires_and_ensures_with_returns_together() {
    let result = parse_and_expand(
        quote! { requires(x > 0), ensures(ret > x), returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(result.contains("ObligationKind :: Requires"));
    assert!(result.contains("ObligationKind :: Ensures"));
    assert!(result.contains("trust_vc :: returns"));
}

#[test]
fn test_returns_clause_emits_attribute() {
    let result = parse_and_expand(
        quote! { returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("trust_vc :: returns"),
        "should emit #[trust_vc::returns(ret)] attribute, got: {result}"
    );
}

#[test]
fn test_decreases_clause_emits_attribute() {
    let result = parse_and_expand(
        quote! { decreases(n) },
        quote! { fn factorial(n: u64) -> u64 { if n == 0 { 1 } else { n } } },
    );
    assert!(
        result.contains("trust_vc :: decreases"),
        "should emit #[trust_vc::decreases(n)] attribute, got: {result}"
    );
}

#[test]
fn test_full_contract_all_clauses() {
    let result = parse_and_expand(
        quote! {
            requires(x > 0),
            ensures(ret > x),
            returns(ret),
            decreases(x)
        },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(result.contains("ObligationKind :: Requires"));
    assert!(result.contains("ObligationKind :: Ensures"));
    assert!(result.contains("trust_vc :: returns"));
    assert!(result.contains("trust_vc :: decreases"));
}

#[test]
fn test_unknown_clause_errors() {
    let result = parse_and_expand(
        quote! { invariant(x > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "unknown clause should produce compile_error, got: {result}"
    );
}

#[test]
fn test_empty_requires_errors() {
    let result = parse_and_expand(
        quote! { requires() },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "empty requires should produce compile_error, got: {result}"
    );
}

#[test]
fn test_duplicate_returns_errors() {
    let result = parse_and_expand(
        quote! { returns(a), returns(b) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "duplicate returns should produce compile_error, got: {result}"
    );
}

#[test]
fn test_preserves_original_body() {
    let result = parse_and_expand(
        quote! { requires(x > 0) },
        quote! { fn foo(x: u32) -> u32 { let y = x + 1; y } },
    );
    assert!(
        result.contains("let y = x + 1"),
        "should preserve original body, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_captures_return_value() {
    let result = parse_and_expand(
        quote! { ensures(ret > 0), returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("let ret"),
        "should capture return value in `let ret`, got: {result}"
    );
    assert!(result.contains("ObligationKind :: Ensures"));
    assert!(result.contains("trust_vc :: returns"));
}

#[test]
fn test_returns_with_ensures_rewrites_early_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret > 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                if x < 0 {
                    return -1;
                }
                x + 1
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return - 1"),
        "outer early return should rewrite to a labeled break, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_match_arm_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 13u64), returns(ret) },
        quote! {
            fn foo(flag: bool) -> u64 {
                match flag {
                    true => {
                        return 11u64;
                    }
                    false => 13u64,
                }
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 11u64"),
        "match-arm early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("false => 13u64"),
        "non-returning match arm should remain as the normal arm value, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_loop_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 13u64), returns(ret) },
        quote! {
            fn foo(flag: bool) -> u64 {
                loop {
                    if flag {
                        return 11u64;
                    }
                    break;
                }
                13u64
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 11u64"),
        "loop-body early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("13u64"),
        "normal loop-exit tail return should remain present, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_while_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { requires(flag), ensures(ret == ()), returns(ret) },
        quote! {
            fn foo(flag: bool) {
                while flag || !flag {
                    trust_vc::invariant!(flag);
                    return;
                }
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return ()"),
        "unit return from a while body should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("trust_vc :: invariant ! (flag)"),
        "while-loop invariant should remain structurally present, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_local_initializer_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 17u64), returns(ret) },
        quote! {
            fn foo(flag: bool) -> u64 {
                let value: u64 = if flag {
                    return 11u64;
                } else {
                    17u64
                };
                value
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 11u64"),
        "local-initializer early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("let value : u64 = if flag"),
        "non-returning initializer path should remain in place, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_if_let_expression_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 13u64), returns(ret) },
        quote! {
            fn foo(maybe: Option<u64>) -> u64 {
                let value = if let Some(value) = maybe {
                    value
                } else {
                    return 13u64;
                };
                value
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 13u64"),
        "if-let expression early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("if let Some (value) = maybe"),
        "if-let expression should remain structurally present, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_let_else_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 13u64), returns(ret) },
        quote! {
            fn foo(maybe: Option<u64>) -> u64 {
                let Some(value) = maybe else {
                    return 13u64;
                };
                value
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 13u64"),
        "let-else early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("let Some (value) = maybe else"),
        "let-else local should remain structurally present, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_rewrites_call_argument_return_to_labeled_break() {
    let result = parse_and_expand(
        quote! { ensures(ret == 11u64 || ret == 17u64), returns(ret) },
        quote! {
            fn foo(flag: bool) -> u64 {
                identity_u64(if flag {
                    return 11u64;
                } else {
                    17u64
                })
            }
        },
    );

    assert!(
        result.contains("'__trust_vc_contract_return"),
        "should emit a labeled block for the named-return contract path, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return 11u64"),
        "call-argument early return should rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("identity_u64 (if flag"),
        "call argument expression should remain structurally present, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_skips_closure_return_rewrite() {
    let result = parse_and_expand(
        quote! { ensures(ret >= 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                let thunk = || -> i32 {
                    return 5;
                };
                if x < 0 {
                    return thunk();
                }
                thunk()
            }
        },
    );

    assert!(
        result.contains("break '__trust_vc_contract_return thunk ()"),
        "outer function early return should still rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("return 5"),
        "closure-local return should remain untouched, got: {result}"
    );
    assert!(
        !result.contains("break '__trust_vc_contract_return 5"),
        "closure-local return must not rewrite to the outer label, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_skips_nested_function_return_rewrite() {
    let result = parse_and_expand(
        quote! { ensures(ret >= 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                fn nested() -> i32 {
                    return 5;
                }
                if x < 0 {
                    return nested();
                }
                0
            }
        },
    );

    assert!(
        result.contains("break '__trust_vc_contract_return nested ()"),
        "outer function early return should still rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("return 5"),
        "nested-function return should remain untouched, got: {result}"
    );
    assert!(
        !result.contains("break '__trust_vc_contract_return 5"),
        "nested-function return must not rewrite to the outer label, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_skips_nested_impl_method_return_rewrite() {
    let result = parse_and_expand(
        quote! { ensures(ret >= 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                struct Local;
                impl Local {
                    fn value() -> i32 {
                        return 5;
                    }
                }
                if x < 0 {
                    return Local::value();
                }
                0
            }
        },
    );

    assert!(
        result.contains("break '__trust_vc_contract_return Local :: value ()"),
        "outer function early return should still rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("return 5"),
        "nested impl method return should remain untouched, got: {result}"
    );
    assert!(
        !result.contains("break '__trust_vc_contract_return 5"),
        "nested impl method return must not rewrite to the outer label, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_fails_closed_on_macro_return_tokens() {
    let result = parse_and_expand(
        quote! { ensures(ret == 13u64), returns(ret) },
        quote! {
            fn foo() -> u64 {
                early!(return 11u64);
                13u64
            }
        },
    );

    assert!(
        result.contains("compile_error"),
        "macro-hidden return should fail closed, got: {result}"
    );
    assert!(
        result.contains("return` inside a macro invocation is not supported"),
        "diagnostic should explain unsupported macro returns, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_allows_nested_item_macro_return_tokens() {
    let result = parse_and_expand(
        quote! { ensures(ret >= 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                struct Local;
                impl Local {
                    fn value() -> i32 {
                        early!(return 5)
                    }
                }
                if x < 0 {
                    return Local::value();
                }
                0
            }
        },
    );

    assert!(
        !result.contains("compile_error"),
        "nested-item macro return tokens should not be treated as outer returns, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return Local :: value ()"),
        "outer function early return should still rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("early ! (return 5)"),
        "nested item macro body should remain untouched, got: {result}"
    );
}

#[test]
fn test_returns_with_ensures_allows_closure_local_macro_return_tokens() {
    let result = parse_and_expand(
        quote! { ensures(ret >= 0), returns(ret) },
        quote! {
            fn foo(x: i32) -> i32 {
                let thunk = || -> i32 {
                    early!(return 5)
                };
                if x < 0 {
                    return thunk();
                }
                0
            }
        },
    );

    assert!(
        !result.contains("compile_error"),
        "closure-local macro return tokens should not be treated as outer returns, got: {result}"
    );
    assert!(
        result.contains("break '__trust_vc_contract_return thunk ()"),
        "outer function early return should still rewrite to the labeled break, got: {result}"
    );
    assert!(
        result.contains("early ! (return 5)"),
        "closure-local macro body should remain untouched, got: {result}"
    );
}

#[test]
fn test_returns_without_ensures_does_not_capture() {
    let result = parse_and_expand(
        quote! { returns(ret), requires(x > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        !result.contains("let ret ="),
        "should NOT capture return value when no ensures, got: {result}"
    );
}

#[test]
fn test_preserves_function_attributes() {
    let result = parse_and_expand(
        quote! { requires(x > 0) },
        quote! {
            #[inline]
            fn foo(x: u32) -> u32 { x + 1 }
        },
    );
    assert!(
        result.contains("inline"),
        "should preserve #[inline] attribute, got: {result}"
    );
}

#[test]
fn test_contract_old_capture_generates_bindings() {
    let result = parse_and_expand(
        quote! { ensures(ret == old!(x) + 1), returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );

    assert!(
        result.contains("let __trust_vc_old_x = x"),
        "should bind old!(x) before the body, got: {result}"
    );
    assert!(
        result.contains("ret == __trust_vc_old_x + 1"),
        "runtime ensures should use the rewritten old binding, got: {result}"
    );
}

#[test]
fn test_contract_old_deref_capture_generates_deref_binding() {
    let result = parse_and_expand(
        quote! { ensures(ret == old!(*x) + 1), returns(ret) },
        quote! { fn foo(x: &mut u32) -> u32 { *x + 1 } },
    );

    assert!(
        result.contains("let __trust_vc_old_x = * x"),
        "should bind old!(*x) by dereferencing before the body, got: {result}"
    );
}

#[test]
fn test_requires_only_empty_proof_contract_errors() {
    let result = parse_and_expand(
        quote! { requires(n > 0) },
        quote! {
            #[trust_vc::proof]
            fn lemma_positive(n: u32) {}
        },
    );

    assert!(
        result.contains("compile_error"),
        "requires-only empty proof contracts should fail closed, got: {result}"
    );
    assert!(
        result.contains("empty #[trust_vc::proof] bodies cannot use #[trust_vc::contract(requires(...))] without ensures(...)"),
        "diagnostic should explain the proof/contract vacuity, got: {result}"
    );
}

#[test]
fn test_requires_only_nonempty_proof_contract_still_expands() {
    let result = parse_and_expand(
        quote! { requires(n > 0) },
        quote! {
            #[trust_vc::proof]
            fn lemma_positive(n: u32) {
                trust_vc::assert!(n > 0);
            }
        },
    );

    assert!(
        !result.contains("compile_error"),
        "proof contracts with body assertions should still expand, got: {result}"
    );
    assert!(
        result.contains("ObligationKind :: Requires"),
        "the requires clause should still lower into the body, got: {result}"
    );
}

#[test]
fn test_recommends_expands_to_obligation() {
    let result = parse_and_expand(
        quote! { recommends(x > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Recommends"),
        "should contain Recommends obligation, got: {result}"
    );
}

#[test]
fn test_recommends_with_requires_both_expand() {
    let result = parse_and_expand(
        quote! { requires(x < 100), recommends(x > 0) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Requires"),
        "requires should expand, got: {result}"
    );
    assert!(
        result.contains("ObligationKind :: Recommends"),
        "recommends should expand, got: {result}"
    );
}

#[test]
fn test_empty_recommends_errors() {
    let result = parse_and_expand(
        quote! { recommends() },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "empty recommends should produce compile_error, got: {result}"
    );
}

#[test]
fn test_recommends_in_returns_ensures_path() {
    let result = parse_and_expand(
        quote! { recommends(x > 0), ensures(ret > 0), returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Recommends"),
        "recommends should expand in returns+ensures path, got: {result}"
    );
    assert!(
        result.contains("ObligationKind :: Ensures"),
        "ensures should expand in returns+ensures path, got: {result}"
    );
}

// -- cite clause -------------------------------------------------------------

#[test]
fn test_cite_without_reference_expands_to_trusted_assume() {
    // (a)+(b): cite(expr) parses and lowers to a TRUSTED `Assume` obligation —
    // the cited fact is assumed, never proven.
    let result = parse_and_expand(
        quote! { cite(monotone(x)) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Assume"),
        "cite should lower to a trusted Assume obligation, got: {result}"
    );
    // SOUNDNESS: a cited fact must NOT become an asserted/proven obligation.
    assert!(
        !result.contains("ObligationKind :: Assert"),
        "cite must not produce an Assert obligation, got: {result}"
    );
    assert!(
        !result.contains("ObligationKind :: Requires"),
        "cite must not produce a Requires obligation, got: {result}"
    );
    assert!(
        !result.contains("ObligationKind :: Ensures"),
        "cite must not produce an Ensures obligation, got: {result}"
    );
    assert!(
        !result.contains("compile_error"),
        "cite(expr) should expand cleanly, got: {result}"
    );
}

#[test]
fn test_cite_with_string_reference_embeds_provenance() {
    // (a): cite(expr, "ref") parses and expands, surfacing the citation.
    let result = parse_and_expand(
        quote! { cite(monotone(x), "proofs::lemma_4_2") },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Assume"),
        "cite with reference should still be a trusted Assume, got: {result}"
    );
    assert!(
        result.contains("proofs::lemma_4_2"),
        "the citation reference should be surfaced in the expansion, got: {result}"
    );
}

#[test]
fn test_cite_with_path_reference_expands() {
    // The citation reference may be a path to an external proof/lemma/source.
    let result = parse_and_expand(
        quote! { cite(monotone(x), proofs::seq::len_nonneg) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Assume"),
        "cite with a path reference should be a trusted Assume, got: {result}"
    );
    assert!(
        !result.contains("compile_error"),
        "a path citation reference should be accepted, got: {result}"
    );
}

#[test]
fn test_contract_with_only_cite_is_accepted() {
    // (d): a contract whose sole clause is `cite` must be accepted.
    let result = parse_and_expand(
        quote! { cite(monotone(x), "ref") },
        quote! { fn foo(x: u32) -> u32 { let y = x + 1; y } },
    );
    assert!(
        !result.contains("compile_error"),
        "a contract with only a cite clause should be accepted, got: {result}"
    );
    assert!(
        result.contains("ObligationKind :: Assume"),
        "the cited fact should still lower to a trusted Assume, got: {result}"
    );
    assert!(
        result.contains("let y = x + 1"),
        "the original body should be preserved, got: {result}"
    );
}

#[test]
fn test_cite_empty_args_errors() {
    let result = parse_and_expand(
        quote! { cite() },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("compile_error"),
        "cite() with no fact should produce a compile_error, got: {result}"
    );
}

#[test]
fn test_cite_in_returns_ensures_path() {
    // cite is injected before the body even on the returns+ensures path.
    let result = parse_and_expand(
        quote! { cite(monotone(x), "ref"), ensures(ret > 0), returns(ret) },
        quote! { fn foo(x: u32) -> u32 { x + 1 } },
    );
    assert!(
        result.contains("ObligationKind :: Assume"),
        "cite should expand in the returns+ensures path, got: {result}"
    );
    assert!(
        result.contains("ObligationKind :: Ensures"),
        "ensures should still expand alongside cite, got: {result}"
    );
}

#[test]
fn test_contract_error_message_lists_cite() {
    // (c): the "at least one clause" diagnostic now lists `cite`.
    let result = parse_and_expand(quote! {}, quote! { fn foo(x: u32) -> u32 { x + 1 } });
    assert!(
        result.contains("compile_error"),
        "an empty contract should fail closed, got: {result}"
    );
    assert!(
        result.contains("cite"),
        "the contract clause diagnostic should list `cite`, got: {result}"
    );
}
