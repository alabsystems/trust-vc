// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use quote::quote;

#[test]
fn test_extract_simple_range() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for i in 0..n {
            sum += i;
        }
    })
    .unwrap();

    let info = try_extract_for_range(&expr).expect("should detect for i in 0..n");
    assert_eq!(info.iter_var, "i");
    assert_eq!(info.lo_str, "0");
    assert_eq!(info.hi_ident.as_deref(), Some("n"));
    assert!(!info.inclusive);
    assert!(info.body_modified.contains(&"sum".to_string()));
}

#[test]
fn test_extract_non_range_returns_none() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for x in items.iter() {
            do_something(x);
        }
    })
    .unwrap();

    assert!(
        try_extract_for_range(&expr).is_none(),
        "iterator-based loop should not match"
    );
}

#[test]
fn test_extract_complex_pattern_returns_none() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for (a, b) in 0..10 {
            sum += a;
        }
    })
    .unwrap();

    assert!(
        try_extract_for_range(&expr).is_none(),
        "tuple pattern should not match"
    );
}

#[test]
fn test_fold_wraps_range_loop() {
    let block: syn::Block = syn::parse2(quote! {
        {
            for i in 0..n {
                sum += i;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("LoopContextGuard"),
        "folded block should contain LoopContextGuard: {output}"
    );
    assert!(
        output.contains("collect_variable_from_ref"),
        "folded block should declare the iterator from the upper-bound type: {output}"
    );
    assert!(
        output.contains("auto_range_bound"),
        "folded block should contain auto range bound invariant: {output}"
    );
    assert!(
        output.contains("0 <= i"),
        "folded block should encode the inferred lower-bound invariant: {output}"
    );
    assert!(
        output.contains("\"sum\""),
        "folded block should include body-modified vars in loop metadata: {output}"
    );
    assert!(
        output.contains("auto_loop_exit"),
        "folded block should contain auto loop exit fact: {output}"
    );
    assert!(
        output.contains("i == n"),
        "folded block should encode the loop exit fact for the iterator: {output}"
    );
}

#[test]
fn test_fold_preserves_non_range_loop() {
    let block: syn::Block = syn::parse2(quote! {
        {
            for x in items.iter() {
                process(x);
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        !output.contains("LoopContextGuard"),
        "non-range loop should not be wrapped: {output}"
    );
}

#[test]
fn test_collect_assigned_vars() {
    let block: syn::Block = syn::parse2(quote! {
        {
            sum += i;
            count = count + 1;
            let temp = 5;
        }
    })
    .unwrap();

    let vars = collect_assigned_vars(&block);
    assert!(vars.contains(&"sum".to_string()));
    assert!(vars.contains(&"count".to_string()));
    // `let temp = 5` is a let binding, not an assignment
    assert!(!vars.contains(&"temp".to_string()));
}

// === Phase 2 tests (P1: literal suffix, P2: inclusive, P3: while, P4: nested) ===

/// P1: literal suffix type inference — `0usize..10usize` yields `usize` type.
#[test]
fn test_extract_literal_suffix_type() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for i in 0usize..10usize {
            sum += i;
        }
    })
    .unwrap();

    let info = try_extract_for_range(&expr).expect("should detect for i in 0usize..10usize");
    assert_eq!(info.literal_suffix_type.as_deref(), Some("usize"));
}

/// P1: literal suffix from lo when hi has no suffix.
#[test]
fn test_extract_literal_suffix_from_lo() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for i in 0u64..n {
            x = i;
        }
    })
    .unwrap();

    let info = try_extract_for_range(&expr).expect("should detect range");
    // hi is an ident (n), so no suffix there; but lo has u64
    assert_eq!(info.literal_suffix_type.as_deref(), Some("u64"));
}

/// P1: codegen uses literal suffix type in collect_variable call.
#[test]
fn test_fold_literal_suffix_type_emits_collect_variable() {
    let block: syn::Block = syn::parse2(quote! {
        {
            for i in 0..10usize {
                sum += i;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("\"usize\""),
        "folded block should emit collect_variable with usize type: {output}"
    );
    // Should NOT use collect_variable_from_ref since hi is a literal
    assert!(
        !output.contains("collect_variable_from_ref"),
        "literal hi should NOT use collect_variable_from_ref: {output}"
    );
}

/// P2: inclusive range `lo..=hi` emits correct guard (`i <= hi`).
#[test]
fn test_extract_inclusive_range() {
    let expr: ExprForLoop = syn::parse2(quote! {
        for i in 0..=n {
            sum += i;
        }
    })
    .unwrap();

    let info = try_extract_for_range(&expr).expect("should detect inclusive range");
    assert!(info.inclusive);
}

/// P2: inclusive range codegen emits `i <= n` guard (not `i < n`).
#[test]
fn test_fold_inclusive_range_emits_correct_guard() {
    let block: syn::Block = syn::parse2(quote! {
        {
            for i in 0..=n {
                sum += i;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("i <= n"),
        "inclusive range should emit guard 'i <= n': {output}"
    );
}

/// P3: while loop wraps with LoopContextGuard containing guard + modified vars.
#[test]
fn test_fold_wraps_while_loop() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while x < 10 {
                x += 1;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("LoopContextGuard"),
        "while loop should be wrapped with LoopContextGuard: {output}"
    );
    assert!(
        output.contains("x < 10"),
        "while loop guard should be captured: {output}"
    );
    assert!(
        output.contains("\"x\""),
        "while loop body-modified var x should be in metadata: {output}"
    );
    // while loops should NOT have auto range bounds, but pure no-break boolean
    // while loops do get a normal-exit fact even without a direct invariant.
    assert!(
        !output.contains("auto_range_bound"),
        "while loop should NOT have auto range bound: {output}"
    );
    assert!(
        output.contains("auto_while_exit"),
        "pure no-break while loop should have auto loop exit: {output}"
    );
    assert!(
        output.contains("!(x < 10)"),
        "normal-exit fact should negate the guard: {output}"
    );
}

/// P3: while loop with a direct invariant also emits a normal-exit assumption.
#[test]
fn test_fold_while_with_invariant_emits_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while i < limit {
                trust_vc::invariant!(limit == 10u64);
                i += 1u64;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("auto_while_exit"),
        "while loop with invariant should emit normal-exit fact: {output}"
    );
    assert!(
        output.contains("!(i < limit)"),
        "normal-exit fact should negate the loop guard: {output}"
    );
}

/// P3: a break-capable while loop must not assume that the guard is false.
#[test]
fn test_fold_while_with_break_skips_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while i < limit {
                trust_vc::invariant!(limit == 10u64);
                if stop {
                    break;
                }
                i += 1u64;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        !output.contains("auto_while_exit"),
        "while loop with break should not emit normal-exit fact: {output}"
    );
}

/// Upstream `while_b2`: a break from a nested loop does not exit the outer
/// while, so the outer while may still contribute its normal-exit fact.
#[test]
fn test_fold_while_with_nested_break_keeps_outer_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while b {
                while b {
                    break;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    let exit_count = output.matches("auto_while_exit").count();
    assert_eq!(
        exit_count, 1,
        "only the outer while should emit a normal-exit fact, found {exit_count}: {output}"
    );
    assert!(
        output.contains("!(b)"),
        "outer normal-exit fact should negate the boolean guard: {output}"
    );
}

/// Upstream `while_b2_y`: a labeled break targeting the inner loop does not
/// exit the outer while, so it must not suppress the outer normal-exit fact.
#[test]
fn test_fold_while_with_labeled_nested_break_keeps_outer_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while b {
                'y: while b {
                    break 'y;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    let exit_count = output.matches("auto_while_exit").count();
    assert_eq!(
        exit_count, 1,
        "labeled inner break should not suppress the outer exit fact, found {exit_count}: {output}"
    );
}

/// Upstream `while_b2_x`: a labeled break targeting the outer while exits that
/// loop, so the outer guard must not be assumed false after the loop.
#[test]
fn test_fold_while_with_labeled_break_to_outer_skips_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            'x: while b {
                'y: while b {
                    break 'x;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        !output.contains("auto_while_exit"),
        "break to outer while should suppress normal-exit facts: {output}"
    );
}

/// P3: an impure while guard must not assume that the guard is false.
#[test]
fn test_fold_while_with_impure_guard_skips_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while iter.next().is_some() {
                i += 1u64;
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        !output.contains("auto_while_exit"),
        "while loop with impure guard should not emit normal-exit fact: {output}"
    );
}

/// Bare `loop {}` gets metadata for invariants but no normal-exit fact.
#[test]
fn test_fold_wraps_bare_loop_without_exit_fact() {
    let block: syn::Block = syn::parse2(quote! {
        {
            loop {
                trust_vc::invariant!(limit == 10u64);
                i += 1u64;
                if i == 1u64 {
                    break;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        output.contains("LoopContextGuard"),
        "bare loop should be wrapped with LoopContextGuard: {output}"
    );
    assert!(
        output.contains("\"i\""),
        "bare loop body-modified var i should be in metadata: {output}"
    );
    assert!(
        !output.contains("auto_while_exit") && !output.contains("auto_loop_exit"),
        "bare loop should not emit a normal-exit fact: {output}"
    );
}

/// P3: `while let` is NOT wrapped (no simple condition guard).
#[test]
fn test_fold_preserves_while_let() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while let Some(x) = items.pop() {
                process(x);
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    assert!(
        !output.contains("LoopContextGuard"),
        "while let should not be wrapped: {output}"
    );
}

/// P4: nested for-range loops each get their own wrapper.
#[test]
fn test_fold_nested_range_loops() {
    let block: syn::Block = syn::parse2(quote! {
        {
            for i in 0..n {
                for j in 0..m {
                    sum += i + j;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    // Both loops should have their own guard
    let guard_count = output.matches("LoopContextGuard").count();
    assert_eq!(
        guard_count, 2,
        "nested loops should each have a LoopContextGuard, found {guard_count}: {output}"
    );
}

/// P4: nested while + for-range loops both get wrappers.
#[test]
fn test_fold_nested_while_and_for_range() {
    let block: syn::Block = syn::parse2(quote! {
        {
            while x < 100 {
                for i in 0..n {
                    x += i;
                }
            }
        }
    })
    .unwrap();

    let folded = fold_with_range_inference(&block);
    let output = quote!(#folded).to_string();

    let guard_count = output.matches("LoopContextGuard").count();
    assert_eq!(
        guard_count, 2,
        "nested while + for should each have a guard, found {guard_count}: {output}"
    );
}
