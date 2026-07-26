// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---- String-based rewrite tests ----

#[test]
fn test_replace_whole_word_basic() {
    assert_eq!(replace_whole_word("x > 0", "x", "x_pre"), "x_pre > 0");
}

#[test]
fn test_replace_whole_word_no_partial() {
    // "idx" should NOT be affected when replacing "i"
    assert_eq!(replace_whole_word("idx > i", "i", "i_pre"), "idx > i_pre");
}

#[test]
fn test_replace_whole_word_multiple() {
    assert_eq!(
        replace_whole_word("x + x > 0", "x", "x_pre"),
        "x_pre + x_pre > 0"
    );
}

#[test]
fn test_replace_whole_word_empty() {
    assert_eq!(replace_whole_word("x > 0", "", "y"), "x > 0");
}

#[test]
fn test_replace_whole_word_adjacent_underscores() {
    // "x_old" should NOT be matched when replacing "x"
    assert_eq!(
        replace_whole_word("x_old > x", "x", "x_pre"),
        "x_old > x_pre"
    );
}

/// Non-ASCII UTF-8 test: variable names are ASCII but condition text
/// contains multi-byte characters. The function must not corrupt
/// multi-byte codepoints. Fixes #1655.
#[test]
fn test_replace_whole_word_non_ascii_context() {
    // Greek alpha (U+03B1: 2 bytes 0xCE 0xB1) — must not corrupt
    assert_eq!(
        replace_whole_word("x + α > 0", "x", "x_pre"),
        "x_pre + α > 0"
    );
    // Non-ASCII char adjacent to underscore acts as word boundary
    assert_eq!(replace_whole_word("α > x", "x", "x_pre"), "α > x_pre");
    // Non-ASCII variable name as the word to replace
    assert_eq!(replace_whole_word("α > 0", "α", "α_pre"), "α_pre > 0");
    // 3-byte UTF-8: "∀" (U+2200: 0xE2 0x88 0x80)
    assert_eq!(replace_whole_word("∀ x > 0", "x", "x_pre"), "∀ x_pre > 0");
}

#[test]
fn test_replace_whole_word_non_ascii_identifier_boundary() {
    // Greek alpha inside αβ is part of a larger identifier and must not match.
    assert_eq!(
        replace_whole_word("αβ + α > 0", "α", "α_pre"),
        "αβ + α_pre > 0"
    );
}

#[test]
fn test_replace_vars_with_pre_basic() {
    let vars = vec![
        VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
    ];
    assert_eq!(
        replace_vars_with_pre("x + y > 0", &vars),
        "x__trust_vc_pre + y__trust_vc_pre > 0"
    );
}

#[test]
fn test_replace_vars_with_pre_longest_first() {
    let vars = vec![
        VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "idx".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
    ];
    assert_eq!(
        replace_vars_with_pre("idx > i", &vars),
        "idx__trust_vc_pre > i__trust_vc_pre"
    );
}

#[test]
fn test_replace_vars_with_pre_no_double_replace() {
    let vars = vec![VariableDecl {
        bounded_len: false,
        name: "n".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }];
    // Must be "n__trust_vc_pre > 0", NOT "n__trust_vc_pre__trust_vc_pre > 0"
    assert_eq!(replace_vars_with_pre("n > 0", &vars), "n__trust_vc_pre > 0");
}

/// User variable `x_pre` must NOT collide with the pre-state of `x` (#1728).
#[test]
fn test_replace_vars_with_pre_no_user_collision() {
    let vars = vec![
        VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "x_pre".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
    ];
    // x → x__trust_vc_pre, x_pre → x_pre__trust_vc_pre (distinct symbols)
    let result = replace_vars_with_pre("x > x_pre", &vars);
    assert!(
        result.contains("x__trust_vc_pre") && result.contains("x_pre__trust_vc_pre"),
        "pre-state of 'x' and user variable 'x_pre' must map to distinct symbols, got: {}",
        result
    );
}
