// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for pointer-width detection in verification units.
//!
//! A suffixed numeric literal is one `TokenTree::Literal`; `usize`/`isize` is
//! not emitted as a separate identifier. These cases ensure suffix-only units
//! are checked at both 32 and 64 bits, while portable arithmetic still passes.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/usize_literal_suffix_dual_width_soundness");
    fs::create_dir_all(dir).unwrap();
    let file = dir.join(format!("{name}.rs"));
    fs::write(&file, code).unwrap();
    verify_function_from_file(file.to_str().unwrap(), name)
        .unwrap_or_else(|error| panic!("{name} should extract and verify: {error}"))
}

fn assert_not_verified(code: &str, name: &str) {
    let result = verify(code, name);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{name}: a pointer-width-dependent claim false at 32 bits must not verify, got {result:?}"
    );
}

fn assert_verified(code: &str, name: &str) {
    let result = verify(code, name);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{name}: a claim true at both pointer widths must verify, got {result:?}"
    );
}

#[test]
fn shift_literal_overflow_eq_not_verified() {
    assert_not_verified(
        r#"
fn shift_literal_overflow_eq_not_verified() {
    trust_vc::assert!((1usize << 40u32) == 1099511627776usize);
}
"#,
        "shift_literal_overflow_eq_not_verified",
    );
}

#[test]
fn shift_literal_overflow_ge_not_verified() {
    assert_not_verified(
        r#"
fn shift_literal_overflow_ge_not_verified() {
    trust_vc::assert!((1usize << 40u32) >= 1usize);
}
"#,
        "shift_literal_overflow_ge_not_verified",
    );
}

#[test]
fn mul_literal_overflow_eq_not_verified() {
    assert_not_verified(
        r#"
fn mul_literal_overflow_eq_not_verified() {
    trust_vc::assert!((1000000usize * 1000000usize) == 1000000000000usize);
}
"#,
        "mul_literal_overflow_eq_not_verified",
    );
}

#[test]
fn mul_literal_overflow_ge_not_verified() {
    assert_not_verified(
        r#"
fn mul_literal_overflow_ge_not_verified() {
    trust_vc::assert!((1000000usize * 1000000usize) >= 1000000usize);
}
"#,
        "mul_literal_overflow_ge_not_verified",
    );
}

#[test]
fn isize_literal_suffix_overflow_not_verified() {
    assert_not_verified(
        r#"
fn isize_literal_suffix_overflow_not_verified() {
    trust_vc::assert!((1isize << 40u32) == 1099511627776isize);
}
"#,
        "isize_literal_suffix_overflow_not_verified",
    );
}

#[test]
fn shift_literal_in_range_eq_still_verifies() {
    assert_verified(
        r#"
fn shift_literal_in_range_eq_still_verifies() {
    trust_vc::assert!((1usize << 4u32) == 16usize);
}
"#,
        "shift_literal_in_range_eq_still_verifies",
    );
}

#[test]
fn mul_literal_in_range_eq_still_verifies() {
    assert_verified(
        r#"
fn mul_literal_in_range_eq_still_verifies() {
    trust_vc::assert!((1000usize * 1000usize) == 1000000usize);
}
"#,
        "mul_literal_in_range_eq_still_verifies",
    );
}

#[test]
fn add_literal_in_range_eq_still_verifies() {
    assert_verified(
        r#"
fn add_literal_in_range_eq_still_verifies() {
    trust_vc::assert!((1000usize + 2000usize) == 3000usize);
}
"#,
        "add_literal_in_range_eq_still_verifies",
    );
}

#[test]
fn isize_literal_in_range_eq_still_verifies() {
    assert_verified(
        r#"
fn isize_literal_in_range_eq_still_verifies() {
    trust_vc::assert!((1isize << 4u32) == 16isize);
}
"#,
        "isize_literal_in_range_eq_still_verifies",
    );
}
