// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS regression (round8 "charquant" findings 20/21): a quantifier whose
//! bound variable is typed `char` was given the bare `[0, 2^32)` range guard
//! (same as `u32`), omitting BOTH the U+10FFFF cap AND the UTF-16 surrogate-band
//! exclusion U+D800..=U+DFFF.
//!
//! Rust `char` is a Unicode scalar value, so no `char` exists with `(c as u32)`
//! in `0xD800..=0xDFFF` or above `0x10FFFF`. The missing guard let an existential
//! over a surrogate / out-of-range code point manufacture a spurious witness and
//! false-`Verify`, and DUALLY over-rejected the genuinely-true universal
//! `forall c. (c as u32) <= 0x10FFFF` (reported as a Counterexample).
//!
//! The fix applies the full Unicode scalar-validity predicate
//! `0 <= c <= 0x10FFFF && (c < 0xD800 || c > 0xDFFF)` to quantifier-bound `char`
//! vars (exists: `valid(c) && body`; forall: `valid(c) => body`). It must:
//!   * make every surrogate / above-cap EXISTENTIAL fail to verify, while
//!   * still verifying every in-domain (true) char existential (no
//!     over-rejection), and
//!   * verifying the genuinely-true char universals (fixing the dual
//!     over-rejection).

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ======================================================================
// GENUINELY FALSE char existentials -> must NEVER Verify.
// No char has a scalar value in the surrogate band or above U+10FFFF.
// ======================================================================

#[trust_vc::ensures(true)]
fn exists_surrogate_eq() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0xD800u32);
}

#[trust_vc::ensures(true)]
fn exists_surrogate_band() {
    trust_vc::assert!(exists|c: char| (c as u32) >= 0xD800u32 && (c as u32) <= 0xDFFFu32);
}

#[trust_vc::ensures(true)]
fn exists_surrogate_mid() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0xDABCu32);
}

#[trust_vc::ensures(true)]
fn exists_above_max() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0x110000u32);
}

// ======================================================================
// GENUINELY TRUE char existentials -> must STILL Verify (no over-rejection).
// Each target is a real Unicode scalar value.
// ======================================================================

#[trust_vc::ensures(true)]
fn exists_ascii_a() {
    trust_vc::assert!(exists|c: char| (c as u32) == 65u32);
}

#[trust_vc::ensures(true)]
fn exists_just_below_surrogate() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0xD799u32);
}

#[trust_vc::ensures(true)]
fn exists_just_above_surrogate() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0xE000u32);
}

#[trust_vc::ensures(true)]
fn exists_at_max() {
    trust_vc::assert!(exists|c: char| (c as u32) == 0x10FFFFu32);
}

// ======================================================================
// GENUINELY TRUE char universals -> must Verify (fixes the dual
// over-rejection; the bare [0, 2^32) guard wrongly admitted surrogate /
// above-cap witnesses and refuted these true universals).
// ======================================================================

#[trust_vc::ensures(true)]
fn forall_no_surrogate() {
    trust_vc::assert!(forall|c: char| (c as u32) != 0xD800u32);
}

#[trust_vc::ensures(true)]
fn forall_char_le_max() {
    trust_vc::assert!(forall|c: char| (c as u32) <= 0x10FFFFu32);
}

#[trust_vc::ensures(true)]
fn forall_not_in_band() {
    trust_vc::assert!(forall|c: char| (c as u32) < 0xD800u32 || (c as u32) > 0xDFFFu32);
}
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_charquant_{}_{}.rs",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, SOURCE).expect("write temp source");
    let result = verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{func} should verify-from-file without error: {e}"));
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn surrogate_and_above_cap_char_existentials_never_verify() {
    for f in [
        "exists_surrogate_eq",
        "exists_surrogate_band",
        "exists_surrogate_mid",
        "exists_above_max",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: no Rust char has a scalar value in the surrogate band or above \
             U+10FFFF, so this existential must NEVER verify, got {result:?}"
        );
    }
}

#[test]
fn in_domain_char_existentials_still_verify() {
    // No over-rejection: a char existential whose target IS a Unicode scalar
    // value (ASCII 'A', just below/above the surrogate band, and the maximum
    // code point) must continue to verify — proving the fix narrows the domain
    // rather than rejecting all char existentials.
    for f in [
        "exists_ascii_a",
        "exists_just_below_surrogate",
        "exists_just_above_surrogate",
        "exists_at_max",
    ] {
        let result = verify(f);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{f}: a char existential over an in-domain scalar value must STILL \
             verify (no over-rejection), got {result:?}"
        );
    }
}

#[test]
fn true_char_universals_verify() {
    // The dual of the witness bug: the bare [0, 2^32) guard wrongly admitted a
    // surrogate / above-cap witness, so these genuinely-true universals were
    // over-rejected. With the scalar-validity guard they must verify.
    for f in [
        "forall_no_surrogate",
        "forall_char_le_max",
        "forall_not_in_band",
    ] {
        let result = verify(f);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{f}: a genuinely-true char universal must verify, got {result:?}"
        );
    }
}
