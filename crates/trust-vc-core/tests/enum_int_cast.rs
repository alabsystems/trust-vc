// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Row 483 (Numeric casts) slice: a fieldless C-like enum cast to an integer
//! (`Color::Green as u64`, `c as int`) now models the variant's
//! declaration-order discriminant. `enum_int_cast_desugar.rs` rewrites the cast
//! OPERAND — the enum expression — into an equal integer expression
//! (`<index>` for a literal constructor, `match c { V0 => 0, .. }` for an
//! enum-typed parameter), keeping the `as TARGET` so the existing int→TARGET
//! cast finishes the conversion.
//!
//! Discriminants follow Rust's exact rule — the explicit value where given, else
//! the previous discriminant + 1 (first defaulting to 0) — so `enum E { A = 5, B }`
//! models A→5, B→6, and `enum Mix { P, Q = 10, R }` models P→0, Q→10, R→11.
//!
//! CARDINAL SOUNDNESS: the rewrite reproduces Rust's discriminant assignment, so
//! the DECL-ORDER value of an explicitly-numbered variant (`E::A as u64 == 0`)
//! is REFUTED (the true discriminant is 5). An enum with a non-literal explicit
//! discriminant, or a duplicate discriminant, is excluded (fail-closed). A
//! parameter re-bound (shadowed) in the body is also excluded, since inside the
//! shadow `c` no longer denotes the enum.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_eic_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const DECL_ORDER: &str = r#"
enum Color { Red, Green, Blue }
// literal constructor, in an assert! macro body
#[trust_vc::ensures(true)]
fn lit() { trust_vc::assert!((Color::Green as u64) == 1u64); }
#[trust_vc::ensures(true)]
fn lit_liar() { trust_vc::assert!((Color::Green as u64) == 2u64); }
// enum-typed parameter, in an assert! body
#[trust_vc::requires(c == Color::Blue)]
#[trust_vc::ensures(true)]
fn var(c: Color) { trust_vc::assert!((c as u64) == 2u64); }
#[trust_vc::requires(c == Color::Blue)]
#[trust_vc::ensures(true)]
fn var_liar(c: Color) { trust_vc::assert!((c as u64) == 1u64); }
// spec-idiomatic `as int`, and the cast inside an ensures ATTRIBUTE. (A
// VARIABLE cast in a requires/ensures whose truth needs the reverse
// discriminant→variant or constructor-equality↔tester inference stays soundly
// fail-closed as a solver incompleteness; the assert-position `var` case above
// exercises the variable path where it completes.)
#[trust_vc::ensures(true)]
fn as_int() { trust_vc::assert!((Color::Red as int) == 0int); }
#[trust_vc::ensures((Color::Green as int) == 1int)]
fn in_ensures() {}
// exec return position
#[trust_vc::ensures(result == 1u64)]
fn ret() -> u64 { Color::Green as u64 }
"#;

const EXPLICIT_DISC: &str = r#"
enum E { A = 5, B }              // A=5, B=6 (implicit continuation)
enum Mix { P, Q = 10, R }        // P=0, Q=10, R=11
// Explicit discriminants model their TRUE value.
#[trust_vc::ensures(true)]
fn e_true() { trust_vc::assert!((E::A as u64) == 5u64); }
#[trust_vc::ensures(true)]
fn e_continuation() { trust_vc::assert!((E::B as u64) == 6u64); }
#[trust_vc::ensures(true)]
fn mix_r() { trust_vc::assert!((Mix::R as u64) == 11u64); }
// CARDINAL: the DECL-ORDER value of an explicitly-numbered variant is REFUTED
// (E::A's real discriminant is 5, not the ordinal 0).
#[trust_vc::ensures(true)]
fn decl_order_wrong() { trust_vc::assert!((E::A as u64) == 0u64); }
"#;

// An enum whose explicit discriminant is a non-literal const expression is
// EXCLUDED — its discriminant is not statically evaluable here, so the cast
// stays fail-closed rather than risk a wrong value.
const NON_LITERAL_DISC: &str = r#"
const K: isize = 7;
enum NL { A = K, B }
#[trust_vc::ensures(true)]
fn nl(x: NL) { trust_vc::assert!((NL::A as u64) == 7u64); }
"#;

const SHADOW: &str = r#"
enum Color { Red, Green, Blue }
// A parameter shadowed by a non-enum `let` must not be rewritten as a
// discriminant match — inside the shadow `c` is a u64. `9 as u64 == 9` is a
// plain integer cast and verifies on its own merits.
#[trust_vc::ensures(true)]
fn shadowed(c: Color) { let c = 9u64; trust_vc::assert!((c as u64) == 9u64); }
"#;

#[test]
fn fieldless_enum_to_int_verifies() {
    for f in ["lit", "var", "as_int", "in_ensures", "ret"] {
        assert!(
            verified(&verify(f, f, DECL_ORDER)),
            "`{f}`: a fieldless decl-order enum cast to int should model the variant's \
             declaration-order discriminant; got {:?}",
            verify(f, f, DECL_ORDER)
        );
    }
}

#[test]
fn fieldless_enum_to_int_liars_fail_closed() {
    for f in ["lit_liar", "var_liar"] {
        assert!(
            !verified(&verify(f, f, DECL_ORDER)),
            "CARDINAL: `{f}`: a false consequence of the discriminant must NOT verify"
        );
    }
}

#[test]
fn explicit_discriminant_enum_models_true_value() {
    for f in ["e_true", "e_continuation", "mix_r"] {
        assert!(
            verified(&verify(f, f, EXPLICIT_DISC)),
            "`{f}`: an explicitly-numbered fieldless enum should model its true \
             discriminant; got {:?}",
            verify(f, f, EXPLICIT_DISC)
        );
    }
    // The load-bearing cardinal guard: the ORDINAL value of an explicitly-numbered
    // variant must be REFUTED (E::A's real discriminant is 5, not 0).
    assert!(
        !verified(&verify(
            "decl_order_wrong",
            "decl_order_wrong",
            EXPLICIT_DISC
        )),
        "CARDINAL: the declaration-order value of an explicitly-numbered variant \
         (`E::A as u64 == 0`) must NOT verify — its true discriminant is 5"
    );
}

#[test]
fn non_literal_discriminant_stays_fail_closed() {
    // `enum NL { A = K }` (K a const) is not statically evaluable here → excluded.
    assert!(
        !verified(&verify("nl", "nl", NON_LITERAL_DISC)),
        "CARDINAL: an enum with a non-literal explicit discriminant must stay \
         fail-closed (its value is not statically known to the desugar)"
    );
}

#[test]
fn shadowed_parameter_not_rewritten() {
    assert!(
        verified(&verify("shadowed", "shadowed", SHADOW)),
        "a parameter shadowed by a non-enum let must keep its shadow semantics \
         (`9 as u64 == 9`), not be rewritten as a discriminant match; got {:?}",
        verify("shadowed", "shadowed", SHADOW)
    );
}
