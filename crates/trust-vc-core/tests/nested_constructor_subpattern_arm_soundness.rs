// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nested constructor sub-patterns in statement `match` / `if let` arms (the
//! upstream adts.rs `matches_syntax_precedence_1` / `_2` shapes).
//!
//! SOUNDNESS: an UPPERCASE bare ident inside a constructor pattern
//! (`W(None)`, `Some(None)`) was counted as a plain binding, so the arm
//! condition was the outer tester alone and every later same-variant arm was
//! excluded through its prior negation — `match w { W(None) => {}, W(x) =>
//! assert!(false), .. }` VERIFIED. It is a refinement now: the arm has no
//! renderable condition and its assertions fire unguarded (fail closed).
//!
//! Only the false programs are pinned here. The exact nested-constructor arm
//! condition that would let the TRUE twins verify is a precision feature of
//! the syn lane, which is frozen, so the true twins stay in the fixture as
//! documentation and are not asserted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ncsa_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, SRC).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

/// Any answer but `Verified`: a refutation, or a fail-closed refusal.
fn assert_not_verified(id: &str, func: &str) {
    let r = verify(id, func);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "FALSE VERIFY: {func} must not verify: {r:?}"
    );
}

const SRC: &str = r#"
use trust_vc_types::nat;
enum AM {
    A1 { v: nat },
    A2 { v: nat },
}
enum BM {
    B1(AM),
    B2 { a: AM },
}
enum Opt {
    Some(u64),
    None,
}
enum Wrap {
    W(Opt),
    Nothing,
}
enum WrapStd {
    W(Option<u64>),
    Nothing,
}

#[trust_vc::requires(b matches BM::B1(a) ==> a matches AM::A1 { v } ==> v == 3)]
#[trust_vc::ensures(true)]
fn nested_arm_guarded_by_requires(b: BM) {
    match b {
        BM::B1(AM::A1 { v }) => trust_vc::assert!(v == 3),
        _ => (),
    }
}
#[trust_vc::requires(b matches BM::B1(a) ==> a matches AM::A1 { v } ==> v == 3)]
#[trust_vc::ensures(true)]
fn nested_arm_guarded_by_requires_liar(b: BM) {
    match b {
        BM::B1(AM::A1 { v }) => trust_vc::assert!(v == 4),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_first_arm_does_not_cover_sibling_liar(b: BM) {
    match b {
        BM::B1(AM::A1 { v }) => (),
        BM::B1(_) => trust_vc::assert!(false),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_wildcard_reachable_liar(b: BM) {
    match b {
        BM::B1(AM::A1 { v }) => (),
        _ => trust_vc::assert!(false),
    }
}
#[trust_vc::ensures(true)]
fn nested_struct_field_subpattern_exact() {
    let b = BM::B2 { a: AM::A2 { v: 7 } };
    match b {
        BM::B2 { a: AM::A1 { v } } => trust_vc::assert!(false),
        BM::B2 { a: AM::A2 { v } } => trust_vc::assert!(v == 7),
        _ => trust_vc::assert!(false),
    }
}
#[trust_vc::ensures(true)]
fn nested_struct_field_subpattern_exact_liar() {
    let b = BM::B2 { a: AM::A2 { v: 7 } };
    match b {
        BM::B2 { a: AM::A1 { v } } => (),
        BM::B2 { a: AM::A2 { v } } => trust_vc::assert!(v == 8),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_unit_variant_subpattern(w: Wrap) {
    match w {
        Wrap::W(Opt::None) => (),
        Wrap::W(Opt::Some(x)) => (),
        Wrap::Nothing => (),
    }
}
#[trust_vc::requires(w is W && (w matches Wrap::W(o) ==> o is Some))]
#[trust_vc::ensures(true)]
fn nested_unit_variant_arm_dead(w: Wrap) {
    match w {
        Wrap::W(Opt::None) => trust_vc::assert!(false),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_unit_variant_arm_live_liar(w: Wrap) {
    match w {
        Wrap::W(Opt::None) => trust_vc::assert!(false),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_literal_subpattern_stays_unguarded(w: Wrap) {
    match w {
        Wrap::W(Opt::Some(0)) => (),
        Wrap::W(Opt::Some(x)) => trust_vc::assert!(x != 0),
        _ => (),
    }
}
#[trust_vc::ensures(true)]
fn nested_if_let(b: BM) {
    if let BM::B1(AM::A2 { v }) = b {
        trust_vc::assert!(b is B1);
    }
}
#[trust_vc::ensures(true)]
fn nested_if_let_liar(b: BM) {
    if let BM::B1(AM::A2 { v }) = b {
        trust_vc::assert!(b is B2);
    }
}
#[trust_vc::ensures(true)]
fn uppercase_ident_subpattern_liar(w: WrapStd) {
    match w {
        WrapStd::W(None) => {}
        WrapStd::W(x) => trust_vc::assert!(false),
        WrapStd::Nothing => {}
    }
}
#[trust_vc::ensures(true)]
fn uppercase_ident_option_nested_liar(o: Option<Option<u64>>) {
    match o {
        Some(None) => {}
        Some(x) => trust_vc::assert!(false),
        None => {}
    }
}
#[trust_vc::ensures(true)]
fn uppercase_ident_option_nested_exact(o: Option<Option<u64>>) {
    match o {
        Some(None) => {}
        Some(x) => trust_vc::assert!(x.is_some()),
        None => {}
    }
}
"#;

#[test]
fn uppercase_ident_subpattern_is_a_refinement_not_a_binder() {
    assert_not_verified("u1", "uppercase_ident_subpattern_liar");
    assert_not_verified("u2", "uppercase_ident_option_nested_liar");
}

#[test]
fn nested_constructor_liars_never_verify() {
    for (id, func) in [
        ("n2", "nested_arm_guarded_by_requires_liar"),
        ("n3", "nested_first_arm_does_not_cover_sibling_liar"),
        ("n4", "nested_wildcard_reachable_liar"),
        ("s2", "nested_struct_field_subpattern_exact_liar"),
        ("s5", "nested_unit_variant_arm_live_liar"),
        ("i2", "nested_if_let_liar"),
        ("l1", "nested_literal_subpattern_stays_unguarded"),
    ] {
        assert_not_verified(id, func);
    }
}
