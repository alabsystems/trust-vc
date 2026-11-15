// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A type spelling that need not denote the type the syn lane reads it as.
//!
//! The lane reads type names as text. Two rules, one per shape of the hazard:
//!
//! 1. The receiver classifier (`single_typed_bindings`,
//!    `type_is_free_of_interior_mutability`, `immutable_value_params`) treats
//!    a type spelled like any generic type parameter of the file as a type
//!    parameter. `fn q6<u8: Display + PartialEq>(x: u8, y: u8)` names a type
//!    parameter, not the primitive, so `let p = x; p.to_string()` may change
//!    `p` through interior mutability and the binding is not kept.
//! 2. A file that rebinds a primitive type name (`type u64 = u8;`, `use
//!    core::primitive::u8 as u64;`, also in a body), renames a primitive type,
//!    or declares a generic type parameter spelled like a primitive, a
//!    modelled std type or a type of the file gets no `Verified` answer
//!    (`vc_extraction::type_name_rebinding`), and no step of its report is
//!    `Verified` either. A refutation is kept.
//!
//! Every liar below is well typed and false at run time: the `u64 = u8`
//! programs overflow a `u8` (checked with trustc, overflow checks on), and the
//! generic ones are false for a type whose `Display` bumps a `Cell` that its
//! `PartialEq` compares.

use trust_vc_core::proven_facts::extract_proven_facts;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, StepResultKind,
    VerificationReport, VerificationReportOptions, VerifyResult,
};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of rule 2 starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_type_name_rebinding_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false claim refuted with a counterexample.
    Counterexample,
    /// Refused by rule 2: an `Error` carrying the tag.
    Refused,
    /// Refused before any verdict, by something other than rule 2.
    FailClosedUntagged,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn matches_expect(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match expect {
        Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
        Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        Expect::Refused => {
            matches!(r, Ok(VerifyResult::Error { message }) if message.starts_with(TAG))
        }
        Expect::FailClosedUntagged => match r {
            Ok(VerifyResult::Error { message }) => !message.contains(TAG),
            Err(message) => !message.contains(TAG),
            _ => false,
        },
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = matches_expect(&r, *expect);
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Counterexample, FailClosedUntagged, Refused, Verified};

// ---------------------------------------------------------------- rule 1

/// Type parameters spelled like a primitive or a file struct, on a function
/// and on a method.
const SRC_GENERIC_RECEIVER: &str = r#"
#![allow(dead_code, unused, unused_mut, non_camel_case_types)]
use std::fmt::Display;

struct W {
    o: Option<u64>,
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q6_generic_named_u8_liar<u8: Display + PartialEq>(x: u8, y: u8) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q7_generic_named_t_twin<T: Display + PartialEq>(x: T, y: T) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q9_generic_named_file_struct_liar<W: Display + PartialEq>(x: W, y: W) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q10_generic_named_bool_liar<bool: Display + PartialEq>(x: bool, y: bool) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}

struct H;
impl H {
    #[trust_vc::requires(x == y)]
    #[trust_vc::ensures(true)]
    fn q11_method_generic_named_u64_liar<u64: Display + PartialEq>(&self, x: u64, y: u64) {
        let p = x;
        let _s = p.to_string();
        trust_vc::assert!(p == y);
    }
}
"#;

/// A type parameter spelled like a file struct, in a file with no parameter
/// spelled like a primitive. Rule 2 refuses this file too (the generic `W`
/// shadows `struct W`), but the classifier fails closed first.
const SRC_FILE_STRUCT_GENERIC: &str = r#"
#![allow(dead_code, unused, unused_mut)]
use std::fmt::Display;

struct W {
    o: Option<u64>,
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q9_generic_named_file_struct_liar<W: Display + PartialEq>(x: W, y: W) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}
"#;

/// The real primitive, in a file with no type parameter spelled like it.
const SRC_REAL_PRIMITIVE: &str = r#"
#![allow(dead_code, unused, unused_mut)]

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q12_real_u8_ctrl(x: u8, y: u8) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p == y);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn q12_real_u8_twin_cx(x: u8, y: u8) {
    let p = x;
    let _s = p.to_string();
    trust_vc::assert!(p != y);
}
"#;

/// Rule 1. Every liar fails closed in the classifier: the receiver is poisoned
/// (`unresolved variable p`), before any verdict, so rule 2 never sees one.
/// Measured with the generic-parameter check switched off (temporary code):
/// in `SRC_GENERIC_RECEIVER`, `q6`, `q9`, `q10` and `q11` reach `Verified` and
/// rule 2 refuses them (the file has parameters spelled `u8`, `bool`, `u64`);
/// in `SRC_FILE_STRUCT_GENERIC`, `q9` is `Verified` (rule 2 also refuses that
/// file, for its generic `W`). With both rules off all five are `Verified`. `q7` is the same
/// program with the parameter named
/// `T` and fails closed either way. `q12` is the real primitive and verifies;
/// its one-line twin is refuted.
#[test]
fn a_type_spelled_like_a_generic_parameter_is_not_classified() {
    check_table(
        SRC_GENERIC_RECEIVER,
        &[
            ("q6_generic_named_u8_liar", FailClosedUntagged),
            ("q7_generic_named_t_twin", FailClosedUntagged),
            ("q9_generic_named_file_struct_liar", FailClosedUntagged),
            ("q10_generic_named_bool_liar", FailClosedUntagged),
            ("q11_method_generic_named_u64_liar", FailClosedUntagged),
        ],
    );
    check_table(
        SRC_FILE_STRUCT_GENERIC,
        &[("q9_generic_named_file_struct_liar", FailClosedUntagged)],
    );
    check_table(
        SRC_REAL_PRIMITIVE,
        &[
            ("q12_real_u8_ctrl", Verified),
            ("q12_real_u8_twin_cx", Counterexample),
        ],
    );
}

// ---------------------------------------------------------------- rule 2

/// `type u64 = u8;`: the closure definition-site frame read `u64` as written.
const SRC_ALIAS: &str = r#"
#![allow(dead_code, unused, unused_mut, non_camel_case_types)]

type u64 = u8;

fn apply(g: impl Fn(u8) -> u8, a: u8) -> u8 {
    g(a)
}

#[trust_vc::ensures(true)]
fn c1_cast_seed_alias_liar(v: Vec<u8>, a: u8) {
    let _r = v.iter().fold(a as u64, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn c1_cast_seed_u8_twin_cx(v: Vec<u8>, a: u8) {
    let _r = v.iter().fold(a as u8, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e1_let_elem_alias_liar(v: Vec<u8>) {
    let w: Vec<u64> = v;
    let _r = w.iter().fold(0u8, |acc, x| x / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e1_let_elem_u8_twin_cx(v: Vec<u8>) {
    let w: Vec<u8> = v;
    let _r = w.iter().fold(0u8, |acc, x| x / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1_written_acc_alias_liar(v: Vec<u8>) {
    let _r = v.iter().fold(0u8, |acc: u64, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1_written_acc_u8_twin_cx(v: Vec<u8>) {
    let _r = v.iter().fold(0u8, |acc: u8, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w2_escaping_written_alias_liar(a: u8) {
    let g = |x: u64| x / 2 + 200;
    let _ = apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w2_escaping_written_u8_twin_cx(a: u8) {
    let g = |x: u8| x / 2 + 200;
    let _ = apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn g1_straightline_cast_alias_cx(a: u8) {
    let _y = (a as u64) / 2 + 200;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn f8_param_seed_alias_cx(v: Vec<u8>, a: u64) {
    let _r = v.iter().fold(a, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn t1_alias_true_claim(a: u8) {
    let y = (a as u64) / 2 + 100;
    trust_vc::assert!(y >= 100u8);
}
"#;

/// `use core::primitive::u8 as u64;` at file scope: no reader resolved it.
const SRC_USE_RENAME: &str = r#"
#![allow(dead_code, unused, unused_mut, non_camel_case_types)]
use core::primitive::u8 as u64;

#[trust_vc::ensures(true)]
fn g3_param_use_straightline(a: u64) {
    let y = a / 2 + 200;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn g4_cast_body_use_straightline(a: u8) {
    let y = (a as u64) / 2 + 200;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p1_param_file_use_liar(v: Vec<u8>, a: u64) {
    let _r = v.iter().fold(a, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p1_param_u8_cx(v: Vec<u8>, a: u8) {
    let _r = v.iter().fold(a, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}
"#;

/// The same rename inside a function body.
const SRC_BODY_USE_RENAME: &str = r#"
#![allow(dead_code, unused, unused_mut, non_camel_case_types)]

#[trust_vc::ensures(true)]
fn g5_cast_body_use_straightline(a: u8) {
    use core::primitive::u8 as u64;
    let y = (a as u64) / 2 + 200;
    trust_vc::assert!(true);
}
"#;

/// The alias inside a tuple component.
const SRC_TUPLE_ALIAS: &str = r#"
#![allow(dead_code, unused, unused_mut, non_camel_case_types)]

type u64 = u8;

#[trust_vc::ensures(true)]
fn e5_elem_tuple_alias_liar(t: (Vec<u64>, bool)) {
    let _r = t.0.iter().fold(0u8, |acc, x| x / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e5_elem_tuple_u8_cx(t: (Vec<u8>, bool)) {
    let _r = t.0.iter().fold(0u8, |acc, x| x / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e8_scalar_tuple_alias_straightline(t: (u64, bool)) {
    let _y = t.0 / 2 + 200;
    trust_vc::assert!(true);
}
"#;

/// The programs above with `u8` spelled out and no rebinding in the file:
/// the frame decides them at the right width.
const SRC_NO_REBINDING: &str = r#"
#![allow(dead_code, unused, unused_mut)]

fn apply(g: impl Fn(u8) -> u8, a: u8) -> u8 {
    g(a)
}

#[trust_vc::ensures(true)]
fn n1_cast_seed_ctrl(v: Vec<u8>, a: u8) {
    let _r = v.iter().fold(a as u8, |acc, x| acc / 2 + 100);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n1_cast_seed_twin_cx(v: Vec<u8>, a: u8) {
    let _r = v.iter().fold(a as u8, |acc, x| acc / 2 + 200);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n2_escaping_ctrl(a: u8) {
    let g = |x: u8| x / 2 + 100;
    let _ = apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n2_escaping_twin_cx(a: u8) {
    let g = |x: u8| x / 2 + 200;
    let _ = apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n3_straightline_ctrl(a: u8) {
    let y = a / 2 + 100;
    trust_vc::assert!(y >= 100u8);
}

#[trust_vc::ensures(true)]
fn n3_straightline_twin_cx(a: u8) {
    let y = a / 2 + 200;
    trust_vc::assert!(y >= 100u8);
}
"#;

/// Rule 2. Each liar is refused with the tag: before this rule every one of
/// them was `Verified` (measured on the merged tree before the change). Each
/// `_cx` twin spells `u8` and stays a `Counterexample` in the same file: the
/// rule refuses a `Verified` answer and keeps a refutation. `t1_alias_true_claim`
/// is a TRUE program in the rebinding file, and is refused too: that is the
/// cost of the rule. In a file with no rebinding the same shapes verify when
/// true and are refuted when false.
#[test]
fn a_file_that_rebinds_a_primitive_name_gets_no_verified_answer() {
    check_table(
        SRC_ALIAS,
        &[
            ("c1_cast_seed_alias_liar", Refused),
            ("c1_cast_seed_u8_twin_cx", Counterexample),
            ("e1_let_elem_alias_liar", Refused),
            ("e1_let_elem_u8_twin_cx", Counterexample),
            ("w1_written_acc_alias_liar", Refused),
            ("w1_written_acc_u8_twin_cx", Counterexample),
            ("w2_escaping_written_alias_liar", Refused),
            ("w2_escaping_written_u8_twin_cx", Counterexample),
            ("g1_straightline_cast_alias_cx", Counterexample),
            ("f8_param_seed_alias_cx", Counterexample),
            ("t1_alias_true_claim", Refused),
        ],
    );
    check_table(
        SRC_USE_RENAME,
        &[
            ("g3_param_use_straightline", Refused),
            ("g4_cast_body_use_straightline", Refused),
            ("p1_param_file_use_liar", Refused),
            ("p1_param_u8_cx", Counterexample),
        ],
    );
    check_table(
        SRC_BODY_USE_RENAME,
        &[("g5_cast_body_use_straightline", Refused)],
    );
    check_table(
        SRC_TUPLE_ALIAS,
        &[
            ("e5_elem_tuple_alias_liar", Refused),
            ("e5_elem_tuple_u8_cx", Counterexample),
            ("e8_scalar_tuple_alias_straightline", Refused),
        ],
    );
    check_table(
        SRC_NO_REBINDING,
        &[
            ("n1_cast_seed_ctrl", Verified),
            ("n1_cast_seed_twin_cx", Counterexample),
            ("n2_escaping_ctrl", Verified),
            ("n2_escaping_twin_cx", Counterexample),
            ("n3_straightline_ctrl", Verified),
            ("n3_straightline_twin_cx", Counterexample),
        ],
    );
}

// ---------------------------------------------------------------- reports

/// Extracts `func` from `src` as the file lane does and verifies it with a
/// report, the path `--emit-certificate` and `--emit-hints` read.
fn report_for(src: &str, func: &str) -> VerificationReport {
    let file = syn::parse_file(src).expect("parse fixture");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == func => Some(f.clone()),
            _ => None,
        })
        .expect("fixture function");
    let ctx = extract_verification_conditions_with_file_context(&file, &item).expect("extract");
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        ctx.verify_with_report(VerificationReportOptions::new())
    })
}

fn verified_steps(report: &VerificationReport) -> Vec<&str> {
    report
        .steps()
        .iter()
        .filter(|step| step.result() == StepResultKind::Verified)
        .map(|step| step.label())
        .collect()
}

/// `g3` overflows a `u8` for `a >= 112`. `g6`'s first sum overflows the same
/// way and its second is refuted outright. `g3` in `SRC_REPORT_TWIN` is the
/// same body with no rebinding, where `a` is a `u64` and nothing overflows.
const SRC_REPORT_LIAR: &str = r#"
#![allow(dead_code, unused, non_camel_case_types)]
use core::primitive::u8 as u64;

#[trust_vc::ensures(true)]
fn g3(a: u64) {
    let y = a / 2 + 200;
}

#[trust_vc::ensures(true)]
fn g6(a: u64, b: u8) {
    let y = a / 2 + 200;
    let z = b + 255;
}
"#;

const SRC_REPORT_TWIN: &str = r#"
#[trust_vc::ensures(true)]
fn g3(a: u64) {
    let y = a / 2 + 200;
}
"#;

/// A refused `Verified` answer is refused for each obligation as well: no
/// step of the report is `Verified`, no proven fact (and so no
/// `unreachable_unchecked` hint) comes out of it, and it carries no proof
/// certificate. A refutation in the same context is kept.
#[test]
fn a_refused_verified_answer_publishes_no_verified_step() {
    let liar = report_for(SRC_REPORT_LIAR, "g3");
    assert!(
        matches!(liar.result(), VerifyResult::Error { message } if message.starts_with(TAG)),
        "g3 must be refused, got {:?}",
        liar.result()
    );
    assert!(
        liar.steps()
            .iter()
            .any(|step| step.label() == "overflow_check_0"),
        "g3's overflow obligation must be checked"
    );
    assert_eq!(verified_steps(&liar), Vec::<&str>::new());
    assert!(extract_proven_facts(&liar).is_empty());
    #[cfg(feature = "proof-certificates")]
    assert!(liar.proof().is_none());

    let mixed = report_for(SRC_REPORT_LIAR, "g6");
    assert!(
        matches!(mixed.result(), VerifyResult::Counterexample { .. }),
        "g6 must stay refuted, got {:?}",
        mixed.result()
    );
    assert_eq!(verified_steps(&mixed), Vec::<&str>::new());
    assert!(extract_proven_facts(&mixed).is_empty());

    let twin = report_for(SRC_REPORT_TWIN, "g3");
    assert!(
        matches!(twin.result(), VerifyResult::Verified),
        "the twin must verify, got {:?}",
        twin.result()
    );
    assert!(verified_steps(&twin).contains(&"overflow_check_0"));
    assert!(!extract_proven_facts(&twin).is_empty());
}
