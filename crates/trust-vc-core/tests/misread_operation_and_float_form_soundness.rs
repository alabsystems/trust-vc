//! Residuals of two misread-value classes, found reviewing the round-2 fixes.
//! Every `never_*` program panics under `-C overflow-checks=on` or its goal is
//! false when run:
//!
//! * a loop-written binding bound to an unsuffixed integer literal (`let mut
//!   w = 0`) is declared at the type its uses give it. An OPERATION of its type
//!   (`w - 45`) standing where that reading does not type it — a call or
//!   method argument, a struct field — was read as a use that fixes nothing,
//!   so the binding was declared `i32` where `g8(w - 45)` makes it a `u8`, and
//!   the loop's `u8` overflow went unchecked;
//! * an unsuffixed float literal is lowered as the exact `real` it is next to
//!   a `real` peer, and only an operation over float literals ALONE was
//!   refused. A conditional or `match` whose values are such literals, a value
//!   written to a binding bound to one, and a `vec!` of them were still exact:
//!   `let a = if c { 0.1 } else { 0.1 }; a + 0.2 == 0.3` held, where `f64`
//!   arithmetic makes it false.
//!
//! Every `never_*` goal must not be `Verified`; every `verified_*` twin must
//! be `Verified`; every `true_*` twin must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_UNTYPED_OPERATION_POSITION: &str = r####"
fn g8(x: u8) {}

struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_operation_call_argument(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    g8(w - 45);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_operation_struct_field(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let s = S2 { g: w - 45, h: y };
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_operation_method_argument(y: u8) {
    let mut v: Vec<u8> = Vec::new();
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    v.push(w - 45);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_operation_tail(y: u8) -> u8 {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    w - 45
}

#[trust_vc::requires(y < 100u8)]
fn verified_loop_operation_next_to_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        trust_vc::invariant!(w <= 100);
        w = 100;
        i = i + 1;
    }
    let z = w * 1 + y;
}
"####;

const SRC_FLOAT_VALUE_FORMS: &str = r####"
fn never_float_conditional(c: bool) {
    let a = if c { 0.1 } else { 0.1 };
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn never_float_match(c: bool) {
    let a = match c {
        true => 0.1,
        false => 0.1,
    };
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn never_float_conditional_operand(c: bool) {
    trust_vc::assert!((if c { 0.1 } else { 0.1 }) * 3.0 == 0.3);
}

fn never_float_two_conditionals(c: bool) {
    let a = if c { 0.1 } else { 0.2 };
    let b = if c { 0.2 } else { 0.1 };
    trust_vc::assert!(a + b == 0.3);
}

fn never_float_negated_conditional(c: bool) {
    let a = if c { -0.1 } else { -0.1 };
    trust_vc::assert!(a - 0.2 == -0.3);
}

fn never_float_written(c: bool) {
    let mut a = 0.0;
    a = 0.1;
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn never_float_written_in_branches(c: bool) {
    let mut a = 0.0;
    if c {
        a = 0.1;
    } else {
        a = 0.1;
    }
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn never_float_vec_cells() {
    let v = vec![0.1, 0.2];
    trust_vc::assert!(v[0] + v[1] == 0.3);
}

fn never_float_vec_cell_binding() {
    let v = vec![0.1, 0.2];
    let a = v[0];
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn true_float_dyadic_conditional(c: bool) {
    let a = if c { 0.5 } else { 0.5 };
    trust_vc::assert!(a + 0.25 == 0.75);
}
"####;

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } => "Refuted",
        VerifyResult::NotProved { .. } => "NotProved",
        _ => "Unknown",
    }
}

fn run_source(src: &str, file: &str, func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/misread_operation_and_float_form_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(file);
    let mut f = std::fs::File::create(&path).expect("create source");
    f.write_all(src.as_bytes()).expect("write source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn check(src: &str, file: &str, expected: usize) {
    let names: Vec<&str> = src
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(names.len(), expected, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(src, file, func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("RESIDUAL|{file}|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("true_") && got == "Refuted" {
            wrong.push(format!("TRUE CLAIM REFUTED {func}: {raw}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {raw}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn an_operation_of_a_loop_written_untyped_binding_is_a_typing_use() {
    check(
        SRC_UNTYPED_OPERATION_POSITION,
        "untyped_operation_position.rs",
        5,
    );
}

#[test]
fn an_unsuffixed_float_value_form_is_never_exact() {
    check(SRC_FLOAT_VALUE_FORMS, "float_value_forms.rs", 10);
}
