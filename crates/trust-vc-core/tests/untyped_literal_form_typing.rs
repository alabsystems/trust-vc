//! A conditional of unsuffixed integer literals (`if c { 200 } else { 0 }`, a
//! `match` of them) is an UNTYPED literal form, like `200` and `200 + 100`:
//! Rust types every literal in it by the one peer the form meets
//! (design-trust-proof-backend.md §5b rule 2). It was read as a value of its
//! `i32` placeholder instead, so meeting `y: u8` made a mixed `i32 + u8`
//! operation, which is EXACT: `let a = if c { 200 } else { 200 }; let z = a +
//! y;` (`y == 100`) raised no overflow obligation, and `a + y == 300` held.
//!
//! A binding whose witness is such a form (`let mut w = 0`) takes its type
//! from its uses, which the extractor does not see in order:
//!
//! * a write in a branch joins as a conditional of the written forms, typed
//!   where it is read;
//! * an operation over such a form that meets no peer where it is evaluated
//!   (`w = w + 100` before `let z: u8 = w`) is checked in every type its
//!   literals fit, since the peer that types it may come later;
//! * a loop that writes the binding declares its loop-head value at the type
//!   the binding's later uses give it (`i32` only when every use is read and
//!   none fixes a type), and fails closed when they do not decide it: it was
//!   declared `i32`, so `w + y` after the loop was again a mixed, exact
//!   addition.
//!
//! A loop models a written name as the declared variable of that name, so a
//! `let` that shadows a parameter (`let mut w = 0` or `let mut w: u8 = 0`
//! over `w: u64`) was havocked at the parameter's type; such a loop is now
//! refused unless the two have one type.
//!
//! Every `never_*` goal is false or its program panics (`trustc -C
//! overflow-checks=on`) and must not be `Verified`; every `verified_*` twin
//! must be `Verified`; every `true_*` twin is the honest reading and must not
//! be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_UNTYPED_CONDITIONAL: &str = r####"
#[trust_vc::requires(y == 100u8)]
fn never_cond_let_then_add(y: u8, c: bool) {
    let a = if c { 200 } else { 200 };
    let z = a + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_match_let_then_add(y: u8, c: bool) {
    let a = match c {
        true => 200,
        false => 200,
    };
    let z = a + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_direct(y: u8, c: bool) {
    let z = (if c { 200 } else { 200 }) + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_peer_on_left(y: u8, c: bool) {
    let a = if c { 200 } else { 200 };
    let z = y + a;
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_mul_suffixed_peer(y: u8, c: bool) {
    let a = if c { 200 } else { 200 };
    let z = a * 2u8;
}

#[trust_vc::requires(y == 100i8)]
fn never_cond_i8_sub(y: i8, c: bool) {
    let a = if c { -100 } else { -100 };
    let z = a - y;
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_assert_exact_sum(y: u8, c: bool) {
    let a = if c { 200 } else { 200 };
    trust_vc::assert!(a + y == 300);
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_chain(y: u8, c: bool) {
    let a = if c { 200 } else { 250 };
    let b = if a < 220 { a } else { 220 };
    let z = b + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_closure_argument(y: u8, c: bool) {
    let f = |a: u8| a + y;
    let z = f(if c { 200 } else { 200 });
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_shadowing_a_u8(y: u8, c: bool) {
    let a: u8 = 1;
    let a = if c { 200 } else { 200 };
    let z = a + y;
}

#[trust_vc::requires(x == 18446744073709551615u64)]
fn never_cond_u64_overflow(x: u64, c: bool) {
    let a = if c { 1 } else { 1 };
    let z = x + a;
}

#[trust_vc::requires(x == 4294967295u32)]
fn never_cond_u32_exact_sum(x: u32, c: bool) {
    let a = if c { 1 } else { 1 };
    trust_vc::assert!(x + a == 4294967296);
}

#[trust_vc::requires(y == 100u8)]
fn never_cond_times_literal_then_add(y: u8, c: bool) {
    let a = (if c { 1 } else { 1 }) * 200;
    let z = a + y;
}

#[trust_vc::requires(c)]
fn never_cond_product_overflows_its_later_type(c: bool) {
    let a = (if c { 2 } else { 2 }) * 200;
    let z: u8 = a;
}

#[trust_vc::requires(y == 100u8)]
fn verified_cond_fits(y: u8, c: bool) {
    let a = if c { 100 } else { 100 };
    let z = a + y;
}

#[trust_vc::requires(y == 100u8)]
fn verified_cond_times_literal_fits(y: u8, c: bool) {
    let a = (if c { 1 } else { 1 }) * 100;
    let z = a + y;
}

#[trust_vc::requires(x == 4294967295u32)]
fn verified_cond_u32_difference(x: u32, c: bool) {
    let a = if c { 1 } else { 1 };
    trust_vc::assert!(x - a == 4294967294);
}
"####;

const SRC_UNTYPED_WITNESS: &str = r####"
#[trust_vc::requires(y == 100u8)]
fn never_branch_write(c: bool, y: u8) {
    let mut w = 0;
    if c {
        w = 200;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_branch_compound_write(y: u8, c: bool) {
    let mut w = 0;
    if c {
        w += 200;
    }
    let z = w + y;
}

#[trust_vc::requires(c && y == 100u8)]
fn never_branch_write_assert_exact_sum(y: u8, c: bool) {
    let mut w = 0;
    if c {
        w = 200;
    }
    trust_vc::assert!(w + y == 300);
}

#[trust_vc::requires(c)]
fn never_branch_write_then_ascribed_read(c: bool) {
    let mut w = 0;
    if c {
        w = 200;
    }
    w = w + 100;
    let z: u8 = w;
}

#[trust_vc::requires(y == 100u8)]
fn never_while_write(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = 200;
        i = i + 1;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_for_write(y: u8) {
    let mut w = 0;
    for i in 0..1u8 {
        trust_vc::invariant!(true);
        w = 200;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_break_write(y: u8) {
    let mut w = 0;
    loop {
        trust_vc::invariant!(true);
        w = 200;
        break;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn verified_branch_write_fits(c: bool, y: u8) {
    let mut w = 0;
    if c {
        w = 100;
    }
    let z = w + y;
}

#[trust_vc::requires(c && y == 100u8)]
fn verified_branch_write_sum_fits(y: u8, c: bool) {
    let mut w = 0;
    if c {
        w = 100;
    }
    trust_vc::assert!(w + y == 200);
}

#[trust_vc::requires(c)]
fn verified_branch_write_then_ascribed_read_fits(c: bool) {
    let mut w = 0;
    if c {
        w = 100;
    }
    w = w + 20;
    let z: u8 = w;
}

#[trust_vc::requires(y == 100u8)]
fn verified_while_write_fits(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1 && w <= 100);
        w = 100;
        i = i + 1;
    }
    let z = w + y;
}

#[trust_vc::ensures(true)]
fn verified_untyped_counter_defaults_to_i32() {
    let mut i = 0;
    while i < 10 {
        trust_vc::invariant!(i <= 10);
        i = i + 1;
    }
    trust_vc::assert!(i == 10);
}

#[trust_vc::ensures(true)]
fn verified_untyped_counter_typed_by_an_earlier_local() {
    let n: u8 = 10;
    let mut i = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        i = i + 1;
    }
    trust_vc::assert!(i == 10u8);
}
"####;

const SRC_SHADOWING_LET_IN_LOOP: &str = r####"
#[trust_vc::requires(y == 100u8)]
fn never_untyped_let_shadows_wider_param(w: u64, y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = 200;
        i = i + 1;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_typed_let_shadows_wider_param(w: u64, y: u8) {
    let mut w: u8 = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = 200;
        i = i + 1;
    }
    let z = w + y;
}

#[trust_vc::requires(x <= 100u64)]
fn verified_same_type_shadow_of_param(x: u64) {
    let mut x = x;
    while x > 0 {
        trust_vc::invariant!(x <= 100u64);
        x = x - 1u64;
    }
    trust_vc::assert!(x == 0u64);
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
        .join("../../target/untyped_literal_form_src");
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
        println!("UNTYPED|{file}|{func}|{got}|{raw}");
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
fn an_untyped_conditional_takes_the_type_of_its_peer() {
    check(SRC_UNTYPED_CONDITIONAL, "untyped_conditional.rs", 17);
}

#[test]
fn a_binding_of_an_untyped_literal_keeps_no_guessed_type() {
    check(SRC_UNTYPED_WITNESS, "untyped_witness.rs", 13);
}

#[test]
fn a_loop_never_models_a_shadowing_let_as_the_parameter() {
    check(SRC_SHADOWING_LET_IN_LOOP, "shadowing_let_in_loop.rs", 3);
}
