//! Residuals of the misread-value classes (round-2 verifier). Each group is
//! one cause, and every `never_*` program panics under `-C
//! overflow-checks=on` or its goal is false:
//!
//! * the panic-safety substitution of an invoked exec closure puts each call
//!   argument in bare, so an UNSUFFIXED literal argument keeps its `i32`
//!   placeholder instead of the parameter's type: `let f = |a: u8| a + 100;
//!   f(200)` checked `200 + 100` in `i32`;
//! * a bitwise `!` over an unsuffixed literal is not an untyped literal form,
//!   so it stays an `i32` value and meets a `u8` peer as a mixed, EXACT
//!   operation: `!0 + y` raised no overflow obligation;
//! * a loop-written unsuffixed-literal binding whose only typing use reaches
//!   its peer THROUGH an operation of its own type (`w - 1 + y`, and `(w >>
//!   1) + y`: a shift's result has its left operand's type) is declared `i32`
//!   at the loop head, so the loop's `u8` overflow is never checked;
//! * an unsuffixed float literal carried in a tuple, an array or an `Option`
//!   is still the exact `real`: `let p = (0.1, 0.2); p.0 + p.1 == 0.3` held;
//! * a `while let` pattern binding is not shadowed, so its name reads an
//!   OUTER binding of that name (`v < 10`);
//! * `std::mem::{swap, replace, take}` given `&mut` to a field or a cell drop
//!   the write: `swap(&mut v[0].g, &mut t)` left `v[0].g` unchanged;
//! * a loop models a written name as the declared variable of that name, and
//!   a `let` of a COMPOSITE type shadowing a parameter of another type (`let
//!   mut s = B1 { g: 0 }` over `s: A1`) was havocked at the parameter's type.
//!
//! Every `never_*` goal must not be `Verified`; every `verified_*` twin must
//! be `Verified`; every `true_*` twin must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_CLOSURE_LITERAL_ARGUMENT: &str = r####"
#[trust_vc::requires(y == 100u8)]
fn never_closure_literal_arg(y: u8) {
    let f = |a: u8| a + 100;
    let z = f(200);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_literal_arg_fnptr(y: u8) {
    let f: fn(u8) -> u8 = |a| a + 100;
    let z = f(200);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_literal_arg_mul(y: u8) {
    let f = |a: u8| a * 2;
    let z = f(200);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_let_literal_arg(y: u8) {
    let f = |a: u8| a + 100;
    let k = 200;
    let z = f(k);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_two_params_literal(y: u8) {
    let f = |a: u8, b: u8| a + b;
    let z = f(200, 100);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_literal_arg_sub(y: u8) {
    let f = |a: u8| a - 1;
    let z = f(0);
}

#[trust_vc::requires(y == 100u8)]
fn never_closure_literal_arg_i8(y: u8) {
    let f = |a: i8| a + 100;
    let z = f(100);
}

#[trust_vc::requires(y == 100u8)]
fn never_immediate_closure_literal_arg(y: u8) {
    let z = (|a: u8| a + 100)(200);
}

#[trust_vc::requires(y == 100u8)]
fn verified_closure_literal_arg_fits(y: u8) {
    let f = |a: u8| a + 100;
    let z = f(100);
}
"####;

const SRC_UNTYPED_BITWISE_NOT: &str = r####"
#[trust_vc::requires(y == 1u8)]
fn never_not_literal_direct(y: u8) {
    let z = !0 + y;
}

#[trust_vc::requires(y == 1u8)]
fn never_not_let_plus_peer(y: u8) {
    let w = 0;
    let z = !w + y;
}

#[trust_vc::requires(y == 1u8)]
fn never_not_literal_assert(y: u8) {
    let w = 0;
    trust_vc::assert!(!w + y == 0u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_not_init_branch(c: bool, y: u8) {
    let mut w = 0;
    if c {
        w = !0;
    }
    let z = w + y;
}

#[trust_vc::requires(c && y == 1u8)]
fn never_not_init_direct_cond(c: bool, y: u8) {
    let z = (if c { !0 } else { 0 }) + y;
}

#[trust_vc::requires(y == 1u8)]
fn verified_not_typed_literal_fits(y: u8) {
    let z = !254u8 + y;
}
"####;

const SRC_LOOP_SHIFT_TYPED: &str = r####"
#[trust_vc::requires(y == 100u8)]
fn never_loop_write_shift_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = 200;
        i = i + 1;
    }
    let z = (w << 0) + y;
}

#[trust_vc::requires(y == 200u8)]
fn never_loop_shr_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = 250;
        i = i + 1;
    }
    let z = (w >> 1) + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_counter_nested_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w - 1 + y;
}
"####;

const SRC_FLOAT_LITERAL_AGGREGATE: &str = r####"
fn never_float_tuple_fields() {
    let p = (0.1, 0.2);
    trust_vc::assert!(p.0 + p.1 == 0.3);
}

fn never_float_tuple_destructure() {
    let (a, b) = (0.1, 0.2);
    trust_vc::assert!(a + b == 0.3);
}

fn never_float_array_cells() {
    let a = [0.1, 0.2];
    trust_vc::assert!(a[0] + a[1] == 0.3);
}

fn never_float_option_unwrap() {
    let o = Some(0.1);
    trust_vc::assert!(o.unwrap() + 0.2 == 0.3);
}

fn never_float_tuple_field_mul() {
    let p = (0.1, 3.0);
    trust_vc::assert!(p.0 * p.1 == 0.3);
}
"####;

const SRC_WHILE_LET_PATTERN_SHADOW: &str = r####"
#[trust_vc::requires(v < 10u64)]
fn never_while_let_payload(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        trust_vc::invariant!(true);
        let w = v + 1u64;
        p = None;
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_while_let_tuple(v: u64, o: Option<(u64, u64)>) {
    let mut p = o;
    while let Some((v, _)) = p {
        trust_vc::invariant!(true);
        let w = v + 1u64;
        p = None;
    }
}

#[trust_vc::requires(v < 10u64)]
fn true_while_let_payload_halved(v: u64, o: Option<u64>) {
    let mut p = o;
    while let Some(v) = p {
        trust_vc::invariant!(true);
        let w = v / 2u64;
        p = None;
    }
}
"####;

const SRC_MEM_PROJECTION_WRITE: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_elem_field(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    let mut t = x;
    std::mem::swap(&mut v[0].g, &mut t);
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_replace_elem_field(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    let old = std::mem::replace(&mut v[0].g, x);
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_take_elem_field(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    let old = std::mem::take(&mut v[0].g);
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_struct_field(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    std::mem::swap(&mut s.g, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_replace_struct_field(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let old = std::mem::replace(&mut s.g, x);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_vec_cell(y: u8, x: u8) {
    let mut v: Vec<u8> = vec![y];
    let mut t = x;
    std::mem::swap(&mut v[0], &mut t);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_replace_vec_cell(y: u8, x: u8) {
    let mut v: Vec<u8> = vec![y];
    let old = std::mem::replace(&mut v[0], x);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_core_replace_elem_field(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    let old = core::mem::replace(&mut v[0].g, x);
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_array_elem_field(y: u8, x: u8) {
    let mut a: [S2; 1] = [S2 { g: y, h: y }];
    let mut t = x;
    std::mem::swap(&mut a[0].g, &mut t);
    trust_vc::assert!(a[0].g == 1u8);
}
"####;

const SRC_LOOP_SHADOWED_NON_SCALAR: &str = r####"
struct A1 {
    g: u64,
}

struct B1 {
    g: u8,
}

#[trust_vc::requires(y == 100u8)]
fn never_struct_shadow_loop(s: A1, y: u8) {
    let mut s = B1 { g: 0 };
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        s.g = 200;
        i = i + 1;
    }
    let z = s.g + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_struct_shadow_loop_whole(s: A1, y: u8) {
    let mut s = B1 { g: 0 };
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        s = B1 { g: 200 };
        i = i + 1;
    }
    let z = s.g + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_tuple_shadow_loop(w: (u64, u64), y: u8) {
    let mut w: (u8, u8) = (0, 0);
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w.0 = 200;
        i = i + 1;
    }
    let z = w.0 + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_option_shadow_loop(w: Option<u64>, y: u8) {
    let mut w: Option<u8> = None;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        w = Some(200);
        i = i + 1;
    }
    if let Some(k) = w {
        let z = k + y;
    }
}

#[trust_vc::requires(s.g < 10u64)]
fn verified_struct_self_rebind_loop(s: A1) {
    let mut s = s;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        s.g = 5;
        i = i + 1;
    }
    trust_vc::assert!(i == 1u8);
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
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/misread_residual_src");
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
fn an_invoked_closure_argument_is_checked_at_its_parameter_type() {
    check(
        SRC_CLOSURE_LITERAL_ARGUMENT,
        "closure_literal_argument.rs",
        9,
    );
}

#[test]
fn a_bitwise_not_of_an_untyped_literal_takes_its_peer_type() {
    check(SRC_UNTYPED_BITWISE_NOT, "untyped_bitwise_not.rs", 6);
}

#[test]
fn a_nested_operation_types_a_loop_written_untyped_binding() {
    check(SRC_LOOP_SHIFT_TYPED, "loop_shift_typed.rs", 3);
}

#[test]
fn an_unsuffixed_float_literal_in_an_aggregate_is_never_exact() {
    check(SRC_FLOAT_LITERAL_AGGREGATE, "float_literal_aggregate.rs", 5);
}

#[test]
fn a_while_let_binding_is_never_read_as_the_outer_binding() {
    check(
        SRC_WHILE_LET_PATTERN_SHADOW,
        "while_let_pattern_shadow.rs",
        3,
    );
}

#[test]
fn a_mem_function_write_through_a_projection_is_never_dropped() {
    check(SRC_MEM_PROJECTION_WRITE, "mem_projection_write.rs", 9);
}

#[test]
fn a_loop_never_models_a_shadowing_composite_as_the_parameter() {
    check(
        SRC_LOOP_SHADOWED_NON_SCALAR,
        "loop_shadowed_non_scalar.rs",
        5,
    );
}
