//! A value is bound only at a type that holds it (design-trust-proof-backend.md
//! §5b rules 6, 7 and 9): the sites where a value meets a DECLARED integer type
//! through an equation, not an operation.
//!
//! Since the value-preserving literal rule (§5b rule 2) an unsuffixed `-1`
//! next to a `u8` is `-1`, not the `u8` 255, and a mixed-type sum is the exact
//! integer. Bound by an EQUATION at a type that cannot hold it, such a value
//! does not bind — it makes the equation unsatisfiable, and an assumed,
//! unsatisfiable equation prunes every path through it:
//!
//! * an exec function's return value (`result == value` is assumed):
//!   `-> u8 { if c { -1 } else { 0 } }` forced `!c`, so `ensures c ==> result
//!   == 7` was `Verified`;
//! * an exec callee's contract instantiated at the call's arguments: `inc(-1)`
//!   (`fn inc(a: u8) -> u8 ensures result == a`) assumed `r == -1` of a `u8`;
//! * the proc-macro builders (`ir_builder::*_inferred`), which re-typed a
//!   literal by shape — `x + (-1)` next to `x: u8` was the `u8` 255, and the
//!   value of `1 << k` became a `u32`;
//! * a suffixed `200i32`, which was read as the unsuffixed placeholder;
//! * a demand-inline retry, which assumed "no overflow" of arithmetic inside
//!   an inlined spec-function body the separate overflow pass never checked.
//!
//! An `if` whose branches are a bit-vector and an integer (`if c { !x } else
//! { y + z }`, `x: u8`, `y: i8`, `z: u128`) is the integer each branch
//! denotes; the encoder handed both sorts to the solver's `ite` (`Unknown`).
//!
//! `never_*` goals are FALSE under every reading (the exact integers, two's
//! complement in any operand's type); `must_*` goals are TRUE under every
//! reading. A refusal (`Unknown`/`Error`) is the accepted answer for a program
//! Rust itself rejects.

use std::io::Write;

use trust_vc_core::ir::{ArithOp, CompareOp, SpecialArithOp, TrustVcExpr, TrustVcType};
use trust_vc_core::ir_builder::{arith_inferred, int_lit, neg, special_arith_inferred, var};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::ensures(c ==> result == 7)]
fn never_return_neg_literal_prunes_path(c: bool) -> u8 {
    if c { -1 } else { 0 }
}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1 || y == 1)]
#[trust_vc::ensures(y == -1 ==> result > 1000)]
fn never_return_mixed_sum_prunes_path(x: u8, y: i16) -> u8 {
    x + y
}

#[trust_vc::ensures(c ==> result == 200)]
fn must_return_fitting_literals(c: bool) -> u8 {
    if c { 200 } else { 0 }
}

#[trust_vc::ensures(result == a)]
fn inc(a: u8) -> u8 {
    a
}

fn never_call_neg_literal_arg_prunes_path(c: bool) {
    let mut r: u8 = 0;
    if c {
        r = inc(-1);
    }
    trust_vc::assert!(c ==> r == 7);
}

#[trust_vc::requires(c)]
fn never_call_neg_literal_arg(c: bool) {
    let r = inc(-1);
    trust_vc::assert!(r > 1000);
}

#[trust_vc::requires(y == -1 || y == 1)]
fn never_call_i16_arg_for_u8_param(y: i16) {
    let mut r: u8 = 0;
    if y == -1 {
        r = inc(y);
    }
    trust_vc::assert!(y == -1 ==> r == 7);
}

fn must_call_fitting_literal_arg() {
    let r = inc(200);
    trust_vc::assert!(r == 200);
}

#[trust_vc::spec]
fn h(x: u16) -> int {
    5i16 / ((x * 3) as int)
}

#[trust_vc::requires(x == 34862)]
#[trust_vc::ensures(h(x) == 0 && h(x) == 1)]
fn never_demand_inline_assumes_unchecked_overflow(x: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 100)]
#[trust_vc::ensures(x + 200i32 == 44)]
fn never_suffixed_i32_read_as_placeholder(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 100)]
#[trust_vc::ensures(x + 200i32 == 300)]
fn must_suffixed_i32_is_i32(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 1)]
#[trust_vc::ensures(x * -128i32 == -128)]
fn must_negative_suffixed_i32_is_i32(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 100)]
#[trust_vc::ensures(x + 200 == 44)]
fn must_unsuffixed_literal_takes_u8(x: u8) {}

#[trust_vc::requires(c && x == 242 && y == 0 && z == 200)]
#[trust_vc::ensures((if c { !x } else { y + z }) == 13)]
fn must_ite_lifts_bit_vector_arm_beside_int(c: bool, x: u8, y: i8, z: u128) {}

#[trust_vc::requires(c && x == 242 && y == 0 && z == 200)]
#[trust_vc::ensures((if c { !x } else { y + z }) == 269)]
fn never_ite_bit_vector_arm_beside_int(c: bool, x: u8, y: i8, z: u128) {}

#[trust_vc::proof]
#[trust_vc::requires(!c && y == -1 && z == 0)]
#[trust_vc::ensures((if c { !x } else { y + z }) == -1)]
fn must_ite_int_arm_keeps_its_value(c: bool, x: u8, y: i8, z: u128) {}

#[trust_vc::proof]
#[trust_vc::requires(!c && y == -1 && z == 0)]
#[trust_vc::ensures((if c { !x } else { y + z }) == 255)]
fn never_ite_int_arm_read_at_bit_vector_type(c: bool, x: u8, y: i8, z: u128) {}
"####;

fn run_source(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/integer_binding_soundness_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join("integer_binding_soundness.rs");
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(SRC.as_bytes()))
        .expect("write source");
    verify_function_from_file(path.to_str().expect("utf-8"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
        _ => "Unknown",
    }
}

fn check(name: &str, got: &VerifyResult, bad: &mut Vec<String>) {
    let g = verdict(got);
    let raw: String = format!("{got:?}").chars().take(220).collect();
    println!("BIND|{name}|{g}|{raw}");
    if (name.starts_with("never_") && g == "Verified")
        || (name.starts_with("must_") && g != "Verified")
    {
        bad.push(format!("{name}: {g}"));
    }
}

#[test]
fn source_bindings_hold_their_declared_type() {
    let mut bad = Vec::new();
    for name in SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("must_"))
    {
        check(name, &run_source(name), &mut bad);
    }
    assert!(bad.is_empty(), "{bad:#?}");
}

fn u(width: u32) -> TrustVcType {
    TrustVcType::Uint { width }
}

fn typed_seam(
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    goal: TrustVcExpr,
) -> VerifyResult {
    let mut variables: Vec<VariableDecl> = params
        .iter()
        .map(|(n, t)| VariableDecl::new((*n).to_string(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = requires
        .iter()
        .enumerate()
        .map(|(i, r)| TypedProofObligation::requires(format!("b_requires_{i}"), r.clone()))
        .collect();
    obligations.push(TypedProofObligation::ensures("b_ensures_0", goal));
    VerificationContext::from_typed_parts(variables, obligations).verify()
}

fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}

/// The proc-macro codegen builders type a literal by value, like the syn
/// lowering, and derive the node's type.
#[test]
fn codegen_builders_type_literals_by_value() {
    let i32t = TrustVcType::Int { width: 32 };
    let mut bad = Vec::new();

    // `x + (-1)`, `x: u8 == 0`: the integer -1 (a negative literal is never
    // unsigned); the shape rule made it the `u8` negation 255.
    let x = || var("x", u(8));
    let pin = cmp(CompareOp::Eq, x(), int_lit(0, u(8)));
    let sum = arith_inferred(ArithOp::Add, x(), neg(int_lit(1, i32t.clone())));
    check(
        "never_builder_neg_literal_becomes_u8",
        &typed_seam(
            &[("x", u(8))],
            std::slice::from_ref(&pin),
            cmp(CompareOp::Eq, sum.clone(), int_lit(255, u(16))),
        ),
        &mut bad,
    );
    check(
        "must_builder_neg_literal_is_minus_one",
        &typed_seam(
            &[("x", u(8))],
            &[pin],
            cmp(
                CompareOp::Eq,
                sum,
                neg(int_lit(1, TrustVcType::Int { width: 16 })),
            ),
        ),
        &mut bad,
    );

    // `1 << k`, `k: u32 == 31`: Rust types the value `i32` (the amount's type
    // is independent), so the result is `i32::MIN`. The builder coerced the
    // VALUE to the amount's `u32`, reading 2^31.
    let k = || var("k", u(32));
    let shl = special_arith_inferred(SpecialArithOp::Shl, int_lit(1, i32t.clone()), k());
    check(
        "must_builder_shift_keeps_value_type",
        &typed_seam(
            &[("k", u(32))],
            &[cmp(CompareOp::Eq, k(), int_lit(31, u(32)))],
            cmp(CompareOp::Lt, shl, int_lit(0, i32t)),
        ),
        &mut bad,
    );
    assert!(bad.is_empty(), "{bad:#?}");
}
