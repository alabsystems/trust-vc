//! Integer typing regressions (design-trust-proof-backend.md §5b): the type of
//! an arithmetic / bitwise / conditional result is DERIVED from both operands;
//! a literal's type never changes its value; `===` compares values; a shift
//! amount is never truncated; a report's admitted verdict needs evidence (that
//! one lives in trust-vc-trust-engine).
//!
//! Every FALSE goal here is false under EVERY reading on offer — the exact
//! integer (Verus spec arithmetic) AND two's complement in the arithmetic
//! node's own declared type — so no reading of the semantics excuses a
//! `Verified`. Each has a TRUE twin that must still verify.
//!
//! Measured at 8bbef1af (the tree before the fix): 14 of the 17 tests here
//! FAIL — a false goal `Verified` or a true twin refuted:
//! * source frontend — the syn lowering typed `x + y` by its LEFT operand and
//!   `if c { x } else { y }` by its then-branch; the encoder computed at the
//!   wider width with each operand's own sign and the comparison read the
//!   result with the (unsigned) node type's sign: `0u8 + (-1i16)` compared as
//!   65535;
//! * typed seam — a negative `Int{32}` literal next to an unsigned operand
//!   stayed signed while the node said `u16`/`u8`, same misreading;
//! * `-x0` with `x0: i32 == -128` next to an `i8` peer: equality substitution
//!   closed it into `Neg(IntLit { -128 })`, which the peer typed as the `i8`
//!   negation of -128, i.e. -128;
//! * `===` compared the BITS after own-sign extension: `255u8 === -1i8`;
//! * `by(bit_vector)` narrowed a shift amount wider than the value by bit
//!   extraction: `1u8 << 256u16` shifted by 0;
//! * the pre-solve constant evaluator folded `-(-128i8) == 128` exactly and a
//!   mixed-type division in the node's declared type.
//!
//! Three pass there and stay as controls of the decided semantics:
//! `src_u8_minus_positive_i16_is_not_at_least_256`,
//! `src_u8_plus_negative_i16_is_minus_one` and
//! `typed_untyped_literal_tree_is_typed_by_its_peer`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::io::Write;

use trust_vc_core::ir::{ArithOp, CompareOp, SpecialArithOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{SolverMode, TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

// ---------------------------------------------------------------------------
// Source frontend (`verify_function_from_file`), Verus-style spec clauses.
// ---------------------------------------------------------------------------

const SRC: &str = r####"
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures(x + y >= z)]
fn u8_plus_neg_i16_ge_i16(x: u8, y: i16, z: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures(x + y < z)]
fn twin_u8_plus_neg_i16_lt_i16(x: u8, y: i16, z: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures(x + y >= z)]
fn u8_plus_neg_i64_ge_i64(x: u8, y: i64, z: i64) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures(x + y >= z)]
fn u16_plus_neg_i64_ge_i16(x: u16, y: i64, z: i16) {}

#[trust_vc::requires(x == 1)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 1000)]
#[trust_vc::ensures(x * y > z)]
fn u8_times_neg_i16_gt_i16(x: u8, y: i16, z: i16) {}

#[trust_vc::requires(x == 1)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x * y == -1)]
fn twin_u8_times_neg_i16_is_minus_one(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == 1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures(x - y >= z)]
fn u8_minus_pos_i16_ge_i16(x: u8, y: i16, z: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x + y != -1)]
fn u8_plus_neg_i16_ne_minus_one(x: u8, y: i16) {}

#[trust_vc::requires(c)]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures((if !c { x } else { y }) >= z)]
fn ite_u8_then_i16_else_ge_i16(c: bool, x: u8, y: i16, z: i16) {}

#[trust_vc::requires(c)]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures((if !c { x } else { y }) == -1)]
fn twin_ite_u8_then_i16_else_is_minus_one(c: bool, x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures((x | y) >= z)]
fn u8_bitor_neg_i16_ge_i16(x: u8, y: i16, z: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures((x | y) == -1)]
fn twin_u8_bitor_neg_i16_is_minus_one(x: u8, y: i16) {}

#[trust_vc::requires(x0 == -128)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures(-x0 < z)]
fn neg_pinned_i32_lt_i8(x0: i32, z: i8) {}

#[trust_vc::requires(x0 == -128)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures(-x0 < (z as i32))]
fn neg_pinned_i32_lt_i8_cast(x0: i32, z: i8) {}

#[trust_vc::requires(x0 == -128)]
#[trust_vc::requires(z == 0)]
fn neg_pinned_i32_lt_i8_assert(x0: i32, z: i8) {
    trust_vc::assert!(-x0 < (z as i32));
}

#[trust_vc::requires(x0 == -128)]
#[trust_vc::ensures(-x0 == 128)]
fn twin_neg_pinned_i32_is_128(x0: i32) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x + y >= 256)]
fn u8_plus_neg_i32_ge_256(x: u8, y: i32, a: u64, b: u64) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::ensures(x + -1 >= 256)]
fn u8_plus_neg_literal_ge_256(x: u8, a: u64, b: u64) {}
"####;

fn run_src(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/integer_typing_soundness_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(format!("{func}.rs"));
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(SRC.as_bytes()))
        .expect("write source");
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn src_not_verified(func: &str) {
    let r = run_src(func);
    assert!(!r.is_verified(), "{func}: FALSE Verified: {r:?}");
    assert!(
        matches!(
            r,
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. }
        ),
        "{func}: a pinned false goal must be refuted, not left undecided: {r:?}"
    );
}

fn src_verified(func: &str) {
    let r = run_src(func);
    assert!(r.is_verified(), "{func}: true goal not verified: {r:?}");
}

#[test]
fn src_u8_plus_negative_i16_is_not_at_least_256() {
    src_not_verified("u8_plus_neg_i16_ge_i16");
    src_verified("twin_u8_plus_neg_i16_lt_i16");
}
#[test]
fn src_u8_plus_negative_i64_is_not_at_least_256() {
    src_not_verified("u8_plus_neg_i64_ge_i64");
}
#[test]
fn src_u16_plus_negative_i64_is_not_at_least_256() {
    src_not_verified("u16_plus_neg_i64_ge_i16");
}
#[test]
fn src_u8_times_negative_i16_is_not_above_1000() {
    src_not_verified("u8_times_neg_i16_gt_i16");
    src_verified("twin_u8_times_neg_i16_is_minus_one");
}
#[test]
fn src_u8_minus_positive_i16_is_not_at_least_256() {
    src_not_verified("u8_minus_pos_i16_ge_i16");
}
#[test]
fn src_u8_plus_negative_i16_is_minus_one() {
    src_not_verified("u8_plus_neg_i16_ne_minus_one");
}
#[test]
fn src_ite_of_u8_and_negative_i16_is_not_at_least_256() {
    src_not_verified("ite_u8_then_i16_else_ge_i16");
    src_verified("twin_ite_u8_then_i16_else_is_minus_one");
}
#[test]
fn src_u8_bitor_negative_i16_is_not_at_least_256() {
    src_not_verified("u8_bitor_neg_i16_ge_i16");
    src_verified("twin_u8_bitor_neg_i16_is_minus_one");
}
#[test]
fn src_neg_of_pinned_i32_is_not_below_zero() {
    src_not_verified("neg_pinned_i32_lt_i8");
    src_not_verified("neg_pinned_i32_lt_i8_cast");
    src_not_verified("neg_pinned_i32_lt_i8_assert");
    src_verified("twin_neg_pinned_i32_is_128");
}
#[test]
fn src_u8_plus_negative_i32_is_not_at_least_256() {
    src_not_verified("u8_plus_neg_i32_ge_256");
    src_not_verified("u8_plus_neg_literal_ge_256");
}

// ---------------------------------------------------------------------------
// Typed seam (`VerificationContext::from_typed_parts`, the DriverFn body).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Goal {
    Ensures,
    Assert,
    BitVectorAssert,
}

fn run(
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    goal: TrustVcExpr,
    kind: Goal,
    exec: bool,
) -> VerifyResult {
    let mut variables: Vec<VariableDecl> = params
        .iter()
        .map(|(n, t)| VariableDecl::new((*n).to_string(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = requires
        .iter()
        .enumerate()
        .map(|(i, r)| TypedProofObligation::requires(format!("f_requires_{i}"), r.clone()))
        .collect();
    obligations.push(match kind {
        Goal::Ensures => TypedProofObligation::ensures("f_ensures_0", goal),
        Goal::Assert => TypedProofObligation::assert("f_goal", goal),
        Goal::BitVectorAssert => {
            TypedProofObligation::assert("f_goal", goal).with_solver_mode(SolverMode::BitVector)
        }
    });
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    if exec {
        ctx.enable_overflow_checks();
    }
    ctx.verify()
}

fn u8t() -> TrustVcType {
    TrustVcType::Uint { width: 8 }
}
fn u16t() -> TrustVcType {
    TrustVcType::Uint { width: 16 }
}
fn u32t() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}
fn u64t() -> TrustVcType {
    TrustVcType::Uint { width: 64 }
}
fn u128t() -> TrustVcType {
    TrustVcType::Uint { width: 128 }
}
fn i8t() -> TrustVcType {
    TrustVcType::Int { width: 8 }
}
fn i16t() -> TrustVcType {
    TrustVcType::Int { width: 16 }
}
fn i32t() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}
fn i64t() -> TrustVcType {
    TrustVcType::Int { width: 64 }
}
fn lit(v: i128, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value: v, ty: t }
}
fn var(n: &str, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: n.to_string(),
        ty: t,
    }
}
fn neg(e: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Neg(Box::new(e))
}
fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}
fn arith(op: ArithOp, l: TrustVcExpr, r: TrustVcExpr, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty: t,
    }
}
fn pin(n: &str, t: &TrustVcType, v: i128) -> TrustVcExpr {
    cmp(CompareOp::Eq, var(n, t.clone()), lit(v, t.clone()))
}
fn strict_eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "__trust_vc_strict_eq".to_string(),
        args: vec![l, r],
        return_ty: TrustVcType::Bool,
    }
}

fn is_refuted(r: &VerifyResult) -> bool {
    matches!(
        r,
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. }
    )
}

/// The goal is false: refuted in every mode (spec `ensures` and exec
/// `assert`, overflow checks off and on).
fn refuted_everywhere(
    label: &str,
    params: &[(&str, TrustVcType)],
    req: &[TrustVcExpr],
    goal: &TrustVcExpr,
) {
    for (kind, exec) in [
        (Goal::Ensures, false),
        (Goal::Ensures, true),
        (Goal::Assert, false),
        (Goal::Assert, true),
    ] {
        let r = run(params, req, goal.clone(), kind, exec);
        assert!(
            is_refuted(&r),
            "{label} (exec={exec}, assert={}): false goal not refuted: {r:?}",
            matches!(kind, Goal::Assert)
        );
    }
}

/// A node DECLARING an integer type its operands do not derive is a claim
/// the one IR typing validator refuses (§5b rule 13): `Unknown` in every mode.
fn refused_everywhere(
    label: &str,
    params: &[(&str, TrustVcType)],
    req: &[TrustVcExpr],
    goal: &TrustVcExpr,
) {
    for (kind, exec) in [
        (Goal::Ensures, false),
        (Goal::Ensures, true),
        (Goal::Assert, false),
        (Goal::Assert, true),
    ] {
        let r = run(params, req, goal.clone(), kind, exec);
        assert!(
            matches!(r, VerifyResult::Unknown { .. } | VerifyResult::Error { .. }),
            "{label} (exec={exec}): a declared-type lie was decided: {r:?}"
        );
    }
}

/// The goal is true and its arithmetic cannot overflow: verified everywhere.
fn verified_everywhere(
    label: &str,
    params: &[(&str, TrustVcType)],
    req: &[TrustVcExpr],
    goal: &TrustVcExpr,
) {
    for (kind, exec) in [
        (Goal::Ensures, false),
        (Goal::Ensures, true),
        (Goal::Assert, false),
        (Goal::Assert, true),
    ] {
        let r = run(params, req, goal.clone(), kind, exec);
        assert!(
            r.is_verified(),
            "{label} (exec={exec}): true goal not verified: {r:?}"
        );
    }
}

/// `29878u16 * -256 >= 28688i16`: the `-256` an `Int{32}` literal (and the
/// `Neg(IntLit 256)` spelling), with 0..2 pinned `u128` decoys steering the
/// context's literal width, `x` a literal or a pinned variable. Exact:
/// -7648768; in `u16`: 18944 — both below 28688. The product declared at its
/// derived `int` decides both; declared `u16` (what its operands do not
/// derive) it is refused (§5b rule 13).
#[test]
fn typed_u16_times_negative_untyped_literal() {
    for decoys in 0..3 {
        for x_is_var in [false, true] {
            for neg_form in [false, true] {
                let mut params: Vec<(String, TrustVcType)> = Vec::new();
                let mut req = Vec::new();
                for i in 0..decoys {
                    let n = format!("d{i}");
                    req.push(pin(&n, &u128t(), 7));
                    params.push((n, u128t()));
                }
                let x = if x_is_var {
                    req.push(pin("x", &u16t(), 29878));
                    params.push(("x".to_string(), u16t()));
                    var("x", u16t())
                } else {
                    lit(29878, u16t())
                };
                let m = if neg_form {
                    neg(lit(256, i32t()))
                } else {
                    lit(-256, i32t())
                };
                let p: Vec<(&str, TrustVcType)> = params
                    .iter()
                    .map(|(n, t)| (n.as_str(), t.clone()))
                    .collect();
                let lie = arith(ArithOp::Mul, x.clone(), m.clone(), u16t());
                let product = arith(ArithOp::Mul, x, m, TrustVcType::MathInt);
                let label = format!("decoys={decoys} x_var={x_is_var} neg_form={neg_form}");
                refused_everywhere(
                    &label,
                    &p,
                    &req,
                    &cmp(CompareOp::Ge, lie, lit(28688, i16t())),
                );
                refuted_everywhere(
                    &label,
                    &p,
                    &req,
                    &cmp(CompareOp::Ge, product.clone(), lit(28688, i16t())),
                );
                // True twin (exact): the product is negative.
                let twin = cmp(CompareOp::Eq, product, lit(-7_648_768, i32t()));
                for exec in [false, true] {
                    let r = run(&p, &req, twin.clone(), Goal::Ensures, exec);
                    assert!(r.is_verified(), "{label} twin (exec={exec}): {r:?}");
                }
            }
        }
    }
}

fn ctx64_params() -> Vec<(&'static str, TrustVcType)> {
    vec![("x", u8t()), ("a", u64t()), ("b", u64t())]
}
fn ctx64_requires(x: i128) -> Vec<TrustVcExpr> {
    vec![
        pin("x", &u8t(), x),
        pin("a", &u64t(), 1000),
        pin("b", &u64t(), 0),
    ]
}

/// `x + (-1) >= 256u64` / `> a` and `x * (-1) > a`, `x: u8`, the `-1` an
/// `Int{32}` literal (or `Neg(IntLit 1)`), in a context whose literal width
/// is 64. Exact: -1; in `u8`: 255 — neither reaches 256 or 1000. Declared at
/// the derived `int`; declared `u8`, the node is refused (§5b rule 13).
#[test]
fn typed_u8_with_negative_untyped_literal_in_a_wide_context() {
    let minus_one = [lit(-1, i32t()), neg(lit(1, i32t()))];
    for m in &minus_one {
        refused_everywhere(
            "x + (-1) declared u8",
            &ctx64_params(),
            &ctx64_requires(0),
            &cmp(
                CompareOp::Ge,
                arith(ArithOp::Add, var("x", u8t()), m.clone(), u8t()),
                lit(256, u64t()),
            ),
        );
        let sum = arith(
            ArithOp::Add,
            var("x", u8t()),
            m.clone(),
            TrustVcType::MathInt,
        );
        refuted_everywhere(
            "x + (-1) >= 256u64",
            &ctx64_params(),
            &ctx64_requires(0),
            &cmp(CompareOp::Ge, sum.clone(), lit(256, u64t())),
        );
        refuted_everywhere(
            "x + (-1) > a",
            &ctx64_params(),
            &ctx64_requires(0),
            &cmp(CompareOp::Gt, sum.clone(), var("a", u64t())),
        );
        let product = arith(
            ArithOp::Mul,
            var("x", u8t()),
            m.clone(),
            TrustVcType::MathInt,
        );
        refuted_everywhere(
            "x * (-1) > a",
            &ctx64_params(),
            &ctx64_requires(1),
            &cmp(CompareOp::Gt, product.clone(), var("a", u64t())),
        );
        verified_everywhere(
            "x + (-1) < 0",
            &ctx64_params(),
            &ctx64_requires(0),
            &cmp(CompareOp::Lt, sum, lit(0, u64t())),
        );
        verified_everywhere(
            "x * (-1) == -1",
            &ctx64_params(),
            &ctx64_requires(1),
            &cmp(CompareOp::Eq, product, lit(-1, i64t())),
        );
    }
    // The same with no wide context at all.
    let sum = arith(
        ArithOp::Add,
        var("x", u8t()),
        lit(-1, i32t()),
        TrustVcType::MathInt,
    );
    refuted_everywhere(
        "ctx8 x + (-1) >= 256u64",
        &[("x", u8t())],
        &[pin("x", &u8t(), 0)],
        &cmp(CompareOp::Ge, sum, lit(256, u64t())),
    );
}

/// `-x0 cmp z` with `x0: i32` pinned: `-x0` is the `i32` negation, never the
/// peer type's. `-(-128) == 128`, `-(-32768) == 32768`; exec `assert` of
/// `-i32::MIN` overflows.
#[test]
fn typed_negation_of_a_pinned_i32_keeps_its_type() {
    let cases = [
        (-128i128, i8t(), CompareOp::Lt),
        (-32768, i16t(), CompareOp::Le),
    ];
    for (x0, peer, op) in cases {
        let params = [("x0", i32t()), ("z", peer.clone())];
        let req = [pin("x0", &i32t(), x0), pin("z", &peer, 0)];
        refuted_everywhere(
            "-x0 vs peer",
            &params,
            &req,
            &cmp(op, neg(var("x0", i32t())), var("z", peer.clone())),
        );
        verified_everywhere(
            "-x0 == -value",
            &params,
            &req,
            &cmp(CompareOp::Eq, neg(var("x0", i32t())), lit(-x0, i32t())),
        );
    }
    let params = [("x0", i32t()), ("z", i64t())];
    let req = [
        pin("x0", &i32t(), i128::from(i32::MIN)),
        pin("z", &i64t(), 0),
    ];
    let r = run(
        &params,
        &req,
        cmp(CompareOp::Gt, neg(var("x0", i32t())), var("z", i64t())),
        Goal::Assert,
        true,
    );
    assert!(
        is_refuted(&r),
        "exec assert -i32::MIN > 0i64 must refute (overflow): {r:?}"
    );
}

/// `===` compares the VALUES: `255u8 === -1i8` and `u64::MAX === -1i16`
/// are false; `255u8 === 255i16` and `-1i8 === -1i64` are true.
#[test]
fn typed_strict_eq_compares_values() {
    let false_pairs = [
        ((u8t(), 255i128), (i8t(), -1i128)),
        ((u64t(), i128::from(u64::MAX)), (i16t(), -1)),
        ((u32t(), 128), (i8t(), -128)),
    ];
    for ((lt, lv), (rt, rv)) in false_pairs {
        let params = [("x", lt.clone()), ("y", rt.clone())];
        let req = [pin("x", &lt, lv), pin("y", &rt, rv)];
        refuted_everywhere(
            "===",
            &params,
            &req,
            &strict_eq(var("x", lt.clone()), var("y", rt.clone())),
        );
    }
    let true_pairs = [
        ((u8t(), 255i128), (i16t(), 255i128)),
        ((i8t(), -1), (i64t(), -1)),
    ];
    for ((lt, lv), (rt, rv)) in true_pairs {
        let params = [("x", lt.clone()), ("y", rt.clone())];
        let req = [pin("x", &lt, lv), pin("y", &rt, rv)];
        verified_everywhere(
            "===",
            &params,
            &req,
            &strict_eq(var("x", lt.clone()), var("y", rt.clone())),
        );
    }
}

/// `by(bit_vector)`: an amount at or above the width shifts every bit out,
/// whatever the amount's own width — `1u8 << 8u32`, `1u8 << 256u16`,
/// `1u8 >> 256u32` are all 0, and none is 1 (the amount used to be narrowed
/// by bit extraction, so `1u8 << 256u16` was `1u8 << 0`).
#[test]
fn typed_bit_vector_shift_amount_is_never_truncated() {
    let amounts = [
        (u32t(), 8i128),
        (u16t(), 256),
        (u32t(), 256),
        (u64t(), 264),
        (u16t(), 9),
    ];
    for (kt, k) in amounts {
        for op in [SpecialArithOp::Shl, SpecialArithOp::Shr] {
            let shifted = TrustVcExpr::SpecialArith {
                op,
                left: Box::new(var("x", u8t())),
                right: Box::new(var("k", kt.clone())),
                ty: u8t(),
            };
            let params = [("x", u8t()), ("k", kt.clone())];
            let req = [pin("x", &u8t(), 1), pin("k", &kt, k)];
            let zero = run(
                &params,
                &req,
                cmp(CompareOp::Eq, shifted.clone(), lit(0, u8t())),
                Goal::BitVectorAssert,
                false,
            );
            assert!(
                zero.is_verified(),
                "1u8 {op:?} {k}:{kt:?} == 0 must verify: {zero:?}"
            );
            let one = run(
                &params,
                &req,
                cmp(CompareOp::Eq, shifted, lit(1, u8t())),
                Goal::BitVectorAssert,
                false,
            );
            assert!(
                is_refuted(&one),
                "1u8 {op:?} {k}:{kt:?} == 1 must refute: {one:?}"
            );
        }
    }
    // Signed `>>` fills with the sign bit.
    let shifted = TrustVcExpr::SpecialArith {
        op: SpecialArithOp::Shr,
        left: Box::new(var("x", i8t())),
        right: Box::new(var("k", u16t())),
        ty: i8t(),
    };
    let params = [("x", i8t()), ("k", u16t())];
    let req = [pin("x", &i8t(), -3), pin("k", &u16t(), 256)];
    let fill = run(
        &params,
        &req,
        cmp(CompareOp::Eq, shifted, lit(-1, i8t())),
        Goal::BitVectorAssert,
        false,
    );
    assert!(
        fill.is_verified(),
        "-3i8 >> 256u16 == -1 must verify: {fill:?}"
    );
}

/// An untyped literal TREE takes its peer's type when every literal in it
/// does, and is then that type's arithmetic: `(i32::MIN - 0) - 256908456` next
/// to an `i64` is `i64` arithmetic, -2404392104 (Rust infers `i64` for every
/// literal; Verus computes it over `int`; they agree). Next to an untyped `0`
/// there is no peer: it is `i32` arithmetic, Rust's default literal type, and
/// wraps.
#[test]
fn typed_untyped_literal_tree_is_typed_by_its_peer() {
    let tree = || {
        arith(
            ArithOp::Sub,
            arith(
                ArithOp::Sub,
                lit(i128::from(i32::MIN), i32t()),
                lit(0, i32t()),
                i32t(),
            ),
            lit(256_908_456, i32t()),
            i32t(),
        )
    };
    for exec in [false, true] {
        let at_i64 = run(
            &[("a", i64t())],
            &[pin("a", &i64t(), 0)],
            cmp(CompareOp::Le, tree(), lit(0, i64t())),
            Goal::Ensures,
            exec,
        );
        assert!(
            at_i64.is_verified(),
            "tree <= 0i64 (exec={exec}): {at_i64:?}"
        );
        let above = run(
            &[("a", i64t())],
            &[pin("a", &i64t(), 0)],
            cmp(CompareOp::Gt, tree(), lit(0, i64t())),
            Goal::Ensures,
            exec,
        );
        assert!(is_refuted(&above), "tree > 0i64 (exec={exec}): {above:?}");
    }
    let untyped_peer = run(
        &[("a", i64t())],
        &[pin("a", &i64t(), 0)],
        cmp(CompareOp::Gt, tree(), lit(0, i32t())),
        Goal::Ensures,
        false,
    );
    assert!(
        untyped_peer.is_verified(),
        "i32 tree wraps to 1890575192 > 0: {untyped_peer:?}"
    );
}

/// The pre-solve constant evaluator folded `-(-128i8)` to 128 (exact) and
/// `-13i16 / 256u16` to the truncating 0 of the node's declared `u16`: every
/// fold now takes the DERIVED type and declines what that type cannot hold.
/// (The quotient declared `u16`, a claim its operands do not derive, is
/// refused before any fold — §5b rule 13; declared at its derived `int`, it
/// is the Euclidean -1.)
#[test]
fn typed_constant_folding_uses_the_derived_type() {
    let no_vars: [(&str, TrustVcType); 0] = [];
    for exec in [false, true] {
        let wrapped = run(
            &no_vars,
            &[],
            cmp(CompareOp::Eq, neg(lit(-128, i8t())), lit(128, i16t())),
            Goal::Ensures,
            exec,
        );
        assert!(
            is_refuted(&wrapped),
            "-(-128i8) == 128 (exec={exec}): {wrapped:?}"
        );
        let lie = arith(ArithOp::Div, lit(-13, i16t()), lit(256, u16t()), u16t());
        let refused = run(
            &no_vars,
            &[],
            cmp(CompareOp::Eq, lie, lit(0, i32t())),
            Goal::Ensures,
            exec,
        );
        assert!(
            matches!(
                refused,
                VerifyResult::Unknown { .. } | VerifyResult::Error { .. }
            ),
            "-13i16 / 256u16 declared u16 (exec={exec}): {refused:?}"
        );
        let quotient = arith(
            ArithOp::Div,
            lit(-13, i16t()),
            lit(256, u16t()),
            TrustVcType::MathInt,
        );
        let euclid = run(
            &no_vars,
            &[],
            cmp(CompareOp::Eq, quotient.clone(), lit(-1, i32t())),
            Goal::Ensures,
            exec,
        );
        assert!(
            euclid.is_verified(),
            "-13i16 / 256u16 == -1 (exec={exec}): {euclid:?}"
        );
        let truncated = run(
            &no_vars,
            &[],
            cmp(CompareOp::Eq, quotient, lit(0, i32t())),
            Goal::Ensures,
            exec,
        );
        assert!(
            is_refuted(&truncated),
            "-13i16 / 256u16 == 0 (exec={exec}): {truncated:?}"
        );
    }
}
