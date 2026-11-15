//! Mechanical check: comparisons and arithmetic over operands of EVERY integer
//! width and BOTH signednesses decide exactly what an `i128` evaluation says.
//!
//! Every generated VC pins its operands to concrete values (a variable `xN`
//! with `requires xN == v`, a literal, or a negated literal), so the only
//! acceptable verdicts are `Verified` for a true goal and a refutation for a
//! false one; anything else fails the property.
//!
//! The generators are biased at the failure class this file exists for: ay
//! hash-conses BV constants, so the same bits read with the opposite sign
//! (`255u8` / `-1i8`, `u64::MAX` / `-1i64`) are ONE term, and a signedness read
//! from a term-keyed table belongs to whichever occurrence registered last.
//! `shared_bits_pair` generates exactly such pairs; the Route A properties put
//! a spec-collection length (an Int term) next to BV peers of every width.
//!
//! Seeds are fixed so a failure reproduces; persistence is off (no files).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use proptest::prelude::*;
use proptest::test_runner::RngSeed;
use trust_vc_core::ir::{ArithOp, CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntTy {
    width: u32,
    signed: bool,
}

impl IntTy {
    fn ir(self) -> TrustVcType {
        if self.signed {
            TrustVcType::Int { width: self.width }
        } else {
            TrustVcType::Uint { width: self.width }
        }
    }

    fn min(self) -> i128 {
        match (self.signed, self.width) {
            (false, _) => 0,
            (true, 128) => i128::MIN,
            (true, w) => -(1i128 << (w - 1)),
        }
    }

    /// The largest value the `i128` oracle can hold: `u128` is capped at
    /// `i128::MAX`.
    fn max(self) -> i128 {
        match (self.signed, self.width) {
            (true, 128) | (false, 128) => i128::MAX,
            (true, w) => (1i128 << (w - 1)) - 1,
            (false, w) => (1i128 << w) - 1,
        }
    }

    fn contains(self, value: i128) -> bool {
        (self.min()..=self.max()).contains(&value)
    }

    /// The value the low `width` bits of `bits` denote under this type, or
    /// `None` when it does not fit the oracle (a `u128` at or above 2^127).
    fn decode_bits(self, bits: u128) -> Option<i128> {
        let shift = 128 - self.width;
        let masked = (bits << shift) >> shift;
        // Signed: sign-extend the low `width` bits (the `as` reinterprets).
        #[allow(clippy::cast_possible_wrap)]
        let signed = ((masked << shift) as i128) >> shift;
        if self.signed {
            Some(signed)
        } else {
            i128::try_from(masked).ok()
        }
    }

    /// Two's-complement wrap of an exact result into this type.
    fn wrap(self, exact: i128) -> Option<i128> {
        #[allow(clippy::cast_sign_loss)]
        self.decode_bits(exact as u128)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// A variable `xN: T` pinned by `requires xN == v`.
    Var,
    /// `IntLit { value: v, ty: T }`.
    Lit,
    /// `Neg(IntLit { value: -v, ty: T })` — how lowering spells a negative
    /// literal (only generated for a negative `v > MIN`).
    NegLit,
}

#[derive(Debug, Clone, Copy)]
struct Operand {
    ty: IntTy,
    value: i128,
    form: Form,
}

/// Collects the variables and pinning `requires` an expression needs.
#[derive(Default)]
struct Ctx {
    params: Vec<(String, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
}

impl Ctx {
    fn operand(&mut self, operand: Operand) -> TrustVcExpr {
        let ty = operand.ty.ir();
        match operand.form {
            Form::Var => {
                let name = format!("x{}", self.params.len());
                let var = TrustVcExpr::Var {
                    name: name.clone(),
                    ty: ty.clone(),
                };
                self.requires.push(cmp(
                    CompareOp::Eq,
                    var.clone(),
                    lit(operand.value, ty.clone()),
                ));
                self.params.push((name, ty));
                var
            }
            Form::NegLit if operand.value < 0 && operand.value != operand.ty.min() => {
                TrustVcExpr::Neg(Box::new(lit(-operand.value, ty)))
            }
            Form::Lit | Form::NegLit => lit(operand.value, ty),
        }
    }

    fn run(self, ensures: TrustVcExpr, exec: bool) -> (Verdict, VerifyResult) {
        self.run_as(ensures, exec, Goal::Ensures)
    }

    fn run_as(self, goal: TrustVcExpr, exec: bool, kind: Goal) -> (Verdict, VerifyResult) {
        let mut variables: Vec<VariableDecl> = self
            .params
            .iter()
            .map(|(name, ty)| VariableDecl::new(name.clone(), ty.clone()))
            .collect();
        variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
        let mut obligations: Vec<TypedProofObligation> = self
            .requires
            .into_iter()
            .enumerate()
            .map(|(i, req)| TypedProofObligation::requires(format!("p_requires_{i}"), req))
            .collect();
        obligations.push(match kind {
            Goal::Ensures => TypedProofObligation::ensures("p_ensures_0", goal),
            Goal::Assert => TypedProofObligation::assert("p_assert_0", goal),
        });
        let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
        if exec {
            ctx.enable_overflow_checks();
        }
        let raw = ctx.verify();
        let verdict = match &raw {
            VerifyResult::Verified => Verdict::Verified,
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => {
                Verdict::Refuted
            }
            _ => Verdict::Other,
        };
        (verdict, raw)
    }
}

/// The goal's obligation: an `ensures` is SPEC arithmetic (never overflow-
/// checked: a fixed-width result wraps), an `assert` is overflow-checked exec.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Goal {
    Ensures,
    Assert,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Verified,
    Refuted,
    Other,
}

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// The i128 oracle: `Verified` iff `left <op> right` holds, else `Refuted`.
fn oracle(op: CompareOp, left: i128, right: i128) -> Verdict {
    let holds = match op {
        CompareOp::Eq => left == right,
        CompareOp::Ne => left != right,
        CompareOp::Lt => left < right,
        CompareOp::Le => left <= right,
        CompareOp::Gt => left > right,
        CompareOp::Ge => left >= right,
        other => panic!("no oracle for {other:?}"),
    };
    if holds {
        Verdict::Verified
    } else {
        Verdict::Refuted
    }
}

fn int_ty() -> impl Strategy<Value = IntTy> {
    (prop::sample::select(WIDTHS.to_vec()), any::<bool>())
        .prop_map(|(width, signed)| IntTy { width, signed })
}

/// Values of `ty`, biased toward its edges and its sign-bit boundary.
fn value_in(ty: IntTy) -> BoxedStrategy<i128> {
    let (min, max) = (ty.min(), ty.max());
    let half = i128::MAX >> (128 - ty.width);
    let mut edges = vec![min, max, 0, 1, half, half.saturating_add(1).min(max)];
    if ty.signed {
        edges.push(-1);
        edges.push(min + 1);
    }
    prop_oneof![
        2 => prop::sample::select(edges),
        1 => -8i128..=8,
        3 => min..=max,
    ]
    .prop_filter("in range", move |value| ty.contains(*value))
    .boxed()
}

fn form() -> impl Strategy<Value = Form> {
    prop_oneof![Just(Form::Var), Just(Form::Lit), Just(Form::NegLit)]
}

fn operand_of(ty: IntTy) -> impl Strategy<Value = Operand> {
    (value_in(ty), form()).prop_map(move |(value, form)| Operand { ty, value, form })
}

fn operand() -> impl Strategy<Value = Operand> {
    int_ty().prop_flat_map(operand_of)
}

/// Two operands of ONE width holding the SAME bits under OPPOSITE
/// signedness — one hash-consed BV term, two different integers.
fn shared_bits_pair() -> impl Strategy<Value = (Operand, Operand)> {
    let bits = prop_oneof![
        Just(u128::MAX),
        Just(1u128 << 127),
        Just(0xC8u128),
        Just(0xFFu128),
        any::<u128>(),
    ];
    let widths = prop::sample::select(WIDTHS.to_vec());
    (widths, bits, form(), form(), any::<bool>()).prop_filter_map(
        "both readings fit the oracle",
        |(width, bits, f1, f2, swap)| {
            let reading = |signed, form| {
                let ty = IntTy { width, signed };
                ty.decode_bits(bits)
                    .map(|value| Operand { ty, value, form })
            };
            let (u, s) = (reading(false, f1)?, reading(true, f2)?);
            Some(if swap { (s, u) } else { (u, s) })
        },
    )
}

/// `Int { width: 32 }` is also the UNSUFFIXED-literal placeholder, typed by its
/// peer (`coerce_default_int_literal`), so an all-literal `i32` pair has no `i32`
/// meaning to check: keep one variable (which must then stay `i32`).
fn explicit_i32_tree((mut x, y): (Operand, Operand)) -> (Operand, Operand) {
    if x.ty
        == (IntTy {
            width: 32,
            signed: true,
        })
        && x.form != Form::Var
        && y.form != Form::Var
    {
        x.form = Form::Var;
    }
    (x, y)
}

fn operand_pair() -> impl Strategy<Value = (Operand, Operand)> {
    prop_oneof![(operand(), operand()), shared_bits_pair()]
}

fn compare_op() -> impl Strategy<Value = CompareOp> {
    prop::sample::select(vec![
        CompareOp::Eq,
        CompareOp::Ne,
        CompareOp::Lt,
        CompareOp::Le,
        CompareOp::Gt,
        CompareOp::Ge,
    ])
}

/// A spec-collection receiver whose `.len()` is an Int term (Route A): the
/// driver's `&str` view (length typed `i64`) or a `Seq<u8>` (`usize`).
#[derive(Debug, Clone, Copy)]
enum Receiver {
    Str,
    Seq,
}

impl Receiver {
    fn param(self) -> (String, TrustVcType) {
        match self {
            Self::Str => ("a".to_string(), TrustVcType::StrSlice),
            Self::Seq => (
                "s".to_string(),
                TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 })),
            ),
        }
    }

    fn len_ty(self) -> TrustVcType {
        match self {
            Self::Str => TrustVcType::Int { width: 64 },
            Self::Seq => TrustVcType::Uint { width: 64 },
        }
    }

    fn len(self) -> TrustVcExpr {
        let (name, ty) = self.param();
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver: Box::new(TrustVcExpr::Var {
                name: name.clone(),
                ty,
            }),
            receiver_name: Some(name),
            args: vec![],
            ty: self.len_ty(),
        }
    }
}

fn config(seed: u64) -> ProptestConfig {
    ProptestConfig {
        cases: 256,
        failure_persistence: None,
        rng_seed: RngSeed::Fixed(seed),
        ..ProptestConfig::default()
    }
}

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(config(0x5167_0001))]

    /// `l <op> r` for two operands of any widths and signednesses.
    #[test]
    fn compare_matches_integer_order(
        (left, right) in operand_pair(),
        op in compare_op(),
        exec in any::<bool>(),
    ) {
        let mut ctx = Ctx::default();
        let l = ctx.operand(left);
        let r = ctx.operand(right);
        let ensures = cmp(op, l, r);
        let want = oracle(op, left.value, right.value);
        let (got, raw) = ctx.run(ensures.clone(), exec);
        prop_assert_eq!(
            got,
            want,
            "{}",
            format!("{left:?} {op:?} {right:?} (exec={exec})\n  {ensures:?}\n  {raw:?}")
        );
    }
}

proptest! {
    #![proptest_config(config(0x5167_0002))]

    /// `(len ± v) <op> w` with `len` a pinned spec-collection length (an Int
    /// term) and `v`, `w` BV operands of any widths and signednesses —
    /// including `w` sharing its bits with `v` under the other sign.
    #[test]
    fn length_arithmetic_matches_integer_arithmetic(
        receiver in prop_oneof![Just(Receiver::Str), Just(Receiver::Seq)],
        len in 0i128..=3,
        add in any::<bool>(),
        (peer, bound) in operand_pair(),
        op in compare_op(),
        exec in any::<bool>(),
    ) {
        let exact = if add { len.checked_add(peer.value) } else { len.checked_sub(peer.value) };
        prop_assume!(exact.is_some());
        let exact = exact.unwrap_or_default();

        let mut ctx = Ctx::default();
        let param = receiver.param();
        ctx.params.push(param);
        ctx.requires.push(cmp(CompareOp::Eq, receiver.len(), lit(len, receiver.len_ty())));
        let v = ctx.operand(peer);
        let w = ctx.operand(bound);
        let arith_op = if add { ArithOp::Add } else { ArithOp::Sub };
        // Declared at the exact `int` it derives (§5b rule 13).
        let ensures = cmp(op, arith(arith_op, receiver.len(), v, TrustVcType::MathInt), w);
        let want = oracle(op, exact, bound.value);
        let (got, raw) = ctx.run(ensures.clone(), exec);
        prop_assert_eq!(
            got,
            want,
            "{}",
            format!(
                "{receiver:?}.len()=={len} add={add} {peer:?} {op:?} {bound:?} (exec={exec})\n  \
                 {ensures:?}\n  {raw:?}"
            )
        );
    }
}

proptest! {
    #![proptest_config(config(0x5167_0003))]

    /// `(x <op2> y) <op> z`: `x`, `y` of one type `T` (the node's), `z` of any
    /// width and signedness. A fixed-width result wraps into `T` — except for
    /// an `assert` under exec semantics, where an overflowing result is
    /// refuted (its no-overflow obligation fails) and any other result is
    /// compared exactly. An `ensures` is spec arithmetic: never
    /// overflow-checked, and (the regression this pins) never ASSUMED
    /// overflow-free either.
    #[test]
    fn bv_arithmetic_then_compare_matches_integer_semantics(
        (x, y) in int_ty()
            .prop_flat_map(|ty| (operand_of(ty), operand_of(ty)))
            .prop_map(explicit_i32_tree),
        arith_op in prop_oneof![Just(ArithOp::Add), Just(ArithOp::Sub), Just(ArithOp::Mul)],
        z in operand(),
        op in compare_op(),
        exec in any::<bool>(),
        kind in prop_oneof![Just(Goal::Ensures), Just(Goal::Assert)],
    ) {
        let ty = x.ty;
        prop_assume!(!matches!(arith_op, ArithOp::Mul) || ty.width <= 32);
        let exact = match arith_op {
            ArithOp::Add => x.value.checked_add(y.value),
            ArithOp::Sub => x.value.checked_sub(y.value),
            _ => x.value.checked_mul(y.value),
        };
        prop_assume!(exact.is_some());
        let exact = exact.unwrap_or_default();
        let overflows = !ty.contains(exact);
        let want = if exec && kind == Goal::Assert {
            if overflows {
                Verdict::Refuted
            } else {
                oracle(op, exact, z.value)
            }
        } else {
            let wrapped = ty.wrap(exact);
            prop_assume!(wrapped.is_some());
            oracle(op, wrapped.unwrap_or_default(), z.value)
        };

        let mut ctx = Ctx::default();
        let l = ctx.operand(x);
        let r = ctx.operand(y);
        let rz = ctx.operand(z);
        let ensures = cmp(op, arith(arith_op, l, r, ty.ir()), rz);
        let (got, raw) = ctx.run_as(ensures.clone(), exec, kind);
        prop_assert_eq!(
            got,
            want,
            "{}",
            format!(
                "({x:?} {arith_op:?} {y:?}) {op:?} {z:?} ({kind:?}, exec={exec})\n  \
                 {ensures:?}\n  {raw:?}"
            )
        );
    }
}
