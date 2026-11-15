//! Property check of trust-vc's INTEGER SEMANTICS against an `i128` oracle,
//! over every width and both signednesses, every operand form, both
//! frontends, exec and non-exec (design-trust-proof-backend.md §5b):
//!
//! * the type of an arithmetic / bitwise / conditional result is DERIVED from
//!   both operands: one fixed-width type `T` computes in `T` (two's
//!   complement; an exec `assert` refutes on overflow); DIFFERENT fixed-width
//!   types compute the EXACT integer (Verus spec arithmetic over `int`; `/`
//!   and `%` Euclidean, as Verus's `int` division is);
//! * comparisons, `===`, conditionals and bitwise results over mixed types
//!   are decided on the integers the operands denote;
//! * an untyped literal (the `Int { width: 32 }` placeholder) takes its
//!   peer's type only when its value fits — never a value change;
//! * a shift keeps its left operand's type; under `by(bit_vector)` an amount
//!   at or above the width shifts every bit out, whatever the amount's width;
//! * the source frontend checks an exec function's `ensures` arithmetic for
//!   overflow: a same-type operation that leaves its type is refuted.
//!
//! Every generated VC pins its operands to concrete values (a variable with
//! `requires x == v`, which equality substitution then exercises, a literal,
//! a negated literal, or an untyped literal), so the goal is decided: a
//! `Verified` for a false goal (FALSE VERIFIED) or a refutation of a true one
//! (FALSE COUNTEREXAMPLE) fails the property. `Unknown` is reported and
//! tolerated (fail-closed), but a shape whose every case is Unknown fails —
//! a property that decides nothing checks nothing.
//!
//! Deterministic: `INTEGER_TYPING_SEED` (default below) and
//! `INTEGER_TYPING_CASES` (cases per shape) steer the generator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::fmt::Write as _;
use std::io::Write as _;

use trust_vc_core::ir::{
    ArithOp, CollectionOp, CompareOp, SpecialArithOp, TrustVcExpr, TrustVcType,
};
use trust_vc_core::vc::{SolverMode, TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

// ---------------------------------------------------------------------------
// Types and the oracle's arithmetic.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct T {
    w: u32,
    s: bool,
}

const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

impl T {
    fn ir(self) -> TrustVcType {
        if self.s {
            TrustVcType::Int { width: self.w }
        } else {
            TrustVcType::Uint { width: self.w }
        }
    }
    fn rust(self) -> String {
        format!("{}{}", if self.s { "i" } else { "u" }, self.w)
    }
    fn min(self) -> i128 {
        match (self.s, self.w) {
            (false, _) => 0,
            (true, 128) => i128::MIN,
            (true, w) => -(1i128 << (w - 1)),
        }
    }
    /// The oracle holds `u128` values below 2^127 only.
    fn max(self) -> i128 {
        match (self.s, self.w) {
            (_, 128) => i128::MAX,
            (true, w) => (1i128 << (w - 1)) - 1,
            (false, w) => (1i128 << w) - 1,
        }
    }
    fn contains(self, v: i128) -> bool {
        (self.min()..=self.max()).contains(&v)
    }
    /// The value of the low `w` bits of `bits` read as this type (`None`
    /// for a `u128` value the oracle cannot hold).
    fn decode_bits(self, bits: u128) -> Option<i128> {
        let shift = 128 - self.w;
        let masked = (bits << shift) >> shift;
        #[allow(clippy::cast_possible_wrap)]
        let signed = ((masked << shift) as i128) >> shift;
        if self.s {
            Some(signed)
        } else {
            i128::try_from(masked).ok()
        }
    }
    #[allow(clippy::cast_sign_loss)]
    fn wrap(self, exact: i128) -> Option<i128> {
        self.decode_bits(exact as u128)
    }
}

fn all_types() -> Vec<T> {
    WIDTHS
        .iter()
        .flat_map(|&w| [T { w, s: false }, T { w, s: true }])
        .collect()
}

const PLACEHOLDER: TrustVcType = TrustVcType::Int { width: 32 };
const I32: T = T { w: 32, s: true };

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Verified,
    Refuted,
    Unknown,
}

fn verdict_of(result: &VerifyResult) -> Verdict {
    match result {
        VerifyResult::Verified => Verdict::Verified,
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => Verdict::Refuted,
        _ => Verdict::Unknown,
    }
}

fn holds(op: CompareOp, l: i128, r: i128) -> bool {
    match op {
        CompareOp::Eq => l == r,
        CompareOp::Ne => l != r,
        CompareOp::Lt => l < r,
        CompareOp::Le => l <= r,
        CompareOp::Gt => l > r,
        CompareOp::Ge => l >= r,
        other => unreachable!("not generated: {other:?}"),
    }
}

fn expected(truth: bool) -> Verdict {
    if truth {
        Verdict::Verified
    } else {
        Verdict::Refuted
    }
}

const OPS: [CompareOp; 6] = [
    CompareOp::Eq,
    CompareOp::Ne,
    CompareOp::Lt,
    CompareOp::Le,
    CompareOp::Gt,
    CompareOp::Ge,
];

fn rust_cmp(op: CompareOp) -> &'static str {
    match op {
        CompareOp::Eq => "==",
        CompareOp::Ne => "!=",
        CompareOp::Lt => "<",
        CompareOp::Le => "<=",
        CompareOp::Gt => ">",
        CompareOp::Ge => ">=",
        other => unreachable!("not generated: {other:?}"),
    }
}

/// `l op r` over the integers; `None` when it does not exist or the `i128`
/// oracle cannot hold it. `/` and `%` are Euclidean (Verus `int`).
fn exact(op: ArithOp, l: i128, r: i128) -> Option<i128> {
    match op {
        ArithOp::Add => l.checked_add(r),
        ArithOp::Sub => l.checked_sub(r),
        ArithOp::Mul => l.checked_mul(r),
        ArithOp::Div => (r != 0).then(|| l.checked_div_euclid(r)).flatten(),
        ArithOp::Rem => (r != 0).then(|| l.checked_rem_euclid(r)).flatten(),
        _ => None,
    }
}

/// `l op r` in the fixed-width type `t`: `(value, overflowed)`. `/` and `%`
/// truncate (Rust); `None` for a zero divisor or `MIN / -1`.
fn in_type(t: T, op: ArithOp, l: i128, r: i128) -> Option<(i128, bool)> {
    match op {
        ArithOp::Div | ArithOp::Rem => {
            if r == 0 || (t.s && l == t.min() && r == -1) {
                return None;
            }
            let v = if op == ArithOp::Div { l / r } else { l % r };
            Some((v, false))
        }
        _ => {
            let e = exact(op, l, r)?;
            Some((t.wrap(e)?, !t.contains(e)))
        }
    }
}

// ---------------------------------------------------------------------------
// Generator.
// ---------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn pick<C: Copy>(&mut self, xs: &[C]) -> C {
        #[allow(clippy::cast_possible_truncation)]
        let i = self.below(xs.len() as u64) as usize;
        xs[i]
    }
    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }
    fn ty(&mut self) -> T {
        self.pick(&all_types())
    }
    /// A value of `t`, biased to the edges and the sign-bit boundary.
    fn value(&mut self, t: T) -> i128 {
        let half = if t.w == 128 {
            i128::MAX
        } else {
            (1i128 << (t.w - 1)) - 1
        };
        let mut edges = vec![t.min(), t.max(), 0, 1, 2, half, half.saturating_add(1)];
        if t.s {
            edges.extend([-1, -2, t.min() + 1, -128, -56, -256]);
        } else {
            edges.extend([200, 255, 128, 256]);
        }
        let v = match self.below(4) {
            0 | 1 => self.pick(&edges),
            #[allow(clippy::cast_possible_wrap)]
            2 => self.below(33) as i128 - 16,
            _ => {
                let raw = (u128::from(self.next()) << 64) | u128::from(self.next());
                t.decode_bits(raw).unwrap_or(0)
            }
        };
        if t.contains(v) {
            v
        } else {
            0
        }
    }
}

fn seed() -> u64 {
    std::env::var("INTEGER_TYPING_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x1a7e_9e25_0924)
}

fn cases() -> usize {
    std::env::var("INTEGER_TYPING_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(48)
}

/// How an operand appears in the VC.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// A variable pinned by `requires x == v` (equality substitution applies).
    Pinned,
    /// A literal of the operand's own type.
    Literal,
    /// `Neg(IntLit { -v })` of the operand's type (negative `v` only).
    NegLiteral,
    /// An untyped literal: `IntLit { v, Int{32} }` — its type comes from the
    /// peer it meets (only when `v` fits).
    Untyped,
}

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}
fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}
fn arith(op: ArithOp, l: TrustVcExpr, r: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty,
    }
}
fn special(op: SpecialArithOp, l: TrustVcExpr, r: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty,
    }
}

/// One generated operand: its expression, value and the type it DENOTES
/// (an untyped literal's type is settled by `settle`).
#[derive(Clone, Debug)]
struct Operand {
    expr: TrustVcExpr,
    value: i128,
    ty: T,
    untyped: bool,
    form: Form,
}

/// A typed-seam VC under construction.
struct Seam {
    params: Vec<(String, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
}

impl Seam {
    fn new() -> Self {
        Self {
            params: Vec::new(),
            requires: Vec::new(),
        }
    }
    fn pinned(&mut self, t: T, v: i128) -> TrustVcExpr {
        let name = format!("x{}", self.params.len());
        let e = var(&name, t.ir());
        self.requires
            .push(cmp(CompareOp::Eq, e.clone(), lit(v, t.ir())));
        self.params.push((name, t.ir()));
        e
    }
    fn operand(&mut self, rng: &mut Rng, t: T, v: i128, allow_untyped: bool) -> Operand {
        let untyped_ok = allow_untyped && I32.contains(v);
        let mut forms = vec![Form::Pinned, Form::Literal];
        if v < 0 && v != t.min() {
            forms.push(Form::NegLiteral);
        }
        if untyped_ok {
            forms.push(Form::Untyped);
        }
        let form = rng.pick(&forms);
        let expr = match form {
            Form::Pinned => self.pinned(t, v),
            Form::Literal => lit(v, t.ir()),
            Form::NegLiteral => TrustVcExpr::Neg(Box::new(lit(-v, t.ir()))),
            Form::Untyped => lit(v, PLACEHOLDER),
        };
        // `Int { width: 32 }` IS the untyped placeholder: an `i32` literal (or
        // negated literal) is typed by its peer like any unsuffixed literal.
        let untyped = form == Form::Untyped || (t == I32 && form != Form::Pinned);
        Operand {
            expr,
            value: v,
            ty: if untyped { I32 } else { t },
            untyped,
            form,
        }
    }
    fn run(self, goal: TrustVcExpr, exec: bool, assert: bool, bv: bool) -> VerifyResult {
        let mut variables: Vec<VariableDecl> = self
            .params
            .iter()
            .map(|(n, t)| VariableDecl::new(n.clone(), t.clone()))
            .collect();
        variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
        let mut obligations: Vec<TypedProofObligation> = self
            .requires
            .into_iter()
            .enumerate()
            .map(|(i, r)| TypedProofObligation::requires(format!("p_requires_{i}"), r))
            .collect();
        let mut goal = if assert {
            TypedProofObligation::assert("p_goal", goal)
        } else {
            TypedProofObligation::ensures("p_goal", goal)
        };
        if bv {
            goal = goal.with_solver_mode(SolverMode::BitVector);
        }
        obligations.push(goal);
        let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
        if exec {
            ctx.enable_overflow_checks();
        }
        ctx.verify()
    }
}

/// The types two operands denote once untyped literals meet their peer:
/// an untyped literal takes the other operand's type when its value fits,
/// `declared` when both are untyped — except that a node DECLARED `i32` reads
/// its `i32` literal as the `i32` it is declared to be next to a non-`i32`
/// peer (design-trust-proof-backend.md §5b rule 7).
fn settle(l: &Operand, r: &Operand, declared: T) -> (T, T) {
    let take = |o: &Operand, peer: T| {
        if (declared == I32 && peer != I32) || !peer.contains(o.value) {
            I32
        } else {
            peer
        }
    };
    match (l.untyped, r.untyped) {
        (true, true) => (take(l, declared), take(r, declared)),
        (true, false) => (take(l, r.ty), r.ty),
        (false, true) => (l.ty, take(r, l.ty)),
        (false, false) => (l.ty, r.ty),
    }
}

// ---------------------------------------------------------------------------
// Tally.
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Tally {
    total: usize,
    decided: usize,
    unknown: usize,
    false_verified: Vec<String>,
    false_counterexample: Vec<String>,
}

impl Tally {
    fn record(
        &mut self,
        shape: &str,
        want: Verdict,
        got: &VerifyResult,
        detail: impl Fn() -> String,
    ) {
        self.total += 1;
        let got_v = verdict_of(got);
        match (want, got_v) {
            (_, Verdict::Unknown) => {
                self.unknown += 1;
                if std::env::var_os("INTEGER_TYPING_VERBOSE").is_some() {
                    println!("UNKNOWN|{shape}|{}|{got:?}", detail());
                }
            }
            (w, g) if w == g => self.decided += 1,
            (Verdict::Refuted, Verdict::Verified) => self
                .false_verified
                .push(format!("FALSE VERIFIED|{shape}|{}", detail())),
            (Verdict::Verified, Verdict::Refuted) => self
                .false_counterexample
                .push(format!("FALSE COUNTEREXAMPLE|{shape}|{}|{got:?}", detail())),
            _ => {}
        }
    }
    fn finish(self, name: &str) {
        println!(
            "SUMMARY {name}: total={} decided={} unknown={} false_verified={} false_counterexample={}",
            self.total,
            self.decided,
            self.unknown,
            self.false_verified.len(),
            self.false_counterexample.len()
        );
        let mut bad = self.false_verified;
        bad.extend(self.false_counterexample);
        assert!(
            bad.is_empty(),
            "{name}: {} wrong verdicts:\n{}",
            bad.len(),
            bad.join("\n")
        );
        assert!(
            self.decided > 0,
            "{name}: no case was decided ({} unknown) — the property checks nothing",
            self.unknown
        );
    }
}

/// A comparison peer of any type and form.
fn peer(rng: &mut Rng, seam: &mut Seam) -> Operand {
    let t = rng.ty();
    let v = rng.value(t);
    seam.operand(rng, t, v, true)
}

// ---------------------------------------------------------------------------
// Typed seam.
// ---------------------------------------------------------------------------

/// `(x op y) cmp z`: operands of one type or two, the node's declared type
/// ANY of the two or a third — the result's type must not be copied from it.
#[test]
fn arithmetic_result_type_is_derived() {
    let mut rng = Rng(seed() ^ 0x01);
    let mut tally = Tally::default();
    for _ in 0..cases() * 3 {
        let op = rng.pick(&[
            ArithOp::Add,
            ArithOp::Sub,
            ArithOp::Mul,
            ArithOp::Div,
            ArithOp::Rem,
        ]);
        let tx = rng.ty();
        let ty = if rng.coin() { tx } else { rng.ty() };
        let (xv, yv) = (rng.value(tx), rng.value(ty));
        let mut seam = Seam::new();
        let x = seam.operand(&mut rng, tx, xv, true);
        let y = seam.operand(&mut rng, ty, yv, !x.untyped);
        let third = rng.ty();
        let declared = rng.pick(&[tx, ty, third]);
        if x.untyped && y.untyped && declared == I32 {
            // A closed untyped tree: typed by the comparison peer it meets
            // (`typed_untyped_literal_tree_is_typed_by_its_exact_value`).
            continue;
        }
        let (lt, rt) = settle(&x, &y, declared);
        let (exec, assert) = (rng.coin(), rng.coin());
        let (value, overflow) = if lt == rt {
            match in_type(lt, op, xv, yv) {
                Some(r) => r,
                None => continue,
            }
        } else {
            match exact(op, xv, yv) {
                Some(v) => (v, false),
                None => continue,
            }
        };
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let goal = cmp(
            cop,
            arith(op, x.expr.clone(), y.expr.clone(), declared.ir()),
            z.expr.clone(),
        );
        let want = if exec && assert && overflow {
            Verdict::Refuted
        } else {
            expected(holds(cop, value, z.value))
        };
        let got = seam.run(goal, exec, assert, false);
        tally.record("arith", want, &got, || {
            format!(
                "({xv}:{tx:?}/{:?} {op:?} {yv}:{ty:?}/{:?}) declared {declared:?} -> {value} (lt={lt:?} rt={rt:?}) {cop:?} {}:{:?}/{:?} exec={exec} assert={assert}",
                x.form, y.form, z.value, z.ty, z.form
            )
        });
    }
    tally.finish("arith");
}

/// `x cmp z` over any two types and forms: the integers they denote.
#[test]
fn comparison_is_over_the_integers() {
    let mut rng = Rng(seed() ^ 0x02);
    let mut tally = Tally::default();
    for _ in 0..cases() {
        let mut seam = Seam::new();
        let tx = rng.ty();
        let xv = rng.value(tx);
        let x = seam.operand(&mut rng, tx, xv, true);
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let exec = rng.coin();
        let want = expected(holds(cop, xv, z.value));
        let got = seam.run(
            cmp(cop, x.expr.clone(), z.expr.clone()),
            exec,
            rng.coin(),
            false,
        );
        tally.record("compare", want, &got, || {
            format!(
                "{xv}:{tx:?}/{:?} {cop:?} {}:{:?}/{:?}",
                x.form, z.value, z.ty, z.form
            )
        });
    }
    tally.finish("compare");
}

/// `(if c { x } else { y }) cmp z`: the chosen branch's value, whatever the
/// two branch types and the declared type.
#[test]
fn conditional_takes_both_branch_types() {
    let mut rng = Rng(seed() ^ 0x03);
    let mut tally = Tally::default();
    for _ in 0..cases() {
        let tx = rng.ty();
        let ty = if rng.coin() { tx } else { rng.ty() };
        let (xv, yv) = (rng.value(tx), rng.value(ty));
        let mut seam = Seam::new();
        let x = seam.operand(&mut rng, tx, xv, true);
        let y = seam.operand(&mut rng, ty, yv, !x.untyped);
        let c = rng.coin();
        let cv = seam.pinned(T { w: 8, s: false }, i128::from(c));
        let cond = cmp(CompareOp::Eq, cv, lit(1, TrustVcType::Uint { width: 8 }));
        let third = rng.ty();
        let declared = rng.pick(&[tx, ty, third]);
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let ite = TrustVcExpr::Ite {
            cond: Box::new(cond),
            then_branch: Box::new(x.expr.clone()),
            else_branch: Box::new(y.expr.clone()),
            ty: declared.ir(),
        };
        let value = if c { xv } else { yv };
        let exec = rng.coin();
        let want = expected(holds(cop, value, z.value));
        let got = seam.run(cmp(cop, ite, z.expr.clone()), exec, false, false);
        tally.record("ite", want, &got, || {
            format!(
                "c={c} {xv}:{tx:?}/{:?} | {yv}:{ty:?}/{:?} declared {declared:?} {cop:?} {}:{:?}/{:?}",
                x.form, y.form, z.value, z.ty, z.form
            )
        });
    }
    tally.finish("ite");
}

/// `(x & | ^ y) cmp z`: the two's-complement result over the integers — for
/// one type it stays in that type; for two it is exact.
#[test]
fn bitwise_result_type_is_derived() {
    let mut rng = Rng(seed() ^ 0x04);
    let mut tally = Tally::default();
    for _ in 0..cases() {
        let tx = rng.ty();
        let ty = if rng.coin() { tx } else { rng.ty() };
        let (xv, yv) = (rng.value(tx), rng.value(ty));
        let mut seam = Seam::new();
        let x = seam.operand(&mut rng, tx, xv, true);
        let y = seam.operand(&mut rng, ty, yv, !x.untyped);
        let op = rng.pick(&[
            SpecialArithOp::BitAnd,
            SpecialArithOp::BitOr,
            SpecialArithOp::BitXor,
        ]);
        let value = match op {
            SpecialArithOp::BitAnd => xv & yv,
            SpecialArithOp::BitOr => xv | yv,
            _ => xv ^ yv,
        };
        let third = rng.ty();
        let declared = rng.pick(&[tx, ty, third]);
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let exec = rng.coin();
        let goal = cmp(
            cop,
            special(op, x.expr.clone(), y.expr.clone(), declared.ir()),
            z.expr.clone(),
        );
        let want = expected(holds(cop, value, z.value));
        let got = seam.run(goal, exec, rng.coin(), false);
        tally.record("bitwise", want, &got, || {
            format!(
                "{xv}:{tx:?}/{:?} {op:?} {yv}:{ty:?}/{:?} declared {declared:?} = {value} {cop:?} {}:{:?}/{:?}",
                x.form, y.form, z.value, z.ty, z.form
            )
        });
    }
    tally.finish("bitwise");
}

/// `-x cmp z` for a signed `x` (pinned — substituted — or literal): the
/// negation in `x`'s type; an exec `assert` refutes `-MIN`.
#[test]
fn negation_stays_in_its_type() {
    let mut rng = Rng(seed() ^ 0x05);
    let mut tally = Tally::default();
    let signed: Vec<T> = all_types().into_iter().filter(|t| t.s).collect();
    for _ in 0..cases() {
        let t = rng.pick(&signed);
        let xv = if rng.coin() { t.min() } else { rng.value(t) };
        let mut seam = Seam::new();
        let pinned = rng.coin();
        let x = if pinned {
            seam.pinned(t, xv)
        } else {
            lit(xv, t.ir())
        };
        let (exec, assert) = (rng.coin(), rng.coin());
        let z = peer(&mut rng, &mut seam);
        // `-v` of an `i32` LITERAL is an untyped form, typed by the peer it
        // meets literal by literal: for `v >= 0` it is the negative literal
        // `-v` (exact); for `v < 0` it is the negation OPERATION of the literal
        // `v`, computed in a signed peer's type when `v` is one of its values,
        // else in `i32` (the default).
        let (value, overflow) = if t == I32 && !pinned {
            let in_type = if xv >= 0 {
                None
            } else if !z.untyped && z.ty.s && z.ty.contains(xv) {
                Some(z.ty)
            } else {
                Some(I32)
            };
            match in_type {
                None => (-xv, false),
                Some(u) => {
                    let exact = xv.checked_neg();
                    let wrapped = exact.and_then(|n| u.wrap(n)).unwrap_or(xv);
                    (wrapped, exact.is_none_or(|n| !u.contains(n)))
                }
            }
        } else {
            (
                xv.checked_neg().and_then(|n| t.wrap(n)).unwrap_or(xv),
                xv == t.min(),
            )
        };
        let cop = rng.pick(&OPS);
        let want = if exec && assert && overflow {
            Verdict::Refuted
        } else {
            expected(holds(cop, value, z.value))
        };
        let got = seam.run(
            cmp(cop, TrustVcExpr::Neg(Box::new(x)), z.expr.clone()),
            exec,
            assert,
            false,
        );
        tally.record("neg", want, &got, || {
            format!(
                "-({xv}:{t:?}) = {value} {cop:?} {}:{:?}/{:?} exec={exec} assert={assert}",
                z.value, z.ty, z.form
            )
        });
    }
    // The equality-substitution class exactly: `-x0` with `x0: i32` pinned,
    // next to a zero peer of every type.
    for peer_t in all_types() {
        for xv in [-128i128, -32768, i128::from(i32::MIN), -1, 127, 128, 32768] {
            for cop in OPS {
                for (exec, assert) in [(false, false), (true, false), (true, true)] {
                    let mut seam = Seam::new();
                    let x = seam.pinned(I32, xv);
                    let z = seam.pinned(peer_t, 0);
                    let overflow = xv == i128::from(i32::MIN);
                    let value = I32.wrap(-xv).unwrap_or(xv);
                    let want = if exec && assert && overflow {
                        Verdict::Refuted
                    } else {
                        expected(holds(cop, value, 0))
                    };
                    let got = seam.run(
                        cmp(cop, TrustVcExpr::Neg(Box::new(x)), z),
                        exec,
                        assert,
                        false,
                    );
                    tally.record("neg-subst", want, &got, || {
                        format!("-(x0:i32=={xv}) = {value} {cop:?} z:{peer_t:?}==0 exec={exec} assert={assert}")
                    });
                }
            }
        }
    }
    tally.finish("neg");
}

/// `x === y` over any two types: equality of the VALUES.
#[test]
fn strict_equality_compares_values() {
    let mut rng = Rng(seed() ^ 0x06);
    let mut tally = Tally::default();
    for _ in 0..cases() {
        let w = rng.pick(&WIDTHS);
        let lt = T { w, s: rng.coin() };
        let rt = if rng.coin() {
            T { w, s: !lt.s }
        } else {
            rng.ty()
        };
        // Same bits, both readings — the pairs `===` used to confuse.
        let bits = rng.pick(&[u128::MAX, 1u128 << 127, 0xC8, 0xFF, 0x80, 5, 0]);
        let (Some(lv), Some(rv)) = (lt.decode_bits(bits), rt.decode_bits(bits)) else {
            continue;
        };
        let mut seam = Seam::new();
        let l = seam.operand(&mut rng, lt, lv, false);
        let r = seam.operand(&mut rng, rt, rv, false);
        let goal = TrustVcExpr::FnCall {
            name: "__trust_vc_strict_eq".to_string(),
            args: vec![l.expr.clone(), r.expr.clone()],
            return_ty: TrustVcType::Bool,
        };
        let exec = rng.coin();
        let want = expected(lv == rv);
        let got = seam.run(goal, exec, false, false);
        tally.record("strict_eq", want, &got, || {
            format!("{lv}:{lt:?}/{:?} === {rv}:{rt:?}/{:?}", l.form, r.form)
        });
    }
    tally.finish("strict_eq");
}

/// `x << k` / `x >> k`: the left operand's type, the amount of any type.
/// Below the width, both modes; at or above it, `by(bit_vector)` only, where
/// every bit is shifted out whatever the amount's own width.
#[test]
fn shift_keeps_the_value_type_and_the_whole_amount() {
    let mut rng = Rng(seed() ^ 0x07);
    let mut tally = Tally::default();
    for _ in 0..cases() * 2 {
        let t = rng.ty();
        let xv = rng.value(t);
        let wide = rng.coin();
        // `by(bit_vector)` refuses a SIGNED amount outright ("possibly negative
        // shift", Verus's rule): wide amounts, which only that mode reads, are
        // unsigned; below the width any amount type is read in both modes.
        let kt = if wide {
            T {
                w: rng.pick(&WIDTHS),
                s: false,
            }
        } else {
            rng.ty()
        };
        let kv: i128 = if wide {
            let candidates = [
                i128::from(t.w),
                i128::from(t.w) + 1,
                256,
                i128::from(t.w) + 256,
                65536,
                kt.max(),
            ];
            rng.pick(&candidates)
        } else {
            i128::from(u32::try_from(rng.below(u64::from(t.w))).unwrap_or(0))
        };
        if !kt.contains(kv) || kv < 0 {
            continue;
        }
        let shl = rng.coin();
        #[allow(clippy::cast_sign_loss)]
        let value = if kv >= i128::from(t.w) {
            if shl || xv >= 0 {
                0
            } else {
                -1
            }
        } else if shl {
            #[allow(clippy::cast_possible_truncation)]
            let k = kv as u32;
            match t.wrap(((xv as u128) << k) as i128) {
                Some(v) => v,
                None => continue,
            }
        } else {
            xv >> kv
        };
        let mut seam = Seam::new();
        let x = if rng.coin() {
            seam.pinned(t, xv)
        } else {
            lit(xv, t.ir())
        };
        let k = if rng.coin() {
            seam.pinned(kt, kv)
        } else {
            lit(kv, kt.ir())
        };
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let op = if shl {
            SpecialArithOp::Shl
        } else {
            SpecialArithOp::Shr
        };
        let goal = cmp(cop, special(op, x, k, t.ir()), z.expr.clone());
        let want = expected(holds(cop, value, z.value));
        // A wide amount is Rust UB in exec code: only the by(bit_vector) reading
        // is a value.
        let bv = wide || (!kt.s && rng.coin());
        let got = seam.run(goal, false, bv, bv);
        tally.record(
            if wide { "shift-wide" } else { "shift" },
            want,
            &got,
            || {
                format!(
                    "{xv}:{t:?} {op:?} {kv}:{kt:?} = {value} {cop:?} {}:{:?}/{:?} bv={bv}",
                    z.value, z.ty, z.form
                )
            },
        );
    }
    tally.finish("shift");
}

/// `(x as U) cmp z`, `U` any fixed-width type or `int`.
#[test]
fn cast_wraps_into_its_target() {
    let mut rng = Rng(seed() ^ 0x08);
    let mut tally = Tally::default();
    for _ in 0..cases() {
        let from = rng.ty();
        let to_int = rng.below(5) == 0;
        let to = rng.ty();
        let xv = rng.value(from);
        let value = if to_int {
            xv
        } else {
            match to.wrap(xv) {
                Some(v) => v,
                None => continue,
            }
        };
        let mut seam = Seam::new();
        let x = seam.operand(&mut rng, from, xv, false);
        let cast = TrustVcExpr::Cast {
            expr: Box::new(x.expr.clone()),
            from_ty: from.ir(),
            to_ty: if to_int {
                TrustVcType::MathInt
            } else {
                to.ir()
            },
        };
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let exec = rng.coin();
        let want = expected(holds(cop, value, z.value));
        let got = seam.run(cmp(cop, cast, z.expr.clone()), exec, false, false);
        tally.record("cast", want, &got, || {
            format!(
                "({xv}:{from:?}/{:?} as {}) = {value} {cop:?} {}:{:?}/{:?}",
                x.form,
                if to_int {
                    "int".to_string()
                } else {
                    format!("{to:?}")
                },
                z.value,
                z.ty,
                z.form
            )
        });
    }
    tally.finish("cast");
}

/// A spec-collection length (an unbounded `Int`) in arithmetic and
/// comparison with fixed-width peers of every type: exact.
#[test]
fn length_arithmetic_is_exact() {
    let mut rng = Rng(seed() ^ 0x09);
    let mut tally = Tally::default();
    let u64t = TrustVcType::Uint { width: 64 };
    for _ in 0..cases() {
        let len = i128::from(u8::try_from(rng.below(4)).unwrap_or(0));
        let mut seam = Seam::new();
        let sname = format!("s{}", seam.params.len());
        let sty = TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }));
        let len_expr = TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver: Box::new(var(&sname, sty.clone())),
            receiver_name: Some(sname.clone()),
            args: vec![],
            ty: u64t.clone(),
        };
        seam.requires
            .push(cmp(CompareOp::Eq, len_expr.clone(), lit(len, u64t.clone())));
        seam.params.push((sname, sty));
        let vt = rng.ty();
        let vv = rng.value(vt);
        let v = seam.operand(&mut rng, vt, vv, true);
        let op = rng.pick(&[ArithOp::Add, ArithOp::Sub, ArithOp::Mul]);
        let Some(value) = exact(op, len, vv) else {
            continue;
        };
        let z = peer(&mut rng, &mut seam);
        let cop = rng.pick(&OPS);
        let exec = rng.coin();
        let goal = cmp(
            cop,
            arith(op, len_expr, v.expr.clone(), u64t.clone()),
            z.expr.clone(),
        );
        let want = expected(holds(cop, value, z.value));
        let got = seam.run(goal, exec, false, false);
        tally.record("seq_len", want, &got, || {
            format!(
                "(len={len} {op:?} {vv}:{vt:?}/{:?}) = {value} {cop:?} {}:{:?}/{:?}",
                v.form, z.value, z.ty, z.form
            )
        });
    }
    tally.finish("seq_len");
}

// ---------------------------------------------------------------------------
// Source frontend (`verify_function_from_file`, Verus-style spec clauses).
// ---------------------------------------------------------------------------

/// A Rust literal of `v` for a `requires x == v` pin (typed by `x`).
fn rust_lit(v: i128) -> String {
    format!("{v}")
}

struct SourceCase {
    name: String,
    params: Vec<(String, T)>,
    pins: Vec<(String, i128)>,
    goal: String,
    truth: bool,
    detail: String,
}

impl SourceCase {
    fn render(&self, out: &mut String) {
        for (n, v) in &self.pins {
            let _ = writeln!(out, "#[trust_vc::requires({n} == {})]", rust_lit(*v));
        }
        let _ = writeln!(out, "#[trust_vc::ensures({})]", self.goal);
        let params: Vec<String> = self
            .params
            .iter()
            .map(|(n, t)| {
                if n == "c" {
                    "c: bool".to_string()
                } else {
                    format!("{n}: {}", t.rust())
                }
            })
            .collect();
        let _ = writeln!(out, "fn {}({}) {{}}\n", self.name, params.join(", "));
    }
}

/// Values the source spelling can pin (`i128::MIN`'s magnitude has no
/// unsuffixed `i128` literal).
fn source_value(rng: &mut Rng, t: T) -> i128 {
    let v = rng.value(t);
    if v == i128::MIN {
        i128::MIN + 1
    } else {
        v
    }
}

fn source_case(rng: &mut Rng, index: usize) -> Option<SourceCase> {
    let tx = rng.ty();
    let ty = if rng.coin() { tx } else { rng.ty() };
    let tz = rng.ty();
    let (xv, yv, zv) = (
        source_value(rng, tx),
        source_value(rng, ty),
        source_value(rng, tz),
    );
    let cop = rng.pick(&OPS);
    let name = format!("case_{index}");
    let mut params = vec![
        ("x".to_string(), tx),
        ("y".to_string(), ty),
        ("z".to_string(), tz),
    ];
    let mut pins = vec![
        ("x".to_string(), xv),
        ("y".to_string(), yv),
        ("z".to_string(), zv),
    ];
    // The source frontend checks the arithmetic of an exec function's
    // `ensures` for overflow: a same-type operation that leaves its type is
    // refuted whatever the comparison says (`overflow`).
    let (lhs, value, what, overflow) = match rng.below(6) {
        0..=2 => {
            let op = rng.pick(&[ArithOp::Add, ArithOp::Sub, ArithOp::Mul]);
            let sym = match op {
                ArithOp::Add => "+",
                ArithOp::Sub => "-",
                _ => "*",
            };
            let (value, overflow) = if tx == ty {
                in_type(tx, op, xv, yv)?
            } else {
                (exact(op, xv, yv)?, false)
            };
            (format!("(x {sym} y)"), value, format!("{op:?}"), overflow)
        }
        3 => {
            let c = rng.coin();
            params.push(("c".to_string(), T { w: 8, s: false }));
            let cond = if c { "c" } else { "!c" };
            pins.push(("c".to_string(), 1));
            (
                format!("(if {cond} {{ x }} else {{ y }})"),
                if c { xv } else { yv },
                "ite".into(),
                false,
            )
        }
        4 => {
            let (sym, value) = match rng.below(3) {
                0 => ("&", xv & yv),
                1 => ("|", xv | yv),
                _ => ("^", xv ^ yv),
            };
            (format!("(x {sym} y)"), value, "bitwise".into(), false)
        }
        _ => {
            if !tx.s {
                return None;
            }
            let overflow = xv == tx.min();
            let value = xv.checked_neg().and_then(|n| tx.wrap(n)).unwrap_or(xv);
            ("(-x)".to_string(), value, "neg".into(), overflow)
        }
    };
    let goal = format!("{lhs} {} z", rust_cmp(cop));
    let truth = !overflow && holds(cop, value, zv);
    let detail =
        format!("{what}: x={xv}:{tx:?} y={yv}:{ty:?} z={zv}:{tz:?} lhs={lhs}={value} {cop:?}");
    Some(SourceCase {
        name,
        params,
        pins: pins
            .into_iter()
            .map(|(n, v)| if n == "c" { (n, 1) } else { (n, v) })
            .collect(),
        goal,
        truth,
        detail,
    })
}

#[test]
fn source_frontend_derives_the_same_types() {
    let mut rng = Rng(seed() ^ 0x10);
    let mut cases_v = Vec::new();
    let mut index = 0;
    while cases_v.len() < cases() * 2 {
        index += 1;
        if let Some(c) = source_case(&mut rng, index) {
            cases_v.push(c);
        }
    }
    let mut src = String::new();
    for c in &cases_v {
        let mut rendered = String::new();
        c.render(&mut rendered);
        // `c` is a bool: its pin is the bare condition.
        let rendered =
            rendered.replace("#[trust_vc::requires(c == 1)]", "#[trust_vc::requires(c)]");
        src.push_str(&rendered);
    }
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/integer_typing_proptest_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(format!("cases_{:x}.rs", seed()));
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(src.as_bytes()))
        .expect("write source");
    let mut tally = Tally::default();
    for c in &cases_v {
        let got = verify_function_from_file(path.to_str().expect("utf-8 path"), &c.name)
            .unwrap_or_else(|e| VerifyResult::Error {
                message: e.to_string(),
            });
        tally.record("source", expected(c.truth), &got, || {
            format!("{}: {} ({})", c.name, c.goal, c.detail)
        });
    }
    tally.finish("source");
}
