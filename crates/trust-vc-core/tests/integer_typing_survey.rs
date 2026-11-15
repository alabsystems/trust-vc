//! SURVEY: seeded random NESTED integer expressions (depth
//! up to 3) through both frontends, every width 8..128 and both signs, exec
//! and non-exec, against an i128 oracle of design-trust-proof-backend.md §5b:
//!
//! * a binary node over ONE fixed type T computes in T (two's complement;
//!   an exec `assert` / an exec fn's `ensures` refutes on overflow; `/ %`
//!   truncate); over two DIFFERENT types, an `int`, or a node DECLARED `int`
//!   it is exact (`/ %` Euclidean);
//! * an untyped literal (`Int{32}` placeholder, incl. `i32` literals in the
//!   typed seam; the source renders them unsuffixed) takes its sibling's type
//!   when its value fits, else stays `i32` — except that a node DECLARED `i32`
//!   reads it as the `i32` it is declared to be next to a non-`i32` sibling;
//! * a `#[trust_vc::spec] fn -> int` body's plain arithmetic is exact;
//! * `-`, `!` stay in the operand's type; casts wrap into the target; a shift
//!   keeps the left type; `wrapping_*` wraps in its (same-type) operands' type;
//!   a conditional's type is derived from both branches;
//! * comparisons are over the integers.
//!
//! The typed-seam half builds `TrustVcExpr` directly (declared node types are
//! random: any operand's type, a third type, or `int`), also under
//! `by(bit_vector)`; the source half renders the same trees as Rust
//! (`#[trust_vc::requires/ensures]`, exec fns and `#[trust_vc::proof]` fns),
//! inline, inside a `#[trust_vc::spec] fn -> bool`, and as a spec fn body
//! returning the tree's derived type (spec-fn bodies are never
//! overflow-checked). Operands are pinned (`requires x == v`) or
//! literals, so every goal is decided: `Verified` for a false goal (FALSE
//! VERIFIED) or a refutation of a true one (FALSE COUNTEREXAMPLE) fails.
//! `Unknown` is tolerated (fail-closed) and counted.
//!
//! `SURVEY_SEED`, `SURVEY_CASES` steer the generator.

use std::fmt::Write as _;
use std::io::Write as _;

use trust_vc_core::ir::{
    ArithOp, CompareOp, SpecialArithOp, TrustVcExpr, TrustVcType, WrappingMode,
};
use trust_vc_core::vc::{SolverMode, TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct T {
    w: u32,
    s: bool,
}
const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];
const I32: T = T { w: 32, s: true };

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ty {
    F(T),
    Int,
}
impl Ty {
    fn ir(self) -> TrustVcType {
        match self {
            Ty::F(t) => t.ir(),
            Ty::Int => TrustVcType::MathInt,
        }
    }
    fn rust(self) -> String {
        match self {
            Ty::F(t) => t.rust(),
            Ty::Int => "int".to_string(),
        }
    }
    fn holds(self, v: i128) -> bool {
        match self {
            Ty::F(t) => t.contains(v),
            Ty::Int => true,
        }
    }
}

fn all_types() -> Vec<T> {
    WIDTHS
        .iter()
        .flat_map(|&w| [T { w, s: false }, T { w, s: true }])
        .collect()
}

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
    fn t(&mut self) -> T {
        self.pick(&all_types())
    }
    fn value(&mut self, t: T) -> i128 {
        let half = if t.w == 128 {
            i128::MAX
        } else {
            (1i128 << (t.w - 1)) - 1
        };
        let mut edges = vec![
            t.min(),
            t.max(),
            0,
            1,
            2,
            3,
            half,
            half.saturating_add(1),
            100,
            200,
        ];
        if t.s {
            edges.extend([-1, -2, t.min() + 1, -128, -100, -256, -7]);
        } else {
            edges.extend([255, 128, 256, 7]);
        }
        let v = match self.below(4) {
            0 | 1 => self.pick(&edges),
            #[allow(clippy::cast_possible_wrap)]
            2 => self.below(41) as i128 - 20,
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
    fn int_value(&mut self) -> i128 {
        let t = self.t();
        let v = self.value(t);
        if self.coin() {
            v
        } else {
            v.saturating_mul(3).saturating_sub(1)
        }
    }
}

// ---------------------------------------------------------------------------
// The generated tree.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum N {
    /// A variable pinned by `requires name == value`.
    Var {
        name: String,
        ty: Ty,
        value: i128,
    },
    /// A literal of its own type (an `i32` one is untyped).
    Lit {
        value: i128,
        ty: Ty,
    },
    /// `-(mag)` of the type (mag > 0; an `i32` one is untyped).
    NegLit {
        mag: i128,
        ty: Ty,
    },
    /// An unsuffixed literal (`Int{32}`), value within i32.
    Untyped {
        value: i128,
    },
    Arith {
        op: ArithOp,
        l: Box<N>,
        r: Box<N>,
        decl: Ty,
    },
    Bit {
        op: SpecialArithOp,
        l: Box<N>,
        r: Box<N>,
        decl: Ty,
    },
    Neg(Box<N>),
    Not(Box<N>),
    Ite {
        cname: String,
        c: bool,
        l: Box<N>,
        r: Box<N>,
        decl: Ty,
    },
    Cast {
        e: Box<N>,
        to: Ty,
    },
    Shift {
        shl: bool,
        l: Box<N>,
        k: i128,
        kt: T,
    },
    Wrap {
        op: ArithOp,
        l: Box<N>,
        r: Box<N>,
        t: T,
    },
}

fn is_untyped(n: &N) -> bool {
    match n {
        N::Untyped { .. } => true,
        N::Lit { ty, .. } | N::NegLit { ty, .. } => *ty == Ty::F(I32),
        _ => false,
    }
}
fn untyped_value(n: &N) -> i128 {
    match n {
        N::Untyped { value } | N::Lit { value, .. } => *value,
        N::NegLit { mag, .. } => -*mag,
        _ => unreachable!(),
    }
}

/// The two operand types after the untyped-literal rule. A node DECLARED
/// `i32` reads its `i32`-typed literal as the `i32` it is declared to be when
/// the other operand has another fixed-width type (§5b rule 7: the
/// placeholder reading contradicts the declaration).
fn settle(l: &N, r: &N, decl: Ty) -> (Ty, Ty) {
    let take = |u: &N, peer: Ty| {
        let declared_i32 = decl == Ty::F(I32) && matches!(peer, Ty::F(t) if t != I32);
        if !declared_i32 && peer.holds(untyped_value(u)) {
            peer
        } else {
            Ty::F(I32)
        }
    };
    match (is_untyped(l), is_untyped(r)) {
        (true, false) => {
            let rt = ty(r);
            (take(l, rt), rt)
        }
        (false, true) => {
            let lt = ty(l);
            (lt, take(r, lt))
        }
        (true, true) => unreachable!("never generated"),
        (false, false) => (ty(l), ty(r)),
    }
}

fn derive(l: &N, r: &N, decl: Ty) -> Ty {
    if decl == Ty::Int {
        return Ty::Int;
    }
    let (lt, rt) = settle(l, r, decl);
    if lt == Ty::Int || rt == Ty::Int || lt != rt {
        Ty::Int
    } else {
        lt
    }
}

fn ty(n: &N) -> Ty {
    match n {
        N::Var { ty, .. } | N::Lit { ty, .. } | N::NegLit { ty, .. } => *ty,
        N::Untyped { .. } => Ty::F(I32),
        N::Arith { l, r, decl, .. } | N::Bit { l, r, decl, .. } | N::Ite { l, r, decl, .. } => {
            derive(l, r, *decl)
        }
        N::Neg(e) | N::Not(e) => ty(e),
        N::Cast { to, .. } => *to,
        N::Shift { l, .. } => ty(l),
        N::Wrap { t, .. } => Ty::F(*t),
    }
}

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

fn in_type(t: T, op: ArithOp, l: i128, r: i128) -> Option<(i128, bool)> {
    match op {
        ArithOp::Div | ArithOp::Rem => {
            if r == 0 || (t.s && l == t.min() && r == -1) {
                return None;
            }
            Some((if op == ArithOp::Div { l / r } else { l % r }, false))
        }
        _ => {
            let e = exact(op, l, r)?;
            Some((t.wrap(e)?, !t.contains(e)))
        }
    }
}

/// `(value, overflowed)`; `None` when undefined or beyond the i128 oracle.
fn eval(n: &N) -> Option<(i128, bool)> {
    match n {
        N::Var { value, .. } | N::Lit { value, .. } | N::Untyped { value } => Some((*value, false)),
        N::NegLit { mag, .. } => Some((-*mag, false)),
        N::Arith { op, l, r, .. } => {
            let (lv, lo) = eval(l)?;
            let (rv, ro) = eval(r)?;
            match ty(n) {
                Ty::Int => Some((exact(*op, lv, rv)?, lo || ro)),
                Ty::F(t) => {
                    let (v, o) = in_type(t, *op, lv, rv)?;
                    Some((v, lo || ro || o))
                }
            }
        }
        N::Bit { op, l, r, .. } => {
            let (lv, lo) = eval(l)?;
            let (rv, ro) = eval(r)?;
            let v = match op {
                SpecialArithOp::BitAnd => lv & rv,
                SpecialArithOp::BitOr => lv | rv,
                _ => lv ^ rv,
            };
            Some((v, lo || ro))
        }
        N::Neg(e) => {
            let (v, o) = eval(e)?;
            match ty(e) {
                Ty::Int => Some((v.checked_neg()?, o)),
                Ty::F(t) => {
                    let exact = v.checked_neg()?;
                    Some((t.wrap(exact)?, o || !t.contains(exact)))
                }
            }
        }
        N::Not(e) => {
            let (v, o) = eval(e)?;
            let Ty::F(t) = ty(e) else { return None };
            Some((t.wrap(!v)?, o))
        }
        N::Ite { c, l, r, .. } => {
            let lv = eval(l)?;
            let rv = eval(r)?;
            Some(if *c { lv } else { rv })
        }
        N::Cast { e, to } => {
            let (v, o) = eval(e)?;
            match to {
                Ty::Int => Some((v, o)),
                Ty::F(t) => Some((t.wrap(v)?, o)),
            }
        }
        N::Shift { shl, l, k, .. } => {
            let (v, o) = eval(l)?;
            let Ty::F(t) = ty(l) else { return None };
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let kk = *k as u32;
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
            let r = if *shl {
                t.wrap(((v as u128) << kk) as i128)?
            } else {
                v >> kk
            };
            Some((r, o))
        }
        N::Wrap { op, l, r, t } => {
            let (lv, lo) = eval(l)?;
            let (rv, ro) = eval(r)?;
            Some((t.wrap(exact(*op, lv, rv)?)?, lo || ro))
        }
    }
}

/// `eval` of the body of a `#[trust_vc::spec] fn -> int`: its plain
/// arithmetic — `+ - * / %`, unary `-`, `if` — is exact throughout (§5b rule
/// 8, Verus's `int` result context); every other node (bitwise, `!`, casts,
/// shifts, `wrapping_*`) keeps its own semantics.
fn eval_int_context(n: &N) -> Option<i128> {
    match n {
        N::Arith { op, l, r, .. } => exact(*op, eval_int_context(l)?, eval_int_context(r)?),
        N::Neg(e) => eval_int_context(e)?.checked_neg(),
        N::Ite { c, l, r, .. } => {
            let lv = eval_int_context(l)?;
            let rv = eval_int_context(r)?;
            Some(if *c { lv } else { rv })
        }
        other => eval(other).map(|(v, _)| v),
    }
}

// ---------------------------------------------------------------------------
// Generation.
// ---------------------------------------------------------------------------

struct Gen<'a> {
    rng: &'a mut Rng,
    pins: Vec<(String, Ty, i128)>,
    bools: Vec<(String, bool)>,
    allow_int: bool,
}

impl Gen<'_> {
    fn some_ty(&mut self) -> Ty {
        if self.allow_int && self.rng.below(6) == 0 {
            Ty::Int
        } else {
            Ty::F(self.rng.t())
        }
    }
    fn value_of(&mut self, t: Ty) -> i128 {
        match t {
            Ty::F(t) => self.rng.value(t),
            Ty::Int => self.rng.int_value(),
        }
    }
    fn var(&mut self, t: Ty) -> N {
        let mut value = self.value_of(t);
        // `i128::MIN`'s magnitude has no literal spelling in a source pin.
        if value == i128::MIN {
            value += 1;
        }
        let name = format!("x{}", self.pins.len());
        self.pins.push((name.clone(), t, value));
        N::Var { name, ty: t, value }
    }
    /// A leaf; `untyped_ok` allows the untyped forms.
    fn leaf(&mut self, untyped_ok: bool) -> N {
        let t = self.some_ty();
        match self.rng.below(if untyped_ok { 6 } else { 4 }) {
            0 | 1 => self.var(t),
            2 => {
                let value = self.value_of(t);
                if t == Ty::F(I32) && !untyped_ok {
                    return self.var(t);
                }
                // `i128::MIN`'s magnitude has no literal spelling.
                if value == i128::MIN {
                    return self.var(t);
                }
                N::Lit { value, ty: t }
            }
            3 => {
                let signed = match t {
                    Ty::F(tt) => tt.s,
                    Ty::Int => true,
                };
                let value = self.value_of(t);
                if !signed || value >= 0 || value == i128::MIN || (t == Ty::F(I32) && !untyped_ok) {
                    return self.var(t);
                }
                N::NegLit { mag: -value, ty: t }
            }
            _ => {
                let v = self.rng.value(I32);
                if v < 0 && v != i128::from(i32::MIN) && self.rng.coin() {
                    N::NegLit {
                        mag: -v,
                        ty: Ty::F(I32),
                    }
                } else {
                    N::Untyped { value: v }
                }
            }
        }
    }
    /// The type the syn lowering declares a node with: its typed operand's
    /// (`ir_lowering::derived_node_type`), then derived.
    fn lowered_decl(l: &N, r: &N) -> Ty {
        derive(l, r, if is_untyped(l) { ty(r) } else { ty(l) })
    }
    fn decl(&mut self, l: &N, r: &N) -> Ty {
        match self.rng.below(7) {
            0 | 1 => ty(l),
            2 | 3 => ty(r),
            4 if self.allow_int => Ty::Int,
            _ => Ty::F(self.rng.t()),
        }
    }
    /// Two operands, never both untyped.
    fn pair(&mut self, depth: u32, typed_seam: bool) -> (N, N) {
        let l = self.node(depth - 1, true, typed_seam);
        let r = self.node(depth - 1, !is_untyped(&l), typed_seam);
        if self.rng.coin() {
            (l, r)
        } else if !is_untyped(&r) || !is_untyped(&l) {
            (r, l)
        } else {
            (l, r)
        }
    }
    fn node(&mut self, depth: u32, untyped_ok: bool, typed_seam: bool) -> N {
        if depth == 0 || self.rng.below(4) == 0 {
            return self.leaf(untyped_ok);
        }
        match self.rng.below(10) {
            0..=2 => {
                let op = self.rng.pick(&[
                    ArithOp::Add,
                    ArithOp::Sub,
                    ArithOp::Mul,
                    ArithOp::Div,
                    ArithOp::Rem,
                ]);
                let (l, r) = self.pair(depth, typed_seam);
                let decl = if typed_seam {
                    self.decl(&l, &r)
                } else {
                    Self::lowered_decl(&l, &r)
                };
                N::Arith {
                    op,
                    l: Box::new(l),
                    r: Box::new(r),
                    decl,
                }
            }
            3 => {
                let op = self.rng.pick(&[
                    SpecialArithOp::BitAnd,
                    SpecialArithOp::BitOr,
                    SpecialArithOp::BitXor,
                ]);
                let (l, r) = self.pair(depth, typed_seam);
                if ty(&l) == Ty::Int || ty(&r) == Ty::Int {
                    return self.leaf(untyped_ok);
                }
                let decl = if typed_seam {
                    self.decl(&l, &r)
                } else {
                    Self::lowered_decl(&l, &r)
                };
                N::Bit {
                    op,
                    l: Box::new(l),
                    r: Box::new(r),
                    decl,
                }
            }
            4 => {
                let e = self.node(depth - 1, false, typed_seam);
                let signed = match ty(&e) {
                    Ty::F(t) => t.s,
                    Ty::Int => true,
                };
                if !signed || matches!(e, N::Lit { .. } | N::NegLit { .. } | N::Untyped { .. }) {
                    return e;
                }
                N::Neg(Box::new(e))
            }
            5 => {
                let e = self.node(depth - 1, false, typed_seam);
                if ty(&e) == Ty::Int
                    || matches!(e, N::Lit { .. } | N::NegLit { .. } | N::Untyped { .. })
                {
                    return e;
                }
                N::Not(Box::new(e))
            }
            6 => {
                let (l, r) = self.pair(depth, typed_seam);
                let c = self.rng.coin();
                let cname = format!("c{}", self.bools.len());
                self.bools.push((cname.clone(), c));
                let decl = if typed_seam {
                    self.decl(&l, &r)
                } else {
                    Self::lowered_decl(&l, &r)
                };
                N::Ite {
                    cname,
                    c,
                    l: Box::new(l),
                    r: Box::new(r),
                    decl,
                }
            }
            7 => {
                let e = self.node(depth - 1, false, typed_seam);
                let to = self.some_ty();
                N::Cast { e: Box::new(e), to }
            }
            8 => {
                let l = self.node(depth - 1, false, typed_seam);
                let Ty::F(t) = ty(&l) else { return l };
                let kt = T {
                    w: self.rng.pick(&WIDTHS),
                    s: false,
                };
                let k =
                    i128::from(u32::try_from(self.rng.below(u64::from(t.w.min(64)))).unwrap_or(0));
                if !kt.contains(k) {
                    return l;
                }
                N::Shift {
                    shl: self.rng.coin(),
                    l: Box::new(l),
                    k,
                    kt,
                }
            }
            _ => {
                let t = self.rng.t();
                let op = self.rng.pick(&[ArithOp::Add, ArithOp::Sub, ArithOp::Mul]);
                let l = self.var(Ty::F(t));
                let r = if t == I32 || self.rng.coin() {
                    self.var(Ty::F(t))
                } else {
                    let value = self.rng.value(t);
                    if value == i128::MIN {
                        self.var(Ty::F(t))
                    } else {
                        N::Lit {
                            value,
                            ty: Ty::F(t),
                        }
                    }
                };
                N::Wrap {
                    op,
                    l: Box::new(l),
                    r: Box::new(r),
                    t,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Typed seam rendering.
// ---------------------------------------------------------------------------

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}
const PLACEHOLDER: TrustVcType = TrustVcType::Int { width: 32 };

fn to_ir(n: &N) -> TrustVcExpr {
    match n {
        N::Var { name, ty, .. } => TrustVcExpr::Var {
            name: name.clone(),
            ty: ty.ir(),
        },
        N::Lit { value, ty } => lit(*value, ty.ir()),
        N::NegLit { mag, ty } => TrustVcExpr::Neg(Box::new(lit(*mag, ty.ir()))),
        N::Untyped { value } => lit(*value, PLACEHOLDER),
        N::Arith { op, l, r, decl } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(to_ir(l)),
            right: Box::new(to_ir(r)),
            ty: decl.ir(),
        },
        N::Bit { op, l, r, decl } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(to_ir(l)),
            right: Box::new(to_ir(r)),
            ty: decl.ir(),
        },
        N::Neg(e) => TrustVcExpr::Neg(Box::new(to_ir(e))),
        N::Not(e) => TrustVcExpr::Not(Box::new(to_ir(e))),
        N::Ite {
            cname, l, r, decl, ..
        } => TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::Var {
                name: cname.clone(),
                ty: TrustVcType::Bool,
            }),
            then_branch: Box::new(to_ir(l)),
            else_branch: Box::new(to_ir(r)),
            ty: decl.ir(),
        },
        N::Cast { e, to } => TrustVcExpr::Cast {
            expr: Box::new(to_ir(e)),
            from_ty: ty(e).ir(),
            to_ty: to.ir(),
        },
        N::Shift { shl, l, k, kt } => TrustVcExpr::SpecialArith {
            op: if *shl {
                SpecialArithOp::Shl
            } else {
                SpecialArithOp::Shr
            },
            left: Box::new(to_ir(l)),
            right: Box::new(lit(*k, kt.ir())),
            ty: ty(l).ir(),
        },
        N::Wrap { op, l, r, t } => TrustVcExpr::WrappingArith {
            mode: WrappingMode::Wrapping,
            op: *op,
            left: Box::new(to_ir(l)),
            right: Box::new(to_ir(r)),
            ty: t.ir(),
        },
    }
}

// ---------------------------------------------------------------------------
// Source rendering.
// ---------------------------------------------------------------------------

fn rust_lit(value: i128, ty: Option<Ty>) -> String {
    let suffix = match ty {
        // The oracle's `i32` literal is untyped (`is_untyped`): unsuffixed. A
        // suffixed `200i32` is an `i32` (§5b rule 7).
        Some(Ty::F(I32)) => String::new(),
        Some(Ty::F(t)) => t.rust(),
        Some(Ty::Int) => "int".to_string(),
        None => String::new(),
    };
    format!("{value}{suffix}")
}

fn to_rust(n: &N) -> String {
    let sym = |op: ArithOp| match op {
        ArithOp::Add => "+",
        ArithOp::Sub => "-",
        ArithOp::Mul => "*",
        ArithOp::Div => "/",
        _ => "%",
    };
    match n {
        N::Var { name, .. } => name.clone(),
        N::Lit { value, ty } => {
            if *value < 0 {
                format!("(-{})", rust_lit(-*value, Some(*ty)))
            } else {
                rust_lit(*value, Some(*ty))
            }
        }
        N::NegLit { mag, ty } => format!("(-{})", rust_lit(*mag, Some(*ty))),
        N::Untyped { value } => {
            if *value < 0 {
                format!("(-{})", -*value)
            } else {
                format!("{value}")
            }
        }
        N::Arith { op, l, r, .. } => format!("({} {} {})", to_rust(l), sym(*op), to_rust(r)),
        N::Bit { op, l, r, .. } => {
            let s = match op {
                SpecialArithOp::BitAnd => "&",
                SpecialArithOp::BitOr => "|",
                _ => "^",
            };
            format!("({} {s} {})", to_rust(l), to_rust(r))
        }
        N::Neg(e) => format!("(-{})", to_rust(e)),
        N::Not(e) => format!("(!{})", to_rust(e)),
        N::Ite { cname, l, r, .. } => {
            format!(
                "(if {cname} {{ {} }} else {{ {} }})",
                to_rust(l),
                to_rust(r)
            )
        }
        N::Cast { e, to } => format!("({} as {})", to_rust(e), to.rust()),
        N::Shift { shl, l, k, kt } => format!(
            "({} {} {k}{})",
            to_rust(l),
            if *shl { "<<" } else { ">>" },
            kt.rust()
        ),
        N::Wrap { op, l, r, .. } => {
            let m = match op {
                ArithOp::Add => "wrapping_add",
                ArithOp::Sub => "wrapping_sub",
                _ => "wrapping_mul",
            };
            format!("{}.{m}({})", to_rust(l), to_rust(r))
        }
    }
}

// ---------------------------------------------------------------------------
// Tally.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Verified,
    Refuted,
    /// `NotProved`: not verified, but no counterexample is claimed.
    NotProved,
    Unknown,
}
fn verdict_of(r: &VerifyResult) -> Verdict {
    match r {
        VerifyResult::Verified => Verdict::Verified,
        VerifyResult::Counterexample { .. } => Verdict::Refuted,
        VerifyResult::NotProved { .. } => Verdict::NotProved,
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
        _ => l >= r,
    }
}
fn rust_cmp(op: CompareOp) -> &'static str {
    match op {
        CompareOp::Eq => "==",
        CompareOp::Ne => "!=",
        CompareOp::Lt => "<",
        CompareOp::Le => "<=",
        CompareOp::Gt => ">",
        _ => ">=",
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

#[derive(Default)]
struct Tally {
    total: usize,
    decided: usize,
    unknown: usize,
    bad: Vec<String>,
}
impl Tally {
    fn record(&mut self, shape: &str, want: Verdict, got: &VerifyResult, detail: &str) {
        self.total += 1;
        match (want, verdict_of(got)) {
            (Verdict::Refuted, Verdict::NotProved) => self.decided += 1,
            (_, Verdict::Unknown | Verdict::NotProved) => {
                self.unknown += 1;
                if std::env::var_os("SURVEY_VERBOSE").is_some() {
                    let raw: String = format!("{got:?}").chars().take(200).collect();
                    println!("UNKNOWN|{shape}|{detail}|{raw}");
                }
            }
            (w, g) if w == g => self.decided += 1,
            (Verdict::Refuted, Verdict::Verified) => {
                let line = format!("FALSE VERIFIED|{shape}|{detail}");
                println!("{line}");
                self.bad.push(line);
            }
            (_, g) => {
                let raw: String = format!("{got:?}").chars().take(200).collect();
                let line = format!("FALSE COUNTEREXAMPLE|{shape}|{detail}|{g:?}|{raw}");
                println!("{line}");
                self.bad.push(line);
            }
        }
    }
    fn finish(self, name: &str) {
        println!(
            "SUMMARY {name}: total={} decided={} unknown={} wrong={}",
            self.total,
            self.decided,
            self.unknown,
            self.bad.len()
        );
        assert!(
            self.bad.is_empty(),
            "{name}: {} wrong verdicts:\n{}",
            self.bad.len(),
            self.bad.join("\n")
        );
    }
}

fn seed() -> u64 {
    std::env::var("SURVEY_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x5eed_0924_0005)
}
fn cases() -> usize {
    std::env::var("SURVEY_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(120)
}

/// A comparison peer: pinned variable or literal of any type.
fn peer(g: &mut Gen<'_>) -> N {
    g.leaf(false)
}

fn shape_name(n: &N) -> &'static str {
    match n {
        N::Arith { .. } => "arith",
        N::Bit { .. } => "bitwise",
        N::Neg(_) => "neg",
        N::Not(_) => "not",
        N::Ite { .. } => "ite",
        N::Cast { .. } => "cast",
        N::Shift { .. } => "shift",
        N::Wrap { .. } => "wrapping",
        _ => "leaf",
    }
}

#[test]
fn survey_typed_seam_nested() {
    typed_seam_nested(false, "typed_seam_nested", 3);
}

/// The same trees under `by(bit_vector)` (fixed-width types only).
#[test]
fn survey_typed_seam_bit_vector() {
    typed_seam_nested(true, "typed_seam_bit_vector", 1);
}

fn typed_seam_nested(bv: bool, name: &str, factor: usize) {
    let mut rng = Rng(seed() ^ if bv { 0xC3 } else { 0xA1 });
    let mut tally = Tally::default();
    for _ in 0..cases() * factor {
        let mut g = Gen {
            rng: &mut rng,
            pins: Vec::new(),
            bools: Vec::new(),
            allow_int: !bv,
        };
        let tree = g.node(3, false, true);
        let z = peer(&mut g);
        let cop = g.rng.pick(&OPS);
        let (exec, assert) = if bv {
            (false, true)
        } else {
            (g.rng.coin(), g.rng.coin())
        };
        let Some((value, overflow)) = eval(&tree) else {
            continue;
        };
        let Some((zv, _)) = eval(&z) else { continue };
        let want = if exec && assert && overflow {
            Verdict::Refuted
        } else if holds(cop, value, zv) {
            Verdict::Verified
        } else {
            Verdict::Refuted
        };
        let mut variables: Vec<VariableDecl> = g
            .pins
            .iter()
            .map(|(n, t, _)| VariableDecl::new(n.clone(), t.ir()))
            .collect();
        variables.extend(
            g.bools
                .iter()
                .map(|(n, _)| VariableDecl::new(n.clone(), TrustVcType::Bool)),
        );
        variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
        let mut obligations: Vec<TypedProofObligation> = Vec::new();
        for (i, (n, t, v)) in g.pins.iter().enumerate() {
            obligations.push(TypedProofObligation::requires(
                format!("s_requires_{i}"),
                cmp(
                    CompareOp::Eq,
                    TrustVcExpr::Var {
                        name: n.clone(),
                        ty: t.ir(),
                    },
                    lit(*v, t.ir()),
                ),
            ));
        }
        for (i, (n, c)) in g.bools.iter().enumerate() {
            let v = TrustVcExpr::Var {
                name: n.clone(),
                ty: TrustVcType::Bool,
            };
            obligations.push(TypedProofObligation::requires(
                format!("s_requires_b{i}"),
                if *c { v } else { TrustVcExpr::Not(Box::new(v)) },
            ));
        }
        let goal = cmp(cop, to_ir(&tree), to_ir(&z));
        let mut goal = if assert {
            TypedProofObligation::assert("s_goal", goal)
        } else {
            TypedProofObligation::ensures("s_ensures_0", goal)
        };
        if bv {
            goal = goal.with_solver_mode(SolverMode::BitVector);
        }
        obligations.push(goal);
        let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
        if exec {
            ctx.enable_overflow_checks();
        }
        let got = ctx.verify();
        let detail = format!(
            "{} {} {} [value {value} ty {:?} overflow {overflow}; peer {zv}:{:?}] exec={exec} assert={assert} pins={:?} bools={:?} tree={tree:?}",
            to_rust(&tree),
            rust_cmp(cop),
            to_rust(&z),
            ty(&tree),
            ty(&z),
            g.pins,
            g.bools
        );
        let shape = shape_name(&tree);
        tally.record(shape, want, &got, &detail);
    }
    tally.finish(name);
}

struct SrcCase {
    name: String,
    text: String,
    want: Verdict,
    detail: String,
}

#[test]
fn survey_source_nested() {
    source_nested(SrcMode::Plain, "source_nested");
}

/// The comparison inside a `#[trust_vc::spec] fn -> bool` body.
#[test]
fn survey_source_specfn_bool() {
    source_nested(SrcMode::SpecBool, "source_specfn_bool");
}

/// The tree as a `#[trust_vc::spec]` fn body returning its derived type.
#[test]
fn survey_source_specfn_value() {
    source_nested(SrcMode::SpecValue, "source_specfn_value");
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SrcMode {
    Plain,
    SpecBool,
    SpecValue,
}

fn source_nested(mode: SrcMode, tag: &str) {
    let mut rng = Rng(seed() ^ 0xB2 ^ (mode as u64) << 8);
    let mut cs = Vec::new();
    let mut index = 0usize;
    while cs.len() < cases() {
        index += 1;
        let proof = rng.coin();
        let mut g = Gen {
            rng: &mut rng,
            pins: Vec::new(),
            bools: Vec::new(),
            allow_int: proof,
        };
        let tree = g.node(3, false, false);
        let z = peer(&mut g);
        let cop = g.rng.pick(&OPS);
        let Some((value, overflow)) = eval(&tree) else {
            continue;
        };
        // A spec fn returning `int` computes its body's plain arithmetic
        // exactly (§5b rule 8).
        let value = if mode == SrcMode::SpecValue && ty(&tree) == Ty::Int {
            let Some(value) = eval_int_context(&tree) else {
                continue;
            };
            value
        } else {
            value
        };
        let Some((zv, _)) = eval(&z) else { continue };
        // An exec fn's `ensures` is overflow-checked; a proof fn's is not,
        // and neither is a spec fn body.
        let checked = !proof && mode == SrcMode::Plain;
        let want = if (checked && overflow) || !holds(cop, value, zv) {
            Verdict::Refuted
        } else {
            Verdict::Verified
        };
        let name = format!("case_{index}");
        let mut text = String::new();
        if proof {
            text.push_str("#[trust_vc::proof]\n");
        }
        for (n, _, v) in &g.pins {
            let _ = writeln!(
                text,
                "#[trust_vc::requires({n} == {})]",
                if *v < 0 {
                    format!("-{}", -*v)
                } else {
                    format!("{v}")
                }
            );
        }
        for (n, c) in &g.bools {
            let _ = writeln!(
                text,
                "#[trust_vc::requires({}{n})]",
                if *c { "" } else { "!" }
            );
        }
        let mut params: Vec<String> = g
            .pins
            .iter()
            .map(|(n, t, _)| format!("{n}: {}", t.rust()))
            .collect();
        params.extend(g.bools.iter().map(|(n, _)| format!("{n}: bool")));
        let args: Vec<String> = g
            .pins
            .iter()
            .map(|(n, _, _)| n.clone())
            .chain(g.bools.iter().map(|(n, _)| n.clone()))
            .collect();
        let goal = match mode {
            SrcMode::Plain => format!("{} {} {}", to_rust(&tree), rust_cmp(cop), to_rust(&z)),
            SrcMode::SpecBool => {
                let mut spec = String::new();
                let _ = writeln!(
                    spec,
                    "#[trust_vc::spec]\nfn p_{name}({}) -> bool {{\n    {} {} {}\n}}\n",
                    params.join(", "),
                    to_rust(&tree),
                    rust_cmp(cop),
                    to_rust(&z)
                );
                text.insert_str(0, &spec);
                format!("p_{name}({})", args.join(", "))
            }
            SrcMode::SpecValue => {
                let mut spec = String::new();
                let _ = writeln!(
                    spec,
                    "#[trust_vc::spec]\nfn g_{name}({}) -> {} {{\n    {}\n}}\n",
                    params.join(", "),
                    ty(&tree).rust(),
                    to_rust(&tree)
                );
                text.insert_str(0, &spec);
                format!(
                    "g_{name}({}) {} {}",
                    args.join(", "),
                    rust_cmp(cop),
                    to_rust(&z)
                )
            }
        };
        let _ = writeln!(text, "#[trust_vc::ensures({goal})]");
        let _ = writeln!(text, "fn {name}({}) {{}}\n", params.join(", "));
        let detail = format!(
            "{} [value {value} ty {:?} overflow {overflow}; peer {zv}:{:?}] proof={proof} pins={:?} bools={:?}",
            goal,
            ty(&tree),
            ty(&z),
            g.pins,
            g.bools
        );
        let _ = shape_name(&tree);
        cs.push(SrcCase {
            name,
            text,
            want,
            detail,
        });
    }
    let src: String = cs.iter().map(|c| c.text.as_str()).collect();
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/integer_typing_survey_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(format!("{tag}_{:x}.rs", seed()));
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(src.as_bytes()))
        .expect("write source");
    let mut tally = Tally::default();
    for c in &cs {
        let got =
            verify_function_from_file(path.to_str().expect("utf-8"), &c.name).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            });
        tally.record(tag, c.want, &got, &format!("{}: {}", c.name, c.detail));
    }
    tally.finish(tag);
}
