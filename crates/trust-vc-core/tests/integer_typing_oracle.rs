//! MECHANICAL integer-typing ORACLE (design-trust-proof-backend.md §5b).
//!
//! The integer-typing defect class kept reappearing in constructs the
//! property tests did not generate — r4 (9def8d43: a result typed by its left
//! operand, a literal re-valued by its peer, `===` over bits, a truncated
//! shift amount), r5 (f8f2e624: a value bound at a type that cannot hold it, a
//! substitution that retyped its variable, an `int` body that stopped being
//! exact), r6 (a `match` arm widened by the MATCH's sign, a call argument
//! bound at a type that cannot hold it). So this oracle is complete by
//! CONSTRUCTION, not by review:
//!
//! * **every integer-role expression variant.** `trust_vc_core::ir::
//!   integer_surface::EXPR_VARIANTS` is generated from one exhaustive `match`
//!   over `TrustVcExpr` inside trust-vc-core (the enum is `non_exhaustive`, so
//!   only that crate can write it): a new variant does not compile until it is
//!   classified, and `every_integer_role_variant_is_generated` fails until the
//!   generator here produces every variant whose role is not `None` (or names
//!   it in [`EXEMPT`] with the reason no value can be computed for it), and
//!   the seam run asserts each was DECIDED at least once;
//! * **every binding site** ([`Site`], checked the same way: `ALL_SITES` is
//!   derived from the enum, and [`frontends`] classifies each site by an
//!   exhaustive `match`): `let` at a declared type, EVERY WRITE into a typed
//!   slot ([`Bind`], each shape generated in turn — an assignment, a
//!   compound assignment, a deferred `let`, a write through `&mut` to a
//!   binding, a struct field or a `Vec` cell (read back through the alias),
//!   a tuple, struct or parameter field write, a write to a binding typed by its
//!   initializer or first write — a value, an element read — or by a
//!   pattern, in a glob-import file one time in four; an unascribed
//!   binding read into a typed slot through a borrow, a closure capture or a
//!   copy, whose type the slot gives it; an exec function's argument; and a
//!   write through a `&mut` the lane does not track, which must never be
//!   DECIDED wrongly and is never decided — `Bind::fail_closed`), a call
//!   argument at its parameter's type (an INLINE spec function's too), a spec function's
//!   result at its declared type, a `match` arm / conditional branch at the
//!   join's type, a `wrapping_*`/`saturating_*` operand, a cast operand, a
//!   sequence element, a `choose` binder, an arithmetic / bitwise / shift /
//!   comparison operand, a pinned variable's substituted value, a
//!   `take`/`skip` count (at the top level and inside a spec function's
//!   defining axiom, often out of `0..=len`, where the length is a `nat`
//!   Verus leaves unspecified), and — on the typed seam, where a declared
//!   type is a producer's claim — a literal declared at a type that cannot
//!   hold it, a cast declared from a type that is not its operand's, and an
//!   element read through a chain of receivers with a lie at a random depth
//!   (§5b rules 10 and 13: refused);
//! * both frontends — the typed seam (`VerificationContext::from_typed_parts`,
//!   random DECLARED node types) and the source frontend (Verus-style
//!   `requires`/`ensures`, exec and proof fns, exec and proof bodies, spec-fn
//!   bodies returning a value and spec-fn results bound at `int`) — exec and
//!   non-exec, every width 8..128 and both signs;
//! * ground truth: an exact `i128` evaluator of §5b (values a `u128` holds
//!   beyond `i128::MAX` are not generated; a case whose exact value leaves
//!   `i128` is skipped and counted).
//!
//! A case is decided when every operand is pinned (`requires x == v`) or a
//! literal. `Verified` for a false goal (FALSE VERIFIED) or a refutation of a
//! true one (FALSE COUNTEREXAMPLE) fails; so does a DECIDED verdict for a goal
//! §5b refuses (a binding the declared type cannot hold, a typed-seam node
//! whose declared type is not the one its operands derive: RULE). A goal over
//! an unspecified length must never be `Verified` unless every `nat`
//! satisfies it (then the case is skipped). `Unknown` is fail-closed and
//! tolerated, but counted, and coverage demands decided cases.
//!
//! `ORACLE_SEED`, `ORACLE_CASES` steer the generator; `ORACLE_VERBOSE=1`
//! prints every `Unknown`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;

use trust_vc_core::ir::integer_surface::{expr_variants_in, IntegerRole, EXPR_VARIANTS};
use trust_vc_core::ir::{
    ArithOp, CollectionOp, CompareOp, IntConstKind, MatchArm, MatchPattern, QuantifierKind,
    SpecialArithOp, TrustVcExpr, TrustVcType, WrappingMode,
};
use trust_vc_core::vc::{
    ObligationKind, ProofObligation, TypedProofObligation, VariableDecl, VerificationContext,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Integer-role variants the oracle cannot give a VALUE to, and why. Every
/// other variant with a role other than `None` must be generated.
const EXEMPT: &[(&str, &str)] = &[
    (
        "ReadPlace",
        "a read of a memory place: its value is the heap's, not a function of the expression",
    ),
    (
        "ProphecyNew",
        "a fresh prophecy: unconstrained by construction",
    ),
    (
        "ProphecyResolve",
        "constrains a prophecy of the mut-ref lane; no integer value of its own",
    ),
    (
        "Quantifier",
        "a Boolean binder: its integer binders are typed like pinned variables, which \
         every case exercises; quantifier bodies compute same-type arithmetic exactly \
         (the documented FV-B deviation), a separate model",
    ),
];

// ---------------------------------------------------------------------------
// Types and values.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct T {
    w: u32,
    s: bool,
}
const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];
const I32: T = T { w: 32, s: true };
const U8: T = T { w: 8, s: false };

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
    /// Every value of `self` is a value of `outer`.
    fn within(self, outer: T) -> bool {
        match (self.s, outer.s) {
            (false, false) | (true, true) => self.w <= outer.w,
            (false, true) => self.w < outer.w,
            (true, false) => false,
        }
    }
    fn value_of_bits(self, bits: u128) -> Option<i128> {
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
        self.value_of_bits(exact as u128)
    }
}

fn all_types() -> Vec<T> {
    WIDTHS
        .iter()
        .flat_map(|&w| [T { w, s: false }, T { w, s: true }])
        .collect()
}

/// A value's type: fixed-width, `int`, or `nat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Ty {
    F(T),
    Int,
    Nat,
}
impl Ty {
    fn ir(self) -> TrustVcType {
        match self {
            Ty::F(t) => t.ir(),
            Ty::Int => TrustVcType::MathInt,
            Ty::Nat => TrustVcType::Nat,
        }
    }
    fn rust(self) -> String {
        match self {
            Ty::F(t) => t.rust(),
            Ty::Int => "int".to_string(),
            Ty::Nat => "nat".to_string(),
        }
    }
    fn holds(self, v: i128) -> bool {
        match self {
            Ty::F(t) => t.contains(v),
            Ty::Int => true,
            Ty::Nat => v >= 0,
        }
    }
    fn fixed(self) -> Option<T> {
        match self {
            Ty::F(t) => Some(t),
            _ => None,
        }
    }
    fn unbounded(self) -> bool {
        matches!(self, Ty::Int | Ty::Nat)
    }
}

// ---------------------------------------------------------------------------
// Binding sites (checked for coverage like the expression variants).
// ---------------------------------------------------------------------------

/// A fieldless enum and `$all`, EVERY variant in declaration order — derived
/// from the enum itself, so a new variant is in `$all`, and so in every
/// coverage check over it, by construction (never a hand-kept list).
macro_rules! enum_with_all {
    (
        $(#[$meta:meta])*
        enum $name:ident, all = $all:ident {
            $($(#[$vmeta:meta])* $variant:ident,)*
        }
    ) => {
        $(#[$meta])*
        enum $name {
            $($(#[$vmeta])* $variant,)*
        }
        const $all: &[$name] = &[$($name::$variant,)*];
    };
}

enum_with_all! {
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Site, all = ALL_SITES {
    /// `requires x == v`, substituted by equality where the solver does.
    PinnedVariable,
    ArithOperand,
    BitwiseOperand,
    ShiftOperand,
    CompareOperand,
    /// `x.wrapping_*(y)` / `saturating_*`: both at the method's type.
    WrappingOperand,
    CastOperand,
    /// A `match` arm at the match's (derived) type, each by its own sign.
    MatchArm,
    /// A conditional branch at the conditional's (derived) type.
    IteBranch,
    /// `let v: T = value`.
    LetDeclared,
    /// `f(arg)` at the parameter's type.
    CallArgument,
    /// `f(..) == body` at the declared result type.
    SpecFnResult,
    /// An element of a sequence literal at its element type.
    SeqElement,
    /// `choose|v: T| v == value`.
    ChooseBinder,
    /// A `take`/`skip` COUNT lifted to a length by its own sign, specified
    /// only for `0 <= n <= len` — also inside a spec function's body, whose
    /// defining axiom checks no precondition (§5b rule 10).
    CollectionCount,
    /// An element read through a chain of receivers (`take`, `push`, `let`,
    /// a conditional), each DECLARING its element type (typed seam): the
    /// read is refused wherever any claim disagrees with what the chain
    /// derives, at every depth.
    ElementReceiver,
    /// A literal at its DECLARED type (typed seam): refused unless the type
    /// holds its value.
    DeclaredLiteral,
    /// `v = value` to a `let mut v: T` (source body): the value bound at `T`.
    Assignment,
    /// `v += value` to a `let mut v: T = 0`: `v + value` bound at `T`.
    CompoundAssignment,
    /// `v = value` to a deferred `let v: T;`.
    DeferredBinding,
    /// `*r = value` through `let r = &mut v` of a `let mut v: T`.
    DerefWrite,
    /// `*r = value` through `let r = &mut v` of an unascribed `let mut v = w`.
    InferredDerefWrite,
    /// `t.0 = value` to a `let mut t: (T, T)`.
    FieldWrite,
    /// `s.f = value` to a `let mut s = W { f: 0 }` (`struct W { f: T }`).
    StructFieldWrite,
    /// `p.0 = value` to a parameter `mut p: (T, T)`.
    ParamFieldWrite,
    /// `*r = value` through `let r = &mut s.f` (`struct W { f: T }`), read
    /// back through `*r`.
    FieldAliasWrite,
    /// `*r = value` through `let r = &mut c[0]` of a `let mut c: Vec<T>`,
    /// read back through `*r` (exec bodies: a ghost sequence has no `&mut`
    /// cell).
    CellAliasWrite,
    /// `v = value` to `let mut v = w` (`w: T`): a binding whose type is
    /// inferred from its initializer.
    InferredBinding,
    /// `v = value` to `let mut v = e[0]` (`e: Seq<T>`): the initializer's
    /// type is its element type, whatever literal indexes it.
    ElementWitnessBinding,
    /// `v = value` to `let mut v; v = e[0];` (`e: Seq<T>`): a deferred
    /// binding typed by its first write.
    DeferredWitnessBinding,
    /// `v = value` to the payload of `if let Some(mut v) = o` (`o:
    /// Option<T>`): a binding whose type is the pattern's.
    PatternBinding,
    /// `v = value` to the payload of a `match o { Some(mut v) => .. }` arm.
    MatchPayloadBinding,
    /// Any binding site in a file whose declared-width lane is OFF (a glob
    /// import): a `u8` there need not be the primitive (source frontend).
    LaneOffFile,
    /// `fK(arg)` of an INLINE spec function (typed seam): the argument is
    /// bound at the parameter's type before the body is substituted.
    InlineCallArgument,
    /// A cast DECLARED from a type that is not its operand's — a `char`, a
    /// type parameter, a sequence (typed seam): refused.
    CastFromLie,
    /// `let w = value; let r = &w; let v: T = *r;`: an unascribed binding read
    /// through a borrow into a typed slot (its type is the slot's).
    BorrowedBindingRead,
    /// `let w = value; let f = || w; let v: T = f();`: an unascribed binding
    /// read through a closure capture into a typed slot.
    CapturedBindingRead,
    /// `let w = value; let v: T = w;`: an unascribed binding copied into a
    /// typed slot, which gives the binding its type.
    BindingCopy,
    /// `let v: T = pass(value);` for an exec `fn pass(x: T) -> T { x }`: the
    /// argument at the exec parameter's type.
    ExecCallArgument,
    /// `let w = value; let v: T = w.clone();`: a trait method whose result is
    /// the binding's type gives the binding the slot's type.
    MethodResultBinding,
    /// `let f = |a| a; let v: T = f(value);`: an unannotated closure
    /// parameter, typed by the argument and the slot its result fills.
    ClosureParameter,
    /// `let mut t: T = value;` written into a struct field through a `&mut`
    /// the lane does not track (a conditional borrow passed to
    /// `std::mem::swap`): fail-closed, never decided (`Bind::fail_closed`).
    UntrackedBorrowWrite,
}
}

/// Which frontend can express a site: both, only the typed seam (a declared
/// type is a producer's claim there; the source frontend derives it), or
/// only the source frontend (the typed seam has no statements: a write is a
/// source construct). An exhaustive `match`, so a new site does not compile
/// until it is classified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Frontends {
    Both,
    SeamOnly,
    SourceOnly,
}
fn frontends(site: Site) -> Frontends {
    match site {
        Site::PinnedVariable
        | Site::ArithOperand
        | Site::BitwiseOperand
        | Site::ShiftOperand
        | Site::CompareOperand
        | Site::WrappingOperand
        | Site::CastOperand
        | Site::MatchArm
        | Site::IteBranch
        | Site::LetDeclared
        | Site::CallArgument
        | Site::SpecFnResult
        | Site::SeqElement
        | Site::ChooseBinder
        | Site::CollectionCount => Frontends::Both,
        Site::ElementReceiver
        | Site::DeclaredLiteral
        | Site::InlineCallArgument
        | Site::CastFromLie => Frontends::SeamOnly,
        Site::Assignment
        | Site::CompoundAssignment
        | Site::DeferredBinding
        | Site::DerefWrite
        | Site::InferredDerefWrite
        | Site::FieldWrite
        | Site::StructFieldWrite
        | Site::ParamFieldWrite
        | Site::FieldAliasWrite
        | Site::CellAliasWrite
        | Site::InferredBinding
        | Site::ElementWitnessBinding
        | Site::DeferredWitnessBinding
        | Site::PatternBinding
        | Site::MatchPayloadBinding
        | Site::LaneOffFile
        | Site::BorrowedBindingRead
        | Site::CapturedBindingRead
        | Site::BindingCopy
        | Site::ExecCallArgument
        | Site::MethodResultBinding
        | Site::ClosureParameter
        | Site::UntrackedBorrowWrite => Frontends::SourceOnly,
    }
}

// ---------------------------------------------------------------------------
// The generated tree.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WMode {
    Wrapping,
    Saturating,
}

/// A spec function `fK(p: P) -> R { p }` or `{ p + 1 }` (`plus_one`),
/// declared INLINE on the typed seam one time in three (its body substituted
/// at the call, its argument bound first).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SpecFn {
    param: Ty,
    result: Ty,
    plus_one: bool,
    inline: bool,
}

#[derive(Debug, Clone)]
enum N {
    /// A variable pinned by `requires name == value`.
    Var {
        name: String,
        ty: Ty,
        value: i128,
    },
    /// A literal of its own type (an `i32` one is the untyped placeholder).
    Lit {
        value: i128,
        ty: Ty,
    },
    /// `-(mag)` of the type (mag > 0; an `i32` one is untyped).
    NegLit {
        mag: i128,
        ty: Ty,
    },
    /// An unsuffixed literal (`Int{32}`), value within `i32`.
    Untyped {
        value: i128,
    },
    /// `T::MIN` / `T::MAX`.
    Const {
        t: T,
        max: bool,
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
    Shift {
        shl: bool,
        l: Box<N>,
        k: i128,
        kt: T,
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
    /// `match s { 0 => a0, 1 => a1, .., _ => an }` over a `u8` pinned to
    /// `pick`; `guard` guards arm 1 with `t if t >= 1` (a binder pattern).
    Match {
        sname: String,
        pick: usize,
        arms: Vec<N>,
        guard: bool,
        decl: Ty,
    },
    Cast {
        e: Box<N>,
        to: Ty,
    },
    /// A cast DECLARED `from` a type that is not its operand's (typed seam):
    /// refused (§5b rule 13).
    CastLie {
        e: Box<N>,
        from: FromLie,
        to: Ty,
    },
    Wrap {
        mode: WMode,
        op: ArithOp,
        l: Box<N>,
        r: Box<N>,
        t: T,
    },
    /// `let name: decl = value; name` (typed seam: anywhere; source: the
    /// top of a body).
    Let {
        name: String,
        decl: Ty,
        value: Box<N>,
    },
    /// `fK(arg)`.
    Call {
        f: usize,
        sig: SpecFn,
        arg: Box<N>,
    },
    /// `s.len()` of a `Seq<u8>` pinned to `len` (typed seam).
    Len {
        sname: String,
        len: i128,
    },
    /// `seq![e0, e1, ..][idx]` with element type `et`.
    Elem {
        elems: Vec<N>,
        idx: usize,
        et: T,
    },
    /// `choose|v: t| v == value`.
    Choose {
        t: T,
        value: i128,
    },
    /// A literal DECLARED at a type that cannot hold its value (typed seam):
    /// `IntLit { -1, nat }`, `IntLit { -1, u8 }`, `IntLit { 200, i8 }`.
    LitLie {
        value: i128,
        ty: Ty,
    },
    /// `s.take(n).len()` / `s.skip(n).len()` of a `Seq<u8>` pinned to `len`.
    Count {
        sname: String,
        len: i128,
        n: Box<N>,
        take: bool,
    },
    /// `ocK(s, n)` for `spec fn ocK(s: Seq<u8>, n: nty) -> int {
    /// s.take(n).len() as int }` (or `skip`): the count read inside a spec
    /// function's DEFINING AXIOM.
    CountCall {
        f: usize,
        take: bool,
        nty: Ty,
        sname: String,
        len: i128,
        n: Box<N>,
    },
    /// `seq![..]` of `et`, then each link in turn (a whole-sequence `take`, a
    /// `push`, a `let`, a conditional) DECLARED `Seq<link type>`, then read at
    /// `idx` DECLARED `read` (typed seam): refused unless every claim is `et`.
    ElemVia {
        elems: Vec<N>,
        idx: usize,
        et: T,
        links: Vec<(Link, T)>,
        read: T,
    },
}

/// The declared `from_ty` of an [`N::CastLie`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FromLie {
    Char,
    TypeParam,
    SeqOf(T),
}
impl FromLie {
    fn ir(self) -> TrustVcType {
        match self {
            FromLie::Char => TrustVcType::Char,
            FromLie::TypeParam => TrustVcType::TypeParam("T".to_string()),
            FromLie::SeqOf(t) => TrustVcType::Seq(Box::new(t.ir())),
        }
    }
}

/// One receiver link of [`N::ElemVia`]: each keeps the element at `idx`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Link {
    TakeAll,
    Push,
    Let,
    Ite,
}

/// A spec function wrapping a count: its parameter type and `take`/`skip`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CountFn {
    take: bool,
    nty: Ty,
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
        _ => unreachable!("not an untyped literal"),
    }
}

/// The two operand types after the untyped-literal rule (§5b rules 2, 7).
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

/// §5b rule 1: one fixed type computes in it; anything else is exact — `nat`
/// when both operands are `nat`s and the join keeps them `nat` (`keeps_nat`:
/// not a subtraction), else `int`. A declared `nat` alone makes nothing `nat`
/// (§5b rule 6: `nat + int` and `nat / int` are `int`).
fn derive(l: &N, r: &N, decl: Ty, keeps_nat: bool) -> Ty {
    if decl == Ty::Int {
        return Ty::Int;
    }
    let (lt, rt) = settle(l, r, decl);
    if decl.unbounded() || lt.unbounded() || rt.unbounded() {
        return if keeps_nat && lt == Ty::Nat && rt == Ty::Nat {
            Ty::Nat
        } else {
            Ty::Int
        };
    }
    if lt != rt {
        Ty::Int
    } else {
        lt
    }
}

/// The type each `match` arm denotes and the match's type
/// (`ir_lowering::derive_arms_int_type`).
fn arm_types(arms: &[N], decl: Ty) -> (Vec<Ty>, Ty) {
    let typed: Vec<Ty> = arms.iter().filter(|a| !is_untyped(a)).map(ty).collect();
    let peer = match typed.split_first() {
        Some((first, rest)) => rest.iter().all(|t| t == first).then_some(*first),
        None => decl.fixed().map(Ty::F),
    };
    let tys: Vec<Ty> = arms
        .iter()
        .map(|a| {
            if is_untyped(a) {
                match peer {
                    Some(p) if p.holds(untyped_value(a)) => p,
                    _ => Ty::F(I32),
                }
            } else {
                ty(a)
            }
        })
        .collect();
    let derived = if decl == Ty::Int {
        Ty::Int
    } else if decl.unbounded() || tys.iter().any(|t| t.unbounded()) {
        if tys.iter().all(|t| *t == Ty::Nat) {
            Ty::Nat
        } else {
            Ty::Int
        }
    } else if tys.iter().all(|t| *t == tys[0]) {
        tys[0]
    } else if let Some(d) = decl.fixed() {
        if tys.iter().all(|t| t.fixed().is_some_and(|tt| tt.within(d))) {
            decl
        } else {
            Ty::Int
        }
    } else {
        Ty::Int
    };
    (tys, derived)
}

fn ty(n: &N) -> Ty {
    match n {
        N::Var { ty, .. } | N::Lit { ty, .. } | N::NegLit { ty, .. } => *ty,
        N::Untyped { .. } => Ty::F(I32),
        N::Const { t, .. } | N::Wrap { t, .. } | N::Choose { t, .. } => Ty::F(*t),
        N::Elem { et, .. } => Ty::F(*et),
        N::Arith { op, l, r, decl } => derive(l, r, *decl, *op != ArithOp::Sub),
        N::Bit { l, r, decl, .. } | N::Ite { l, r, decl, .. } => derive(l, r, *decl, true),
        // The negation of a `nat` is an `int`.
        N::Neg(e) => match ty(e) {
            Ty::Nat => Ty::Int,
            t => t,
        },
        N::Not(e) => ty(e),
        N::Cast { to, .. } | N::CastLie { to, .. } => *to,
        N::Shift { l, .. } => ty(l),
        N::Match { arms, decl, .. } => arm_types(arms, *decl).1,
        N::Let { decl, .. } => *decl,
        N::Call { sig, .. } => sig.result,
        N::Len { .. } | N::Count { .. } | N::CountCall { .. } => Ty::Int,
        N::LitLie { ty, .. } => *ty,
        N::ElemVia { read, .. } => Ty::F(*read),
    }
}

/// A node DECLARING an integer type its operands do not derive (typed seam;
/// the source lowering declares the derived type): refused, like every
/// other disagreement (`ir_lowering::validate_ir_typing`).
fn declared_type_lie(n: &N) -> bool {
    match n {
        N::Arith { decl, .. } | N::Bit { decl, .. } | N::Ite { decl, .. } => *decl != ty(n),
        N::Match { arms, decl, .. } => arm_types(arms, *decl).1 != *decl,
        _ => false,
    }
}

/// The value of a `take`/`skip` of a length-`len` sequence at the count
/// value `n`: exact where `0 <= n <= len`, UNSPECIFIED otherwise (a `nat`
/// Verus does not determine).
fn count_value(take: bool, len: i128, n: i128, overflow: bool) -> Val {
    if (0..=len).contains(&n) {
        Val::V(if take { n } else { len - n }, overflow)
    } else {
        Val::Unspecified
    }
}

// ---------------------------------------------------------------------------
// The exact evaluator of §5b.
// ---------------------------------------------------------------------------

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

/// `l op r` in `t`: `(value, overflowed)`; `/ %` truncate (Rust).
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

/// What a tree evaluates to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    /// `(value, overflowed on the taken path)`.
    V(i128, bool),
    /// §5b refuses it: a value bound at a type that cannot hold it.
    Refused,
    /// A `nat` Verus leaves unspecified (a `take`/`skip` length outside
    /// `0 <= n <= len`): only at the root of a comparison.
    Unspecified,
}

/// A binding of a value of type `vt` (a literal form when `literal`) at the
/// declared type `decl` (§5b rule 6 and the call-argument clause): `Some`
/// when bound, `None` when refused.
fn binds(vt: Ty, value: i128, literal: bool, decl: Ty, widening_ok: bool) -> Option<()> {
    if vt == decl {
        return Some(());
    }
    if literal {
        return decl.holds(value).then_some(());
    }
    match decl {
        Ty::Int => Some(()),
        Ty::Nat => matches!(vt, Ty::F(T { s: false, .. }) | Ty::Nat).then_some(()),
        Ty::F(d) => match vt {
            Ty::F(v) if widening_ok && v.within(d) => Some(()),
            _ => None,
        },
    }
}

/// A literal form (any suffix) — its value is known where it is bound.
fn is_literal_form(n: &N) -> bool {
    matches!(n, N::Lit { .. } | N::NegLit { .. } | N::Untyped { .. })
}

/// An evaluated operand: its value, and whether it overflowed on the taken path.
type Flagged = (i128, bool);

fn eval(n: &N) -> Option<Val> {
    use Val::{Refused, V};
    let both = |l: &N, r: &N| -> Option<Result<(Flagged, Flagged), ()>> {
        match (eval(l)?, eval(r)?) {
            (V(a, ao), V(b, bo)) => Some(Ok(((a, ao), (b, bo)))),
            (Val::Unspecified, _) | (_, Val::Unspecified) => None,
            _ => Some(Err(())),
        }
    };
    if declared_type_lie(n) {
        return Some(Refused);
    }
    Some(match n {
        N::Var { value, .. } | N::Lit { value, .. } | N::Untyped { value } => V(*value, false),
        N::Choose { value, .. } => V(*value, false),
        N::Len { len, .. } => V(*len, false),
        N::NegLit { mag, .. } => V(-*mag, false),
        // `u128::MAX` is beyond the oracle's `i128` (its `T::max` is the
        // model's `i128::MAX` cap, not the constant): the case is skipped
        // (seed 424242 judged `u128::MAX != i128::MAX` false).
        N::Const { t, max: true } if t.w == 128 && !t.s => return None,
        N::Const { t, max } => V(if *max { T::max(*t) } else { T::min(*t) }, false),
        N::Arith { op, l, r, .. } => match both(l, r)? {
            Err(()) => Refused,
            Ok(((lv, lo), (rv, ro))) => match ty(n) {
                Ty::F(t) => {
                    let (v, o) = in_type(t, *op, lv, rv)?;
                    V(v, lo || ro || o)
                }
                _ => V(exact(*op, lv, rv)?, lo || ro),
            },
        },
        N::Bit { op, l, r, .. } => match both(l, r)? {
            Err(()) => Refused,
            Ok(((lv, lo), (rv, ro))) => V(
                match op {
                    SpecialArithOp::BitAnd => lv & rv,
                    SpecialArithOp::BitOr => lv | rv,
                    _ => lv ^ rv,
                },
                lo || ro,
            ),
        },
        N::Neg(e) => match eval(e)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => match ty(e) {
                Ty::F(t) => {
                    let ex = v.checked_neg()?;
                    V(t.wrap(ex)?, o || !t.contains(ex))
                }
                _ => V(v.checked_neg()?, o),
            },
        },
        N::Not(e) => match eval(e)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => {
                let Ty::F(t) = ty(e) else { return None };
                V(t.wrap(!v)?, o)
            }
        },
        N::Ite { c, l, r, .. } => match both(l, r)? {
            Err(()) => Refused,
            Ok((lv, rv)) => {
                let (v, o) = if *c { lv } else { rv };
                V(v, o)
            }
        },
        N::Match {
            pick, arms, decl, ..
        } => {
            let mut values = Vec::new();
            for a in arms {
                match eval(a)? {
                    Refused => return Some(Refused),
                    Val::Unspecified => return None,
                    V(v, o) => values.push((v, o)),
                }
            }
            // Every arm the integer it holds (its own sign): the match's
            // type is derived so that it holds every arm's value.
            let _ = arm_types(arms, *decl);
            let (v, o) = values[*pick];
            V(v, o)
        }
        N::Cast { e, to } => match eval(e)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => match to {
                Ty::F(t) => V(t.wrap(v)?, o),
                Ty::Int => V(v, o),
                Ty::Nat => {
                    if v < 0 {
                        return None;
                    }
                    V(v, o)
                }
            },
        },
        N::Shift { shl, l, k, .. } => match eval(l)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => {
                let Ty::F(t) = ty(l) else { return None };
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let kk = *k as u32;
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
                let r = if *shl {
                    t.wrap(((v as u128) << kk) as i128)?
                } else {
                    v >> kk
                };
                V(r, o)
            }
        },
        N::Wrap { mode, op, l, r, t } => match both(l, r)? {
            Err(()) => Refused,
            Ok(_) if wrap_refused(r, *t) => Refused,
            Ok(((lv, lo), (rv, ro))) => {
                let e = exact(*op, lv, rv)?;
                let v = match mode {
                    WMode::Wrapping => t.wrap(e)?,
                    WMode::Saturating => e.clamp(T::min(*t), T::max(*t)),
                };
                V(v, lo || ro)
            }
        },
        N::Let { decl, value, .. } => match eval(value)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => {
                // A `let` binds an UNTYPED literal form by its value; a
                // suffixed literal is a value of its suffix's type.
                if binds(ty(value), v, is_untyped(value), *decl, false).is_none() {
                    Refused
                } else {
                    V(v, o)
                }
            }
        },
        N::Call { sig, arg, .. } => match eval(arg)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => {
                if binds(ty(arg), v, is_literal_form(arg), sig.param, true).is_none() {
                    Refused
                } else {
                    // The body `p` / `p + 1`, computed at the result's type:
                    // an `int` result computes it exactly (rule 8), a
                    // fixed-width one in `P` (== R). Spec bodies are never
                    // overflow-checked.
                    let body = if sig.plus_one {
                        match (sig.result, sig.param) {
                            (Ty::F(_), Ty::F(p)) => in_type(p, ArithOp::Add, v, 1)?.0,
                            _ => v.checked_add(1)?,
                        }
                    } else {
                        v
                    };
                    V(body, o)
                }
            }
        },
        N::Elem { elems, idx, et } => {
            if elem_refused(elems, *et) {
                return Some(Refused);
            }
            let mut chosen = None;
            for (k, e) in elems.iter().enumerate() {
                match eval(e)? {
                    Refused => return Some(Refused),
                    Val::Unspecified => return None,
                    V(v, o) => {
                        if k == *idx {
                            chosen = Some((v, o));
                        }
                    }
                }
            }
            let (v, o) = chosen?;
            V(v, o)
        }
        N::LitLie { .. } | N::CastLie { .. } => Refused,
        N::Count { len, n, take, .. } => match eval(n)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => count_value(*take, *len, v, o),
        },
        N::CountCall {
            take, nty, len, n, ..
        } => match eval(n)? {
            Refused => Refused,
            Val::Unspecified => return None,
            V(v, o) => {
                if binds(ty(n), v, is_literal_form(n), *nty, true).is_none() {
                    Refused
                } else {
                    count_value(*take, *len, v, o)
                }
            }
        },
        N::ElemVia {
            elems,
            idx,
            et,
            links,
            read,
        } => {
            if *read != *et || links.iter().any(|(_, t)| t != et) || elem_refused(elems, *et) {
                return Some(Refused);
            }
            let (v, o) = match eval(&elems[*idx])? {
                Refused => return Some(Refused),
                Val::Unspecified => return None,
                V(v, o) => (v, o),
            };
            for e in elems {
                if matches!(eval(e)?, Refused) {
                    return Some(Refused);
                }
            }
            V(v, o)
        }
    })
}

/// `eval` of a `#[trust_vc::spec] fn -> int` body: its plain arithmetic —
/// `+ - * / %`, unary `-`, `if`, `match` — is exact throughout (rule 8).
fn eval_int_context(n: &N) -> Option<Val> {
    use Val::{Refused, V};
    Some(match n {
        N::Arith { op, l, r, .. } => match (eval_int_context(l)?, eval_int_context(r)?) {
            (V(a, _), V(b, _)) => V(exact(*op, a, b)?, false),
            (Val::Unspecified, _) | (_, Val::Unspecified) => return None,
            _ => Refused,
        },
        N::Neg(e) => match eval_int_context(e)? {
            V(a, _) => V(a.checked_neg()?, false),
            Refused => Refused,
            Val::Unspecified => return None,
        },
        N::Ite { c, l, r, .. } => match (eval_int_context(l)?, eval_int_context(r)?) {
            (V(a, _), V(b, _)) => V(if *c { a } else { b }, false),
            (Val::Unspecified, _) | (_, Val::Unspecified) => return None,
            _ => Refused,
        },
        N::Match { pick, arms, .. } => {
            let mut values = Vec::new();
            for a in arms {
                match eval_int_context(a)? {
                    Refused => return Some(Refused),
                    Val::Unspecified => return None,
                    V(v, _) => values.push(v),
                }
            }
            V(values[*pick], false)
        }
        other => match eval(other)? {
            V(v, _) => V(v, false),
            Refused => Refused,
            Val::Unspecified => Val::Unspecified,
        },
    })
}

// ---------------------------------------------------------------------------
// Generation.
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
    fn t(&mut self) -> T {
        self.pick(&all_types())
    }
    /// A value of `t`, biased to the edges and the sign-bit boundary.
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
            half,
            half.saturating_add(1),
            100,
            200,
        ];
        if t.s {
            edges.extend([-1, -2, t.min() + 1, -128, -56, -256]);
        } else {
            edges.extend([255, 128, 256, 65535]);
        }
        let v = match self.below(4) {
            0 | 1 => self.pick(&edges),
            #[allow(clippy::cast_possible_wrap)]
            2 => self.below(41) as i128 - 20,
            _ => {
                let raw = (u128::from(self.next()) << 64) | u128::from(self.next());
                t.value_of_bits(raw).unwrap_or(0)
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

/// Which frontend a tree is generated for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Front {
    Seam,
    Source,
}

struct Gen<'a> {
    rng: &'a mut Rng,
    front: Front,
    /// `int`/`nat` values are available (the typed seam; proof fns).
    ghost: bool,
    pins: Vec<(String, Ty, i128)>,
    bools: Vec<(String, bool)>,
    /// `u8` scrutinees, pinned.
    selectors: Vec<(String, i128)>,
    /// `Seq<u8>` variables with a pinned length.
    seqs: Vec<(String, i128)>,
    fns: Vec<SpecFn>,
    /// Count-wrapping spec functions (`ocK`), numbered from `fn_base`.
    count_fns: Vec<(usize, CountFn)>,
    /// Global index of this case's first spec fn (source files hold many).
    fn_base: usize,
    /// The tree is EXEC code (a `let` in an exec fn body): no spec-only
    /// constructs (spec fn calls, `choose`, sequences).
    exec_code: bool,
    chooses: usize,
}

impl Gen<'_> {
    fn some_ty(&mut self) -> Ty {
        if self.ghost && self.rng.below(6) == 0 {
            if self.rng.below(3) == 0 {
                Ty::Nat
            } else {
                Ty::Int
            }
        } else {
            Ty::F(self.rng.t())
        }
    }
    fn value_of(&mut self, t: Ty) -> i128 {
        match t {
            Ty::F(t) => self.rng.value(t),
            Ty::Int => self.rng.int_value(),
            Ty::Nat => self.rng.int_value().checked_abs().unwrap_or(0),
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
    fn lit_of(&mut self, t: Ty) -> N {
        let value = self.value_of(t);
        if value == i128::MIN || (t == Ty::F(I32) && self.front == Front::Source) {
            return self.var(t);
        }
        if value < 0 {
            N::NegLit { mag: -value, ty: t }
        } else {
            N::Lit { value, ty: t }
        }
    }
    fn untyped(&mut self) -> N {
        let v = self.rng.value(I32);
        if v < 0 && v != i128::from(i32::MIN) && self.rng.coin() {
            N::NegLit {
                mag: -v,
                ty: Ty::F(I32),
            }
        } else if v < 0 {
            N::Untyped {
                value: v.max(-2_147_483_647),
            }
        } else {
            N::Untyped { value: v }
        }
    }
    /// A leaf; `untyped_ok` allows the untyped forms.
    fn leaf(&mut self, untyped_ok: bool) -> N {
        // An `i32` variable pinned at an edge: substituted by equality, its
        // value must stay an `i32` (§5b rule 3 — an untyped-looking `i32`
        // literal next to a peer of another type used to be retyped).
        if self.rng.below(8) == 0 {
            let value = self.rng.pick(&[
                i128::from(i32::MAX),
                i128::from(i32::MIN) + 1,
                -128,
                127,
                128,
                -32768,
                32767,
                255,
                -1,
            ]);
            let name = format!("x{}", self.pins.len());
            self.pins.push((name.clone(), Ty::F(I32), value));
            return N::Var {
                name,
                ty: Ty::F(I32),
                value,
            };
        }
        if self.front == Front::Seam && self.rng.below(24) == 0 {
            return self.lit_lie();
        }
        let t = self.some_ty();
        match self.rng.below(if untyped_ok { 7 } else { 5 }) {
            0 | 1 => self.var(t),
            2 => {
                if t == Ty::F(I32) && !untyped_ok {
                    return self.var(t);
                }
                self.lit_of(t)
            }
            3 => {
                let t = self.rng.t();
                N::Const {
                    t,
                    max: self.rng.coin(),
                }
            }
            4 => self.var(t),
            _ => self.untyped(),
        }
    }
    /// The type the syn lowering declares a binary node with: its typed
    /// operand's (`ir_lowering::derived_node_type`), then derived (a `nat`
    /// difference is re-derived `int` by [`ty`]).
    fn lowered_decl(l: &N, r: &N, keeps_nat: bool) -> Ty {
        derive(l, r, if is_untyped(l) { ty(r) } else { ty(l) }, keeps_nat)
    }
    /// The declared type of a binary node: the source lowering's (derived —
    /// `ir_lowering::arith_node_type`, so a `nat` difference is declared
    /// `int`), or on the typed seam any type, a lie included (refused).
    fn decl(&mut self, l: &N, r: &N) -> Ty {
        self.decl_of(l, r, true)
    }
    fn decl_of(&mut self, l: &N, r: &N, keeps_nat: bool) -> Ty {
        if self.front == Front::Source {
            return Self::lowered_decl(l, r, keeps_nat);
        }
        match self.rng.below(7) {
            0 | 1 => ty(l),
            2 | 3 => ty(r),
            4 if self.ghost => Ty::Int,
            _ => Ty::F(self.rng.t()),
        }
    }
    /// Two operands, never both untyped.
    fn pair(&mut self, depth: u32) -> (N, N) {
        let l = self.node(depth - 1, true);
        let r = self.node(depth - 1, !is_untyped(&l));
        if self.rng.coin() {
            (l, r)
        } else {
            (r, l)
        }
    }
    fn bool_var(&mut self) -> (String, bool) {
        let c = self.rng.coin();
        let name = format!("c{}", self.bools.len());
        self.bools.push((name.clone(), c));
        (name, c)
    }
    fn node(&mut self, depth: u32, untyped_ok: bool) -> N {
        if depth == 0 || self.rng.below(5) == 0 {
            return self.leaf(untyped_ok);
        }
        let kinds = 21;
        match self.rng.below(kinds) {
            0..=2 => {
                let op = self.rng.pick(&[
                    ArithOp::Add,
                    ArithOp::Sub,
                    ArithOp::Mul,
                    ArithOp::Div,
                    ArithOp::Rem,
                ]);
                let (mut l, mut r) = self.pair(depth);
                // A `/` or `%` is over LEAVES: an exact (`int`) division of or
                // by a symbolic conditional over 64/128-bit values sends ay's
                // certificate validation into unbounded rational arithmetic
                // that the per-obligation watchdog cannot interrupt — a hang,
                // not a verdict (measured: one such case ran > 60 s without
                // returning, another 75 s), so it is kept out of the oracle.
                if matches!(op, ArithOp::Div | ArithOp::Rem) {
                    let leaf = |n: &N| {
                        matches!(
                            n,
                            N::Var { .. }
                                | N::Lit { .. }
                                | N::NegLit { .. }
                                | N::Untyped { .. }
                                | N::Const { .. }
                        )
                    };
                    if !leaf(&l) {
                        l = self.leaf(true);
                    }
                    if !leaf(&r) {
                        r = self.leaf(!is_untyped(&l));
                    }
                    if is_untyped(&l) && is_untyped(&r) {
                        let t = self.rng.t();
                        r = self.var(Ty::F(t));
                    }
                }
                // A spec-collection length (an unbounded `Int`) as an operand.
                if self.front == Front::Seam && self.rng.below(8) == 0 {
                    let name = format!("s{}", self.seqs.len());
                    let len = i128::from(u8::try_from(self.rng.below(4)).unwrap_or(0));
                    self.seqs.push((name.clone(), len));
                    l = N::Len { sname: name, len };
                }
                let decl = self.decl_of(&l, &r, op != ArithOp::Sub);
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
                let (l, r) = self.pair(depth);
                if ty(&l).unbounded() || ty(&r).unbounded() {
                    return self.leaf(untyped_ok);
                }
                let decl = self.decl(&l, &r);
                N::Bit {
                    op,
                    l: Box::new(l),
                    r: Box::new(r),
                    decl,
                }
            }
            4 => {
                let e = self.node(depth - 1, false);
                let signed = match ty(&e) {
                    Ty::F(t) => t.s,
                    Ty::Int => true,
                    Ty::Nat => false,
                };
                if !signed || is_literal_form(&e) {
                    return e;
                }
                N::Neg(Box::new(e))
            }
            5 => {
                let e = self.node(depth - 1, false);
                if ty(&e).unbounded() || is_literal_form(&e) {
                    return e;
                }
                N::Not(Box::new(e))
            }
            6 => {
                let (l, r) = self.pair(depth);
                let (cname, c) = self.bool_var();
                let decl = self.decl(&l, &r);
                N::Ite {
                    cname,
                    c,
                    l: Box::new(l),
                    r: Box::new(r),
                    decl,
                }
            }
            7 => {
                let e = self.node(depth - 1, false);
                let to = if self.ghost && self.rng.below(4) == 0 {
                    if self.rng.coin() {
                        Ty::Int
                    } else {
                        Ty::Nat
                    }
                } else {
                    Ty::F(self.rng.t())
                };
                // A cast declared from another type than its operand's, one
                // time in three on the typed seam (§5b rule 13).
                if self.front == Front::Seam && self.rng.below(3) == 0 {
                    let from = match self.rng.below(3) {
                        0 => FromLie::Char,
                        1 => FromLie::TypeParam,
                        _ => FromLie::SeqOf(self.rng.t()),
                    };
                    return N::CastLie {
                        e: Box::new(e),
                        from,
                        to,
                    };
                }
                N::Cast { e: Box::new(e), to }
            }
            8 => {
                let l = self.node(depth - 1, false);
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
            9 => self.wrap(depth),
            10 | 11 => self.matched(depth),
            12 if self.front == Front::Seam => {
                let value = self.node(depth - 1, true);
                let decl = self.let_decl(&value);
                let name = format!("v{}", self.pins.len() + self.bools.len() + self.fns.len());
                N::Let {
                    name,
                    decl,
                    value: Box::new(value),
                }
            }
            12 | 13 if !self.exec_code => self.call(depth),
            14 if !self.exec_code => {
                if self.front == Front::Seam && self.rng.coin() {
                    self.elem_via()
                } else {
                    self.elem(depth)
                }
            }
            // Substitution-sensitive shapes (§5b rule 3): an `i32` variable
            // pinned at an edge, negated or summed with an untyped literal,
            // so a substituted value that lost its `i32` type would be
            // retyped by the comparison peer (`-x0 < z_i8` with `x0 ==
            // -128` read `-(-128i8)`).
            16..=18 => {
                let v = if self.rng.coin() {
                    self.rng
                        .pick(&[-128i128, -32768, i128::from(i32::MIN) + 1, -1])
                } else {
                    self.rng.pick(&[
                        i128::from(i32::MAX),
                        i128::from(i32::MAX) - 1,
                        127,
                        32767,
                        255,
                    ])
                };
                let name = format!("x{}", self.pins.len());
                self.pins.push((name.clone(), Ty::F(I32), v));
                let x = N::Var {
                    name,
                    ty: Ty::F(I32),
                    value: v,
                };
                if v < 0 && self.rng.coin() {
                    N::Neg(Box::new(x))
                } else {
                    let k = i128::from(u8::try_from(self.rng.below(3)).unwrap_or(0)) + 1;
                    let (l, r) = if self.rng.coin() {
                        (x, N::Untyped { value: k })
                    } else {
                        (N::Untyped { value: k }, x)
                    };
                    let op = self.rng.pick(&[ArithOp::Add, ArithOp::Sub]);
                    let decl = self.decl_of(&l, &r, op != ArithOp::Sub);
                    let sum = N::Arith {
                        op,
                        l: Box::new(l),
                        r: Box::new(r),
                        decl,
                    };
                    // Beside a peer of ANOTHER type (`(x + 1) * 2i64`): an
                    // axiom instantiated at a bare `x` literal read the
                    // closed tree `x + 1` at the peer's type while the
                    // quantified axiom wraps it in `i32` (f8f2e624).
                    if self.rng.below(4) != 0 {
                        let t = T {
                            w: self.rng.pick(&[8u32, 16, 64, 128]),
                            s: self.rng.coin(),
                        };
                        let peer = if self.rng.below(4) != 0 {
                            N::Lit {
                                value: 2,
                                ty: Ty::F(t),
                            }
                        } else {
                            self.var(Ty::F(t))
                        };
                        let decl = self.decl(&sum, &peer);
                        N::Arith {
                            op: self.rng.pick(&[ArithOp::Mul, ArithOp::Add]),
                            l: Box::new(sum),
                            r: Box::new(peer),
                            decl,
                        }
                    } else {
                        sum
                    }
                }
            }
            15 if !self.exec_code => {
                let t = self.rng.t();
                // `i128::MIN`'s magnitude has no literal spelling.
                let value = self.rng.value(t).max(i128::MIN + 1);
                self.chooses += 1;
                N::Choose { t, value }
            }
            _ => self.leaf(untyped_ok),
        }
    }
    /// The comparison peer: a typed leaf, or — one time in four, beside a
    /// typed tree — an UNTYPED literal (negative more often than not), which
    /// takes the tree's type only where it holds the literal's value (§5b
    /// rule 2: `-1` beside a `u8` is -1, never 255).
    fn peer(&mut self, tree: &N) -> N {
        if !is_untyped(tree) && self.rng.below(4) == 0 {
            let v = self.rng.value(I32).clamp(-2_147_483_647, 2_147_483_647);
            let v = if self.rng.coin() { -v.abs() } else { v };
            return if v < 0 {
                N::NegLit {
                    mag: -v,
                    ty: Ty::F(I32),
                }
            } else {
                N::Untyped { value: v }
            };
        }
        self.leaf(false)
    }
    fn wrap(&mut self, depth: u32) -> N {
        let _ = depth;
        let t = self.rng.t();
        let mode = if self.rng.coin() {
            WMode::Wrapping
        } else {
            WMode::Saturating
        };
        let op = self.rng.pick(&[ArithOp::Add, ArithOp::Sub, ArithOp::Mul]);
        let l = self.var(Ty::F(t));
        // The operand is bound at the method's type: of that type, an untyped
        // literal (bound where it fits), or — rarely — another type (refused).
        let r = match self.rng.below(8) {
            0..=3 => self.var(Ty::F(t)),
            4 | 5 if t != I32 => self.lit_of(Ty::F(t)),
            6 => self.untyped(),
            _ => {
                let other = self.rng.t();
                self.var(Ty::F(other))
            }
        };
        N::Wrap {
            mode,
            op,
            l: Box::new(l),
            r: Box::new(r),
            t,
        }
    }
    /// A WIDENING match: arm 0 of a signed type `T`, every other arm of a
    /// type within `T` (an unsigned one more often than not, with its top
    /// bit set), so the match is typed `T` and a narrower arm is widened
    /// into it — the r6 shape, where the chain widened the later arms by
    /// the MATCH's sign. Returns the arms and the arm to pick.
    fn widening_arms(&mut self, count: usize) -> (Vec<N>, usize) {
        let wide = T {
            w: self.rng.pick(&[16, 32, 64, 128]),
            s: true,
        };
        let mut arms = vec![self.var(Ty::F(wide))];
        let mut narrow_at = Vec::new();
        for k in 1..count {
            let narrower: Vec<T> = all_types()
                .into_iter()
                .filter(|t| t.within(wide) && *t != wide)
                .collect();
            let t = if self.rng.below(4) == 0 {
                self.rng.pick(&narrower)
            } else {
                T {
                    w: self.rng.pick(&[8u32, 16, 32, 64]).min(wide.w / 2),
                    s: false,
                }
            };
            // Top bit set: the value a sign-extension would misread.
            let v = if !t.s && self.rng.below(3) != 0 {
                t.max() - i128::from(u8::try_from(self.rng.below(3)).unwrap_or(0))
            } else {
                self.rng.value(t)
            };
            let name = format!("x{}", self.pins.len());
            self.pins.push((name.clone(), Ty::F(t), v));
            arms.push(N::Var {
                name,
                ty: Ty::F(t),
                value: v,
            });
            narrow_at.push(k);
        }
        let pick = if self.rng.below(4) == 0 {
            0
        } else {
            self.rng.pick(&narrow_at)
        };
        (arms, pick)
    }
    fn matched(&mut self, depth: u32) -> N {
        let count = 2 + usize::try_from(self.rng.below(3)).unwrap_or(0);
        let widening = self.rng.below(3) == 0;
        let (mut arms, widening_pick) = if widening {
            self.widening_arms(count)
        } else {
            ((0..count).map(|_| self.node(depth - 1, true)).collect(), 0)
        };
        if arms.iter().all(is_untyped) {
            let t = self.rng.t();
            arms[0] = self.var(Ty::F(t));
        }
        let guard = count >= 3 && self.rng.coin();
        let pick = if widening {
            widening_pick
        } else {
            usize::try_from(self.rng.below(count as u64)).unwrap_or(0)
        };
        let sname = format!("m{}", self.selectors.len());
        // The last arm is `_`: the scrutinee value `count - 1 + k` selects it.
        let scrutinee = if pick + 1 == count {
            i128::try_from(pick).unwrap_or(0)
                + i128::from(u8::try_from(self.rng.below(3)).unwrap_or(0))
        } else {
            i128::try_from(pick).unwrap_or(0)
        };
        self.selectors.push((sname.clone(), scrutinee));
        let decl = match self.front {
            // The typed seam declares a widening match its widest arm's
            // type; the source lowering takes the first non-`i32` arm's,
            // which is the same type unless it is `i32` (computed below).
            Front::Seam if widening => ty(&arms[0]),
            Front::Source => {
                // `ir_lowering::match_lowering`: the first non-`i32` arm's type,
                // and every untyped arm that fits it coerced to it.
                let target = arms
                    .iter()
                    .map(ty)
                    .find(|t| *t != Ty::F(I32))
                    .unwrap_or_else(|| ty(&arms[0]));
                for arm in &mut arms {
                    if is_untyped(arm) && target != Ty::Nat && target.holds(untyped_value(arm)) {
                        let v = untyped_value(arm);
                        *arm = if v < 0 {
                            N::NegLit {
                                mag: -v,
                                ty: target,
                            }
                        } else {
                            N::Lit {
                                value: v,
                                ty: target,
                            }
                        };
                    }
                }
                // ...and the match is DECLARED at the type its arms derive.
                arm_types(&arms, target).1
            }
            Front::Seam => match self.rng.below(5) {
                0 if self.ghost => Ty::Int,
                1 => Ty::F(self.rng.t()),
                _ => {
                    let k = usize::try_from(self.rng.below(arms.len() as u64)).unwrap_or(0);
                    ty(&arms[k])
                }
            },
        };
        N::Match {
            sname,
            pick,
            arms,
            guard,
            decl,
        }
    }
    fn let_decl(&mut self, value: &N) -> Ty {
        // Any type, including a `nat` for a negative literal (`let x: nat =
        // -1` is refused: a `nat` holds no negative value, §5b rule 6).
        let vt = ty(value);
        match self.rng.below(6) {
            0..=2 => vt,
            3 if self.ghost => Ty::Int,
            4 if self.ghost => Ty::Nat,
            _ => Ty::F(self.rng.t()),
        }
    }
    fn call(&mut self, depth: u32) -> N {
        let param = self.some_ty();
        let plus_one = self.rng.coin();
        let result = match param {
            Ty::F(_) | Ty::Int if self.rng.coin() => param,
            Ty::Nat | Ty::F(T { s: false, .. }) if !plus_one && self.rng.coin() => Ty::Nat,
            _ if self.ghost || self.front == Front::Source => Ty::Int,
            _ => param,
        };
        let result = if result == Ty::Nat && plus_one {
            Ty::Int
        } else {
            result
        };
        let sig = SpecFn {
            param,
            result,
            plus_one,
            inline: self.front == Front::Seam && self.rng.below(3) == 0,
        };
        let f = self.fn_base + self.fns.len();
        self.fns.push(sig);
        // Any argument: bound where the parameter type holds it, else refused.
        let arg = match self.rng.below(4) {
            0 => self.var(param),
            1 if param != Ty::F(I32) || self.front == Front::Seam => self.lit_of(param),
            _ => self.node(depth - 1, true),
        };
        N::Call {
            f,
            sig,
            arg: Box::new(arg),
        }
    }
    fn elem(&mut self, depth: u32) -> N {
        let _ = depth;
        let et = self.rng.t();
        let count = 2 + usize::try_from(self.rng.below(2)).unwrap_or(0);
        let mut elems = vec![self.var(Ty::F(et))];
        for _ in 1..count {
            elems.push(match self.rng.below(4) {
                0 | 1 => self.var(Ty::F(et)),
                2 if et != I32 => self.lit_of(Ty::F(et)),
                _ => {
                    let v = self.rng.value(et).clamp(-2_147_483_647, 2_147_483_647);
                    if v < 0 {
                        N::NegLit {
                            mag: -v,
                            ty: Ty::F(I32),
                        }
                    } else {
                        N::Untyped { value: v }
                    }
                }
            });
        }
        let idx = usize::try_from(self.rng.below(count as u64)).unwrap_or(0);
        N::Elem { elems, idx, et }
    }
    /// A literal DECLARED at a type that cannot hold its value (seam).
    fn lit_lie(&mut self) -> N {
        let t = self.rng.t();
        if self.ghost && self.rng.below(3) == 0 {
            let mag = i128::from(u8::try_from(self.rng.below(200)).unwrap_or(0)) + 1;
            return N::LitLie {
                value: -mag,
                ty: Ty::Nat,
            };
        }
        if t == I32 || t.w == 128 {
            // The `i32` literal is the untyped placeholder, which holds any
            // value; a 128-bit type's range is the oracle's own.
            return N::LitLie {
                value: -1,
                ty: Ty::F(U8),
            };
        }
        let value = match self.rng.below(3) {
            0 if !t.s => -1 - i128::from(u8::try_from(self.rng.below(3)).unwrap_or(0)),
            1 => t.min() - 1,
            _ => t.max() + 1 + i128::from(u8::try_from(self.rng.below(100)).unwrap_or(0)),
        };
        N::LitLie {
            value,
            ty: Ty::F(t),
        }
    }
    /// An element read through a chain of receivers, each declaring its
    /// element type — a lie at a random depth one time in two (seam).
    fn elem_via(&mut self) -> N {
        let N::Elem { elems, idx, et } = self.elem(1) else {
            unreachable!("elem builds an Elem")
        };
        let depth = 1 + usize::try_from(self.rng.below(3)).unwrap_or(0);
        let lie_at = if self.rng.coin() {
            Some(usize::try_from(self.rng.below(depth as u64 + 1)).unwrap_or(0))
        } else {
            None
        };
        let other = loop {
            let t = self.rng.t();
            if t.w == et.w && t != et || self.rng.below(4) == 0 && t != et {
                break t;
            }
        };
        let mut links = Vec::new();
        let mut claim = et;
        for k in 0..depth {
            if lie_at == Some(k) {
                claim = other;
            }
            let link = self
                .rng
                .pick(&[Link::TakeAll, Link::Push, Link::Let, Link::Ite]);
            links.push((link, claim));
        }
        if lie_at == Some(depth) {
            claim = other;
        }
        N::ElemVia {
            elems,
            idx,
            et,
            links,
            read: claim,
        }
    }
    /// A pinned variable of type `t` holding exactly `value`.
    fn var_at(&mut self, t: Ty, value: i128) -> N {
        let name = format!("x{}", self.pins.len());
        self.pins.push((name.clone(), t, value));
        N::Var { name, ty: t, value }
    }
    /// A `take`/`skip` count — or one read inside a spec function — of a
    /// `Seq<u8>` pinned to a length, the count often out of `0..=len`
    /// (negative, one past the end, or a signed value whose bits read
    /// unsigned fall inside the length).
    fn count(&mut self) -> N {
        let len = self.rng.pick(&[0i128, 1, 2, 3, 300, 70000]);
        let sname = format!("s{}", self.seqs.len());
        self.seqs.push((sname.clone(), len));
        let t = if self.ghost && self.rng.below(3) == 0 {
            Ty::Int
        } else {
            Ty::F(self.rng.pick(&[
                T { w: 8, s: true },
                T { w: 16, s: true },
                T { w: 64, s: true },
                T { w: 8, s: false },
                T { w: 32, s: false },
                T { w: 64, s: false },
            ]))
        };
        let candidates = [-1i128, -2, 0, 1, len, len + 1, len - 1, len / 2, 255, 65535];
        let value = loop {
            let v = self.rng.pick(&candidates);
            if t.holds(v) {
                break v;
            }
        };
        let n = match self.rng.below(4) {
            0 if value >= 0 && value <= i128::from(i32::MAX) => N::Untyped { value },
            _ => self.var_at(t, value),
        };
        let take = self.rng.coin();
        // The spec-function-wrapped count: one in two on the seam, one in
        // three in the source (see `source_cases`).
        let wrapped = match self.front {
            Front::Seam => self.rng.coin(),
            Front::Source => self.rng.below(3) == 0,
        };
        if self.exec_code || !wrapped {
            return N::Count {
                sname,
                len,
                n: Box::new(n),
                take,
            };
        }
        let nty = match &n {
            N::Untyped { .. } => t,
            other => ty(other),
        };
        let f = self.fn_base + self.fns.len() + self.count_fns.len();
        self.count_fns.push((f, CountFn { take, nty }));
        N::CountCall {
            f,
            take,
            nty,
            sname,
            len,
            n: Box::new(n),
        }
    }
}

/// `Elem` element binding: an element of another type is refused (the
/// sequence literal's element type is its FIRST element's).
fn elem_refused(elems: &[N], et: T) -> bool {
    elems.iter().skip(1).any(|e| {
        if is_untyped(e) {
            !et.contains(untyped_value(e))
        } else {
            ty(e) != Ty::F(et)
        }
    })
}

/// `Wrap` operand binding: the right operand at the method's type.
fn wrap_refused(r: &N, t: T) -> bool {
    if is_untyped(r) {
        !t.contains(untyped_value(r))
    } else {
        ty(r) != Ty::F(t)
    }
}

/// Every binding site the tree exercises.
fn sites(n: &N, out: &mut BTreeSet<Site>) {
    match n {
        N::Var { .. } => {
            out.insert(Site::PinnedVariable);
        }
        N::Lit { .. } | N::NegLit { .. } | N::Untyped { .. } | N::Const { .. } => {}
        N::Len { .. } => {}
        N::Choose { .. } => {
            out.insert(Site::ChooseBinder);
        }
        N::Arith { l, r, .. } => {
            out.insert(Site::ArithOperand);
            sites(l, out);
            sites(r, out);
        }
        N::Bit { l, r, .. } => {
            out.insert(Site::BitwiseOperand);
            sites(l, out);
            sites(r, out);
        }
        N::Shift { l, .. } => {
            out.insert(Site::ShiftOperand);
            sites(l, out);
        }
        N::Neg(e) | N::Not(e) => sites(e, out),
        N::Ite { l, r, .. } => {
            out.insert(Site::IteBranch);
            sites(l, out);
            sites(r, out);
        }
        N::Match { arms, .. } => {
            out.insert(Site::MatchArm);
            arms.iter().for_each(|a| sites(a, out));
        }
        N::Cast { e, .. } => {
            out.insert(Site::CastOperand);
            sites(e, out);
        }
        N::CastLie { e, .. } => {
            out.insert(Site::CastFromLie);
            sites(e, out);
        }
        N::Wrap { l, r, .. } => {
            out.insert(Site::WrappingOperand);
            sites(l, out);
            sites(r, out);
        }
        N::Let { value, .. } => {
            out.insert(Site::LetDeclared);
            sites(value, out);
        }
        N::Call { arg, sig, .. } => {
            out.insert(Site::CallArgument);
            out.insert(Site::SpecFnResult);
            if sig.inline {
                out.insert(Site::InlineCallArgument);
            }
            sites(arg, out);
        }
        N::Elem { elems, .. } => {
            out.insert(Site::SeqElement);
            elems.iter().for_each(|e| sites(e, out));
        }
        N::LitLie { .. } => {
            out.insert(Site::DeclaredLiteral);
        }
        N::Count { n, .. } => {
            out.insert(Site::CollectionCount);
            sites(n, out);
        }
        N::CountCall { n, .. } => {
            out.insert(Site::CollectionCount);
            out.insert(Site::CallArgument);
            out.insert(Site::SpecFnResult);
            sites(n, out);
        }
        N::ElemVia { elems, .. } => {
            out.insert(Site::SeqElement);
            out.insert(Site::ElementReceiver);
            elems.iter().for_each(|e| sites(e, out));
        }
    }
}

// ---------------------------------------------------------------------------
// Typed-seam rendering.
// ---------------------------------------------------------------------------

const PLACEHOLDER: TrustVcType = TrustVcType::Int { width: 32 };

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
fn fn_name(f: usize) -> String {
    format!("of{f}")
}
fn seq_empty_name(et: T) -> String {
    format!("__trust_vc_collection_ctor_Seq_{}_empty", et.rust())
}

fn to_ir(n: &N, chooses: &mut usize) -> TrustVcExpr {
    match n {
        N::Var { name, ty, .. } => var(name, ty.ir()),
        N::Lit { value, ty } => lit(*value, ty.ir()),
        N::NegLit { mag, ty } => TrustVcExpr::Neg(Box::new(lit(*mag, ty.ir()))),
        N::Untyped { value } => lit(*value, PLACEHOLDER),
        N::Const { t, max } => TrustVcExpr::IntConst {
            ty: t.ir(),
            kind: if *max {
                IntConstKind::Max
            } else {
                IntConstKind::Min
            },
        },
        N::Arith { op, l, r, decl } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(to_ir(l, chooses)),
            right: Box::new(to_ir(r, chooses)),
            ty: decl.ir(),
        },
        N::Bit { op, l, r, decl } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(to_ir(l, chooses)),
            right: Box::new(to_ir(r, chooses)),
            ty: decl.ir(),
        },
        N::Neg(e) => TrustVcExpr::Neg(Box::new(to_ir(e, chooses))),
        N::Not(e) => TrustVcExpr::Not(Box::new(to_ir(e, chooses))),
        N::Ite {
            cname, l, r, decl, ..
        } => TrustVcExpr::Ite {
            cond: Box::new(var(cname, TrustVcType::Bool)),
            then_branch: Box::new(to_ir(l, chooses)),
            else_branch: Box::new(to_ir(r, chooses)),
            ty: decl.ir(),
        },
        N::Match {
            sname,
            arms,
            guard,
            decl,
            ..
        } => {
            let last = arms.len() - 1;
            let u8t = U8.ir();
            TrustVcExpr::Match {
                scrutinee: Box::new(var(sname, u8t.clone())),
                arms: arms
                    .iter()
                    .enumerate()
                    .map(|(k, a)| {
                        let body = to_ir(a, chooses);
                        if k == last {
                            MatchArm::new(MatchPattern::Wildcard, body)
                        } else if *guard && k == 1 {
                            let mut arm = MatchArm::new(MatchPattern::Ident("g".to_string()), body);
                            arm.guard = Some(cmp(
                                CompareOp::Eq,
                                var("g", u8t.clone()),
                                lit(1, u8t.clone()),
                            ));
                            arm
                        } else {
                            MatchArm::new(
                                MatchPattern::Lit(lit(i128::try_from(k).unwrap_or(0), u8t.clone())),
                                body,
                            )
                        }
                    })
                    .collect(),
                ty: decl.ir(),
            }
        }
        N::Cast { e, to } => TrustVcExpr::Cast {
            expr: Box::new(to_ir(e, chooses)),
            from_ty: ty(e).ir(),
            to_ty: to.ir(),
        },
        N::CastLie { e, from, to } => TrustVcExpr::Cast {
            expr: Box::new(to_ir(e, chooses)),
            from_ty: from.ir(),
            to_ty: to.ir(),
        },
        N::Shift { shl, l, k, kt } => TrustVcExpr::SpecialArith {
            op: if *shl {
                SpecialArithOp::Shl
            } else {
                SpecialArithOp::Shr
            },
            left: Box::new(to_ir(l, chooses)),
            right: Box::new(lit(*k, kt.ir())),
            ty: ty(l).ir(),
        },
        N::Wrap { mode, op, l, r, t } => TrustVcExpr::WrappingArith {
            mode: match mode {
                WMode::Wrapping => WrappingMode::Wrapping,
                WMode::Saturating => WrappingMode::Saturating,
            },
            op: *op,
            left: Box::new(to_ir(l, chooses)),
            right: Box::new(to_ir(r, chooses)),
            ty: t.ir(),
        },
        N::Let { name, decl, value } => TrustVcExpr::Let {
            name: name.clone(),
            ty: decl.ir(),
            value: Box::new(to_ir(value, chooses)),
            body: Box::new(var(name, decl.ir())),
        },
        N::Call { f, sig, arg } => TrustVcExpr::FnCall {
            name: fn_name(*f),
            args: vec![to_ir(arg, chooses)],
            return_ty: sig.result.ir(),
        },
        N::Len { sname, .. } => TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver: Box::new(var(sname, TrustVcType::Seq(Box::new(U8.ir())))),
            receiver_name: Some(sname.clone()),
            args: vec![],
            ty: TrustVcType::Uint { width: 64 },
        },
        N::Elem { elems, idx, et } => {
            let empty = seq_empty_name(*et);
            let seq_ty = TrustVcType::Seq(Box::new(et.ir()));
            let mut seq = TrustVcExpr::FnCall {
                name: empty.clone(),
                args: vec![],
                return_ty: seq_ty.clone(),
            };
            for e in elems {
                seq = TrustVcExpr::CollectionOp {
                    op: CollectionOp::Push,
                    receiver: Box::new(seq),
                    receiver_name: Some(empty.clone()),
                    args: vec![to_ir(e, chooses)],
                    ty: seq_ty.clone(),
                };
            }
            TrustVcExpr::Index {
                receiver: Box::new(seq),
                index: Box::new(lit(i128::try_from(*idx).unwrap_or(0), PLACEHOLDER)),
                receiver_name: Some(empty),
                elem_ty: et.ir(),
            }
        }
        N::LitLie { value, ty } => lit(*value, ty.ir()),
        N::Count { sname, n, take, .. } => seam_count(sname, to_ir(n, chooses), *take),
        N::CountCall { f, sname, n, .. } => TrustVcExpr::FnCall {
            name: count_fn_name(*f),
            args: vec![seq_u8_var(sname), to_ir(n, chooses)],
            return_ty: TrustVcType::MathInt,
        },
        N::ElemVia {
            elems,
            idx,
            et,
            links,
            read,
        } => {
            let empty = seq_empty_name(*et);
            let seq_of = |t: T| TrustVcType::Seq(Box::new(t.ir()));
            let mut seq = TrustVcExpr::FnCall {
                name: empty.clone(),
                args: vec![],
                return_ty: seq_of(*et),
            };
            for e in elems {
                seq = TrustVcExpr::CollectionOp {
                    op: CollectionOp::Push,
                    receiver: Box::new(seq),
                    receiver_name: Some(empty.clone()),
                    args: vec![to_ir(e, chooses)],
                    ty: seq_of(*et),
                };
            }
            let mut len = elems.len();
            for (k, (link, t)) in links.iter().enumerate() {
                seq = match link {
                    Link::TakeAll => TrustVcExpr::CollectionOp {
                        op: CollectionOp::Take,
                        receiver: Box::new(seq),
                        receiver_name: Some(empty.clone()),
                        args: vec![lit(i128::try_from(len).unwrap_or(0), TrustVcType::MathInt)],
                        ty: seq_of(*t),
                    },
                    Link::Push => {
                        len += 1;
                        TrustVcExpr::CollectionOp {
                            op: CollectionOp::Push,
                            receiver: Box::new(seq),
                            receiver_name: Some(empty.clone()),
                            args: vec![lit(0, et.ir())],
                            ty: seq_of(*t),
                        }
                    }
                    Link::Let => {
                        let name = format!("r{k}");
                        TrustVcExpr::Let {
                            name: name.clone(),
                            ty: seq_of(*t),
                            value: Box::new(seq),
                            body: Box::new(var(&name, seq_of(*t))),
                        }
                    }
                    Link::Ite => TrustVcExpr::Ite {
                        cond: Box::new(TrustVcExpr::BoolLit(true)),
                        then_branch: Box::new(seq.clone()),
                        else_branch: Box::new(seq),
                        ty: seq_of(*t),
                    },
                };
            }
            TrustVcExpr::Index {
                receiver: Box::new(seq),
                index: Box::new(lit(i128::try_from(*idx).unwrap_or(0), PLACEHOLDER)),
                receiver_name: Some(empty),
                elem_ty: read.ir(),
            }
        }
        N::Choose { t, value } => {
            *chooses += 1;
            let name = format!("q{chooses}");
            TrustVcExpr::Choose {
                var_name: name.clone(),
                var_ty: t.ir(),
                condition: Box::new(cmp(CompareOp::Eq, var(&name, t.ir()), lit(*value, t.ir()))),
                key: format!("oracle_choose_{chooses}"),
                also_assert: None,
            }
        }
    }
}

fn count_fn_name(f: usize) -> String {
    format!("oc{f}")
}
fn seq_u8_var(name: &str) -> TrustVcExpr {
    var(name, TrustVcType::Seq(Box::new(U8.ir())))
}
/// `s.take(n).len()` / `s.skip(n).len()` of the `Seq<u8>` `s` (seam IR).
fn seam_count(sname: &str, n: TrustVcExpr, take: bool) -> TrustVcExpr {
    let seq = TrustVcType::Seq(Box::new(U8.ir()));
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(TrustVcExpr::CollectionOp {
            op: if take {
                CollectionOp::Take
            } else {
                CollectionOp::Skip
            },
            receiver: Box::new(var(sname, seq.clone())),
            receiver_name: Some(sname.to_string()),
            args: vec![n],
            ty: seq,
        }),
        receiver_name: Some(sname.to_string()),
        args: vec![],
        ty: TrustVcType::Uint { width: 64 },
    }
}
/// The defining axiom `forall s, m. ocK(s, m) == s.take(m).len()` of a
/// typed-seam count-wrapping spec fn.
fn seam_count_axiom(f: usize, cf: CountFn) -> TrustVcExpr {
    let seq = TrustVcType::Seq(Box::new(U8.ir()));
    let call = TrustVcExpr::FnCall {
        name: count_fn_name(f),
        args: vec![seq_u8_var("s"), var("m", cf.nty.ir())],
        return_ty: TrustVcType::MathInt,
    };
    let body = TrustVcExpr::Cast {
        expr: Box::new(seam_count("s", var("m", cf.nty.ir()), cf.take)),
        from_ty: TrustVcType::Uint { width: 64 },
        to_ty: TrustVcType::MathInt,
    };
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("s".to_string(), seq), ("m".to_string(), cf.nty.ir())],
        body: Box::new(cmp(CompareOp::Eq, call.clone(), body)),
        triggers: Some(vec![vec![call]]),
        trigger_inference_mode: None,
    }
}

/// The defining axiom `forall p. fK(p) == body` of a typed-seam spec fn.
fn seam_axiom(f: usize, sig: SpecFn) -> TrustVcExpr {
    let (call, equation) = seam_equation(f, sig);
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("p".to_string(), sig.param.ir())],
        body: Box::new(equation),
        triggers: Some(vec![vec![call]]),
        trigger_inference_mode: None,
    }
}

/// The call `fK(p)` and the defining equation `fK(p) == body` over the free
/// parameter `p` (an INLINE function's body axiom states it bare).
fn seam_equation(f: usize, sig: SpecFn) -> (TrustVcExpr, TrustVcExpr) {
    let p = var("p", sig.param.ir());
    let as_result = |e: TrustVcExpr| -> TrustVcExpr {
        if sig.result == sig.param {
            e
        } else {
            TrustVcExpr::Cast {
                expr: Box::new(e),
                from_ty: sig.param.ir(),
                to_ty: sig.result.ir(),
            }
        }
    };
    let body = if sig.plus_one {
        match (sig.result, sig.param) {
            (Ty::F(t), Ty::F(_)) => TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(p.clone()),
                right: Box::new(lit(1, t.ir())),
                ty: t.ir(),
            },
            _ => TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(as_result(p.clone())),
                right: Box::new(lit(1, TrustVcType::MathInt)),
                ty: TrustVcType::MathInt,
            },
        }
    } else {
        as_result(p.clone())
    };
    let call = TrustVcExpr::FnCall {
        name: fn_name(f),
        args: vec![p],
        return_ty: sig.result.ir(),
    };
    (call.clone(), cmp(CompareOp::Eq, call, body))
}

// ---------------------------------------------------------------------------
// Source rendering.
// ---------------------------------------------------------------------------

fn rust_lit(value: i128, ty: Ty) -> String {
    let suffix = match ty {
        // The oracle's `i32` literal is untyped: unsuffixed. A suffixed
        // `200i32` is an `i32` (§5b rule 7).
        Ty::F(I32) => String::new(),
        other => other.rust(),
    };
    format!("{value}{suffix}")
}

fn to_rust(n: &N, chooses: &mut usize) -> String {
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
                format!("(-{})", rust_lit(-*value, *ty))
            } else {
                rust_lit(*value, *ty)
            }
        }
        N::NegLit { mag, ty } => format!("(-{})", rust_lit(*mag, *ty)),
        N::Untyped { value } => {
            if *value < 0 {
                format!("(-{})", -*value)
            } else {
                format!("{value}")
            }
        }
        N::Const { t, max } => format!("{}::{}", t.rust(), if *max { "MAX" } else { "MIN" }),
        N::Arith { op, l, r, .. } => format!(
            "({} {} {})",
            to_rust(l, chooses),
            sym(*op),
            to_rust(r, chooses)
        ),
        N::Bit { op, l, r, .. } => {
            let s = match op {
                SpecialArithOp::BitAnd => "&",
                SpecialArithOp::BitOr => "|",
                _ => "^",
            };
            format!("({} {s} {})", to_rust(l, chooses), to_rust(r, chooses))
        }
        N::Neg(e) => format!("(-{})", to_rust(e, chooses)),
        N::Not(e) => format!("(!{})", to_rust(e, chooses)),
        N::Ite { cname, l, r, .. } => format!(
            "(if {cname} {{ {} }} else {{ {} }})",
            to_rust(l, chooses),
            to_rust(r, chooses)
        ),
        N::Match {
            sname, arms, guard, ..
        } => {
            let last = arms.len() - 1;
            let arms_src: Vec<String> = arms
                .iter()
                .enumerate()
                .map(|(k, a)| {
                    let body = to_rust(a, chooses);
                    if k == last {
                        format!("_ => {body}")
                    } else if *guard && k == 1 {
                        format!("g if g == 1 => {body}")
                    } else {
                        format!("{k} => {body}")
                    }
                })
                .collect();
            format!("(match {sname} {{ {} }})", arms_src.join(", "))
        }
        N::Cast { e, to } => format!("({} as {})", to_rust(e, chooses), to.rust()),
        N::Shift { shl, l, k, kt } => format!(
            "({} {} {k}{})",
            to_rust(l, chooses),
            if *shl { "<<" } else { ">>" },
            kt.rust()
        ),
        N::Wrap { mode, op, l, r, .. } => {
            let m = match (mode, op) {
                (WMode::Wrapping, ArithOp::Add) => "wrapping_add",
                (WMode::Wrapping, ArithOp::Sub) => "wrapping_sub",
                (WMode::Wrapping, _) => "wrapping_mul",
                (WMode::Saturating, ArithOp::Add) => "saturating_add",
                (WMode::Saturating, ArithOp::Sub) => "saturating_sub",
                (WMode::Saturating, _) => "saturating_mul",
            };
            format!("{}.{m}({})", to_rust(l, chooses), to_rust(r, chooses))
        }
        N::Let { .. } => unreachable!("a source `let` is rendered as a statement"),
        N::Call { f, arg, .. } => format!("{}({})", fn_name(*f), to_rust(arg, chooses)),
        N::Len { .. } => unreachable!("typed seam only"),
        N::Elem { elems, idx, .. } => format!(
            "seq![{}][{idx}]",
            elems
                .iter()
                .map(|e| to_rust(e, chooses))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        N::LitLie { .. } | N::ElemVia { .. } | N::CastLie { .. } => {
            unreachable!("typed seam only")
        }
        N::Count { sname, n, take, .. } => format!(
            "{sname}.{}({}).len()",
            if *take { "take" } else { "skip" },
            to_rust(n, chooses)
        ),
        N::CountCall { f, sname, n, .. } => {
            format!("{}({sname}, {})", count_fn_name(*f), to_rust(n, chooses))
        }
        N::Choose { t, value } => {
            *chooses += 1;
            format!(
                "trust_vc::choose!(|q{chooses}: {}| q{chooses} == {})",
                t.rust(),
                rust_lit_signed(*value, Ty::F(*t))
            )
        }
    }
}

fn rust_lit_signed(value: i128, ty: Ty) -> String {
    if value < 0 {
        format!("(-{})", rust_lit(-value, ty))
    } else {
        rust_lit(value, ty)
    }
}

fn source_count_fn(f: usize, cf: CountFn) -> String {
    format!(
        "#[trust_vc::spec]\nfn {}(s: Seq<u8>, n: {}) -> int {{\n    s.{}(n).len() as int\n}}\n\n",
        count_fn_name(f),
        cf.nty.rust(),
        if cf.take { "take" } else { "skip" }
    )
}

fn source_spec_fn(f: usize, sig: SpecFn) -> String {
    let body = if sig.plus_one { "p + 1" } else { "p" };
    format!(
        "#[trust_vc::spec]\nfn {}(p: {}) -> {} {{\n    {body}\n}}\n\n",
        fn_name(f),
        sig.param.rust(),
        sig.result.rust()
    )
}

// ---------------------------------------------------------------------------
// Verdicts and tallies.
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

/// What §5b says a goal is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Want {
    Verified,
    Refuted,
    /// A binding §5b refuses: must be `Unknown`.
    Refused,
    /// A contradiction over FREE variables (`g(x) != g(x)`): false under
    /// every reading, so it must never be `Verified` — a spec function's
    /// defining axiom that two instantiations read two ways proves it.
    NeverVerified,
}

#[derive(Default)]
struct Tally {
    total: usize,
    decided: usize,
    unknown: usize,
    skipped: usize,
    bad: Vec<String>,
    /// Decided cases per expression variant / binding site.
    variants: BTreeMap<&'static str, usize>,
    sites: BTreeMap<Site, usize>,
}
impl Tally {
    fn record(
        &mut self,
        want: Want,
        got: &VerifyResult,
        variants: &BTreeSet<&'static str>,
        sites: &BTreeSet<Site>,
        detail: &str,
    ) {
        self.total += 1;
        let g = verdict_of(got);
        let decided = match (want, g) {
            (Want::NeverVerified, Verdict::Verified) => {
                let line = format!("FALSE VERIFIED (a contradiction)|{detail}");
                println!("{line}");
                self.bad.push(line);
                false
            }
            (Want::NeverVerified, _) => true,
            (Want::Refused, Verdict::Unknown) => true,
            (Want::Refused, other) => {
                let raw: String = format!("{got:?}").chars().take(160).collect();
                let line = format!("RULE (refused binding decided {other:?})|{detail}|{raw}");
                println!("{line}");
                self.bad.push(line);
                false
            }
            (Want::Refuted, Verdict::NotProved) => true,
            (_, Verdict::Unknown | Verdict::NotProved) => {
                self.unknown += 1;
                if std::env::var_os("ORACLE_VERBOSE").is_some() {
                    let raw: String = format!("{got:?}").chars().take(200).collect();
                    println!("UNKNOWN|{detail}|{raw}");
                }
                false
            }
            (Want::Verified, Verdict::Verified) | (Want::Refuted, Verdict::Refuted) => true,
            (Want::Refuted, Verdict::Verified) => {
                let line = format!("FALSE VERIFIED|{detail}");
                println!("{line}");
                self.bad.push(line);
                false
            }
            (Want::Verified, _) => {
                let raw: String = format!("{got:?}").chars().take(200).collect();
                let line = format!("FALSE COUNTEREXAMPLE|{detail}|{raw}");
                println!("{line}");
                self.bad.push(line);
                false
            }
        };
        if decided {
            self.decided += 1;
            for v in variants {
                *self.variants.entry(v).or_default() += 1;
            }
            for s in sites {
                *self.sites.entry(*s).or_default() += 1;
            }
        }
    }
    fn finish(&self, name: &str) {
        println!(
            "SUMMARY {name}: total={} decided={} unknown={} skipped={} wrong={}",
            self.total,
            self.decided,
            self.unknown,
            self.skipped,
            self.bad.len()
        );
        println!("COVERAGE {name}: variants={:?}", self.variants);
        println!("COVERAGE {name}: sites={:?}", self.sites);
    }
    fn assert_clean(&self, name: &str) {
        assert!(
            self.bad.is_empty(),
            "{name}: {} wrong verdicts:\n{}",
            self.bad.len(),
            self.bad.join("\n")
        );
        assert!(self.decided > 0, "{name}: nothing decided");
    }
}

fn seed() -> u64 {
    std::env::var("ORACLE_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x06_ac1e_0924)
}
fn cases() -> usize {
    std::env::var("ORACLE_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64)
}

/// The integer-role variants the oracle must generate and decide.
fn required_variants() -> BTreeSet<&'static str> {
    EXPR_VARIANTS
        .iter()
        .filter(|(name, roles)| {
            roles.iter().any(|r| *r != IntegerRole::None)
                && !EXEMPT.iter().any(|(exempt, _)| exempt == name)
        })
        .map(|(name, _)| *name)
        .collect()
}

/// Map a generated tree onto the IR variant names it exercises (the source
/// frontend's lowered IR is not observable here).
fn tree_variants(n: &N, out: &mut BTreeSet<&'static str>) {
    let mut add = |v: &'static str| {
        out.insert(v);
    };
    match n {
        N::Var { .. } => add("Var"),
        N::Lit { .. } | N::Untyped { .. } => add("IntLit"),
        N::NegLit { .. } => {
            add("Neg");
            add("IntLit");
        }
        N::Const { .. } => add("IntConst"),
        N::Choose { .. } => add("Choose"),
        N::Len { .. } => {
            add("CollectionOp");
        }
        N::Arith { .. } => add("Arith"),
        N::Bit { .. } | N::Shift { .. } => add("SpecialArith"),
        N::Neg(_) => add("Neg"),
        N::Not(_) => add("Not"),
        N::Ite { .. } => add("Ite"),
        N::Match { .. } => add("Match"),
        N::Cast { .. } | N::CastLie { .. } => add("Cast"),
        N::Wrap { .. } => add("WrappingArith"),
        N::Let { .. } => add("Let"),
        N::Call { .. } => add("FnCall"),
        N::Elem { .. } => {
            add("Index");
            add("CollectionOp");
            add("FnCall");
        }
        N::LitLie { .. } => add("IntLit"),
        N::Count { .. } => add("CollectionOp"),
        N::CountCall { .. } => add("FnCall"),
        N::ElemVia { links, .. } => {
            add("Index");
            add("CollectionOp");
            add("FnCall");
            for (link, _) in links {
                match link {
                    Link::Let => add("Let"),
                    Link::Ite => add("Ite"),
                    Link::TakeAll | Link::Push => {}
                }
            }
        }
    }
    match n {
        N::Arith { l, r, .. }
        | N::Bit { l, r, .. }
        | N::Ite { l, r, .. }
        | N::Wrap { l, r, .. } => {
            tree_variants(l, out);
            tree_variants(r, out);
        }
        N::Shift { l: e, .. }
        | N::Neg(e)
        | N::Not(e)
        | N::Cast { e, .. }
        | N::CastLie { e, .. } => tree_variants(e, out),
        N::Let { value: e, .. } | N::Call { arg: e, .. } => tree_variants(e, out),
        N::Count { n: e, .. } | N::CountCall { n: e, .. } => tree_variants(e, out),
        N::Match { arms, .. } => arms.iter().for_each(|a| tree_variants(a, out)),
        N::Elem { elems, .. } | N::ElemVia { elems, .. } => {
            elems.iter().for_each(|a| tree_variants(a, out));
        }
        _ => {}
    }
}

/// The expected verdict of `tree cmp z` in a context that does (`checked`)
/// or does not check overflow; `None` when the case is outside the oracle.
fn want_of(tree_value: Val, z: i128, cop: CompareOp, checked: bool) -> Option<Want> {
    Some(match tree_value {
        Val::Refused => Want::Refused,
        Val::V(v, overflow) => {
            if (checked && overflow) || !holds(cop, v, z) {
                Want::Refuted
            } else {
                Want::Verified
            }
        }
        // An unspecified `nat`: a comparison some `nat` falsifies is never
        // `Verified` (its refutation, and the precondition trust-vc checks
        // where Verus only recommends, are both fine); one EVERY `nat`
        // satisfies (`>= 0`) is left undecided by the oracle.
        Val::Unspecified => {
            let valid_for_every_nat = match cop {
                CompareOp::Ne | CompareOp::Gt => z < 0,
                CompareOp::Ge => z <= 0,
                _ => false,
            };
            if valid_for_every_nat {
                return None;
            }
            Want::NeverVerified
        }
    })
}

// ---------------------------------------------------------------------------
// Typed seam.
// ---------------------------------------------------------------------------

struct SeamOutcome {
    tally: Tally,
    generated: BTreeSet<&'static str>,
}

fn run_seam(factor: usize, salt: u64) -> SeamOutcome {
    let mut rng = Rng(seed() ^ salt);
    let mut tally = Tally::default();
    let mut generated = BTreeSet::new();
    for _ in 0..cases() * factor {
        let mut g = Gen {
            rng: &mut rng,
            front: Front::Seam,
            ghost: true,
            pins: Vec::new(),
            bools: Vec::new(),
            selectors: Vec::new(),
            seqs: Vec::new(),
            fns: Vec::new(),
            count_fns: Vec::new(),
            fn_base: 0,
            exec_code: false,
            chooses: 0,
        };
        let tree = if g.rng.below(6) == 0 {
            g.count()
        } else {
            g.node(3, false)
        };
        let z = g.peer(&tree);
        let cop = g.rng.pick(&OPS);
        let (exec, assert) = (g.rng.coin(), g.rng.coin());
        let (Some(value), Some(Val::V(zv, _))) = (eval(&tree), eval(&z)) else {
            tally.skipped += 1;
            continue;
        };
        let Some(want) = want_of(value, zv, cop, exec && assert) else {
            tally.skipped += 1;
            continue;
        };
        let mut chooses = 0usize;
        let goal = cmp(cop, to_ir(&tree, &mut chooses), to_ir(&z, &mut chooses));
        let variants: BTreeSet<&'static str> = expr_variants_in(&goal).into_iter().collect();
        for v in &variants {
            generated.insert(*v);
        }
        let mut site_set = BTreeSet::new();
        sites(&tree, &mut site_set);
        site_set.insert(Site::CompareOperand);

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
        variables.extend(
            g.selectors
                .iter()
                .map(|(n, _)| VariableDecl::new(n.clone(), U8.ir())),
        );
        variables.extend(
            g.seqs
                .iter()
                .map(|(n, _)| VariableDecl::new(n.clone(), TrustVcType::Seq(Box::new(U8.ir())))),
        );
        variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
        let mut obligations: Vec<TypedProofObligation> = Vec::new();
        for (i, (n, t, v)) in g.pins.iter().enumerate() {
            obligations.push(TypedProofObligation::requires(
                format!("o_requires_{i}"),
                cmp(CompareOp::Eq, var(n, t.ir()), lit(*v, t.ir())),
            ));
        }
        for (i, (n, c)) in g.bools.iter().enumerate() {
            let v = var(n, TrustVcType::Bool);
            obligations.push(TypedProofObligation::requires(
                format!("o_requires_b{i}"),
                if *c { v } else { TrustVcExpr::Not(Box::new(v)) },
            ));
        }
        for (i, (n, v)) in g.selectors.iter().enumerate() {
            obligations.push(TypedProofObligation::requires(
                format!("o_requires_m{i}"),
                cmp(CompareOp::Eq, var(n, U8.ir()), lit(*v, U8.ir())),
            ));
        }
        for (i, (n, len)) in g.seqs.iter().enumerate() {
            let u64t = TrustVcType::Uint { width: 64 };
            obligations.push(TypedProofObligation::requires(
                format!("o_requires_s{i}"),
                cmp(
                    CompareOp::Eq,
                    TrustVcExpr::CollectionOp {
                        op: CollectionOp::Len,
                        receiver: Box::new(var(n, TrustVcType::Seq(Box::new(U8.ir())))),
                        receiver_name: Some(n.clone()),
                        args: vec![],
                        ty: u64t.clone(),
                    },
                    lit(*len, u64t),
                ),
            ));
        }
        for (f, sig) in g.fns.iter().enumerate().filter(|(_, sig)| !sig.inline) {
            obligations.push(TypedProofObligation::requires(
                format!("o_axiom_{f}"),
                seam_axiom(f, *sig),
            ));
        }
        for (f, cf) in &g.count_fns {
            obligations.push(TypedProofObligation::requires(
                format!("o_count_axiom_{f}"),
                seam_count_axiom(*f, *cf),
            ));
        }
        let goal_obligation = if assert {
            TypedProofObligation::assert("o_goal", goal)
        } else {
            TypedProofObligation::ensures("o_ensures_0", goal)
        };
        obligations.push(goal_obligation);
        let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
        for (f, sig) in g.fns.iter().enumerate() {
            ctx.declare_helper_function_typed(
                &fn_name(f),
                sig.result.ir(),
                vec![("p".to_string(), sig.param.ir())],
            );
            // An INLINE function's body axiom: substituted at each call,
            // its argument bound at `p`'s type first.
            if sig.inline {
                ctx.push_obligation(
                    ProofObligation::new_typed(
                        format!("__body_axiom_{}", fn_name(f)),
                        seam_equation(f, *sig).1,
                        ObligationKind::BroadcastAssume,
                    )
                    .with_bound_vars(vec!["p".to_string()])
                    .with_inline(true),
                );
            }
        }
        for (f, cf) in &g.count_fns {
            ctx.declare_helper_function_typed(
                &count_fn_name(*f),
                TrustVcType::MathInt,
                vec![
                    ("s".to_string(), TrustVcType::Seq(Box::new(U8.ir()))),
                    ("m".to_string(), cf.nty.ir()),
                ],
            );
        }
        if exec {
            ctx.enable_overflow_checks();
        }
        let started = std::time::Instant::now();
        let got = ctx.verify();
        println!(
            "CASE|seam|{}|{:?}|{}ms",
            tally.total,
            verdict_of(&got),
            started.elapsed().as_millis()
        );
        let mut ch = 0usize;
        let detail = format!(
            "SEAM {} {} {} [value {value:?} ty {:?}; peer {zv}:{:?}] exec={exec} assert={assert} pins={:?} bools={:?} sel={:?} seqs={:?} fns={:?} count_fns={:?} tree={tree:?}",
            to_rust_or_ir(&tree, &mut ch),
            rust_cmp(cop),
            to_rust_or_ir(&z, &mut ch),
            ty(&tree),
            ty(&z),
            g.pins,
            g.bools,
            g.selectors,
            g.seqs,
            g.fns,
            g.count_fns
        );
        tally.record(want, &got, &variants, &site_set, &detail);
    }
    SeamOutcome { tally, generated }
}

/// A readable rendering for a failure line (`Let`/`Len` are seam-only).
fn to_rust_or_ir(n: &N, chooses: &mut usize) -> String {
    let mut plain = true;
    let mut check = |m: &N| {
        if matches!(
            m,
            N::Let { .. }
                | N::Len { .. }
                | N::LitLie { .. }
                | N::ElemVia { .. }
                | N::CastLie { .. }
        ) {
            plain = false;
        }
    };
    fn walk(n: &N, f: &mut dyn FnMut(&N)) {
        f(n);
        match n {
            N::Arith { l, r, .. }
            | N::Bit { l, r, .. }
            | N::Ite { l, r, .. }
            | N::Wrap { l, r, .. } => {
                walk(l, f);
                walk(r, f);
            }
            N::Shift { l: e, .. }
            | N::Neg(e)
            | N::Not(e)
            | N::Cast { e, .. }
            | N::CastLie { e, .. } => walk(e, f),
            N::Let { value: e, .. } | N::Call { arg: e, .. } => walk(e, f),
            N::Count { n: e, .. } | N::CountCall { n: e, .. } => walk(e, f),
            N::Match { arms, .. } => arms.iter().for_each(|a| walk(a, f)),
            N::Elem { elems, .. } | N::ElemVia { elems, .. } => {
                elems.iter().for_each(|a| walk(a, f));
            }
            _ => {}
        }
    }
    walk(n, &mut check);
    if plain {
        to_rust(n, chooses)
    } else {
        "<seam-only tree>".to_string()
    }
}

/// The typed seam, every construct, exec and non-exec, asserting coverage.
#[test]
fn oracle_typed_seam() {
    let out = run_seam(4, 0x5EA);
    out.tally.finish("typed_seam");
    out.tally.assert_clean("typed_seam");
    let missing: Vec<&str> = required_variants()
        .into_iter()
        .filter(|v| out.tally.variants.get(v).copied().unwrap_or(0) == 0)
        .collect();
    assert!(
        missing.is_empty(),
        "typed seam: integer-role variants never DECIDED: {missing:?} (generated {:?})",
        out.generated
    );
    let missing_sites: Vec<Site> = ALL_SITES
        .iter()
        .copied()
        .filter(|s| frontends(*s) != Frontends::SourceOnly)
        .filter(|s| out.tally.sites.get(s).copied().unwrap_or(0) == 0)
        .collect();
    assert!(
        missing_sites.is_empty(),
        "typed seam: binding sites never DECIDED: {missing_sites:?}"
    );
}

/// COVERAGE, without a solver: the generator produces every integer-role
/// variant of `TrustVcExpr` (derived from the IR enum inside trust-vc-core)
/// and every binding site. A new integer-role variant fails here until the
/// generator produces it, or it is exempted with its reason.
#[test]
fn every_integer_role_variant_is_generated() {
    for (exempt, reason) in EXEMPT {
        let roles = EXPR_VARIANTS
            .iter()
            .find(|(name, _)| name == exempt)
            .map(|(_, roles)| *roles)
            .unwrap_or_else(|| panic!("EXEMPT names `{exempt}`, which is no variant"));
        assert!(
            roles.iter().any(|r| *r != IntegerRole::None),
            "EXEMPT names `{exempt}`, which has no integer role ({reason})"
        );
    }
    let mut rng = Rng(seed() ^ 0xC0);
    let mut generated = BTreeSet::new();
    let mut site_set = BTreeSet::new();
    for _ in 0..4000 {
        let mut g = Gen {
            rng: &mut rng,
            front: Front::Seam,
            ghost: true,
            pins: Vec::new(),
            bools: Vec::new(),
            selectors: Vec::new(),
            seqs: Vec::new(),
            fns: Vec::new(),
            count_fns: Vec::new(),
            fn_base: 0,
            exec_code: false,
            chooses: 0,
        };
        let tree = if g.rng.below(6) == 0 {
            g.count()
        } else {
            g.node(3, false)
        };
        let mut chooses = 0;
        let goal = cmp(CompareOp::Eq, to_ir(&tree, &mut chooses), lit(0, U8.ir()));
        generated.extend(expr_variants_in(&goal));
        sites(&tree, &mut site_set);
    }
    let missing: Vec<&str> = required_variants()
        .into_iter()
        .filter(|v| !generated.contains(v))
        .collect();
    assert!(
        missing.is_empty(),
        "integer-role variants the oracle never generates: {missing:?}"
    );
    // Every tree meets its comparison peer: `CompareOperand` is the goal's.
    site_set.insert(Site::CompareOperand);
    let missing_sites: Vec<Site> = ALL_SITES
        .iter()
        .copied()
        .filter(|s| frontends(*s) != Frontends::SourceOnly && !site_set.contains(s))
        .collect();
    assert!(
        missing_sites.is_empty(),
        "binding sites the oracle never generates: {missing_sites:?}"
    );
}

// ---------------------------------------------------------------------------
// Source frontend (`verify_function_from_file`, Verus-style clauses).
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SrcMode {
    /// `#[ensures(tree cmp z)]` on an exec fn: its arithmetic is
    /// overflow-checked.
    EnsuresExec,
    /// The same on a `#[trust_vc::proof]` fn.
    EnsuresProof,
    /// `let v[: T] = tree; assert!(v cmp z);` in an exec fn body (exec code:
    /// checked).
    BodyExec,
    /// The same in a proof fn body.
    BodyProof,
    /// `tree cmp z` as a `#[trust_vc::spec] fn -> bool` body.
    SpecBool,
    /// `tree` as a `#[trust_vc::spec]` fn body returning its type or `int`
    /// (the spec-fn RESULT binding; an `int` result is exact, rule 8).
    SpecValue,
}

enum_with_all! {
/// How a body-mode case binds its tree before asserting on it: a `let`
/// (declared or inferred) or a WRITE into a typed slot (§5b rule 12). Every
/// variant is generated in turn (`ALL_BINDS`), and [`Bind::site`] names the
/// binding site each one exercises.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bind, all = ALL_BINDS {
    /// `let v[: T] = tree;`
    Let,
    /// `let mut v: T = 0; v = tree;`
    Assign,
    /// `let mut v: T = 0; v += tree;` (`0 + tree` is `tree` in every type)
    CompoundAssign,
    /// `let v: T; v = tree;`
    Deferred,
    /// `let mut v: T = 0; let r = &mut v; *r = tree;`
    DerefWrite,
    /// `let mut v = w; let r = &mut v; *r = tree;` with a parameter `w: T`
    InferredDeref,
    /// `let mut t: (T, T) = (0, 0); t.0 = tree;` (the assertion reads `t.0`)
    FieldWrite,
    /// `let mut s = W { f: 0 }; s.f = tree;` with `struct W { f: T }`
    StructField,
    /// `p.0 = tree;` to a parameter `mut p: (T, T)`
    ParamField,
    /// `let mut s = W { f: 0 }; let r = &mut s.f; *r = tree;` (the assertion
    /// reads `*r`)
    FieldAlias,
    /// `let mut c: Vec<T> = vec![w]; let r = &mut c[0]; *r = tree;` with a
    /// parameter `w: T` (the assertion reads `*r`; exec bodies only)
    CellAlias,
    /// `let mut v = w; v = tree;` with a parameter `w: T`
    Inferred,
    /// `let mut v = e[0]; v = tree;` with a parameter `e: Seq<T>`
    ElementWitness,
    /// `let mut v; v = e[0]; v = tree;` with a parameter `e: Seq<T>`
    DeferredWitness,
    /// `if let Some(mut v) = o { v = tree; assert!(..) }` with `o: Option<T>`
    IfLet,
    /// `match o { Some(mut v) => { v = tree; assert!(..) } None => {} }`
    MatchPayload,
    /// `let w = tree; let r = &w; let v: T = *r;`
    BorrowRead,
    /// `let w = tree; let f = || w; let v: T = f();` (exec bodies only)
    CaptureRead,
    /// `let w = tree; let v: T = w;`
    BindingCopy,
    /// `let v: T = pass_T(tree);` with `fn pass_T(x: T) -> T { x }` (exec
    /// bodies only)
    ExecCall,
    /// `let w = tree; let v: T = w.clone();`
    MethodCopy,
    /// `let f = |a| a; let v: T = f(tree);` (exec bodies only)
    ClosureCall,
    /// `let mut s = W { f: 0 }; let mut t: T = tree; let r = if b { &mut s.f
    /// } else { &mut s.f }; std::mem::swap(r, &mut t);` (the assertion reads
    /// `s.f`; exec bodies only; fail-closed)
    UntrackedSwap,
}
}
impl Bind {
    /// The binding site a case of this shape exercises.
    fn site(self) -> Site {
        match self {
            Bind::Let => Site::LetDeclared,
            Bind::Assign => Site::Assignment,
            Bind::CompoundAssign => Site::CompoundAssignment,
            Bind::Deferred => Site::DeferredBinding,
            Bind::DerefWrite => Site::DerefWrite,
            Bind::InferredDeref => Site::InferredDerefWrite,
            Bind::FieldWrite => Site::FieldWrite,
            Bind::StructField => Site::StructFieldWrite,
            Bind::ParamField => Site::ParamFieldWrite,
            Bind::FieldAlias => Site::FieldAliasWrite,
            Bind::CellAlias => Site::CellAliasWrite,
            Bind::Inferred => Site::InferredBinding,
            Bind::ElementWitness => Site::ElementWitnessBinding,
            Bind::DeferredWitness => Site::DeferredWitnessBinding,
            Bind::IfLet => Site::PatternBinding,
            Bind::MatchPayload => Site::MatchPayloadBinding,
            Bind::BorrowRead => Site::BorrowedBindingRead,
            Bind::CaptureRead => Site::CapturedBindingRead,
            Bind::BindingCopy => Site::BindingCopy,
            Bind::ExecCall => Site::ExecCallArgument,
            Bind::MethodCopy => Site::MethodResultBinding,
            Bind::ClosureCall => Site::ClosureParameter,
            Bind::UntrackedSwap => Site::UntrackedBorrowWrite,
        }
    }
    /// Whether the shape ends by binding its value with `let v: T = ..`.
    fn ends_in_declared_let(self) -> bool {
        match self {
            Bind::BorrowRead
            | Bind::CaptureRead
            | Bind::BindingCopy
            | Bind::ExecCall
            | Bind::MethodCopy
            | Bind::ClosureCall => true,
            Bind::Let
            | Bind::Assign
            | Bind::CompoundAssign
            | Bind::Deferred
            | Bind::DerefWrite
            | Bind::InferredDeref
            | Bind::FieldWrite
            | Bind::StructField
            | Bind::ParamField
            | Bind::FieldAlias
            | Bind::CellAlias
            | Bind::Inferred
            | Bind::ElementWitness
            | Bind::DeferredWitness
            | Bind::IfLet
            | Bind::MatchPayload
            | Bind::UntrackedSwap => false,
        }
    }

    /// Whether every case of the shape is refused by design: a write through
    /// a `&mut` the lane does not track poisons the place, so no case is
    /// DECIDED, and the oracle checks only that none is decided wrongly.
    fn fail_closed(self) -> bool {
        match self {
            Bind::UntrackedSwap => true,
            Bind::Let
            | Bind::Assign
            | Bind::CompoundAssign
            | Bind::Deferred
            | Bind::DerefWrite
            | Bind::InferredDeref
            | Bind::FieldWrite
            | Bind::StructField
            | Bind::ParamField
            | Bind::FieldAlias
            | Bind::CellAlias
            | Bind::Inferred
            | Bind::ElementWitness
            | Bind::DeferredWitness
            | Bind::IfLet
            | Bind::MatchPayload
            | Bind::BorrowRead
            | Bind::CaptureRead
            | Bind::BindingCopy
            | Bind::ExecCall
            | Bind::MethodCopy
            | Bind::ClosureCall => false,
        }
    }
    /// Whether the shape exists only in an exec body (a `Vec` cell borrowed
    /// `&mut`).
    fn exec_only(self) -> bool {
        match self {
            Bind::CellAlias
            | Bind::CaptureRead
            | Bind::ExecCall
            | Bind::ClosureCall
            | Bind::UntrackedSwap => true,
            Bind::Let
            | Bind::Assign
            | Bind::CompoundAssign
            | Bind::Deferred
            | Bind::DerefWrite
            | Bind::InferredDeref
            | Bind::FieldWrite
            | Bind::StructField
            | Bind::ParamField
            | Bind::FieldAlias
            | Bind::Inferred
            | Bind::ElementWitness
            | Bind::DeferredWitness
            | Bind::IfLet
            | Bind::MatchPayload
            | Bind::BorrowRead
            | Bind::BindingCopy
            | Bind::MethodCopy => false,
        }
    }
}

/// The binding shapes a body of `mode` takes in turn.
fn binds_of(mode: SrcMode) -> Vec<Bind> {
    ALL_BINDS
        .iter()
        .copied()
        .filter(|bind| mode == SrcMode::BodyExec || !bind.exec_only())
        .collect()
}

struct SrcCase {
    name: String,
    text: String,
    want: Want,
    variants: BTreeSet<&'static str>,
    sites: BTreeSet<Site>,
    detail: String,
}

fn source_cases(mode: SrcMode, salt: u64, count: usize) -> (Vec<SrcCase>, usize) {
    let mut rng = Rng(seed() ^ salt ^ ((mode as u64) << 8));
    let mut cs = Vec::new();
    let mut fn_count = 0usize;
    let mut skipped = 0usize;
    let mut index = 0usize;
    let mut produced = 0usize;
    // Body cases take the binding shapes IN TURN (`binds_of`), so every one
    // is generated at any case count of at least `ALL_BINDS.len()`.
    let mut bind_turn = 0usize;
    let ghost = !matches!(mode, SrcMode::EnsuresExec | SrcMode::BodyExec);
    while produced < count {
        index += 1;
        let mut g = Gen {
            rng: &mut rng,
            front: Front::Source,
            ghost,
            pins: Vec::new(),
            bools: Vec::new(),
            selectors: Vec::new(),
            seqs: Vec::new(),
            fns: Vec::new(),
            count_fns: Vec::new(),
            fn_base: fn_count,
            exec_code: mode == SrcMode::BodyExec,
            chooses: 0,
        };
        // A count out of its domain inside a spec function (an axiom) is a
        // goal the solver can only time out on (~4-5 min a case, measured),
        // so counts are one case in eight of the two proof modes, whose tree
        // is not itself a spec function's body (the seam decides its counts
        // in milliseconds and generates them one case in six).
        let counted =
            matches!(mode, SrcMode::EnsuresProof | SrcMode::BodyProof) && g.rng.below(8) == 0;
        let tree = if counted { g.count() } else { g.node(3, false) };
        let z = g.peer(&tree);
        let cop = g.rng.pick(&OPS);
        let body_mode = matches!(mode, SrcMode::BodyExec | SrcMode::BodyProof);
        // Body modes bind the tree with a `let`, declared or inferred (a
        // count's `len()` is a `nat` the oracle types `int`: inferred), or
        // WRITE it into a typed slot: an assignment, a write through `&mut`,
        // a field write, a write to an inferred or a pattern binding — each
        // binds the value at the slot's type exactly as a declared `let` does.
        let bind = if body_mode && !counted {
            let binds = binds_of(mode);
            binds[bind_turn % binds.len()]
        } else {
            Bind::Let
        };
        let let_decl = if body_mode && !counted && (bind != Bind::Let || g.rng.coin()) {
            Some(g.let_decl(&tree))
        } else {
            None
        };
        // One file in four imports a glob, which turns the declared-width
        // lane OFF: nothing may bind differently there.
        let glob = g.rng.below(4) == 0;
        let spec_result = if mode == SrcMode::SpecValue {
            match ty(&tree) {
                Ty::F(_) if g.rng.below(3) == 0 => Ty::Int,
                other => other,
            }
        } else {
            ty(&tree)
        };
        let value = if mode == SrcMode::SpecValue && spec_result == Ty::Int {
            eval_int_context(&tree)
        } else {
            eval(&tree)
        };
        let (Some(value), Some(Val::V(zv, _))) = (value, eval(&z)) else {
            skipped += 1;
            continue;
        };
        let value = match (value, let_decl) {
            (Val::V(v, o), Some(d)) => {
                // An exec call's argument is bound like any call argument
                // (§5b rule 11: a narrower fixed-width argument is widened).
                let widening_ok = bind == Bind::ExecCall;
                if binds(ty(&tree), v, is_untyped(&tree), d, widening_ok).is_none() {
                    Val::Refused
                } else {
                    Val::V(v, o)
                }
            }
            (other, _) => other,
        };
        let checked = matches!(mode, SrcMode::EnsuresExec | SrcMode::BodyExec);
        let Some(want) = want_of(value, zv, cop, checked) else {
            skipped += 1;
            continue;
        };
        let proof = !matches!(mode, SrcMode::EnsuresExec | SrcMode::BodyExec);
        let name = format!("case_{index}");
        let mut chooses = 0usize;
        let tree_src = to_rust(&tree, &mut chooses);
        let z_src = to_rust(&z, &mut chooses);

        let mut variants = BTreeSet::new();
        tree_variants(&tree, &mut variants);
        let mut site_set = BTreeSet::new();
        sites(&tree, &mut site_set);
        site_set.insert(Site::CompareOperand);
        if let_decl.is_some() {
            variants.insert("Let");
            site_set.insert(bind.site());
            // A shape that reads its value into `let v: T = ..` binds at a
            // declared type too.
            if bind.ends_in_declared_let() {
                site_set.insert(Site::LetDeclared);
            }
        }
        if glob {
            site_set.insert(Site::LaneOffFile);
        }
        if mode == SrcMode::SpecValue {
            variants.insert("FnCall");
            site_set.insert(Site::SpecFnResult);
        }
        let mut spec_fns = String::new();
        for (k, sig) in g.fns.iter().enumerate() {
            spec_fns.push_str(&source_spec_fn(fn_count + k, *sig));
        }
        for (f, cf) in &g.count_fns {
            spec_fns.push_str(&source_count_fn(*f, *cf));
        }
        fn_count += g.fns.len() + g.count_fns.len();

        let mut text = String::new();
        let mut params: Vec<String> = g
            .pins
            .iter()
            .map(|(n, t, _)| format!("{n}: {}", t.rust()))
            .collect();
        params.extend(g.bools.iter().map(|(n, _)| format!("{n}: bool")));
        params.extend(g.selectors.iter().map(|(n, _)| format!("{n}: u8")));
        params.extend(g.seqs.iter().map(|(n, _)| format!("{n}: Seq<u8>")));
        match (bind, let_decl) {
            (Bind::Inferred | Bind::InferredDeref | Bind::CellAlias, Some(d)) => {
                params.push(format!("w: {}", d.rust()));
            }
            (Bind::IfLet | Bind::MatchPayload, Some(d)) => {
                params.push(format!("o: Option<{}>", d.rust()));
            }
            (Bind::ParamField, Some(d)) => params.push(format!("mut p: ({0}, {0})", d.rust())),
            (Bind::ElementWitness | Bind::DeferredWitness, Some(d)) => {
                params.push(format!("e: Seq<{}>", d.rust()));
            }
            _ => {}
        }
        let args: Vec<String> = g
            .pins
            .iter()
            .map(|(n, _, _)| n.clone())
            .chain(g.bools.iter().map(|(n, _)| n.clone()))
            .chain(g.selectors.iter().map(|(n, _)| n.clone()))
            .chain(g.seqs.iter().map(|(n, _)| n.clone()))
            .collect();
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
        for (n, v) in &g.selectors {
            let _ = writeln!(text, "#[trust_vc::requires({n} == {v})]");
        }
        for (n, len) in &g.seqs {
            let _ = writeln!(text, "#[trust_vc::requires({n}.len() == {len})]");
        }
        if matches!(bind, Bind::ElementWitness | Bind::DeferredWitness) && let_decl.is_some() {
            let _ = writeln!(text, "#[trust_vc::requires(e.len() > 0)]");
        }
        let mut prelude = String::new();
        let body = match mode {
            SrcMode::EnsuresExec | SrcMode::EnsuresProof => {
                let _ = writeln!(
                    text,
                    "#[trust_vc::ensures({tree_src} {} {z_src})]",
                    rust_cmp(cop)
                );
                "{}".to_string()
            }
            SrcMode::BodyExec | SrcMode::BodyProof => {
                let _ = writeln!(text, "#[trust_vc::ensures(true)]");
                let decl = let_decl
                    .map(|d| format!(": {}", d.rust()))
                    .unwrap_or_default();
                let c = rust_cmp(cop);
                let assert_v = format!("trust_vc::assert!(v {c} {z_src});");
                let body = |lines: &[String]| {
                    let mut body = String::from("{\n");
                    for line in lines {
                        let _ = writeln!(body, "    {line}");
                    }
                    body.push('}');
                    body
                };
                let write = format!("v = {tree_src};");
                match (bind, let_decl) {
                    (Bind::Assign, Some(d)) => {
                        body(&[format!("let mut v: {} = 0;", d.rust()), write, assert_v])
                    }
                    (Bind::CompoundAssign, Some(d)) => body(&[
                        format!("let mut v: {} = 0;", d.rust()),
                        format!("v += {tree_src};"),
                        assert_v,
                    ]),
                    (Bind::Deferred, Some(d)) => {
                        body(&[format!("let v: {};", d.rust()), write, assert_v])
                    }
                    (Bind::DerefWrite, Some(d)) => body(&[
                        format!("let mut v: {} = 0;", d.rust()),
                        "let r = &mut v;".to_string(),
                        format!("*r = {tree_src};"),
                        assert_v,
                    ]),
                    (Bind::InferredDeref, Some(_)) => body(&[
                        "let mut v = w;".to_string(),
                        "let r = &mut v;".to_string(),
                        format!("*r = {tree_src};"),
                        assert_v,
                    ]),
                    (Bind::FieldWrite, Some(d)) => body(&[
                        format!("let mut t: ({0}, {0}) = (0, 0);", d.rust()),
                        format!("t.0 = {tree_src};"),
                        format!("trust_vc::assert!(t.0 {c} {z_src});"),
                    ]),
                    (Bind::StructField, Some(d)) => {
                        let _ = writeln!(prelude, "struct W {{\n    f: {},\n}}\n", d.rust());
                        body(&[
                            "let mut s = W { f: 0 };".to_string(),
                            format!("s.f = {tree_src};"),
                            format!("trust_vc::assert!(s.f {c} {z_src});"),
                        ])
                    }
                    (Bind::ParamField, Some(_)) => body(&[
                        format!("p.0 = {tree_src};"),
                        format!("trust_vc::assert!(p.0 {c} {z_src});"),
                    ]),
                    (Bind::FieldAlias, Some(d)) => {
                        let _ = writeln!(prelude, "struct W {{\n    f: {},\n}}\n", d.rust());
                        body(&[
                            "let mut s = W { f: 0 };".to_string(),
                            "let r = &mut s.f;".to_string(),
                            format!("*r = {tree_src};"),
                            format!("trust_vc::assert!(*r {c} {z_src});"),
                        ])
                    }
                    (Bind::CellAlias, Some(d)) => body(&[
                        format!("let mut c: Vec<{}> = vec![w];", d.rust()),
                        "let r = &mut c[0];".to_string(),
                        format!("*r = {tree_src};"),
                        format!("trust_vc::assert!(*r {c} {z_src});"),
                    ]),
                    (Bind::Inferred, Some(_)) => {
                        body(&["let mut v = w;".to_string(), write, assert_v])
                    }
                    (Bind::ElementWitness, Some(_)) => {
                        body(&["let mut v = e[0];".to_string(), write, assert_v])
                    }
                    (Bind::DeferredWitness, Some(_)) => body(&[
                        "let mut v;".to_string(),
                        "v = e[0];".to_string(),
                        write,
                        assert_v,
                    ]),
                    (Bind::IfLet, Some(_)) => body(&[
                        "if let Some(mut v) = o {".to_string(),
                        format!("    {write}"),
                        format!("    {assert_v}"),
                        "}".to_string(),
                    ]),
                    (Bind::MatchPayload, Some(_)) => body(&[
                        "match o {".to_string(),
                        "    Some(mut v) => {".to_string(),
                        format!("        {write}"),
                        format!("        {assert_v}"),
                        "    }".to_string(),
                        "    None => {}".to_string(),
                        "}".to_string(),
                    ]),
                    (Bind::BorrowRead, Some(d)) => body(&[
                        format!("let w = {tree_src};"),
                        "let r = &w;".to_string(),
                        format!("let v: {} = *r;", d.rust()),
                        assert_v,
                    ]),
                    (Bind::CaptureRead, Some(d)) => body(&[
                        format!("let w = {tree_src};"),
                        "let f = || w;".to_string(),
                        format!("let v: {} = f();", d.rust()),
                        assert_v,
                    ]),
                    (Bind::BindingCopy, Some(d)) => body(&[
                        format!("let w = {tree_src};"),
                        format!("let v: {} = w;", d.rust()),
                        assert_v,
                    ]),
                    (Bind::ExecCall, Some(d)) => {
                        let _ = writeln!(
                            prelude,
                            "fn pass_{name}(x: {0}) -> {0} {{\n    x\n}}\n",
                            d.rust()
                        );
                        body(&[
                            format!("let v: {} = pass_{name}({tree_src});", d.rust()),
                            assert_v,
                        ])
                    }
                    (Bind::MethodCopy, Some(d)) => body(&[
                        format!("let w = {tree_src};"),
                        format!("let v: {} = w.clone();", d.rust()),
                        assert_v,
                    ]),
                    (Bind::ClosureCall, Some(d)) => body(&[
                        "let f = |a| a;".to_string(),
                        format!("let v: {} = f({tree_src});", d.rust()),
                        assert_v,
                    ]),
                    (Bind::UntrackedSwap, Some(d)) => {
                        let _ = writeln!(prelude, "struct W {{\n    f: {},\n}}\n", d.rust());
                        body(&[
                            "let mut s = W { f: 0 };".to_string(),
                            format!("let mut t: {} = {tree_src};", d.rust()),
                            "let r = if s.f == 0 { &mut s.f } else { &mut s.f };".to_string(),
                            "std::mem::swap(r, &mut t);".to_string(),
                            format!("trust_vc::assert!(s.f {c} {z_src});"),
                        ])
                    }
                    _ => body(&[format!("let v{decl} = {tree_src};"), assert_v]),
                }
            }
            SrcMode::SpecBool => {
                let _ = writeln!(
                    prelude,
                    "#[trust_vc::spec]\nfn p_{name}({}) -> bool {{\n    {tree_src} {} {z_src}\n}}\n",
                    params.join(", "),
                    rust_cmp(cop)
                );
                let _ = writeln!(text, "#[trust_vc::ensures(p_{name}({}))]", args.join(", "));
                "{}".to_string()
            }
            SrcMode::SpecValue => {
                let _ = writeln!(
                    prelude,
                    "#[trust_vc::spec]\nfn g_{name}({}) -> {} {{\n    {tree_src}\n}}\n",
                    params.join(", "),
                    spec_result.rust()
                );
                let _ = writeln!(
                    text,
                    "#[trust_vc::ensures(g_{name}({}) {} {z_src})]",
                    args.join(", "),
                    rust_cmp(cop)
                );
                "{}".to_string()
            }
        };
        let _ = writeln!(text, "fn {name}({}) {body}\n", params.join(", "));
        let detail = format!(
            "SRC {mode:?} {name}: {tree_src} {} {z_src} [value {value:?} ty {:?} decl {let_decl:?} bind {bind:?} glob {glob} result {spec_result:?}; peer {zv}:{:?}] pins={:?} seqs={:?} fns={:?} count_fns={:?}",
            rust_cmp(cop),
            ty(&tree),
            ty(&z),
            g.pins,
            g.seqs,
            g.fns,
            g.count_fns
        );
        // The spec fn's definition must be CONSISTENT: over free
        // (unpinned) arguments, `p(..) && !p(..)` / `g(..) != g(..)` is a
        // contradiction. A definition two instantiations read two ways — the
        // f8f2e624 class, where a bare `i32` literal substituted for a
        // parameter was retyped by a peer of the body — proves it.
        let consistency = match mode {
            SrcMode::SpecBool => Some(format!("p_{name}({0}) && !p_{name}({0})", args.join(", "))),
            SrcMode::SpecValue if want != Want::Refused => {
                Some(format!("g_{name}({0}) != g_{name}({0})", args.join(", ")))
            }
            _ => None,
        };
        let file_prelude = if glob { GLOB_PRELUDE } else { PRELUDE };
        if let Some(goal) = consistency {
            let cname = format!("consistency_{name}");
            cs.push(SrcCase {
                name: cname.clone(),
                text: format!(
                    "{file_prelude}{spec_fns}{prelude}#[trust_vc::proof]\n#[trust_vc::ensures({goal})]\nfn {cname}({}) {{}}\n",
                    params.join(", ")
                ),
                want: Want::NeverVerified,
                variants: variants.clone(),
                sites: site_set.clone(),
                detail: format!("SRC {mode:?} {cname}: {goal} (free arguments)"),
            });
        }
        cs.push(SrcCase {
            name,
            text: format!("{file_prelude}{spec_fns}{prelude}{text}"),
            want,
            variants,
            sites: site_set,
            detail,
        });
        produced += 1;
        if body_mode && !counted {
            bind_turn += 1;
        }
    }
    (cs, skipped)
}

/// What every generated source file starts with (`seq!` and `Seq` resolve
/// through `trust_vc_types`, as in the collection tests).
const PRELUDE: &str = "use trust_vc_types::Seq;\n\n";
/// The same through a GLOB import, which turns the file's declared-width
/// lane off (`declared_width::FileTypeNames::enumerable`).
const GLOB_PRELUDE: &str = "use trust_vc_types::*;\n\n";

fn run_source(mode: SrcMode, count: usize) -> Tally {
    let (cs, skipped) = source_cases(mode, 0x50C, count);
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/integer_typing_oracle_src")
        .join(format!("{mode:?}_{:x}", seed()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let mut tally = Tally {
        skipped,
        ..Tally::default()
    };
    for c in &cs {
        // One file per case: its own spec functions only, so no case's
        // background axioms weigh on another's query.
        let path = dir.join(format!("{}.rs", c.name));
        std::fs::File::create(&path)
            .and_then(|mut f| f.write_all(c.text.as_bytes()))
            .expect("write source");
        let started = std::time::Instant::now();
        let got =
            verify_function_from_file(path.to_str().expect("utf-8"), &c.name).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            });
        println!(
            "CASE|{mode:?}|{}|{:?}|{}ms",
            c.name,
            verdict_of(&got),
            started.elapsed().as_millis()
        );
        tally.record(c.want, &got, &c.variants, &c.sites, &c.detail);
    }
    tally
}

fn source_mode(mode: SrcMode, required_sites: &[Site]) {
    let tally = run_source(mode, cases());
    let name = format!("source_{mode:?}");
    tally.finish(&name);
    tally.assert_clean(&name);
    let missing: Vec<Site> = required_sites
        .iter()
        .copied()
        .filter(|s| tally.sites.get(s).copied().unwrap_or(0) == 0)
        .collect();
    assert!(
        missing.is_empty(),
        "{name}: binding sites never DECIDED: {missing:?}"
    );
}

/// Sites every source mode must DECIDE at least once. The per-construct
/// sites are asserted DECIDED by the typed-seam run and GENERATED for the
/// source frontend by `every_binding_site_is_generated_for_the_source_frontend`
/// (a per-mode decided floor on each of them is noise at the default case
/// count, not coverage).
const COMMON_SITES: [Site; 3] = [
    Site::PinnedVariable,
    Site::ArithOperand,
    Site::CompareOperand,
];

#[test]
fn oracle_source_ensures_exec() {
    source_mode(SrcMode::EnsuresExec, &COMMON_SITES);
}

#[test]
fn oracle_source_ensures_proof() {
    source_mode(SrcMode::EnsuresProof, &COMMON_SITES);
}

#[test]
fn oracle_source_body_exec() {
    let mut sites = COMMON_SITES.to_vec();
    sites.push(Site::LetDeclared);
    sites.extend(
        ALL_BINDS
            .iter()
            .filter(|bind| bind.exec_only() && !bind.fail_closed())
            .map(|bind| bind.site()),
    );
    source_mode(SrcMode::BodyExec, &sites);
}

#[test]
fn oracle_source_body_proof() {
    let mut sites = COMMON_SITES.to_vec();
    sites.extend(
        binds_of(SrcMode::BodyProof)
            .iter()
            .filter(|bind| !bind.fail_closed())
            .map(|bind| bind.site()),
    );
    sites.push(Site::LaneOffFile);
    source_mode(SrcMode::BodyProof, &sites);
}

/// COVERAGE of the source frontend, without a solver: across its six modes
/// the generator produces every binding site (the typed seam's `let` is the
/// source's body `let`).
#[test]
fn every_binding_site_is_generated_for_the_source_frontend() {
    let mut site_set = BTreeSet::new();
    for mode in [
        SrcMode::EnsuresExec,
        SrcMode::EnsuresProof,
        SrcMode::BodyExec,
        SrcMode::BodyProof,
        SrcMode::SpecBool,
        SrcMode::SpecValue,
    ] {
        let (cs, _) = source_cases(mode, 0x50C, 200);
        for c in cs {
            site_set.extend(c.sites);
        }
    }
    let missing: Vec<Site> = ALL_SITES
        .iter()
        .copied()
        .filter(|s| frontends(*s) != Frontends::SeamOnly && !site_set.contains(s))
        .collect();
    assert!(
        missing.is_empty(),
        "binding sites the source frontend never generates: {missing:?}"
    );
}

#[test]
fn oracle_source_spec_fn_bool() {
    source_mode(SrcMode::SpecBool, &COMMON_SITES);
}

#[test]
fn oracle_source_spec_fn_value() {
    let mut sites = COMMON_SITES.to_vec();
    sites.push(Site::SpecFnResult);
    source_mode(SrcMode::SpecValue, &sites);
}
