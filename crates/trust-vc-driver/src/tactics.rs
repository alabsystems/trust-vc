//! Solver-specialization hook: VC-shape → strategy dispatch (capability #7).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # What this is (and honestly, what it is not)
//!
//! The *native-code* solver specialization — turning a recurring SMT query
//! shape into specialized machine code — lives in **ay's self-hosted JIT**
//! (`ay-jit`, see the crate-root note in `CLAUDE.md`). This module is the
//! **trust-vc side** of that mechanism: a shape-keyed dispatch table that
//! recognizes when two verification conditions have the *same structure* and
//! lets the driver reuse (and ultimately feed the JIT) a single chosen
//! [`Strategy`] for that shape. No solver behavior changes here; this is pure
//! trust-vc dispatch logic.
//!
//! # The shape fingerprint
//!
//! [`shape_fingerprint`] walks a [`DriverFn`]'s typed IR and emits a canonical
//! *skeleton* string. The skeleton keeps everything that determines how the
//! solver should be driven — operators, type widths/kinds, quantifier shape,
//! collection ops, and nesting structure — but **erases the parts that do not
//! change the proof strategy**:
//!
//! * every [`TrustVcExpr::IntLit`] value collapses to a `#` placeholder
//!   (keeping its *type*), and
//! * every [`TrustVcExpr::Var`] / bound-variable *name* collapses to `$`
//!   (keeping its *type*).
//!
//! So two monomorphized VCs that differ only in constant values and in
//! variable names — exactly what you get from generic code instantiated at
//! different call sites — produce the **same** fingerprint and therefore share
//! one cache entry, while a structurally different VC (a different operator,
//! type, or nesting) produces a **different** fingerprint. That is the property
//! the tests pin.
//!
//! # Fail-closed
//!
//! Fingerprinting is *advisory*: it only selects which precomputed strategy to
//! try. It never asserts a goal is true, never alters the encoding, and the
//! cache returning the wrong [`Strategy`] can at worst pick a slower path — it
//! cannot make a false thing verify. The match arms below are exhaustive over
//! today's IR with a stable catch-all token, so a future `#[non_exhaustive]`
//! variant degrades to "unknown shape" rather than silently aliasing onto an
//! existing fingerprint.

use std::collections::HashMap;
use std::fmt::Write as _;

use trust_vc_core::ir::{
    ArithOp, CollectionOp, CompareOp, IntConstKind, LogicOp, QuantifierKind, SpecialArithOp,
    TrustVcExpr, TrustVcType, WrappingMode,
};

use crate::lower::DriverFn;

/// A solver-driving strategy selected for a given VC shape.
///
/// These name *how* the (ay) backend should attack a query whose structure
/// matches a recorded fingerprint. The variants are deliberately coarse; the
/// fine-grained, native-code specialization is ay-JIT's job — this enum is the
/// trust-vc-side selector that decides which JIT-backed path to feed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum Strategy {
    /// No specialization: drive the solver with its default configuration.
    #[default]
    Default,
    /// Bit-blast: eagerly reduce bit-vector / integer-width reasoning to SAT.
    /// A good fit for shapes dominated by fixed-width [`TrustVcType::Int`] /
    /// [`TrustVcType::Uint`] arithmetic and bitwise ops.
    BitVectorBlast,
    /// Linear-arithmetic focus: prefer the LIA/LRA decision procedure for
    /// shapes over unbounded [`TrustVcType::MathInt`] / [`TrustVcType::Nat`] /
    /// [`TrustVcType::Real`] with only `+`/`-` and comparisons.
    LinearArithmetic,
    /// Quantifier-instantiation focus: shapes carrying a
    /// [`TrustVcExpr::Quantifier`] benefit from trigger-guided instantiation.
    QuantifierInstantiation,
    /// Collection-theory focus: shapes touching Seq/Set/Map/Multiset ops are
    /// routed to ay's native collection decision procedures.
    CollectionTheory,
}

/// A shape-keyed dispatch table: VC-shape fingerprint → chosen [`Strategy`].
///
/// Recurring monomorphized VC shapes (generic code instantiated at many call
/// sites) collide on a single fingerprint, so the strategy chosen the first
/// time is reused for every later instance — the trust-vc-side reuse that
/// amortizes ay-JIT specialization across structurally-identical queries.
#[derive(Debug, Clone, Default)]
pub struct SpecializationCache {
    entries: HashMap<String, Strategy>,
}

impl SpecializationCache {
    /// Creates an empty cache.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Records `strategy` for `fingerprint`, returning the previous strategy for
    /// that shape if one was already recorded.
    pub fn record(
        &mut self,
        fingerprint: impl Into<String>,
        strategy: Strategy,
    ) -> Option<Strategy> {
        self.entries.insert(fingerprint.into(), strategy)
    }

    /// Records the strategy keyed by `f`'s structural fingerprint. Convenience
    /// wrapper over [`SpecializationCache::record`] + [`shape_fingerprint`].
    pub fn record_fn(&mut self, f: &DriverFn, strategy: Strategy) -> Option<Strategy> {
        self.record(shape_fingerprint(f), strategy)
    }

    /// Looks up the strategy recorded for `fingerprint`, if any.
    #[must_use]
    pub fn lookup(&self, fingerprint: &str) -> Option<Strategy> {
        self.entries.get(fingerprint).copied()
    }

    /// Looks up the strategy recorded for `f`'s structural fingerprint. Two
    /// [`DriverFn`]s identical up to constants/renames hit the same entry.
    #[must_use]
    pub fn lookup_fn(&self, f: &DriverFn) -> Option<Strategy> {
        self.lookup(&shape_fingerprint(f))
    }

    /// Number of distinct shapes recorded.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// True if no shapes have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Computes the canonical structural fingerprint of a verification target.
///
/// The result is identical for two [`DriverFn`]s that differ **only** in
/// integer-literal values and in variable names, and differs whenever the
/// operator/type/structure skeleton differs. See the module docs for the exact
/// erasure rules.
///
/// The fingerprint covers the whole obligation skeleton — parameter and result
/// *types* (names erased), every `requires`, the `body` relation, and every
/// `ensures` — in the same order [`DriverFn::to_context`] lowers them, so the
/// key tracks what the encoder actually sees.
#[must_use]
pub fn shape_fingerprint(f: &DriverFn) -> String {
    let mut out = String::new();

    // Parameter *types* only — names are part of what we deliberately erase.
    out.push_str("params[");
    for p in &f.params {
        type_skeleton(&p.ty, &mut out);
        out.push(';');
    }
    out.push(']');

    // Result type (its name, `result`, is irrelevant to shape).
    out.push_str("->result:");
    type_skeleton(&f.result.ty, &mut out);

    out.push_str("|requires[");
    for r in &f.requires {
        expr_skeleton(r, &mut out);
        out.push(';');
    }
    out.push(']');

    out.push_str("|body:");
    match &f.body_value {
        Some(b) => expr_skeleton(b, &mut out),
        None => out.push_str("<opaque>"),
    }

    out.push_str("|ensures[");
    for e in &f.ensures {
        expr_skeleton(e, &mut out);
        out.push(';');
    }
    out.push(']');

    out
}

/// Suggests a default [`Strategy`] from a function's dominant shape.
///
/// A convenience heuristic so callers can seed a [`SpecializationCache`] with a
/// reasonable first guess; it is *advisory only* (see the fail-closed note in
/// the module docs). The classification is purely structural — it never
/// inspects literal values — so it is stable under the same renames/constant
/// changes the fingerprint erases.
#[must_use]
pub fn suggest_strategy(f: &DriverFn) -> Strategy {
    let mut flags = ShapeFlags::default();
    for p in &f.params {
        flags.observe_type(&p.ty);
    }
    flags.observe_type(&f.result.ty);
    for r in &f.requires {
        flags.observe_expr(r);
    }
    if let Some(b) = &f.body_value {
        flags.observe_expr(b);
    }
    for e in &f.ensures {
        flags.observe_expr(e);
    }
    flags.classify()
}

#[derive(Default)]
struct ShapeFlags {
    has_collection: bool,
    has_quantifier: bool,
    has_bitvec: bool,
    has_unbounded: bool,
}

impl ShapeFlags {
    fn observe_type(&mut self, ty: &TrustVcType) {
        match ty {
            TrustVcType::Int { .. } | TrustVcType::Uint { .. } | TrustVcType::Char => {
                self.has_bitvec = true;
            }
            TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real => {
                self.has_unbounded = true;
            }
            t if t.is_collection() || t.is_string_like() => self.has_collection = true,
            _ => {}
        }
    }

    fn observe_expr(&mut self, e: &TrustVcExpr) {
        match e {
            TrustVcExpr::Quantifier { .. } => self.has_quantifier = true,
            TrustVcExpr::CollectionOp { .. } | TrustVcExpr::Index { .. } => {
                self.has_collection = true;
            }
            TrustVcExpr::SpecialArith { .. } => self.has_bitvec = true,
            TrustVcExpr::IntLit { ty, .. } | TrustVcExpr::Var { ty, .. } => self.observe_type(ty),
            _ => {}
        }
        // Recurse so nested shapes (e.g. a quantifier over a collection) count.
        walk_children(e, &mut |child| self.observe_expr(child));
    }

    fn classify(&self) -> Strategy {
        // Most-specific theory wins; the order encodes which specialization the
        // backend benefits from most when several apply.
        if self.has_quantifier {
            Strategy::QuantifierInstantiation
        } else if self.has_collection {
            Strategy::CollectionTheory
        } else if self.has_bitvec {
            Strategy::BitVectorBlast
        } else if self.has_unbounded {
            Strategy::LinearArithmetic
        } else {
            Strategy::Default
        }
    }
}

// ---------------------------------------------------------------------------
// Skeleton emission.
//
// The two functions below produce the canonical tokens. The invariant they must
// maintain: *every* field that distinguishes proof strategy is written, and only
// `IntLit` values + `Var`/bound names are erased. New IR variants land in the
// `_` arm as a distinct `<expr?>` token — a coarser-but-sound fingerprint, never
// a collision with an existing shape.
// ---------------------------------------------------------------------------

fn type_skeleton(ty: &TrustVcType, out: &mut String) {
    match ty {
        TrustVcType::Unit => out.push_str("Unit"),
        TrustVcType::Bool => out.push_str("Bool"),
        TrustVcType::Int { width } => {
            let _ = write!(out, "Int{width}");
        }
        TrustVcType::Uint { width } => {
            let _ = write!(out, "Uint{width}");
        }
        TrustVcType::MathInt => out.push_str("MathInt"),
        TrustVcType::Nat => out.push_str("Nat"),
        TrustVcType::Real => out.push_str("Real"),
        TrustVcType::Float { width } => {
            let _ = write!(out, "Float{width}");
        }
        TrustVcType::Char => out.push_str("Char"),
        TrustVcType::StrSlice => out.push_str("StrSlice"),
        TrustVcType::String => out.push_str("String"),
        TrustVcType::Seq(inner) => {
            out.push_str("Seq<");
            type_skeleton(inner, out);
            out.push('>');
        }
        TrustVcType::Array(inner, n) => {
            out.push_str("Array<");
            type_skeleton(inner, out);
            // The length `N` is part of the *type* skeleton: `[T; 4]` and
            // `[T; 8]` are different monomorphizations the encoder treats
            // distinctly, so it is structure, not an erasable literal value.
            let _ = write!(out, ";{n}>");
        }
        TrustVcType::Set(inner) => {
            out.push_str("Set<");
            type_skeleton(inner, out);
            out.push('>');
        }
        TrustVcType::Multiset(inner) => {
            out.push_str("Multiset<");
            type_skeleton(inner, out);
            out.push('>');
        }
        TrustVcType::Map(k, v) => {
            out.push_str("Map<");
            type_skeleton(k, out);
            out.push(',');
            type_skeleton(v, out);
            out.push('>');
        }
        TrustVcType::SpecFn(args, ret) => {
            out.push_str("SpecFn<(");
            for a in args {
                type_skeleton(a, out);
                out.push(',');
            }
            out.push_str(")->");
            type_skeleton(ret, out);
            out.push('>');
        }
        // For nominal types the *name* is load-bearing structure (a different
        // datatype is a genuinely different shape), so it is kept, unlike the
        // erased variable/literal names above.
        TrustVcType::Datatype { name, .. } => {
            let _ = write!(out, "Datatype({name})");
        }
        TrustVcType::RecursiveRef(name) => {
            let _ = write!(out, "RecursiveRef({name})");
        }
        TrustVcType::TypeParam(name) => {
            let _ = write!(out, "TypeParam({name})");
        }
        TrustVcType::Poly => out.push_str("Poly"),
        TrustVcType::Opaque(name) => {
            let _ = write!(out, "Opaque({name})");
        }
        // Forward-compat: a future type variant gets a coarse, distinct token.
        _ => out.push_str("<type?>"),
    }
}

fn expr_skeleton(e: &TrustVcExpr, out: &mut String) {
    match e {
        TrustVcExpr::UnitLit => out.push_str("unit"),
        TrustVcExpr::BoolLit(b) => {
            // A boolean literal's *value* flips which branch of a goal is true,
            // so unlike an integer magnitude it is structure, not noise.
            let _ = write!(out, "bool({b})");
        }
        // A string literal's *content* is an erasable constant, just like an
        // integer literal value.
        TrustVcExpr::StringLit(_) => out.push_str("str(#)"),
        // ERASED: the integer value collapses to `#`; the *type* is kept.
        TrustVcExpr::IntLit { ty, .. } => {
            out.push_str("int(#:");
            type_skeleton(ty, out);
            out.push(')');
        }
        // ERASED: the variable *name* collapses to `$`; the *type* is kept.
        TrustVcExpr::Var { ty, .. } => {
            out.push_str("var($:");
            type_skeleton(ty, out);
            out.push(')');
        }
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => {
            out.push_str("arith(");
            out.push_str(arith_op_token(*op));
            out.push(':');
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(left, out);
            out.push(',');
            expr_skeleton(right, out);
            out.push(')');
        }
        TrustVcExpr::Neg(inner) => {
            out.push_str("neg(");
            expr_skeleton(inner, out);
            out.push(')');
        }
        TrustVcExpr::Compare { op, left, right } => {
            out.push_str("cmp(");
            out.push_str(compare_op_token(*op));
            out.push(',');
            expr_skeleton(left, out);
            out.push(',');
            expr_skeleton(right, out);
            out.push(')');
        }
        TrustVcExpr::Logic { op, left, right } => {
            out.push_str("logic(");
            out.push_str(logic_op_token(*op));
            out.push(',');
            expr_skeleton(left, out);
            out.push(',');
            expr_skeleton(right, out);
            out.push(')');
        }
        TrustVcExpr::Not(inner) => {
            out.push_str("not(");
            expr_skeleton(inner, out);
            out.push(')');
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            out.push_str("implies(");
            expr_skeleton(premise, out);
            out.push(',');
            expr_skeleton(conclusion, out);
            out.push(')');
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            out.push_str("ite(");
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(cond, out);
            out.push(',');
            expr_skeleton(then_branch, out);
            out.push(',');
            expr_skeleton(else_branch, out);
            out.push(')');
        }
        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => {
            out.push_str("match(");
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(scrutinee, out);
            let _ = write!(out, ",arms{}", arms.len());
            for arm in arms {
                out.push(',');
                expr_skeleton(&arm.body, out);
            }
            out.push(')');
        }
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            // The binding *name* is erased (it is a `Var` name elsewhere); the
            // bound *type* and the value/body structure are kept.
            out.push_str("let($:");
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(value, out);
            out.push(',');
            expr_skeleton(body, out);
            out.push(')');
        }
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => {
            out.push_str("cast(");
            type_skeleton(from_ty, out);
            out.push_str("->");
            type_skeleton(to_ty, out);
            out.push(',');
            expr_skeleton(expr, out);
            out.push(')');
        }
        TrustVcExpr::CollectionOp {
            op,
            receiver,
            args,
            ty,
            ..
        } => {
            // `receiver_name` is an erasable variable name; the op, element
            // type, and operand structure are what drive the collection theory.
            out.push_str("coll(");
            out.push_str(collection_op_token(*op));
            out.push(':');
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(receiver, out);
            for a in args {
                out.push(',');
                expr_skeleton(a, out);
            }
            out.push(')');
        }
        TrustVcExpr::Index {
            receiver,
            index,
            elem_ty,
            ..
        } => {
            out.push_str("index(");
            type_skeleton(elem_ty, out);
            out.push(',');
            expr_skeleton(receiver, out);
            out.push(',');
            expr_skeleton(index, out);
            out.push(')');
        }
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            ..
        } => {
            out.push_str("quant(");
            out.push_str(quantifier_kind_token(*kind));
            // Bound-variable names are erased; their *types* (and arity) stay.
            out.push_str(",binders[");
            for (_, ty) in bound_vars {
                type_skeleton(ty, out);
                out.push(';');
            }
            out.push(']');
            // Trigger *presence/arity* changes instantiation behavior, so it is
            // structure; the trigger expressions themselves are skeletonized.
            match triggers {
                None => out.push_str(",trig:none"),
                Some(groups) => {
                    let _ = write!(out, ",trig{}", groups.len());
                    for group in groups {
                        out.push('[');
                        for t in group {
                            expr_skeleton(t, out);
                            out.push(';');
                        }
                        out.push(']');
                    }
                }
            }
            out.push(',');
            expr_skeleton(body, out);
            out.push(')');
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            // A called function's *name* selects a different uninterpreted
            // symbol / body axiom, so it is load-bearing structure, kept.
            let _ = write!(out, "call({name}:");
            type_skeleton(return_ty, out);
            for a in args {
                out.push(',');
                expr_skeleton(a, out);
            }
            out.push(')');
        }
        TrustVcExpr::SpecClosure { params, body, ty } => {
            out.push_str("closure(");
            type_skeleton(ty, out);
            out.push_str(",params[");
            for (_, pty) in params {
                type_skeleton(pty, out);
                out.push(';');
            }
            out.push(']');
            out.push(',');
            expr_skeleton(body, out);
            out.push(')');
        }
        TrustVcExpr::IntConst { ty, kind } => {
            // `MIN`/`MAX` are distinct *symbols*, not erasable magnitudes.
            out.push_str("intconst(");
            out.push_str(int_const_kind_token(*kind));
            out.push(':');
            type_skeleton(ty, out);
            out.push(')');
        }
        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => {
            out.push_str("bitop(");
            out.push_str(special_arith_op_token(*op));
            out.push(':');
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(left, out);
            out.push(',');
            expr_skeleton(right, out);
            out.push(')');
        }
        TrustVcExpr::WrappingArith {
            mode,
            op,
            left,
            right,
            ty,
        } => {
            out.push_str("wrap(");
            out.push_str(wrapping_mode_token(*mode));
            out.push(':');
            out.push_str(arith_op_token(*op));
            out.push(':');
            type_skeleton(ty, out);
            out.push(',');
            expr_skeleton(left, out);
            out.push(',');
            expr_skeleton(right, out);
            out.push(')');
        }
        TrustVcExpr::Choose {
            var_ty, condition, ..
        } => {
            // `var_name`/`key` are erasable identities; the bound type and the
            // condition structure stay.
            out.push_str("choose($:");
            type_skeleton(var_ty, out);
            out.push(',');
            expr_skeleton(condition, out);
            out.push(')');
        }
        TrustVcExpr::ReadPlace { ty, .. } => {
            // The concrete place (root var name + projections) is identity, not
            // shape; only the read's *type* is kept.
            out.push_str("readplace(");
            type_skeleton(ty, out);
            out.push(')');
        }
        TrustVcExpr::PlaceDisjoint { .. } => out.push_str("disjoint"),
        TrustVcExpr::ProphecyNew { ty, .. } => {
            out.push_str("prophnew(");
            type_skeleton(ty, out);
            out.push(')');
        }
        TrustVcExpr::ProphecyResolve { value, .. } => {
            out.push_str("prophresolve(");
            expr_skeleton(value, out);
            out.push(')');
        }
        // Forward-compat: a future expr variant gets a coarse, distinct token
        // rather than silently aliasing onto an existing shape.
        _ => out.push_str("<expr?>"),
    }
}

/// Visits the direct sub-expression children of `e`, applying `f` to each.
///
/// Used by [`ShapeFlags::observe_expr`] to recurse without re-encoding the full
/// skeleton match. It walks only `TrustVcExpr` children (not the erased names /
/// types), which is all the strategy heuristic needs.
fn walk_children(e: &TrustVcExpr, f: &mut dyn FnMut(&TrustVcExpr)) {
    match e {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. }
        | TrustVcExpr::ReadPlace { .. }
        | TrustVcExpr::PlaceDisjoint { .. }
        | TrustVcExpr::ProphecyNew { .. } => {}
        TrustVcExpr::Neg(inner)
        | TrustVcExpr::Not(inner)
        | TrustVcExpr::ProphecyResolve { value: inner, .. } => f(inner),
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            f(left);
            f(right);
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            f(premise);
            f(conclusion);
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            f(cond);
            f(then_branch);
            f(else_branch);
        }
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            f(scrutinee);
            for arm in arms {
                f(&arm.body);
            }
        }
        TrustVcExpr::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        TrustVcExpr::Cast { expr, .. } => f(expr),
        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            f(receiver);
            for a in args {
                f(a);
            }
        }
        TrustVcExpr::Index {
            receiver, index, ..
        } => {
            f(receiver);
            f(index);
        }
        TrustVcExpr::Quantifier { body, .. }
        | TrustVcExpr::Choose {
            condition: body, ..
        } => f(body),
        TrustVcExpr::FnCall { args, .. } => {
            for a in args {
                f(a);
            }
        }
        TrustVcExpr::SpecClosure { body, .. } => f(body),
        _ => {}
    }
}

// --- Operator tokenizers (stable, value-free) ------------------------------

fn arith_op_token(op: ArithOp) -> &'static str {
    match op {
        ArithOp::Add => "+",
        ArithOp::Sub => "-",
        ArithOp::Mul => "*",
        ArithOp::Div => "/",
        ArithOp::Rem => "%",
        _ => "arith?",
    }
}

fn compare_op_token(op: CompareOp) -> &'static str {
    match op {
        CompareOp::Eq => "==",
        CompareOp::Ne => "!=",
        CompareOp::Lt => "<",
        CompareOp::Le => "<=",
        CompareOp::Gt => ">",
        CompareOp::Ge => ">=",
        _ => "cmp?",
    }
}

fn logic_op_token(op: LogicOp) -> &'static str {
    match op {
        LogicOp::And => "&&",
        LogicOp::Or => "||",
        _ => "logic?",
    }
}

fn special_arith_op_token(op: SpecialArithOp) -> &'static str {
    match op {
        SpecialArithOp::BitAnd => "&",
        SpecialArithOp::BitOr => "|",
        SpecialArithOp::BitXor => "^",
        SpecialArithOp::Shl => "<<",
        SpecialArithOp::Shr => ">>",
        _ => "bit?",
    }
}

fn quantifier_kind_token(kind: QuantifierKind) -> &'static str {
    match kind {
        QuantifierKind::Forall => "forall",
        QuantifierKind::Exists => "exists",
        _ => "quant?",
    }
}

fn int_const_kind_token(kind: IntConstKind) -> &'static str {
    match kind {
        IntConstKind::Min => "MIN",
        IntConstKind::Max => "MAX",
        _ => "const?",
    }
}

fn wrapping_mode_token(mode: WrappingMode) -> &'static str {
    match mode {
        WrappingMode::Wrapping => "wrapping",
        WrappingMode::Checked => "checked",
        WrappingMode::Saturating => "saturating",
        _ => "wrap?",
    }
}

fn collection_op_token(op: CollectionOp) -> &'static str {
    match op {
        CollectionOp::Len => "len",
        CollectionOp::IsEmpty => "is_empty",
        CollectionOp::Push => "push",
        CollectionOp::Add => "add",
        CollectionOp::First => "first",
        CollectionOp::Last => "last",
        CollectionOp::Update => "update",
        CollectionOp::DropLast => "drop_last",
        CollectionOp::DropFirst => "drop_first",
        CollectionOp::Take => "take",
        CollectionOp::Skip => "skip",
        CollectionOp::Subrange => "subrange",
        CollectionOp::Concat => "concat",
        CollectionOp::View => "view",
        CollectionOp::SeqMapValues => "seq_map_values",
        CollectionOp::SeqMap => "seq_map",
        CollectionOp::SeqFilter => "seq_filter",
        CollectionOp::SeqFlatMap => "seq_flat_map",
        CollectionOp::SeqFoldLeft => "seq_fold_left",
        CollectionOp::SeqFoldRight => "seq_fold_right",
        CollectionOp::Reverse => "reverse",
        CollectionOp::NoDuplicates => "no_duplicates",
        CollectionOp::ToSet => "to_set",
        CollectionOp::ToMultiset => "to_multiset",
        CollectionOp::Contains => "contains",
        CollectionOp::Insert => "insert",
        CollectionOp::Remove => "remove",
        CollectionOp::Union => "union",
        CollectionOp::Intersect => "intersect",
        CollectionOp::Difference => "difference",
        CollectionOp::Subset => "subset",
        CollectionOp::Superset => "superset",
        CollectionOp::Finite => "finite",
        CollectionOp::SetFilter => "set_filter",
        CollectionOp::SetMap => "set_map",
        CollectionOp::SetMkMap => "set_mk_map",
        CollectionOp::SetFold => "set_fold",
        CollectionOp::Count => "count",
        CollectionOp::Choose => "choose",
        CollectionOp::Get => "get",
        CollectionOp::ContainsKey => "contains_key",
        CollectionOp::ContainsValue => "contains_value",
        CollectionOp::Dom => "dom",
        CollectionOp::MapMapValues => "map_map_values",
        CollectionOp::MapMapEntries => "map_map_entries",
        CollectionOp::MapFilterKeys => "map_filter_keys",
        _ => "coll?",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::{add, cmp, lit, mul, uint, var, Binding};

    fn u32t() -> TrustVcType {
        uint(32)
    }

    // fn add_bounds(x, y) requires x<C, y<C { x+y } ensures result<C  — built
    // with constants C and parameter names N1/N2 supplied by the caller, so the
    // tests can vary *only* those and check fingerprint stability.
    fn add_fn(n1: &str, n2: &str, c1: i128, c2: i128, c3: i128) -> DriverFn {
        DriverFn {
            name: "f".into(),
            params: vec![Binding::new(n1, u32t()), Binding::new(n2, u32t())],
            result: Binding::new("result", u32t()),
            requires: vec![
                cmp(CompareOp::Lt, var(n1, u32t()), lit(c1, u32t())),
                cmp(CompareOp::Lt, var(n2, u32t()), lit(c2, u32t())),
            ],
            body_value: Some(add(var(n1, u32t()), var(n2, u32t()), u32t())),
            ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(c3, u32t()))],
        }
    }

    #[test]
    fn constants_and_names_are_erased() {
        let a = add_fn("x", "y", 100, 100, 200);
        let b = add_fn("p", "q", 7, 9999, 1);
        assert_eq!(
            shape_fingerprint(&a),
            shape_fingerprint(&b),
            "functions differing only in constants/names must share a fingerprint"
        );
    }

    #[test]
    fn different_operator_changes_fingerprint() {
        let plus = add_fn("x", "y", 100, 100, 200);
        let mut times = add_fn("x", "y", 100, 100, 200);
        // Same constants/names, but `*` instead of `+` in the body.
        times.body_value = Some(mul(var("x", u32t()), var("y", u32t()), u32t()));
        assert_ne!(
            shape_fingerprint(&plus),
            shape_fingerprint(&times),
            "a different operator is a different shape"
        );
    }

    #[test]
    fn different_type_width_changes_fingerprint() {
        let w32 = add_fn("x", "y", 100, 100, 200);
        let w64 = DriverFn {
            params: vec![Binding::new("x", uint(64)), Binding::new("y", uint(64))],
            result: Binding::new("result", uint(64)),
            requires: vec![
                cmp(CompareOp::Lt, var("x", uint(64)), lit(100, uint(64))),
                cmp(CompareOp::Lt, var("y", uint(64)), lit(100, uint(64))),
            ],
            body_value: Some(add(var("x", uint(64)), var("y", uint(64)), uint(64))),
            ensures: vec![cmp(
                CompareOp::Lt,
                var("result", uint(64)),
                lit(200, uint(64)),
            )],
            name: "f".into(),
        };
        assert_ne!(
            shape_fingerprint(&w32),
            shape_fingerprint(&w64),
            "a different integer width is a different shape"
        );
    }

    #[test]
    fn cache_shares_entry_across_renames_and_constants() {
        let mut cache = SpecializationCache::new();
        let a = add_fn("x", "y", 100, 100, 200);
        let b = add_fn("p", "q", 7, 9999, 1);

        assert!(cache.lookup_fn(&a).is_none());
        cache.record_fn(&a, Strategy::BitVectorBlast);

        // `b` is the same shape as `a`, so it hits the same entry.
        assert_eq!(cache.lookup_fn(&b), Some(Strategy::BitVectorBlast));
        assert_eq!(cache.len(), 1, "same shape must not grow the cache");
    }

    #[test]
    fn suggest_strategy_picks_bitvector_for_fixed_width_arith() {
        let f = add_fn("x", "y", 100, 100, 200);
        assert_eq!(suggest_strategy(&f), Strategy::BitVectorBlast);
    }
}
