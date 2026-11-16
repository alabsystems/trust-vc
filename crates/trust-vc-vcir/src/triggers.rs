//! Verus's triggers for a quantifier or choice (`vir/src/triggers.rs` and
//! `vir/src/triggers_auto.rs`), over VcIR expressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A producer reads a quantifier's body and gives [`build_triggers`] what
//! Verus would see: the body, the `#[trigger]` marks found while reading it
//! (those of nested quantifiers included), the `#![trigger ..]` groups and
//! the `#![auto]` / `#![all_triggers]` annotation. The result is Verus's
//! choice of triggers, or Verus's error with its message.
//!
//! Manual triggers are checked as Verus checks them: the forms a trigger
//! may take, the forms it may contain, and that each group covers every
//! variable. Without manual triggers the automatic choice is Verus's: among
//! the candidate terms (applications, field accesses, constructors and
//! bitwise operators over the variables, with no arithmetic, comparison or
//! boolean operator inside), drop the ones that look like matching loops,
//! then pick the covers of the variables with the fewest terms and, among
//! those, the lowest score (bitwise operators, then terms without a call,
//! then depth, then size). Ties are all kept; `#![all_triggers]` keeps
//! every minimal cover.
//!
//! Where VcIR is coarser than Verus's SST the reading here follows the
//! VcIR: a call names the function the producer calls (an instance of a
//! generic function at its type arguments), where Verus names the generic
//! function and treats concrete type arguments as part of no term.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::expr::{BinOp, CastKind, Expr, ExprKind, Lit, Place, Projection, UnOp};
use crate::ids::{FnId, LocalId, SpanId};
use crate::ty::{IntRange, Ty};

/// Verus's annotation for automatic triggers on a quantifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AutoMode {
    /// No annotation: Verus chooses, and reports a low-confidence choice.
    #[default]
    None,
    /// `#![auto]`: accept Verus's choice.
    Auto,
    /// `#![all_triggers]`: every minimal cover.
    All,
}

/// A `#[trigger]` mark on a term inside a quantifier's body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mark {
    /// `None` for `#[trigger]`, the group for `#[trigger(n)]`.
    pub group: Option<u64>,
    /// The marked term.
    pub term: Expr,
}

/// Verus's error: its message at its span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TriggerError {
    /// Where Verus reports it.
    pub span: SpanId,
    /// Verus's message.
    pub message: String,
}

/// What [`build_triggers`] needs about one quantifier.
pub struct Quantifier<'a> {
    /// The variables the triggers must cover.
    pub vars: &'a [LocalId],
    /// The body (a choice's condition).
    pub body: &'a Expr,
    /// The `#[trigger]` marks inside the body, nested quantifiers' included.
    pub marks: &'a [Mark],
    /// The `#![trigger ..]` groups on the body.
    pub with_triggers: &'a [Vec<Expr>],
    /// The `#![auto]` / `#![all_triggers]` annotation on the body.
    pub auto: AutoMode,
    /// The quantifier as a whole, where Verus reports a missing trigger.
    pub span: SpanId,
    /// The type of a local, for field accesses through a place.
    pub local_ty: &'a dyn Fn(LocalId) -> Option<Ty>,
    /// Functions Verus never chooses (`#[verifier::no_auto_trigger]`).
    pub no_auto_trigger: &'a dyn Fn(FnId) -> bool,
}

/// `vir/src/triggers_auto.rs`, the message when nothing covers the
/// variables.
pub const MSG_NO_TRIGGERS: &str = "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.";
/// `vir/src/triggers.rs`, `check_trigger_expr`.
pub const MSG_TRIGGER_FORM: &str =
    "trigger must be a function call, a field access, or arithmetic operator";
/// `vir/src/triggers.rs`, `build_triggers`.
pub const MSG_MANUAL_AND_AUTO: &str =
    "cannot use both manual triggers (#[trigger] or #![trigger ...]) and #![auto]";
/// `vir/src/triggers.rs`, a let variable in a trigger.
pub const MSG_LET_IN_TRIGGER: &str =
    "let variables in triggers not supported, use #![trigger ...] instead";
/// `vir/src/triggers.rs`, a boolean operator in a trigger.
pub const MSG_BOOL_IN_TRIGGER: &str = "triggers cannot contain boolean operators";
/// `vir/src/triggers.rs`, an inequality in a trigger.
pub const MSG_INEQ_IN_TRIGGER: &str = "triggers cannot contain inequalities";
/// `vir/src/triggers.rs`, an `if` in a trigger.
pub const MSG_IF_IN_TRIGGER: &str = "triggers cannot contain if/else";
/// `vir/src/triggers.rs`, a binder in a trigger.
pub const MSG_BIND_IN_TRIGGER: &str = "triggers cannot contain let/forall/exists/lambda/choose";
/// `vir/src/triggers_auto.rs`, the search's step limit.
pub const MSG_TOO_LARGE: &str =
    "could not infer triggers, because quantifier is too large (use manual #[trigger] instead)";

/// Verus's message for a group that misses a variable.
#[must_use]
pub fn msg_not_covered(group: Option<u64>, var: &str) -> String {
    let group = match group {
        None => String::new(),
        Some(id) => format!(" group {id}"),
    };
    format!("trigger{group} does not cover variable {var}")
}

/// Verus's triggers for `q`, or its error. `name` gives a variable's source
/// name for messages.
pub fn build_triggers(
    q: &Quantifier<'_>,
    name: &dyn Fn(LocalId) -> String,
) -> Result<Vec<Vec<Expr>>, TriggerError> {
    let vars: HashSet<LocalId> = q.vars.iter().copied().collect();
    let mut nested: HashSet<LocalId> = HashSet::new();
    let mut lets: HashSet<LocalId> = HashSet::new();
    binders(q.body, &mut nested, &mut lets);
    for group in q.with_triggers {
        for term in group {
            binders(term, &mut nested, &mut lets);
        }
    }
    // Groups: `#![trigger ..]` as groups 0, 1, ..; marks join their group.
    let mut groups: BTreeMap<Option<u64>, Vec<Expr>> = BTreeMap::new();
    let mut coverage: HashMap<Option<u64>, HashSet<LocalId>> = HashMap::new();
    for (n, group) in q.with_triggers.iter().enumerate() {
        let key = Some(n as u64);
        let mut covered = HashSet::new();
        for term in group {
            check_trigger_expr(term, &lets)?;
            covered.extend(free_locals(term).into_iter().filter(|x| vars.contains(x)));
        }
        groups.insert(key, group.clone());
        coverage.insert(key, covered);
    }
    for mark in q.marks {
        let free = free_locals(&mark.term);
        // A mark with a variable of a nested quantifier is that
        // quantifier's; one with none of ours is an outer quantifier's.
        if free
            .iter()
            .any(|x| nested.contains(x) && !vars.contains(x) && !lets.contains(x))
        {
            continue;
        }
        check_trigger_expr(&mark.term, &lets)?;
        if !free.iter().any(|x| vars.contains(x)) {
            continue;
        }
        groups
            .entry(mark.group)
            .or_default()
            .push(mark.term.clone());
        coverage
            .entry(mark.group)
            .or_default()
            .extend(free.into_iter().filter(|x| vars.contains(x)));
    }
    if !groups.is_empty() {
        if q.auto != AutoMode::None {
            return Err(TriggerError {
                span: q.span,
                message: MSG_MANUAL_AND_AUTO.to_string(),
            });
        }
        for group in groups.keys() {
            for x in q.vars {
                if !coverage.get(group).is_some_and(|c| c.contains(x)) {
                    return Err(TriggerError {
                        span: q.span,
                        message: msg_not_covered(*group, &name(*x)),
                    });
                }
            }
        }
        return Ok(groups.into_values().collect());
    }
    auto_triggers(q)
}

/// The locals bound inside `e`: by nested quantifiers and choices
/// (`nested`, lets included) and by lets (`lets`).
fn binders(e: &Expr, nested: &mut HashSet<LocalId>, lets: &mut HashSet<LocalId>) {
    match &e.kind {
        ExprKind::Let { local, .. } => {
            nested.insert(*local);
            lets.insert(*local);
        }
        ExprKind::Quant { vars, .. }
        | ExprKind::Choose { vars, .. }
        | ExprKind::UntriggeredQuant { vars, .. }
        | ExprKind::UntriggeredChoose { vars, .. } => {
            nested.extend(vars.iter().map(|(var, _)| *var));
        }
        _ => {}
    }
    e.for_each_child(&mut |child| binders(child, nested, lets));
}

/// The locals `e` reads, through `Read` and `Old`.
fn free_locals(e: &Expr) -> Vec<LocalId> {
    let mut out = Vec::new();
    collect_reads(e, &mut out);
    out
}

fn collect_reads(e: &Expr, out: &mut Vec<LocalId>) {
    if let ExprKind::Read(place) | ExprKind::Old(place) = &e.kind {
        if !out.contains(&place.local) {
            out.push(place.local);
        }
    }
    e.for_each_child(&mut |child| collect_reads(child, out));
}

fn error(e: &Expr, message: &str) -> TriggerError {
    TriggerError {
        span: e.span,
        message: message.to_string(),
    }
}

/// Is `e` an integer operation in Verus's sense (not a boolean one)?
fn on_ints(e: &Expr) -> bool {
    e.ty.int_range().is_some()
}

/// `check_trigger_expr`: the forms a trigger may take and contain.
fn check_trigger_expr(e: &Expr, lets: &HashSet<LocalId>) -> Result<(), TriggerError> {
    let top = strip_transparent(e);
    let allowed = match &top.kind {
        ExprKind::Call { .. }
        | ExprKind::Field { .. }
        | ExprKind::IsVariant { .. }
        | ExprKind::TupleField { .. } => true,
        ExprKind::Read(place) => place
            .projections
            .iter()
            .any(|p| !matches!(p, Projection::Deref)),
        ExprKind::Binary { op, .. } => {
            (op.is_bitwise() || op.is_shift()) && on_ints(top) || op.is_arithmetic()
        }
        ExprKind::Unary { op: UnOp::Not, .. } => on_ints(top),
        ExprKind::Unary { op: UnOp::Neg, .. } => true,
        ExprKind::Cast { .. } => true,
        _ => false,
    };
    if !allowed {
        return Err(error(top, MSG_TRIGGER_FORM));
    }
    check_inside(e, lets)
}

/// Casts to `int`, shared borrows and derefs have no node in Verus's SST.
fn strip_transparent(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Cast {
            arg,
            kind: CastKind::Exact,
        } if e.ty.int_range() == Some(IntRange::Int) => strip_transparent(arg),
        ExprKind::Borrow(inner) => strip_transparent(inner),
        _ => e,
    }
}

/// The forms a trigger may not contain, first one in pre-order.
fn check_inside(e: &Expr, lets: &HashSet<LocalId>) -> Result<(), TriggerError> {
    match &e.kind {
        ExprKind::Read(place) | ExprKind::Old(place) => {
            if lets.contains(&place.local) {
                return Err(error(e, MSG_LET_IN_TRIGGER));
            }
        }
        ExprKind::Unary { op: UnOp::Not, .. } if !on_ints(e) => {
            return Err(error(e, MSG_BOOL_IN_TRIGGER))
        }
        ExprKind::Binary { op, lhs, .. } => {
            let boolean = op.is_logical()
                || matches!(op, BinOp::Eq | BinOp::Ne)
                || (op.is_bitwise() && !on_ints(lhs));
            if boolean {
                return Err(error(e, MSG_BOOL_IN_TRIGGER));
            }
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
                return Err(error(e, MSG_INEQ_IN_TRIGGER));
            }
        }
        ExprKind::If { .. } => return Err(error(e, MSG_IF_IN_TRIGGER)),
        ExprKind::Let { .. }
        | ExprKind::Quant { .. }
        | ExprKind::Choose { .. }
        | ExprKind::UntriggeredQuant { .. }
        | ExprKind::UntriggeredChoose { .. } => return Err(error(e, MSG_BIND_IN_TRIGGER)),
        _ => {}
    }
    let mut result = Ok(());
    e.for_each_child(&mut |child| {
        if result.is_ok() {
            result = check_inside(child, lets);
        }
    });
    result
}

// ----------------------------------------------------------------------
// Automatic triggers
// ----------------------------------------------------------------------

/// The head of a term (`App` in `triggers_auto.rs`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum App {
    Const(String),
    Field(String, u32, u32),
    Call(FnId, Vec<Ty>),
    Ctor(String, u32),
    IsVariant(String, u32),
    Tuple,
    Other(u64),
    VarAt(LocalId),
    BitOp(&'static str),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum T {
    Var(LocalId),
    App(App, Vec<T>),
}

/// Lower is better, lexicographically.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
struct Score {
    num_operators: u64,
    num_special: u64,
    no_calls: u64,
    depth: u64,
    size: u64,
}

impl Score {
    fn add(self, other: Self) -> Self {
        Self {
            num_operators: self.num_operators + other.num_operators,
            num_special: self.num_special + other.num_special,
            no_calls: self.no_calls + other.no_calls,
            depth: self.depth + other.depth,
            size: self.size + other.size,
        }
    }
}

struct Gather<'q, 'a> {
    q: &'q Quantifier<'a>,
    vars: HashSet<LocalId>,
    /// Every application term met, by head.
    all_by_app: HashMap<App, HashSet<T>>,
    all: HashSet<T>,
    /// Candidate terms with their expression and order of discovery.
    pure_terms: HashMap<T, (Expr, usize)>,
    best_scores: HashMap<T, Score>,
    next_id: u64,
}

impl Gather<'_, '_> {
    fn other(&mut self) -> App {
        self.next_id += 1;
        App::Other(self.next_id)
    }

    fn var_depth(&self, t: &T, depth: u64) -> Option<u64> {
        match t {
            T::Var(x) if self.vars.contains(x) => Some(depth),
            T::Var(_) => None,
            T::App(_, args) => args
                .iter()
                .filter_map(|a| self.var_depth(a, depth + 1))
                .max(),
        }
    }

    /// A place read: the local, then each projection as a field access.
    fn place(&mut self, e: &Expr, place: &Place, old: bool, depth: u64) -> (bool, T) {
        if old {
            return (true, T::App(App::VarAt(place.local), Vec::new()));
        }
        let mut ty = (self.q.local_ty)(place.local);
        let mut term = T::Var(place.local);
        let mut chain = Vec::new();
        for projection in &place.projections {
            let base = ty.as_ref().map(strip_refs);
            let label = base.as_ref().map_or_else(String::new, |t| format!("{t:?}"));
            match projection {
                Projection::Deref => {
                    ty = base;
                    continue;
                }
                Projection::Field { variant, field } => {
                    term = T::App(App::Field(label, *variant, *field), vec![term]);
                    ty = None;
                }
                Projection::TupleField(index) => {
                    term = T::App(App::Field(label, 0, *index), vec![term]);
                    ty = match base {
                        Some(Ty::Tuple(elems)) => elems.get(*index as usize).cloned(),
                        _ => None,
                    };
                }
            }
            chain.push(term.clone());
        }
        // The outermost access is at `depth`, each inner one a level deeper;
        // inner terms are met first.
        let n = chain.len() as u64;
        for (i, t) in chain.iter().enumerate() {
            self.record(t, e, true, depth + (n - 1 - i as u64));
        }
        (true, term)
    }

    fn record(&mut self, term: &T, e: &Expr, pure: bool, depth: u64) {
        if matches!(term, T::Var(_) | T::App(App::VarAt(_) | App::Tuple, _)) {
            return;
        }
        if self.all.insert(term.clone()) {
            if let T::App(app, _) = term {
                self.all_by_app
                    .entry(app.clone())
                    .or_default()
                    .insert(term.clone());
            }
        }
        if pure {
            if let Some(var_depth) = self.var_depth(term, depth) {
                let order = self.pure_terms.len();
                self.pure_terms
                    .entry(term.clone())
                    .or_insert_with(|| (e.clone(), order));
                let score = make_score(term, var_depth);
                let better = self.best_scores.get(term).is_none_or(|old| score < *old);
                if better {
                    self.best_scores.insert(term.clone(), score);
                }
            }
        }
    }

    /// `gather_terms`: the term of `e`, whether it may be a trigger, with
    /// every subterm recorded.
    fn gather(&mut self, e: &Expr, depth: u64) -> (bool, T) {
        let (pure, term) = match &e.kind {
            ExprKind::IntegerConstant(value) => (
                true,
                T::App(
                    App::Const(format!("integer_constant({value:?}):{:?}", e.ty)),
                    Vec::new(),
                ),
            ),
            ExprKind::Lit(lit) => (true, T::App(App::Const(lit_key(*lit, &e.ty)), Vec::new())),
            ExprKind::Read(place) => {
                if place
                    .projections
                    .iter()
                    .all(|p| matches!(p, Projection::Deref))
                {
                    (true, T::Var(place.local))
                } else {
                    return self.place(e, place, false, depth);
                }
            }
            ExprKind::Old(place) => return self.place(e, place, true, depth),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                let mut pure = true;
                let mut terms = Vec::new();
                for arg in args {
                    let (p, t) = self.gather(arg, depth + 1);
                    pure &= p;
                    terms.push(t);
                }
                if (self.q.no_auto_trigger)(*callee) {
                    let app = self.other();
                    (false, T::App(app, terms))
                } else {
                    (pure, T::App(App::Call(*callee, type_args.clone()), terms))
                }
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let mut pure = true;
                let mut terms = Vec::new();
                for field in fields {
                    let (p, t) = self.gather(field, depth + 1);
                    pure &= p;
                    terms.push(t);
                }
                (pure, T::App(App::Ctor(format!("{adt:?}"), *variant), terms))
            }
            ExprKind::IsVariant { base, variant } => {
                let (pure, arg) = self.gather(base, depth + 1);
                let label = format!("{:?}", strip_refs(&base.ty));
                (pure, T::App(App::IsVariant(label, *variant), vec![arg]))
            }
            ExprKind::Tuple(elems) => {
                let mut pure = true;
                let mut terms = Vec::new();
                for elem in elems {
                    let (p, t) = self.gather(elem, depth + 1);
                    pure &= p;
                    terms.push(t);
                }
                (pure, T::App(App::Tuple, terms))
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let (pure, arg) = self.gather(base, depth + 1);
                let label = format!("{:?}", strip_refs(&base.ty));
                (pure, T::App(App::Field(label, *variant, *field), vec![arg]))
            }
            ExprKind::TupleField { base, index } => {
                let (pure, arg) = self.gather(base, depth + 1);
                let label = format!("{:?}", strip_refs(&base.ty));
                (pure, T::App(App::Field(label, 0, *index), vec![arg]))
            }
            ExprKind::Borrow(inner) => return self.gather(inner, depth),
            ExprKind::MutRefCurrent(inner)
            | ExprKind::MutRefFuture(inner)
            | ExprKind::HasResolved(inner) => {
                let (pure, inner) = self.gather(inner, depth + 1);
                let name = match &e.kind {
                    ExprKind::MutRefCurrent(_) => "mut_ref_current",
                    ExprKind::MutRefFuture(_) => "mut_ref_future",
                    _ => "has_resolved",
                };
                (pure, T::App(App::Const(name.into()), vec![inner]))
            }
            ExprKind::MutRefUpdate { reference, value } => {
                let (p, reference) = self.gather(reference, depth + 1);
                let (q, value) = self.gather(value, depth + 1);
                (
                    p && q,
                    T::App(
                        App::Const("mut_ref_update_current".into()),
                        vec![reference, value],
                    ),
                )
            }
            ExprKind::Cast {
                arg,
                kind: CastKind::Exact,
            } if e.ty.int_range() == Some(IntRange::Int) => return self.gather(arg, depth),
            ExprKind::Cast { arg, .. } => {
                let (_, t) = self.gather(arg, 1);
                let app = self.other();
                (false, T::App(app, vec![t]))
            }
            ExprKind::Unary { op, arg, .. } => match op {
                UnOp::Not if on_ints(e) => {
                    let (p, t) = self.gather(arg, 1);
                    (p, T::App(App::BitOp("bitnot"), vec![t]))
                }
                UnOp::Not => {
                    let (_, t) = self.gather(arg, 0);
                    let app = self.other();
                    (false, T::App(app, vec![t]))
                }
                UnOp::Neg => {
                    let (_, t) = self.gather(arg, 1);
                    let app = self.other();
                    (false, T::App(app, vec![t]))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let bitwise = (op.is_bitwise() && on_ints(lhs)) || op.is_shift();
                let d = if op.is_logical() || (*op == BinOp::Eq) || (op.is_bitwise() && !bitwise) {
                    0
                } else {
                    1
                };
                let (p1, t1) = self.gather(lhs, d);
                let (p2, t2) = self.gather(rhs, d);
                if bitwise {
                    let name = match op {
                        BinOp::BitAnd => "bitand",
                        BinOp::BitOr => "bitor",
                        BinOp::BitXor => "bitxor",
                        BinOp::Shl => "shl",
                        _ => "shr",
                    };
                    (p1 && p2, T::App(App::BitOp(name), vec![t1, t2]))
                } else {
                    let app = self.other();
                    (false, T::App(app, vec![t1, t2]))
                }
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let (_, t1) = self.gather(cond, 1);
                let (_, t2) = self.gather(then_expr, 1);
                let (_, t3) = self.gather(else_expr, 1);
                let app = self.other();
                (false, T::App(app, vec![t1, t2, t3]))
            }
            ExprKind::Let { .. }
            | ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::UntriggeredQuant { .. }
            | ExprKind::UntriggeredChoose { .. }
            | ExprKind::ProofInSpec(_)
            | ExprKind::ProofInSpecTail { .. } => {
                let app = self.other();
                (false, T::App(app, Vec::new()))
            }
        };
        self.record(&term, e, pure, depth);
        (pure, term)
    }
}

fn strip_refs(ty: &Ty) -> Ty {
    match ty {
        Ty::Ref { inner, .. } => strip_refs(inner),
        other => other.clone(),
    }
}

fn lit_key(lit: Lit, ty: &Ty) -> String {
    format!("{lit:?}:{ty:?}")
}

fn size(t: &T) -> u64 {
    match t {
        T::Var(_) => 1,
        T::App(_, args) => 1 + args.iter().map(size).sum::<u64>(),
    }
}

fn count(t: &T, pred: &dyn Fn(&App) -> bool) -> u64 {
    match t {
        T::Var(_) => 0,
        T::App(app, args) => {
            u64::from(pred(app)) + args.iter().map(|a| count(a, pred)).sum::<u64>()
        }
    }
}

fn make_score(t: &T, depth: u64) -> Score {
    Score {
        num_operators: count(t, &|app| matches!(app, App::BitOp(_))),
        num_special: 0,
        no_calls: u64::from(count(t, &|app| matches!(app, App::Call(..))) == 0),
        depth,
        size: size(t),
    }
}

/// `structure_matches`: is `term` an instance of `template` for some
/// values of the variables, and may the instance be bigger?
fn structure_matches(vars: &HashSet<LocalId>, template: &T, term: &T) -> (bool, bool) {
    match (template, term) {
        (T::Var(x), T::App(app, _)) if vars.contains(x) && !matches!(app, App::VarAt(_)) => {
            (true, true)
        }
        (T::Var(x), _) if vars.contains(x) => (true, false),
        (T::Var(x), T::Var(y)) => (x == y, false),
        (T::App(a1, args1), T::App(a2, args2)) if a1 == a2 && args1.len() == args2.len() => {
            let mut eq = true;
            let mut bigger = false;
            for (a, b) in args1.iter().zip(args2) {
                let (e, g) = structure_matches(vars, a, b);
                eq &= e;
                bigger |= g;
            }
            (eq, bigger)
        }
        _ => (false, false),
    }
}

fn vars_of(vars: &HashSet<LocalId>, t: &T, out: &mut HashSet<LocalId>) {
    match t {
        T::Var(x) if vars.contains(x) => {
            out.insert(*x);
        }
        T::Var(_) => {}
        T::App(_, args) => {
            for a in args {
                vars_of(vars, a, out);
            }
        }
    }
}

struct Search<'g> {
    vars: &'g HashSet<LocalId>,
    by_var: HashMap<LocalId, Vec<T>>,
    scores: &'g HashMap<T, Score>,
    remaining: Vec<LocalId>,
    accumulated: Vec<T>,
    chosen: Vec<Vec<T>>,
    all: bool,
    steps: u64,
}

impl Search<'_> {
    fn score(&self, trigger: &[T]) -> Score {
        trigger
            .iter()
            .fold(Score::default(), |acc, t| acc.add(self.scores[t]))
    }

    /// `compute_triggers`.
    fn run(&mut self) -> Result<(), ()> {
        if self.remaining.is_empty() {
            let trigger = self.accumulated.clone();
            if self.all {
                let new: HashSet<&T> = trigger.iter().collect();
                let mut old_sub_new = false;
                self.chosen.retain(|old| {
                    let old_set: HashSet<&T> = old.iter().collect();
                    old_sub_new = old_sub_new || old_set.is_subset(&new);
                    !(new.is_subset(&old_set) && new.len() < old_set.len())
                });
                if !old_sub_new {
                    self.chosen.push(trigger);
                }
                return Ok(());
            }
            if let Some(first) = self.chosen.first() {
                if first.len() > trigger.len() {
                    self.chosen.clear();
                } else {
                    let previous = self.score(first);
                    let new = self.score(&trigger);
                    if previous > new {
                        self.chosen.clear();
                    } else if previous < new {
                        return Ok(());
                    }
                }
            }
            self.chosen.push(trigger);
            return Ok(());
        }
        if !self.all {
            if let Some(first) = self.chosen.first() {
                if first.len() <= self.accumulated.len() {
                    return Ok(());
                }
            }
        }
        if self.steps == 0 {
            return Err(());
        }
        self.steps -= 1;
        let x = self.remaining[0];
        let candidates = self.by_var.get(&x).cloned().unwrap_or_default();
        for term in candidates {
            if self.accumulated.contains(&term) {
                continue;
            }
            self.accumulated.push(term.clone());
            let mut covered = HashSet::new();
            vars_of(self.vars, &term, &mut covered);
            let removed: Vec<LocalId> = self
                .remaining
                .iter()
                .copied()
                .filter(|y| covered.contains(y))
                .collect();
            self.remaining.retain(|y| !covered.contains(y));
            let result = self.run();
            for y in removed.into_iter().rev() {
                self.remaining.insert(0, y);
            }
            self.accumulated.pop();
            result?;
        }
        Ok(())
    }
}

/// `triggers_auto.rs`, `build_triggers`.
fn auto_triggers(q: &Quantifier<'_>) -> Result<Vec<Vec<Expr>>, TriggerError> {
    let mut g = Gather {
        q,
        vars: q.vars.iter().copied().collect(),
        all_by_app: HashMap::new(),
        all: HashSet::new(),
        pure_terms: HashMap::new(),
        best_scores: HashMap::new(),
        next_id: 0,
    };
    g.gather(q.body, 0);
    // remove_obvious_potential_loops
    let mut remove = Vec::new();
    for pure in g.pure_terms.keys() {
        if let T::App(app, _) = pure {
            if matches!(app, App::VarAt(_)) {
                continue;
            }
            if let Some(terms) = g.all_by_app.get(app) {
                for term in terms {
                    let (eq, bigger) = structure_matches(&g.vars, pure, term);
                    if eq && bigger {
                        remove.push(pure.clone());
                        break;
                    }
                }
            }
        }
    }
    for pure in remove {
        g.pure_terms.remove(&pure);
    }
    let mut by_var: HashMap<LocalId, Vec<T>> = HashMap::new();
    let mut ordered: Vec<(&T, usize)> = g.pure_terms.iter().map(|(t, (_, n))| (t, *n)).collect();
    ordered.sort_by_key(|(_, n)| *n);
    for (term, _) in &ordered {
        let mut covered = HashSet::new();
        vars_of(&g.vars, term, &mut covered);
        for x in covered {
            by_var.entry(x).or_default().push((*term).clone());
        }
    }
    let mut search = Search {
        vars: &g.vars,
        by_var,
        scores: &g.best_scores,
        remaining: q.vars.to_vec(),
        accumulated: Vec::new(),
        chosen: Vec::new(),
        all: q.auto == AutoMode::All,
        steps: 10_000,
    };
    if search.run().is_err() {
        return Err(TriggerError {
            span: q.span,
            message: MSG_TOO_LARGE.to_string(),
        });
    }
    let mut chosen = search.chosen;
    for trigger in &mut chosen {
        trigger.sort_by_key(|t| g.pure_terms[t].1);
    }
    chosen.sort_by_key(|trigger| {
        trigger
            .iter()
            .map(|t| g.pure_terms[t].1)
            .collect::<Vec<_>>()
    });
    chosen.dedup();
    if chosen.is_empty() {
        return Err(TriggerError {
            span: q.span,
            message: MSG_NO_TRIGGERS.to_string(),
        });
    }
    Ok(chosen
        .into_iter()
        .map(|trigger| {
            trigger
                .into_iter()
                .map(|t| g.pure_terms[&t].0.clone())
                .collect()
        })
        .collect())
}
