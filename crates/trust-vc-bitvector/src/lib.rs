//! The isolated, explicitly typed bit-vector query language.
//!
//! It carries no ambient hypotheses, function definitions or import authority.
//! Integer extension/comparison choices are explicit so the ordinary Int query
//! language cannot silently reinterpret a modular operation.

/// Exact signed magnitude; no machine truncation occurs until the literal is
/// encoded at its explicitly declared bit width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntLit {
    pub negative: bool,
    pub magnitude: u128,
}

use std::collections::{HashMap, HashSet};

pub mod congruence;
pub mod integer;

/// Which architecture cases an isolated assertion must establish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Architecture {
    /// Verus's default: establish each architecture-dependent assertion twice.
    Either32Or64,
    /// An explicit source/driver architecture setting.
    Exactly(u32),
}

impl Architecture {
    /// Actual finite architecture cases, refusing malformed settings.
    pub fn cases(self) -> Result<&'static [u32], &'static str> {
        match self {
            Self::Either32Or64 => Ok(&[32, 64]),
            Self::Exactly(32) => Ok(&[32]),
            Self::Exactly(64) => Ok(&[64]),
            Self::Exactly(_) => Err("invalid bit-vector architecture"),
        }
    }
}

/// SMT sorts; signedness belongs to the operation, not to the bit-vector sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Bits(u32),
}

/// Exact native bit-vector operations. Shift operands have equal widths here;
/// the pinned translation's extension/truncation occurs before this node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Not,
    And,
    Or,
    Xor,
    Implies,
    BitNot,
    BitAnd,
    BitOr,
    BitXor,
    Add,
    Sub,
    Mul,
    UDiv,
    URem,
    SDiv,
    SRem,
    Eq,
    ULt,
    ULe,
    SLt,
    SLe,
    Shl,
    LShr,
    AShr,
    ZeroExtend(u32),
    SignExtend(u32),
    Extract { high: u32, low: u32 },
}

/// An isolated formula. Variables are exactly its explicit declarations or
/// lexical binders, never names resolved from an enclosing solver context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Immutable sharing prevents nested arithmetic construction from copying
    /// whole operand trees. Admission still charges EVERY traversed edge.
    Shared(std::sync::Arc<Term>),
    Euclidean(std::sync::Arc<integer::Euclidean>),
    Bool(bool),
    Bits {
        value: IntLit,
        width: u32,
    },
    Var(String),
    App {
        op: Op,
        args: Vec<Term>,
    },
    If {
        condition: Box<Term>,
        then_term: Box<Term>,
        else_term: Box<Term>,
    },
    Let {
        name: String,
        value: Box<Term>,
        body: Box<Term>,
    },
    Quant {
        forall: bool,
        binders: Vec<(String, Sort)>,
        body: Box<Term>,
        /// Explicit source multi-patterns, under these same lexical binders.
        /// The outer list contains alternatives; each inner list must cover
        /// every binder and retain every actual typed application.
        triggers: Vec<Vec<Term>>,
    },
}

/// One isolated goal under ONLY explicitly supplied requires clauses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    pub variables: Vec<(String, Sort)>,
    pub requires: Vec<Term>,
    pub goal: Term,
    pub architecture: u32,
}

const WORK: usize = 200_000;
const DEPTH: usize = 512;
const MAX_WIDTH: u32 = 65_536;

fn name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 128
        && name
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
}
fn sort(sort: Sort) -> bool {
    matches!(sort, Sort::Bool) || matches!(sort, Sort::Bits(w) if w > 0 && w <= MAX_WIDTH)
}

impl Query {
    /// Type-check the entire independent query before a solver is created.
    /// The work/depth bounds cover repeated edges and every lexical binder.
    pub fn validate(&self) -> Result<(), &'static str> {
        if !matches!(self.architecture, 32 | 64) {
            return Err("invalid bit-vector architecture");
        }
        let mut work = WORK;
        let mut scope = HashMap::new();
        for (n, s) in &self.variables {
            charge(&mut work, n.len().saturating_add(1))?;
            sort_work(&mut work, *s)?;
            if !name(n) || !sort(*s) || scope.insert(n.as_str(), *s).is_some() {
                return Err("invalid or duplicate bit-vector variable");
            }
        }
        for requirement in &self.requires {
            if term_sort(requirement, &mut scope, &mut work, 0)? != Sort::Bool {
                return Err("non-Boolean bit-vector requirement");
            }
        }
        if term_sort(&self.goal, &mut scope, &mut work, 0)? != Sort::Bool {
            return Err("non-Boolean bit-vector goal");
        }
        Ok(())
    }
}

fn charge(work: &mut usize, amount: usize) -> Result<(), &'static str> {
    *work = work
        .checked_sub(amount)
        .ok_or("bit-vector query work exhausted")?;
    Ok(())
}

fn sort_work(work: &mut usize, sort: Sort) -> Result<(), &'static str> {
    if !self::sort(sort) {
        return Err("invalid bit-vector sort");
    }
    // Width-dependent construction (not only AST node count) is admitted
    // before native constants/extensions can allocate their dense payload.
    let units = match sort {
        Sort::Bool => 1,
        Sort::Bits(width) => (width as usize).div_ceil(64),
    };
    charge(work, units)
}

fn term_sort<'a>(
    term: &'a Term,
    scope: &mut HashMap<&'a str, Sort>,
    work: &mut usize,
    depth: usize,
) -> Result<Sort, &'static str> {
    charge(work, 1)?;
    if depth > DEPTH {
        return Err("bit-vector query depth exhausted");
    }
    let next = depth + 1;
    match term {
        Term::Shared(term) => term_sort(term, scope, work, next),
        Term::Euclidean(operation) => term_sort(operation.expanded(), scope, work, next),
        Term::Bool(_) => Ok(Sort::Bool),
        Term::Bits { width, .. } => {
            let s = Sort::Bits(*width);
            sort_work(work, s)?;
            if sort(s) {
                Ok(s)
            } else {
                Err("invalid bit-vector literal width")
            }
        }
        Term::Var(n) => {
            charge(work, n.len().saturating_add(1))?;
            if !name(n) {
                return Err("invalid bit-vector variable name");
            }
            scope
                .get(n.as_str())
                .copied()
                .ok_or("undeclared bit-vector variable")
        }
        Term::If {
            condition,
            then_term,
            else_term,
        } => {
            if term_sort(condition, scope, work, next)? != Sort::Bool {
                return Err("non-Boolean bit-vector condition");
            }
            let a = term_sort(then_term, scope, work, next)?;
            let b = term_sort(else_term, scope, work, next)?;
            if a == b {
                Ok(a)
            } else {
                Err("bit-vector conditional sort mismatch")
            }
        }
        Term::Let {
            name: n,
            value,
            body,
        } => {
            charge(work, n.len().saturating_add(1))?;
            if !name(n) {
                return Err("invalid bit-vector binder name");
            }
            let s = term_sort(value, scope, work, next)?;
            let old = scope.insert(n, s);
            let result = term_sort(body, scope, work, next);
            if let Some(old) = old {
                scope.insert(n, old);
            } else {
                scope.remove(n.as_str());
            }
            result
        }
        Term::Quant {
            binders,
            body,
            triggers,
            ..
        } => {
            let mut saved: Vec<(&str, Option<Sort>)> = Vec::new();
            let mut names = HashSet::new();
            for (n, s) in binders {
                charge(work, n.len().saturating_add(1))?;
                sort_work(work, *s)?;
                if !name(n) || !sort(*s) || !names.insert(n.as_str()) {
                    for (prior, old) in saved.into_iter().rev() {
                        if let Some(old) = old {
                            scope.insert(prior, old);
                        } else {
                            scope.remove(prior);
                        }
                    }
                    return Err("invalid or duplicate bit-vector binder");
                }
                saved.push((n.as_str(), scope.insert(n, *s)));
            }
            let result = (|| {
                if binders.is_empty() || triggers.is_empty() {
                    return Err("a bit-vector quantifier without binders or triggers");
                }
                for group in triggers {
                    charge(work, group.len().saturating_add(1))?;
                    if group.is_empty() {
                        return Err("an empty bit-vector trigger group");
                    }
                    let mut covered = HashSet::new();
                    for pattern in group {
                        term_sort(pattern, scope, work, next)?;
                        trigger_application(pattern, work, next)?;
                        let mut mentioned = HashSet::new();
                        trigger_variables(pattern, &mut mentioned, work, next)?;
                        let mut mentions_current = false;
                        for name in mentioned {
                            charge(work, name.len().saturating_add(1))?;
                            if names.contains(name) {
                                covered.insert(name);
                                mentions_current = true;
                            }
                        }
                        if !mentions_current {
                            return Err("a bit-vector trigger without a current bound variable");
                        }
                    }
                    for name in &names {
                        charge(work, name.len().saturating_add(1))?;
                        if !covered.contains(name) {
                            return Err(
                                "a bit-vector trigger group that does not cover every binder",
                            );
                        }
                    }
                }
                if term_sort(body, scope, work, next)? != Sort::Bool {
                    return Err("non-Boolean quantified bit-vector body");
                }
                Ok(Sort::Bool)
            })();
            for (n, old) in saved.into_iter().rev() {
                if let Some(old) = old {
                    scope.insert(n, old);
                } else {
                    scope.remove(n);
                }
            }
            result
        }
        Term::App { op, args } => {
            use Op::*;
            let unary = matches!(
                op,
                Not | BitNot | ZeroExtend(_) | SignExtend(_) | Extract { .. }
            );
            if args.len() != if unary { 1 } else { 2 } {
                return Err("bit-vector operator arity mismatch");
            }
            let a = term_sort(&args[0], scope, work, next)?;
            if unary {
                return match (*op, a) {
                    (Not, Sort::Bool) => Ok(Sort::Bool),
                    (BitNot, Sort::Bits(_)) => Ok(a),
                    (ZeroExtend(extra) | SignExtend(extra), Sort::Bits(w)) => {
                        let w = w.checked_add(extra).ok_or("bit-vector width overflow")?;
                        sort_work(work, Sort::Bits(w))?;
                        if sort(Sort::Bits(w)) {
                            Ok(Sort::Bits(w))
                        } else {
                            Err("bit-vector width exhausted")
                        }
                    }
                    (Extract { high, low }, Sort::Bits(w)) if low <= high && high < w => {
                        Ok(Sort::Bits(high - low + 1))
                    }
                    _ => Err("bit-vector unary operand sort mismatch"),
                };
            }
            let b = term_sort(&args[1], scope, work, next)?;
            if a != b {
                return Err("bit-vector binary operand sort mismatch");
            }
            sort_work(work, a)?;
            match (*op, a) {
                (Eq, _) => Ok(Sort::Bool),
                (And | Or | Xor | Implies, Sort::Bool) => Ok(Sort::Bool),
                (ULt | ULe | SLt | SLe, Sort::Bits(_)) => Ok(Sort::Bool),
                (
                    BitAnd | BitOr | BitXor | Add | Sub | Mul | UDiv | URem | SDiv | SRem | Shl
                    | LShr | AShr,
                    Sort::Bits(_),
                ) => Ok(a),
                _ => Err("bit-vector binary operand sort mismatch"),
            }
        }
    }
}

/// Shared wrappers preserve representation, not an application of their own.
/// Bare variables/constants, conditionals and lexical binders cannot become
/// patterns merely because they contain an application elsewhere.
fn trigger_application(term: &Term, work: &mut usize, depth: usize) -> Result<(), &'static str> {
    charge(work, 1)?;
    if depth > DEPTH {
        return Err("bit-vector trigger depth exhausted");
    }
    match term {
        Term::Shared(inner) => trigger_application(inner, work, depth + 1),
        Term::Euclidean(operation) => trigger_application(operation.expanded(), work, depth + 1),
        Term::App { .. } => Ok(()),
        _ => Err("a bit-vector trigger that is not a typed application"),
    }
}

fn trigger_variables<'a>(
    term: &'a Term,
    found: &mut HashSet<&'a str>,
    work: &mut usize,
    depth: usize,
) -> Result<(), &'static str> {
    charge(work, 1)?;
    if depth > DEPTH {
        return Err("bit-vector trigger depth exhausted");
    }
    match term {
        Term::Shared(inner) => trigger_variables(inner, found, work, depth + 1),
        Term::Euclidean(operation) => {
            trigger_variables(operation.expanded(), found, work, depth + 1)
        }
        Term::Bool(_) | Term::Bits { .. } => Ok(()),
        Term::Var(name) => {
            charge(work, name.len().saturating_add(1))?;
            found.insert(name);
            Ok(())
        }
        Term::App { args, .. } => {
            for arg in args {
                trigger_variables(arg, found, work, depth + 1)?;
            }
            Ok(())
        }
        Term::If {
            condition,
            then_term,
            else_term,
        } => {
            trigger_variables(condition, found, work, depth + 1)?;
            trigger_variables(then_term, found, work, depth + 1)?;
            trigger_variables(else_term, found, work, depth + 1)
        }
        Term::Let { .. } | Term::Quant { .. } => {
            Err("a lexical binder inside a bit-vector trigger")
        }
    }
}
