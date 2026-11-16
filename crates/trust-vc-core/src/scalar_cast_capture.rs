//! Bounded data read from the actual typed encoder, never proof authority.
//!
//! The collector belongs to one verification request. It changes no solver
//! input, policy, budget or retry. A refused/incomplete capture cannot produce
//! a mathematical binding; ordinary native verification keeps its verdict.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use ay_dpll::api::{Solver, Sort, Term, TermKind};

use crate::ir::TrustVcType;

const MAX_ROWS: usize = 4096;
const MAX_BYTES: usize = 8 * 1024 * 1024;
const MAX_TERM_OCCURRENCES: usize = 512;
const MAX_SYMBOL_BYTES: usize = 4096;
pub(crate) const MAX_ROOT_BYTES: usize = 16 * 1024;

/// Untrusted data from one real cast call, before the solver is dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCastEmission {
    pub declared_source: TrustVcType,
    pub effective_source: TrustVcType,
    pub destination: TrustVcType,
    pub operand_variable: Option<String>,
    pub operand_term: String,
    pub operand_sort: Sort,
    pub operand_bindings: Vec<(String, Sort)>,
    pub result_term: String,
    pub result_sort: Sort,
    pub result_bindings: Vec<(String, Sort)>,
}

/// Every final guarded check returned by this same encoding call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCastDomainCheck {
    pub label: String,
    pub predicate: String,
    pub bindings: Vec<(String, Sort)>,
}

/// Which existing encoder entry produced this exact term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarCastEncodingPhase {
    Condition,
    Refutation,
    /// The returned condition plus final guarded side conditions. Assumption
    /// encoding asserts this returned term only after checking its domains.
    CheckedCondition,
}

/// One actual typed condition and all its casts and final domain checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCastCondition {
    pub phase: ScalarCastEncodingPhase,
    pub original_typed_root: crate::ir::TrustVcExpr,
    pub prepared_typed_root: crate::ir::TrustVcExpr,
    pub result_term: String,
    pub result_sort: Sort,
    pub result_bindings: Vec<(String, Sort)>,
    pub casts: Vec<ScalarCastEmission>,
    pub domain_checks: Vec<ScalarCastDomainCheck>,
    /// Existing constant-fold verdicts: true means OVERFLOW, not a valid domain.
    pub constant_overflow_verdicts: Vec<(String, bool)>,
}

#[derive(Debug, Default)]
struct State {
    closed: bool,
    active: usize,
    failure: Option<String>,
    bytes: usize,
    conditions: Vec<ScalarCastCondition>,
}

/// A request-owned observational sink, shared by its existing encoder workers.
#[derive(Debug, Clone, Default)]
pub struct ScalarCastCapture(Arc<Mutex<State>>);

/// A completed capture is data only, not a verifier or a kernel acceptance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCastCaptureData {
    conditions: Vec<ScalarCastCondition>,
}

impl ScalarCastCaptureData {
    pub fn conditions(&self) -> &[ScalarCastCondition] {
        &self.conditions
    }
}

impl ScalarCastCapture {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn begin(&self) -> Option<ActiveCapture> {
        let mut state = self.0.lock().ok()?;
        if state.closed || state.failure.is_some() {
            return None;
        }
        state.active += 1;
        Some(ActiveCapture(self.clone()))
    }

    pub(crate) fn refuse(&self, reason: impl Into<String>) {
        if let Ok(mut state) = self.0.lock() {
            if state.failure.is_none() {
                state.failure = Some(reason.into());
            }
            state.conditions.clear();
        }
    }

    pub(crate) fn record(&self, condition: ScalarCastCondition) {
        let Ok(encoded) = bounded_debug(&condition, MAX_BYTES) else {
            self.refuse("cast observation exceeds its data bound");
            return;
        };
        if let Ok(mut state) = self.0.lock() {
            if state.closed || state.failure.is_some() {
                return;
            }
            if state.conditions.len() >= MAX_ROWS
                || encoded.len() > MAX_BYTES.saturating_sub(state.bytes)
            {
                state.failure = Some("cast observation exceeds its fixed data bound".into());
                state.conditions.clear();
                return;
            }
            state.bytes += encoded.len();
            state.conditions.push(condition);
        }
    }

    /// Call after the existing synchronous verifier has joined its workers.
    /// A second completion, poisoned sink or any refused row fails closed.
    pub fn finish(&self) -> Result<ScalarCastCaptureData, String> {
        let mut state = self
            .0
            .lock()
            .map_err(|_| "cast observation lock poisoned")?;
        if state.closed {
            return Err("cast observation already completed".into());
        }
        state.closed = true;
        if state.active != 0 {
            return Err("cast observation has active encoders".into());
        }
        if let Some(reason) = &state.failure {
            return Err(reason.clone());
        }
        Ok(ScalarCastCaptureData {
            conditions: std::mem::take(&mut state.conditions),
        })
    }
}

/// Read only bounded Bool/BV1..128 syntax through AY's existing term API.
/// Traversing occurrences bounds the printer even when a small DAG expands
/// exponentially. This is a resource walk, not an SMT evaluator or decoder.
pub(crate) struct ActualTerm {
    pub text: String,
    pub sort: Sort,
    pub bindings: Vec<(String, Sort)>,
}

pub(crate) fn actual_term(solver: &Solver, root: Term) -> Result<ActualTerm, String> {
    let mut pending = vec![root];
    let mut occurrences = 0;
    let mut symbol_bytes = 0;
    let mut bindings = BTreeMap::new();
    while let Some(term) = pending.pop() {
        occurrences += 1;
        if occurrences > MAX_TERM_OCCURRENCES {
            return Err("cast term exceeds the occurrence bound".into());
        }
        match solver.term_sort(term) {
            Sort::Bool => {}
            Sort::BitVec(sort) if sort.width > 0 && sort.width <= 128 => {}
            _ => return Err("cast mathematical binding supports actual Bool/BV terms only".into()),
        }
        let count = solver
            .try_term_child_count(term)
            .map_err(|error| error.to_string())?;
        if count > MAX_TERM_OCCURRENCES.saturating_sub(occurrences + pending.len()) {
            return Err("cast term exceeds the child bound".into());
        }
        match solver.term_kind(term) {
            TermKind::Forall | TermKind::Exists | TermKind::Let => {
                return Err("cast binding requires a quantifier-free scalar term".into())
            }
            TermKind::Var { name } => {
                let sort = solver.term_sort(term);
                if bindings
                    .insert(name.clone(), sort.clone())
                    .is_some_and(|old| old != sort)
                {
                    return Err("cast term binds one lexical name at conflicting sorts".into());
                }
                symbol_bytes += name.len();
                if symbol_bytes > MAX_SYMBOL_BYTES {
                    return Err("cast term exceeds the symbol bound".into());
                }
            }
            TermKind::App { name, .. } => {
                symbol_bytes += name.len();
                if symbol_bytes > MAX_SYMBOL_BYTES {
                    return Err("cast term exceeds the symbol bound".into());
                }
            }
            _ => {}
        }
        pending.extend(solver.term_children(term));
    }
    let text = solver
        .format_term_checked(root)
        .ok_or("cast term rendering refused")?;
    if text.len() > MAX_ROOT_BYTES {
        return Err("cast term exceeds the printed bound".into());
    }
    Ok(ActualTerm {
        text,
        sort: solver.term_sort(root),
        bindings: bindings.into_iter().collect(),
    })
}

/// Keep the original typed value, using the existing visitor and Debug
/// implementation only to bound copying. No wire language is introduced.
pub(crate) fn typed_root(value: &crate::ir::TrustVcExpr) -> Result<crate::ir::TrustVcExpr, String> {
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
    #[derive(Default)]
    struct Bound {
        depth: usize,
        count: usize,
        refused: bool,
    }
    impl TrustVcExprVisitor for Bound {
        fn visit_expr(&mut self, expr: &crate::ir::TrustVcExpr) {
            self.count += 1;
            if self.depth >= 64 || self.count > MAX_TERM_OCCURRENCES {
                self.refused = true;
                return;
            }
            use crate::ir::TrustVcExpr as E;
            let scalar = |ty: &TrustVcType| {
                matches!(
                    ty,
                    TrustVcType::Bool
                        | TrustVcType::Int { width: 1..=128 }
                        | TrustVcType::Uint { width: 1..=128 }
                )
            };
            let supported = match expr {
                E::BoolLit(_)
                | E::Not(_)
                | E::Neg(_)
                | E::Compare { .. }
                | E::Logic { .. }
                | E::Implies { .. } => true,
                E::Var { ty, .. }
                | E::IntLit { ty, .. }
                | E::Arith { ty, .. }
                | E::Ite { ty, .. } => scalar(ty),
                E::Cast { from_ty, to_ty, .. } => scalar(from_ty) && scalar(to_ty),
                _ => false,
            };
            if !supported {
                self.refused = true;
                return;
            }
            self.depth += 1;
            walk_expr(self, expr);
            self.depth -= 1;
        }
    }
    let mut bound = Bound::default();
    bound.visit_expr(value);
    if bound.refused {
        return Err("typed cast root exceeds its tree bound".into());
    }
    bounded_debug(value, MAX_ROOT_BYTES)?;
    Ok(value.clone())
}

fn bounded_debug(value: &impl std::fmt::Debug, limit: usize) -> Result<String, String> {
    use std::fmt::Write;
    struct Bounded {
        text: String,
        limit: usize,
    }
    impl Write for Bounded {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            if text.len() > self.limit.saturating_sub(self.text.len()) {
                return Err(std::fmt::Error);
            }
            self.text.push_str(text);
            Ok(())
        }
    }
    let mut out = Bounded {
        text: String::new(),
        limit,
    };
    write!(&mut out, "{value:?}").map_err(|_| "cast observation exceeds its data bound")?;
    Ok(out.text)
}

pub(crate) struct ActiveCapture(ScalarCastCapture);
impl Drop for ActiveCapture {
    fn drop(&mut self) {
        if let Ok(mut state) = self.0 .0.lock() {
            state.active -= 1;
        }
    }
}
