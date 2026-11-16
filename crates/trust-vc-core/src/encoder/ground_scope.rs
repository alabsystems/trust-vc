//! Owned lifetimes for ground-demand template binders.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_dpll::api::{Solver, Term};

struct Frame {
    bound: Vec<Term>,
    active: Arc<AtomicBool>,
}

/// Only live frames contribute binders. Expired storage is pruned before the
/// next scope or demand; it never contributes a ground seed or changes a pool's
/// revision/flush state.
#[derive(Default)]
pub(super) struct TemplateScopes {
    frames: Vec<Frame>,
}

/// An owned identity for the original frame, independent of a parser's optional
/// pool attachment. Unwinding deactivates this same frame without recovering a
/// mutable reference from the callback or changing its panic payload.
pub(super) struct TemplateScope {
    active: Arc<AtomicBool>,
}

impl TemplateScopes {
    pub(super) fn enter(&mut self, solver: &Solver, bound: &[Term]) -> TemplateScope {
        // Keep the existing same-solver validation before installing any state.
        for &term in bound {
            let _ = solver.term_children(term);
        }
        self.prune();
        let active = Arc::new(AtomicBool::new(true));
        self.frames.push(Frame {
            bound: bound.to_vec(),
            active: Arc::clone(&active),
        });
        TemplateScope { active }
    }

    pub(super) fn bound_terms(&mut self) -> HashSet<Term> {
        self.prune();
        self.frames
            .iter()
            .flat_map(|frame| &frame.bound)
            .copied()
            .collect()
    }

    fn prune(&mut self) {
        self.frames
            .retain(|frame| frame.active.load(Ordering::Acquire));
    }

    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.frames
            .iter()
            .all(|frame| !frame.active.load(Ordering::Acquire))
    }
}

impl Drop for TemplateScope {
    fn drop(&mut self) {
        self.active.store(false, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ay_dpll::api::{Logic, Solver, Sort};

    use crate::encoder::{ground_pool::GroundTermPool, AstExpressionParser};
    use crate::ir::{TrustVcExpr, TrustVcType};

    #[test]
    fn parser_unwind_restores_the_original_pool_after_detachment() {
        let mut solver = Solver::try_new(Logic::All).expect("solver");
        let binder = solver.declare_const("binder", Sort::bitvec(32));
        let mut pool = GroundTermPool::new();
        let variables = HashMap::new();
        let mut lengths = HashMap::new();
        let types = HashMap::new();
        let functions = HashMap::new();
        {
            let mut parser =
                AstExpressionParser::new(&mut solver, &variables, &mut lengths, &types, &functions);
            parser.ground_pool = Some(&mut pool);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                parser.with_ground_template_scope(&[binder], |parser| {
                    parser.ground_pool = None;
                    panic!("original callback panic");
                });
            }));
            let payload = result.expect_err("the callback must unwind");
            assert_eq!(
                payload.downcast_ref::<&str>(),
                Some(&"original callback panic")
            );
            assert!(parser.ground_pool.is_none());
        }
        assert!(pool.template_scopes.is_empty());
        assert!(
            pool.register_expr_scoped(
                &solver,
                "actual_caller",
                vec![binder],
                vec![TrustVcExpr::Var {
                    name: "binder".into(),
                    ty: TrustVcType::Int { width: 32 },
                }],
                binder,
            ),
            "the original pool must accept actual caller demand after unwinding"
        );
        assert_eq!(pool.ground_term_count(), 1);
    }
}
