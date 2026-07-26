// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::ir::TrustVcType;
use crate::proof_session::try_with_session_mut;
use crate::vc::SolverMode;

/// Registers a quantifier-bound variable's type in local_var_types.
/// Prefer `QuantifierBoundVarGuard` which provides RAII cleanup.
pub fn register_quantifier_bound_var(name: String, ty: TrustVcType) {
    // Graceful skip on borrow conflict: bound var not registered -> quantifier
    // encoding may fail, but no crash. Part of #1955.
    let _ = try_with_session_mut(|s| {
        s.local_var_types.insert(name, ty);
    });
}

/// Removes a quantifier-bound variable from local_var_types.
pub fn unregister_quantifier_bound_var(name: &str) {
    // Graceful skip on borrow conflict: bound var not removed -> stale entry
    // until next clear_all_thread_locals(). Part of #1955.
    let _ = try_with_session_mut(|s| {
        s.local_var_types.remove(name);
    });
}

/// RAII guard: unregisters quantifier-bound variables on drop (including panic unwind).
#[must_use = "QuantifierBoundVarGuard unregisters vars on drop - dropping immediately would register then instantly unregister"]
#[derive(Default)]
pub struct QuantifierBoundVarGuard {
    previous: Vec<(String, Option<TrustVcType>)>,
}

impl QuantifierBoundVarGuard {
    pub fn new() -> Self {
        Self {
            previous: Vec::new(),
        }
    }

    pub fn register(&mut self, name: String, ty: TrustVcType) {
        let previous = try_with_session_mut(|s| s.local_var_types.insert(name.clone(), ty))
            .ok()
            .flatten();
        self.previous.push((name, previous));
    }
}

impl Drop for QuantifierBoundVarGuard {
    fn drop(&mut self) {
        for (name, previous) in self.previous.drain(..).rev() {
            let _ = try_with_session_mut(|s| match previous {
                Some(ty) => {
                    s.local_var_types.insert(name, ty);
                }
                None => {
                    s.local_var_types.remove(&name);
                }
            });
        }
    }
}

pub(super) fn parse_solver_mode(solver_mode: &str) -> SolverMode {
    match solver_mode {
        "nonlinear_arith" => SolverMode::NonlinearArith,
        "bit_vector" => SolverMode::BitVector,
        "compute" => SolverMode::Compute,
        _ => SolverMode::Default,
    }
}
