//! Obligation collection functions for proof-session-backed verification state.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from verify_macro.rs as part of #1740 (god module splitting).
//! Contains all `collect_*` functions and `track_local_variable` that build
//! up the verification context during proof function expansion.

mod collect;
mod let_bindings;
mod quantifier_guard;
mod variables;

#[cfg(test)]
pub(crate) use collect::clear_pre_built_exprs;
pub use collect::{
    cache_pre_built_expr, collect_ext_eq_obligation, collect_obligation, collect_obligation_expr,
    collect_solver_mode_obligation, collect_solver_mode_obligation_expr, collect_typed_obligation,
    total_obligations_collected,
};
pub(crate) use collect::{
    obligations_dropped_count, record_obligation_drop, reset_obligations_dropped,
    set_obligations_dropped_count, take_pre_built_expr, translate_rust_to_smt,
};
pub use let_bindings::{
    collect_final_value, collect_final_value_deref, collect_let_binding,
    collect_let_binding_runtime_value, collect_let_binding_runtime_value_from_ref,
    collect_let_binding_runtime_value_i128, collect_let_binding_runtime_value_u128,
    collect_old_value, collect_old_value_deref, collect_symbolic_assume_expr,
    collect_symbolic_let_binding_expr,
};
use quantifier_guard::parse_solver_mode;
pub use quantifier_guard::{
    register_quantifier_bound_var, unregister_quantifier_bound_var, QuantifierBoundVarGuard,
};
pub use variables::{
    collect_variable, collect_variable_from_ref, collect_variable_runtime, lookup_var_type,
    register_counterexample_display, register_prophecy_local, register_tracked_param,
    track_local_variable,
};

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "../obligation_collection_proof_tests.rs"]
mod proof_tests;

#[cfg(test)]
#[path = "../obligation_collection_runtime_value_tests.rs"]
mod runtime_value_tests;
