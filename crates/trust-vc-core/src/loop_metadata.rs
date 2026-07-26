//! Loop metadata registration for auto-inferred loop invariants.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides a thread-local loop context stack for the proc-macro fold pass.
//! When `#[trust_vc::proof]` expansion detects a `for i in lo..hi` loop, it
//! emits `push_loop_context()` / `pop_loop_context()` calls around the loop
//! body. Any `invariant!()` collected within this scope auto-inherits the
//! loop's modified-variable set and guard condition.
//!
//! Part of #2502 (loop invariant inference for range loops).

use std::cell::RefCell;

struct LoopContext {
    modified_vars: Vec<String>,
    guard: String,
}

thread_local! {
    static LOOP_CONTEXT_STACK: RefCell<Vec<LoopContext>> = const { RefCell::new(Vec::new()) };
}

/// Pushes a loop context onto the thread-local stack.
///
/// Called by proc-macro generated code BEFORE a `for i in lo..hi` loop body.
/// All `invariant!()` obligations collected while this context is active will
/// inherit the specified `modified_vars` and `guard`.
#[doc(hidden)]
pub fn push_loop_context(modified_vars: Vec<String>, guard: String) {
    LOOP_CONTEXT_STACK.with(|stack| {
        if let Ok(mut s) = stack.try_borrow_mut() {
            s.push(LoopContext {
                modified_vars,
                guard,
            });
        }
    });
}

/// Pops the most recent loop context from the thread-local stack.
///
/// Called by proc-macro generated code AFTER a `for i in lo..hi` loop body.
#[doc(hidden)]
pub fn pop_loop_context() {
    LOOP_CONTEXT_STACK.with(|stack| {
        if let Ok(mut s) = stack.try_borrow_mut() {
            s.pop();
        }
    });
}

/// Returns the current loop context (modified vars + guard) if one is active.
///
/// Called by `push_obligation` to auto-apply loop metadata when collecting
/// `LoopInvariant` or `InvariantExceptBreak` obligations.
pub(crate) fn current_loop_context() -> Option<(Vec<String>, String)> {
    LOOP_CONTEXT_STACK.with(|stack| {
        stack.try_borrow().ok().and_then(|s| {
            s.last()
                .map(|ctx| (ctx.modified_vars.clone(), ctx.guard.clone()))
        })
    })
}

/// RAII guard for loop context push/pop.
///
/// Pushes a loop context on creation and pops it on drop. This prevents
/// stale context leaks when a panic occurs between push and pop.
/// Matches existing RAII patterns: QuantifierBoundVarGuard, BroadcastGuard,
/// ContextGuard.
///
/// Part of #2523 (Phase 2 P5).
#[doc(hidden)]
pub struct LoopContextGuard {
    _private: (),
}

impl LoopContextGuard {
    /// Creates a new guard, pushing the loop context onto the stack.
    pub fn new(modified_vars: Vec<String>, guard: String) -> Self {
        push_loop_context(modified_vars, guard);
        Self { _private: () }
    }
}

impl Drop for LoopContextGuard {
    fn drop(&mut self) {
        pop_loop_context();
    }
}

/// Clears the loop context stack. Called from `clear_all_thread_locals()`.
pub(crate) fn clear_loop_context_stack() {
    LOOP_CONTEXT_STACK.with(|stack| {
        if let Ok(mut s) = stack.try_borrow_mut() {
            s.clear();
        }
    });
}

/// Returns the current depth of the loop context stack. Test-only.
#[cfg(test)]
pub(crate) fn loop_context_stack_depth() -> usize {
    LOOP_CONTEXT_STACK.with(|stack| stack.try_borrow().map(|s| s.len()).unwrap_or(0))
}
