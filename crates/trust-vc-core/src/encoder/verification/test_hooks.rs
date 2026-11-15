// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deterministic test hooks for verification-path reliability tests.
//!
//! Centralized here so split verification modules can share the same thread-
//! local hooks without depending on `assertion.rs` for test-only state.

// Thread-local to prevent cross-test interference under parallel execution
// (#1972). Hooks stay test-only; non-test builds use the accessor fallbacks.
#[cfg(test)]
thread_local! {
    pub(in crate::encoder) static FORCE_CONFIRMATION_DISAGREE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_BV_TIMEOUT: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_CONFIRMATION_PANIC: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_EXTENDED_RETRY_SUCCESS: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_OVERFLOW_PRECHECK_DEMOTION: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_EMPTY_MODEL: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_ENCODE_CONDITION_PANIC: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_TRUST_VC_EXPR_ENCODE_PANIC: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_SCOPE_POP_FAILURE_ONCE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static FORCE_SOLVE_PANIC_ONCE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    pub(in crate::encoder) static SETUP_FROM_PREPARED_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    pub(in crate::encoder) static PER_ASSERTION_PRUNE_PLAN_BUILD_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    pub(in crate::encoder) static SHARED_BV_REUSE_ATTEMPT_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(in crate::encoder) fn force_bv_timeout_enabled() -> bool {
    FORCE_BV_TIMEOUT.with(|flag| flag.get())
}

#[cfg(not(test))]
pub(in crate::encoder) fn force_bv_timeout_enabled() -> bool {
    false
}

#[cfg(test)]
pub(in crate::encoder) fn force_extended_retry_success_enabled() -> bool {
    FORCE_EXTENDED_RETRY_SUCCESS.with(|flag| flag.get())
}

#[cfg(not(test))]
pub(in crate::encoder) fn force_extended_retry_success_enabled() -> bool {
    false
}

#[cfg(test)]
pub(in crate::encoder) fn force_empty_model_enabled() -> bool {
    FORCE_EMPTY_MODEL.with(|flag| flag.get())
}

#[cfg(not(test))]
pub(in crate::encoder) fn force_empty_model_enabled() -> bool {
    false
}

#[cfg(test)]
pub(in crate::encoder) fn take_forced_encode_condition_panic() -> bool {
    FORCE_ENCODE_CONDITION_PANIC.with(|flag| {
        let enabled = flag.get();
        flag.set(false);
        enabled
    })
}

#[cfg(test)]
pub(in crate::encoder) fn take_forced_trust_vc_expr_encode_panic() -> bool {
    FORCE_TRUST_VC_EXPR_ENCODE_PANIC.with(|flag| {
        let enabled = flag.get();
        flag.set(false);
        enabled
    })
}

#[cfg(test)]
pub(in crate::encoder) fn take_forced_scope_pop_failure() -> bool {
    FORCE_SCOPE_POP_FAILURE_ONCE.with(|flag| {
        let enabled = flag.get();
        flag.set(false);
        enabled
    })
}

#[cfg(not(test))]
pub(in crate::encoder) fn take_forced_scope_pop_failure() -> bool {
    false
}

/// Make the next solve on this thread panic inside ay's solve call, once.
#[cfg(test)]
pub(in crate::encoder) fn take_forced_solve_panic() -> bool {
    FORCE_SOLVE_PANIC_ONCE.with(|flag| {
        let enabled = flag.get();
        flag.set(false);
        enabled
    })
}

#[cfg(test)]
pub(in crate::encoder) fn bump_setup_from_prepared_count() {
    SETUP_FROM_PREPARED_COUNT.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
pub(in crate::encoder) fn bump_setup_from_prepared_count() {}

#[cfg(test)]
pub(in crate::encoder) fn setup_from_prepared_count() -> usize {
    SETUP_FROM_PREPARED_COUNT.with(|count| count.get())
}

#[cfg(test)]
pub(in crate::encoder) fn reset_setup_from_prepared_count() {
    SETUP_FROM_PREPARED_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub(in crate::encoder) fn bump_per_assertion_prune_plan_build_count() {
    PER_ASSERTION_PRUNE_PLAN_BUILD_COUNT.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
pub(in crate::encoder) fn bump_per_assertion_prune_plan_build_count() {}

#[cfg(test)]
pub(in crate::encoder) fn per_assertion_prune_plan_build_count() -> usize {
    PER_ASSERTION_PRUNE_PLAN_BUILD_COUNT.with(|count| count.get())
}

#[cfg(test)]
pub(in crate::encoder) fn reset_per_assertion_prune_plan_build_count() {
    PER_ASSERTION_PRUNE_PLAN_BUILD_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub(in crate::encoder) fn bump_shared_bv_reuse_attempt_count() {
    SHARED_BV_REUSE_ATTEMPT_COUNT.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
pub(in crate::encoder) fn bump_shared_bv_reuse_attempt_count() {}

#[cfg(test)]
pub(in crate::encoder) fn shared_bv_reuse_attempt_count() -> usize {
    SHARED_BV_REUSE_ATTEMPT_COUNT.with(|count| count.get())
}

#[cfg(test)]
pub(in crate::encoder) fn reset_shared_bv_reuse_attempt_count() {
    SHARED_BV_REUSE_ATTEMPT_COUNT.with(|count| count.set(0));
}
