//! Core proof-session shell for verification collection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Slices 0-3 of #2481 consolidate the core proof-collection state behind
//! one session module while preserving fail-closed borrow-conflict behavior.
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::translator::RustToSmtTranslator;
use crate::vc::{SolverMode, VerificationContext};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use thiserror::Error;

thread_local! {
    static PROOF_SESSION: RefCell<ProofSession> = RefCell::new(ProofSession::new());
    // Keep #2360 fail-closed accounting alive even when the session RefCell is
    // itself the borrow-conflict source. The count is folded back into the
    // session on the next successful read/write.
    static PENDING_OBLIGATION_DROPS: Cell<usize> = const { Cell::new(0) };
}

/// Owned state for the proof-collection session. The verify-macro state plus
/// the obligation translator/cache/counters live behind one RefCell.
/// Part of #2481 Slices 1-3.
pub(crate) struct ProofSession {
    pub(crate) context: Option<VerificationContext>,
    pub(crate) in_proof_mode: bool,
    pub(crate) local_var_types: HashMap<String, TrustVcType>,
    pub(crate) local_let_bindings: HashMap<String, String>,
    /// Stack of active assert-by scopes.
    /// `display_label` is the user-facing step name (e.g. "calc step 1 of 3").
    /// Part of #2652.
    pub(crate) assert_by_scope_stack: Vec<AssertByScope>,
    pub(crate) translator: RustToSmtTranslator,
    pub(crate) pre_built_exprs: HashMap<(String, String), TrustVcExpr>,
    pub(crate) function_solver_mode: Option<SolverMode>,
    pub(crate) total_obligations_collected: Cell<u64>,
    pub(crate) obligations_dropped: Cell<usize>,
}

pub(crate) struct AssertByScope {
    pub(crate) scope_key: String,
    pub(crate) display_label: Option<String>,
    pub(crate) obligation_start_index: usize,
    pub(crate) saved_local_let_bindings: HashMap<String, String>,
}

impl AssertByScope {
    pub(crate) fn new(
        scope_key: String,
        display_label: Option<String>,
        obligation_start_index: usize,
        saved_local_let_bindings: HashMap<String, String>,
    ) -> Self {
        Self {
            scope_key,
            display_label,
            obligation_start_index,
            saved_local_let_bindings,
        }
    }
}

impl ProofSession {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            context: None,
            in_proof_mode: false,
            local_var_types: HashMap::new(),
            local_let_bindings: HashMap::new(),
            assert_by_scope_stack: Vec::new(),
            translator: RustToSmtTranslator::new(),
            pre_built_exprs: HashMap::new(),
            function_solver_mode: None,
            total_obligations_collected: Cell::new(0),
            obligations_dropped: Cell::new(0),
        }
    }
}

impl Default for ProofSession {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub(crate) enum SessionBorrowError {
    #[error("proof session is already mutably borrowed")]
    SharedAccessUnavailable,
    #[error("proof session is already borrowed")]
    MutableAccessUnavailable,
}

pub(crate) fn try_with_session<R>(
    f: impl FnOnce(&ProofSession) -> R,
) -> Result<R, SessionBorrowError> {
    PROOF_SESSION.with(|session| {
        session
            .try_borrow()
            .map(|session_ref| f(&session_ref))
            .map_err(|_| SessionBorrowError::SharedAccessUnavailable)
    })
}

pub(crate) fn try_with_session_mut<R>(
    f: impl FnOnce(&mut ProofSession) -> R,
) -> Result<R, SessionBorrowError> {
    PROOF_SESSION.with(|session| {
        session
            .try_borrow_mut()
            .map(|mut session_ref| f(&mut session_ref))
            .map_err(|_| SessionBorrowError::MutableAccessUnavailable)
    })
}

pub(crate) fn clear_proof_session() -> Result<(), SessionBorrowError> {
    PENDING_OBLIGATION_DROPS.with(|pending| pending.set(0));
    try_with_session_mut(|session| *session = ProofSession::new())
}

fn sync_pending_obligation_drops(session: &ProofSession) {
    let pending = PENDING_OBLIGATION_DROPS.with(|drops| drops.replace(0));
    if pending > 0 {
        session
            .obligations_dropped
            .set(session.obligations_dropped.get() + pending);
    }
}

pub(crate) fn record_obligation_drop() {
    if try_with_session(|session| {
        sync_pending_obligation_drops(session);
        session
            .obligations_dropped
            .set(session.obligations_dropped.get() + 1);
    })
    .is_err()
    {
        PENDING_OBLIGATION_DROPS.with(|drops| drops.set(drops.get() + 1));
    }
}

#[must_use]
pub(crate) fn obligations_dropped_count() -> usize {
    try_with_session(|session| {
        sync_pending_obligation_drops(session);
        session.obligations_dropped.get()
    })
    .unwrap_or_else(|_| PENDING_OBLIGATION_DROPS.with(|drops| drops.get()))
}

pub(crate) fn reset_obligations_dropped() {
    set_obligations_dropped_count(0);
}

pub(crate) fn set_obligations_dropped_count(count: usize) {
    if try_with_session(|session| {
        session.obligations_dropped.set(count);
    })
    .is_ok()
    {
        PENDING_OBLIGATION_DROPS.with(|drops| drops.set(0));
    } else {
        PENDING_OBLIGATION_DROPS.with(|drops| drops.set(count));
    }
}

#[must_use]
pub(crate) fn current_function_solver_mode() -> Option<SolverMode> {
    try_with_session(|session| session.function_solver_mode)
        .ok()
        .flatten()
}

/// Test-only: exposes the raw `RefCell<ProofSession>` so borrow-conflict
/// tests can hold a borrow while calling functions that try to re-borrow.
/// Part of #2481 Slices 1-3.
#[cfg(test)]
pub(crate) fn with_session_cell<R>(f: impl FnOnce(&RefCell<ProofSession>) -> R) -> R {
    PROOF_SESSION.with(f)
}

#[cfg(test)]
#[path = "proof_session_proof_tests.rs"]
mod proof_tests;
