//! Protocol verification by the `ty` model checker, across a process
//! boundary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module adds concurrent protocol verification to trust_vc by
//! dispatching `ProtocolObligation`s to the `ty` binary. Sequential
//! obligations continue through the existing ay path.
//!
//! ```text
//! trust_vc verification pipeline
//!     ├── ay path (existing): sequential properties
//!     │   ProofObligation → AYEncoder → ay-dpll → VerifyResult
//!     │
//!     └── ty path (this module): concurrent protocol properties
//!         ProtocolObligation → `ty check --output json` → VerifyResult
//! ```
//!
//! No ty crate is linked. Each obligation is checked by one run of the
//! binary [`binary`] resolves (`TRUST_VC_TY_BIN`, else `ty` on `PATH`),
//! in a private directory with the environment cleared ([`run`]), and its
//! JSON document is read by the fields ty freezes under
//! `check-json-contract-v2` ([`document`]). The document must advertise
//! every capability in [`document::REQUIRED_CAPABILITIES`]: they carry what
//! this lane used to check itself on ty's AST, that ty read the spec exactly
//! as written and decides `ENABLED` by its contract. The interface, from
//! both sides, is ty's `docs/design/2026-10-08-machine-interface-for-trust-vc.md`.

mod binary;
mod config;
mod document;
mod run;
mod rust_expr;
pub(crate) mod translate;

pub use binary::BIN_VAR;

use crate::VerifyResult;

/// A protocol verification obligation dispatched to the `ty` model checker.
///
/// Unlike `ProofObligation` (which encodes first-order SMT formulas for ay),
/// protocol obligations describe state machines with transitions and invariants
/// that require model checking over finite state spaces.
#[derive(Debug, Clone)]
pub struct ProtocolObligation {
    /// Human-readable name for the protocol.
    pub name: String,
    /// TLA+ module text to be model-checked: exactly one module, which may
    /// extend only ty's standard modules.
    pub spec: String,
    /// TLC configuration text: `INIT`, `NEXT`, `INVARIANT`, `PROPERTY` and
    /// `CHECK_DEADLOCK` lines, one name each; anything else is refused.
    pub config: String,
    /// What the module declares and defines, when it was generated: `None`
    /// for a raw obligation, the emitted variables and operators for a
    /// `#[protocol]` one, which must then be all the module holds.
    pub shape: Option<ProtocolShape>,
}

/// The variables (in order) and operators (each without parameters) a
/// generated module was emitted with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolShape {
    pub variables: Vec<String>,
    pub operators: Vec<String>,
}

/// Encoder that dispatches protocol obligations to ty.
pub(crate) struct TyEncoder;

impl TyEncoder {
    /// Verify a set of protocol obligations via ty model checking.
    ///
    /// Each obligation is model-checked by its own run of `ty`. The first
    /// failure (Counterexample, Error, or Unknown) is returned; if all pass,
    /// returns `VerifyResult::Verified`.
    pub(crate) fn verify_protocol(obligations: &[ProtocolObligation]) -> VerifyResult {
        for obligation in obligations {
            let r = Self::verify_one(obligation);
            if !matches!(r, VerifyResult::Verified) {
                return r;
            }
        }
        VerifyResult::Verified
    }

    fn verify_one(obligation: &ProtocolObligation) -> VerifyResult {
        let refuse = |what: &str, detail: String| VerifyResult::Error {
            message: format!("ty {what} for protocol '{}': {detail}", obligation.name),
        };
        let request = match config::Request::parse(&obligation.config) {
            Ok(request) => request,
            Err(detail) => return refuse("config refused", detail),
        };
        let bin = match binary::resolve() {
            Ok(bin) => bin,
            Err(detail) => return refuse("binary not found", detail),
        };
        let run = match run::check(&bin, &obligation.spec, &request.canonical()) {
            Ok(run) => run,
            Err(detail) => return refuse("run failed", detail),
        };
        document::judge(
            &document::Expected {
                name: &obligation.name,
                spec: &obligation.spec,
                request: &request,
                shape: obligation.shape.as_ref(),
            },
            &run,
        )
    }
}

#[cfg(test)]
#[path = "verify_tests.rs"]
mod verify_tests;
