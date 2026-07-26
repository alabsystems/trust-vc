//! Protocol verification via ty model checking.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module adds concurrent protocol verification to trust_vc by
//! dispatching `ProtocolObligation`s to the ty model checker.
//! Sequential obligations continue through the existing ay path.
//!
//! # Architecture
//!
//! ```text
//! trust_vc verification pipeline
//!     ├── ay path (existing): sequential properties
//!     │   ProofObligation → AYEncoder → ay-dpll → VerifyResult
//!     │
//!     └── ty path (this module): concurrent protocol properties
//!         ProtocolObligation → TyEncoder → tla-check → VerifyResult
//! ```

pub(crate) mod result;
pub(crate) mod translate;

use crate::VerifyResult;

/// A protocol verification obligation dispatched to the ty model checker.
///
/// Unlike `ProofObligation` (which encodes first-order SMT formulas for ay),
/// protocol obligations describe state machines with transitions and invariants
/// that require model checking over finite state spaces.
#[derive(Debug, Clone)]
pub struct ProtocolObligation {
    /// Human-readable name for the protocol.
    pub name: String,
    /// TY spec text to be parsed and model-checked.
    /// Generated from `#[protocol]`/`#[action]`/`#[safety]` annotations.
    pub spec: String,
    /// TY configuration text (INIT, NEXT, INVARIANT, PROPERTY lines).
    pub config: String,
}

/// Encoder that dispatches protocol obligations to ty.
pub(crate) struct TyEncoder;

impl TyEncoder {
    /// Verify a set of protocol obligations via ty model checking.
    ///
    /// Each obligation is parsed, lowered, and model-checked independently.
    /// The first failure (Counterexample, Error, or Unknown) is returned;
    /// if all pass, returns `VerifyResult::Verified`.
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
        // 1. Parse TY spec text
        let tree = tla_core::parse_to_syntax_tree(&obligation.spec);
        let lowered = tla_core::lower(tla_core::FileId(0), &tree);
        let module = match lowered.module {
            Some(m) => m,
            None => {
                return VerifyResult::Error {
                    message: format!(
                        "ty parse/lower failed for protocol '{}': {:?}",
                        obligation.name, lowered.errors
                    ),
                }
            }
        };

        // 2. Parse TY config
        let mut config = match tla_check::Config::parse(&obligation.config) {
            Ok(c) => c,
            Err(e) => {
                return VerifyResult::Error {
                    message: format!(
                        "ty config parse failed for protocol '{}': {:?}",
                        obligation.name, e
                    ),
                }
            }
        };
        // TrustVc-generated protocol obligations are currently small safety/liveness
        // witnesses where correctness is more important than state-space reduction.
        // ty auto-enables POR by default, and that path can prune visible actions for
        // these generated specs, masking invariant violations.
        config.auto_por = Some(false);
        config.por_enabled = false;

        // 3. Model check
        let check_result = tla_check::check_module(&module, &config);

        // 4. Map result
        result::check_result_to_verify_result(check_result)
    }
}
