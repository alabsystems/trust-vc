// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! In-memory verification while the exact native client owner is borrowed.
//! No caller-supplied crate, observation, token or permission flag enters here.

use super::super::super::macro_context::ClientSource;
use super::*;
use crate::reader::{declaration_modes, CrateRead, FnStatus, ReadOptions};
use crate::verdict::Verdict;
use crate::verify::{self, Report, VerifyOptions};

/// Constructed only by performing this owned import registry's actual read.
/// The whole read stays immutable until verification and both revalidations.
pub(in crate::reader::declaration_staging) struct LiveClientRead<'scope, 'library, 'tcx> {
    imports: &'scope ClientImports<'library, 'tcx>,
    tcx: TyCtxt<'tcx>,
    source: &'scope ClientSource,
    read: CrateRead,
}

/// Provisional output only. The standalone caller must also observe compiler0
/// and its final physical-input checks before publishing this result.
pub(in crate::reader::declaration_staging) struct PendingVerification {
    report: Value,
    succeeded: bool,
}

impl PendingVerification {
    pub(in crate::reader::declaration_staging) fn into_report(self) -> (Value, bool) {
        (self.report, self.succeeded)
    }
}

impl<'library, 'tcx> ClientImports<'library, 'tcx> {
    pub(in crate::reader::declaration_staging) fn read_for_verification<'scope>(
        &'scope self,
        tcx: TyCtxt<'tcx>,
        options: ReadOptions,
        source: &'scope ClientSource,
    ) -> Result<LiveClientRead<'scope, 'library, 'tcx>, String> {
        self.revalidate(tcx)?;
        source.file().read()?;
        let read = self.read(tcx, options)?;
        let live = LiveClientRead {
            imports: self,
            tcx,
            source,
            read,
        };
        live.ready()?;
        Ok(live)
    }
}

impl LiveClientRead<'_, '_, '_> {
    fn ready(&self) -> Result<(), String> {
        let Self {
            imports,
            tcx,
            source,
            read,
        } = self;
        imports.revalidate(*tcx)?;
        source.file().read()?;
        diagnostics(*tcx)?;
        if read.fns.is_empty()
            || read.fns.len() > 256
            || read.krate.fns.len() > 16_384
            || read.spans.len() > 65_536
            || read.krate.adts.len() > 16_384
            || imports.functions.len() > 16_384
            || read.refusals().next().is_some()
            || !read.errors.is_empty()
            || !read.verify_refusals.is_empty()
            || !read.pending_item_refusals.is_empty()
            || !read.native_ownership.is_empty()
        {
            return Err(
                "the owned verification read is incomplete or needs canonical ownership checking"
                    .into(),
            );
        }
        let wf = trust_vc_vcir::check_crate(&read.krate);
        if !wf.is_empty() {
            return Err("the actual owned read failed VcIR well-formedness".into());
        }
        let mut local = std::collections::HashSet::new();
        let mut builtins = std::collections::HashSet::new();
        for record in &read.fns {
            let FnStatus::Read(id) = &record.status else {
                return Err("owned verification requires every local record to be read without deferred/external ownership".into());
            };
            let definition = record.def_id.to_def_id();
            if read.fn_defs.get(id) != Some(&record.def_id)
                || !local.insert(*id)
                || !declaration_modes::original_body_available(*tcx, record.def_id)
                || *id != FnId(hash(declaration_native::key(*tcx, definition)))
            {
                return Err("the local verification identity/body correspondence changed".into());
            }
            let declaration = read
                .krate
                .fn_decl(*id)
                .ok_or("a native read record has no VcIR body")?;
            if declaration.role != FnRole::Item
                || declaration.attrs.external_body
                || !matches!(declaration.mode, Mode::Proof | Mode::Spec)
                || declaration
                    .locals
                    .iter()
                    .any(|value| value.mode != Mode::Spec)
            {
                return Err("this owned client needs a canonical non-ghost ownership check".into());
            }
            let ghost = read.ghost_ownership.get(&record.def_id).ok_or(
                "the original native body is outside the checked ghost-only ownership fragment",
            )?;
            if !ghost.current(*tcx, record.def_id) {
                return Err(
                    "the native ghost-only component no longer belongs to this original body"
                        .into(),
                );
            }
            for definition in ghost.builtins() {
                if builtins.len() >= 256 && !builtins.contains(definition) {
                    return Err("the verification builtin inventory exceeds its bound".into());
                }
                builtins.insert(*definition);
            }
        }
        if read.fn_defs.len() != local.len() || read.ghost_ownership.len() != local.len() {
            return Err(
                "the complete original local ownership inventory differs from the read".into(),
            );
        }
        let mut licensed = HashMap::new();
        for function in imports.functions.values() {
            if licensed.insert(function.id, function).is_some() {
                return Err("owned imported function IDs collide".into());
            }
        }
        if read.krate.fns.len() != local.len() + licensed.len() {
            return Err("the complete owned declaration inventory changed".into());
        }
        for declaration in &read.krate.fns {
            if local.contains(&declaration.id) {
                continue;
            }
            let function = licensed
                .get(&declaration.id)
                .ok_or("an extra VcIR declaration has no owned native import")?;
            if *declaration != function.declaration(declaration.span) {
                return Err(
                    "an imported signature acquired body, clause or instance authority".into(),
                );
            }
        }
        // These source/native components alone are not a builtin license.
        // Join every actual foreign identity to this retained fresh cohort.
        for definition in builtins {
            super::super::super::meaning::validate_builtin_member(
                *tcx,
                definition,
                &imports.library.inputs,
                imports.frame.common(),
            )?;
        }
        diagnostics(*tcx)
    }

    pub(in crate::reader::declaration_staging) fn verify(
        self,
        options: VerifyOptions,
    ) -> Result<PendingVerification, String> {
        self.ready()?;
        // This remains observational; it cannot authorize this invocation.
        let footprint = super::super::super::standalone_client::footprint::capture(
            self.tcx,
            &self.read,
            self.imports,
            self.source,
        )?;
        let verification = verify::verify(&self.read, options);
        self.ready()?;
        if verification.fns.len() != self.read.krate.fns.len() {
            return Err("the verifier changed the complete declaration denominator".into());
        }
        let mut functions = Vec::new();
        for record in &self.read.fns {
            let FnStatus::Read(id) = &record.status else {
                return Err("a verified native record changed".into());
            };
            let outcome = verification
                .fns
                .get(id)
                .ok_or("the verifier omitted a native local function")?;
            functions.push(
                json!({"id": {"hi": format!("{:016x}", id.0.hi), "lo": format!("{:016x}", id.0.lo)},
                "verdict": outcome.verdict.as_str(), "tag": outcome.tag,
                "sites": outcome.sites.as_ref().map(|sites| json!({
                    "proved": sites.proved, "failed": sites.failed}))}),
            );
        }
        let imported = self
            .read
            .krate
            .fns
            .iter()
            .filter(|f| f.role == FnRole::Imported)
            .collect::<Vec<_>>();
        if imported.iter().any(|f| {
            verification.fns.get(&f.id).is_none_or(|outcome| {
                outcome.verdict != Verdict::Declared || outcome.sites.is_some()
            })
        }) {
            return Err("an imported declaration was not kept unscored and bodyless".into());
        }
        let reports = verification.reports.iter().map(|report| match report {
            Report::Failure(failure) => json!({"kind": "VerificationFailure", "message": failure.message,
                "primary": failure.primary.iter().map(|span| crate::reader::declaration_facts::source_anchor(self.tcx, *span)).collect::<Vec<_>>(),
                "labels": failure.labels.iter().map(|(span, message)| json!({"source": crate::reader::declaration_facts::source_anchor(self.tcx, *span), "message": message})).collect::<Vec<_>>() }),
            Report::Refusal { tag, detail, .. } => json!({"kind": "Refusal", "tag": tag, "detail": detail}),
            Report::Recommendation(failure) => json!({"kind": "Note", "message": failure.message,
                "primary": failure.primary.iter().map(|span| crate::reader::declaration_facts::source_anchor(self.tcx, *span)).collect::<Vec<_>>(),
                "labels": failure.labels.iter().map(|(span, message)| json!({"source": crate::reader::declaration_facts::source_anchor(self.tcx, *span), "message": message})).collect::<Vec<_>>() }),
            Report::Note { message, .. } => json!({"kind": "Note", "message": message}),
        }).collect::<Vec<_>>();
        let outcomes = self
            .read
            .fns
            .iter()
            .filter_map(|record| match &record.status {
                FnStatus::Read(id) => verification.fns.get(id).map(|outcome| outcome.verdict),
                _ => None,
            })
            .collect::<Vec<_>>();
        let state = if verification
            .reports
            .iter()
            .any(|report| matches!(report, Report::Refusal { .. }))
        {
            "Refused"
        } else {
            outcome_state(&outcomes)
        };
        let verified = outcomes
            .iter()
            .filter(|verdict| **verdict == Verdict::Verified)
            .count();
        Ok(PendingVerification {
            succeeded: state == "Verified",
            report: json!({
            "schema": "trust-vc.owned-client-verification@1",
            "state": "OwnedClientVerification", "verification_state": state,
            "source_path": self.source.file().path, "source_sha256": self.source.file().sha256,
            "functions": functions, "reports": reports, "footprint": footprint,
            "warnings": self.read.warnings.iter().map(|warning| json!({"message": warning.message, "source": crate::reader::declaration_facts::source_anchor(self.tcx, warning.span)})).collect::<Vec<_>>(),
            "ownership": {"state": "OriginalNativeGhostOnly", "roots": self.read.fns.len(),
                "native_owned_value_roots": 0, "canonical_borrow_checks_executed": 0},
            "verification_executed": true,
            "solver_path": "native VcIR -> normal Core query API, including its true-goal fast path",
            "verified_functions": verified, "imported_declarations": imported.len(),
            "imported_verified_functions": 0, "ordinary_reader_imports_enabled": false,
            "proof_active_compiler_hook": false,
            "publication": "Pending enclosing compiler and final physical input checks"}),
        })
    }
}

fn outcome_state(outcomes: &[Verdict]) -> &'static str {
    if outcomes.is_empty()
        || outcomes
            .iter()
            .any(|v| !matches!(v, Verdict::Verified | Verdict::Failed))
    {
        "Refused"
    } else if outcomes.contains(&Verdict::Failed) {
        "VerificationFailed"
    } else {
        "Verified"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn real_failures_remain_distinct_from_refusals_and_empty_output() {
        assert_eq!(outcome_state(&[Verdict::Verified]), "Verified");
        assert_eq!(outcome_state(&[Verdict::Failed]), "VerificationFailed");
        for verdict in [
            Verdict::Refused,
            Verdict::Skipped,
            Verdict::Rejected,
            Verdict::Declared,
            Verdict::Trusted,
            Verdict::External,
        ] {
            assert_eq!(outcome_state(&[Verdict::Verified, verdict]), "Refused");
        }
        assert_eq!(outcome_state(&[]), "Refused");
    }
}
