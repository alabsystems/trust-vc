// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One sealed invocation and one live native preparation govern the read.

use super::*;
use crate::declaration_alignment::source_bindings::PinnedFile;
use crate::reader::declaration_staging::{
    LiveNormalClientRead, NormalClientPlan, NormalPlanIdentity,
};
use std::sync::Arc;

pub(crate) struct OwnedNormalVerifier<'plan, 'owner> {
    run: VerifyRun,
    plan: &'plan NormalClientPlan<'owner>,
    identity: NormalRunIdentity,
}

// The Arc makes this non-zero-sized; the identity itself belongs to this
// verifier, so two verifiers of the same immutable plan are still distinct.
struct NormalRunIdentity {
    plan: Arc<NormalPlanIdentity>,
    source: PinnedFile,
    source_operand: PathBuf,
    read: ReadOptions,
}

#[derive(Clone, Copy)]
pub(crate) struct NormalReadBinding<'run> {
    identity: &'run NormalRunIdentity,
}

impl NormalReadBinding<'_> {
    pub(crate) fn read_options(&self) -> ReadOptions {
        self.identity.read
    }
    pub(crate) fn same_run(&self, other: &NormalReadBinding<'_>) -> bool {
        std::ptr::eq(self.identity, other.identity)
            && Arc::ptr_eq(&self.identity.plan, &other.identity.plan)
    }
    pub(crate) fn source_matches(&self, source: &PinnedFile) -> bool {
        self.identity.source.path == source.path && self.identity.source.sha256 == source.sha256
    }
    pub(crate) fn revalidate_source(&self) -> Result<(), String> {
        if self
            .identity
            .source_operand
            .canonicalize()
            .map_err(|e| e.to_string())?
            != self.identity.source.path
        {
            return Err("the normal preparation source operand changed its actual target".into());
        }
        self.identity.source.read()?;
        Ok(())
    }
}

pub(crate) struct NormalReadScope<'run, 'plan, 'owner, 'tcx> {
    run: &'run mut VerifyRun,
    plan: &'plan NormalClientPlan<'owner>,
    identity: &'run NormalRunIdentity,
    tcx: TyCtxt<'tcx>,
}

impl<'plan, 'owner> OwnedNormalVerifier<'plan, 'owner> {
    pub(crate) fn new(plan: &'plan NormalClientPlan<'owner>) -> Self {
        Self::new_with_outputs(plan, OutputSinks::default())
    }

    /// Output paths are request data, separate from the plan, source binding
    /// and native owner. Constructing them grants no permission to verify.
    pub(crate) fn new_with_outputs(
        plan: &'plan NormalClientPlan<'owner>,
        outputs: OutputSinks,
    ) -> Self {
        let mut options = plan.invocation().options();
        options.compiler_environment = plan.compiler_environment().cloned();
        Self {
            identity: NormalRunIdentity {
                plan: plan.identity(),
                source: plan.source_file().clone(),
                source_operand: plan.source_operand().to_path_buf(),
                read: options.read,
            },
            run: VerifyRun::new(options, outputs),
            plan,
        }
    }

    pub(crate) fn configure(&mut self, config: &mut rustc_interface::interface::Config) {
        self.run.config(config);
    }

    pub(crate) fn after_expansion<'run, 'tcx>(
        &'run mut self,
        tcx: TyCtxt<'tcx>,
    ) -> Option<NormalReadScope<'run, 'plan, 'owner, 'tcx>> {
        if let Err(reason) = self.plan.invocation().check_native_source(tcx) {
            self.run.reached = true;
            self.run.refuse(
                tcx,
                tcx.hir_root_module().spans.inner_span,
                "owned-invocation",
                &reason,
            );
            self.run.outcome = Some(Outcome::Refused);
            self.run.reading = false;
            return None;
        }
        if !self.run.prepare_read(tcx) {
            return None;
        }
        if let Err(reason) = self.plan.check_native_context(tcx) {
            self.run.refuse(
                tcx,
                tcx.hir_root_module().spans.inner_span,
                "owned-native-invocation",
                &reason,
            );
            self.run.outcome = Some(Outcome::Refused);
            self.run.reading = false;
            return None;
        }
        Some(NormalReadScope {
            run: &mut self.run,
            plan: self.plan,
            identity: &self.identity,
            tcx,
        })
    }

    pub(crate) fn into_record(mut self, output: PathBuf) -> Record {
        if self.run.opts.compiler_environment.is_some() {
            if let Err(error) = CompilerEnvironment::require_absent_process() {
                self.run.functions.clear();
                self.run
                    .crate_refusals
                    .push(format!("request-environment: {error}"));
                self.run.outcome = Some(Outcome::Refused);
            }
        }
        Record {
            argv: self.plan.verify().to_vec(),
            entry_file: Some(self.plan.source_file().path.clone()),
            output_file: Some(output),
            functions: self.run.functions,
            crate_refusals: self.run.crate_refusals,
            outcome: self.run.outcome,
            erase_exit: self.run.erase_exit,
            ..Record::default()
        }
    }
}

impl<'run, 'plan, 'owner, 'tcx> NormalReadScope<'run, 'plan, 'owner, 'tcx> {
    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    pub(crate) fn plan(&self) -> &'plan NormalClientPlan<'owner> {
        self.plan
    }
    pub(crate) fn binding(&self) -> NormalReadBinding<'run> {
        NormalReadBinding {
            identity: self.identity,
        }
    }

    pub(crate) fn decide(
        &mut self,
        live: &LiveNormalClientRead<'_, '_, '_, 'tcx>,
    ) -> Result<(), String> {
        // Check data identity before retained-input/native/solver queries.
        if !live.matches_preparation(self.tcx, self.binding()) {
            self.run.reading = false;
            return Err(
                "the normal read belongs to another invocation or verifier preparation".into(),
            );
        }
        let result = live.with_read(|tcx, read| {
            live.check_retained_inputs(tcx)?;
            self.run.decide_with_owner(tcx, read, Some(live));
            if let Some(environment) = &self.run.opts.compiler_environment {
                let checked = environment
                    .check_options(&tcx.sess.opts)
                    .and_then(|()| check_environment_dependencies(environment, tcx.sess));
                if let Err(error) = checked {
                    self.run.functions.clear();
                    self.run.refuse(
                        tcx,
                        rustc_span::DUMMY_SP,
                        "request-environment",
                        &error.to_string(),
                    );
                    self.run.outcome = Some(Outcome::Refused);
                    self.run
                        .record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                    return Err(error.to_string());
                }
            }
            if let Err(reason) = live.check_retained_inputs(tcx) {
                self.run.functions.clear();
                self.run.refuse(
                    tcx,
                    tcx.hir_root_module().spans.inner_span,
                    "owned-inputs",
                    &reason,
                );
                self.run.outcome = Some(Outcome::Refused);
                self.run
                    .record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return Err(reason);
            }
            Ok(())
        });
        self.run.reading = false;
        result
    }
}
