// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{
    is_collection, is_numeric, proposal, proposal_from_strs, returns_option, returns_result,
};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct ErrorFreeTemplate;

impl SpecTemplate for ErrorFreeTemplate {
    fn name(&self) -> &str {
        "error_free"
    }

    fn description(&self) -> &str {
        "ensures!(result.is_ok())"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_result(sig)
    }

    fn instantiate(&self, _sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        vec![proposal_from_strs(&[], &["result.is_ok()"])]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let requires: Vec<String> = sig
            .params
            .iter()
            .filter(|(_, ty)| is_numeric(ty))
            .map(|(name, _)| format!("{name} >= 0"))
            .collect();
        if requires.is_empty() {
            return self.instantiate(sig);
        }

        vec![proposal(requires, vec!["result.is_ok()".to_string()])]
    }
}

pub(crate) struct NullabilityGuardTemplate;

impl SpecTemplate for NullabilityGuardTemplate {
    fn name(&self) -> &str {
        "nullability_guard"
    }

    fn description(&self) -> &str {
        "ensures!(result.is_some()) under preconditions"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_option(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let mut proposals = vec![proposal_from_strs(&[], &["result.is_some()"])];

        let numeric_requires: Vec<String> = sig
            .params
            .iter()
            .filter(|(_, ty)| is_numeric(ty))
            .map(|(name, _)| format!("{name} >= 0"))
            .collect();
        if !numeric_requires.is_empty() {
            proposals.push(proposal(
                numeric_requires,
                vec!["result.is_some()".to_string()],
            ));
        }

        for (name, ty) in &sig.params {
            if is_collection(ty) {
                proposals.push(proposal(
                    vec![format!("{name}@.len() > 0")],
                    vec!["result.is_some()".to_string()],
                ));
            }
        }

        proposals
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let requires: Vec<String> = sig
            .params
            .iter()
            .filter_map(|(name, ty)| {
                if is_numeric(ty) {
                    return Some(format!("{name} > 0"));
                }
                if is_collection(ty) {
                    return Some(format!("{name}@.len() > 0"));
                }
                None
            })
            .collect();
        if requires.is_empty() {
            return self.instantiate(sig);
        }

        vec![proposal(requires, vec!["result.is_some()".to_string()])]
    }
}
