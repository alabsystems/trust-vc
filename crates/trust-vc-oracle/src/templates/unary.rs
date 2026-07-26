// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{
    has_single_param_matching_return, is_collection, is_numeric, proposal, proposal_from_strs,
    returns_numeric,
};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct IdempotentTemplate;

impl SpecTemplate for IdempotentTemplate {
    fn name(&self) -> &str {
        "idempotent"
    }

    fn description(&self) -> &str {
        "ensures!(f(f(x)) == f(x))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("{fname}(result) == {fname}({param})")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(vec![], vec![format!("result == {param}")])]
    }
}

pub(crate) struct IdentityTemplate;

impl SpecTemplate for IdentityTemplate {
    fn name(&self) -> &str {
        "identity"
    }

    fn description(&self) -> &str {
        "ensures!(result == x)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(vec![], vec![format!("result == {param}")])]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        if is_numeric(&sig.params[0].1) {
            return vec![
                proposal(vec![], vec![format!("result >= {param}")]),
                proposal(vec![], vec![format!("result <= {param}")]),
            ];
        }

        vec![]
    }
}

pub(crate) struct PreservesPropertyTemplate;

impl SpecTemplate for PreservesPropertyTemplate {
    fn name(&self) -> &str {
        "preserves_property"
    }

    fn description(&self) -> &str {
        "ensures!(property(result) == property(input))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let (param, ty) = (&sig.params[0].0, &sig.params[0].1);
        let mut proposals = Vec::new();

        if is_numeric(ty) {
            proposals.push(proposal(vec![], vec![format!("result % 2 == {param} % 2")]));
            proposals.push(proposal(
                vec![format!("{param} >= 0")],
                vec!["result >= 0".to_string()],
            ));
            proposals.push(proposal(
                vec![format!("{param} <= 0")],
                vec!["result <= 0".to_string()],
            ));
        }

        if is_collection(ty) {
            proposals.push(proposal(
                vec![],
                vec![format!("result@.len() == {param}@.len()")],
            ));
        }

        proposals
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        if returns_numeric(sig) {
            return vec![proposal_from_strs(&[], &["result >= 0"])];
        }

        vec![]
    }
}

pub(crate) struct SurjectiveTemplate;

impl SpecTemplate for SurjectiveTemplate {
    fn name(&self) -> &str {
        "surjective"
    }

    fn description(&self) -> &str {
        "forall y: T, exists x: T such that f(x) == y"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let ty = &sig.params[0].1;
        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|y: {ty}| exists(|x: {ty}| {fname}(x) == y))"
                )],
            ),
            proposal(
                vec![],
                vec![format!("exists(|x: {ty}| {fname}(x) == result)")],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let param = &sig.params[0].0;
        let ty = &sig.params[0].1;
        vec![proposal(
            vec![],
            vec![format!("exists(|y: {ty}| {fname}(y) != {fname}({param}))")],
        )]
    }
}

pub(crate) struct InvolutionTemplate;

impl SpecTemplate for InvolutionTemplate {
    fn name(&self) -> &str {
        "involution"
    }

    fn description(&self) -> &str {
        "ensures!(f(f(x)) == x)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("{fname}(result) == {param}")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        if is_numeric(&sig.params[0].1) {
            return vec![proposal(
                vec![],
                vec![format!("result >= 0 && {param} >= 0 ==> result == {param}")],
            )];
        }

        vec![proposal(vec![], vec![format!("result == {param}")])]
    }
}

pub(crate) struct FixedPointTemplate;

impl SpecTemplate for FixedPointTemplate {
    fn name(&self) -> &str {
        "fixed_point"
    }

    fn description(&self) -> &str {
        "exists x: T such that f(x) == x"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_param_matching_return(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let param = &sig.params[0].0;
        let ty = &sig.params[0].1;
        vec![
            proposal(
                vec![format!("{fname}({param}) == {param}")],
                vec![format!("result == {param}")],
            ),
            proposal(
                vec![],
                vec![format!("exists(|fp: {ty}| {fname}(fp) == fp)")],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        if is_numeric(&sig.params[0].1) {
            return vec![proposal(vec![], vec![format!("{fname}(0) == 0")])];
        }

        self.instantiate(sig)
    }
}
