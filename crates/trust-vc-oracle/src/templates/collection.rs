// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{
    has_single_collection_param, proposal, proposal_from_strs, returns_collection,
};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct LengthPreservingTemplate;

impl SpecTemplate for LengthPreservingTemplate {
    fn name(&self) -> &str {
        "length_preserving"
    }

    fn description(&self) -> &str {
        "ensures!(result.len() == input.len())"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_collection_param(sig) && returns_collection(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.len() == {param}@.len()")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.len() <= {param}@.len()")],
        )]
    }
}

pub(crate) struct SortedTemplate;

impl SpecTemplate for SortedTemplate {
    fn name(&self) -> &str {
        "sorted"
    }

    fn description(&self) -> &str {
        "forall!(|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j])"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_collection(sig)
    }

    fn instantiate(&self, _sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        vec![proposal_from_strs(
            &[],
            &["forall(|i: int, j: int| 0 <= i && i < j && j < result@.len() ==> result@[i] <= result@[j])"],
        )]
    }

    fn refine(
        &self,
        _sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        vec![proposal_from_strs(
            &[],
            &["forall(|i: int| 0 <= i && i + 1 < result@.len() ==> result@[i] <= result@[i + 1])"],
        )]
    }
}

pub(crate) struct PermutationTemplate;

impl SpecTemplate for PermutationTemplate {
    fn name(&self) -> &str {
        "permutation"
    }

    fn description(&self) -> &str {
        "ensures!(result@.to_multiset() == input@.to_multiset())"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_collection_param(sig) && returns_collection(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.to_multiset() == {param}@.to_multiset()")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.len() == {param}@.len()")],
        )]
    }
}

pub(crate) struct InvariantTemplate;

impl SpecTemplate for InvariantTemplate {
    fn name(&self) -> &str {
        "invariant"
    }

    fn description(&self) -> &str {
        "ensures!(property(result) == property(input)) for len, is_empty, etc."
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_collection_param(sig) && returns_collection(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![
            proposal(vec![], vec![format!("result@.len() == {param}@.len()")]),
            proposal(
                vec![],
                vec![format!("(result@.len() == 0) == ({param}@.len() == 0)")],
            ),
            proposal(
                vec![format!("{param}@.len() > 0")],
                vec![format!("result@.len() > 0 && result@[0] == {param}@[0]")],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![format!("{param}@.len() > 0")],
            vec!["result@.len() > 0".to_string()],
        )]
    }
}

pub(crate) struct ContainmentPreservingTemplate;

impl SpecTemplate for ContainmentPreservingTemplate {
    fn name(&self) -> &str {
        "containment_preserving"
    }

    fn description(&self) -> &str {
        "forall x in input ==> x in result (no element loss)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_collection_param(sig) && returns_collection(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|i: int| 0 <= i && i < {param}@.len() ==> result@.contains({param}@[i]))"
                )],
            ),
            proposal(
                vec![format!("{param}@.len() > 0")],
                vec![format!("result@.contains({param}@[0])")],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.len() >= {param}@.len()")],
        )]
    }
}

pub(crate) struct SubsetBoundTemplate;

impl SpecTemplate for SubsetBoundTemplate {
    fn name(&self) -> &str {
        "subset_bound"
    }

    fn description(&self) -> &str {
        "forall x in result ==> x in input (no new elements)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_collection_param(sig) && returns_collection(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|i: int| 0 <= i && i < result@.len() ==> {param}@.contains(result@[i]))"
                )],
            ),
            proposal(vec![], vec![format!("result@.len() <= {param}@.len()")]),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let param = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result@.len() <= {param}@.len()")],
        )]
    }
}
