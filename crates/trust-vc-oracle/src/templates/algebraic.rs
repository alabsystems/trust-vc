// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{
    has_two_same_type_numeric_params, has_two_same_type_params, proposal, returns_numeric,
    same_type,
};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct CommutativityTemplate;

impl SpecTemplate for CommutativityTemplate {
    fn name(&self) -> &str {
        "commutativity"
    }

    fn description(&self) -> &str {
        "ensures!(f(a, b) == f(b, a))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && sig.return_type.is_some()
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![],
            vec![format!("result == {fname}({b}, {a})")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        if returns_numeric(sig) {
            return vec![proposal(
                vec![],
                vec![format!("result >= {a} || result >= {b}")],
            )];
        }

        vec![]
    }
}

pub(crate) struct AssociativityTemplate;

impl SpecTemplate for AssociativityTemplate {
    fn name(&self) -> &str {
        "associativity"
    }

    fn description(&self) -> &str {
        "ensures!(f(f(a, b), c) == f(a, f(b, c)))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig)
            && sig
                .return_type
                .as_deref()
                .is_some_and(|ret| same_type(ret, &sig.params[0].1))
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b, ty) = (&sig.params[0].0, &sig.params[1].0, &sig.params[0].1);
        vec![proposal(
            vec![],
            vec![format!(
                "forall(|c: {ty}| {fname}(result, c) == {fname}({a}, {fname}({b}, c)))"
            )],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![],
            vec![format!("result == {fname}({b}, {a})")],
        )]
    }
}

pub(crate) struct DistributivityTemplate;

impl SpecTemplate for DistributivityTemplate {
    fn name(&self) -> &str {
        "distributivity"
    }

    fn description(&self) -> &str {
        "ensures!(f(a, b + c) == f(a, b) + f(a, c))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_numeric_params(sig) && returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        let left_ty = &sig.params[1].1;
        let right_ty = &sig.params[0].1;

        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|c: {left_ty}| {fname}({a}, {b} + c) == {fname}({a}, {b}) + {fname}({a}, c))"
                )],
            ),
            proposal(
                vec![],
                vec![format!(
                    "forall(|c: {right_ty}| {fname}({a} + {b}, c) == {fname}({a}, c) + {fname}({b}, c))"
                )],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let a = &sig.params[0].0;
        vec![proposal(vec![], vec![format!("{fname}({a}, 0) == 0")])]
    }
}

pub(crate) struct ZeroElementTemplate;

impl SpecTemplate for ZeroElementTemplate {
    fn name(&self) -> &str {
        "zero_element"
    }

    fn description(&self) -> &str {
        "ensures!(f(x, 0) == 0) — absorbing element"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_numeric_params(sig) && returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![
            proposal(vec![format!("{b} == 0")], vec!["result == 0".to_string()]),
            proposal(vec![format!("{a} == 0")], vec!["result == 0".to_string()]),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![format!("{a} == 0"), format!("{b} == 0")],
            vec!["result == 0".to_string()],
        )]
    }
}

pub(crate) struct IdentityElementTemplate;

impl SpecTemplate for IdentityElementTemplate {
    fn name(&self) -> &str {
        "identity_element"
    }

    fn description(&self) -> &str {
        "ensures!(f(x, e) == x) — identity / neutral element"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_numeric_params(sig)
            && sig
                .return_type
                .as_deref()
                .is_some_and(|ret| same_type(ret, &sig.params[0].1))
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![
            proposal(vec![format!("{b} == 0")], vec![format!("result == {a}")]),
            proposal(vec![format!("{a} == 0")], vec![format!("result == {b}")]),
            proposal(vec![format!("{b} == 1")], vec![format!("result == {a}")]),
            proposal(vec![format!("{a} == 1")], vec![format!("result == {b}")]),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![format!("{a} == 0 && {b} == 0")],
            vec!["result == 0".to_string()],
        )]
    }
}

pub(crate) struct CancellationTemplate;

impl SpecTemplate for CancellationTemplate {
    fn name(&self) -> &str {
        "cancellation"
    }

    fn description(&self) -> &str {
        "f(x, y) == f(x, z) ==> y == z — left cancellation"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_numeric_params(sig) && returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b, ty) = (&sig.params[0].0, &sig.params[1].0, &sig.params[1].1);
        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|c: {ty}| result == {fname}({a}, c) ==> {b} == c)"
                )],
            ),
            proposal(
                vec![],
                vec![format!(
                    "forall(|c: {ty}| result == {fname}(c, {b}) ==> {a} == c)"
                )],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![format!("{a} != {b}")],
            vec!["result != 0".to_string()],
        )]
    }
}
