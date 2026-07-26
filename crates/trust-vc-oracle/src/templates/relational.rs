// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{has_two_same_type_params, proposal, returns_bool};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct TransitivityTemplate;

impl SpecTemplate for TransitivityTemplate {
    fn name(&self) -> &str {
        "transitivity"
    }

    fn description(&self) -> &str {
        "f(a, b) && f(b, c) ==> f(a, c)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && returns_bool(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b, ty) = (&sig.params[0].0, &sig.params[1].0, &sig.params[0].1);
        vec![proposal(
            vec![format!("{fname}({a}, {b})")],
            vec![format!(
                "forall(|c: {ty}| {fname}({b}, c) ==> {fname}({a}, c))"
            )],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let a = &sig.params[0].0;
        vec![proposal(vec![], vec![format!("{fname}({a}, {a})")])]
    }
}

pub(crate) struct ReflexivityTemplate;

impl SpecTemplate for ReflexivityTemplate {
    fn name(&self) -> &str {
        "reflexivity"
    }

    fn description(&self) -> &str {
        "ensures!(f(a, a) == true)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && returns_bool(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![
            proposal(vec![], vec![format!("{fname}({a}, {a}) == true")]),
            proposal(
                vec![format!("{a} == {b}")],
                vec!["result == true".to_string()],
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
            vec![format!("{a} == {b}")],
            vec!["result == true || result == false".to_string()],
        )]
    }
}

pub(crate) struct SymmetryTemplate;

impl SpecTemplate for SymmetryTemplate {
    fn name(&self) -> &str {
        "symmetry"
    }

    fn description(&self) -> &str {
        "ensures!(f(a, b) == f(b, a))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && returns_bool(sig)
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
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![format!("result == true && {fname}({b}, {a}) == true")],
            vec![format!("{a} == {b}")],
        )]
    }
}

pub(crate) struct AntiSymmetryTemplate;

impl SpecTemplate for AntiSymmetryTemplate {
    fn name(&self) -> &str {
        "antisymmetry"
    }

    fn description(&self) -> &str {
        "f(a, b) && f(b, a) ==> a == b"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && returns_bool(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![format!("result == true && {fname}({b}, {a}) == true")],
            vec![format!("{a} == {b}")],
        )]
    }

    fn refine(
        &self,
        _sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        vec![proposal(
            vec![],
            vec!["result == true || result == false".to_string()],
        )]
    }
}

pub(crate) struct TotalityTemplate;

impl SpecTemplate for TotalityTemplate {
    fn name(&self) -> &str {
        "totality"
    }

    fn description(&self) -> &str {
        "ensures!(f(a, b) || f(b, a))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_params(sig) && returns_bool(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        vec![proposal(
            vec![],
            vec![format!("result == true || {fname}({b}, {a}) == true")],
        )]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let fname = &sig.name;
        let a = &sig.params[0].0;
        vec![proposal(vec![], vec![format!("{fname}({a}, {a})")])]
    }
}
