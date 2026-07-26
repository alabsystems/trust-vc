// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::common::{
    counterexample_i64, counterexample_value, has_param_named, has_single_numeric_param,
    has_two_same_type_numeric_params, is_numeric, is_unsigned, numeric_params, proposal,
    proposal_from_strs, returns_numeric,
};
use super::SpecTemplate;
use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

pub(crate) struct RangeTemplate;

impl SpecTemplate for RangeTemplate {
    fn name(&self) -> &str {
        "range"
    }

    fn description(&self) -> &str {
        "ensures!(result >= lo && result <= hi)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let mut proposals = Vec::new();

        for (name, ty) in &sig.params {
            if is_numeric(ty) {
                proposals.push(proposal(
                    vec![],
                    vec![format!("result >= {name}"), format!("result <= {name}")],
                ));
            }
        }

        let names: Vec<&str> = numeric_params(sig)
            .take(2)
            .map(|(name, _)| name.as_str())
            .collect();
        if names.len() == 2 {
            let (a, b) = (names[0], names[1]);
            proposals.push(proposal(
                vec![],
                vec![format!("result >= {a} && result <= {b}")],
            ));
            proposals.push(proposal(
                vec![],
                vec![format!("result >= {b} && result <= {a}")],
            ));
        }

        if sig.return_type.as_deref().is_some_and(is_unsigned) {
            proposals.push(proposal_from_strs(&[], &["result >= 0"]));
        }

        proposals
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        if let Some(value) = counterexample_value(feedback, "result") {
            if value.starts_with('-') {
                return vec![proposal(vec![], vec![format!("result >= {value}")])];
            }
        }

        self.instantiate(sig)
    }
}

pub(crate) struct NonNegativeTemplate;

impl SpecTemplate for NonNegativeTemplate {
    fn name(&self) -> &str {
        "non_negative"
    }

    fn description(&self) -> &str {
        "ensures!(result >= 0)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let mut proposals = vec![proposal_from_strs(&[], &["result >= 0"])];

        if let Some((name, _)) = sig.params.first() {
            if sig
                .return_type
                .as_deref()
                .is_some_and(|ret| !is_unsigned(ret))
            {
                proposals.push(proposal(
                    vec![format!("{name} >= 0")],
                    vec!["result >= 0".to_string()],
                ));
            }
        }

        proposals
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        if feedback.is_failed() {
            let requires: Vec<String> = numeric_params(sig)
                .map(|(name, _)| format!("{name} >= 0"))
                .collect();
            if !requires.is_empty() {
                return vec![proposal(requires, vec!["result >= 0".to_string()])];
            }
        }

        self.instantiate(sig)
    }
}

pub(crate) struct MonotonicTemplate;

impl SpecTemplate for MonotonicTemplate {
    fn name(&self) -> &str {
        "monotonic"
    }

    fn description(&self) -> &str {
        "requires!(a <= b) ensures!(f(a) <= f(b))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_two_same_type_numeric_params(sig) && returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let (a, b) = (&sig.params[0].0, &sig.params[1].0);
        let fname = &sig.name;

        vec![
            proposal(
                vec![format!("{a} <= {b}")],
                vec![format!("result <= {fname}({b}, {a})")],
            ),
            proposal(
                vec![format!("{a} <= {b}")],
                vec![format!("result >= {a} && result <= {b}")],
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
            vec![format!("{a} <= {b}")],
            vec![format!("result >= {a} || result <= {b}")],
        )]
    }
}

pub(crate) struct InjectiveTemplate;

impl SpecTemplate for InjectiveTemplate {
    fn name(&self) -> &str {
        "injective"
    }

    fn description(&self) -> &str {
        "ensures!(x1 != x2 ==> f(x1) != f(x2))"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        has_single_numeric_param(sig) && returns_numeric(sig)
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let (name, ty) = (&sig.params[0].0, &sig.params[0].1);
        let fname = &sig.name;

        vec![
            proposal(
                vec![],
                vec![format!(
                    "forall(|y: {ty}| y != {name} ==> {fname}(y) != result)"
                )],
            ),
            proposal(
                vec![format!("{name} != 0")],
                vec!["result != 0".to_string()],
            ),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let name = &sig.params[0].0;
        vec![proposal(
            vec![],
            vec![format!("result == {name} || result != {name}")],
        )]
    }
}

pub(crate) struct BoundedByInputTemplate;

impl SpecTemplate for BoundedByInputTemplate {
    fn name(&self) -> &str {
        "bounded_by_input"
    }

    fn description(&self) -> &str {
        "ensures!(result <= x) or ensures!(result >= x)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_numeric(sig) && numeric_params(sig).next().is_some()
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        numeric_params(sig)
            .flat_map(|(name, _)| {
                [
                    proposal(vec![], vec![format!("result <= {name}")]),
                    proposal(vec![], vec![format!("result >= {name}")]),
                ]
            })
            .collect()
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let Some((name, _)) = sig.params.first() else {
            return self.instantiate(sig);
        };

        match (
            counterexample_i64(feedback, "result"),
            counterexample_i64(feedback, name),
        ) {
            (Some(result), Some(input)) if result > input => {
                vec![proposal(vec![], vec![format!("result >= {name}")])]
            }
            (Some(_), Some(_)) => vec![proposal(vec![], vec![format!("result <= {name}")])],
            _ => self.instantiate(sig),
        }
    }
}

pub(crate) struct DivisionSafetyTemplate;

impl SpecTemplate for DivisionSafetyTemplate {
    fn name(&self) -> &str {
        "division_safety"
    }

    fn description(&self) -> &str {
        "requires!(divisor != 0)"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        sig.params.len() >= 2
            && numeric_params(sig).count() >= 2
            && has_param_named(
                sig,
                &["b", "divisor", "denom", "denominator", "d", "y", "rhs"],
            )
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let divisor_names = ["b", "divisor", "denom", "denominator", "d", "y", "rhs"];
        let mut proposals = Vec::new();

        for (name, ty) in &sig.params {
            if is_numeric(ty) && divisor_names.contains(&name.as_str()) {
                proposals.push(proposal(
                    vec![format!("{name} != 0")],
                    vec!["true".to_string()],
                ));
                if returns_numeric(sig) {
                    proposals.push(proposal(
                        vec![format!("{name} != 0")],
                        vec![format!("result >= {name} || result <= {name}")],
                    ));
                }
            }
        }

        proposals
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        let requires: Vec<String> = numeric_params(sig)
            .map(|(name, _)| format!("{name} != 0"))
            .collect();
        if requires.is_empty() {
            return vec![];
        }

        vec![proposal(requires, vec!["true".to_string()])]
    }
}

pub(crate) struct BoundednessTemplate;

impl SpecTemplate for BoundednessTemplate {
    fn name(&self) -> &str {
        "boundedness"
    }

    fn description(&self) -> &str {
        "ensures!(result <= f(inputs)) — bounded output"
    }

    fn applicable_to(&self, sig: &FunctionSignature) -> bool {
        returns_numeric(sig) && sig.params.len() >= 2 && numeric_params(sig).next().is_some()
    }

    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations> {
        let names: Vec<&str> = numeric_params(sig)
            .map(|(name, _)| name.as_str())
            .take(2)
            .collect();
        if names.len() < 2 {
            return vec![];
        }

        let (a, b) = (names[0], names[1]);
        vec![
            proposal(
                vec![format!("{a} >= 0"), format!("{b} >= 0")],
                vec![format!("result <= {a} + {b}")],
            ),
            proposal(
                vec![format!("{a} >= 0"), format!("{b} >= 0")],
                vec![format!("result <= {a} * {b}")],
            ),
            proposal(vec![], vec![format!("result <= {a} || result <= {b}")]),
        ]
    }

    fn refine(
        &self,
        sig: &FunctionSignature,
        _feedback: &ProofFeedback,
    ) -> Vec<ProposedAnnotations> {
        if sig.return_type.as_deref().is_some_and(is_unsigned) {
            return vec![proposal_from_strs(&[], &["result >= 0"])];
        }

        let Some((name, _)) = numeric_params(sig).next() else {
            return vec![];
        };
        vec![proposal(
            vec![],
            vec![format!("result >= 0 || result <= {name}")],
        )]
    }
}
