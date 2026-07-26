// trust-vc-oracle — Specification templates for counterexample-guided spec mining
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

mod algebraic;
mod collection;
mod common;
mod effect;
mod numeric;
mod relational;
mod unary;

/// A parameterized specification pattern for CGSR.
pub trait SpecTemplate: Send + Sync {
    /// Human-readable template name (for example, `range` or `sorted`).
    fn name(&self) -> &str;

    /// One-line shape of the specification template.
    fn description(&self) -> &str;

    /// Whether the template can produce meaningful specs for `sig`.
    fn applicable_to(&self, sig: &FunctionSignature) -> bool;

    /// Produce one or more initial candidate specifications for `sig`.
    fn instantiate(&self, sig: &FunctionSignature) -> Vec<ProposedAnnotations>;

    /// Refine candidates after a failed verification attempt.
    fn refine(&self, sig: &FunctionSignature, feedback: &ProofFeedback)
        -> Vec<ProposedAnnotations>;
}

/// Returns all available specification templates.
#[must_use]
pub fn all_templates() -> Vec<Box<dyn SpecTemplate>> {
    vec![
        Box::new(numeric::RangeTemplate),
        Box::new(numeric::NonNegativeTemplate),
        Box::new(numeric::MonotonicTemplate),
        Box::new(unary::IdempotentTemplate),
        Box::new(collection::LengthPreservingTemplate),
        Box::new(collection::SortedTemplate),
        Box::new(collection::PermutationTemplate),
        Box::new(numeric::InjectiveTemplate),
        Box::new(numeric::BoundedByInputTemplate),
        Box::new(unary::IdentityTemplate),
        Box::new(unary::PreservesPropertyTemplate),
        Box::new(algebraic::CommutativityTemplate),
        Box::new(algebraic::AssociativityTemplate),
        Box::new(algebraic::DistributivityTemplate),
        Box::new(collection::InvariantTemplate),
        Box::new(effect::ErrorFreeTemplate),
        Box::new(relational::TransitivityTemplate),
        Box::new(relational::ReflexivityTemplate),
        Box::new(relational::SymmetryTemplate),
        Box::new(relational::AntiSymmetryTemplate),
        Box::new(relational::TotalityTemplate),
        Box::new(unary::SurjectiveTemplate),
        Box::new(effect::NullabilityGuardTemplate),
        Box::new(unary::InvolutionTemplate),
        Box::new(unary::FixedPointTemplate),
        Box::new(algebraic::ZeroElementTemplate),
        Box::new(algebraic::IdentityElementTemplate),
        Box::new(algebraic::CancellationTemplate),
        Box::new(collection::ContainmentPreservingTemplate),
        Box::new(collection::SubsetBoundTemplate),
        Box::new(numeric::DivisionSafetyTemplate),
        Box::new(numeric::BoundednessTemplate),
    ]
}

/// Returns only the templates applicable to the given function signature.
#[must_use]
pub fn applicable_templates(sig: &FunctionSignature) -> Vec<Box<dyn SpecTemplate>> {
    all_templates()
        .into_iter()
        .filter(|template| template.applicable_to(sig))
        .collect()
}
