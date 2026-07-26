// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Contract 1: term_to_literal
// ---------------------------------------------------------------------------

/// Abstract term identifier for contract specification.
///
/// Maps to `ay_core::TermId(u32)` in the ay implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ContractTermId(pub(crate) u32);

/// Abstract SAT variable for contract specification.
///
/// Maps to `ay_sat::Variable(u32)` in the ay implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ContractVariable(pub(crate) u32);

/// Abstract SAT literal (variable + polarity) for contract specification.
///
/// Maps to `ay_sat::Literal` in the ay implementation.
/// Encoding: positive = 2*var, negative = 2*var + 1 (matching ay-sat).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ContractLiteral(pub(crate) u32);

impl ContractLiteral {
    /// Create a positive literal for a variable.
    #[must_use]
    pub(crate) fn positive(var: ContractVariable) -> Self {
        Self(var.0 << 1)
    }

    /// Create a negative literal for a variable.
    #[must_use]
    pub(crate) fn negative(var: ContractVariable) -> Self {
        Self((var.0 << 1) | 1)
    }

    /// Get the variable this literal refers to.
    #[must_use]
    pub(crate) fn variable(self) -> ContractVariable {
        ContractVariable(self.0 >> 1)
    }

    /// Check if this is a positive literal.
    #[must_use]
    pub(crate) fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Get the negation of this literal.
    #[must_use]
    pub(crate) fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// Get the raw encoded value.
    #[must_use]
    pub(crate) fn raw(self) -> u32 {
        self.0
    }
}

/// Contract abstraction for ay-dpll's theory atom registry.
///
/// Captures the pre/postconditions of `TheoryExtension::term_to_literal`:
///
/// ```text
/// fn term_to_literal(&self, term: TermId, value: bool) -> Option<Literal>
///
/// requires: true  (no preconditions)
///
/// ensures |result|:
///   self.term_to_var.contains_key(&term) ==> result.is_some()
///   !self.term_to_var.contains_key(&term) ==> result.is_none()
///   result.is_some() ==> result.unwrap().variable().id() == self.term_to_var[&term]
///   result.is_some() ==> result.unwrap().is_positive() == value
/// ```
///
/// Any type implementing this trait agrees to satisfy these postconditions.
pub(crate) trait TheoryAtomRegistry {
    /// Returns the SAT variable mapped to `term`, if one exists.
    ///
    /// # Contract
    ///
    /// This is the observable state predicate: whether a term has been
    /// registered with a SAT variable mapping.
    fn var_for_term(&self, term: ContractTermId) -> Option<ContractVariable>;

    /// Convert a theory term + polarity to a SAT literal.
    ///
    /// # Contract (postconditions)
    ///
    /// 1. If `term` is registered (`var_for_term` returns `Some`),
    ///    the result MUST be `Some(lit)` where:
    ///    - `lit.variable() == var_for_term(term).unwrap()`
    ///    - `lit.is_positive() == value`
    ///
    /// 2. If `term` is NOT registered (`var_for_term` returns `None`),
    ///    the result MUST be `None`.
    fn term_to_literal(&self, term: ContractTermId, value: bool) -> Option<ContractLiteral>;
}

/// Validates that a `term_to_literal` result satisfies the contract.
///
/// Returns `true` if the postconditions hold. This is the executable
/// specification that tests call to verify implementations.
#[must_use]
pub(crate) fn validate_term_to_literal_postcondition(
    registry: &dyn TheoryAtomRegistry,
    term: ContractTermId,
    value: bool,
    result: Option<ContractLiteral>,
) -> bool {
    let registered = registry.var_for_term(term);

    // Postcondition 1: registered ==> result.is_some()
    if registered.is_some() && result.is_none() {
        return false;
    }

    // Postcondition 2: !registered ==> result.is_none()
    if registered.is_none() && result.is_some() {
        return false;
    }

    // Postcondition 3 & 4: when Some, variable and polarity match
    if let (Some(var), Some(lit)) = (registered, result) {
        if lit.variable() != var {
            return false;
        }
        if lit.is_positive() != value {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Contract 2: TheoryKind::as_str
// ---------------------------------------------------------------------------

/// Known theory solver kinds (mirrors `AYTheoryKind` from trust-vc-kernel bridge).
///
/// This is a trust-vc-core-local enum capturing the same variants as
/// `trust_vc_kernel::bridge::AYTheoryKind`, without requiring a dependency edge.
///
/// # Contract
///
/// `as_str()` must return a non-empty, known string for every variant.
/// The mapping is total and exhaustive — no variant may return an empty string
/// or a dynamically generated string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ContractTheoryKind {
    /// Equality and uninterpreted functions.
    Euf,
    /// Linear real arithmetic.
    Lra,
    /// Non-linear integer arithmetic.
    Nia,
    /// Bitvector theory.
    BitVector,
    /// Array theory (select/store).
    Array,
    /// Sequence theory.
    Sequence,
    /// Other / unclassified.
    Other,
}

/// Contract abstraction for the `as_str` method on theory kind enums.
///
/// Captures the postcondition:
///
/// ```text
/// fn as_str(&self) -> &'static str
///
/// requires: true
///
/// ensures |result|:
///   !result.is_empty()
///   // The result is a known, fixed label (not dynamically generated)
/// ```
pub(crate) trait TheoryKindLabel {
    /// Human-readable label for this theory kind.
    ///
    /// # Contract (postconditions)
    ///
    /// 1. The result is never empty.
    /// 2. The result is a `&'static str` (compile-time constant).
    /// 3. Distinct variants produce distinct labels.
    fn as_str(&self) -> &'static str;
}

impl TheoryKindLabel for ContractTheoryKind {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Euf => "EUF",
            Self::Lra => "LRA",
            Self::Nia => "NIA",
            Self::BitVector => "BV",
            Self::Array => "Array",
            Self::Sequence => "Seq",
            Self::Other => "Other",
        }
    }
}

/// Validates that an `as_str` result satisfies the contract postconditions.
///
/// Returns `true` if the postconditions hold.
#[must_use]
pub(crate) fn validate_as_str_postcondition(result: &str) -> bool {
    // Postcondition 1: result is non-empty
    !result.is_empty()
}

// ---------------------------------------------------------------------------
// Reference implementation of TheoryAtomRegistry
// ---------------------------------------------------------------------------

/// Reference implementation of [`TheoryAtomRegistry`] for testing.
///
/// Uses a `HashMap<ContractTermId, ContractVariable>` as the term-to-var map,
/// matching the structure of ay-dpll's `TheoryExtension`.
pub(crate) struct HashMapAtomRegistry {
    term_to_var: HashMap<ContractTermId, ContractVariable>,
}

impl HashMapAtomRegistry {
    /// Create an empty registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            term_to_var: HashMap::new(),
        }
    }

    /// Register a term-to-variable mapping.
    pub(crate) fn register(&mut self, term: ContractTermId, var: ContractVariable) {
        self.term_to_var.insert(term, var);
    }
}

impl TheoryAtomRegistry for HashMapAtomRegistry {
    fn var_for_term(&self, term: ContractTermId) -> Option<ContractVariable> {
        self.term_to_var.get(&term).copied()
    }

    fn term_to_literal(&self, term: ContractTermId, value: bool) -> Option<ContractLiteral> {
        self.var_for_term(term).map(|var| {
            if value {
                ContractLiteral::positive(var)
            } else {
                ContractLiteral::negative(var)
            }
        })
    }
}

// ---------------------------------------------------------------------------
// extern_spec! registrations for ay contracts
// ---------------------------------------------------------------------------

/// Registers the `term_to_literal` contract as an extern_spec entry.
///
/// This creates the same kind of `ExternSpecContract` that `extern_spec!` blocks
/// produce, allowing the ay contract to participate in the existing extern_spec
/// verification infrastructure.
///
/// The registered contract uses the ay-dpll function path as the target:
/// `ay_dpll::TheoryExtension::term_to_literal`
pub(crate) fn register_ay_term_to_literal_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_dpll::TheoryExtension::term_to_literal",
        &[
            // requires: true (no preconditions)
            "true".to_string(),
        ],
        &[
            // ensures: registered term yields Some with correct variable and polarity
            "self.term_to_var.contains_key(&term) ==> result.is_some()".to_string(),
            "!self.term_to_var.contains_key(&term) ==> result.is_none()".to_string(),
        ],
    );
}

/// Registers the `as_str` contract for `AYTheoryKind`.
///
/// The registered contract uses the trust-vc-kernel bridge path as the target.
pub(crate) fn register_ay_theory_kind_as_str_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "trust_vc_kernel::bridge::AYTheoryKind::as_str",
        &[
            // requires: true (no preconditions)
            "true".to_string(),
        ],
        &[
            // ensures: result is non-empty
            "!result.is_empty()".to_string(),
        ],
    );
}
