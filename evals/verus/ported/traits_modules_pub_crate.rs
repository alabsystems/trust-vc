// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/traits_modules_pub_crate.rs`.
//
// The upstream file is the `pub(crate)` visibility variant of
// traits_modules.rs. It exercises trait declarations and impls split across
// modules, method-call visibility, mode diagnostics, termination checks,
// private/open spec visibility, generic contracts, and Self/reference
// reasoning. TrustVc does not yet provide one-to-one replacement evidence for
// that full Rust/Verus language surface, so the manifest entry remains an
// unsupported gap.
//
// This Rust-valid scout slice records only the currently executable pieces:
// - A pub(crate) trait declaration in one module, implementation in another,
//   and generic caller in a third module can verify a simple inherited
//   postcondition.
// - A bad pub(crate) module-scoped trait impl body is rejected.
// - A bad pub(crate) module-scoped trait impl receiver-method body fails closed
//   at the current Self-encoding boundary.
// - Impl-side requires clauses on trait method implementations are rejected.
// - Duplicate returns clauses on a trait method declaration and its impl remain
//   a fail-closed contract-inheritance boundary.

#![allow(dead_code)]

pub const TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "pub_crate_module_trait_bound_dispatch_verified",
        "test_supported_9",
        "verified",
        1,
    ),
    (
        "pub_crate_module_false_assert_counterexample",
        "test_verify_2",
        "counterexample",
        1,
    ),
    (
        "pub_crate_module_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "pub_crate_module_grouped_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "pub_crate_module_conflicting_returns_clause_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
];

pub const TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "pub_crate_module_impl_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    (
        "pub_crate_module_grouped_impl_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    (
        "pub_crate_module_conflicting_returns_clause_currently_blocked",
        &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
    ),
];

pub fn traits_modules_pub_crate_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_CASES
}

pub fn traits_modules_pub_crate_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_ERROR_PATTERNS
}

mod pub_crate_module_contracts {
    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleDispatch {
        #[trust_vc::returns(true)]
        fn pub_crate_module_value(&self) -> bool;
    }

    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleRejectsBadBody {
        #[trust_vc::ensures(true)]
        fn pub_crate_module_false_assert_counterexample();
    }

    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleRejectsBadSelfBody {
        #[trust_vc::ensures(true)]
        fn pub_crate_module_self_false_assert_counterexample(&self);
    }

    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleRejectsImplRequires {
        #[trust_vc::ensures(true)]
        fn pub_crate_module_impl_requires_currently_blocked(x: i32) -> i32;
    }

    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleRejectsGroupedImplRequires {
        #[trust_vc::ensures(true)]
        fn pub_crate_module_grouped_impl_requires_currently_blocked(x: i32) -> i32;
    }

    #[trust_vc::trait_spec]
    pub(crate) trait PubCrateModuleConflictingReturns {
        #[trust_vc::returns(true)]
        fn pub_crate_module_conflicting_returns_clause_currently_blocked() -> bool;
    }
}

mod pub_crate_module_impls {
    pub(crate) struct PubCrateModuleGood;
    pub(crate) struct PubCrateModuleBad;
    pub(crate) struct PubCrateModuleSelfBad;
    pub(crate) struct PubCrateModuleImplRequires;
    pub(crate) struct PubCrateModuleGroupedImplRequires;
    pub(crate) struct PubCrateModuleConflicting;

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleDispatch for PubCrateModuleGood {
        fn pub_crate_module_value(&self) -> bool {
            true
        }
    }

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleRejectsBadBody for PubCrateModuleBad {
        fn pub_crate_module_false_assert_counterexample() {
            trust_vc::assert!(false);
        }
    }

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleRejectsBadSelfBody for PubCrateModuleSelfBad {
        fn pub_crate_module_self_false_assert_counterexample(&self) {
            trust_vc::assert!(false);
        }
    }

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleRejectsImplRequires
        for PubCrateModuleImplRequires
    {
        #[trust_vc::requires(x > 0)]
        fn pub_crate_module_impl_requires_currently_blocked(x: i32) -> i32 {
            x
        }
    }

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleRejectsGroupedImplRequires
        for PubCrateModuleGroupedImplRequires
    {
        #[trust_vc::contract(requires(x > 0))]
        fn pub_crate_module_grouped_impl_requires_currently_blocked(x: i32) -> i32 {
            x
        }
    }

    #[trust_vc::trait_impl]
    impl crate::pub_crate_module_contracts::PubCrateModuleConflictingReturns
        for PubCrateModuleConflicting
    {
        #[trust_vc::returns(false)]
        fn pub_crate_module_conflicting_returns_clause_currently_blocked() -> bool {
            false
        }
    }
}

mod pub_crate_module_callers {
    #[trust_vc::ensures(true)]
    pub(crate) fn pub_crate_module_trait_bound_dispatch_verified<
        T: crate::pub_crate_module_contracts::PubCrateModuleDispatch,
    >(
        value: T,
    ) {
        let returned = value.pub_crate_module_value();
        trust_vc::assert!(returned);
    }
}
