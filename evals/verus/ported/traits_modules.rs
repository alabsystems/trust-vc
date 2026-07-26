// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/traits_modules.rs`.
//
// This is scout coverage only. The upstream file exercises Verus traits split
// across modules, mode/diagnostic checks, termination, generic trait contracts,
// private/open spec visibility, and Self/reference reasoning. TrustVc does not
// yet provide replacement evidence for that full surface, so the manifest entry
// remains `unsupported-gap`.
//
// This Rust-valid subset records the currently executable pieces:
// - A trait method declaration in one module and implementation in another
//   module can inherit and verify a simple return contract.
// - A false assertion in a module-scoped trait impl body is rejected.
// - Impl-side requires clauses on trait method implementations are rejected.
// - Module-local trait aliases in impl paths and fully-qualified calls remain
//   fail-closed boundaries.
// - Duplicate returns clauses on a trait method declaration and its impl remain
//   a fail-closed contract-inheritance boundary.

#![allow(dead_code)]

pub const TRAITS_MODULES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "trait_modules_impl_returns_true_verified",
        "test_supported_9",
        "verified",
        1,
    ),
    (
        "trait_modules_impl_false_assert_counterexample",
        "test_verify_2",
        "counterexample",
        1,
    ),
    (
        "trait_modules_alias_impl_returns_true_currently_blocked",
        "test_supported_9",
        "error",
        0,
    ),
    (
        "trait_modules_bad_alias_value_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "trait_modules_alias_qualified_call_currently_blocked",
        "test_supported_9",
        "error",
        0,
    ),
    (
        "trait_modules_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "trait_modules_grouped_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "trait_modules_conflicting_returns_clause_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
];

pub const TRAITS_MODULES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "trait_modules_alias_impl_returns_true_currently_blocked",
        &["Cannot verify context with only assumptions and no assertions"],
    ),
    (
        "trait_modules_bad_alias_value_currently_blocked",
        &["Cannot verify context with only assumptions and no assertions"],
    ),
    (
        "trait_modules_alias_qualified_call_currently_blocked",
        &["type inference failed: unknown return type for function"],
    ),
    (
        "trait_modules_impl_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    (
        "trait_modules_grouped_impl_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    (
        "trait_modules_conflicting_returns_clause_currently_blocked",
        &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
    ),
];

pub fn traits_modules_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    TRAITS_MODULES_RS_EXPECTED_CASES
}

pub fn traits_modules_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    TRAITS_MODULES_RS_EXPECTED_ERROR_PATTERNS
}

mod trait_modules_contracts {
    #[trust_vc::trait_spec]
    pub trait TraitModulesReturnsTrue {
        #[trust_vc::returns(true)]
        fn trait_modules_impl_returns_true_verified() -> bool;
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesAliasReturnsTrue {
        #[trust_vc::returns(true)]
        fn trait_modules_alias_impl_returns_true_currently_blocked() -> bool;
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesRejectsBadBody {
        #[trust_vc::ensures(true)]
        fn trait_modules_impl_false_assert_counterexample();
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesRejectsAliasBadBody {
        #[trust_vc::returns(true)]
        fn trait_modules_bad_alias_value_currently_blocked() -> bool;
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesRejectsImplRequires {
        #[trust_vc::ensures(true)]
        fn trait_modules_impl_requires_currently_blocked(x: i32) -> i32;
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesRejectsGroupedImplRequires {
        #[trust_vc::ensures(true)]
        fn trait_modules_grouped_impl_requires_currently_blocked(x: i32) -> i32;
    }

    #[trust_vc::trait_spec]
    pub trait TraitModulesConflictingReturns {
        #[trust_vc::returns(true)]
        fn trait_modules_conflicting_returns_clause_currently_blocked() -> bool;
    }
}

mod trait_modules_impls {
    use crate::trait_modules_contracts::{
        TraitModulesAliasReturnsTrue as AliasReturnsTrue,
        TraitModulesRejectsAliasBadBody as AliasRejectsBadBody,
    };

    pub struct TraitModulesGood;
    pub struct TraitModulesAliasGood;
    pub struct TraitModulesAliasBad;
    pub struct TraitModulesBad;
    pub struct TraitModulesImplRequires;
    pub struct TraitModulesGroupedImplRequires;
    pub struct TraitModulesConflicting;

    #[trust_vc::trait_impl]
    impl crate::trait_modules_contracts::TraitModulesReturnsTrue for TraitModulesGood {
        fn trait_modules_impl_returns_true_verified() -> bool {
            true
        }
    }

    #[trust_vc::trait_impl]
    impl AliasReturnsTrue for TraitModulesAliasGood {
        fn trait_modules_alias_impl_returns_true_currently_blocked() -> bool {
            true
        }
    }

    #[trust_vc::trait_impl]
    impl AliasRejectsBadBody for TraitModulesAliasBad {
        fn trait_modules_bad_alias_value_currently_blocked() -> bool {
            false
        }
    }

    #[trust_vc::trait_impl]
    impl crate::trait_modules_contracts::TraitModulesRejectsBadBody for TraitModulesBad {
        fn trait_modules_impl_false_assert_counterexample() {
            trust_vc::assert!(false);
        }
    }

    #[trust_vc::trait_impl]
    impl crate::trait_modules_contracts::TraitModulesRejectsImplRequires for TraitModulesImplRequires {
        #[trust_vc::requires(x > 0)]
        fn trait_modules_impl_requires_currently_blocked(x: i32) -> i32 {
            x
        }
    }

    #[trust_vc::trait_impl]
    impl crate::trait_modules_contracts::TraitModulesRejectsGroupedImplRequires
        for TraitModulesGroupedImplRequires
    {
        #[trust_vc::contract(requires(x > 0))]
        fn trait_modules_grouped_impl_requires_currently_blocked(x: i32) -> i32 {
            x
        }
    }

    #[trust_vc::trait_impl]
    impl crate::trait_modules_contracts::TraitModulesConflictingReturns for TraitModulesConflicting {
        #[trust_vc::returns(false)]
        fn trait_modules_conflicting_returns_clause_currently_blocked() -> bool {
            false
        }
    }
}

mod trait_modules_alias_callers {
    use crate::trait_modules_contracts::TraitModulesAliasReturnsTrue as AliasReturnsTrue;
    use crate::trait_modules_impls::TraitModulesAliasGood;

    #[trust_vc::ensures(true)]
    pub fn trait_modules_alias_qualified_call_currently_blocked() {
        let returned =
            <TraitModulesAliasGood as AliasReturnsTrue>::trait_modules_alias_impl_returns_true_currently_blocked();
        trust_vc::assert!(returned);
    }
}
