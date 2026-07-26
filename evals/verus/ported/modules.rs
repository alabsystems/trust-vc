// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `source/rust_verify_test/tests/modules.rs`.
//
// This file intentionally keeps the corpus manifest entry as unsupported-gap.
// It records only Rust-valid module evidence current TrustVc can execute through
// source extraction:
// - public module ADT field projection;
// - public/private module-qualified exec helper calls, crate-qualified helper
//   calls, nested module-qualified helper calls, and block-local helper
//   imports/aliases;
// - stable module-shaped false-claim counterexamples; and
// - fail-closed module spec-function, opaque/reveal, contract-helper,
//   visibility/open/closed, proof/main mode, and uninterp/open boundaries.
//
// It is not a full modules.rs port. Verus open/closed spec visibility,
// opaque_outside_module parity, pub/open diagnostics, proof/main mode
// diagnostics, and uninterp/open syntax remain unsupported replacement gaps.

#![allow(dead_code)]

use trust_vc_types::int;

pub const MODULES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "module_public_struct_field_projection_verified",
        "test_mod_adt_0",
        "verified",
        1,
    ),
    (
        "module_qualified_helper_contract_verified",
        "test_mod_adt_1 / module-qualified helper call shape",
        "verified",
        1,
    ),
    (
        "module_use_alias_helper_contract_verified",
        "test_mod_adt_1 / imported module helper alias shape",
        "verified",
        1,
    ),
    (
        "module_public_qualified_helper_contract_verified",
        "test_mod_adt_1 public module-qualified helper call shape",
        "verified",
        1,
    ),
    (
        "module_private_qualified_helper_contract_verified",
        "test_mod_adt_1 private module-qualified helper call shape",
        "verified",
        1,
    ),
    (
        "module_imported_group_helper_contract_verified",
        "test_mod_adt_1 grouped imported helper call shape",
        "verified",
        1,
    ),
    (
        "module_crate_qualified_helper_contract_verified",
        "test_mod_adt_1 crate-qualified helper call shape",
        "verified",
        1,
    ),
    (
        "module_nested_qualified_helper_contract_verified",
        "open_crate/open_super/open_path nested module helper call shape",
        "verified",
        1,
    ),
    // Module spec-fn calls that now resolve + verify (grouped with the other
    // verified cases so the port order matches the by-verdict test inventory).
    (
        "module_public_spec_fn_qualified_currently_blocked",
        "test_mod_adt_1 qualified module spec-function boundary",
        "verified",
        1,
    ),
    (
        "module_public_spec_fn_alias_currently_blocked",
        "test_mod_adt_1 imported module spec-function alias boundary",
        "verified",
        1,
    ),
    (
        "module_public_spec_fn_in_contract_currently_blocked",
        "test_mod_child_ok module spec-function contract registration boundary",
        "verified",
        1,
    ),
    (
        "module_opaque_spec_fn_imported_reveal_currently_blocked",
        "test_mod_fn_publish_opaque_reveal imported opaque reveal boundary",
        "verified",
        1,
    ),
    (
        "module_public_struct_scope_false_counterexample",
        "test_mod_adt_0 module ADT false assertion sentinel",
        "counterexample",
        1,
    ),
    (
        "module_imported_public_struct_false_counterexample",
        "test_mod_adt_0 imported public module ADT false assertion sentinel",
        "counterexample",
        1,
    ),
    (
        "module_public_spec_fn_qualified_false_currently_blocked",
        "test_mod_adt_1 false qualified module spec-function boundary",
        "counterexample",
        1,
    ),
    (
        "module_opaque_spec_fn_without_reveal_currently_blocked",
        "test_mod_fn_publish_opaque_no_reveal",
        "counterexample",
        1,
    ),
    (
        "module_private_spec_fn_qualified_currently_blocked",
        "test_requires_private private module spec-function registration boundary",
        "error",
        0,
    ),
    (
        "module_qualified_helper_contract_in_ensures_fails_closed",
        "test_mod_sibling_fail contract-helper boundary shape",
        "error",
        0,
    ),
    (
        "module_qualified_helper_contract_in_requires_fails_closed",
        "test_requires_private requires-helper boundary shape",
        "error",
        0,
    ),
    (
        "module_self_qualified_helper_contract_in_ensures_fails_closed",
        "test_mod_sibling_fail self-qualified contract-helper boundary shape",
        "error",
        0,
    ),
    (
        "module_qualified_opaque_reveal_fails_closed",
        "test_mod_fn_publish_opaque_reveal qualified reveal target boundary",
        "error",
        0,
    ),
    (
        "module_open_without_pub_diagnostic_fails_closed",
        "test_publish_but_not_marked_pub open-without-pub diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_open_more_public_than_function_diagnostic_fails_closed",
        "open_more_public_than_function visibility diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_open_proof_mode_diagnostic_fails_closed",
        "publish_proof_fail proof/open mode diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_open_exec_mode_diagnostic_fails_closed",
        "publish_exec_fail exec/open mode diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_closed_exec_mode_diagnostic_fails_closed",
        "publish_exec_fail exec/closed mode diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_open_crate_visibility_diagnostic_fails_closed",
        "open_crate visibility boundary",
        "error",
        0,
    ),
    (
        "module_open_super_visibility_diagnostic_fails_closed",
        "open_super visibility boundary",
        "error",
        0,
    ),
    (
        "module_open_path_visibility_diagnostic_fails_closed",
        "open_path visibility boundary",
        "error",
        0,
    ),
    (
        "module_main_proof_mode_diagnostic_fails_closed",
        "main_proof_fail main/proof mode diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_main_spec_mode_diagnostic_fails_closed",
        "main_spec_fail main/spec mode diagnostic boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_exec_syntax_diagnostic_fails_closed",
        "uninterp_exec_fail uninterp exec syntax boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_spec_body_diagnostic_fails_closed",
        "uninterp_spec_body_free_fail uninterp spec body boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_spec_body_assoc_diagnostic_fails_closed",
        "uninterp_spec_body_assoc_fail uninterp assoc spec body boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_spec_body_trait_diagnostic_fails_closed",
        "uninterp_spec_body_trait_fail uninterp trait spec body boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_spec_body_trait_impl_diagnostic_fails_closed",
        "uninterp_spec_body_trait_impl_fail uninterp trait impl boundary",
        "error",
        0,
    ),
    (
        "module_uninterp_open_syntax_diagnostic_fails_closed",
        "uninterp_open_fail uninterp/open syntax boundary",
        "error",
        0,
    ),
];

pub const MODULES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "module_private_spec_fn_qualified_currently_blocked",
        &[
            "type inference failed: unknown return type for function",
            "module_specs::private_truth",
        ],
    ),
    (
        "module_qualified_helper_contract_in_ensures_fails_closed",
        &[
            "Unsupported call to sibling helper `module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_qualified_helper_contract_in_requires_fails_closed",
        &[
            "Unsupported call to sibling helper `module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_self_qualified_helper_contract_in_ensures_fails_closed",
        &[
            "Unsupported call to sibling helper `self::module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_qualified_opaque_reveal_fails_closed",
        &[
            "supports only unqualified function names",
            "module_adt :: opaque_is_four_doors",
        ],
    ),
    (
        "module_open_without_pub_diagnostic_fails_closed",
        &["unknown contract clause `open_without_pub` in #[contract]"],
    ),
    (
        "module_open_more_public_than_function_diagnostic_fails_closed",
        &["unknown contract clause `open_more_public_than_function` in #[contract]"],
    ),
    (
        "module_open_proof_mode_diagnostic_fails_closed",
        &["unknown contract clause `open_proof_mode` in #[contract]"],
    ),
    (
        "module_open_exec_mode_diagnostic_fails_closed",
        &["unknown contract clause `open_exec_mode` in #[contract]"],
    ),
    (
        "module_closed_exec_mode_diagnostic_fails_closed",
        &["unknown contract clause `closed_exec_mode` in #[contract]"],
    ),
    (
        "module_open_crate_visibility_diagnostic_fails_closed",
        &["unknown contract clause `open_crate_visibility` in #[contract]"],
    ),
    (
        "module_open_super_visibility_diagnostic_fails_closed",
        &["unknown contract clause `open_super_visibility` in #[contract]"],
    ),
    (
        "module_open_path_visibility_diagnostic_fails_closed",
        &["unknown contract clause `open_path_visibility` in #[contract]"],
    ),
    (
        "module_main_proof_mode_diagnostic_fails_closed",
        &["unknown contract clause `main_proof_mode` in #[contract]"],
    ),
    (
        "module_main_spec_mode_diagnostic_fails_closed",
        &["unknown contract clause `main_spec_mode` in #[contract]"],
    ),
    (
        "module_uninterp_exec_syntax_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_exec_syntax` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_spec_body` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_assoc_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_spec_body_assoc` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_trait_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_spec_body_trait` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_trait_impl_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_spec_body_trait_impl` in #[contract]"],
    ),
    (
        "module_uninterp_open_syntax_diagnostic_fails_closed",
        &["unknown contract clause `uninterp_open_syntax` in #[contract]"],
    ),
];

pub fn modules_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MODULES_RS_EXPECTED_CASES
}

pub fn modules_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MODULES_RS_EXPECTED_ERROR_PATTERNS
}

mod module_adt {
    use super::int;

    #[derive(Clone, Copy)]
    pub struct Car {
        pub four_doors: bool,
        pub passengers: int,
    }

    #[trust_vc::spec]
    pub fn is_four_doors(c: Car) -> bool {
        c.four_doors
    }

    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn opaque_is_four_doors(c: Car) -> bool {
        c.four_doors
    }
}

type ModuleCar = module_adt::Car;

mod module_helpers {
    use super::int;

    #[trust_vc::requires(v >= 0)]
    #[trust_vc::ensures(result > v)]
    pub fn inc_positive(v: int) -> int {
        v + 1
    }

    #[trust_vc::ensures(result)]
    pub fn always_true() -> bool {
        true
    }
}

pub mod public_module_helpers {
    use super::int;

    #[trust_vc::requires(v >= 0)]
    #[trust_vc::ensures(result == v + 2)]
    pub fn add_two(v: int) -> int {
        v + 2
    }
}

pub mod public_nested_helpers {
    use super::int;

    pub mod child {
        use super::int;

        #[trust_vc::requires(v >= 0)]
        #[trust_vc::ensures(result == v + 4)]
        pub fn add_four(v: int) -> int {
            v + 4
        }
    }
}

mod private_module_helpers {
    use super::int;

    #[trust_vc::requires(v >= 0)]
    #[trust_vc::ensures(result == v + 3)]
    fn add_three(v: int) -> int {
        v + 3
    }
}

mod module_specs {
    #[trust_vc::spec]
    pub fn public_truth() -> bool {
        true
    }

    #[trust_vc::spec]
    fn private_truth() -> bool {
        true
    }
}

#[trust_vc::ensures(true)]
fn module_public_struct_field_projection_verified() {
    use self::module_adt::Car;

    let c = Car {
        four_doors: false,
        passengers: 4,
    };

    trust_vc::assert!(!c.four_doors);
    trust_vc::assert!(c.passengers == 4);
}

#[trust_vc::ensures(true)]
fn module_public_spec_fn_qualified_currently_blocked() {
    use self::module_adt::Car;

    let c = Car {
        four_doors: true,
        passengers: 4,
    };

    trust_vc::assert!(module_adt::is_four_doors(c));
}

#[trust_vc::ensures(true)]
fn module_opaque_spec_fn_imported_reveal_currently_blocked() {
    use self::module_adt::{opaque_is_four_doors, Car};

    let c = Car {
        four_doors: true,
        passengers: 4,
    };

    trust_vc::reveal!(opaque_is_four_doors);
    trust_vc::assert!(opaque_is_four_doors(c));
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_qualified_helper_contract_verified(x: int) {
    let y = module_helpers::inc_positive(x);
    trust_vc::assert!(y > x);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_public_qualified_helper_contract_verified(x: int) {
    let y = public_module_helpers::add_two(x);
    trust_vc::assert!(y == x + 2);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_private_qualified_helper_contract_verified(x: int) {
    let y = private_module_helpers::add_three(x);
    trust_vc::assert!(y == x + 3);
}

#[trust_vc::ensures(true)]
fn module_public_struct_scope_false_counterexample() {
    let c = ModuleCar {
        four_doors: false,
        passengers: 4,
    };
    let _ = c;

    trust_vc::assert!(false);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_use_alias_helper_contract_verified(x: int) {
    use self::module_helpers::inc_positive as inc;

    let y = inc(x);
    trust_vc::assert!(y > x);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_imported_group_helper_contract_verified(x: int) {
    use self::module_helpers::inc_positive;

    let y = inc_positive(x);
    trust_vc::assert!(y > x);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_crate_qualified_helper_contract_verified(x: int) {
    let y = crate::module_helpers::inc_positive(x);
    trust_vc::assert!(y > x);
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(true)]
fn module_nested_qualified_helper_contract_verified(x: int) {
    let y = public_nested_helpers::child::add_four(x);
    trust_vc::assert!(y == x + 4);
}

#[trust_vc::ensures(true)]
fn module_public_spec_fn_qualified_false_currently_blocked() {
    use self::module_adt::Car;

    let c = Car {
        four_doors: false,
        passengers: 4,
    };

    trust_vc::assert!(module_adt::is_four_doors(c));
}

#[trust_vc::ensures(true)]
fn module_imported_public_struct_false_counterexample() {
    use self::module_adt::Car;

    let c = Car {
        four_doors: false,
        passengers: 4,
    };

    trust_vc::assert!(!c.four_doors);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn module_opaque_spec_fn_without_reveal_currently_blocked() {
    use self::module_adt::{opaque_is_four_doors, Car};

    let c = Car {
        four_doors: true,
        passengers: 4,
    };

    trust_vc::assert!(opaque_is_four_doors(c));
}

#[trust_vc::ensures(module_helpers::always_true())]
fn module_qualified_helper_contract_in_ensures_fails_closed() {}

#[trust_vc::requires(module_helpers::always_true())]
#[trust_vc::ensures(true)]
fn module_qualified_helper_contract_in_requires_fails_closed() {}

#[trust_vc::ensures(true)]
fn module_public_spec_fn_alias_currently_blocked() {
    use self::module_adt::{is_four_doors, Car};

    let c = Car {
        four_doors: true,
        passengers: 4,
    };

    trust_vc::assert!(is_four_doors(c));
}

#[trust_vc::ensures(module_specs::public_truth())]
fn module_public_spec_fn_in_contract_currently_blocked() {}

#[trust_vc::ensures(true)]
fn module_private_spec_fn_qualified_currently_blocked() {
    trust_vc::assert!(module_specs::private_truth());
}

#[trust_vc::ensures(self::module_helpers::always_true())]
fn module_self_qualified_helper_contract_in_ensures_fails_closed() {}

#[trust_vc::ensures(true)]
fn module_qualified_opaque_reveal_fails_closed() {
    let c = module_adt::Car {
        four_doors: true,
        passengers: 4,
    };

    trust_vc::reveal!(module_adt::opaque_is_four_doors);
    trust_vc::assert!(module_adt::opaque_is_four_doors(c));
}

#[trust_vc::contract(open_without_pub(), ensures(true))]
fn module_open_without_pub_diagnostic_fails_closed() {}

#[trust_vc::contract(open_more_public_than_function(), ensures(true))]
fn module_open_more_public_than_function_diagnostic_fails_closed() {}

#[trust_vc::contract(open_proof_mode(), ensures(true))]
fn module_open_proof_mode_diagnostic_fails_closed() {}

#[trust_vc::contract(open_exec_mode(), ensures(true))]
fn module_open_exec_mode_diagnostic_fails_closed() {}

#[trust_vc::contract(closed_exec_mode(), ensures(true))]
fn module_closed_exec_mode_diagnostic_fails_closed() {}

#[trust_vc::contract(open_crate_visibility(), ensures(true))]
fn module_open_crate_visibility_diagnostic_fails_closed() {}

#[trust_vc::contract(open_super_visibility(), ensures(true))]
fn module_open_super_visibility_diagnostic_fails_closed() {}

#[trust_vc::contract(open_path_visibility(), ensures(true))]
fn module_open_path_visibility_diagnostic_fails_closed() {}

#[trust_vc::contract(main_proof_mode(), ensures(true))]
fn module_main_proof_mode_diagnostic_fails_closed() {}

#[trust_vc::contract(main_spec_mode(), ensures(true))]
fn module_main_spec_mode_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_exec_syntax(), ensures(true))]
fn module_uninterp_exec_syntax_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_spec_body(), ensures(true))]
fn module_uninterp_spec_body_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_spec_body_assoc(), ensures(true))]
fn module_uninterp_spec_body_assoc_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_spec_body_trait(), ensures(true))]
fn module_uninterp_spec_body_trait_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_spec_body_trait_impl(), ensures(true))]
fn module_uninterp_spec_body_trait_impl_diagnostic_fails_closed() {}

#[trust_vc::contract(uninterp_open_syntax(), ensures(true))]
fn module_uninterp_open_syntax_diagnostic_fails_closed() {}
