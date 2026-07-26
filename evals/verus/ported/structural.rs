// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/structural.rs`.
//
// The upstream file exercises Verus's `Structural` derive and its connection
// between Rust `PartialEq` and SMT equality. TrustVc does not currently expose
// the Verus `Structural` derive or the associated non-structural diagnostics as
// one-to-one executable evidence.
//
// This first slice keeps the upstream manifest entry unsupported-gap and pins
// only Rust-valid scout coverage:
// - A struct with the same fields as upstream `Car` preserves field equality.
// - Direct derived `PartialEq` over the whole struct verifies for equal values.
// - A false direct `PartialEq` assertion must not verify.
// - Wildcard enum payload patterns and fieldless enum values now have narrow
//   executable witnesses.
// - Custom PartialEq-style surfaces remain fail-closed boundaries instead of
//   accepted replacement evidence.

#![allow(dead_code)]

pub const STRUCTURAL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "structural_car_field_equality_verified",
        "test_structural_eq",
        "verified",
        1,
    ),
    (
        "structural_car_direct_derived_partial_eq_verified",
        "test_structural_eq",
        "verified",
        1,
    ),
    (
        "structural_vehicle_direct_derived_partial_eq_verified",
        "test_structural_eq",
        "verified",
        1,
    ),
    (
        "structural_car_direct_derived_partial_eq_wrong_value",
        "test_structural_eq",
        "counterexample",
        1,
    ),
    (
        "structural_vehicle_direct_derived_partial_eq_wrong_variant",
        "test_structural_eq",
        "counterexample",
        1,
    ),
    (
        "structural_enum_value_status_derived_eq_verified",
        "test_structural_enum_with_values",
        "verified",
        1,
    ),
    (
        "structural_enum_value_status_wrong_value",
        "test_structural_enum_with_values",
        "counterexample",
        1,
    ),
    (
        "structural_manual_partial_eq_method_currently_blocked",
        "test_not_structural_generic",
        "error",
        0,
    ),
];

pub const STRUCTURAL_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "structural_manual_partial_eq_method_currently_blocked",
    &["unsupported method", "eq()"],
)];

pub fn structural_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    STRUCTURAL_RS_EXPECTED_CASES
}

pub fn structural_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    STRUCTURAL_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct StructuralCar {
    four_doors: bool,
    passengers: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StructuralVehicle {
    Car(StructuralCar),
    Train(bool),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StructuralValueStatus {
    Valid = 0,
    Invalid = 1,
}

#[derive(Clone, Copy, Eq)]
struct ManualEq;

impl PartialEq for ManualEq {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

#[trust_vc::ensures(true)]
fn structural_car_field_equality_verified(passengers: u64) {
    let c1 = StructuralCar {
        passengers,
        four_doors: true,
    };
    let c2 = StructuralCar {
        passengers,
        four_doors: false,
    };
    let c3 = StructuralCar {
        passengers,
        four_doors: true,
    };

    trust_vc::assert!(c1.passengers == c3.passengers);
    trust_vc::assert!(c1.four_doors == c3.four_doors);
    trust_vc::assert!(c1.four_doors != c2.four_doors);
}

#[trust_vc::ensures(true)]
fn structural_car_direct_derived_partial_eq_verified(passengers: u64) {
    let c1 = StructuralCar {
        passengers,
        four_doors: true,
    };
    let c2 = StructuralCar {
        passengers,
        four_doors: false,
    };
    let c3 = StructuralCar {
        passengers,
        four_doors: true,
    };

    trust_vc::assert!(c1 == c3);
    trust_vc::assert!(c1 != c2);
}

#[trust_vc::ensures(true)]
fn structural_car_direct_derived_partial_eq_wrong_value(passengers: u64) {
    let c1 = StructuralCar {
        passengers,
        four_doors: true,
    };
    let c2 = StructuralCar {
        passengers,
        four_doors: false,
    };

    trust_vc::assert!(c1 == c2);
}

#[trust_vc::ensures(true)]
fn structural_vehicle_direct_derived_partial_eq_verified(passengers: u64) {
    let c1 = StructuralCar {
        passengers,
        four_doors: true,
    };
    let t = StructuralVehicle::Train(true);
    let ca = StructuralVehicle::Car(c1);

    trust_vc::assert!(t != ca);
}

#[trust_vc::ensures(true)]
fn structural_vehicle_direct_derived_partial_eq_wrong_variant(passengers: u64) {
    let c1 = StructuralCar {
        passengers,
        four_doors: true,
    };
    let t = StructuralVehicle::Train(true);
    let ca = StructuralVehicle::Car(c1);

    trust_vc::assert!(t == ca);
}

#[trust_vc::ensures(true)]
fn structural_enum_value_status_derived_eq_verified() {
    let valid = StructuralValueStatus::Valid;
    let same_valid = StructuralValueStatus::Valid;
    let invalid = StructuralValueStatus::Invalid;

    trust_vc::assert!(valid == same_valid);
    trust_vc::assert!(valid != invalid);
}

#[trust_vc::ensures(true)]
fn structural_enum_value_status_wrong_value() {
    trust_vc::assert!(StructuralValueStatus::Valid == StructuralValueStatus::Invalid);
}

#[trust_vc::ensures(result)]
fn structural_vehicle_wildcard_payload_match_verified(passengers: u64) -> bool {
    match StructuralVehicle::Car(StructuralCar {
        passengers,
        four_doors: true,
    }) {
        StructuralVehicle::Car(car) => car.passengers == passengers && car.four_doors,
        StructuralVehicle::Train(_) => false,
    }
}

#[trust_vc::ensures(true)]
fn structural_manual_partial_eq_method_currently_blocked(left: ManualEq, right: ManualEq) {
    trust_vc::assert!(left.eq(&right));
}
