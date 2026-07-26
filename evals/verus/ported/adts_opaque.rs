// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/adts_opaque.rs`.
//
// The upstream file is primarily about Verus datatype opacity, module
// visibility, and opaque spec-function reveal rules. TrustVc does not currently
// model Verus-visible/private datatype boundaries, so this scout keeps the
// manifest entry unsupported-gap and records only Rust-valid behavior available
// today:
// - transparent ADT field projection;
// - a wrong transparent field projection counterexample;
// - an opaque source spec accessor over an ADT alias that verifies after reveal;
// - a revealed opaque accessor preserving constructor field facts;
// - opaque accessor precondition facts, including reveal-to-field reasoning;
// - concrete enum accessors after reveal;
// - nested concrete ADT accessor parameters as a fail-closed boundary;
// - wrong or unrevealed opaque accessor facts that must not verify; and
// - qualified/associated reveal target boundaries that fail closed.

pub type AdtsOpaqueRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type AdtsOpaqueRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ADTS_OPAQUE_RS_EXPECTED_CASES: &[AdtsOpaqueRsExpectedCase] = &[
    (
        "transparent_adt_field_projection_verified",
        "test_transparent_struct_1",
        "verified",
        1,
    ),
    (
        "opaque_adt_accessor_reveal_verified",
        "test_opaque_fn",
        "verified",
        1,
    ),
    (
        "opaque_adt_reveal_preserves_constructor_facts_verified",
        "test_opaque_struct_1",
        "verified",
        1,
    ),
    (
        "transparent_adt_wrong_field_projection_compute_counterexample",
        "test_transparent_struct_1",
        "counterexample",
        1,
    ),
    (
        "qualified_opaque_adt_reveal_fails_closed",
        "test_opaque_fn_modules_pass",
        "error",
        0,
    ),
    (
        "associated_opaque_method_reveal_fails_closed",
        "test_opaque_fn",
        "error",
        0,
    ),
];

pub const ADTS_OPAQUE_RS_FAIL_CLOSED_ERROR_PATTERNS: &[AdtsOpaqueRsFailClosedErrorPatterns] = &[
    (
        "qualified_opaque_adt_reveal_fails_closed",
        &[
            "supports only unqualified function names",
            "module_car_passengers",
        ],
    ),
    (
        "associated_opaque_method_reveal_fails_closed",
        &[
            "supports only unqualified function names",
            "OpaqueMethodWitness :: always",
        ],
    ),
];

pub fn adts_opaque_rs_expected_cases() -> &'static [AdtsOpaqueRsExpectedCase] {
    ADTS_OPAQUE_RS_EXPECTED_CASES
}

pub fn adts_opaque_rs_fail_closed_error_patterns(
) -> &'static [AdtsOpaqueRsFailClosedErrorPatterns] {
    ADTS_OPAQUE_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy)]
struct Car {
    passengers: u64,
    four_doors: bool,
}

type CarModel = Car;

#[derive(Clone, Copy)]
struct Bike {
    hard_tail: bool,
}

#[derive(Clone, Copy)]
struct Garage {
    primary: CarModel,
    backup: CarModel,
    capacity: u64,
}

#[derive(Clone, Copy)]
enum ParkingState {
    Open { spaces: u64 },
    Full,
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_car_passengers(car: CarModel) -> u64 {
    car.passengers
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_garage_primary_passengers(garage: Garage) -> u64 {
    garage.primary.passengers
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_available_spaces(state: ParkingState) -> u64 {
    match state {
        ParkingState::Open { spaces } => spaces,
        ParkingState::Full => 0u64,
    }
}

#[trust_vc::ensures(true)]
fn transparent_adt_field_projection_verified() {
    let bike = Bike { hard_tail: true };

    trust_vc::assert!(bike.hard_tail);
}

#[trust_vc::ensures(true)]
fn transparent_adt_wrong_field_projection_compute_counterexample() {
    trust_vc::assert_by_compute!(
        (Car {
            passengers: 12u64,
            four_doors: true,
        })
        .passengers
            == 13u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn opaque_adt_accessor_reveal_verified() {
    let car = Car {
        passengers: 12u64,
        four_doors: true,
    };

    trust_vc::reveal!(opaque_car_passengers);
    trust_vc::assert!(opaque_car_passengers(car) == 12u64);
    trust_vc::assert!(car.four_doors);
}

#[trust_vc::ensures(true)]
fn opaque_adt_reveal_preserves_constructor_facts_verified() {
    let car: CarModel = Car {
        passengers: 12u64,
        four_doors: true,
    };

    trust_vc::reveal!(opaque_car_passengers);
    trust_vc::assert!(opaque_car_passengers(car) == car.passengers);
    trust_vc::assert!(car.passengers == 12u64);
    trust_vc::assert!(car.four_doors);
}

#[trust_vc::requires(opaque_car_passengers(car) == 12u64)]
#[trust_vc::ensures(true)]
fn opaque_adt_precondition_fact_verified(car: CarModel) {
    trust_vc::assert!(opaque_car_passengers(car) == 12u64);
}

#[trust_vc::requires(opaque_car_passengers(car) == 12u64)]
#[trust_vc::ensures(true)]
fn opaque_adt_precondition_reveal_exposes_field_verified(car: CarModel) {
    trust_vc::reveal!(opaque_car_passengers);
    trust_vc::assert!(car.passengers == 12u64);
}

#[trust_vc::requires(opaque_car_passengers(car) == 12u64)]
#[trust_vc::ensures(true)]
fn opaque_adt_precondition_without_reveal_must_not_expose_field(car: CarModel) {
    trust_vc::assert!(car.passengers == 12u64);
}

#[trust_vc::ensures(true)]
fn opaque_nested_adt_accessor_reveal_verified() {
    let garage = Garage {
        primary: Car {
            passengers: 12u64,
            four_doors: true,
        },
        backup: Car {
            passengers: 2u64,
            four_doors: false,
        },
        capacity: 2u64,
    };

    trust_vc::reveal!(opaque_garage_primary_passengers);
    trust_vc::assert!(opaque_garage_primary_passengers(garage) == 12u64);
    trust_vc::assert!(garage.capacity == 2u64);
}

#[trust_vc::ensures(true)]
fn opaque_enum_record_accessor_reveal_verified() {
    let state = ParkingState::Open { spaces: 4u64 };

    trust_vc::reveal!(opaque_available_spaces);
    trust_vc::assert!(opaque_available_spaces(state) == 4u64);
}

#[trust_vc::ensures(true)]
fn opaque_enum_unit_accessor_reveal_verified() {
    let state = ParkingState::Full;

    trust_vc::reveal!(opaque_available_spaces);
    trust_vc::assert!(opaque_available_spaces(state) == 0u64);
}

#[trust_vc::ensures(true)]
fn opaque_adt_accessor_revealed_wrong_value_must_not_verify() {
    let car = Car {
        passengers: 12u64,
        four_doors: true,
    };

    trust_vc::reveal!(opaque_car_passengers);
    trust_vc::assert!(opaque_car_passengers(car) == 13u64);
}

#[trust_vc::ensures(true)]
fn opaque_adt_accessor_without_reveal_must_not_verify() {
    let car = Car {
        passengers: 12u64,
        four_doors: true,
    };

    trust_vc::assert!(opaque_car_passengers(car) == 12u64);
}

#[trust_vc::ensures(true)]
fn opaque_nested_adt_accessor_wrong_value_must_not_verify() {
    let garage = Garage {
        primary: Car {
            passengers: 12u64,
            four_doors: true,
        },
        backup: Car {
            passengers: 2u64,
            four_doors: false,
        },
        capacity: 2u64,
    };

    trust_vc::reveal!(opaque_garage_primary_passengers);
    trust_vc::assert!(opaque_garage_primary_passengers(garage) == 13u64);
}

#[trust_vc::ensures(true)]
fn opaque_enum_record_accessor_wrong_value_must_not_verify() {
    let state = ParkingState::Open { spaces: 4u64 };

    trust_vc::reveal!(opaque_available_spaces);
    trust_vc::assert!(opaque_available_spaces(state) == 5u64);
}

mod opaque_module {
    #[derive(Clone, Copy)]
    pub struct ModuleCar {
        pub passengers: u64,
        pub four_doors: bool,
    }

    pub type ModuleCarModel = ModuleCar;

    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn module_car_passengers(car: ModuleCarModel) -> u64 {
        car.passengers
    }
}

struct OpaqueMethodWitness {}

impl OpaqueMethodWitness {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    fn always(&self) -> bool {
        true
    }
}

#[trust_vc::ensures(true)]
fn associated_opaque_method_reveal_fails_closed() {
    let witness = OpaqueMethodWitness {};

    trust_vc::reveal!(OpaqueMethodWitness::always);
    trust_vc::assert!(witness.always());
}

#[trust_vc::ensures(true)]
fn qualified_opaque_adt_reveal_fails_closed() {
    let car = opaque_module::ModuleCar {
        passengers: 12u64,
        four_doors: true,
    };

    trust_vc::reveal!(opaque_module::module_car_passengers);
    trust_vc::assert!(opaque_module::module_car_passengers(car) == 12u64);
    trust_vc::assert!(car.four_doors);
}
