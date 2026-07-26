// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::int;

pub const ADTS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "struct_literal_field_projection_preserves_named_field_order",
        "test_struct_1/test_struct_4",
        "verified",
        2,
    ),
    (
        "struct_parameter_projection_preserves_required_field",
        "test_struct_2",
        "verified",
        1,
    ),
    (
        "local_struct_binding_preserves_projected_fields",
        "test_struct_3/test_struct_4",
        "verified",
        2,
    ),
    (
        "compact_car_u8_field_is_nonnegative",
        "test_struct_u8",
        "verified",
        1,
    ),
    (
        "struct_update_copies_omitted_fields",
        "test_update1",
        "verified",
        2,
    ),
    (
        "struct_update_with_contract_call_preserves_ensured_field",
        "test_update2",
        "verified",
        2,
    ),
    (
        "type_alias_parameter_projection_preserves_field",
        "type_alias_basic",
        "verified",
        1,
    ),
    (
        "tuple_struct_projection_preserves_positional_field",
        "test_regression_tuple_1",
        "verified",
        1,
    ),
    (
        "enum_unit_variant_helper_on_constructed_left",
        "resolve_ctors_for_unit_syntax enum unit constructor prefix",
        "verified",
        1,
    ),
    (
        "enum_variant_helper_methods_on_constructed_tuple_variant",
        "simple enum is_Variant/get_Variant_field helper parity",
        "verified",
        1,
    ),
    (
        "enum_record_variant_match_extracts_named_field",
        "test_enum_adt_mod",
        "verified",
        1,
    ),
    (
        "enum_tuple_variant_match_extracts_payload",
        "test_enum_adt_mod tuple-variant match payload extraction",
        "verified",
        1,
    ),
    (
        "enum_named_field_helper_on_constructed_record_variant",
        "test_is_variant_get_named_field",
        "verified",
        1,
    ),
    (
        "generic_single_variant_helper_on_arbitrary_value",
        "generic single-variant helper",
        "verified",
        1,
    ),
];

pub fn adts_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    ADTS_RS_EXPECTED_CASES
}

struct Car {
    four_doors: bool,
    passengers: int,
}

struct CompactCar {
    four_doors: bool,
    passengers: u8,
}

struct S2 {
    u: u64,
    v: u64,
}

struct AliasAnimal {
    num_legs: u8,
}

type AliasAni = AliasAnimal;

struct TupleBool(bool);

enum TrafficLight {
    Red,
    Yellow(u64),
    Green(u64),
}

enum EnumRecord {
    A { a: u64 },
    B(u64),
}

enum ResBool {
    Ok { t: bool },
    Err { v: u64 },
}

enum Direction {
    Left,
    Right,
}

enum GenericAdt<T> {
    Wrapped(T),
}

enum RecursiveAdt {
    Nil,
    Cons(u64, Box<RecursiveAdt>),
}

#[trust_vc::ensures(true)]
fn struct_literal_field_projection_preserves_named_field_order(passengers: int) {
    trust_vc::assert!(
        (Car {
            four_doors: true,
            passengers
        })
        .passengers
            == passengers
    );
    trust_vc::assert!(
        (Car {
            passengers,
            four_doors: true
        })
        .passengers
            == passengers
    );
}

#[trust_vc::requires(car.passengers == passengers)]
#[trust_vc::ensures(true)]
fn struct_parameter_projection_preserves_required_field(car: Car, passengers: int) {
    trust_vc::assert!(car.passengers == passengers);
}

#[trust_vc::ensures(true)]
fn local_struct_binding_preserves_projected_fields(passengers: int) {
    let c = Car {
        passengers,
        four_doors: true,
    };

    trust_vc::assert!(c.passengers == passengers);
    trust_vc::assert!(c.four_doors);
}

#[trust_vc::ensures(true)]
fn struct_literal_field_projection_wrong_value_fails_closed() {
    trust_vc::assert!((S2 { u: 10u64, v: 20u64 }).u == 11u64);
}

#[trust_vc::ensures(true)]
fn compact_car_u8_field_is_nonnegative(car: CompactCar) {
    trust_vc::assert!(car.passengers >= 0u8);
}

#[trust_vc::ensures(true)]
fn struct_update_copies_omitted_fields() {
    let s2 = S2 { u: 10u64, v: 20u64 };
    let s3 = S2 { v: 23u64, ..s2 };
    trust_vc::assert!(s3.u == 10u64);
    trust_vc::assert!(s3.v == 23u64);
}

#[trust_vc::ensures(result.u == 100u64)]
fn struct_update_contract_source() -> S2 {
    S2 {
        u: 100u64,
        v: 200u64,
    }
}

#[trust_vc::ensures(true)]
fn struct_update_with_contract_call_preserves_ensured_field() {
    let s3 = S2 {
        v: 1u64 + 22u64,
        ..struct_update_contract_source()
    };

    trust_vc::assert!(s3.u == 100u64);
    trust_vc::assert!(s3.v == 23u64);
}

#[trust_vc::requires(animal.num_legs == 5u8)]
#[trust_vc::ensures(true)]
fn type_alias_parameter_projection_preserves_field(animal: AliasAni) {
    let legs = animal.num_legs;

    trust_vc::assert!(legs == 5u8);
}

#[trust_vc::ensures(true)]
fn tuple_struct_projection_preserves_positional_field(b: TupleBool) {
    let z = b.0;

    trust_vc::assert!(z == b.0);
}

#[trust_vc::ensures(result.is_Left())]
#[trust_vc::ensures(!result.is_Right())]
fn enum_unit_variant_helper_on_constructed_left() -> Direction {
    Direction::Left
}

#[trust_vc::ensures(result.is_Green())]
#[trust_vc::ensures(!result.is_Red())]
#[trust_vc::ensures(result.get_Green_0() == 7u64)]
fn enum_variant_helper_methods_on_constructed_tuple_variant() -> TrafficLight {
    TrafficLight::Green(7u64)
}

#[trust_vc::ensures(result.get_Green_0() == 8u64)]
fn enum_variant_helper_wrong_payload_fails_closed() -> TrafficLight {
    TrafficLight::Green(7u64)
}

#[trust_vc::ensures(result)]
fn enum_record_variant_match_extracts_named_field() -> bool {
    match (EnumRecord::A { a: 12u64 }) {
        EnumRecord::A { a } => a == 12u64,
        _ => false,
    }
}

#[trust_vc::ensures(result)]
fn enum_tuple_variant_match_extracts_payload() -> bool {
    match (TrafficLight::Yellow(9u64)) {
        TrafficLight::Yellow(value) => value == 9u64,
        _ => false,
    }
}

#[trust_vc::ensures(result.is_Err())]
#[trust_vc::ensures(!result.is_Ok())]
#[trust_vc::ensures(result.get_Err_v() == 42u64)]
fn enum_named_field_helper_on_constructed_record_variant() -> ResBool {
    ResBool::Err { v: 42u64 }
}

#[trust_vc::ensures(result)]
fn enum_tuple_variant_match_wrong_payload_fails_closed() -> bool {
    match (TrafficLight::Yellow(9u64)) {
        TrafficLight::Yellow(value) => value == 10u64,
        _ => false,
    }
}

#[trust_vc::ensures(true)]
fn generic_single_variant_helper_on_arbitrary_value(value: GenericAdt<u64>) {
    trust_vc::assert!(value.is_Wrapped());
}

#[trust_vc::ensures(true)]
fn recursive_enum_helpers_fail_closed(value: RecursiveAdt) {
    trust_vc::assert!(value.is_Nil());
}
