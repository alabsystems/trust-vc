// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

#[derive(Clone, Copy)]
struct LetElsePayload {
    x: u64,
    y: bool,
    z: i32,
}

#[derive(Clone, Copy)]
enum LetElseX {
    A(LetElsePayload, u64, bool),
    B(bool),
}

#[allow(non_snake_case)]
impl LetElseX {
    fn is_A(&self) -> bool {
        matches!(self, LetElseX::A(_, _, _))
    }

    fn get_A_0(&self) -> LetElsePayload {
        match *self {
            LetElseX::A(payload, _, _) => payload,
            LetElseX::B(_) => panic!("not LetElseX::A"),
        }
    }

    fn get_A_2(&self) -> bool {
        match *self {
            LetElseX::A(_, _, b) => b,
            LetElseX::B(_) => panic!("not LetElseX::A"),
        }
    }
}

#[allow(irrefutable_let_patterns)]
fn let_else_irrefutable_binding(x: u64) {
    let y = x else { loop {} };

    trust_vc::assert!(y == x);
}

#[allow(irrefutable_let_patterns)]
#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_irrefutable_binding_false_counterexample(x: u64) {
    let _y = x else { loop {} };

    trust_vc::assert!(false);
}

#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_option_some_path() {
    let maybe = Some(17u64);
    let Some(_) = maybe else { loop {} };

    trust_vc::assert!(true);
}

#[trust_vc::contract(ensures(result == x.is_A()), returns(result))]
fn let_else_custom_enum_early_return_postcondition(x: LetElseX) -> bool {
    let LetElseX::A(_, _, _) = x else {
        return false;
    };

    true
}

fn let_else_custom_enum_wrong_else_return_unchecked(x: LetElseX) -> bool {
    let LetElseX::A(_, _, _) = x else {
        return true;
    };

    true
}

#[trust_vc::ensures(true)]
fn let_else_custom_enum_wrong_else_return_counterexample() {
    let x = LetElseX::B(false);
    let LetElseX::A(_, _, _) = x else {
        trust_vc::assert!(false);
        return;
    };
}

#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_verus_parse_else_counterexample() {
    let Some(_) = None::<u64> else {
        trust_vc::assert!(false);
        return;
    };
}

#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_custom_enum_dotted_pattern_extracts_fields(value: LetElseX) {
    let LetElseX::A(LetElsePayload { x, .. }, .., b) = value else {
        loop {}
    };

    trust_vc::assert!(x == value.get_A_0().x);
    trust_vc::assert!(b == value.get_A_2());
}

#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_dotted_pattern_loop_else_verified(value: LetElseX) {
    let LetElseX::A(_, _, _) = value else { loop {} };

    trust_vc::assert!(value.is_A());
}

#[trust_vc::proof]
#[trust_vc::ensures(result == 0u64 || result == value.get_A_0().x)]
fn let_else_not_supported_in_proof_mode(value: LetElseX) -> u64 {
    let LetElseX::A(payload, _, _) = value else {
        return 0u64;
    };

    payload.x
}

#[trust_vc::spec]
#[trust_vc::ensures(result == 0u64 || result == value.get_A_0().x)]
fn let_else_not_supported_in_spec_mode(value: LetElseX) -> u64 {
    let LetElseX::A(payload, _, _) = value else {
        return 0u64;
    };

    payload.x
}

#[trust_vc::contract(ensures(true), returns(result))]
fn let_else_option_symbolic_refutable_path(maybe: Option<u64>) {
    let Some(_) = maybe else { loop {} };

    trust_vc::assert!(true);
}
