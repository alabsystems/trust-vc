// SpecFn basic compile tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::{int, nat, SpecFn};

fn make_doubler() -> SpecFn<i32, i32> {
    SpecFn::new(|i: i32| i * 2)
}

fn make_adder(k: i32) -> SpecFn<i32, i32> {
    SpecFn::new(move |i: i32| i + k)
}

fn make_math_successor() -> SpecFn<int, int> {
    SpecFn::new(|i: int| i + 1)
}

fn make_nat_successor() -> SpecFn<nat, nat> {
    SpecFn::new(|i: nat| i + 1)
}

#[test]
fn spec_fn_construction_compiles() {
    let _ = make_doubler();
    let _ = make_adder(5);
    let _ = make_math_successor();
    let _ = make_nat_successor();
}
