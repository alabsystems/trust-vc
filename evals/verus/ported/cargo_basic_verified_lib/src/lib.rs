// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

use trust_vc_types::{SpecFn, View};

#[trust_vc::contract(ensures(result == (x as u32) + (x as u32)), returns(result))]
pub fn lib(x: u16) -> u32 {
    x as u32 + x as u32
}

pub use lib as double;

trait Trait: View {}

impl<T: View> Trait for Option<T> {}

fn test(_f: SpecFn<u64, u64>) {}

mod is_not_regression_issue_1573 {
    #[derive(Clone, Copy)]
    enum Test {
        A,
        B,
    }

    fn is_not_a(t: Test) -> bool {
        !matches!(t, Test::A)
    }

    fn is_a(t: Test) -> bool {
        matches!(t, Test::A)
    }
}
