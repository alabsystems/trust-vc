// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ORDER-FLIP CONTROL for `module_call_shadow_true.rs`. Same two declarations,
//! `mod app` first. Must still VERIFY: the narrowness pin has to survive both
//! orders, or the resolver is reading declaration position rather than scope.

mod app {
    pub mod util {
        #[trust_vc::proof]
        #[trust_vc::requires(x >= 10)]
        #[trust_vc::ensures(result == x - 10)]
        pub fn f(x: u32) -> u32 {
            x - 10
        }
    }

    #[trust_vc::proof]
    #[trust_vc::requires(x >= 10 && x < 100)]
    #[trust_vc::ensures(result == x - 10)]
    pub fn call(x: u32) -> u32 {
        util::f(x)
    }
}

mod util {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x)]
    pub fn f(x: u32) -> u32 {
        x
    }
}
