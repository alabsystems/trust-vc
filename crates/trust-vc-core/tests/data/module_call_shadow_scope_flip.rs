// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ORDER-FLIP CONTROL for `module_call_shadow_scope.rs`: byte-for-byte the same
//! two declarations, with `mod app` written FIRST. Scope decides which `f` the
//! call names, so the verdict must be identical to the unflipped file. A
//! resolver that is wrong in the other direction (declaration order, or
//! last-wins) shows up here and nowhere else.

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
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x)]
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
