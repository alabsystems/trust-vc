// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PINS for the call-path scope walk: the ordinary, NON-colliding
//! call shapes that must keep verifying after FV-A is closed.
//!
//! * `cross_module_bare` — `mod a` calling `b::g` where `g` is unique.
//! * `cross_module_crate` — the same edge spelled `crate::b::g`.
//! * `same_module` — a call to a sibling declared in the caller's own module.
//! * `via_super` / `via_self` — the two explicit qualifiers the walk understands.
//!
//! Every one of these carries a contract that is provable ONLY from the intended
//! callee's `ensures`, so a decline shows up as a failure, not as a pass.

mod b {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x + 1)]
    pub fn g(x: u32) -> u32 {
        x + 1
    }
}

mod a {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0 && x < 100)]
    #[trust_vc::ensures(result == x + 1)]
    pub fn cross_module_bare(x: u32) -> u32 {
        b::g(x)
    }

    #[trust_vc::proof]
    #[trust_vc::requires(x > 0 && x < 100)]
    #[trust_vc::ensures(result == x + 1)]
    pub fn cross_module_crate(x: u32) -> u32 {
        crate::b::g(x)
    }
}

mod m {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x + 3)]
    pub fn h(x: u32) -> u32 {
        x + 3
    }

    #[trust_vc::proof]
    #[trust_vc::requires(x > 0 && x < 100)]
    #[trust_vc::ensures(result == x + 3)]
    pub fn same_module(x: u32) -> u32 {
        h(x)
    }
}

mod outer {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x + 4)]
    pub fn bump(x: u32) -> u32 {
        x + 4
    }

    pub mod nested {
        #[trust_vc::proof]
        #[trust_vc::requires(x > 0 && x < 100)]
        #[trust_vc::ensures(result == x + 4)]
        pub fn via_super(x: u32) -> u32 {
            super::bump(x)
        }
    }
}

mod selfmod {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x + 2)]
    pub fn step(x: u32) -> u32 {
        x + 2
    }

    #[trust_vc::proof]
    #[trust_vc::requires(x > 0 && x < 100)]
    #[trust_vc::ensures(result == x + 2)]
    pub fn via_self(x: u32) -> u32 {
        self::step(x)
    }
}
