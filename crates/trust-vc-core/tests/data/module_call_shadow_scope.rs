// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-A reproducer: a call written inside `mod app` spells `util::f`, which
//! Rust resolves to `app::util::f`. The source-function registry is keyed by the
//! DECLARATION's module path but was looked up with the spelling read as
//! file-root-relative, so it answered with the top-level `util::f` instead — a
//! different body, a different `requires` and a different `ensures`.
//!
//! Ground truth (rustc): `app::call(50) == 40`, against `ensures(result == x)`.
//! The dropped `requires(x >= 10)` also hides a `u32` underflow at `call(1)`.
//! `call` must NOT verify.

mod util {
    #[trust_vc::proof]
    #[trust_vc::requires(x > 0)]
    #[trust_vc::ensures(result == x)]
    pub fn f(x: u32) -> u32 {
        x
    }
}

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
