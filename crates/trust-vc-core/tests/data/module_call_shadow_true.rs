// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PIN for `module_call_shadow_scope.rs`: the SAME shadowing shape,
//! with `call`'s contract stating what the function Rust actually calls
//! (`app::util::f`) really does. This must VERIFY.
//!
//! Without it the FV-A fix could degenerate into "decline every colliding call
//! path", which closes the hole and answers nothing. Verifying here proves the
//! call resolved to the INNER declaration — the top-level `f` is the identity,
//! under which `result == x - 10` is refutable.

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
    #[trust_vc::requires(x >= 10 && x < 100)]
    #[trust_vc::ensures(result == x - 10)]
    pub fn call(x: u32) -> u32 {
        util::f(x)
    }
}
