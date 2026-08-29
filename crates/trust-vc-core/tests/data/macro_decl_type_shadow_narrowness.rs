// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS: the refusal is scoped to an item macro that could bind a name
//! NEARER to the use site than the declaration the walk chose. A macro that is
//! not on the use site's outward walk path must cost nothing.

pub struct S {
    pub x: u8,
}

mod sibling {
    macro_rules! decl_t {
        () => {
            pub struct T {
                pub y: u8,
            }
        };
    }
    decl_t!();
}

mod user {
    use super::S;

    /// TRUE: `sibling` is not an ancestor of `user`, so its macro cannot bind
    /// anything on this use site's walk path.
    #[trust_vc::ensures(true)]
    pub fn sibling_macro_still_verifies(s: S) -> u64 {
        trust_vc::assert!(s.x <= 255u8);
        0u64
    }
}

/// TRUE: a root use site is enclosed by no module at all, so a macro inside one
/// is never on its path.
#[trust_vc::ensures(true)]
fn root_use_site_with_module_macro(s: S) -> u64 {
    trust_vc::assert!(s.x <= 255u8);
    0u64
}
