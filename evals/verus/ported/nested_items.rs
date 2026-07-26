// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod m {
    // Upstream Verus ignores this item inside the inline module.
    use super::*;

    #[trust_vc::spec]
    #[trust_vc::ensures(result)]
    pub fn test() -> bool {
        true
    }
}

#[trust_vc::ensures(true)]
fn test_use_item() {
    use m::test as test2;

    let result: bool = test2();
    trust_vc::assert!(result);
}

#[trust_vc::ensures(true)]
fn test_macro_item() {
    let mut x = 1;
    macro_rules! add_1 {
        () => {
            x = x + 1;
        };
    }
    add_1!();

    trust_vc::assert!(x == 2);
}
