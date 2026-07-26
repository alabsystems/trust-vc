// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::{nat, Map, Set, SpecFn};

pub fn test1_fails_subtype() {
    let s1 = Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32);
    let m1: Map<i32, i32> = s1.mk_map(SpecFn::new(|k: i32| 10i32 * k));

    let _m4: Map<nat, i32> = m1;
}
