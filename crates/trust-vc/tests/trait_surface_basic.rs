// Compile-surface coverage for trait verification Slice 1 (#2432).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::trait_spec]
trait CounterSpec {
    #[requires(self.value() >= 0)]
    #[trust_vc::ensures(result >= 0)]
    fn value(&self) -> i32;

    #[trust_vc::returns(ret)]
    #[trust_vc::ensures(ret >= 0)]
    fn value_with_return_alias(&self) -> i32;

    fn incremented(&self, delta: i32) -> i32 {
        self.value() + delta
    }
}

struct Counter(i32);

#[trust_vc::trait_impl]
impl CounterSpec for Counter {
    #[trust_vc::ensures(result >= self.0)]
    fn value(&self) -> i32 {
        self.0
    }

    fn value_with_return_alias(&self) -> i32 {
        self.0
    }
}

#[test]
fn trait_spec_and_impl_surface_compile_and_run() {
    let counter = Counter(4);
    assert_eq!(counter.value(), 4);
    assert_eq!(counter.value_with_return_alias(), 4);
    assert_eq!(counter.incremented(3), 7);
}
