// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub fn foo(g: state_machine_macro_usage::Global) {
    let _f = state_machine_macro_usage::Global { ..g };
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib() {
    let g = state_machine_macro_usage::Global::new(0);
    foo(g);
    trust_vc::assert!(true);
}

#[trust_vc::contract(ensures(result == 2u32), returns(result))]
pub fn direct_verified_dependency_call() -> u32 {
    state_machine_macro_usage::verified_counter_witness()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn upstream_foo_body_rebuilds_upstream_shaped_global() {
        let global = state_machine_macro_usage::Global::new(0);
        foo(global);
    }

    #[test]
    fn support_runtime_witness_loads_two() {
        assert_eq!(state_machine_macro_usage::runtime_counter_witness(), 2);
    }
}
