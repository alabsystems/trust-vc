// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

use trust_vc_types::{Ghost, Tracked};
use std::sync::atomic::{AtomicU32, Ordering};

#[allow(non_snake_case)]
pub mod X {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Instance {
        id: u64,
    }

    impl Instance {
        pub fn new(id: u64) -> Self {
            Self { id }
        }

        pub fn id(&self) -> u64 {
            self.id
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct counter {
        instance_id: u64,
        value: u32,
    }

    impl counter {
        pub fn new(instance_id: u64, value: u32) -> Self {
            Self { instance_id, value }
        }

        pub fn instance_id(&self) -> u64 {
            self.instance_id
        }

        pub fn value(&self) -> u32 {
            self.value
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct inc_a {
        value: bool,
    }

    impl inc_a {
        pub fn new(value: bool) -> Self {
            Self { value }
        }

        pub fn value(&self) -> bool {
            self.value
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct inc_b {
        value: bool,
    }

    impl inc_b {
        pub fn new(value: bool) -> Self {
            Self { value }
        }

        pub fn value(&self) -> bool {
            self.value
        }
    }
}

#[derive(Debug)]
pub struct AtomicCounter {
    value: AtomicU32,
    instance_id: u64,
    counter_token: Ghost<X::counter>,
}

impl AtomicCounter {
    pub fn new(value: u32, token: X::counter) -> Self {
        Self {
            value: AtomicU32::new(value),
            instance_id: token.instance_id(),
            counter_token: Ghost::new(token),
        }
    }

    pub fn load(&self) -> u32 {
        self.value.load(Ordering::SeqCst)
    }

    pub fn fetch_add_one(&self) -> u32 {
        self.value.fetch_add(1, Ordering::SeqCst)
    }

    pub fn instance_id(&self) -> u64 {
        self.instance_id
    }
}

#[derive(Debug)]
pub struct Global {
    pub atomic: AtomicCounter,
    pub instance: Tracked<X::Instance>,
}

impl Global {
    pub fn new(counter: u32) -> Self {
        let instance = X::Instance::new(0);
        let counter_token = X::counter::new(instance.id(), counter);
        Self {
            atomic: AtomicCounter::new(counter, counter_token),
            instance: Tracked::new(instance),
        }
    }

    pub fn load(&self) -> u32 {
        self.atomic.load()
    }

    pub fn instance_id(&self) -> u64 {
        self.atomic.instance_id()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CounterProtocol {
    pub counter: u32,
    pub inc_a: bool,
    pub inc_b: bool,
}

impl CounterProtocol {
    pub fn initialize() -> Self {
        Self {
            counter: 0,
            inc_a: false,
            inc_b: false,
        }
    }

    pub fn main_inv(&self) -> bool {
        self.counter == Self::token_count(self.inc_a, self.inc_b)
    }

    pub fn tr_inc_a(&mut self) {
        assert!(!self.inc_a);
        assert!(self.main_inv());
        self.counter += 1;
        self.inc_a = true;
        assert!(self.main_inv());
    }

    pub fn tr_inc_b(&mut self) {
        assert!(!self.inc_b);
        assert!(self.main_inv());
        self.counter += 1;
        self.inc_b = true;
        assert!(self.main_inv());
    }

    pub fn finalize(&self) -> u32 {
        assert!(self.main_inv());
        assert!(self.inc_a);
        assert!(self.inc_b);
        assert_eq!(self.counter, 2);
        self.counter
    }

    fn token_count(inc_a: bool, inc_b: bool) -> u32 {
        let a = if inc_a { 1 } else { 0 };
        let b = if inc_b { 1 } else { 0 };
        a + b
    }
}

#[trust_vc::contract(ensures(result == 2u32), returns(result))]
pub fn verified_counter_witness() -> u32 {
    let counter0 = 0u32;
    let inc_a = false;
    let inc_b = false;

    trust_vc::assert!(counter0 == 0u32);
    trust_vc::assert!(!inc_a);
    trust_vc::assert!(!inc_b);
    trust_vc::assert!(counter0 == 0u32 + 0u32);

    let counter1 = counter0 + 1u32;
    let inc_a = true;
    trust_vc::assert!(counter1 == 1u32);
    trust_vc::assert!(inc_a);
    trust_vc::assert!(counter1 == 1u32 + 0u32);

    let counter2 = counter1 + 1u32;
    let inc_b = true;
    trust_vc::assert!(counter2 == 2u32);
    trust_vc::assert!(inc_a);
    trust_vc::assert!(inc_b);
    trust_vc::assert!(counter2 == 1u32 + 1u32);
    counter2
}

pub fn runtime_counter_witness() -> u32 {
    let global = Global::new(0);
    assert_eq!(global.load(), 0);
    let _previous = global.atomic.fetch_add_one();
    let _previous = global.atomic.fetch_add_one();

    let mut protocol = CounterProtocol::initialize();
    assert!(protocol.main_inv());
    protocol.tr_inc_a();
    protocol.tr_inc_b();

    let loaded = global.load();
    assert_eq!(loaded, protocol.finalize());
    loaded
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn global_rebuild_moves_atomic_and_tracked_instance() {
        let global = Global::new(0);
        assert_eq!(global.load(), 0);
        assert_eq!(global.instance_id(), 0);

        let rebuilt = Global { ..global };
        assert_eq!(rebuilt.load(), 0);
        assert_eq!(rebuilt.instance_id(), 0);
    }

    #[test]
    fn counter_protocol_finalizes_at_two() {
        let mut protocol = CounterProtocol::initialize();
        assert!(protocol.main_inv());
        protocol.tr_inc_a();
        protocol.tr_inc_b();
        assert_eq!(protocol.finalize(), 2);
    }

    #[test]
    fn runtime_counter_witness_loads_two() {
        assert_eq!(runtime_counter_witness(), 2);
    }
}
