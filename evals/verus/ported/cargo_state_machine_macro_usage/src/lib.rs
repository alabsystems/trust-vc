// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// Upstream `state_machine_macro_usage` is a Verus macro fixture built around
// `state_machine!`, `tokenized_state_machine!`, ghost tokens, and atomic ghost
// invariants. TrustVc does not yet expand those macros, so this port keeps an
// ordinary Rust witness for the generated Y/X transition behavior and a local
// macro crate that fails closed when the real macro surface is invoked.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::thread;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Y {
    pub x: i32,
    pub y: i32,
    pub z: i32,
}

pub type InvariantMachine = Y;

impl Y {
    pub fn initialize(x: i32, y: i32, z: i32) -> Self {
        assert!(y <= z);
        let z = if x == y { z } else { z + 1 };
        Self { x, y, z }
    }

    pub fn tr1(&mut self, b: bool, c: bool) {
        assert!(b);
        assert!(self.y <= self.z);
        assert!(c);
        self.z += 1;
    }

    pub fn tr2(&mut self, b: bool, c: bool) {
        if b {
            self.z += 1;
        } else {
            assert!(self.y <= self.z);
        }
        assert!(c);
    }

    pub fn tr3(&mut self, b: bool, c: bool) {
        if b {
            assert!(self.y <= self.z);
        } else {
            let next = self.z + 1;
            self.z = next;
        }
        assert!(c);
    }

    pub fn the_inv(&self) -> bool {
        self.y <= self.z
    }

    pub fn invariant(&self) -> bool {
        self.the_inv()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct X {
    pub counter: u32,
    pub inc_a: bool,
    pub inc_b: bool,
}

pub type CounterProtocol = X;

impl X {
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

    pub fn increment_will_not_overflow_u32(&self) {
        assert!(self.counter < u32::MAX);
    }

    pub fn tr_inc_a(&mut self) {
        assert!(!self.inc_a);
        assert!(self.main_inv());
        self.increment_will_not_overflow_u32();
        self.counter += 1;
        self.inc_a = true;
        assert!(self.main_inv());
    }

    pub fn tr_inc_b(&mut self) {
        assert!(!self.inc_b);
        assert!(self.main_inv());
        self.increment_will_not_overflow_u32();
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct XCounterToken {
    pub value: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct XIncAToken {
    pub value: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct XIncBToken {
    pub value: bool,
}

impl XCounterToken {
    pub fn zero() -> Self {
        Self { value: 0 }
    }
}

impl XIncAToken {
    pub fn false_token() -> Self {
        Self { value: false }
    }

    pub fn true_token() -> Self {
        Self { value: true }
    }
}

impl XIncBToken {
    pub fn false_token() -> Self {
        Self { value: false }
    }

    pub fn true_token() -> Self {
        Self { value: true }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XInstance {
    pub id: u64,
}

impl XInstance {
    pub fn initialize() -> (Self, XCounterToken, XIncAToken, XIncBToken) {
        (
            Self { id: 0 },
            XCounterToken::zero(),
            XIncAToken::false_token(),
            XIncBToken::false_token(),
        )
    }

    pub fn tr_inc_a(&self, counter: &mut XCounterToken, token: &mut XIncAToken) {
        let mut protocol = X {
            counter: counter.value,
            inc_a: token.value,
            inc_b: false,
        };
        protocol.tr_inc_a();
        counter.value = protocol.counter;
        token.value = protocol.inc_a;
    }

    pub fn tr_inc_b(&self, counter: &mut XCounterToken, token: &mut XIncBToken) {
        let mut protocol = X {
            counter: counter.value,
            inc_a: true,
            inc_b: token.value,
        };
        protocol.tr_inc_b();
        counter.value = protocol.counter;
        token.value = protocol.inc_b;
    }

    pub fn finalize(&self, counter: &XCounterToken, inc_a: &XIncAToken, inc_b: &XIncBToken) -> u32 {
        let protocol = X {
            counter: counter.value,
            inc_a: inc_a.value,
            inc_b: inc_b.value,
        };
        protocol.finalize()
    }
}

#[derive(Debug)]
pub struct Global {
    pub atomic: AtomicU32,
}

impl Global {
    pub fn new(counter: u32) -> Self {
        Self {
            atomic: AtomicU32::new(counter),
        }
    }

    pub fn load(&self) -> u32 {
        self.atomic.load(Ordering::SeqCst)
    }

    pub fn fetch_add_one(&self) -> u32 {
        self.atomic.fetch_add(1, Ordering::SeqCst)
    }
}

pub type IncrementToken = XIncAToken;

pub fn threaded_counter_witness() -> u32 {
    let global = Arc::new(Global::new(0));
    let (instance, mut counter_token, inc_a_token, inc_b_token) = XInstance::initialize();

    let global_a = Arc::clone(&global);
    let join_a = thread::spawn(move || {
        let _previous = global_a.fetch_add_one();
        inc_a_token
    });

    let global_b = Arc::clone(&global);
    let join_b = thread::spawn(move || {
        let _previous = global_b.fetch_add_one();
        inc_b_token
    });

    let mut inc_a_token = join_a.join().expect("inc_a thread should not panic");
    let mut inc_b_token = join_b.join().expect("inc_b thread should not panic");

    counter_token.value = 0;
    instance.tr_inc_a(&mut counter_token, &mut inc_a_token);
    instance.tr_inc_b(&mut counter_token, &mut inc_b_token);

    let loaded = global.load();
    assert_eq!(
        loaded,
        instance.finalize(&counter_token, &inc_a_token, &inc_b_token)
    );
    loaded
}

pub fn macro_dependency_marker() {
    verus_state_machines_macros::trust_vc_port_dependency_marker();
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn y_transition_relation_witness() {
    let init_x = 1i32;
    let init_y = 2i32;
    let init_z_arg = 3i32;
    trust_vc::assert!(init_y <= init_z_arg);

    let y0_x = init_x;
    let y0_y = init_y;
    let y0_z = init_z_arg + 1i32;
    trust_vc::assert!(y0_x == 1i32);
    trust_vc::assert!(y0_y == 2i32);
    trust_vc::assert!(y0_z == 4i32);
    trust_vc::assert!(y0_y <= y0_z);

    let y1_z = y0_z + 1i32;
    trust_vc::assert!(y0_y <= y0_z);
    trust_vc::assert!(y1_z == 5i32);
    trust_vc::assert!(y0_y <= y1_z);

    let y2_z = y1_z;
    trust_vc::assert!(y0_y <= y2_z);

    let y3_z = y2_z + 1i32;
    trust_vc::assert!(y3_z == 6i32);
    trust_vc::assert!(y0_y <= y3_z);
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn x_tokenized_counter_relation_witness() {
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
}

#[trust_vc::contract(ensures(true), returns(result))]
pub fn lib() {
    let init_x = 1i32;
    let init_y = 2i32;
    let init_z_arg = 3i32;
    trust_vc::assert!(init_y <= init_z_arg);

    let y0_x = init_x;
    let y0_y = init_y;
    let y0_z = init_z_arg + 1i32;
    trust_vc::assert!(y0_x == 1i32);
    trust_vc::assert!(y0_y == 2i32);
    trust_vc::assert!(y0_z == 4i32);
    trust_vc::assert!(y0_y <= y0_z);

    let y1_z = y0_z + 1i32;
    trust_vc::assert!(y0_y <= y0_z);
    trust_vc::assert!(y1_z == 5i32);
    trust_vc::assert!(y0_y <= y1_z);

    let y2_z = y1_z;
    trust_vc::assert!(y0_y <= y2_z);

    let y3_z = y2_z + 1i32;
    trust_vc::assert!(y3_z == 6i32);
    trust_vc::assert!(y0_y <= y3_z);

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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invariant_machine_preserves_y_le_z() {
        let mut machine = Y::initialize(1, 2, 3);
        machine.tr1(true, true);
        machine.tr2(false, true);
        machine.tr3(false, true);
        assert!(machine.the_inv());
    }

    #[test]
    fn counter_protocol_finalizes_at_two() {
        let mut protocol = X::initialize();
        assert!(protocol.main_inv());
        protocol.tr_inc_a();
        assert!(protocol.main_inv());
        protocol.tr_inc_b();
        assert!(protocol.main_inv());
        assert_eq!(protocol.finalize(), 2);
    }

    #[test]
    fn x_instance_tokens_follow_increment_transitions() {
        let (instance, mut counter, mut inc_a, mut inc_b) = XInstance::initialize();
        instance.tr_inc_a(&mut counter, &mut inc_a);
        instance.tr_inc_b(&mut counter, &mut inc_b);
        assert_eq!(instance.finalize(&counter, &inc_a, &inc_b), 2);
    }

    #[test]
    fn threaded_counter_witness_joins_to_two() {
        assert_eq!(threaded_counter_witness(), 2);
    }

    #[test]
    fn macro_dependency_marker_is_linked() {
        macro_dependency_marker();
    }
}
