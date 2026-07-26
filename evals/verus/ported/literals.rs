// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::{set, Seq, Set};

#[trust_vc::ensures(true)]
fn set_literal_0() {
    trust_vc::assert!(Set::<i32>::empty() == Set::<i32>::empty());
    trust_vc::assert!(Set::<i32>::empty().len() == 0usize);
    trust_vc::assert!(!Set::<i32>::empty().contains(2i32));
}

#[trust_vc::ensures(true)]
fn set_literal_1() {
    trust_vc::assert!(set![2i32] == set![2i32]);
    trust_vc::assert!(set![2i32].len() == 1usize);
    trust_vc::assert!(set![2i32].contains(2i32));
    trust_vc::assert!(!set![2i32].contains(4i32));
}

#[trust_vc::ensures(true)]
fn set_literal_2() {
    trust_vc::assert!(set![2i32, 4i32] == set![4i32, 2i32]);
    trust_vc::assert!(set![2i32, 4i32,].len() == 2usize);
    trust_vc::assert!(set![2i32, 4i32].contains(2i32));
    trust_vc::assert!(set![2i32, 4i32].contains(4i32));
    trust_vc::assert!(!set![2i32, 4i32].contains(6i32));
}

#[trust_vc::ensures(true)]
fn seq_literals() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(2i32)
            .push(4i32)
            .push(6i32)
            .push(8i32)
            .push(10i32)
            .len()
            == 5usize
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(2i32)
            .push(4i32)
            .push(6i32)
            .push(8i32)
            .push(10i32)
            .index(0usize)
            == 2i32
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(2i32)
            .push(4i32)
            .push(6i32)
            .push(8i32)
            .push(10i32)
            .index(2usize)
            == 6i32
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(2i32)
            .push(4i32)
            .push(6i32)
            .push(8i32)
            .push(10i32)
            .index(4usize)
            == 10i32
    );
}
