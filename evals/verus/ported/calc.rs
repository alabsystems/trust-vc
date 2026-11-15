// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::{seq, Seq};

#[trust_vc::ensures(true)]
fn calc_basics() {
    let a: Seq<u8> = seq![1u8, 2u8];
    let b: Seq<u8> = seq![1u8];
    let c: Seq<u8> = seq![2u8];
    let d: Seq<u8> = seq![1u8, 2u8];

    trust_vc::calc! {
        (==)
        a;
        { trust_vc::assert_seqs_equal!(a == b + c); }
        b + c;
        { trust_vc::assert_seqs_equal!(b + c == d); }
        d;
    };

    trust_vc::assert!(a == d);
}

fn calc_scalar_omitted_ops_with_proof_blocks() {
    let a: i32 = 2i32;
    let b: i32 = 3i32;
    let c: i32 = 1i32;
    let d: i32 = 4i32;

    trust_vc::calc! {
        (==)
        a + c;
        { trust_vc::assert!(a + c == b); }
        b;
        { trust_vc::assert!(b == d - c); }
        d - c;
    };

    trust_vc::assert!(a + c == d - c);
}

#[trust_vc::ensures(true)]
fn calc_intermediate_relations() {
    let x: i32 = 2i32;

    trust_vc::calc! {
        (<=)
        2i32;
        (==) {} 3i32 - 1i32;
        (<) {} 5i32;
    };

    trust_vc::assert!(x <= 5i32);
}

#[trust_vc::ensures(true)]
fn calc_hides_intermediates() {
    let a: Seq<u8> = seq![1u8, 2u8];
    let b: Seq<u8> = seq![123u8, 45u8];
    let c: Seq<u8> = seq![67u8, 89u8];
    let d: Seq<u8> = seq![1u8, 2u8];

    trust_vc::calc! {
        (==)
        a;
        { trust_vc::assume!(false); } b;
        { trust_vc::assume!(false); } c;
        { trust_vc::assume!(false); } d;
    };

    trust_vc::assert!(b == d); // FAILS
}

fn calc_scalar_keeps_intermediates_distinct() {
    let a: i32 = 3i32;
    let b: i32 = 10i32;
    let c: i32 = 20i32;
    let d: i32 = 3i32;

    trust_vc::calc! {
        (==)
        a;
        { trust_vc::assume!(false); } b + c;
        { trust_vc::assert!(1i32 == 2i32); } d;
    };
}

fn calc_scalar_descending_relations() {
    let high: i32 = 9i32;
    let middle: i32 = 6i32;
    let low: i32 = 2i32;

    trust_vc::calc! {
        (>=)
        high;
        (==) {} 12i32 - 3i32;
        (>) {} middle;
        {} low;
    };

    trust_vc::assert!(high >= low);
}

#[trust_vc::ensures(true)]
fn calc_keeps_intermediates_distinct() {
    let a: Seq<u8> = seq![1u8, 2u8];
    let b: Seq<u8> = seq![1u8];
    let c: Seq<u8> = seq![2u8];
    let d: Seq<u8> = seq![1u8, 2u8];

    trust_vc::calc! {
        (==)
        a; { trust_vc::assume!(false); }
        b + c; { trust_vc::assert!(1i32 == 2i32); } // FAILS
        d;
    };
}

#[trust_vc::ensures(true)]
fn calc_checks_consistency_of_intermediate_relations() {
    trust_vc::calc! {
        (<=)
        2i32;
        (==) {} 3i32 - 1i32;
        (>) {} 1i32;
        {} 5i32;
    };
}
