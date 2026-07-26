// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::ensures(true)]
fn test1(b1: u32) {
    let b2 = !b1;
    trust_vc::assert_by_bit_vector!(b1 + b2 == 0xffff_ffffu32; requires b2 == !b1);
    trust_vc::assert!(b1 + b2 == 0xffff_ffffu32);
}

#[trust_vc::ensures(true)]
fn test2(b1: u32, b2: u32) {
    let b: u64 = (b1 as u64) << 32u64 | (b2 as u64);
    trust_vc::assert_by_bit_vector!(
        b == (b1 as u64) * 0x1_0000_0000u64 + (b2 as u64);
        requires b == ((b1 as u64) << 32u64 | (b2 as u64))
    );
    trust_vc::assert!(b == (b1 as u64) * 0x1_0000_0000u64 + (b2 as u64));
}

#[trust_vc::ensures(true)]
fn test3(b: u64) {
    let b1 = (b >> 32u64) as u32;
    let b2 = (b & 0x0000_0000_ffff_ffffu64) as u32;
    trust_vc::assert_by_bit_vector!(
        b == (b1 as u64) * 0x1_0000_0000u64 + (b2 as u64);
        requires b1 == (b >> 32u64) as u32,
            b2 == (b & 0x0000_0000_ffff_ffffu64) as u32
    );
    trust_vc::assert!(b == (b1 as u64) * 0x1_0000_0000u64 + (b2 as u64));
}

#[trust_vc::ensures(true)]
fn test1_fails(b: u32) {
    trust_vc::assert_by_bit_vector!((b << 2u32) == b * 4u32);
    trust_vc::assert!((b << 2u32) == b * 4u32);
    trust_vc::assert_by_bit_vector!((b << 1u32) == b * 4u32);
    trust_vc::assert!((b << 1u32) == b * 4u32);
}

#[trust_vc::ensures(true)]
fn test2_fails(b1: u32) {
    trust_vc::assert_by_bit_vector!((b1 << 1u32) == 0x200u32; requires b1 == 0x100u32);
    trust_vc::assert!((b1 << 1u32) == 0x200u32);
}

#[trust_vc::requires(b1 != b2)]
#[trust_vc::ensures(true)]
fn test3_fails(b1: u32, b2: u32) {
    trust_vc::assert_by_bit_vector!((b1 << 10u32) == (b2 << 10u32); requires b1 == b2);
}
