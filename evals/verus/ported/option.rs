// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub const OPTION_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test_unwrap_expect",
        "test_unwrap_expect",
        "verified",
        1,
    ),
    ("test_ok_or_else", "test_ok_or_else", "verified", 1),
    (
        "test_unwrap_or_default",
        "test_unwrap_or_default",
        "verified",
        1,
    ),
    ("test_and_then", "test_and_then", "verified", 1),
    ("test_cloned", "test_cloned", "verified", 1),
    (
        "test_unwrap_or_else",
        "test_unwrap_or_else",
        "verified",
        1,
    ),
];

pub fn option_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    OPTION_RS_EXPECTED_CASES
}

#[trust_vc::ensures(
    Option::<i8>::Some(1i8).is_some()
        && Option::<i8>::Some(1i8).unwrap() == 1i8
        && Option::<i8>::Some(1i8).expect("option was built with Some") == 1i8
        && Option::<i8>::None.is_none()
)]
fn test_unwrap_expect() {}

#[trust_vc::ensures(
    { let opt: Option<u32> = Some(42u32); opt.ok_or_else(|| 0u32) }
        == Ok::<u32, u32>(42u32)
        && { let opt: Option<u32> = None; opt.ok_or_else(|| -> u32 { 99u32 }) }
            == Err::<u32, u32>(99u32)
        && {
            let opt: Option<u32> = Some(42u32);
            let res: Result<u32, u32> = opt.ok_or_else(|| -> u32 { 99u32 });
            match opt {
                Some(x) => res == Ok::<u32, u32>(x),
                None => res == Err::<u32, u32>(99u32),
            }
        }
        && {
            let opt: Option<u32> = None;
            let res: Result<u32, u32> = opt.ok_or_else(|| -> u32 { 99u32 });
            match opt {
                Some(x) => res == Ok::<u32, u32>(x),
                None => res == Err::<u32, u32>(99u32),
            }
        }
)]
fn test_ok_or_else() {}

#[trust_vc::ensures(
    { let opt: Option<u32> = Some(42u32); opt.unwrap_or_default() } == 42u32
        && { let opt: Option<u32> = None; opt.unwrap_or_default() } == 0u32
)]
fn test_unwrap_or_default() {}

#[trust_vc::ensures(
    { let opt: Option<u32> = Some(2u32); opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }) }
        == Some(3u32)
        && { let opt: Option<u32> = None; opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }) }
            == Option::<u32>::None
        && {
            let opt: Option<u32> = Some(2u32);
            let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) });
            match opt {
                Some(x) => x < 1000u32 && res == Some(x + 1u32),
                None => res == Option::<u32>::None,
            }
        }
        && {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) });
            match opt {
                Some(x) => x < 1000u32 && res == Some(x + 1u32),
                None => res == Option::<u32>::None,
            }
        }
)]
fn test_and_then() {}

#[trust_vc::ensures(
    { let val: u32 = 42u32; let opt: Option<&u32> = Some(&val); opt.cloned() }
        == Some(42u32)
        && { let opt: Option<&u32> = None; opt.cloned() } == Option::<u32>::None
)]
fn test_cloned() {}

#[trust_vc::ensures(
    { let opt: Option<u32> = Some(42u32); opt.unwrap_or_else(|| 0u32) } == 42u32
        && { let opt: Option<u32> = None; opt.unwrap_or_else(|| -> u32 { 99u32 }) } == 99u32
        && {
            let opt: Option<u32> = Some(42u32);
            let val: u32 = opt.unwrap_or_else(|| -> u32 { 99u32 });
            match opt { Some(x) => val == x, None => val == 99u32 }
        }
        && {
            let opt: Option<u32> = None;
            let val: u32 = opt.unwrap_or_else(|| -> u32 { 99u32 });
            match opt { Some(x) => val == x, None => val == 99u32 }
        }
)]
fn test_unwrap_or_else() {}
