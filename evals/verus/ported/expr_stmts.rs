// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::ensures(result == v)]
fn expr_stmts_id_value(v: u64) -> u64 {
    v
}

#[trust_vc::ensures(result == 13u64)]
fn test_stmts_expr_1() -> u64 {
    let mut a = 12u64;
    let b = expr_stmts_id_value({
        a = a + 1u64;
        a
    });
    trust_vc::assert!(b == 13u64);
    b
}

#[trust_vc::ensures(result == *v)]
fn expr_stmts_id_ref(v: &u64) -> u64 {
    *v
}

#[trust_vc::ensures(result == 13u64)]
fn test_stmts_expr_2() -> u64 {
    let mut a = 12u64;
    let b = expr_stmts_id_ref({
        a = a + 1u64;
        &a
    });
    trust_vc::assert!(b == 13u64);
    b
}
