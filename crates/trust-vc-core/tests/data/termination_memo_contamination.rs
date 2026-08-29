// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the isolated-termination-query MEMO contamination probe.
//
// Each pair proves a WELL-FOUNDED cycle first (populating the memo) and then a
// NON-SHRINKING one whose defining axiom is contradictory. If the memo ever
// served the well-founded verdict to the non-shrinking query, the `exploit`
// function would verify while returning 0 and claiming 1 — the cardinal
// false-verify. Verified in ONE process with `--test-threads=1`, so libtest
// runs every test on the SAME thread and the thread-local memo is genuinely
// shared across them.

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn good(n: u64) -> u64 {
    if n == 0u64 {
        1u64
    } else {
        good(n - 1u64)
    }
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bad(n: u64) -> u64 {
    bad(n) + 1u64
}

#[trust_vc::ensures(result == 1u64)]
fn memo_warmup(k: u64) -> u64 {
    let _w = good(k);
    1u64
}

#[trust_vc::ensures(result == 1u64)]
fn memo_exploit(k: u64) -> u64 {
    let _w = bad(k);
    0u64
}

// The tightest key-collision candidate the isolated query's obligation text can
// express: the same parameter name, the same type, differing only in the
// RECURSIVE ARGUMENT.
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn t1(n: u64) -> u64 {
    if n == 0u64 {
        1u64
    } else {
        t1(n - 1u64)
    }
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn t2(n: u64) -> u64 {
    if n == 0u64 {
        1u64
    } else {
        t2(n)
    }
}

#[trust_vc::ensures(result == 1u64)]
fn twin_warmup(k: u64) -> u64 {
    let _w = t1(k);
    1u64
}

#[trust_vc::ensures(result == 1u64)]
fn twin_exploit(k: u64) -> u64 {
    let _w = t2(k);
    0u64
}
