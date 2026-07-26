// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/cell_lib.rs`.
//
// The upstream file exercises Verus `vstd::cell::PCell` tracked tokens and
// `vstd::raw_ptr` allocation/read/write/deallocation tokens. TrustVc does not
// currently expose those ghost-token APIs or raw-pointer memory ownership
// contracts as executable Rust evidence.
//
// This first slice keeps the upstream manifest entry unsupported-gap and pins
// only a Rust-valid token-state model for the `PCell` happy path using
// immutable state snapshots plus concrete rejected boundaries for wrong take
// values and mismatched token ownership. The negative probes are scalarized to
// avoid current struct-field counterexample instability. Raw pointers and real
// `std::cell::Cell`/`UnsafeCell` behavior remain known gaps rather than
// replacement evidence.

#![allow(dead_code)]

pub type CellLibRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type CellLibRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CELL_LIB_RS_EXPECTED_CASES: &[CellLibRsExpectedCase] = &[
    (
        "cell_lib_empty_cell_handle_verified",
        "CELL_TEST PCell::empty cell id",
        "verified",
        1,
    ),
    (
        "cell_lib_empty_token_verified",
        "CELL_TEST PCell::empty token contents",
        "verified",
        1,
    ),
    (
        "cell_lib_model_put",
        "CELL_TEST cell.put token transition",
        "verified",
        1,
    ),
    (
        "cell_lib_model_replace",
        "CELL_TEST cell.replace token transition",
        "verified",
        1,
    ),
    (
        "cell_lib_pcell_state_trace_verified",
        "CELL_TEST put/replace/borrow/take happy path",
        "verified",
        1,
    ),
    (
        "cell_lib_take_wrong_value_counterexample",
        "CELL_TEST false taken-value assertion",
        "counterexample",
        1,
    ),
    (
        "cell_lib_mismatched_token_counterexample",
        "cell_mismatch_* token/cell id mismatch",
        "counterexample",
        1,
    ),
    (
        "cell_lib_std_cell_get_currently_blocked",
        "real std::cell::Cell method boundary",
        "error",
        0,
    ),
];

pub const CELL_LIB_RS_FAIL_CLOSED_ERROR_PATTERNS: &[CellLibRsFailClosedErrorPatterns] = &[(
    "cell_lib_std_cell_get_currently_blocked",
    &["std::cell::Cell::new"],
)];

pub fn cell_lib_rs_expected_cases() -> &'static [CellLibRsExpectedCase] {
    CELL_LIB_RS_EXPECTED_CASES
}

pub fn cell_lib_rs_fail_closed_error_patterns() -> &'static [CellLibRsFailClosedErrorPatterns] {
    CELL_LIB_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct TrustVcPCell {
    id: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct TrustVcPCellToken {
    pcell_id: u64,
    initialized: bool,
    value: u32,
}

#[trust_vc::ensures(result.id == id)]
fn cell_lib_empty_cell_handle_verified(id: u64) -> TrustVcPCell {
    TrustVcPCell { id }
}

#[trust_vc::ensures(result.pcell_id == id)]
#[trust_vc::ensures(result.initialized == false)]
fn cell_lib_empty_token_verified(id: u64) -> TrustVcPCellToken {
    TrustVcPCellToken {
        pcell_id: id,
        initialized: false,
        value: 0u32,
    }
}

#[trust_vc::requires(token.pcell_id == cell.id)]
#[trust_vc::requires(token.initialized == false)]
#[trust_vc::ensures(result.pcell_id == cell.id)]
#[trust_vc::ensures(result.initialized)]
#[trust_vc::ensures(result.value == value)]
fn cell_lib_model_put(
    cell: TrustVcPCell,
    token: TrustVcPCellToken,
    value: u32,
) -> TrustVcPCellToken {
    TrustVcPCellToken {
        pcell_id: token.pcell_id,
        initialized: true,
        value,
    }
}

#[trust_vc::requires(token.pcell_id == cell.id)]
#[trust_vc::requires(token.initialized)]
#[trust_vc::ensures(result.pcell_id == cell.id)]
#[trust_vc::ensures(result.initialized)]
#[trust_vc::ensures(result.value == value)]
fn cell_lib_model_replace(
    cell: TrustVcPCell,
    token: TrustVcPCellToken,
    value: u32,
) -> TrustVcPCellToken {
    TrustVcPCellToken {
        pcell_id: token.pcell_id,
        initialized: true,
        value,
    }
}

#[trust_vc::ensures(true)]
fn cell_lib_pcell_state_trace_verified(cell_id: u64) {
    let cell = TrustVcPCell { id: cell_id };
    let empty = TrustVcPCellToken {
        pcell_id: cell_id,
        initialized: false,
        value: 0u32,
    };

    trust_vc::assert!(empty.pcell_id == cell.id);
    trust_vc::assert!(empty.initialized == false);

    let after_put = TrustVcPCellToken {
        pcell_id: empty.pcell_id,
        initialized: true,
        value: 5u32,
    };
    trust_vc::assert!(after_put.pcell_id == cell.id);
    trust_vc::assert!(after_put.initialized);
    trust_vc::assert!(after_put.value == 5u32);

    let replaced = after_put.value;
    let after_replace = TrustVcPCellToken {
        pcell_id: after_put.pcell_id,
        initialized: true,
        value: 7u32,
    };
    trust_vc::assert!(after_replace.pcell_id == cell.id);
    trust_vc::assert!(after_replace.initialized);
    trust_vc::assert!(after_replace.value == 7u32);
    trust_vc::assert!(replaced == 5u32);

    let borrowed = after_replace.value;
    trust_vc::assert!(borrowed == 7u32);

    let taken = after_replace.value;
    let after_take = TrustVcPCellToken {
        pcell_id: after_replace.pcell_id,
        initialized: false,
        value: after_replace.value,
    };
    trust_vc::assert!(after_take.pcell_id == cell.id);
    trust_vc::assert!(after_take.initialized == false);
    trust_vc::assert!(taken == 7u32);
}

#[trust_vc::ensures(true)]
fn cell_lib_take_wrong_value_counterexample() {
    let taken = 7u32;
    trust_vc::assert!(taken == 5u32);
}

#[trust_vc::ensures(true)]
fn cell_lib_mismatched_token_counterexample() {
    let cell_id = 1u64;
    let token_pcell_id = 2u64;
    trust_vc::assert!(token_pcell_id == cell_id);
}

#[trust_vc::ensures(true)]
fn cell_lib_std_cell_get_currently_blocked() {
    let cell = std::cell::Cell::new(5u32);
    trust_vc::assert!(cell.get() == 5u32);
}
