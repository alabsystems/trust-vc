// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/raw_ptrs.rs`.
//
// The upstream file exercises Verus raw-pointer views, provenance/metadata,
// strict-provenance operations, PointsTo tokens, raw-pointer reads/writes,
// pointer/int casts, unsupported int-to-pointer casts, raw-pointer dereference
// diagnostics, and allocation helpers. TrustVc does not currently model raw
// pointer values, pointer provenance, raw memory permissions, or vstd::raw_ptr
// APIs as executable replacement evidence.
//
// This scout keeps the manifest entry unsupported-gap and records only stable,
// Rust-valid behavior TrustVc can execute today:
// - address/provenance/metadata scalar witnesses for upstream pointer-view,
//   strict-provenance, cast, pointer/int, comparison, and slice metadata themes;
// - a scalar null-address boundary witness adjacent to upstream `test_null`;
// - sized and unsized extensionality witnesses for address/provenance/metadata
//   equality;
// - a small PointsTo-token state-machine surrogate for write/ref/read flow;
// - false scalar probes that produce counterexamples for upstream failing shapes;
//   and
// - native raw-pointer construction/cast/dereference/provenance/PointsTo/allocate
//   operations as fail-closed unsupported boundaries.

#![allow(dead_code, unused_variables)]

#[derive(Clone, Copy, PartialEq, Eq)]
struct RawPtrViewWitness {
    addr: usize,
    same_addr: usize,
    provenance_token: u32,
    metadata: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct RawPointsToStateWitness {
    ptr_addr: usize,
    is_init: bool,
    value: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct RawPointsToApiBoundary {
    ptr_addr: usize,
    initialized: bool,
    value: u8,
}

impl RawPointsToApiBoundary {
    fn ptr(self) -> usize {
        self.ptr_addr
    }

    fn is_init(self) -> bool {
        self.initialized
    }

    fn value(self) -> u8 {
        self.value
    }
}

extern "Rust" {
    fn raw_ptr_mut_write_boundary(
        ptr: *mut u8,
        token: RawPointsToApiBoundary,
        value: u8,
    ) -> RawPointsToApiBoundary;

    fn raw_ptr_allocate_boundary(size: usize, align: usize) -> *mut u8;
}

pub struct RawPtrsExpectedCase {
    pub case: &'static str,
    pub upstream_case: &'static str,
    pub evidence_status: &'static str,
    pub min_obligations: usize,
}

pub const RAW_PTRS_RS_EXPECTED_CASES: &[RawPtrsExpectedCase] = &[
    RawPtrsExpectedCase {
        case: "raw_ptr_addr_view_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_null_addr_boundary_surrogate_verified",
        upstream_case: "test_null",
        evidence_status: "verified",
        min_obligations: 2,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_mut_const_cast_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_strict_provenance_with_addr_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_slice_metadata_cast_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_pointer_int_cast_surrogate_verified",
        upstream_case: "pointer_cast_to_ints",
        evidence_status: "verified",
        min_obligations: 2,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_compare_addr_surrogate_verified",
        upstream_case: "compare_const_mut_pointers",
        evidence_status: "verified",
        min_obligations: 2,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_points_to_write_read_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 6,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_addr_distinct_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_strict_provenance_addr_change_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_pointer_int_truncation_counterexample",
        upstream_case: "pointer_cast_to_ints",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_exec_eq_not_spec_eq_counterexample",
        upstream_case: "pointer_exec_eq_is_not_spec_eq",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_points_to_uninit_read_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_points_to_wrong_ptr_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_int_to_mut_ptr_cast_currently_blocked",
        upstream_case: "not_supported_int_to_ptr_cast",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_null_constructor_currently_blocked",
        upstream_case: "test_null",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_null_mut_constructor_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_const_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_mut_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_mut_to_const_cast_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_addr_method_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_with_addr_method_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_compare_const_mut_native_currently_blocked",
        upstream_case: "compare_const_mut_pointers",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_points_to_token_methods_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 7,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_points_to_write_api_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_allocate_helper_currently_blocked",
        upstream_case: "allocate_in_bounds",
        evidence_status: "error",
        min_obligations: 0,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_extensionality_sized_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    RawPtrsExpectedCase {
        case: "raw_ptr_extensionality_unsized_metadata_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
];

pub const RAW_PTRS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "raw_ptr_int_to_mut_ptr_cast_currently_blocked",
        &["unsupported cast from", "*mutu8"],
    ),
    (
        "raw_ptr_null_constructor_currently_blocked",
        &["unknown return type", "core::ptr::null"],
    ),
    (
        "raw_ptr_null_mut_constructor_currently_blocked",
        &["unknown return type", "core::ptr::null_mut"],
    ),
    (
        "raw_ptr_const_deref_currently_blocked",
        &["dereference expressions are not supported", "*x"],
    ),
    (
        "raw_ptr_mut_deref_currently_blocked",
        &["dereference expressions are not supported", "*x"],
    ),
    (
        "raw_ptr_mut_to_const_cast_currently_blocked",
        &["unsupported cast", "*constu8", "*mutu8"],
    ),
    (
        "raw_ptr_addr_method_currently_blocked",
        &[
            "addr",
            "unsupported method",
            "unknown return type",
            "unsupported cast",
        ],
    ),
    (
        "raw_ptr_with_addr_method_currently_blocked",
        &[
            "with_addr",
            "unsupported method",
            "unknown return type",
            "unsupported cast",
        ],
    ),
    (
        "raw_ptr_compare_const_mut_native_currently_blocked",
        &["unsupported", "unsupported cast", "*constu32", "*mutu32"],
    ),
    (
        "raw_ptr_points_to_write_api_currently_blocked",
        &[
            "raw_ptr_mut_write_boundary",
            "unknown return type",
            "unsupported",
        ],
    ),
    (
        "raw_ptr_allocate_helper_currently_blocked",
        &[
            "raw_ptr_allocate_boundary",
            "unknown return type",
            "unsupported",
        ],
    ),
];

pub fn raw_ptrs_rs_expected_cases() -> &'static [RawPtrsExpectedCase] {
    RAW_PTRS_RS_EXPECTED_CASES
}

pub fn raw_ptrs_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    RAW_PTRS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn raw_ptr_addr_view_surrogate_verified(addr: usize) {
    let witness = RawPtrViewWitness {
        addr,
        same_addr: addr,
        provenance_token: 7u32,
        metadata: 0usize,
    };
    let cast_like_witness = RawPtrViewWitness {
        addr,
        same_addr: witness.same_addr,
        provenance_token: witness.provenance_token,
        metadata: 0usize,
    };

    trust_vc::assert!(witness.addr == witness.same_addr);
    trust_vc::assert!(witness.provenance_token == cast_like_witness.provenance_token);
    trust_vc::assert!(cast_like_witness.metadata == 0usize);
    trust_vc::assert!(witness == cast_like_witness);
}

#[trust_vc::ensures(true)]
fn raw_ptr_null_addr_boundary_surrogate_verified() {
    let null_addr = 0usize;
    let one_past_null_addr = null_addr + 1usize;

    trust_vc::assert!(null_addr == 0usize);
    trust_vc::assert!(one_past_null_addr != null_addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_mut_const_cast_surrogate_verified(addr: usize, provenance_token: u32) {
    let mutable_view = RawPtrViewWitness {
        addr,
        same_addr: addr,
        provenance_token,
        metadata: 0usize,
    };
    let const_view = RawPtrViewWitness {
        addr: mutable_view.addr,
        same_addr: mutable_view.same_addr,
        provenance_token: mutable_view.provenance_token,
        metadata: mutable_view.metadata,
    };

    trust_vc::assert!(const_view.addr == mutable_view.addr);
    trust_vc::assert!(const_view.same_addr == mutable_view.same_addr);
    trust_vc::assert!(const_view.provenance_token == mutable_view.provenance_token);
    trust_vc::assert!(const_view == mutable_view);
}

#[trust_vc::ensures(true)]
fn raw_ptr_strict_provenance_with_addr_surrogate_verified(
    addr: usize,
    provenance_token: u32,
    metadata: usize,
) {
    let original = RawPtrViewWitness {
        addr,
        same_addr: addr,
        provenance_token,
        metadata,
    };
    let with_addr = RawPtrViewWitness {
        addr: 7usize,
        same_addr: 7usize,
        provenance_token: original.provenance_token,
        metadata: original.metadata,
    };

    trust_vc::assert!(with_addr.addr == 7usize);
    trust_vc::assert!(with_addr.same_addr == 7usize);
    trust_vc::assert!(with_addr.provenance_token == original.provenance_token);
    trust_vc::assert!(with_addr.metadata == original.metadata);
}

#[trust_vc::ensures(true)]
fn raw_ptr_slice_metadata_cast_surrogate_verified() {
    let array_ptr_view = RawPtrViewWitness {
        addr: 64usize,
        same_addr: 64usize,
        provenance_token: 9u32,
        metadata: 16usize,
    };
    let slice_ptr_view = RawPtrViewWitness {
        addr: array_ptr_view.addr,
        same_addr: array_ptr_view.same_addr,
        provenance_token: array_ptr_view.provenance_token,
        metadata: array_ptr_view.metadata,
    };

    trust_vc::assert!(slice_ptr_view.addr == array_ptr_view.addr);
    trust_vc::assert!(slice_ptr_view.provenance_token == array_ptr_view.provenance_token);
    trust_vc::assert!(slice_ptr_view.metadata == 16usize);
    trust_vc::assert!(slice_ptr_view == array_ptr_view);
}

#[trust_vc::ensures(true)]
fn raw_ptr_pointer_int_cast_surrogate_verified(addr: usize) {
    let addr_as_usize = addr;
    let narrowed = addr as u16;
    let narrowed_again = addr as u16;

    trust_vc::assert!(addr_as_usize == addr);
    trust_vc::assert!(narrowed == narrowed_again);
}

#[trust_vc::ensures(true)]
fn raw_ptr_compare_addr_surrogate_verified(left_addr: usize, right_addr: usize) {
    let result = left_addr < right_addr;

    trust_vc::assert!(result == (left_addr < right_addr));
    trust_vc::assert!((left_addr >= right_addr) == (result == false));
}

#[trust_vc::ensures(true)]
fn raw_ptr_extensionality_sized_surrogate_verified(addr: usize, provenance_token: u32) {
    let left = RawPtrViewWitness {
        addr,
        same_addr: addr,
        provenance_token,
        metadata: 0usize,
    };
    let right = RawPtrViewWitness {
        addr: left.addr,
        same_addr: left.same_addr,
        provenance_token: left.provenance_token,
        metadata: 0usize,
    };

    trust_vc::assert!(left.addr == right.addr);
    trust_vc::assert!(left.provenance_token == right.provenance_token);
    trust_vc::assert!(left.metadata == right.metadata);
    trust_vc::assert!(left == right);
}

#[trust_vc::ensures(true)]
fn raw_ptr_points_to_write_read_surrogate_verified(ptr_addr: usize) {
    let token_before_write = RawPointsToStateWitness {
        ptr_addr,
        is_init: false,
        value: 0u8,
    };
    let token_after_write = RawPointsToStateWitness {
        ptr_addr: token_before_write.ptr_addr,
        is_init: true,
        value: 20u8,
    };
    let token_after_read = RawPointsToStateWitness {
        ptr_addr: token_after_write.ptr_addr,
        is_init: false,
        value: token_after_write.value,
    };

    trust_vc::assert!(token_after_write.ptr_addr == token_before_write.ptr_addr);
    trust_vc::assert!(token_after_write.is_init);
    trust_vc::assert!(token_after_write.value == 20u8);
    trust_vc::assert!(token_after_read.value == 20u8);
    trust_vc::assert!(token_after_read.ptr_addr == token_before_write.ptr_addr);
    trust_vc::assert!(token_after_read.is_init == false);
}

#[trust_vc::ensures(true)]
fn raw_ptr_addr_distinct_counterexample() {
    let left_addr = 7usize;
    let right_addr = 8usize;

    trust_vc::assert!(left_addr == right_addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_strict_provenance_addr_change_counterexample() {
    let original_addr = 4usize;
    let with_addr_addr = 7usize;

    trust_vc::assert!(original_addr == with_addr_addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_pointer_int_truncation_counterexample() {
    let wide_addr = 65_536usize;
    let truncated_addr = 0usize;

    trust_vc::assert!(wide_addr == truncated_addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_exec_eq_not_spec_eq_counterexample() {
    let exec_equal_addr = 19usize;
    let left_provenance_token = 1u32;
    let right_provenance_token = 2u32;

    trust_vc::assert!(exec_equal_addr == 19usize);
    trust_vc::assert!(left_provenance_token == right_provenance_token);
}

#[trust_vc::ensures(true)]
fn raw_ptr_extensionality_unsized_metadata_counterexample() {
    let left_addr = 24usize;
    let right_addr = left_addr;
    let left_provenance_token = 5u32;
    let right_provenance_token = left_provenance_token;
    let left_metadata = 4usize;
    let right_metadata = 8usize;

    trust_vc::assert!(left_addr == right_addr);
    trust_vc::assert!(left_provenance_token == right_provenance_token);
    trust_vc::assert!(left_metadata == right_metadata);
}

#[trust_vc::ensures(true)]
fn raw_ptr_points_to_uninit_read_counterexample() {
    let token_is_init = false;

    trust_vc::assert!(token_is_init);
}

#[trust_vc::ensures(true)]
fn raw_ptr_points_to_wrong_ptr_counterexample() {
    let ptr_addr = 41usize;
    let token_ptr_addr = 42usize;

    trust_vc::assert!(ptr_addr == token_ptr_addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_int_to_mut_ptr_cast_currently_blocked(addr: usize) {
    trust_vc::assert!(addr == (addr as *mut u8) as usize);
}

#[trust_vc::ensures(true)]
fn raw_ptr_null_constructor_currently_blocked() {
    trust_vc::assert!((core::ptr::null::<u8>() as usize) == 0usize);
}

#[trust_vc::ensures(true)]
fn raw_ptr_null_mut_constructor_currently_blocked() {
    trust_vc::assert!((core::ptr::null_mut::<u8>() as usize) == 0usize);
}

#[trust_vc::ensures(true)]
fn raw_ptr_const_deref_currently_blocked(ptr: *const u8) {
    unsafe {
        let value = *ptr;
        trust_vc::assert!(value == value);
    }
}

#[trust_vc::ensures(true)]
fn raw_ptr_mut_deref_currently_blocked(ptr: *mut u8) {
    unsafe {
        let value = *ptr;
        trust_vc::assert!(value == value);
    }
}

#[trust_vc::ensures(true)]
fn raw_ptr_mut_to_const_cast_currently_blocked(addr: usize) {
    let ptr = addr as *mut u8;
    let const_ptr = ptr as *const u8;

    trust_vc::assert!((const_ptr as usize) == addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_addr_method_currently_blocked(addr: usize) {
    let ptr = addr as *mut u64;
    let addr = ptr.addr();

    trust_vc::assert!(addr == addr);
}

#[trust_vc::ensures(true)]
fn raw_ptr_with_addr_method_currently_blocked(addr: usize) {
    let ptr = addr as *mut u64;
    let shifted = ptr.with_addr(7usize);

    trust_vc::assert!(shifted == shifted);
}

#[trust_vc::ensures(true)]
fn raw_ptr_compare_const_mut_native_currently_blocked(left_addr: usize, right_addr: usize) {
    let p1 = left_addr as *const u32;
    let p2 = right_addr as *mut u32;
    let result = p1 < p2;

    trust_vc::assert!(result == ((p1 as usize) < (p2 as *const u32 as usize)));
}

// De-surrogated 2026-07-18: PointsTo-token method reads (`ptr()`, `is_init()`,
// `value()`) against the token's fields now verify (unmasked behind ROOT B;
// stash-control showed the flip is pre-existing, not ROOT B itself).
// Discriminator-certified genuine: `ptr() != ptr_addr` and
// `is_init() == !initialized` mutations both Counterexample with models, and
// the `ptr_addr + 1` form is non-verified (overflow side-check fails closed).
#[trust_vc::ensures(true)]
fn raw_ptr_points_to_token_methods_verified(token: RawPointsToApiBoundary) {
    trust_vc::assert!(token.ptr() == token.ptr_addr);
    trust_vc::assert!(token.is_init() == token.initialized);
    trust_vc::assert!(token.value() == token.value);
}

#[trust_vc::ensures(true)]
fn raw_ptr_points_to_write_api_currently_blocked(addr: usize) {
    let ptr = addr as *mut u8;
    let token = RawPointsToApiBoundary {
        ptr_addr: 0usize,
        initialized: false,
        value: 0u8,
    };
    let token = unsafe { raw_ptr_mut_write_boundary(ptr, token, 20u8) };

    trust_vc::assert!(token.initialized);
}

#[trust_vc::ensures(true)]
fn raw_ptr_allocate_helper_currently_blocked() {
    let block_ptr = unsafe { raw_ptr_allocate_boundary(8usize, 4usize) };

    trust_vc::assert!((block_ptr as usize) == (block_ptr as usize));
}
