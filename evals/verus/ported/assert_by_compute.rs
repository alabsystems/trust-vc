// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc port for upstream rust_verify_test/tests/assert_by_compute.rs.
//
// This covers the local block-let portion of the upstream `lets` and `lets_bad`
// cases through `trust_vc::assert_by_compute!`, a broader finite bitwise
// constant subset including wider fixed-width unsigned values, signed shifts,
// and a recursive shift spec function,
// concrete datatype/tuple-struct/struct-like constants and Option matches, tuple projections,
// concrete sequence subranges, push/last/update/add operations, array constants,
// direct array literal indexing, and local array indexing,
// concrete bounded forall reductions, concrete char casts/comparisons,
// concrete `if_then_else` compute_only cases, concrete Euclidean `int` division/modulo
// including small-sign boundary cases, nested spec-function calls, a
// fail-closed module constant lookup boundary, the smallest executable
// compute_only syntax case, and bounded recursive spec-function compute cases.
// The manifest keeps the upstream file classified as an unsupported gap because
// TrustVc still lacks full parity for general
// bitwise compute, arbitrary datatypes/tuples/structs, closures, broader
// sequence/array operations, traits, external-body functions, and recursion-depth
// diagnostics.

use trust_vc_types::{int, Seq, View};

pub type AssertByComputeRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type AssertByComputeRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ASSERT_BY_COMPUTE_RS_EXPECTED_CASES: &[AssertByComputeRsExpectedCase] = &[
    ("lets_bool", "lets", "verified", 1),
    ("lets_arith", "lets", "verified", 1),
    ("lets_bad", "lets_bad", "counterexample", 1),
    ("bitwise_and_constants", "bit_vectors", "verified", 1),
    ("bitwise_basic_constants", "bit_vectors", "verified", 5),
    (
        "bitwise_wide_and_signed_shift_constants_compute_only",
        "bit_vectors",
        "verified",
        7,
    ),
    (
        "bitwise_wide_constants_counterexample",
        "bit_vectors",
        "counterexample",
        1,
    ),
    (
        "datatype_struct_tuple_constants_compute_only",
        "datatypes",
        "verified",
        4,
    ),
    (
        "datatype_struct_tuple_constants_counterexample",
        "datatypes",
        "counterexample",
        1,
    ),
    (
        "datatype_option_match_compute_only",
        "datatype",
        "verified",
        3,
    ),
    (
        "datatype_option_match_counterexample",
        "datatype",
        "counterexample",
        1,
    ),
    (
        "struct_constants_counterexample",
        "structs",
        "counterexample",
        1,
    ),
    (
        "sequence_constants_compute_only",
        "sequences",
        "verified",
        4,
    ),
    (
        "sequence_constants_counterexample",
        "sequences",
        "counterexample",
        1,
    ),
    (
        "sequence_subrange_compute_only",
        "sequences",
        "verified",
        2,
    ),
    (
        "sequence_subrange_counterexample",
        "sequences",
        "counterexample",
        1,
    ),
    (
        "sequence_push_last_update_add_compute_only",
        "sequences",
        "verified",
        7,
    ),
    (
        "sequence_push_last_update_add_counterexample",
        "sequences",
        "counterexample",
        1,
    ),
    (
        "array_constants_compute_only",
        "array_literals",
        "verified",
        3,
    ),
    (
        "array_literal_index_compute_only",
        "array_literals",
        "verified",
        1,
    ),
    (
        "array_constants_counterexample",
        "array_literals",
        "counterexample",
        1,
    ),
    (
        "array_literal_index_counterexample",
        "array_literals",
        "counterexample",
        1,
    ),
    (
        "bounded_forall_compute_only",
        "range_all_simple",
        "verified",
        1,
    ),
    (
        "bounded_forall_counterexample",
        "range_all_simple",
        "counterexample",
        1,
    ),
    (
        "char_casts_and_comparisons_compute_only",
        "char_casting",
        "verified",
        4,
    ),
    (
        "char_casts_counterexample",
        "char_casting",
        "counterexample",
        1,
    ),
    (
        "if_then_else_compute_only",
        "if_then_else",
        "verified",
        5,
    ),
    (
        "if_then_else_counterexample",
        "if_then_else",
        "counterexample",
        1,
    ),
    ("compute_only_arith", "arith", "verified", 1),
    (
        "compute_only_euclidean_div_mod_arith",
        "arith",
        "verified",
        1,
    ),
    (
        "compute_only_euclidean_div_mod_small_boundaries",
        "arith",
        "verified",
        1,
    ),
    (
        "compute_only_euclidean_div_mod_counterexample",
        "arith",
        "counterexample",
        1,
    ),
    (
        "compute_only_euclidean_div_mod_small_boundary_counterexample",
        "arith",
        "counterexample",
        1,
    ),
    (
        "compute_only_recursive_spec_function",
        "recursive_spec_fn",
        "verified",
        1,
    ),
    (
        "fn_calls_upstream_nested_compute_only",
        "fn_calls_good",
        "verified",
        4,
    ),
    (
        "depth_tracking_deep_but_finite_compute_only",
        "depth_tracking_deep_but_finite",
        "verified",
        1,
    ),
    (
        "lets_upstream_comparisons_compute_only",
        "lets",
        "verified",
        1,
    ),
    (
        "bitwise_recursive_shift_compute_only",
        "bit_vectors",
        "verified",
        1,
    ),
    (
        "tuple_projection_constants_compute_only",
        "tuples",
        "verified",
        1,
    ),
    (
        "sequence_upstream_literals_compute_only",
        "sequences",
        "verified",
        1,
    ),
    (
        "local_array_index_compute_only",
        "array_literals",
        "verified",
        1,
    ),
    (
        "lets_upstream_comparisons_counterexample",
        "lets",
        "counterexample",
        1,
    ),
    (
        "tuple_projection_counterexample",
        "tuples",
        "counterexample",
        1,
    ),
    (
        "sequence_upstream_literals_counterexample",
        "sequences",
        "counterexample",
        1,
    ),
    (
        "local_array_index_counterexample",
        "array_literals",
        "counterexample",
        1,
    ),
    (
        "bitwise_recursive_shift_counterexample",
        "bit_vectors",
        "counterexample",
        1,
    ),
    (
        "fn_calls_upstream_nested_counterexample",
        "fn_calls_good",
        "counterexample",
        1,
    ),
    (
        "depth_tracking_deep_but_finite_counterexample",
        "depth_tracking_deep_but_finite",
        "counterexample",
        1,
    ),
    (
        "const_in_another_module_compute_only",
        "const_in_another_module",
        "error",
        0,
    ),
];

pub const ASSERT_BY_COMPUTE_RS_FAIL_CLOSED_ERROR_PATTERNS: &[AssertByComputeRsFailClosedErrorPatterns] =
    &[(
        "const_in_another_module_compute_only",
        &[
            "unsupported expression `assert_by_compute_const_module::BIN_HUGE`",
            "only pure, side-effect-free expressions",
        ],
    )];

pub fn assert_by_compute_rs_expected_cases() -> &'static [AssertByComputeRsExpectedCase] {
    ASSERT_BY_COMPUTE_RS_EXPECTED_CASES
}

pub fn assert_by_compute_rs_fail_closed_error_patterns(
) -> &'static [AssertByComputeRsFailClosedErrorPatterns] {
    ASSERT_BY_COMPUTE_RS_FAIL_CLOSED_ERROR_PATTERNS
}

fn forall<T, F>(_f: F) -> bool
where
    F: Fn(T) -> bool,
{
    true
}

struct ComputePair {
    x: u8,
    flag: bool,
}

struct ComputeTuple(u8, bool);

mod assert_by_compute_const_module {
    pub const BIN_HUGE: u64 = 12u64;
}

#[trust_vc::decreases(amt)]
#[trust_vc::spec]
fn shifter_compute(x: u64, amt: usize) -> u64 {
    if amt == 0 {
        x
    } else {
        shifter_compute(x << 1u32, amt - 1usize)
    }
}

#[trust_vc::decreases(n)]
#[trust_vc::spec]
fn fib_compute(n: u64) -> u64 {
    if n <= 1 {
        n
    } else {
        fib_compute(n - 1) + fib_compute(n - 2)
    }
}

#[trust_vc::spec]
fn fn_call_eq_compute(x: int, y: int) -> bool {
    x == y
}

#[trust_vc::spec]
fn fn_call_g_compute(x: int) -> bool {
    fn_call_eq_compute(3 as int, x)
}

#[trust_vc::decreases(n)]
#[trust_vc::spec]
fn sum_compute(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        1 + sum_compute(n - 1)
    }
}

#[trust_vc::decreases(n)]
#[trust_vc::spec]
fn count_down_compute(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        count_down_compute(n - 1)
    }
}

#[trust_vc::ensures(true)]
fn lets_bool() {
    trust_vc::assert_by_compute!({
        let x = true;
        x
    });
}

#[trust_vc::ensures(true)]
fn lets_arith() {
    trust_vc::assert_by_compute!({
        let x: i32 = 7;
        let y: i32 = x + 1;
        x + y == 15
    });
}

#[trust_vc::ensures(true)]
fn lets_upstream_comparisons_compute_only() {
    trust_vc::assert_by_compute!(
        {
            let x: i32 = 7;
            x > 4
        };
        compute_only
    );
    trust_vc::assert_by_compute!(
        {
            let x: i32 = 7;
            let y: i32 = 14;
            x + y > 20
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn lets_bad() {
    trust_vc::assert_by_compute!({
        let x: i32 = 4;
        let r1: i32 = x + 1;
        let x: i32 = 5;
        let r2: i32 = x + 1;
        r1 == r2
    });
}

#[trust_vc::ensures(true)]
fn bitwise_and_constants() {
    trust_vc::assert_by_compute!((0b1010u8 & 0b1100u8) == 0b1000u8);
}

#[trust_vc::ensures(true)]
fn bitwise_basic_constants() {
    trust_vc::assert_by_compute!(!1u8 == 0xFEu8; compute_only);
    trust_vc::assert_by_compute!((1u8 ^ 2u8) == 3u8; compute_only);
    trust_vc::assert_by_compute!((1u8 | 2u8) == 3u8; compute_only);
    trust_vc::assert_by_compute!((1u8 << 3u32) == 8u8; compute_only);
    trust_vc::assert_by_compute!((2u8 >> 1u32) == 1u8; compute_only);
}

#[trust_vc::ensures(true)]
fn bitwise_wide_and_signed_shift_constants_compute_only() {
    trust_vc::assert_by_compute!(!1u32 == 0xFFFF_FFFEu32; compute_only);
    trust_vc::assert_by_compute!(!2u32 == 0xFFFF_FFFDu32; compute_only);
    trust_vc::assert_by_compute!(!1u64 == 0xFFFF_FFFF_FFFF_FFFEu64; compute_only);
    trust_vc::assert_by_compute!((2u32 << 3u32) == 16u32; compute_only);
    trust_vc::assert_by_compute!((0x8000_0000u32 >> 1u32) == 0x4000_0000u32; compute_only);
    trust_vc::assert_by_compute!((0x8000_0000u32 << 1u32) == 0u32; compute_only);
    trust_vc::assert_by_compute!(((0i32 - 1i32) << 3u32) == -8i32; compute_only);
}

#[trust_vc::ensures(true)]
fn bitwise_recursive_shift_compute_only() {
    trust_vc::assert_by_compute!(shifter_compute(1u64, 10usize) == 1024u64; compute_only);
}

#[trust_vc::ensures(true)]
fn bitwise_wide_constants_counterexample() {
    trust_vc::assert_by_compute!(!2u32 == 0xFFFF_FFFEu32; compute_only);
}

#[trust_vc::ensures(true)]
fn bitwise_recursive_shift_counterexample() {
    trust_vc::assert_by_compute!(shifter_compute(1u64, 4usize) == 8u64; compute_only);
}

#[trust_vc::ensures(true)]
fn datatype_struct_tuple_constants_compute_only() {
    trust_vc::assert_by_compute!(
        Some(2u8) == Some(2u8);
        compute_only
    );
    trust_vc::assert_by_compute!(
        ComputePair { x: 7u8, flag: true } == ComputePair { x: 7u8, flag: true };
        compute_only
    );
    trust_vc::assert_by_compute!(
        ComputePair { x: 7u8, flag: true }.x == 7u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        ComputeTuple(5u8, false).0 == 5u8;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn tuple_projection_constants_compute_only() {
    trust_vc::assert_by_compute!((42u32, 330u32, 0x1_0000_0000u64, false).0 == 42u32; compute_only);
    trust_vc::assert_by_compute!((42u32, 330u32, 0x1_0000_0000u64, false).1 == 330u32; compute_only);
    trust_vc::assert_by_compute!(
        (42u32, 330u32, 0x1_0000_0000u64, false).2 - 0xFFFF_FFFFu64 == 1u64;
        compute_only
    );
    trust_vc::assert_by_compute!(!(42u32, 330u32, 0x1_0000_0000u64, false).3; compute_only);
}

#[trust_vc::ensures(true)]
fn datatype_struct_tuple_constants_counterexample() {
    trust_vc::assert_by_compute!(
        Some(2u8) == Some(3u8);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn datatype_option_match_compute_only() {
    trust_vc::assert_by_compute!(
        match Some(true) {
            Some(b) => b,
            _ => false,
        };
        compute_only
    );
    trust_vc::assert_by_compute!(
        match Some(false) {
            Some(b) => !b,
            _ => false,
        };
        compute_only
    );
    trust_vc::assert_by_compute!(
        match Option::<bool>::None {
            Some(_) => false,
            _ => true,
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn datatype_option_match_counterexample() {
    trust_vc::assert_by_compute!(
        match Some(false) {
            Some(b) => b,
            _ => true,
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn tuple_projection_counterexample() {
    trust_vc::assert_by_compute!(
        (42u32, 330u32, 0x1_0000_0000u64, false).2 - 0xFFFF_FFFFu64 == 2u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn struct_constants_counterexample() {
    trust_vc::assert_by_compute!(
        ComputePair { x: 7u8, flag: true } == ComputePair { x: 8u8, flag: true };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn lets_upstream_comparisons_counterexample() {
    trust_vc::assert_by_compute!(
        {
            let x: i32 = 7;
            let y: i32 = 14;
            x + y > 22
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_constants_compute_only() {
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].len() == 3usize; compute_only);
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].index(1usize) == 2u8;
        compute_only
    );
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].contains(3u8); compute_only);
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8] == trust_vc_types::seq![1u8, 2u8];
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_upstream_literals_compute_only() {
    trust_vc::assert_by_compute!(Seq::<u8>::empty().len() == 0usize; compute_only);
    trust_vc::assert_by_compute!(Seq::<u8>::empty().push(4u8).len() == 1usize; compute_only);
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].index(0usize) == 1u8; compute_only);
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].index(2usize) == 3u8; compute_only);
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].last() == 3u8; compute_only);
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8].subrange(1usize, 2usize) == trust_vc_types::seq![2u8];
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8, 4u8, 5u8].subrange(2usize, 4usize)
            == trust_vc_types::seq![3u8, 4u8];
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_constants_counterexample() {
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].index(1usize) == 3u8;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_upstream_literals_counterexample() {
    trust_vc::assert_by_compute!(trust_vc_types::seq![1u8, 2u8, 3u8].last() == 2u8; compute_only);
}

#[trust_vc::ensures(true)]
fn sequence_subrange_compute_only() {
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8, 4u8].subrange(1usize, 3usize)
            == trust_vc_types::seq![2u8, 3u8];
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8, 4u8].subrange(1usize, 3usize).len() == 2usize;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_subrange_counterexample() {
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8, 4u8].subrange(1usize, 3usize)
            == trust_vc_types::seq![3u8, 4u8];
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_push_last_update_add_compute_only() {
    trust_vc::assert_by_compute!(
        Seq::<u8>::empty().push(4u8).last() == 4u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        Seq::<u8>::empty().push(1u8).push(2u8).index(1usize) == 2u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].update(1usize, 5u8).index(0usize) == 1u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].update(1usize, 5u8).index(1usize) == 5u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].update(1usize, 5u8).index(2usize) == 3u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8]
            .add(trust_vc_types::seq![4u8, 5u8])
            .len() == 5usize;
        compute_only
    );
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8]
            == trust_vc_types::seq![1u8].add(trust_vc_types::seq![2u8, 3u8]);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn sequence_push_last_update_add_counterexample() {
    trust_vc::assert_by_compute!(
        trust_vc_types::seq![1u8, 2u8, 3u8].update(1usize, 5u8).index(1usize) == 2u8;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn array_constants_compute_only() {
    trust_vc::assert_by_compute!([10u8, 20u8, 30u8].view().len() == 3usize; compute_only);
    trust_vc::assert_by_compute!(
        ([10u8, 20u8, 30u8].view() as Seq<u8>).index(2usize) == 30u8;
        compute_only
    );
    trust_vc::assert_by_compute!(
        ([10u8, 20u8, 30u8].view() as Seq<u8>).contains(20u8);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn array_literal_index_compute_only() {
    trust_vc::assert_by_compute!([41u32, 42u32][1usize] == 42u32; compute_only);
}

#[trust_vc::ensures(true)]
fn local_array_index_compute_only() {
    trust_vc::assert_by_compute!(
        {
            let my_array = [31u32, 32u32, 33u32];
            my_array[1usize] == 32u32
        };
        compute_only
    );
    trust_vc::assert_by_compute!(
        {
            let my_array = [31u32, 32u32, 33u32];
            let x: usize = 0usize;
            my_array[x] == 31u32
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn array_constants_counterexample() {
    trust_vc::assert_by_compute!(
        ([10u8, 20u8, 30u8].view() as Seq<u8>).contains(40u8);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn array_literal_index_counterexample() {
    trust_vc::assert_by_compute!([41u32, 42u32][1usize] == 41u32; compute_only);
}

#[trust_vc::ensures(true)]
fn local_array_index_counterexample() {
    trust_vc::assert_by_compute!(
        {
            let my_array = [31u32, 32u32, 33u32];
            my_array[1usize] == 31u32
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn bounded_forall_compute_only() {
    trust_vc::assert_by_compute!(
        forall(|i: usize| !(i < 3usize) || trust_vc_types::seq![1u8, 2u8, 3u8].index(i) >= 1u8);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn bounded_forall_counterexample() {
    trust_vc::assert_by_compute!(
        forall(|i: usize| !(i < 3usize) || trust_vc_types::seq![1u8, 2u8, 3u8].index(i) <= 2u8);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn char_casts_and_comparisons_compute_only() {
    trust_vc::assert_by_compute!('b' > 'a'; compute_only);
    trust_vc::assert_by_compute!(('A' as u32) == 65u32; compute_only);
    trust_vc::assert_by_compute!((65u8 as char) == 'A'; compute_only);
    trust_vc::assert_by_compute!(
        {
            let c: char = 66u8 as char;
            c == 'B'
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn char_casts_counterexample() {
    trust_vc::assert_by_compute!((66u8 as char) == 'A'; compute_only);
}

#[trust_vc::ensures(true)]
fn if_then_else_compute_only() {
    trust_vc::assert_by_compute!(9i32 == if 7i32 > 3i32 { 9i32 } else { 5i32 }; compute_only);
    trust_vc::assert_by_compute!(if true { true } else { false }; compute_only);
    trust_vc::assert_by_compute!(if !true { false } else { true }; compute_only);
    trust_vc::assert_by_compute!(if !!true { true } else { false }; compute_only);
    trust_vc::assert_by_compute!(
        9i32 == if 7i32 + 7i32 * 2i32 > 20i32 {
            7i32 + 2i32
        } else {
            22i32 - 5i32 + 10i32 * 10i32
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn if_then_else_counterexample() {
    trust_vc::assert_by_compute!(if 7i32 > 3i32 { false } else { true }; compute_only);
}

#[trust_vc::ensures(true)]
fn compute_only_arith() {
    trust_vc::assert_by_compute!(2u32 + 3u32 == 5u32; compute_only);
}

#[trust_vc::ensures(true)]
fn compute_only_euclidean_div_mod_arith() {
    trust_vc::assert_by_compute!(
        (8 as int) / (3 as int) == 2
            && (8 as int) / (-3 as int) == -2
            && (-8 as int) / (3 as int) == -3
            && (-8 as int) / (-3 as int) == 3
            && (8 as int) % (3 as int) == 2
            && (8 as int) % (-3 as int) == 2
            && (-8 as int) % (3 as int) == 1
            && (-8 as int) % (-3 as int) == 1;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn compute_only_euclidean_div_mod_small_boundaries() {
    trust_vc::assert_by_compute!(
        (1 as int) / (2 as int) == 0
            && (1 as int) / (-2 as int) == 0
            && (-1 as int) / (2 as int) == -1
            && (-1 as int) / (-2 as int) == 1
            && (1 as int) % (2 as int) == 1
            && (1 as int) % (-2 as int) == 1
            && (-1 as int) % (2 as int) == 1
            && (-1 as int) % (-2 as int) == 1;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn compute_only_euclidean_div_mod_counterexample() {
    trust_vc::assert_by_compute!(
        (-8 as int) / (3 as int) == -2;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn compute_only_euclidean_div_mod_small_boundary_counterexample() {
    trust_vc::assert_by_compute!(
        (-1 as int) / (2 as int) == 0;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn compute_only_recursive_spec_function() {
    trust_vc::assert_by_compute!(fib_compute(6) == 8; compute_only);
}

#[trust_vc::ensures(true)]
fn fn_calls_upstream_nested_compute_only() {
    trust_vc::assert_by_compute!(sum_compute(20u64) == 20u64; compute_only);
    trust_vc::assert_by_compute!(sum_compute(10u64) == 10u64; compute_only);
    trust_vc::assert_by_compute!(sum_compute(0u64) == 0u64; compute_only);
    trust_vc::assert_by_compute!(
        {
            let x: int = 22 as int;
            let z = fn_call_g_compute(x);
            !!!z
        };
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn depth_tracking_deep_but_finite_compute_only() {
    trust_vc::assert_by_compute!(count_down_compute(20u64) == 0u64; compute_only);
}

#[trust_vc::ensures(true)]
fn const_in_another_module_compute_only() {
    trust_vc::assert_by_compute!(assert_by_compute_const_module::BIN_HUGE == 12u64; compute_only);
}

#[trust_vc::ensures(true)]
fn fn_calls_upstream_nested_counterexample() {
    trust_vc::assert_by_compute!(sum_compute(4u64) == 5u64; compute_only);
}

#[trust_vc::ensures(true)]
fn depth_tracking_deep_but_finite_counterexample() {
    trust_vc::assert_by_compute!(count_down_compute(4u64) == 1u64; compute_only);
}
