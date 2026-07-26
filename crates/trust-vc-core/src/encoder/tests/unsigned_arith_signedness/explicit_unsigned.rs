//! Direct unsigned IR tests: bvudiv/bvurem vs bvsdiv/bvsrem discrimination,
//! variable-by-literal signedness, signed control, and overflow checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from unsigned_arith_signedness/mod.rs (#2145).

use super::*;

/// DISCRIMINATING: u32 division with high-bit-set value must use bvudiv.
///
/// 0x8000_0000u32 / 2 = 0x4000_0000 (1073741824) with bvudiv.
/// With bvsdiv: 0x8000_0000 is interpreted as -2147483648, so -2147483648 / 2
/// = -1073741824 (0xC000_0000), which is WRONG for unsigned semantics.
///
/// If encode_arith incorrectly uses bvsdiv for unsigned types (#2070),
/// the solver will produce the wrong quotient and this test fails.
#[test]
fn test_ir_unsigned_div_high_bit_discriminates_bvudiv_vs_bvsdiv() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: 0x8000_0000u32 / 2u32
    let expr = unsigned_div_expr(unsigned_lit(0x8000_0000), unsigned_lit(2));
    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 division should encode");

    // Assert result == 0x4000_0000 (correct unsigned division)
    let expected = parser.solver.try_bv_const(0x4000_0000_i64, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "0x8000_0000u32 / 2 must equal 0x4000_0000 (bvudiv), not 0xC000_0000 (bvsdiv) (#2070)"
    );
}

/// DISCRIMINATING: u32 remainder with high-bit-set value must use bvurem.
///
/// 0x8000_0001u32 % 2 = 1 with bvurem (2147483649 % 2 = 1).
/// With bvsrem: 0x8000_0001 is -2147483647, and -2147483647 % 2 = -1
/// (0xFFFF_FFFF), which is WRONG for unsigned semantics.
#[test]
fn test_ir_unsigned_rem_high_bit_discriminates_bvurem_vs_bvsrem() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: 0x8000_0001u32 % 2u32
    let expr = unsigned_rem_expr(unsigned_lit(0x8000_0001), unsigned_lit(2));
    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 remainder should encode");

    // Assert result == 1 (correct unsigned remainder)
    let expected = parser.solver.try_bv_const(1, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "0x8000_0001u32 % 2 must equal 1 (bvurem), not 0xFFFFFFFF (bvsrem) (#2070)"
    );
}

/// DISCRIMINATING: u32 division with variable numerator and literal denominator.
///
/// This test catches the specific #2070 scenario where a u32 variable is
/// divided by an unsuffixed integer literal. `operands_are_unsigned(term_widths)`
/// returns false because the literal lacks a term_widths entry, even though
/// the IR node's ty field is Uint{32}.
///
/// For x = 0xFFFF_FFF0u32 (4294967280):
///   bvudiv: 4294967280 / 16 = 268435455 (0x0FFF_FFFF)
///   bvsdiv: -16 / 16 = -1 (0xFFFF_FFFF) — WRONG
#[test]
fn test_ir_unsigned_div_variable_by_literal_signedness() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: x / 16u32  (variable / literal)
    let expr = unsigned_div_expr(unsigned_var("x"), unsigned_lit(16));
    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 variable division should encode");

    // Set x = 0xFFFF_FFF0u32
    let x_val = parser
        .solver
        .try_bv_const(0xFFFF_FFF0_u32 as i64, 32)
        .unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // Assert result == 0x0FFF_FFFF (correct unsigned division)
    let expected = parser.solver.try_bv_const(0x0FFF_FFFF_i64, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "0xFFFF_FFF0u32 / 16 must equal 0x0FFFFFFF (bvudiv), not 0xFFFFFFFF (bvsdiv) (#2070)"
    );
}

/// NEGATIVE CONTROL: Signed division should NOT produce unsigned results.
///
/// Ensures that the fix for #2070 doesn't over-correct by making all
/// arithmetic unsigned. For signed i32, bvsdiv must still be used.
///
/// -16i32 / 4 = -4 (bvsdiv). With bvudiv, -16 (0xFFFF_FFF0) / 4 = 0x3FFF_FFFC.
#[test]
fn test_ir_signed_div_still_uses_bvsdiv() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Int { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: -16i32 / 4i32
    let expr = signed_div_expr(signed_lit(-16), signed_lit(4));
    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("i32 division should encode");

    // Assert result == -4 (correct signed division)
    let expected = parser.solver.try_bv_const(-4_i64, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "-16i32 / 4 must equal -4 (bvsdiv), not 0x3FFFFFFC (bvudiv) — signed must stay signed"
    );
}

/// DISCRIMINATING: Unsigned overflow check on addition must use unsigned semantics.
///
/// For u32: 0x7FFF_FFFF + 1 = 0x8000_0000 does NOT overflow u32 range.
/// But under signed i32, this IS overflow (MAX_I32 + 1). If signed overflow
/// checks are used for unsigned types, this will falsely report overflow.
#[test]
fn test_ir_unsigned_add_overflow_check_no_false_positive() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: x + 1u32 with overflow checks
    let add_expr = crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(unsigned_var("x")),
        right: Box::new(unsigned_lit(1)),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    };

    parser.overflow_checks.clear();
    parser
        .encode_trust_vc_expr(&add_expr)
        .expect("u32 addition should encode");

    // Set x = 0x7FFF_FFFF (i32::MAX). Not a u32 overflow (result = 0x8000_0000).
    let x_val = parser.solver.try_bv_const(0x7FFF_FFFF_i64, 32).unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // All overflow checks must be satisfiable (no overflow for u32 at this value)
    for (name, check) in &parser.overflow_checks {
        parser.solver.try_push().unwrap();
        parser.solver.try_assert_term(*check).unwrap();
        let sat = parser.solver.try_check_sat().unwrap();
        parser.solver.try_pop().unwrap();
        assert_eq!(
            sat,
            SolveResult::Sat,
            "u32 overflow check '{}' at x=0x7FFFFFFF: 0x7FFFFFFF + 1 = 0x80000000 is within \
             u32 range. False positive means signed overflow check is being used (#2070)",
            name
        );
    }
}

/// DISCRIMINATING: u32 unsigned remainder with variable and literal.
///
/// For x = 0x8000_0003u32 (2147483651):
///   bvurem: 2147483651 % 3 = 2
///   bvsrem: -2147483645 % 3 = -2 (0xFFFFFFFE)
#[test]
fn test_ir_unsigned_rem_variable_by_literal_signedness() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode: x % 3u32  (variable / literal)
    let expr = unsigned_rem_expr(unsigned_var("x"), unsigned_lit(3));
    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 variable remainder should encode");

    // Set x = 0x8000_0003u32
    let x_val = parser
        .solver
        .try_bv_const(0x8000_0003_u32 as i64, 32)
        .unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // Assert result == 2 (correct unsigned remainder: 2147483651 % 3 = 2)
    let expected = parser.solver.try_bv_const(2, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "0x8000_0003u32 % 3 must equal 2 (bvurem), not 0xFFFFFFFE (bvsrem) (#2070)"
    );
}
