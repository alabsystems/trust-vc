//! #2223 regressions: exists quantifier encoder path + MathInt Skolemization.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Gap 1: TrustVcExpr exists encoder path (zero coverage before #2223)
// ========================================================================

/// Exists encoding succeeds for a satisfiable existential.
/// exists |x: u32| x == 42
#[test]
fn test_exists_basic_encoding_succeeds() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser();

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 42,
                ty: TrustVcType::Uint { width: 32 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2223: exists encoding must succeed, got: {:?}",
        result.err()
    );
}

/// Exists with arithmetic in body: exists |x: i16| x + 1 == 0
/// Exercises int_mode coercion for exists path.
#[test]
fn test_exists_arithmetic_in_body() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser();

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 16 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 16 },
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 16 },
                }),
                ty: TrustVcType::Int { width: 16 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 16 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2223: exists with arithmetic must encode without sort mismatch, got: {:?}",
        result.err()
    );
}

/// Exists with multiple bound vars: exists |x: u8, y: u8| x + y == 100
#[test]
fn test_exists_multiple_bound_vars() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser();

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![
            ("x".to_string(), TrustVcType::Uint { width: 8 }),
            ("y".to_string(), TrustVcType::Uint { width: 8 }),
        ],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }),
                right: Box::new(TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }),
                ty: TrustVcType::Uint { width: 8 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 100,
                ty: TrustVcType::Uint { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2223: exists with multiple bound vars must encode, got: {:?}",
        result.err()
    );
}

/// Native-seq regression: non-Skolemized quantifiers must keep bound Seq<T>
/// sorts aligned with declared Seq<T> variables. Part of #2690.
#[cfg(feature = "native-seq")]
#[test]
fn test_exists_native_seq_bound_var_matches_declared_seq_sort() {
    let mut env = QuantifierTestEnv::new();
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let seq_sort = Sort::seq(Sort::bitvec(32));
    let seq_term = env.solver.declare_const("s", seq_sort.clone());
    let same_seq = env
        .solver
        .try_declare_fun(
            "same_seq",
            &[seq_sort.clone(), seq_sort.clone()],
            Sort::Bool,
        )
        .expect("same_seq should declare");
    env.variables.insert("s".to_string(), seq_term);
    env.var_types.insert("s".to_string(), seq_ty.clone());
    env.functions.insert("same_seq".to_string(), same_seq);

    let mut parser = env.parser();
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("t".to_string(), seq_ty.clone())],
        body: Box::new(TrustVcExpr::FnCall {
            name: "same_seq".to_string(),
            args: vec![
                TrustVcExpr::Var {
                    name: "t".to_string(),
                    ty: seq_ty.clone(),
                },
                TrustVcExpr::Var {
                    name: "s".to_string(),
                    ty: seq_ty,
                },
            ],
            return_ty: TrustVcType::Bool,
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    let term = result.unwrap_or_else(|err| {
        panic!(
            "#2690: native-seq exists over Seq<i32> should encode without Seq(Int)/Seq(BV32) sort drift: {err}"
        )
    });
    assert_eq!(
        env.solver.term_sort(term),
        Sort::Bool,
        "native-seq Seq equality quantifier should produce a Bool term"
    );
}

// ========================================================================
// Gap 2: MathInt bound vars must not use BV-sorted Skolemization
// ========================================================================

/// MathInt bound var in trigger-less forall with collection access must not
/// cause a sort mismatch. Before the fix, Skolemization created an Int-sorted
/// fresh var but collection access expected BV-sorted index (#2223).
///
/// Under native-seq, this test's manual setup (Array sort + BV64 length) is
/// incompatible with the native Seq encoding (Sort::Seq + Int length).
/// The quantifier handling being tested still works — only the test harness
/// setup needs different sorts. Part of #2680.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_mathint_bound_var_forall_no_sort_mismatch() {
    let mut env = QuantifierTestEnv::new();

    // Declare a Seq<i32> variable
    let seq_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let seq_term = env.solver.declare_const("s", seq_sort);
    env.variables.insert("s".to_string(), seq_term);
    env.var_types.insert(
        "s".to_string(),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    let len_term = env.solver.declare_const("s_len", Sort::bitvec(64));
    env.collection_lengths.insert("s".to_string(), len_term);

    let mut parser = env.parser();

    // forall |i: MathInt| s.index(i) >= 0
    // MathInt has no bit_width — must NOT Skolemize, must fall back to int_mode.
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".to_string(), TrustVcType::MathInt)],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Index {
                receiver: Box::new(TrustVcExpr::Var {
                    name: "s".to_string(),
                    ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
                }),
                index: Box::new(TrustVcExpr::Var {
                    name: "i".to_string(),
                    ty: TrustVcType::MathInt,
                }),
                receiver_name: Some("s".to_string()),
                elem_ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2223: MathInt bound var in forall with Seq access must not sort-mismatch, got: {:?}",
        result.err()
    );
}
