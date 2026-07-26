// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::HashMap;

#[cfg(test)]
mod theory_contracts_tests {
    use super::*;

    #[cfg(test)]
    mod euf_tests {
        use super::*;

        fn terms(ids: &[u32]) -> Vec<EufTermId> {
            ids.iter().map(|&id| EufTermId(id)).collect()
        }

        fn eq(a: u32, b: u32) -> Equality {
            Equality {
                lhs: EufTermId(a),
                rhs: EufTermId(b),
            }
        }

        // -----------------------------------------------------------------------
        // EUF: basic propagation
        // -----------------------------------------------------------------------

        #[test]
        fn test_euf_empty_equalities_consistent() {
            let euf = ReferenceEuf::new();
            let t = terms(&[0, 1, 2]);
            let result = euf.propagate_equality(&t, &[]);
            assert!(matches!(result, EufResult::Consistent { .. }));
            assert!(validate_euf_postcondition(&t, &[], &[], &result));
        }

        #[test]
        fn test_euf_single_equality_consistent() {
            let euf = ReferenceEuf::new();
            let t = terms(&[0, 1]);
            let eqs = vec![eq(0, 1)];
            let result = euf.propagate_equality(&t, &eqs);
            assert!(matches!(result, EufResult::Consistent { .. }));
            assert!(validate_euf_postcondition(&t, &eqs, &[], &result));
        }

        #[test]
        fn test_euf_transitivity_derives_equality() {
            let euf = ReferenceEuf::new();
            let t = terms(&[0, 1, 2]);
            let eqs = vec![eq(0, 1), eq(1, 2)];
            let result = euf.propagate_equality(&t, &eqs);
            match &result {
                EufResult::Consistent { derived } => {
                    // a=b and b=c should derive a=c.
                    assert!(
                        derived.iter().any(|e| {
                            (e.lhs == EufTermId(0) && e.rhs == EufTermId(2))
                                || (e.lhs == EufTermId(2) && e.rhs == EufTermId(0))
                        }),
                        "transitivity should derive 0=2, got: {derived:?}"
                    );
                }
                _ => panic!("expected Consistent"),
            }
            assert!(validate_euf_postcondition(&t, &eqs, &[], &result));
        }

        #[test]
        fn test_euf_congruence_propagation() {
            let mut euf = ReferenceEuf::new();
            // f(a) = c, f(b) = d
            euf.add_function_app(FunctionApp {
                func_id: 1,
                args: vec![EufTermId(0)],
                result: EufTermId(2),
            });
            euf.add_function_app(FunctionApp {
                func_id: 1,
                args: vec![EufTermId(1)],
                result: EufTermId(3),
            });

            let t = terms(&[0, 1, 2, 3]);
            // Assert a = b.
            let eqs = vec![eq(0, 1)];
            let result = euf.propagate_equality(&t, &eqs);
            match &result {
                EufResult::Consistent { derived } => {
                    // a=b and f(a)=c, f(b)=d should derive c=d.
                    assert!(
                        derived.iter().any(|e| {
                            (e.lhs == EufTermId(2) && e.rhs == EufTermId(3))
                                || (e.lhs == EufTermId(3) && e.rhs == EufTermId(2))
                        }),
                        "congruence should derive f(a)=f(b), got: {derived:?}"
                    );
                }
                _ => panic!("expected Consistent"),
            }
            assert!(validate_euf_postcondition(
                &t,
                &eqs,
                &euf.function_apps,
                &result,
            ));
        }

        #[test]
        fn test_euf_contradiction_detected() {
            let mut euf = ReferenceEuf::new();
            euf.add_disequality(eq(0, 1));
            let t = terms(&[0, 1]);
            let eqs = vec![eq(0, 1)];
            let result = euf.propagate_equality(&t, &eqs);
            assert!(matches!(result, EufResult::Contradiction { .. }));
            assert!(validate_euf_postcondition(&t, &eqs, &[], &result));
        }

        #[test]
        fn test_euf_transitive_contradiction() {
            let mut euf = ReferenceEuf::new();
            euf.add_disequality(eq(0, 2)); // assert a != c
            let t = terms(&[0, 1, 2]);
            let eqs = vec![eq(0, 1), eq(1, 2)]; // a=b, b=c => a=c contradiction
            let result = euf.propagate_equality(&t, &eqs);
            assert!(matches!(result, EufResult::Contradiction { .. }));
        }

        #[test]
        fn test_euf_congruence_contradiction() {
            let mut euf = ReferenceEuf::new();
            // f(a) = c, f(b) = d, assert c != d
            euf.add_function_app(FunctionApp {
                func_id: 1,
                args: vec![EufTermId(0)],
                result: EufTermId(2),
            });
            euf.add_function_app(FunctionApp {
                func_id: 1,
                args: vec![EufTermId(1)],
                result: EufTermId(3),
            });
            euf.add_disequality(eq(2, 3));

            let t = terms(&[0, 1, 2, 3]);
            let eqs = vec![eq(0, 1)]; // a=b => f(a)=f(b) => c=d contradiction
            let result = euf.propagate_equality(&t, &eqs);
            assert!(matches!(result, EufResult::Contradiction { .. }));
        }

        #[test]
        fn test_euf_multi_arg_congruence() {
            let mut euf = ReferenceEuf::new();
            // g(a, b) = e, g(c, d) = f
            euf.add_function_app(FunctionApp {
                func_id: 2,
                args: vec![EufTermId(0), EufTermId(1)],
                result: EufTermId(4),
            });
            euf.add_function_app(FunctionApp {
                func_id: 2,
                args: vec![EufTermId(2), EufTermId(3)],
                result: EufTermId(5),
            });

            let t = terms(&[0, 1, 2, 3, 4, 5]);
            let eqs = vec![eq(0, 2), eq(1, 3)]; // a=c, b=d => g(a,b)=g(c,d) => e=f
            let result = euf.propagate_equality(&t, &eqs);
            match &result {
                EufResult::Consistent { derived } => {
                    assert!(
                        derived.iter().any(|e| {
                            (e.lhs == EufTermId(4) && e.rhs == EufTermId(5))
                                || (e.lhs == EufTermId(5) && e.rhs == EufTermId(4))
                        }),
                        "multi-arg congruence should derive e=f, got: {derived:?}"
                    );
                }
                _ => panic!("expected Consistent"),
            }
        }

        #[test]
        fn test_euf_no_congruence_different_functions() {
            let mut euf = ReferenceEuf::new();
            // f(a) = c, g(b) = d — different function IDs, no congruence.
            euf.add_function_app(FunctionApp {
                func_id: 1,
                args: vec![EufTermId(0)],
                result: EufTermId(2),
            });
            euf.add_function_app(FunctionApp {
                func_id: 2,
                args: vec![EufTermId(1)],
                result: EufTermId(3),
            });

            let t = terms(&[0, 1, 2, 3]);
            let eqs = vec![eq(0, 1)];
            let result = euf.propagate_equality(&t, &eqs);
            match &result {
                EufResult::Consistent { derived } => {
                    // Should NOT derive c=d (different functions).
                    assert!(
                        !derived.iter().any(|e| {
                            (e.lhs == EufTermId(2) && e.rhs == EufTermId(3))
                                || (e.lhs == EufTermId(3) && e.rhs == EufTermId(2))
                        }),
                        "different functions should not trigger congruence"
                    );
                }
                _ => panic!("expected Consistent"),
            }
        }

        #[test]
        fn test_euf_postcondition_rejects_incomplete_congruence() {
            // Fabricate a result that is missing a congruence closure step.
            let apps = vec![
                FunctionApp {
                    func_id: 1,
                    args: vec![EufTermId(0)],
                    result: EufTermId(2),
                },
                FunctionApp {
                    func_id: 1,
                    args: vec![EufTermId(1)],
                    result: EufTermId(3),
                },
            ];
            let t = terms(&[0, 1, 2, 3]);
            let eqs = vec![eq(0, 1)];
            // Derived is empty — missing c=d from congruence.
            let bogus = EufResult::Consistent { derived: vec![] };
            assert!(!validate_euf_postcondition(&t, &eqs, &apps, &bogus));
        }
    }

    #[cfg(test)]
    mod bv_tests {
        use super::*;

        fn bv() -> ReferenceBv {
            ReferenceBv::new()
        }

        // -----------------------------------------------------------------------
        // BV: basic operations
        // -----------------------------------------------------------------------

        #[test]
        fn test_bv_add_no_overflow() {
            let result = bv().evaluate_bv_op(BvOp::Add, 3, 4, 8);
            assert_eq!(result, 7);
            assert!(validate_bv_postcondition(BvOp::Add, 3, 4, 8, result));
        }

        #[test]
        fn test_bv_add_with_wrap() {
            let result = bv().evaluate_bv_op(BvOp::Add, 200, 100, 8);
            assert_eq!(result, 44); // (200 + 100) % 256 = 44
            assert!(validate_bv_postcondition(BvOp::Add, 200, 100, 8, result));
        }

        #[test]
        fn test_bv_sub_no_underflow() {
            let result = bv().evaluate_bv_op(BvOp::Sub, 10, 3, 8);
            assert_eq!(result, 7);
            assert!(validate_bv_postcondition(BvOp::Sub, 10, 3, 8, result));
        }

        #[test]
        fn test_bv_sub_with_wrap() {
            let result = bv().evaluate_bv_op(BvOp::Sub, 3, 10, 8);
            assert_eq!(result, 249); // (3 - 10) mod 256 = 249
            assert!(validate_bv_postcondition(BvOp::Sub, 3, 10, 8, result));
        }

        #[test]
        fn test_bv_mul_fits_in_width() {
            let result = bv().evaluate_bv_op(BvOp::Mul, 5, 6, 8);
            assert_eq!(result, 30);
            assert!(validate_bv_postcondition(BvOp::Mul, 5, 6, 8, result));
        }

        #[test]
        fn test_bv_mul_wraps() {
            let result = bv().evaluate_bv_op(BvOp::Mul, 20, 20, 8);
            assert_eq!(result, 144); // (400) % 256 = 144
            assert!(validate_bv_postcondition(BvOp::Mul, 20, 20, 8, result));
        }

        #[test]
        fn test_bv_udiv_normal() {
            let result = bv().evaluate_bv_op(BvOp::UDiv, 10, 3, 8);
            assert_eq!(result, 3);
            assert!(validate_bv_postcondition(BvOp::UDiv, 10, 3, 8, result));
        }

        #[test]
        fn test_bv_udiv_by_zero_is_all_ones() {
            let result = bv().evaluate_bv_op(BvOp::UDiv, 42, 0, 8);
            assert_eq!(result, 255); // SMT-LIB: bvudiv by 0 = all-ones
            assert!(validate_bv_postcondition(BvOp::UDiv, 42, 0, 8, result));
        }

        #[test]
        fn test_bv_shl_within_width() {
            let result = bv().evaluate_bv_op(BvOp::Shl, 1, 3, 8);
            assert_eq!(result, 8);
            assert!(validate_bv_postcondition(BvOp::Shl, 1, 3, 8, result));
        }

        #[test]
        fn test_bv_shl_overflow_is_zero() {
            let result = bv().evaluate_bv_op(BvOp::Shl, 0xFF, 8, 8);
            assert_eq!(result, 0); // shift >= width => 0
            assert!(validate_bv_postcondition(BvOp::Shl, 0xFF, 8, 8, result));
        }

        #[test]
        fn test_bv_lshr_within_width() {
            let result = bv().evaluate_bv_op(BvOp::LShr, 0x80, 3, 8);
            assert_eq!(result, 16); // 128 >> 3 = 16
            assert!(validate_bv_postcondition(BvOp::LShr, 0x80, 3, 8, result));
        }

        #[test]
        fn test_bv_lshr_overflow_is_zero() {
            let result = bv().evaluate_bv_op(BvOp::LShr, 0xFF, 8, 8);
            assert_eq!(result, 0);
            assert!(validate_bv_postcondition(BvOp::LShr, 0xFF, 8, 8, result));
        }

        #[test]
        fn test_bv_ashr_positive_value() {
            let result = bv().evaluate_bv_op(BvOp::AShr, 0x40, 2, 8);
            assert_eq!(result, 16); // 64 >> 2 = 16 (positive, sign bit 0)
            assert!(validate_bv_postcondition(BvOp::AShr, 0x40, 2, 8, result));
        }

        #[test]
        fn test_bv_ashr_negative_fills_ones() {
            // 0x80 = 128 = -128 in 8-bit signed. AShr by 2 = -32 = 0xE0.
            let result = bv().evaluate_bv_op(BvOp::AShr, 0x80, 2, 8);
            assert_eq!(result, 0xE0);
            assert!(validate_bv_postcondition(BvOp::AShr, 0x80, 2, 8, result));
        }

        #[test]
        fn test_bv_ashr_overflow_negative_is_all_ones() {
            let result = bv().evaluate_bv_op(BvOp::AShr, 0x80, 8, 8);
            assert_eq!(result, 0xFF); // negative => all ones
            assert!(validate_bv_postcondition(BvOp::AShr, 0x80, 8, 8, result));
        }

        #[test]
        fn test_bv_ashr_overflow_positive_is_zero() {
            let result = bv().evaluate_bv_op(BvOp::AShr, 0x40, 8, 8);
            assert_eq!(result, 0); // positive => 0
            assert!(validate_bv_postcondition(BvOp::AShr, 0x40, 8, 8, result));
        }

        #[test]
        fn test_bv_sign_ext_positive_preserves() {
            // 0x05 in 4 bits (0101) sign-extended by 4 bits -> 0x05 in 8 bits.
            let result = bv().evaluate_bv_op(BvOp::SignExt, 0x05, 4, 4);
            assert!(validate_bv_postcondition(BvOp::SignExt, 0x05, 4, 4, result));
            assert!(!sign_bit_set(result, 8)); // Still positive.
            assert_eq!(result, 0x05);
        }

        #[test]
        fn test_bv_sign_ext_negative_extends_ones() {
            // 0x08 in 4 bits (1000) = -8 signed. Sign-extend by 4 -> 0xF8.
            let result = bv().evaluate_bv_op(BvOp::SignExt, 0x08, 4, 4);
            assert!(validate_bv_postcondition(BvOp::SignExt, 0x08, 4, 4, result));
            assert!(sign_bit_set(result, 8)); // Negative preserved.
            assert_eq!(result, 0xF8);
        }

        #[test]
        fn test_bv_postcondition_rejects_oversized_result() {
            // Result of 256 does not fit in 8-bit width.
            assert!(!validate_bv_postcondition(BvOp::Add, 0, 0, 8, 256));
        }

        #[test]
        fn test_bv_postcondition_rejects_nonzero_shift_overflow() {
            // Shift by >= width should yield 0 for logical shifts.
            assert!(!validate_bv_postcondition(BvOp::Shl, 1, 8, 8, 1));
        }
    }

    #[cfg(test)]
    mod lra_tests {
        use super::*;

        fn constraint(terms: Vec<(i64, u32)>, cmp: CmpKind, bound: i64) -> LinearConstraint {
            LinearConstraint {
                terms: terms
                    .into_iter()
                    .map(|(c, v)| (Rational::from_int(c), v))
                    .collect(),
                cmp,
                bound: Rational::from_int(bound),
            }
        }

        // -----------------------------------------------------------------------
        // LRA: feasibility
        // -----------------------------------------------------------------------

        #[test]
        fn test_lra_trivially_feasible_empty() {
            let lra = ReferenceLra::new();
            let result = lra.check_feasibility(&[]);
            assert!(matches!(result, LraResult::Feasible { .. }));
            assert!(validate_lra_postcondition(&[], &result));
        }

        #[test]
        fn test_lra_single_le_constraint_zero_satisfies() {
            let lra = ReferenceLra::new();
            let cs = vec![constraint(vec![(1, 0)], CmpKind::Le, 10)];
            let result = lra.check_feasibility(&cs);
            assert!(matches!(result, LraResult::Feasible { .. }));
            assert!(validate_lra_postcondition(&cs, &result));
        }

        #[test]
        fn test_lra_single_ge_constraint_zero_satisfies() {
            let lra = ReferenceLra::new();
            let cs = vec![constraint(vec![(1, 0)], CmpKind::Ge, -5)];
            let result = lra.check_feasibility(&cs);
            assert!(matches!(result, LraResult::Feasible { .. }));
            assert!(validate_lra_postcondition(&cs, &result));
        }

        #[test]
        fn test_lra_equality_constraint_zero_satisfies() {
            let lra = ReferenceLra::new();
            let cs = vec![constraint(vec![(1, 0)], CmpKind::Eq, 0)];
            let result = lra.check_feasibility(&cs);
            assert!(matches!(result, LraResult::Feasible { .. }));
            assert!(validate_lra_postcondition(&cs, &result));
        }

        #[test]
        fn test_lra_contradictory_bounds_infeasible() {
            let lra = ReferenceLra::new();
            // x >= 5 and x <= 3 — infeasible.
            let cs = vec![
                constraint(vec![(1, 0)], CmpKind::Ge, 5),
                constraint(vec![(1, 0)], CmpKind::Le, 3),
            ];
            let result = lra.check_feasibility(&cs);
            assert!(matches!(result, LraResult::Infeasible { .. }));
            assert!(validate_lra_postcondition(&cs, &result));
        }

        #[test]
        fn test_lra_feasible_assignment_satisfies_all() {
            let lra = ReferenceLra::new();
            // x <= 10 and x >= 0 — zero satisfies both.
            let cs = vec![
                constraint(vec![(1, 0)], CmpKind::Le, 10),
                constraint(vec![(1, 0)], CmpKind::Ge, 0),
            ];
            let result = lra.check_feasibility(&cs);
            if let LraResult::Feasible { ref assignment } = result {
                for c in &cs {
                    assert!(ReferenceLra::satisfies(c, assignment));
                }
            } else {
                panic!("expected Feasible");
            }
            assert!(validate_lra_postcondition(&cs, &result));
        }

        #[test]
        fn test_lra_farkas_certificate_length_matches() {
            let lra = ReferenceLra::new();
            let cs = vec![
                constraint(vec![(1, 0)], CmpKind::Ge, 10),
                constraint(vec![(1, 0)], CmpKind::Le, 5),
            ];
            let result = lra.check_feasibility(&cs);
            if let LraResult::Infeasible {
                ref farkas_coefficients,
            } = result
            {
                assert_eq!(farkas_coefficients.len(), cs.len());
            } else {
                panic!("expected Infeasible");
            }
        }

        #[test]
        fn test_lra_farkas_coefficients_nonnegative() {
            let lra = ReferenceLra::new();
            let cs = vec![
                constraint(vec![(1, 0)], CmpKind::Ge, 10),
                constraint(vec![(1, 0)], CmpKind::Le, 5),
            ];
            let result = lra.check_feasibility(&cs);
            if let LraResult::Infeasible {
                ref farkas_coefficients,
            } = result
            {
                for coeff in farkas_coefficients {
                    assert!(
                        !coeff.is_negative(),
                        "Farkas coefficient must be non-negative, got: {coeff:?}"
                    );
                }
            } else {
                panic!("expected Infeasible");
            }
        }

        #[test]
        fn test_lra_postcondition_rejects_wrong_farkas_length() {
            let cs = vec![
                constraint(vec![(1, 0)], CmpKind::Ge, 10),
                constraint(vec![(1, 0)], CmpKind::Le, 5),
            ];
            let bogus = LraResult::Infeasible {
                farkas_coefficients: vec![Rational::from_int(1)], // Too short.
            };
            assert!(!validate_lra_postcondition(&cs, &bogus));
        }

        #[test]
        fn test_lra_postcondition_rejects_negative_farkas() {
            let cs = vec![constraint(vec![(1, 0)], CmpKind::Ge, 10)];
            let bogus = LraResult::Infeasible {
                farkas_coefficients: vec![Rational::from_int(-1)], // Negative!
            };
            assert!(!validate_lra_postcondition(&cs, &bogus));
        }

        #[test]
        fn test_lra_postcondition_rejects_unsatisfied_assignment() {
            let cs = vec![constraint(vec![(1, 0)], CmpKind::Ge, 10)];
            let mut bad_assignment = HashMap::new();
            bad_assignment.insert(0, Rational::from_int(5)); // 5 < 10, violates x >= 10
            let bogus = LraResult::Feasible {
                assignment: bad_assignment,
            };
            assert!(!validate_lra_postcondition(&cs, &bogus));
        }

        #[test]
        fn test_rational_arithmetic() {
            let a = Rational::new(1, 2);
            let b = Rational::new(1, 3);
            let sum = a.add(b);
            // 1/2 + 1/3 = 5/6
            assert_eq!(sum.num, 5);
            assert_eq!(sum.den, 6);
        }
    }

    #[cfg(test)]
    mod nia_tests {
        use super::*;

        fn nl_constraint(terms: Vec<(i64, Vec<u32>)>, cmp: CmpKind, bound: i64) -> NlConstraint {
            NlConstraint {
                terms: terms
                    .into_iter()
                    .map(|(coeff, vars)| NlTerm { coeff, vars })
                    .collect(),
                cmp,
                bound,
            }
        }

        // -----------------------------------------------------------------------
        // NIA: basic checking
        // -----------------------------------------------------------------------

        #[test]
        fn test_nia_trivially_satisfiable_empty() {
            let nia = ReferenceNia::new();
            let result = nia.check_nonlinear(&[]);
            assert!(matches!(result, NiaResult::Satisfiable { .. }));
            assert!(validate_nia_postcondition(&[], &HashMap::new(), &result));
        }

        #[test]
        fn test_nia_linear_constraint_zero_satisfies() {
            let nia = ReferenceNia::new();
            // 2*x <= 10 — x=0 satisfies.
            let cs = vec![nl_constraint(vec![(2, vec![0])], CmpKind::Le, 10)];
            let result = nia.check_nonlinear(&cs);
            assert!(matches!(result, NiaResult::Satisfiable { .. }));
            assert!(validate_nia_postcondition(&cs, &HashMap::new(), &result));
        }

        #[test]
        fn test_nia_quadratic_constraint_zero_satisfies() {
            let nia = ReferenceNia::new();
            // x^2 <= 100 — x=0 satisfies.
            let cs = vec![nl_constraint(vec![(1, vec![0, 0])], CmpKind::Le, 100)];
            let result = nia.check_nonlinear(&cs);
            assert!(matches!(result, NiaResult::Satisfiable { .. }));
            assert!(validate_nia_postcondition(&cs, &HashMap::new(), &result));
        }

        #[test]
        fn test_nia_cross_product_constraint() {
            let nia = ReferenceNia::new();
            // x * y >= 0 — x=0, y=0 satisfies.
            let cs = vec![nl_constraint(vec![(1, vec![0, 1])], CmpKind::Ge, 0)];
            let result = nia.check_nonlinear(&cs);
            assert!(matches!(result, NiaResult::Satisfiable { .. }));
            assert!(validate_nia_postcondition(&cs, &HashMap::new(), &result));
        }

        #[test]
        fn test_nia_interval_detects_infeasibility() {
            let mut nia = ReferenceNia::new();
            nia.set_bound(0, Interval::new(5, 10)); // x in [5, 10]
                                                    // x^2 <= 20 — min x^2 = 25, so infeasible.
            let cs = vec![nl_constraint(vec![(1, vec![0, 0])], CmpKind::Le, 20)];
            let result = nia.check_nonlinear(&cs);
            assert!(matches!(result, NiaResult::Unsatisfiable { .. }));
            assert!(validate_nia_postcondition(&cs, &nia.bounds, &result));
        }

        #[test]
        fn test_nia_model_satisfies_all_constraints() {
            let nia = ReferenceNia::new();
            // x + y = 0, x - y = 0 — x=0, y=0 satisfies.
            let cs = vec![
                nl_constraint(vec![(1, vec![0]), (1, vec![1])], CmpKind::Eq, 0),
                nl_constraint(vec![(1, vec![0]), (-1, vec![1])], CmpKind::Eq, 0),
            ];
            let result = nia.check_nonlinear(&cs);
            if let NiaResult::Satisfiable { ref model } = result {
                for c in &cs {
                    assert!(ReferenceNia::satisfies(c, model));
                }
            } else {
                panic!("expected Satisfiable");
            }
        }

        #[test]
        fn test_nia_enumeration_finds_solution() {
            let mut nia = ReferenceNia::new();
            nia.set_bound(0, Interval::new(1, 5));
            // x^2 = 9 — x=3 is the solution.
            let cs = vec![nl_constraint(vec![(1, vec![0, 0])], CmpKind::Eq, 9)];
            let result = nia.check_nonlinear(&cs);
            match &result {
                NiaResult::Satisfiable { model } => {
                    assert_eq!(model.get(&0), Some(&3));
                }
                _ => panic!("expected Satisfiable with x=3"),
            }
            assert!(validate_nia_postcondition(&cs, &nia.bounds, &result));
        }

        #[test]
        fn test_nia_postcondition_rejects_bad_model() {
            let cs = vec![nl_constraint(vec![(1, vec![0])], CmpKind::Ge, 10)];
            let mut bad_model = HashMap::new();
            bad_model.insert(0, 5i64); // 5 < 10, violates x >= 10
            let bogus = NiaResult::Satisfiable { model: bad_model };
            assert!(!validate_nia_postcondition(&cs, &HashMap::new(), &bogus));
        }

        #[test]
        fn test_nia_postcondition_rejects_invalid_conflict_index() {
            let cs = vec![nl_constraint(vec![(1, vec![0])], CmpKind::Ge, 10)];
            let bogus = NiaResult::Unsatisfiable {
                conflict: vec![5], // Index 5 is out of range.
            };
            assert!(!validate_nia_postcondition(&cs, &HashMap::new(), &bogus));
        }

        #[test]
        fn test_nia_postcondition_rejects_empty_conflict() {
            let cs = vec![nl_constraint(vec![(1, vec![0])], CmpKind::Ge, 10)];
            let bogus = NiaResult::Unsatisfiable {
                conflict: vec![], // Empty conflict is invalid.
            };
            assert!(!validate_nia_postcondition(&cs, &HashMap::new(), &bogus));
        }

        #[test]
        fn test_nia_unknown_is_always_valid() {
            let cs = vec![nl_constraint(vec![(1, vec![0, 0])], CmpKind::Eq, 7)];
            assert!(validate_nia_postcondition(
                &cs,
                &HashMap::new(),
                &NiaResult::Unknown,
            ));
        }

        #[test]
        fn test_interval_intersection() {
            let a = Interval::new(1, 10);
            let b = Interval::new(5, 15);
            let c = a.intersect(b);
            assert_eq!(c.lo, 5);
            assert_eq!(c.hi, 10);
        }

        #[test]
        fn test_interval_multiplication_mixed_signs() {
            let a = Interval::new(-3, 2);
            let b = Interval::new(-1, 4);
            let c = a.mul(b);
            // Products: 3, -12, -2, 8. Min=-12, Max=8.
            assert_eq!(c.lo, -12);
            assert_eq!(c.hi, 8);
        }

        #[test]
        fn test_interval_soundness_basic() {
            let mut bounds = HashMap::new();
            bounds.insert(0, Interval::new(1, 5));
            let mut model = HashMap::new();
            model.insert(0, 3i64);
            // Monomial: 2 * x, with x=3, interval = [2, 10].
            assert!(validate_interval_soundness(&bounds, &[0], 2, &model));
        }

        #[test]
        fn test_nia_model_respects_bounds() {
            let mut nia = ReferenceNia::new();
            nia.set_bound(0, Interval::new(0, 5));
            let cs = vec![nl_constraint(vec![(1, vec![0])], CmpKind::Ge, 3)];
            let result = nia.check_nonlinear(&cs);
            if let NiaResult::Satisfiable { ref model } = result {
                if let Some(&val) = model.get(&0) {
                    assert!(
                        nia.bounds.get(&0).unwrap().contains(val),
                        "model value {val} should be within bounds"
                    );
                }
            }
            assert!(validate_nia_postcondition(&cs, &nia.bounds, &result));
        }
    }
}
