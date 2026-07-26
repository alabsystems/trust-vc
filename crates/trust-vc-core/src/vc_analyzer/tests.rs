// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// -- Helpers --

fn var(name: &str) -> VcExpression {
    VcExpression::Variable(name.into())
}

fn lit(b: bool) -> VcExpression {
    VcExpression::Literal(b)
}

fn int(v: i128) -> VcExpression {
    VcExpression::IntConst(v)
}

fn and(es: Vec<VcExpression>) -> VcExpression {
    VcExpression::And(es)
}

fn or(es: Vec<VcExpression>) -> VcExpression {
    VcExpression::Or(es)
}

fn not(e: VcExpression) -> VcExpression {
    VcExpression::Not(Box::new(e))
}

fn implies(a: VcExpression, b: VcExpression) -> VcExpression {
    VcExpression::Implies(Box::new(a), Box::new(b))
}

fn forall(vars: &[&str], body: VcExpression) -> VcExpression {
    VcExpression::Forall(vars.iter().map(|s| (*s).into()).collect(), Box::new(body))
}

fn exists(vars: &[&str], body: VcExpression) -> VcExpression {
    VcExpression::Exists(vars.iter().map(|s| (*s).into()).collect(), Box::new(body))
}

fn arith(op: ArithOp, es: Vec<VcExpression>) -> VcExpression {
    VcExpression::Arith(op, es)
}

fn bvop(op: BvOp, width: u32, es: Vec<VcExpression>) -> VcExpression {
    VcExpression::BvOp(op, width, es)
}

fn array_op(op: ArrayOp, es: Vec<VcExpression>) -> VcExpression {
    VcExpression::ArrayOp(op, es)
}

fn uf(name: &str, args: Vec<VcExpression>) -> VcExpression {
    VcExpression::UfApp(name.into(), args)
}

fn cmp(op: CompareOp, a: VcExpression, b: VcExpression) -> VcExpression {
    VcExpression::Compare(op, Box::new(a), Box::new(b))
}

fn ite(c: VcExpression, t: VcExpression, e: VcExpression) -> VcExpression {
    VcExpression::Ite(Box::new(c), Box::new(t), Box::new(e))
}

// -----------------------------------------------------------------------
// VcExpression basic methods
// -----------------------------------------------------------------------

#[test]
fn test_depth_literal_is_one() {
    assert_eq!(lit(true).depth(), 1);
    assert_eq!(int(42).depth(), 1);
    assert_eq!(var("x").depth(), 1);
}

#[test]
fn test_depth_nested_not() {
    let e = not(not(not(lit(true))));
    assert_eq!(e.depth(), 4);
}

#[test]
fn test_depth_and_chain() {
    let e = and(vec![var("a"), var("b"), and(vec![var("c"), var("d")])]);
    // And(a, b, And(c, d)): depth 1 + max(1, 1, 1+1) = 3
    assert_eq!(e.depth(), 3);
}

#[test]
fn test_node_count_literal() {
    assert_eq!(lit(false).node_count(), 1);
}

#[test]
fn test_node_count_compound() {
    let e = and(vec![var("a"), not(var("b"))]);
    // And(1) + Variable(1) + Not(1) + Variable(1) = 4
    assert_eq!(e.node_count(), 4);
}

#[test]
fn test_variable_names_simple() {
    let e = and(vec![var("x"), var("y"), var("x")]);
    let names = e.variable_names();
    assert_eq!(names.len(), 2);
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
fn test_variable_names_excludes_bound() {
    let e = forall(&["x"], cmp(CompareOp::Gt, var("x"), var("y")));
    let names = e.variable_names();
    assert_eq!(names.len(), 1);
    assert!(names.contains("y"));
    assert!(!names.contains("x"));
}

#[test]
fn test_contains_theory_arithmetic() {
    let e = arith(ArithOp::Add, vec![var("x"), int(1)]);
    assert!(e.contains_theory(Theory::Arithmetic));
    assert!(!e.contains_theory(Theory::BitVector));
}

#[test]
fn test_contains_theory_bitvector() {
    let e = bvop(BvOp::BvAnd, 32, vec![var("a"), var("b")]);
    assert!(e.contains_theory(Theory::BitVector));
    assert!(!e.contains_theory(Theory::Array));
}

#[test]
fn test_contains_theory_quantifier() {
    let e = forall(&["x"], lit(true));
    assert!(e.contains_theory(Theory::Quantifier));
    assert!(!e.contains_theory(Theory::Arithmetic));
}

#[test]
fn test_contains_theory_array() {
    let e = array_op(ArrayOp::Select, vec![var("arr"), int(0)]);
    assert!(e.contains_theory(Theory::Array));
}

#[test]
fn test_contains_theory_uf() {
    let e = uf("f", vec![var("x")]);
    assert!(e.contains_theory(Theory::UninterpretedFunction));
}

// -----------------------------------------------------------------------
// Theory profile
// -----------------------------------------------------------------------

#[test]
fn test_theory_profile_pure_boolean() {
    let e = and(vec![var("a"), or(vec![var("b"), not(var("c"))])]);
    let tp = TheoryProfile::from_expr(&e);
    assert_eq!(tp.total_nodes, e.node_count());
    assert!(tp.boolean_weight > 0.0);
    assert!((tp.arithmetic_weight - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_theory_profile_arithmetic_dominant() {
    let e = arith(
        ArithOp::Add,
        vec![
            arith(ArithOp::Mul, vec![var("x"), var("y")]),
            arith(ArithOp::Sub, vec![var("z"), int(1)]),
        ],
    );
    let tp = TheoryProfile::from_expr(&e);
    assert!(tp.arithmetic_weight > tp.boolean_weight);
}

#[test]
fn test_theory_profile_dominant_theory() {
    let e = bvop(
        BvOp::BvAdd,
        32,
        vec![bvop(BvOp::BvMul, 32, vec![var("a"), var("b")]), var("c")],
    );
    let tp = TheoryProfile::from_expr(&e);
    assert_eq!(tp.dominant_theory(), Theory::BitVector);
}

// -----------------------------------------------------------------------
// Quantifier profile
// -----------------------------------------------------------------------

#[test]
fn test_quantifier_profile_no_quantifiers() {
    let e = and(vec![var("a"), var("b")]);
    let qp = QuantifierProfile::from_expr(&e);
    assert_eq!(qp.count, 0);
    assert_eq!(qp.max_depth, 0);
}

#[test]
fn test_quantifier_profile_single_forall() {
    let e = forall(&["x", "y"], cmp(CompareOp::Gt, var("x"), var("y")));
    let qp = QuantifierProfile::from_expr(&e);
    assert_eq!(qp.count, 1);
    assert_eq!(qp.forall_count, 1);
    assert_eq!(qp.exists_count, 0);
    assert_eq!(qp.max_depth, 1);
    assert_eq!(qp.bound_variable_count, 2);
    assert_eq!(qp.alternation_count, 0);
}

#[test]
fn test_quantifier_profile_nested_alternation() {
    // forall x. exists y. x > y
    let e = forall(
        &["x"],
        exists(&["y"], cmp(CompareOp::Gt, var("x"), var("y"))),
    );
    let qp = QuantifierProfile::from_expr(&e);
    assert_eq!(qp.count, 2);
    assert_eq!(qp.forall_count, 1);
    assert_eq!(qp.exists_count, 1);
    assert_eq!(qp.max_depth, 2);
    assert_eq!(qp.alternation_count, 1);
}

#[test]
fn test_quantifier_profile_same_kind_nesting() {
    // forall x. forall y. P(x, y)
    let e = forall(&["x"], forall(&["y"], uf("P", vec![var("x"), var("y")])));
    let qp = QuantifierProfile::from_expr(&e);
    assert_eq!(qp.count, 2);
    assert_eq!(qp.alternation_count, 0);
    assert_eq!(qp.max_depth, 2);
}

// -----------------------------------------------------------------------
// Arithmetic profile
// -----------------------------------------------------------------------

#[test]
fn test_arith_profile_no_arith() {
    let e = and(vec![var("a"), var("b")]);
    let ap = ArithProfile::from_expr(&e);
    assert!(!ap.has_linear);
    assert!(!ap.has_nonlinear);
    assert!(!ap.has_integer);
}

#[test]
fn test_arith_profile_linear() {
    let e = arith(ArithOp::Add, vec![var("x"), int(1)]);
    let ap = ArithProfile::from_expr(&e);
    assert!(ap.has_linear);
    assert!(!ap.has_nonlinear);
    assert!(ap.has_integer);
    assert_eq!(ap.op_count, 1);
}

#[test]
fn test_arith_profile_nonlinear_mul() {
    let e = arith(ArithOp::Mul, vec![var("x"), var("y")]);
    let ap = ArithProfile::from_expr(&e);
    assert!(ap.has_nonlinear);
}

#[test]
fn test_arith_profile_linear_const_mul() {
    // 3 * x is linear.
    let e = arith(ArithOp::Mul, vec![int(3), var("x")]);
    let ap = ArithProfile::from_expr(&e);
    assert!(ap.has_linear);
    assert!(!ap.has_nonlinear);
}

#[test]
fn test_arith_profile_division() {
    let e = arith(ArithOp::Div, vec![var("x"), var("y")]);
    let ap = ArithProfile::from_expr(&e);
    assert!(ap.has_division);
    assert!(ap.has_nonlinear);
    assert!(ap.has_real);
}

#[test]
fn test_arith_profile_modulus() {
    let e = arith(ArithOp::Mod, vec![var("x"), int(3)]);
    let ap = ArithProfile::from_expr(&e);
    assert!(ap.has_modulus);
    assert!(ap.has_nonlinear);
}

// -----------------------------------------------------------------------
// Bitvector profile
// -----------------------------------------------------------------------

#[test]
fn test_bv_profile_empty() {
    let e = var("x");
    let bp = BvProfile::from_expr(&e);
    assert_eq!(bp.op_count, 0);
    assert_eq!(bp.max_width, 0);
}

#[test]
fn test_bv_profile_basic() {
    let e = bvop(BvOp::BvAnd, 32, vec![var("a"), var("b")]);
    let bp = BvProfile::from_expr(&e);
    assert_eq!(bp.op_count, 1);
    assert_eq!(bp.max_width, 32);
    assert!(bp.widths_used.contains(&32));
    assert!(!bp.has_shift);
}

#[test]
fn test_bv_profile_shift_and_rotate() {
    let e = and(vec![
        bvop(BvOp::Shl, 64, vec![var("x"), int(1)]),
        bvop(BvOp::RotateRight, 8, vec![var("y"), int(2)]),
    ]);
    let bp = BvProfile::from_expr(&e);
    assert_eq!(bp.op_count, 2);
    assert!(bp.has_shift);
    assert!(bp.has_rotate);
    assert_eq!(bp.max_width, 64);
    assert!(bp.widths_used.contains(&64));
    assert!(bp.widths_used.contains(&8));
}

#[test]
fn test_bv_profile_extract() {
    let e = bvop(BvOp::Extract, 16, vec![var("x")]);
    let bp = BvProfile::from_expr(&e);
    assert!(bp.has_extract);
}

// -----------------------------------------------------------------------
// VcStatistics
// -----------------------------------------------------------------------

#[test]
fn test_statistics_trivial() {
    let e = lit(true);
    let s = VcStatistics::compute(&e);
    assert_eq!(s.node_count, 1);
    assert_eq!(s.depth, 1);
    assert_eq!(s.variable_count, 0);
}

#[test]
fn test_statistics_compound() {
    let e = and(vec![
        cmp(CompareOp::Gt, var("x"), int(0)),
        forall(&["i"], arith(ArithOp::Add, vec![var("i"), int(1)])),
    ]);
    let s = VcStatistics::compute(&e);
    assert!(s.node_count > 1);
    assert_eq!(s.quantifier_count, 1);
    assert_eq!(s.arith_op_count, 1);
    // "x" is free; "i" is bound.
    assert_eq!(s.variable_count, 1);
}

// -----------------------------------------------------------------------
// Pattern detection
// -----------------------------------------------------------------------

#[test]
fn test_pattern_bounds_check() {
    // 0 <= x && x < len
    let e = and(vec![
        cmp(CompareOp::Ge, var("x"), int(0)),
        cmp(CompareOp::Lt, var("x"), var("len")),
    ]);
    let patterns = PatternDetector::detect(&e);
    assert!(patterns.iter().any(|p| p.name == "bounds_check"));
}

#[test]
fn test_pattern_overflow_guard() {
    // x <= 2147483647
    let e = cmp(CompareOp::Le, var("x"), int(2_147_483_647));
    let patterns = PatternDetector::detect(&e);
    assert!(patterns.iter().any(|p| p.name == "overflow_guard"));
}

#[test]
fn test_pattern_null_check_uf() {
    let e = uf("is_some", vec![var("opt")]);
    let patterns = PatternDetector::detect(&e);
    assert!(patterns.iter().any(|p| p.name == "null_check"));
}

#[test]
fn test_pattern_division_safety() {
    // implies(y != 0, x / y > 0)
    let e = implies(
        cmp(CompareOp::Ne, var("y"), int(0)),
        cmp(
            CompareOp::Gt,
            arith(ArithOp::Div, vec![var("x"), var("y")]),
            int(0),
        ),
    );
    let patterns = PatternDetector::detect(&e);
    assert!(patterns.iter().any(|p| p.name == "division_safety"));
}

#[test]
fn test_pattern_loop_invariant() {
    // forall i. (0 <= i && i < n) => arr[i] > 0
    let e = forall(
        &["i"],
        implies(
            and(vec![
                cmp(CompareOp::Ge, var("i"), int(0)),
                cmp(CompareOp::Lt, var("i"), var("n")),
            ]),
            cmp(
                CompareOp::Gt,
                array_op(ArrayOp::Select, vec![var("arr"), var("i")]),
                int(0),
            ),
        ),
    );
    let patterns = PatternDetector::detect(&e);
    assert!(patterns.iter().any(|p| p.name == "loop_invariant"));
}

#[test]
fn test_pattern_no_false_positive_on_single_compare() {
    let e = cmp(CompareOp::Gt, var("x"), int(5));
    let patterns = PatternDetector::detect(&e);
    assert!(!patterns.iter().any(|p| p.name == "bounds_check"));
}

// -----------------------------------------------------------------------
// Difficulty estimation
// -----------------------------------------------------------------------

#[test]
fn test_difficulty_trivial_literal() {
    let e = lit(true);
    let analysis = VcAnalysis::analyze(&e);
    let report = DifficultyEstimator::estimate(&analysis);
    assert_eq!(report.label, DifficultyLabel::Trivial);
    assert!(report.score < 5.0);
}

#[test]
fn test_difficulty_quantifier_heavy() {
    let e = forall(
        &["x"],
        forall(
            &["y"],
            exists(
                &["z"],
                cmp(
                    CompareOp::Eq,
                    arith(ArithOp::Add, vec![var("x"), var("y")]),
                    var("z"),
                ),
            ),
        ),
    );
    let analysis = VcAnalysis::analyze(&e);
    let report = DifficultyEstimator::estimate(&analysis);
    assert!(report.score > 20.0);
    assert!(report.factors.iter().any(|f| f.name == "quantifiers"));
    assert!(report
        .factors
        .iter()
        .any(|f| f.name == "quantifier_alternation"));
}

#[test]
fn test_difficulty_nonlinear_arithmetic() {
    let e = cmp(
        CompareOp::Gt,
        arith(ArithOp::Mul, vec![var("x"), var("y")]),
        int(0),
    );
    let analysis = VcAnalysis::analyze(&e);
    let report = DifficultyEstimator::estimate(&analysis);
    assert!(report
        .factors
        .iter()
        .any(|f| f.name == "nonlinear_arithmetic"));
}

#[test]
fn test_difficulty_recommendations_bv_wide() {
    let e = bvop(BvOp::BvAdd, 128, vec![var("a"), var("b")]);
    let analysis = VcAnalysis::analyze(&e);
    let report = DifficultyEstimator::estimate(&analysis);
    assert!(report
        .recommendations
        .iter()
        .any(|r| r.contains("BV-focused")));
}

// -----------------------------------------------------------------------
// Simplification
// -----------------------------------------------------------------------

#[test]
fn test_simplify_double_negation() {
    let e = not(not(var("x")));
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("x"));
    assert_eq!(stats.double_negations, 1);
}

#[test]
fn test_simplify_and_with_true() {
    let e = and(vec![lit(true), var("x"), lit(true)]);
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("x"));
    assert!(stats.trivial_bounds >= 2);
}

#[test]
fn test_simplify_and_with_false() {
    let e = and(vec![var("x"), lit(false), var("y")]);
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, lit(false));
}

#[test]
fn test_simplify_or_with_true() {
    let e = or(vec![var("x"), lit(true), var("y")]);
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, lit(true));
}

#[test]
fn test_simplify_or_with_false() {
    let e = or(vec![lit(false), var("x"), lit(false)]);
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("x"));
    assert!(stats.identity_eliminations >= 2);
}

#[test]
fn test_simplify_implies_true_antecedent() {
    let e = implies(lit(true), var("x"));
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("x"));
}

#[test]
fn test_simplify_implies_false_antecedent() {
    let e = implies(lit(false), var("x"));
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, lit(true));
}

#[test]
fn test_simplify_implies_true_consequent() {
    let e = implies(var("x"), lit(true));
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, lit(true));
}

#[test]
fn test_simplify_not_literal() {
    let e = not(lit(true));
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, lit(false));
    assert_eq!(stats.constant_folds, 1);
}

#[test]
fn test_simplify_ite_true_condition() {
    let e = ite(lit(true), var("a"), var("b"));
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("a"));
}

#[test]
fn test_simplify_ite_false_condition() {
    let e = ite(lit(false), var("a"), var("b"));
    let (result, _) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("b"));
}

#[test]
fn test_simplify_nested() {
    // not(not(and(true, or(false, x))))
    let e = not(not(and(vec![lit(true), or(vec![lit(false), var("x")])])));
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, var("x"));
    assert!(stats.total_reductions() >= 3);
}

#[test]
fn test_simplification_stats_reduction_ratio() {
    let e = and(vec![lit(true), lit(true), lit(true), var("x")]);
    let (_, stats) = VcSimplifier::simplify(&e);
    assert!(stats.reduction_ratio() > 0.0);
    assert!(stats.final_nodes < stats.original_nodes);
}

#[test]
fn test_simplification_stats_no_change() {
    let e = and(vec![var("a"), var("b")]);
    let (result, stats) = VcSimplifier::simplify(&e);
    assert_eq!(result, e);
    assert_eq!(stats.total_reductions(), 0);
    assert!((stats.reduction_ratio() - 0.0).abs() < f64::EPSILON);
}

// -----------------------------------------------------------------------
// Full analysis (VcAnalysis::analyze)
// -----------------------------------------------------------------------

#[test]
fn test_full_analysis_smoke() {
    let e = forall(
        &["i"],
        implies(
            and(vec![
                cmp(CompareOp::Ge, var("i"), int(0)),
                cmp(CompareOp::Lt, var("i"), var("n")),
            ]),
            cmp(
                CompareOp::Gt,
                array_op(ArrayOp::Select, vec![var("arr"), var("i")]),
                int(0),
            ),
        ),
    );
    let analysis = VcAnalysis::analyze(&e);
    assert_eq!(analysis.quantifier_profile.count, 1);
    assert!(analysis.statistics.array_op_count > 0);
    assert!(analysis.statistics.node_count > 5);
    assert!(analysis.patterns.iter().any(|p| p.name == "loop_invariant"));
}

#[test]
fn test_full_analysis_pure_bv() {
    let e = bvop(
        BvOp::Shl,
        64,
        vec![bvop(BvOp::BvAnd, 64, vec![var("x"), var("mask")]), int(4)],
    );
    let analysis = VcAnalysis::analyze(&e);
    assert_eq!(analysis.bv_profile.op_count, 2);
    assert!(analysis.bv_profile.has_shift);
    assert_eq!(analysis.bv_profile.max_width, 64);
    assert_eq!(analysis.quantifier_profile.count, 0);
}

// -----------------------------------------------------------------------
// Edge cases
// -----------------------------------------------------------------------

#[test]
fn test_empty_and() {
    let e = and(vec![]);
    assert_eq!(e.depth(), 1);
    assert_eq!(e.node_count(), 1);
}

#[test]
fn test_simplify_empty_and_to_true() {
    let e = and(vec![]);
    let (result, _) = VcSimplifier::simplify(&e);
    // And of nothing is vacuously true.
    assert_eq!(result, lit(true));
}

#[test]
fn test_simplify_empty_or_to_false() {
    let e = or(vec![]);
    let (result, _) = VcSimplifier::simplify(&e);
    // Or of nothing is vacuously false.
    assert_eq!(result, lit(false));
}

#[test]
fn test_simplification_stats_empty_expr() {
    let stats = SimplificationStats::default();
    assert_eq!(stats.total_reductions(), 0);
    assert!((stats.reduction_ratio() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_difficulty_label_thresholds() {
    assert_eq!(DifficultyLabel::from_score(0.0), DifficultyLabel::Trivial);
    assert_eq!(DifficultyLabel::from_score(4.9), DifficultyLabel::Trivial);
    assert_eq!(DifficultyLabel::from_score(5.0), DifficultyLabel::Easy);
    assert_eq!(DifficultyLabel::from_score(19.9), DifficultyLabel::Easy);
    assert_eq!(DifficultyLabel::from_score(50.0), DifficultyLabel::Hard);
    assert_eq!(
        DifficultyLabel::from_score(100.0),
        DifficultyLabel::VeryHard
    );
}
