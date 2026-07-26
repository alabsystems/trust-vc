// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Public VerificationPipeline coverage for recursive datatype decreases and
//! multiset surface operations.

use trust_vc::decreases;
use trust_vc_core::ir::TrustVcType;
use trust_vc_core::ir_builder;
use trust_vc_core::vc::{ObligationKind, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;
use trust_vc_types::{List, Tree};

mod common;

fn dt_size_var(name: &str, ty: &str) -> trust_vc_core::ir::TrustVcExpr {
    ir_builder::fn_call(
        "__trust_vc_dt_size",
        vec![ir_builder::var(name, TrustVcType::parse_or_opaque(ty))],
        TrustVcType::MathInt,
    )
}

fn register_recursive_arg(name: &str, ty: &str) {
    verify_macro::collect_variable(name.to_string(), ty.to_string());
}

fn assume_smaller_dt_size(
    smaller_name: &str,
    smaller_ty: &str,
    larger_name: &str,
    larger_ty: &str,
) {
    let condition =
        format!("__trust_vc_dt_size({smaller_name}) < __trust_vc_dt_size({larger_name})");
    verify_macro::collect_obligation_expr(
        ObligationKind::Assume,
        format!("{smaller_name}_size_lt_{larger_name}"),
        condition,
        ir_builder::lt(
            dt_size_var(smaller_name, smaller_ty),
            dt_size_var(larger_name, larger_ty),
        ),
        None,
    );
}

#[test]
fn test_decreases_list_positive_uses_recursive_dt_size() {
    let _ = common::verify_should_pass(|| {
        #[decreases(list)]
        fn shrink_list(list: List<i32>) {
            match list {
                List::Nil => {}
                List::Cons(_, tail) => {
                    let smaller = *tail;
                    register_recursive_arg("smaller", "List<i32>");
                    assume_smaller_dt_size("smaller", "List<i32>", "list", "List<i32>");
                    shrink_list(smaller);
                }
            }
        }

        let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
        shrink_list(list);
    });
}

#[test]
fn test_decreases_list_obligation_contains_dt_size_builtin() {
    common::with_clean_verification(|| {
        #[decreases(list)]
        fn no_list_progress(list: List<i32>, recurse_once: bool) {
            if recurse_once {
                let same = list.clone();
                register_recursive_arg("same", "List<i32>");
                no_list_progress(same, false);
            }
        }

        let list = List::Cons(1, Box::new(List::Nil));
        no_list_progress(list, true);

        let pipeline = VerificationPipeline::collect_from_macros();
        let decrease_conditions: Vec<_> = pipeline
            .context()
            .obligations()
            .iter()
            .filter(|obligation| matches!(obligation.kind(), ObligationKind::MeasureDecreases))
            .map(|obligation| obligation.condition().to_string())
            .collect();
        assert!(
            decrease_conditions
                .iter()
                .any(|condition| condition.contains("__trust_vc_dt_size(")),
            "expected recursive datatype decreases obligation to use __trust_vc_dt_size, got: {:?}",
            decrease_conditions
        );
    });
}

#[test]
fn test_decreases_list_negative_same_argument_fails() {
    let _ = common::verify_should_fail(|| {
        #[decreases(list)]
        fn no_list_progress(list: List<i32>, recurse_once: bool) {
            if recurse_once {
                let same = list.clone();
                register_recursive_arg("same", "List<i32>");
                no_list_progress(same, false);
            }
        }

        let list = List::Cons(1, Box::new(List::Nil));
        no_list_progress(list, true);
    });
}

#[test]
fn test_decreases_tree_positive_uses_recursive_dt_size() {
    let _ = common::verify_should_pass(|| {
        #[decreases(tree)]
        fn shrink_tree(tree: Tree<i32>) {
            match tree {
                Tree::Leaf(_) => {}
                Tree::Branch(left, _) => {
                    let smaller = *left;
                    register_recursive_arg("smaller", "Tree<i32>");
                    assume_smaller_dt_size("smaller", "Tree<i32>", "tree", "Tree<i32>");
                    shrink_tree(smaller);
                }
            }
        }

        let tree = Tree::Branch(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
        shrink_tree(tree);
    });
}

#[test]
fn test_multiset_public_surface_positive_verifies_through_pipeline() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("ms", "Multiset<i32>");
        ctx.push_assume("bounded", "ms.count(5) < 100");
        ctx.push_assert("inserted", "ms.insert(5).contains(5)");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "multiset insert/count public surface should verify through VerificationPipeline, got: {:?}",
            result
        );
    });
}

#[test]
fn test_multiset_choose_public_surface_verifies_when_nonempty() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("ms", "Multiset<i32>");
        ctx.push_assume("nonempty", "ms.len() != 0");
        ctx.push_assert("choose_member", "ms.contains(ms.choose())");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "multiset choose should verify membership through VerificationPipeline when nonempty, got: {:?}",
            result
        );
    });
}

#[test]
fn test_multiset_public_surface_union_uses_unbounded_nat_counts_through_pipeline() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("ms1", "Multiset<i32>");
        ctx.declare_var_parsed("ms2", "Multiset<i32>");
        ctx.push_assume("ms1_max", "ms1.count(5) == 18446744073709551615");
        ctx.push_assume("ms2_one", "ms2.count(5) == 1");
        ctx.push_assert(
            "unbounded_sum",
            "ms1.union(ms2).count(5) == 18446744073709551616",
        );

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "multiset union should use unbounded Nat counts through VerificationPipeline, got: {:?}",
            result
        );
    });
}
