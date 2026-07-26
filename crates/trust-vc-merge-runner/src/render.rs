// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Renders a `MergeBundle` into an executable SMT-LIB2 script.
//!
//! The rendered script declares variables, asserts assumptions, negates
//! the conjunction of assertions, and issues `(check-sat)` + `(get-model)`.

use trust_vc_merge_contract::{MergeBundle, SortMeta, VarDecl};

use crate::error::RunnerError;

/// Converts a `SortMeta` to its SMT-LIB2 sort string.
fn sort_to_smt(sort: &SortMeta, context: &str) -> Result<String, RunnerError> {
    match sort {
        SortMeta::Bool => Ok("Bool".to_string()),
        SortMeta::MathInt => Ok("Int".to_string()),
        SortMeta::Real => Ok("Real".to_string()),
        SortMeta::BitVector { width, .. } => Ok(format!("(_ BitVec {width})")),
        SortMeta::FloatingPoint {
            exponent_bits,
            significand_bits,
        } => Ok(format!(
            "(_ FloatingPoint {exponent_bits} {significand_bits})"
        )),
        SortMeta::Seq { elem } => {
            let inner = sort_to_smt(elem, context)?;
            Ok(format!("(Seq {inner})"))
        }
        SortMeta::Set { elem } => {
            let inner = sort_to_smt(elem, context)?;
            Ok(format!("(Array {inner} Bool)"))
        }
        SortMeta::Map { key, value } => {
            let k = sort_to_smt(key, context)?;
            let v = sort_to_smt(value, context)?;
            Ok(format!("(Array {k} {v})"))
        }
        SortMeta::Array { index, element } => {
            let i = sort_to_smt(index, context)?;
            let e = sort_to_smt(element, context)?;
            Ok(format!("(Array {i} {e})"))
        }
        SortMeta::Opaque { name } => Ok(name.clone()),
        other => Err(RunnerError::UnsupportedSort {
            context: context.to_string(),
            sort_desc: format!("{other:?}"),
        }),
    }
}

/// Renders bound variable list for `forall`: `(n Int) (m Bool)`.
fn render_bound_vars(vars: &[VarDecl], context: &str) -> Result<String, RunnerError> {
    let mut parts = Vec::with_capacity(vars.len());
    for var in vars {
        let sort = sort_to_smt(var.sort(), &format!("{context} bound var `{}`", var.name()))?;
        parts.push(format!("({} {sort})", var.name()));
    }
    Ok(parts.join(" "))
}

/// Renders `(declare-fun ...)` for each v4 function declaration.
fn render_func_decls(bundle: &MergeBundle) -> Result<String, RunnerError> {
    let mut out = String::new();
    for decl in bundle.func_decls() {
        let mut param_sorts = Vec::with_capacity(decl.param_sorts().len());
        for (i, sort) in decl.param_sorts().iter().enumerate() {
            param_sorts.push(sort_to_smt(
                sort,
                &format!("func_decl `{}` param[{i}]", decl.name()),
            )?);
        }
        let ret = sort_to_smt(
            decl.return_sort(),
            &format!("func_decl `{}` return", decl.name()),
        )?;
        out.push_str(&format!(
            "(declare-fun {} ({}) {ret})\n",
            decl.name(),
            param_sorts.join(" ")
        ));
    }
    Ok(out)
}

/// Renders fuel axioms as `(assert (forall (...) (! expr :pattern (trigger))))`.
fn render_fuel_axioms(bundle: &MergeBundle) -> Result<String, RunnerError> {
    let mut out = String::new();
    for axiom in bundle.fuel_axioms() {
        let bound = render_bound_vars(axiom.bound_vars(), axiom.function_name())?;
        out.push_str(&format!(
            "(assert (forall ({bound}) (! {} :pattern ({}))))\n",
            axiom.axiom_expr().expr(),
            axiom.trigger_pattern().expr()
        ));
    }
    Ok(out)
}

/// Renders broadcast lemmas as quantified assertions with guard and triggers.
fn render_broadcast_lemmas(bundle: &MergeBundle) -> Result<String, RunnerError> {
    let mut out = String::new();
    for lemma in bundle.broadcast_lemmas() {
        let bound = render_bound_vars(lemma.bound_vars(), lemma.name())?;
        let body = match lemma.guard_expr() {
            Some(guard) => format!("(=> {} {})", guard.expr(), lemma.body_expr().expr()),
            None => lemma.body_expr().expr().to_string(),
        };
        let mut pattern_clauses = String::new();
        for group in lemma.trigger_groups() {
            let terms: String = group.iter().map(|t| t.expr()).collect::<Vec<_>>().join(" ");
            pattern_clauses.push_str(&format!(" :pattern ({terms})"));
        }
        out.push_str(&format!(
            "(assert (forall ({bound}) (! {body}{pattern_clauses})))\n"
        ));
    }
    Ok(out)
}

/// Renders the full SMT-LIB2 script for the executable core of the bundle.
///
/// The script structure:
/// 1. `(set-logic ALL)` — let ay auto-detect the needed theories
/// 2. `(declare-const ...)` for each variable
/// 3. `(declare-fun ...)` for each function declaration (v4)
/// 4. `(assert (forall ...))` for each fuel axiom (v4)
/// 5. `(assert (forall ...))` for each broadcast lemma (v4)
/// 6. `(assert ...)` for each assumption
/// 7. `(assert (not (and ...)))` for the negated conjunction of assertions
/// 8. `(check-sat)`
/// 9. `(get-model)`
pub(crate) fn render_bundle_to_smt(bundle: &MergeBundle) -> Result<String, RunnerError> {
    let mut script = String::with_capacity(1024);

    script.push_str("(set-logic ALL)\n");

    for var in bundle.variables() {
        let sort = sort_to_smt(var.sort(), &format!("variable `{}`", var.name()))?;
        script.push_str(&format!("(declare-const {} {})\n", var.name(), sort));
    }

    // v4 proof metadata: function declarations, fuel axioms, broadcast lemmas
    script.push_str(&render_func_decls(bundle)?);
    script.push_str(&render_fuel_axioms(bundle)?);
    script.push_str(&render_broadcast_lemmas(bundle)?);

    for (i, assumption) in bundle.assumptions().iter().enumerate() {
        validate_bool_sort(assumption.sort(), &format!("assumption[{i}]"))?;
        script.push_str(&format!("(assert {})\n", assumption.expr()));
    }

    if bundle.assertions().is_empty() {
        script.push_str("; no assertions — trivially verified\n");
        script.push_str("(assert false)\n");
    } else if bundle.assertions().len() == 1 {
        validate_bool_sort(bundle.assertions()[0].sort(), "assertion[0]")?;
        script.push_str(&format!(
            "(assert (not {}))\n",
            bundle.assertions()[0].expr()
        ));
    } else {
        let mut conjunction = String::from("(and");
        for (i, assertion) in bundle.assertions().iter().enumerate() {
            validate_bool_sort(assertion.sort(), &format!("assertion[{i}]"))?;
            conjunction.push(' ');
            conjunction.push_str(assertion.expr());
        }
        conjunction.push(')');
        script.push_str(&format!("(assert (not {conjunction}))\n"));
    }

    script.push_str("(check-sat)\n");
    script.push_str("(get-model)\n");

    Ok(script)
}

fn validate_bool_sort(sort: &SortMeta, context: &str) -> Result<(), RunnerError> {
    if *sort != SortMeta::Bool {
        return Err(RunnerError::UnsupportedSort {
            context: context.to_string(),
            sort_desc: format!("expected Bool, got {sort:?}"),
        });
    }
    Ok(())
}

/// Validates that the bundle's executable fields use only supported sorts.
pub(crate) fn validate_bundle_sorts(bundle: &MergeBundle) -> Result<(), RunnerError> {
    for var in bundle.variables() {
        sort_to_smt(var.sort(), &format!("variable `{}`", var.name()))?;
    }
    for (i, assumption) in bundle.assumptions().iter().enumerate() {
        validate_bool_sort(assumption.sort(), &format!("assumption[{i}]"))?;
    }
    for (i, assertion) in bundle.assertions().iter().enumerate() {
        validate_bool_sort(assertion.sort(), &format!("assertion[{i}]"))?;
    }
    // v4: validate sorts in function declarations and quantifier bound variables
    for decl in bundle.func_decls() {
        for (i, sort) in decl.param_sorts().iter().enumerate() {
            sort_to_smt(sort, &format!("func_decl `{}` param[{i}]", decl.name()))?;
        }
        sort_to_smt(
            decl.return_sort(),
            &format!("func_decl `{}` return", decl.name()),
        )?;
    }
    for axiom in bundle.fuel_axioms() {
        for var in axiom.bound_vars() {
            sort_to_smt(
                var.sort(),
                &format!(
                    "fuel_axiom `{}` bound var `{}`",
                    axiom.function_name(),
                    var.name()
                ),
            )?;
        }
    }
    for lemma in bundle.broadcast_lemmas() {
        for var in lemma.bound_vars() {
            sort_to_smt(
                var.sort(),
                &format!(
                    "broadcast_lemma `{}` bound var `{}`",
                    lemma.name(),
                    var.name()
                ),
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_merge_contract::{
        BroadcastLemmaMeta, FuelAxiomMeta, FuncDeclMeta, TypedExpr, VarDecl,
    };

    fn minimal_bundle() -> MergeBundle {
        MergeBundle::new("test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new("x", SortMeta::MathInt)])
            .with_assumptions(vec![TypedExpr::new("(> x 0)", SortMeta::Bool)])
            .with_assertions(vec![TypedExpr::new("(>= x 1)", SortMeta::Bool)])
    }

    #[test]
    fn test_render_minimal_bundle() {
        let script = render_bundle_to_smt(&minimal_bundle()).unwrap();
        assert!(script.contains("(set-logic ALL)"));
        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (> x 0))"));
        assert!(script.contains("(assert (not (>= x 1)))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-model)"));
    }

    #[test]
    fn test_render_bitvector_sort() {
        let bundle = MergeBundle::new("bv_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "v",
                SortMeta::BitVector {
                    width: 32,
                    signed: false,
                },
            )])
            .with_assertions(vec![TypedExpr::new("(bvuge v (_ bv0 32))", SortMeta::Bool)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(script.contains("(declare-const v (_ BitVec 32))"));
    }

    #[test]
    fn test_render_multiple_assertions_conjunct() {
        let bundle = MergeBundle::new("multi")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new("x", SortMeta::MathInt)])
            .with_assertions(vec![
                TypedExpr::new("(> x 0)", SortMeta::Bool),
                TypedExpr::new("(< x 100)", SortMeta::Bool),
            ]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(script.contains("(assert (not (and (> x 0) (< x 100))))"));
    }

    #[test]
    fn test_render_func_decl() {
        let bundle = minimal_bundle().with_func_decls(vec![FuncDeclMeta::new(
            "factorial",
            vec!["n".to_string()],
            vec![SortMeta::MathInt],
            SortMeta::MathInt,
        )
        .with_recursive(true)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-fun factorial (Int) Int)"),
            "should contain declare-fun: {script}"
        );
    }

    #[test]
    fn test_render_fuel_axiom() {
        let bundle = minimal_bundle()
            .with_func_decls(vec![FuncDeclMeta::new(
                "f",
                vec!["n".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )])
            .with_fuel_axioms(vec![FuelAxiomMeta::new(
                "f",
                vec![VarDecl::new("n", SortMeta::MathInt)],
                TypedExpr::new("(= (f n) (* n 2))", SortMeta::Bool),
                TypedExpr::new("(f n)", SortMeta::MathInt),
            )]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(assert (forall ((n Int)) (! (= (f n) (* n 2)) :pattern ((f n)))))"),
            "should contain fuel axiom forall: {script}"
        );
    }

    #[test]
    fn test_render_broadcast_lemma_with_guard() {
        let bundle = minimal_bundle()
            .with_func_decls(vec![FuncDeclMeta::new(
                "g",
                vec!["n".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )])
            .with_broadcast_lemmas(vec![BroadcastLemmaMeta::new(
                "lemma_g_nonneg",
                vec![VarDecl::new("n", SortMeta::MathInt)],
                TypedExpr::new("(>= (g n) 0)", SortMeta::Bool),
                vec![vec![TypedExpr::new("(g n)", SortMeta::MathInt)]],
            )
            .with_guard_expr(TypedExpr::new("(>= n 0)", SortMeta::Bool))]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains(
                "(assert (forall ((n Int)) (! (=> (>= n 0) (>= (g n) 0)) :pattern ((g n)))))"
            ),
            "should contain broadcast lemma with guard: {script}"
        );
    }

    #[test]
    fn test_render_v4_ordering() {
        let bundle = minimal_bundle().with_func_decls(vec![FuncDeclMeta::new(
            "h",
            vec!["a".to_string()],
            vec![SortMeta::MathInt],
            SortMeta::MathInt,
        )]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        let decl_pos = script.find("(declare-fun h").unwrap();
        let const_pos = script.find("(declare-const x").unwrap();
        let assume_pos = script.find("(assert (> x 0))").unwrap();
        assert!(
            const_pos < decl_pos,
            "declare-const should come before declare-fun"
        );
        assert!(
            decl_pos < assume_pos,
            "declare-fun should come before assumptions"
        );
    }

    #[test]
    fn test_render_floating_point_sort() {
        let bundle = MergeBundle::new("fp_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "f",
                SortMeta::FloatingPoint {
                    exponent_bits: 8,
                    significand_bits: 24,
                },
            )])
            .with_assertions(vec![TypedExpr::new(
                "(fp.gt f (fp #b0 #x00 #b00000000000000000000000))",
                SortMeta::Bool,
            )]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const f (_ FloatingPoint 8 24))"),
            "should render Float32 sort: {script}"
        );
    }

    #[test]
    fn test_render_seq_sort() {
        let bundle = MergeBundle::new("seq_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "s",
                SortMeta::Seq {
                    elem: Box::new(SortMeta::MathInt),
                },
            )])
            .with_assertions(vec![TypedExpr::new("(> (seq.len s) 0)", SortMeta::Bool)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const s (Seq Int))"),
            "should render Seq(Int) sort: {script}"
        );
    }

    #[test]
    fn test_render_set_sort() {
        let bundle = MergeBundle::new("set_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "t",
                SortMeta::Set {
                    elem: Box::new(SortMeta::MathInt),
                },
            )])
            .with_assertions(vec![TypedExpr::new("(select t 42)", SortMeta::Bool)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const t (Array Int Bool))"),
            "should render Set(Int) as Array(Int, Bool): {script}"
        );
    }

    #[test]
    fn test_render_map_sort() {
        let bundle = MergeBundle::new("map_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "m",
                SortMeta::Map {
                    key: Box::new(SortMeta::MathInt),
                    value: Box::new(SortMeta::Bool),
                },
            )])
            .with_assertions(vec![TypedExpr::new("(select m 0)", SortMeta::Bool)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const m (Array Int Bool))"),
            "should render Map(Int, Bool) as Array(Int, Bool): {script}"
        );
    }

    #[test]
    fn test_render_array_sort() {
        let bundle = MergeBundle::new("arr_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "a",
                SortMeta::Array {
                    index: Box::new(SortMeta::BitVector {
                        width: 64,
                        signed: false,
                    }),
                    element: Box::new(SortMeta::BitVector {
                        width: 32,
                        signed: false,
                    }),
                },
            )])
            .with_assertions(vec![TypedExpr::new(
                "(= (select a (_ bv0 64)) (_ bv0 32))",
                SortMeta::Bool,
            )]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const a (Array (_ BitVec 64) (_ BitVec 32)))"),
            "should render Array(BV64, BV32): {script}"
        );
    }

    #[test]
    fn test_render_opaque_sort() {
        let bundle = MergeBundle::new("opaque_test")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new(
                "o",
                SortMeta::Opaque {
                    name: "MyType".to_string(),
                },
            )])
            .with_assertions(vec![TypedExpr::new("(= o o)", SortMeta::Bool)]);
        let script = render_bundle_to_smt(&bundle).unwrap();
        assert!(
            script.contains("(declare-const o MyType)"),
            "should render Opaque as its name: {script}"
        );
    }
}
