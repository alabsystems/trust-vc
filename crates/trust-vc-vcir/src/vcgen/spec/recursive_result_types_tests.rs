//! Recursive helper return typing, including zero fuel and inactive paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::ops::Not;

use super::*;
use crate::ids::DefHash;
use crate::solve::{check, Limits, Verdict};
use crate::vcgen::query::{Hypothesis, Query, Source, Symbol};
use crate::vcgen::relevance::CallRole;
use crate::vcgen::term::ArithOp;

fn vocabulary(range: IntRange, when: Term) -> Tables {
    let id = FnId(DefHash::new(0, 1));
    let sig = SpecSig {
        owner: id,
        boxed_params: false,
        n_types: 0,
        params: vec![Shape::Leaf(LeafTy::Int(IntRange::Nat))],
        result: Shape::Leaf(LeafTy::Int(range)),
        outputs: vec![SpecOutput {
            name: "sf0".to_string(),
            leaf: LeafTy::Int(range),
        }],
        problem: None,
    };
    let (types, values, params) = definition_params(&sig);
    let krate = crate::VcCrate::new("native result bounds");
    let ctx = Ctx::new(&krate);
    let type_guard = parameter_types(&ctx, &sig, &types, &values).expect("native parameter types");
    let parameter = Term::var("a0", Sort::Int);
    let child = rf(Term::arith(ArithOp::Sub, parameter, Term::Int(1)));
    let body = if range == IntRange::Nat {
        Term::arith(ArithOp::Add, child, Term::Int(1))
    } else {
        clip(range, Term::arith(ArithOp::Div, child, Term::Int(2)))
    };
    let rec = RecDef {
        def: SpecDef {
            function: "rf0".to_string(),
            params,
            guard: Term::and([type_guard.clone(), when]),
            body,
        },
        spec_name: "sf0".to_string(),
        type_guard: type_guard.clone(),
        return_bounds: Some(LeafTy::Int(range).bounds()),
        return_predicate: None,
        cycle: 1,
        sort: Sort::Int,
    };
    let mut functions = vec![
        Function {
            name: "sf0".to_string(),
            params: vec![Sort::Int],
            ret: Sort::Int,
        },
        Function {
            name: "rf0".to_string(),
            params: vec![Sort::Int],
            ret: Sort::Int,
        },
    ];
    if range != IntRange::Nat {
        functions.push(Function {
            name: clip_oob_name(range),
            params: vec![Sort::Int],
            ret: Sort::Int,
        });
    }
    Tables {
        sigs: HashMap::from([(id, sig)]),
        defs: HashMap::new(),
        rec_defs: HashMap::from([(id, vec![rec])]),
        rec_names: HashMap::from([("rf0".to_string(), (id, 0))]),
        functions,
        families: HashMap::new(),
        ranged: HashMap::new(),
        typings: HashMap::new(),
    }
}

/// Unfold `count(n)` under `decreases n when n > 0`: its child at zero
/// fuel has no body equation but still has its result typing invariant.
fn query(range: IntRange, argument: i128, relevance: Term, goal: Term) -> Query {
    let when = Term::lt(Term::Int(0), Term::var("a0", Sort::Int));
    query_with_when(range, argument, relevance, goal, when)
}

fn query_with_when(
    range: IntRange,
    argument: i128,
    relevance: Term,
    goal: Term,
    when: Term,
) -> Query {
    let tables = vocabulary(range, when);
    let id = FnId(DefHash::new(0, 1));
    let definitions = HashMap::new();
    let role = |name: &str| {
        if name == "sf0" || name == "rf0" {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    };
    let mut analysis = Analysis::new(&role, &definitions, 100_000);
    let seeds = vec![(sf(Term::Int(argument)), relevance)];
    let unfoldable = HashMap::from([("sf0", (&tables.rec_defs[&id][0], 1))]);
    let facts = unfold(
        seeds,
        &unfoldable,
        &tables,
        &definitions,
        &mut analysis,
        &mut 100_000,
    )
    .expect("small unfolding");
    let resolved = analysis.namer.resolve(facts, 100_000);
    let hypotheses = resolved
        .facts
        .into_iter()
        .chain(resolved.definitions)
        .enumerate()
        .map(|(i, term)| Hypothesis {
            label: format!("h{i}"),
            source: Source::Axiom,
            term,
        })
        .collect();
    let mut symbols = resolved.symbols;
    symbols.push(Symbol {
        name: "active".to_string(),
        sort: Sort::Bool,
        display: "active".to_string(),
    });
    Query {
        architectures: None,
        bitvector: None,
        nominal_types: Vec::new(),
        symbols,
        functions: tables.functions,
        definitions: vec![],
        hypotheses,
        goal,
    }
}

fn sf(argument: Term) -> Term {
    Term::call("sf0", vec![argument], Sort::Int)
}

fn rf(argument: Term) -> Term {
    Term::call("rf0", vec![argument], Sort::Int)
}

fn assert_verdict(query: &Query, proved: bool) {
    let answer = check(query, "recursive_result_typing", &Limits::default());
    if proved {
        assert!(
            matches!(answer, Verdict::Proved { .. }),
            "{answer:?}\n{query}"
        );
    } else {
        assert!(
            matches!(answer, Verdict::Refuted { .. }),
            "{answer:?}\n{query}"
        );
    }
}

#[test]
fn natural_result_survives_zero_fuel_and_false_decreases_when() {
    for (bound, proved) in [(0, true), (1, false)] {
        let goal = Term::lt(Term::Int(bound), sf(Term::Int(1)));
        assert_verdict(&query(IntRange::Nat, 1, Term::Bool(true), goal), proved);
    }
}

#[test]
fn machine_result_keeps_its_upper_bound_at_zero_fuel() {
    for (bound, proved) in [(127, true), (126, false)] {
        let goal = Term::le(sf(Term::Int(1)), Term::Int(bound));
        assert_verdict(&query(IntRange::U(8), 1, Term::Bool(true), goal), proved);
    }
}

#[test]
fn helper_typing_does_not_escape_its_parameter_guard() {
    let goal = Term::le(Term::Int(0), rf(Term::Int(-1)));
    assert_verdict(&query(IntRange::Nat, -1, Term::Bool(true), goal), false);

    // A relevant, well-typed root can expose an ill-typed helper argument.
    // The helper's own parameter guard is still required at zero fuel.
    let goal = Term::le(Term::Int(0), rf(Term::Int(-1)));
    assert_verdict(
        &query_with_when(IntRange::Nat, 0, Term::Bool(true), goal, Term::Bool(true)),
        false,
    );
}

#[test]
fn helper_typing_does_not_escape_its_relevance_guard() {
    let active = Term::var("active", Sort::Bool);
    let bound = Term::le(Term::Int(0), rf(Term::Int(0)));
    for (condition, proved) in [(active.clone(), true), (active.clone().not(), false)] {
        let mut q = query(IntRange::Nat, 1, active.clone(), bound.clone());
        q.hypotheses.push(Hypothesis {
            label: "path".to_string(),
            source: Source::PathCondition,
            term: condition,
        });
        assert_verdict(&q, proved);
    }
    assert_verdict(&query(IntRange::Nat, 1, Term::Bool(false), bound), false);
}

#[test]
fn compiler_provenance_distinguishes_public_and_helper_typing() {
    use crate::{
        BinOp, Expr, ExprKind, FnAttrs, FnDecl, FnRole, LocalDecl, LocalId, LocalKind, Place,
        RecGroup, SpanId, Ty,
    };

    // The schema records the newly required compiler provenance fact.
    assert_eq!(crate::SCHEMA, "trust-vc.vcir@9");
    let id = FnId(DefHash::new(0, 1));
    let span = SpanId(0);
    let n = Expr::read(Place::local(LocalId(1)), Ty::nat(), span);
    let zero = Expr::int_lit(0, Ty::nat(), span);
    let cond = Expr::binary(BinOp::Eq, n.clone(), zero.clone(), Ty::Bool, span);
    let call = Expr::new(
        Ty::nat(),
        span,
        ExprKind::Call {
            callee: id,
            type_args: vec![],
            args: vec![zero.clone()],
        },
    );
    let body = Expr::new(
        Ty::nat(),
        span,
        ExprKind::If {
            cond: Box::new(cond),
            then_expr: Box::new(zero),
            else_expr: Box::new(call),
        },
    );
    for is_trait_method_impl in [false, true] {
        let local = |name: &str, kind| LocalDecl {
            name: name.to_string(),
            ty: Ty::nat(),
            mode: Mode::Spec,
            mutable: false,
            kind,
            span,
        };
        let mut krate = VcCrate::new("typing");
        krate.fns.push(FnDecl {
            id,
            name: "f".to_string(),
            span,
            mode: Mode::Spec,
            role: FnRole::Item,
            kind: Default::default(),
            type_params: vec![],
            locals: vec![
                local("result", LocalKind::Return),
                local("n", LocalKind::Param),
            ],
            params: vec![LocalId(1)],
            ret: LocalId(0),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![n.clone()],
            decreases_when: None,
            decreases_by: None,
            attrs: FnAttrs {
                is_trait_method_impl,
                ..FnAttrs::default()
            },
            body: Body::Spec(body.clone()),
        });
        krate.rec_groups.push(RecGroup {
            members: vec![(id, 1)],
        });
        assert!(crate::check_crate(&krate).is_empty());
        let ctx = Ctx::new(&krate);
        let tables = Tables::build(&ctx, &krate);
        assert_eq!(tables.ranged.get("sf0"), Some(&(Some(0), None)));
        assert_eq!(
            tables.rec_defs[&id][0].return_bounds,
            (!is_trait_method_impl).then_some((Some(0), None)),
        );
    }
}
