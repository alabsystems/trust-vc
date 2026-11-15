//! The one-goal query API (`trust_vc_core::query`), exercised through its
//! public surface only.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every positive case has a liar twin: the same query with the goal (or one
//! hypothesis) changed so the goal is no longer entailed. A twin must come
//! back `Refuted` (or, where the module documents it, `Unknown`), never
//! `Proved`.

use trust_vc_core::ir::{ArithOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType};
use trust_vc_core::query::{
    check, is_admitted_name, Definition, Function, Hypothesis, HypothesisSource, Limits, Query,
    Symbol, Verdict,
};
use trust_vc_core::UnknownCategory;

fn int() -> TrustVcType {
    TrustVcType::MathInt
}

fn boolean() -> TrustVcType {
    TrustVcType::Bool
}

fn nominal(name: &str) -> TrustVcType {
    TrustVcType::NamedCarrier(name.into())
}

#[test]
fn poly_values_do_not_collapse_or_double_as_type_arguments() {
    let p = var("p", TrustVcType::Poly);
    let q = var("q", TrustVcType::Poly);
    let mut query = Query::new("typed poly", cmp(CompareOp::Eq, p.clone(), p.clone()));
    query.symbols = vec![
        Symbol::new("p", TrustVcType::Poly),
        Symbol::new("q", TrustVcType::Poly),
    ];
    assert_proved(&check(&query, &Limits::default()));
    query.goal = cmp(CompareOp::Eq, p.clone(), q);
    assert_refuted(&check(&query, &Limits::default()));
    query.nominal_sorts = vec!["type".into()];
    query.symbols.push(Symbol::new("t", nominal("type")));
    query.goal = cmp(CompareOp::Eq, p, var("t", nominal("type")));
    assert!(matches!(
        check(&query, &Limits::default()),
        Verdict::Error { .. }
    ));
}

#[test]
fn poly_uf_congruence_preserves_type_and_decoration_arguments() {
    let call = |t: &str| TrustVcExpr::FnCall {
        name: "measure".into(),
        args: vec![
            var("d", nominal("dec")),
            var(t, nominal("type")),
            var("p", TrustVcType::Poly),
        ],
        return_ty: int(),
    };
    let mut query = Query::new(
        "complete generic ABI",
        cmp(CompareOp::Eq, call("t"), call("t")),
    );
    query.nominal_sorts = vec!["dec".into(), "type".into()];
    query.symbols = vec![
        Symbol::new("d", nominal("dec")),
        Symbol::new("t", nominal("type")),
        Symbol::new("u", nominal("type")),
        Symbol::new("p", TrustVcType::Poly),
    ];
    query.functions.push(Function {
        name: "measure".into(),
        params: vec![nominal("dec"), nominal("type"), TrustVcType::Poly],
        ret: int(),
    });
    assert_proved(&check(&query, &Limits::default()));
    query.goal = cmp(CompareOp::Eq, call("t"), call("u"));
    assert_refuted(&check(&query, &Limits::default()));
}

fn nominal_pair(goal: TrustVcExpr) -> Query {
    let mut query = Query::new("nominal carriers", goal);
    query.nominal_sorts = vec!["carrier".into()];
    query.symbols = vec![
        Symbol::new("x", nominal("carrier")),
        Symbol::new("y", nominal("carrier")),
    ];
    query
}

#[test]
fn nominal_carrier_equality_does_not_collapse_to_unit() {
    let x = var("x", nominal("carrier"));
    let y = var("y", nominal("carrier"));
    let same = nominal_pair(cmp(CompareOp::Eq, x.clone(), x));
    assert_proved(&check(&same, &Limits::default()));
    let arbitrary = nominal_pair(cmp(CompareOp::Eq, var("x", nominal("carrier")), y));
    assert_refuted(&check(&arbitrary, &Limits::default()));
}

#[test]
fn nominal_carriers_support_only_typed_uf_congruence() {
    // Numeric, same-carrier and distinct-carrier codomains must all retain
    // the declared sort. No carrier interpretation is a singleton/default.
    for result in [int(), nominal("carrier"), nominal("other")] {
        let call = |arg| TrustVcExpr::FnCall {
            name: "measure".into(),
            args: vec![arg],
            return_ty: result.clone(),
        };
        let x = var("x", nominal("carrier"));
        let y = var("y", nominal("carrier"));
        let mut query = nominal_pair(cmp(CompareOp::Eq, call(x.clone()), call(y.clone())));
        query.nominal_sorts.push("other".into());
        query.functions = vec![Function {
            name: "measure".into(),
            params: vec![nominal("carrier")],
            ret: result.clone(),
        }];
        query.hypotheses = vec![hyp("same value", cmp(CompareOp::Eq, x.clone(), y.clone()))];
        assert_proved(&check(&query, &Limits::default()));
        query.hypotheses.clear();
        assert_refuted(&check(&query, &Limits::default()));
        if result == nominal("carrier") {
            query.definitions.push(Definition {
                function: "measure".into(),
                params: vec![("arg".into(), nominal("carrier"))],
                body: var("arg", nominal("carrier")),
            });
            query.goal = cmp(CompareOp::Eq, call(x.clone()), x.clone());
            assert_proved(&check(&query, &Limits::default()));
            query.goal = cmp(CompareOp::Eq, call(x.clone()), y);
            assert_refuted(&check(&query, &Limits::default()));
        } else if result == nominal("other") {
            query.goal = cmp(CompareOp::Eq, call(x.clone()), x);
            assert_error_mentions(&check(&query, &Limits::default()), "comparison between");
        }
    }
}

#[test]
fn undeclared_and_colliding_nominal_registries_are_errors() {
    let mut query = nominal_pair(tt());
    query.nominal_sorts.clear();
    assert_error_mentions(&check(&query, &Limits::default()), "registered nominal");
    query.nominal_sorts = vec!["carrier".into(), "carrier".into()];
    assert_error_mentions(&check(&query, &Limits::default()), "unique name");
    query.nominal_sorts = vec!["Int".into()];
    assert_error_mentions(&check(&query, &Limits::default()), "unique name");
}

#[test]
fn nominal_ordering_arithmetic_and_cross_sort_equality_are_errors() {
    let x = var("x", nominal("carrier"));
    let y = var("y", nominal("carrier"));
    let ordered = nominal_pair(cmp(CompareOp::Lt, x.clone(), y));
    assert_error_mentions(&check(&ordered, &Limits::default()), "ordering");
    let arithmetic = nominal_pair(cmp(
        CompareOp::Eq,
        arith(ArithOp::Add, x.clone(), lit(1)),
        lit(2),
    ));
    assert_error_mentions(&check(&arithmetic, &Limits::default()), "Nominal");
    let mut different = nominal_pair(cmp(CompareOp::Eq, x, var("z", nominal("other"))));
    different.nominal_sorts.push("other".into());
    different.symbols.push(Symbol::new("z", nominal("other")));
    assert_error_mentions(&check(&different, &Limits::default()), "comparison between");
}

#[test]
fn nominal_conditionals_preserve_identity() {
    let x = var("x", nominal("carrier"));
    let y = var("y", nominal("carrier"));
    let selected = ite(bvar("c"), x.clone(), y.clone(), nominal("carrier"));
    let mut query = nominal_pair(implies(bvar("c"), cmp(CompareOp::Eq, selected, x)));
    query.symbols.push(Symbol::new("c", boolean()));
    assert_proved(&check(&query, &Limits::default()));
    query.goal = cmp(CompareOp::Eq, var("x", nominal("carrier")), y);
    assert_refuted(&check(&query, &Limits::default()));
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

fn ivar(name: &str) -> TrustVcExpr {
    var(name, int())
}

fn bvar(name: &str) -> TrustVcExpr {
    var(name, boolean())
}

fn lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty: int() }
}

fn tt() -> TrustVcExpr {
    TrustVcExpr::BoolLit(true)
}

fn ff() -> TrustVcExpr {
    TrustVcExpr::BoolLit(false)
}

fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty: int(),
    }
}

fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn not(inner: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Not(Box::new(inner))
}

fn implies(premise: TrustVcExpr, conclusion: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Implies {
        premise: Box::new(premise),
        conclusion: Box::new(conclusion),
    }
}

fn ite(
    cond: TrustVcExpr,
    then: TrustVcExpr,
    otherwise: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(then),
        else_branch: Box::new(otherwise),
        ty,
    }
}

fn let_in(name: &str, ty: TrustVcType, value: TrustVcExpr, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Let {
        name: name.to_string(),
        ty,
        value: Box::new(value),
        body: Box::new(body),
    }
}

fn call(name: &str, args: Vec<TrustVcExpr>, ret: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: ret,
    }
}

fn hyp(label: &str, expr: TrustVcExpr) -> Hypothesis {
    Hypothesis::new(label, HypothesisSource::Assume, expr)
}

fn ints(names: &[&str]) -> Vec<Symbol> {
    names.iter().map(|name| Symbol::new(*name, int())).collect()
}

fn run(query: &Query) -> Verdict {
    check(query, &Limits::default())
}

#[track_caller]
fn assert_proved(verdict: &Verdict) {
    assert!(verdict.is_proved(), "expected Proved, got {verdict:?}");
}

#[track_caller]
fn assert_refuted(verdict: &Verdict) {
    assert!(verdict.is_refuted(), "expected Refuted, got {verdict:?}");
}

#[track_caller]
fn assert_error_mentions(verdict: &Verdict, needle: &str) {
    match verdict {
        Verdict::Error { message } => assert!(
            message.contains(needle),
            "error message {message:?} does not mention {needle:?}"
        ),
        other => panic!("expected Error mentioning {needle:?}, got {other:?}"),
    }
}

/// `x <= y && y <= z` with goal `goal`.
fn transitivity(goal: TrustVcExpr) -> Query {
    let mut query = Query::new("transitivity", goal);
    query.symbols = ints(&["x", "y", "z"]);
    query.hypotheses = vec![
        hyp("xy", cmp(CompareOp::Le, ivar("x"), ivar("y"))),
        hyp("yz", cmp(CompareOp::Le, ivar("y"), ivar("z"))),
    ];
    query
}

#[test]
fn linear_entailment_is_proved() {
    let verdict = run(&transitivity(cmp(CompareOp::Le, ivar("x"), ivar("z"))));
    assert_proved(&verdict);
}

#[test]
fn liar_strict_transitivity_is_refuted_with_a_model() {
    let verdict = run(&transitivity(cmp(CompareOp::Lt, ivar("x"), ivar("z"))));
    let Verdict::Refuted { model } = &verdict else {
        panic!("expected Refuted, got {verdict:?}");
    };
    let value = |name: &str| {
        model
            .iter()
            .find(|entry| entry.name == name)
            .map(|entry| entry.value.parse::<i128>().expect("integer model value"))
            .unwrap_or_else(|| panic!("model {model:?} has no value for {name}"))
    };
    // The model must really falsify the goal and satisfy the hypotheses.
    let (x, y, z) = (value("x"), value("y"), value("z"));
    assert!(
        x <= y && y <= z && x >= z,
        "model x={x} y={y} z={z} is not a counterexample"
    );
}

#[test]
fn proof_reports_the_hypotheses_it_used() {
    let mut query = transitivity(cmp(CompareOp::Le, ivar("x"), ivar("z")));
    query.symbols.push(Symbol::new("w", int()));
    query
        .hypotheses
        .push(hyp("unrelated", cmp(CompareOp::Eq, ivar("w"), lit(7))));
    match run(&query) {
        Verdict::Proved {
            used_hypotheses: Some(used),
        } => {
            assert!(used.contains(&"xy".to_string()), "core {used:?} misses xy");
            assert!(used.contains(&"yz".to_string()), "core {used:?} misses yz");
            let known = ["xy", "yz", "unrelated"];
            assert!(used.iter().all(|label| known.contains(&label.as_str())));
        }
        other => panic!("expected Proved with a core, got {other:?}"),
    }
}

#[test]
fn display_names_reach_the_model() {
    let mut query = Query::new("display", cmp(CompareOp::Eq, ivar("c_1"), lit(0)));
    query.symbols = vec![Symbol::with_display("c_1", int(), "c")];
    query.hypotheses = vec![hyp("pos", cmp(CompareOp::Gt, ivar("c_1"), lit(0)))];
    match run(&query) {
        Verdict::Refuted { model } => {
            assert!(
                model
                    .iter()
                    .any(|entry| entry.name == "c" && entry.symbol == "c_1"),
                "model {model:?} does not show c_1 as c"
            );
        }
        other => panic!("expected Refuted, got {other:?}"),
    }
}

#[test]
fn boolean_facts_and_their_liars() {
    let mut query = Query::new("assume_b", bvar("b"));
    query.symbols = vec![Symbol::new("b", boolean())];
    query.hypotheses = vec![hyp("b", bvar("b"))];
    assert_proved(&run(&query));

    query.hypotheses.clear();
    assert_refuted(&run(&query));

    // `(true ^ true) == false`, written as `!=`, and its liar.
    let xor = cmp(CompareOp::Ne, tt(), tt());
    assert_proved(&run(&Query::new(
        "xor",
        cmp(CompareOp::Eq, xor.clone(), ff()),
    )));
    assert_refuted(&run(&Query::new("xor_liar", cmp(CompareOp::Eq, xor, tt()))));

    // `true && false` is refuted with no symbols at all.
    assert_refuted(&run(&Query::new("and_false", and(tt(), ff()))));
}

#[test]
fn uninterpreted_function_congruence() {
    let f = Function {
        name: "f".to_string(),
        params: vec![int(), int()],
        ret: boolean(),
    };
    let goal = implies(
        cmp(CompareOp::Eq, ivar("x"), ivar("y")),
        cmp(
            CompareOp::Eq,
            call("f", vec![ivar("x"), ivar("y")], boolean()),
            call("f", vec![ivar("y"), ivar("x")], boolean()),
        ),
    );
    let mut query = Query::new("congruence", goal);
    query.symbols = ints(&["x", "y"]);
    query.functions = vec![f.clone()];
    assert_proved(&run(&query));

    // Liar: without `x == y` nothing relates the two applications.
    let liar = cmp(
        CompareOp::Eq,
        call("f", vec![ivar("x"), ivar("y")], boolean()),
        call("f", vec![ivar("y"), ivar("x")], boolean()),
    );
    let mut query = Query::new("congruence_liar", liar);
    query.symbols = ints(&["x", "y"]);
    query.functions = vec![f];
    assert_refuted(&run(&query));
}

/// basic.rs `test_spec_fn`: `f1(i, j) = i <= j`, `f2(i, j) = let x = i; let
/// y = j; x < y`, `f3(i, j) = f1(j, i)`. With `f2(a, b)` assumed, `f1(a, b)`
/// follows only when `f2`'s definition is visible.
fn spec_fn_query(goal: TrustVcExpr, reveal_f2: bool) -> Query {
    let sig = |name: &str| Function {
        name: name.to_string(),
        params: vec![int(), int()],
        ret: boolean(),
    };
    let params = vec![("i".to_string(), int()), ("j".to_string(), int())];
    let f1 = Definition {
        function: "f1".to_string(),
        params: params.clone(),
        body: cmp(CompareOp::Le, ivar("i"), ivar("j")),
    };
    let f2 = Definition {
        function: "f2".to_string(),
        params: params.clone(),
        body: let_in(
            "x",
            int(),
            ivar("i"),
            let_in(
                "y",
                int(),
                ivar("j"),
                cmp(CompareOp::Lt, ivar("x"), ivar("y")),
            ),
        ),
    };
    let f3 = Definition {
        function: "f3".to_string(),
        params,
        body: call("f1", vec![ivar("j"), ivar("i")], boolean()),
    };
    let mut query = Query::new("spec_fn", goal);
    query.symbols = ints(&["a", "b"]);
    query.functions = vec![sig("f1"), sig("f2"), sig("f3")];
    query.definitions = if reveal_f2 {
        vec![f1, f2, f3]
    } else {
        vec![f1, f3]
    };
    query.hypotheses = vec![hyp(
        "assume_f2",
        call("f2", vec![ivar("a"), ivar("b")], boolean()),
    )];
    query
}

#[test]
fn definitions_unfold_through_lets_and_calls() {
    let f1_ab = call("f1", vec![ivar("a"), ivar("b")], boolean());
    assert_proved(&run(&spec_fn_query(f1_ab.clone(), true)));

    // Hidden definition: `f2(a, b)` is an opaque fact and says nothing.
    assert_refuted(&run(&spec_fn_query(f1_ab, false)));

    // `f3(b, a) = f1(a, b)` follows through two unfoldings.
    let f3_ba = call("f3", vec![ivar("b"), ivar("a")], boolean());
    assert_proved(&run(&spec_fn_query(f3_ba, true)));

    // Liar (the FAILS line of test_spec_fn): `f3(a, b) = b <= a` does not follow.
    let f3_ab = call("f3", vec![ivar("a"), ivar("b")], boolean());
    assert_refuted(&run(&spec_fn_query(f3_ab, true)));
}

/// `fact(n) = if n <= 0 { 1 } else { n * fact(n - 1) }`.
fn fact_query(goal: TrustVcExpr, hypotheses: Vec<Hypothesis>) -> Query {
    let n = ivar("n");
    let body = ite(
        cmp(CompareOp::Le, n.clone(), lit(0)),
        lit(1),
        arith(
            ArithOp::Mul,
            n.clone(),
            call("fact", vec![arith(ArithOp::Sub, n, lit(1))], int()),
        ),
        int(),
    );
    let mut query = Query::new("fact", goal);
    query.symbols = ints(&["m"]);
    query.functions = vec![Function {
        name: "fact".to_string(),
        params: vec![int()],
        ret: int(),
    }];
    query.definitions = vec![Definition {
        function: "fact".to_string(),
        params: vec![("n".to_string(), int())],
        body,
    }];
    query.hypotheses = hypotheses;
    query
}

#[test]
fn recursive_definition_proves_ground_facts() {
    let fact3 = call("fact", vec![lit(3)], int());
    assert_proved(&run(&fact_query(cmp(CompareOp::Eq, fact3, lit(6)), vec![])));
}

#[test]
fn liar_on_a_recursive_definition_is_never_proved() {
    // Unfolding never reaches a syntactic fixpoint (the dead else-branch keeps
    // producing calls), so a satisfiable answer is not a trusted model: the
    // documented outcome is Unknown(Incompleteness), never Refuted, never
    // Proved.
    let fact3 = call("fact", vec![lit(3)], int());
    let verdict = run(&fact_query(cmp(CompareOp::Eq, fact3, lit(7)), vec![]));
    match verdict {
        Verdict::Unknown {
            category: UnknownCategory::Incompleteness,
            ..
        } => {}
        other => panic!("expected Unknown(Incompleteness), got {other:?}"),
    }

    // A symbolic claim that needs induction is likewise not decided.
    let goal = implies(
        cmp(CompareOp::Ge, ivar("m"), lit(1)),
        cmp(
            CompareOp::Ge,
            call("fact", vec![ivar("m")], int()),
            ivar("m"),
        ),
    );
    let verdict = run(&fact_query(goal, vec![]));
    assert!(
        matches!(verdict, Verdict::Unknown { .. }),
        "expected Unknown, got {verdict:?}"
    );
}

#[test]
fn euclidean_division_and_remainder() {
    let q = arith(ArithOp::Div, lit(-7), lit(2));
    let r = arith(ArithOp::Rem, lit(-7), lit(2));
    let good = and(
        cmp(CompareOp::Eq, q.clone(), lit(-4)),
        cmp(CompareOp::Eq, r, lit(1)),
    );
    assert_proved(&run(&Query::new("euclid", good)));
    // Liar: truncating division would give -3.
    assert_refuted(&run(&Query::new(
        "euclid_liar",
        cmp(CompareOp::Eq, q, lit(-3)),
    )));

    // Symbolic divisor: x / 2 * 2 <= x for every int x.
    let mut query = Query::new(
        "euclid_symbolic",
        cmp(
            CompareOp::Le,
            arith(ArithOp::Mul, arith(ArithOp::Div, ivar("x"), lit(2)), lit(2)),
            ivar("x"),
        ),
    );
    query.symbols = ints(&["x"]);
    assert_proved(&run(&query));
    query.goal = cmp(
        CompareOp::Eq,
        arith(ArithOp::Mul, arith(ArithOp::Div, ivar("x"), lit(2)), lit(2)),
        ivar("x"),
    );
    assert_refuted(&run(&query));
}

#[test]
fn nat_symbols_carry_their_lower_bound() {
    let goal = cmp(
        CompareOp::Ge,
        TrustVcExpr::Var {
            name: "n".to_string(),
            ty: TrustVcType::Nat,
        },
        TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Nat,
        },
    );
    let mut query = Query::new("nat", goal);
    query.symbols = vec![Symbol::new("n", TrustVcType::Nat)];
    assert_proved(&run(&query));

    // Liar: the same claim about an int.
    let mut query = Query::new("int_not_nat", cmp(CompareOp::Ge, ivar("n"), lit(0)));
    query.symbols = ints(&["n"]);
    assert_refuted(&run(&query));
}

#[test]
fn let_in_goal_and_nonlinear_commutation() {
    let goal = let_in(
        "t",
        int(),
        arith(ArithOp::Add, ivar("x"), lit(1)),
        cmp(CompareOp::Gt, ivar("t"), ivar("x")),
    );
    let mut query = Query::new("let_goal", goal);
    query.symbols = ints(&["x", "y"]);
    assert_proved(&run(&query));

    query.goal = cmp(
        CompareOp::Eq,
        arith(ArithOp::Mul, ivar("x"), ivar("y")),
        arith(ArithOp::Mul, ivar("y"), ivar("x")),
    );
    assert_proved(&run(&query));
    // Liar: x * y == x + y does not hold in general.
    query.goal = cmp(
        CompareOp::Eq,
        arith(ArithOp::Mul, ivar("x"), ivar("y")),
        arith(ArithOp::Add, ivar("x"), ivar("y")),
    );
    assert!(!run(&query).is_proved());
}

#[test]
fn contradictory_hypotheses_entail_anything() {
    // Entailment is the question asked; detecting vacuity is the caller's job
    // (a VC generator asks it as its own query).
    let mut query = Query::new("vacuous", ff());
    query.symbols = ints(&["x"]);
    query.hypotheses = vec![
        hyp("neg", cmp(CompareOp::Lt, ivar("x"), lit(0))),
        hyp("pos", cmp(CompareOp::Gt, ivar("x"), lit(0))),
    ];
    assert_proved(&run(&query));
    query.hypotheses.pop();
    assert_refuted(&run(&query));
}

#[test]
fn machine_integer_chain_in_math_ints() {
    // basic.rs `test_ret2` step: `ret <= a + a` for `test_ret(a, a)`, then
    // `test_ret(x, x)`, gives `x <= 4 * a`.
    let mut query = Query::new(
        "chain",
        cmp(
            CompareOp::Le,
            ivar("x2"),
            arith(ArithOp::Mul, lit(4), ivar("a")),
        ),
    );
    query.symbols = ints(&["a", "x1", "x2"]);
    query.hypotheses = vec![
        Hypothesis::new(
            "ens1",
            HypothesisSource::CalleeEnsures,
            cmp(
                CompareOp::Le,
                ivar("x1"),
                arith(ArithOp::Add, ivar("a"), ivar("a")),
            ),
        ),
        Hypothesis::new(
            "ens2",
            HypothesisSource::CalleeEnsures,
            cmp(
                CompareOp::Le,
                ivar("x2"),
                arith(ArithOp::Add, ivar("x1"), ivar("x1")),
            ),
        ),
    ];
    assert_proved(&run(&query));
    query.goal = cmp(
        CompareOp::Le,
        ivar("x2"),
        arith(ArithOp::Mul, lit(3), ivar("a")),
    );
    assert_refuted(&run(&query));
}

#[test]
fn if_then_else_values() {
    // x_1 == (if a { 1 } else { 2 }) ==> (a ==> x_1 == 1)
    let mut query = Query::new(
        "ite",
        implies(bvar("a"), cmp(CompareOp::Eq, ivar("x1"), lit(1))),
    );
    query.symbols = vec![Symbol::new("a", boolean()), Symbol::new("x1", int())];
    query.hypotheses = vec![Hypothesis::new(
        "bind",
        HypothesisSource::Binding,
        cmp(
            CompareOp::Eq,
            ivar("x1"),
            ite(bvar("a"), lit(1), lit(2), int()),
        ),
    )];
    assert_proved(&run(&query));
    query.goal = implies(not(bvar("a")), cmp(CompareOp::Eq, ivar("x1"), lit(1)));
    assert_refuted(&run(&query));
}

#[test]
fn names_are_restricted() {
    assert!(is_admitted_name("x"));
    assert!(is_admitted_name("x_2"));
    assert!(is_admitted_name("f12"));
    for bad in ["", "X", "_x", "x_", "x__y", "1x", "x-y", "x.y"] {
        assert!(!is_admitted_name(bad), "{bad:?} must not be admitted");
    }
    let mut query = Query::new("bad_name", tt());
    query.symbols = vec![Symbol::new("x__pre", int())];
    assert_error_mentions(&run(&query), "not an admitted name");
}

#[test]
fn admission_refuses_everything_outside_the_fragment() {
    // Machine-integer symbol.
    let mut query = Query::new("u32", tt());
    query.symbols = vec![Symbol::new("x", TrustVcType::Uint { width: 32 })];
    assert_error_mentions(&run(&query), "symbol `x` has type Uint { width: 32 }");

    // Undeclared variable.
    let query = Query::new("undeclared", cmp(CompareOp::Eq, ivar("q"), lit(0)));
    assert_error_mentions(&run(&query), "not declared");

    // Variable used at the wrong type.
    let mut query = Query::new("wrong_type", bvar("x"));
    query.symbols = ints(&["x"]);
    assert_error_mentions(&run(&query), "declared MathInt");

    // Non-boolean goal.
    let mut query = Query::new("int_goal", ivar("x"));
    query.symbols = ints(&["x"]);
    assert_error_mentions(&run(&query), "goal");

    // Arithmetic at a machine type.
    let goal = cmp(
        CompareOp::Eq,
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(ivar("x")),
            right: Box::new(lit(1)),
            ty: TrustVcType::Uint { width: 8 },
        },
        lit(0),
    );
    let mut query = Query::new("u8_arith", goal);
    query.symbols = ints(&["x"]);
    assert_error_mentions(&run(&query), "queries compute in MathInt");

    // A quantifier.
    let goal = TrustVcExpr::Quantifier {
        kind: trust_vc_core::ir::QuantifierKind::Forall,
        bound_vars: vec![("i".to_string(), int())],
        body: Box::new(tt()),
        triggers: None,
        trigger_inference_mode: None,
    };
    assert_error_mentions(
        &run(&Query::new("forall", goal)),
        "not in the admitted query fragment",
    );

    // Duplicate and reserved hypothesis labels.
    let mut query = Query::new("labels", tt());
    query.hypotheses = vec![hyp("h", tt()), hyp("h", tt())];
    assert_error_mentions(&run(&query), "used twice");
    query.hypotheses = vec![hyp("def:f#0", tt())];
    assert_error_mentions(&run(&query), "reserved prefix");

    // A definition that mentions a query symbol.
    let mut query = Query::new("leaky_definition", tt());
    query.symbols = ints(&["x"]);
    query.functions = vec![Function {
        name: "g".to_string(),
        params: vec![int()],
        ret: int(),
    }];
    query.definitions = vec![Definition {
        function: "g".to_string(),
        params: vec![("i".to_string(), int())],
        body: arith(ArithOp::Add, ivar("i"), ivar("x")),
    }];
    assert_error_mentions(&run(&query), "definition of `g`");

    // Call annotated with the wrong result type.
    let mut query = Query::new("wrong_ret", call("g", vec![lit(1)], boolean()));
    query.functions = vec![Function {
        name: "g".to_string(),
        params: vec![int()],
        ret: int(),
    }];
    assert_error_mentions(&run(&query), "returns MathInt");
}
