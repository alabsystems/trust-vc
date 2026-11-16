//! Ground source facts captured from the untouched A40 summer-school e18
//! recursive Fibonacci implementation. This is ordinary Term construction,
//! preserving the actual question; it is not a query serialization interface.
use super::super::term::ArithOp;
use super::*;

fn value(index: u32) -> Term {
    Term::var(format!("v{index}"), Sort::Int)
}
fn bounded(index: u32) -> Term {
    Term::and([
        Term::le(Term::Int(0), value(index)),
        Term::le(value(index), Term::Int(18_446_744_073_709_551_615)),
    ])
}
fn guarded(term: Term) -> Term {
    Term::implies(
        Term::and([
            Term::eq(value(0), Term::Int(0)).not(),
            Term::eq(value(0), Term::Int(1)).not(),
        ]),
        term,
    )
}
fn subtract(amount: i128) -> Term {
    Term::arith(ArithOp::Sub, value(0), Term::Int(amount))
}
fn sum() -> Term {
    Term::arith(ArithOp::Add, value(5), value(8))
}
fn application(argument: Term) -> Term {
    Term::call("sf0", vec![argument], Sort::Int)
}
fn in_machine_range(term: Term) -> Term {
    Term::and([
        Term::le(Term::Int(0), term.clone()),
        Term::le(term, Term::Int(18_446_744_073_709_551_615)),
    ])
}

pub(in crate::vcgen) fn source_facts() -> (Vec<Term>, Term) {
    let witness = Term::var("sq0", Sort::Int);
    let terms = vec![
        bounded(0),                            // h1
        Term::lt(value(0), Term::Int(20)),     // h2
        Term::lt(Term::Int(1), value(0)),      // h3
        Term::call("qa1", vec![], Sort::Bool), // h4
        bounded(1),
        bounded(2),
        bounded(3),                                         // h5/h6/h7
        guarded(in_machine_range(subtract(2))),             // h13
        bounded(4),                                         // h14
        guarded(Term::eq(value(4), subtract(2))),           // h15
        bounded(5),                                         // h26
        guarded(Term::eq(application(value(4)), value(5))), // h27
        bounded(6),                                         // h28
        guarded(in_machine_range(subtract(1))),             // h43
        bounded(7),                                         // h44
        guarded(Term::eq(value(7), subtract(1))),           // h45
        bounded(8),                                         // h74
        guarded(Term::eq(application(value(7)), value(8))), // h75
        guarded(in_machine_range(sum())),                   // h99
        bounded(9),                                         // h100
        guarded(Term::eq(value(9), sum())),                 // h101
        bounded(10),                                        // h102
        Term::implies(
            Term::and([
                Term::eq(value(0), Term::Int(0)).not(),
                Term::eq(value(0), Term::Int(1)),
            ]),
            Term::eq(value(10), Term::Int(1)),
        ), // h103
        guarded(Term::eq(value(10), value(9))),             // h104
        bounded(11),                                        // h105
        Term::implies(
            Term::eq(value(0), Term::Int(0)),
            Term::eq(value(11), Term::Int(0)),
        ), // h106
        Term::implies(
            Term::eq(value(0), Term::Int(0)).not(),
            Term::eq(value(11), value(10)),
        ), // h107
        Term::implies(
            Term::call("qa1", vec![], Sort::Bool).not(),
            Term::implies(
                Term::le(Term::Int(0), witness.clone()),
                Term::implies(
                    Term::lt(witness.clone(), Term::Int(20)),
                    Term::lt(application(witness), Term::Int(7000)),
                ),
            )
            .not(),
        ), // qi108
    ];
    (terms, Term::eq(application(value(0)), value(11)))
}

pub(in crate::vcgen) fn witness_context(argument: u32, result: u32) -> (Vec<Term>, Term) {
    let definitions = HashMap::new();
    let role = |name: &str| {
        if name == "sf0" || name == "rf0" {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    };
    let (terms, conclusion) = source_facts();
    let hypotheses: Vec<_> = terms
        .into_iter()
        .map(|term| {
            (
                term,
                Position {
                    late: true,
                    gate: None,
                },
            )
        })
        .collect();
    let goal = (
        conclusion,
        Position {
            late: true,
            gate: None,
        },
    );
    let mut analysis = Analysis::new(&role, &definitions, 200_000);
    let _ = analysis.seeds(&hypotheses, &goal).unwrap();
    let member = application(value(argument));
    let node = Term::eq(member.clone(), value(result));
    let containing: Vec<_> = analysis
        .facts
        .iter()
        .filter_map(|(index, term)| {
            let mut found = false;
            term.for_each_call(&mut |name, args| {
                found |= name == "sf0" && args == [value(argument)];
            });
            found.then_some(*index)
        })
        .collect();
    assert_eq!(
        containing.len(),
        1,
        "the actual containing formula is unique"
    );
    let current = containing[0];
    analysis.current = Some(current);
    // These actual scalar arguments do not join one another's classes.
    for other in [0, 4, 7].into_iter().filter(|other| *other != argument) {
        let graph = analysis.graph(current);
        let left = graph.intern(&member);
        let right = graph.intern(&application(value(other)));
        assert_ne!(graph.find(left), graph.find(right));
        assert!(!super::super::witness::same_values(
            &[value(argument)],
            &[value(other)]
        ));
    }
    let selected = analysis.relevant_facts(&node).unwrap();
    let facts: Vec<_> = selected
        .into_iter()
        .map(|index| analysis.fact_list()[index].1.clone())
        .collect();
    // The equality being tested is the node, not an assumed fact. If it
    // were retained, holding its result local fixed would forbid variation.
    assert!(!facts.iter().any(|fact| *fact == node));
    (facts, node)
}

#[test]
fn recursive_postcondition_retains_its_definition_seed_with_all_original_facts() {
    let definitions = HashMap::new();
    let role = |name: &str| {
        if name == "sf0" || name == "rf0" {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    };
    let (terms, conclusion) = source_facts();
    let hypotheses: Vec<_> = terms
        .into_iter()
        .map(|term| {
            (
                term,
                Position {
                    late: true,
                    gate: None,
                },
            )
        })
        .collect();
    let goal = (
        conclusion,
        Position {
            late: true,
            gate: None,
        },
    );
    let mut analysis = Analysis::new(&role, &definitions, 200_000);
    let seeds = analysis.seeds(&hypotheses, &goal).unwrap().into_items();
    eprintln!(
        "e18 witness work: structural={} witness={}; seeds={seeds:?}",
        analysis.budget, analysis.witness_budget
    );
    for argument in [0, 4, 7] {
        assert!(
            seeds
                .iter()
                .any(|(call, _)| *call == application(value(argument))),
            "missing v{argument}: {seeds:?}; structural={} witness={}",
            analysis.budget,
            analysis.witness_budget
        );
    }
    for argument in [4, 7, 0] {
        let arg = value(argument);
        let body = Term::ite(
            Term::eq(arg.clone(), Term::Int(0)),
            Term::Int(0),
            Term::ite(
                Term::eq(arg.clone(), Term::Int(1)),
                Term::Int(1),
                Term::arith(
                    ArithOp::Add,
                    Term::call(
                        "rf0",
                        vec![super::super::spec::clip(
                            crate::IntRange::Nat,
                            Term::arith(ArithOp::Sub, arg.clone(), Term::Int(2)),
                        )],
                        Sort::Int,
                    ),
                    Term::call(
                        "rf0",
                        vec![super::super::spec::clip(
                            crate::IntRange::Nat,
                            Term::arith(ArithOp::Sub, arg, Term::Int(1)),
                        )],
                        Sort::Int,
                    ),
                ),
            ),
        );
        let before = analysis.budget;
        let closure_before = analysis.fact_closure_work;
        let result = analysis.body(&body);
        eprintln!(
            "e18 body v{argument}: budget={before}->{} closure_work={} ok={} closure_calls={} rows={} scans={}",
            analysis.budget,
            analysis.fact_closure_work - closure_before,
            result.is_ok(),
            analysis.fact_closure_calls,
            analysis.fact_closure_input_rows,
            analysis.fact_closure_scanned_rows
        );
        assert!(result.is_ok() && analysis.budget > 0);
    }
}
