//! Component controls over actual Context/Tables and the production matcher.
//! These are unrun source controls, not native ownership/qualification tokens.
use super::super::closed_templates::Vocabulary;
use super::super::expr::{Reads, Tr};
use super::super::query::{Hypothesis, Query};
use super::super::spec;
use super::super::val::Ctx;
use super::*;
use crate::{CastKind, Expr, ExprKind, IntRange, LocalId, Place, SpanId, Ty};

fn source() -> crate::VcCrate {
    let mut source = super::super::closed_templates::tests::source();
    source.fns.remove(0); // actual nongeneric uninterpreted int -> bool declaration
    assert!(crate::check_crate(&source).is_empty());
    source
}
fn arith(op: ArithOp, a: Term, b: Term) -> Term {
    Term::Arith(op, Box::new(a), Box::new(b))
}
fn clip(value: Term) -> TriggerPattern {
    TriggerPattern::clipped(spec::clip_pattern(IntRange::U(8), value).unwrap())
}
fn index<'a>(items: &'a [Item]) -> TriggerIndex<'a, 'a> {
    let mut out = TriggerIndex::default();
    for item in items {
        match &item.0 {
            Term::Call { name, .. } => {
                out.calls.entry(name).or_default().push(item);
            }
            Term::Arith(op, ..) => {
                out.arithmetic.entry(*op).or_default().push(item);
            }
            Term::Ite(..)
                if spec::clip_fallback(&item.0, IntRange::U(8), &mut |_| true).is_some() =>
            {
                out.clips.entry(IntRange::U(8)).or_default().push(item);
            }
            _ => {}
        }
    }
    out
}

#[test]
fn the_actual_cast_trigger_retains_its_whole_clip_ast_and_source_domain() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let at = SpanId(0);
    let x = Expr::read(Place::local(LocalId(77)), Ty::Int(IntRange::U(8)), at);
    let integer_x = Expr::new(
        Ty::int(),
        at,
        ExprKind::Cast {
            arg: Box::new(x.clone()),
            kind: CastKind::Exact,
        },
    );
    let add = Expr::binary(
        crate::BinOp::Add,
        integer_x,
        Expr::int_lit(1, Ty::int(), at),
        Ty::int(),
        at,
    );
    let cast = Expr::new(
        Ty::Int(IntRange::U(8)),
        at,
        ExprKind::Cast {
            arg: Box::new(add),
            kind: CastKind::As,
        },
    );
    let condition = Expr::binary(
        crate::BinOp::Eq,
        x,
        Expr::int_lit(0, Ty::Int(IntRange::U(8)), at),
        Ty::Bool,
        at,
    );
    let quantifier = Expr::new(
        Ty::Bool,
        at,
        ExprKind::Quant {
            kind: QuantKind::Forall,
            vars: vec![(LocalId(77), Ty::Int(IntRange::U(8)))],
            triggers: vec![vec![cast]],
            body: Box::new(condition),
        },
    );
    let reads = Reads::default();
    assert!(Tr::new(&ctx, &tables.sigs, &tables.functions, &reads)
        .bool(&quantifier)
        .is_ok());
    let registry = ctx.quants.borrow();
    let template = registry.quants.last().unwrap();
    assert_eq!(
        template.triggers[0][0].head(),
        TriggerHead::Clip(IntRange::U(8))
    );
    assert!(matches!(template.triggers[0][0].term(), Term::Ite(..)));
    assert!(
        spec::clip_fallback(template.triggers[0][0].term(), IntRange::U(8), &mut |_| {
            true
        })
        .is_some()
    );
    assert_eq!(
        super::at(&template.body, &[], &[Term::Int(-1)], &[], &[Sort::Int]),
        Some(Term::Bool(true)),
        "negative SMT Int stays outside the u8 source quantifier; admission adds no domain fact"
    );
}

#[test]
fn clip_matching_checks_every_branch_opcode_sort_and_binding_condition() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let pattern = clip(arith(
        ArithOp::Add,
        Term::var("qx0", Sort::Int),
        Term::Int(1),
    ));
    let operand = Term::var("actual", Sort::Int);
    let good = spec::clip(
        IntRange::U(8),
        arith(ArithOp::Add, operand.clone(), Term::Int(1)),
    );
    let condition = Term::var("material", Sort::Bool);
    let items = vec![(good.clone(), condition.clone())];
    let found = bindings(
        std::slice::from_ref(&pattern),
        &index(&items),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true,
    );
    assert_eq!(found, vec![(vec![operand.clone()], vec![condition])]);
    let wrong_op = vec![(
        spec::clip(
            IntRange::U(8),
            arith(ArithOp::Sub, operand.clone(), Term::Int(1)),
        ),
        Term::Bool(true),
    )];
    assert!(bindings(
        std::slice::from_ref(&pattern),
        &index(&wrong_op),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    )
    .is_empty());
    let wrong_sort = vec![(good, Term::Bool(true))];
    assert!(bindings(
        std::slice::from_ref(&pattern),
        &index(&wrong_sort),
        &[Sort::Bool],
        &vocabulary,
        &registry,
        &mut |_| true
    )
    .is_empty());
    assert!(bindings(
        &[pattern],
        &index(&items),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| false
    )
    .is_empty());
}

#[test]
fn arithmetic_and_call_names_never_share_a_trigger_namespace() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let pattern = TriggerPattern::application(arith(
        ArithOp::Add,
        Term::var("qx0", Sort::Int),
        Term::Int(1),
    ))
    .unwrap();
    let name = tables.sigs[&source.fns[0].id].outputs[0].name.clone();
    let items = vec![
        (
            Term::call(name, vec![Term::Int(7)], Sort::Bool),
            Term::Bool(true),
        ),
        (
            arith(ArithOp::Sub, Term::Int(7), Term::Int(1)),
            Term::Bool(true),
        ),
    ];
    assert!(bindings(
        &[pattern],
        &index(&items),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    )
    .is_empty());
    assert!(
        TriggerPattern::application(arith(ArithOp::Add, Term::Bool(true), Term::Int(1))).is_none()
    );
    assert!(TriggerPattern::application(arith(
        ArithOp::Add,
        Term::var("opaque", Sort::Nominal(0)),
        Term::Int(1)
    ))
    .is_none());
}

#[test]
fn arithmetic_binding_products_share_the_original_whole_vector_and_work_limits() {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |_| true).unwrap();
    let registry = Registry::default();
    let items: Vec<_> = (0..250)
        .map(|n| {
            (
                arith(ArithOp::Add, Term::Int(n), Term::Int(1)),
                Term::Bool(true),
            )
        })
        .collect();
    let patterns = [0, 1].map(|i| {
        TriggerPattern::application(arith(
            ArithOp::Add,
            Term::var(format!("qx{i}"), Sort::Int),
            Term::Int(1),
        ))
        .unwrap()
    });
    assert_eq!(
        bindings(
            &patterns,
            &index(&items),
            &[Sort::Int, Sort::Int],
            &vocabulary,
            &registry,
            &mut |_| true
        )
        .len(),
        MAX_BINDINGS
    );
    let mut left = 3usize;
    assert!(bindings(
        &patterns,
        &index(&items),
        &[Sort::Int, Sort::Int],
        &vocabulary,
        &registry,
        &mut |cost| match left.checked_sub(cost) {
            Some(next) => {
                left = next;
                true
            }
            None => false,
        }
    )
    .is_empty());
}

#[test]
fn arithmetic_substitution_keeps_a_negative_nat_binding_under_its_domain_premise() {
    let x = Term::var("qx0", Sort::Int);
    let body = Term::implies(x.clone().within(Some(0), None), Term::eq(x, Term::Int(0)));
    assert_eq!(
        at(&body, &[], &[Term::Int(-7)], &[], &[Sort::Int]),
        Some(Term::Bool(true))
    );
    assert!(at(&body, &[], &[Term::Bool(false)], &[], &[Sort::Int]).is_none());
}

fn clip_query(negative: bool) -> Query {
    let source = source();
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let predicate_name = tables.sigs[&source.fns[0].id].outputs[0].name.clone();
    let p = |t| Term::call(predicate_name.clone(), vec![t], Sort::Bool);
    let x = Term::var("x", Sort::Int);
    let n = Term::var("n", Sort::Int);
    let mut registry = Registry::default();
    let quantified = registry
        .quant(
            QuantKind::Forall,
            &[("x".into(), Sort::Int)],
            p(x.clone()),
            vec![vec![clip(x)]],
        )
        .unwrap();
    let constraints = vec![
        (quantified.clone(), Position::default()),
        (
            Term::Cmp(
                super::super::term::CmpOp::Lt,
                Box::new(Term::Int(255)),
                Box::new(n.clone()),
            ),
            Position::default(),
        ),
        (
            Term::Cmp(
                super::super::term::CmpOp::Lt,
                Box::new(Term::Int(0)),
                Box::new(spec::clip(IntRange::U(8), n.clone())),
            ),
            Position::default(),
        ),
    ];
    let goal = if negative { p(n).not() } else { p(n) };
    let instances = instantiate(
        &ctx,
        &registry,
        &constraints,
        &(goal.clone(), Position::default()),
        &HashMap::new(),
        &tables,
    );
    assert!(
        instances.facts.iter().any(|(fact, _)| {
            let mut found = false;
            fact.for_each_call(&mut |name, args| {
                found |= name == predicate_name
                    && args.len() == 1
                    && args[0] == Term::var("n", Sort::Int);
            });
            found
        }),
        "an actual ground instance P(n), not merely the P(skolem) fact, is required"
    );
    let Term::Call { name, .. } = quantified else {
        unreachable!()
    };
    let mut functions = tables.functions.clone();
    functions.push(registry.function(&name).unwrap());
    let mut hypotheses: Vec<_> = constraints
        .into_iter()
        .map(|(term, _)| term)
        .enumerate()
        .map(|(i, term)| Hypothesis {
            label: format!("source{i}"),
            source: super::super::Source::Requires,
            term,
        })
        .collect();
    hypotheses.extend(
        instances
            .definitions
            .into_iter()
            .chain(instances.facts.into_iter().map(|(term, _)| term))
            .enumerate()
            .map(|(i, term)| Hypothesis {
                label: format!("derived_instance{i}"),
                source: super::super::Source::Axiom,
                term,
            }),
    );
    // No body/axiom is fabricated for the uninterpreted source predicate.
    assert!(functions
        .iter()
        .any(|f| f.name == predicate_name && f.params == [Sort::Int] && f.ret == Sort::Bool));
    Query {
        architectures: None,
        bitvector: None,
        nominal_types: vec![],
        symbols: std::iter::once(Symbol {
            name: "n".into(),
            sort: Sort::Int,
            display: "n".into(),
        })
        .chain(instances.symbols)
        .collect(),
        functions,
        definitions: vec![],
        hypotheses: std::mem::take(&mut hypotheses),
        goal,
    }
}

#[test]
fn actual_ordinary_clip_instantiation_is_present_with_both_positive_and_false_goals() {
    let positive = clip_query(false);
    let negative = clip_query(true);
    assert_ne!(positive.goal, negative.goal);
    assert!(positive.hypotheses.len() > 3 && negative.hypotheses.len() > 3);
}

#[cfg(feature = "solve")]
#[test]
fn ordinary_clip_trigger_positive_is_proved_by_the_real_native_query_path() {
    assert!(matches!(
        crate::solve::check(
            &clip_query(false),
            "clip_trigger_positive",
            &crate::solve::Limits::default()
        ),
        crate::solve::Verdict::Proved { .. }
    ));
}

#[cfg(feature = "solve")]
#[test]
fn ordinary_clip_trigger_false_twin_is_refuted_by_the_real_native_query_path() {
    assert!(matches!(
        crate::solve::check(
            &clip_query(true),
            "clip_trigger_false",
            &crate::solve::Limits::default()
        ),
        crate::solve::Verdict::Refuted { .. }
    ));
}

#[derive(Clone, Copy, Debug)]
enum Test8Control {
    Original,
    FalseGoal,
    UnregisteredTrigger,
    WrongClipRange,
}

fn contains_term(term: &Term, expected: &Term) -> bool {
    if term == expected {
        return true;
    }
    match term {
        Term::Not(x) | Term::Neg(x) => contains_term(x, expected),
        Term::And(xs) | Term::Or(xs) | Term::Call { args: xs, .. } => {
            xs.iter().any(|x| contains_term(x, expected))
        }
        Term::Cmp(_, a, b) | Term::Arith(_, a, b) | Term::Implies(a, b) => {
            contains_term(a, expected) || contains_term(b, expected)
        }
        Term::Ite(a, b, c, _) => {
            contains_term(a, expected) || contains_term(b, expected) || contains_term(c, expected)
        }
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => false,
    }
}

/// The actual typed and boxed source shape of upstream bitvector::test8.
/// Its two preceding BV assertions become the quantified and scalar facts;
/// the ordinary query needs a ground commutativity instance, not a Skolem fact.
fn typed_test8_query(width: u32, control: Test8Control) -> Query {
    let source = crate::VcCrate::new("actual test8 quantifier seed reduction");
    let ctx = Ctx::for_width(&source, width);
    let tables = Tables::build(&ctx, &source);
    let mut reads = Reads::default();
    let variable = Term::var("v0", Sort::Int);
    reads
        .read
        .insert(LocalId(0), super::super::val::Val::Leaf(variable.clone()));
    let at = SpanId(0);
    let ty = Ty::Int(IntRange::U(32));
    let read = |id| Expr::read(Place::local(LocalId(id)), ty.clone(), at);
    let and = |left, right| Expr::binary(crate::BinOp::BitAnd, left, right, ty.clone(), at);
    let relation = |op, left, right| Expr::binary(op, left, right, Ty::Bool, at);
    let pattern = and(read(1), read(2));
    let quantified = Expr::new(
        Ty::Bool,
        at,
        ExprKind::Quant {
            kind: crate::QuantKind::Forall,
            vars: vec![(LocalId(1), ty.clone()), (LocalId(2), ty.clone())],
            triggers: vec![vec![pattern.clone()]],
            body: Box::new(relation(crate::BinOp::Eq, pattern, and(read(2), read(1)))),
        },
    );
    let left = and(read(0), Expr::int_lit(255, ty.clone(), at));
    let right = and(Expr::int_lit(255, ty.clone(), at), read(0));
    let mut tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    let qa = tr.bool(&quantified).unwrap();
    let prior = tr
        .bool(&relation(
            crate::BinOp::Lt,
            left.clone(),
            Expr::int_lit(256, ty.clone(), at),
        ))
        .unwrap();
    let bound = if matches!(control, Test8Control::FalseGoal) {
        255
    } else {
        256
    };
    let goal = tr
        .bool(&relation(
            crate::BinOp::Lt,
            right.clone(),
            Expr::int_lit(bound, ty.clone(), at),
        ))
        .unwrap();
    let equality = tr.bool(&relation(crate::BinOp::Eq, left, right)).unwrap();
    {
        let mut registry = ctx.quants.borrow_mut();
        let template = &mut registry.quants[0];
        match control {
            Test8Control::Original | Test8Control::FalseGoal => {}
            Test8Control::UnregisteredTrigger => {
                template.triggers = vec![vec![TriggerPattern::application(Term::call(
                    "unregistered_test8_trigger",
                    vec![Term::var("qx0", Sort::Int), Term::var("qx1", Sort::Int)],
                    Sort::Int,
                ))
                .unwrap()]];
            }
            Test8Control::WrongClipRange => {
                let Term::Ite(_, operand, _, _) = template.triggers[0][0].term() else {
                    unreachable!()
                };
                template.triggers = vec![vec![TriggerPattern::clipped(
                    spec::clip_pattern(IntRange::U(8), (**operand).clone()).unwrap(),
                )]];
            }
        }
    }
    let bounds = Term::and([
        Term::le(Term::Int(0), variable.clone()),
        Term::le(variable, Term::Int(u32::MAX.into())),
    ]);
    let constraints = vec![
        (bounds, Position::default()),
        (qa.clone(), Position::default()),
        (prior, Position::default()),
    ];
    let defs = HashMap::new();
    let registry = ctx.quants.borrow();
    // Independently require seed admission and check the negative controls'
    // actual typed matcher result before any Skolem expansion can spend work.
    let mut head_work = ANALYSIS_BUDGET;
    let heads = registry
        .trigger_heads(&mut |cost| match head_work.checked_sub(cost) {
            Some(next) => {
                head_work = next;
                true
            }
            None => false,
        })
        .unwrap();
    let role = |name: &str| {
        if heads.calls.contains(name) || atom_of(name).is_some() {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    };
    let mut analysis = Analysis::new(&role, &defs, head_work)
        .with_arithmetic_triggers(&heads.arithmetic)
        .with_clip_triggers(&heads.clips)
        .with_ranges(&tables.ranged)
        .with_typings(&tables.typings)
        .with_type_context(&ctx)
        .with_prefix("rq");
    let vocabulary = Vocabulary::new(&ctx, &tables.functions, &tables.sigs, &mut |cost| {
        analysis.charge(cost).is_ok()
    })
    .unwrap();
    assert!(vocabulary.ground(&registry, &qa, &mut |cost| analysis.charge(cost).is_ok()));
    let pool = analysis
        .seeds(&constraints, &(goal.clone(), Position::default()))
        .unwrap()
        .into_items();
    assert!(
        pool.iter().any(|(term, _)| term == &qa),
        "the controls must reach an admitted quantifier atom"
    );
    let mut index = TriggerIndex::default();
    for item in &pool {
        match &item.0 {
            Term::Call { name, .. } => {
                index.calls.entry(name.as_str()).or_default().push(item);
            }
            Term::Ite(..) => {
                for range in &heads.clips {
                    if spec::clip_fallback(&item.0, *range, &mut |cost| {
                        analysis.charge(cost).is_ok()
                    })
                    .is_some()
                    {
                        index.clips.entry(*range).or_default().push(item);
                    }
                }
            }
            _ => {}
        }
    }
    let template = &registry.quants[0];
    let patterns =
        with_params(&template.triggers[0], &[], &template.params, &template.vars).unwrap();
    let matching = bindings(
        &patterns,
        &index,
        &template.vars,
        &vocabulary,
        &registry,
        &mut |cost| analysis.charge(cost).is_ok(),
    );
    let should_match = matches!(control, Test8Control::Original | Test8Control::FalseGoal);
    assert_eq!(
        !matching.is_empty(),
        should_match,
        "{control:?}, width={width}"
    );
    assert!(
        analysis.charge(1).is_ok(),
        "no negative control may pass only through budget exhaustion"
    );
    let instances = instantiate(
        &ctx,
        &registry,
        &constraints,
        &(goal.clone(), Position::default()),
        &defs,
        &tables,
    );
    assert_eq!(instances.facts.iter().any(|(fact, _)| contains_term(fact, &equality)), should_match,
        "a concrete commutativity instance must survive the complete pipeline: {control:?}, width={width}");
    assert!(
        !instances.facts.is_empty(),
        "a rejected trigger still retains the ordinary Skolem polarity fact"
    );
    let mut functions = tables.functions.clone();
    functions.extend(ctx.type_functions());
    let Term::Call { name, .. } = qa else {
        unreachable!()
    };
    functions.push(registry.function(&name).unwrap());
    let mut hypotheses: Vec<_> = constraints
        .into_iter()
        .enumerate()
        .map(|(i, (term, _))| Hypothesis {
            label: format!("source{i}"),
            source: super::super::Source::Assert,
            term,
        })
        .collect();
    hypotheses.extend(
        instances
            .definitions
            .into_iter()
            .chain(instances.facts.into_iter().map(|(term, _)| term))
            .enumerate()
            .map(|(i, term)| Hypothesis {
                label: format!("derived_instance{i}"),
                source: super::super::Source::Axiom,
                term,
            }),
    );
    Query {
        architectures: None,
        bitvector: None,
        nominal_types: vec![],
        symbols: std::iter::once(Symbol {
            name: "v0".into(),
            sort: Sort::Int,
            display: "b".into(),
        })
        .chain(instances.symbols)
        .collect(),
        functions,
        definitions: vec![],
        hypotheses,
        goal,
    }
}

#[test]
fn typed_test8_ground_instance_survives_with_positive_and_false_goals() {
    for width in [32, 64] {
        typed_test8_query(width, Test8Control::Original);
        typed_test8_query(width, Test8Control::FalseGoal);
    }
}

#[test]
fn typed_test8_unregistered_and_wrong_range_triggers_do_not_instantiate() {
    for width in [32, 64] {
        typed_test8_query(width, Test8Control::UnregisteredTrigger);
        typed_test8_query(width, Test8Control::WrongClipRange);
    }
}

#[cfg(feature = "solve")]
#[test]
fn typed_test8_positive_and_false_twin_use_the_actual_solver() {
    for width in [32, 64] {
        let query = typed_test8_query(width, Test8Control::Original);
        let positive = crate::solve::check(
            &query,
            "typed_test8_positive",
            &crate::solve::Limits::default(),
        );
        assert!(
            matches!(positive, crate::solve::Verdict::Proved { .. }),
            "{positive:?}\n{query:#?}"
        );
        assert!(matches!(
            crate::solve::check(
                &typed_test8_query(width, Test8Control::FalseGoal),
                "typed_test8_false",
                &crate::solve::Limits::default()
            ),
            crate::solve::Verdict::Refuted { .. }
        ));
    }
}
