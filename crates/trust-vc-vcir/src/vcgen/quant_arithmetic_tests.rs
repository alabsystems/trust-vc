//! Component controls over actual Context/Tables and the production matcher.
//! These are unrun source controls, not native ownership/qualification tokens.
use super::super::closed_templates::Vocabulary;
use super::super::expr::{Reads, Tr};
use super::super::query::{Hypothesis, Query};
use super::super::spec;
use super::super::val::{Ctx, Val};
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
            Term::Ite(..) => {
                if spec::clip_fallback(&item.0, IntRange::U(8), &mut |_| true).is_some() {
                    out.clips.entry(IntRange::U(8)).or_default().push(item);
                }
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
        &[pattern.clone()],
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
        &[pattern.clone()],
        &index(&wrong_op),
        &[Sort::Int],
        &vocabulary,
        &registry,
        &mut |_| true
    )
    .is_empty());
    let wrong_sort = vec![(good, Term::Bool(true))];
    assert!(bindings(
        &[pattern.clone()],
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
