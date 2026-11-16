//! Shared fact selection/cache controls. No source/solver/native permission is
//! simulated: these are component facts consumed by the real Analysis helper.
use super::*;

fn less(a: Term, b: Term) -> Term {
    Term::Cmp(CmpOp::Lt, Box::new(a), Box::new(b))
}
fn variable(name: &str) -> Term {
    Term::var(name, Sort::Int)
}
fn paid_close(list: &[(usize, Term)], current: usize, node: &Term) -> (Vec<usize>, usize) {
    let mut left = 200_000usize;
    let found = fact_closure::close(
        list,
        current,
        node,
        &mut |cost| match left.checked_sub(cost) {
            Some(next) => {
                left = next;
                true
            }
            None => {
                left = 0;
                false
            }
        },
    )
    .unwrap();
    (found, left)
}

fn grant(left: &mut usize) -> impl FnMut(usize) -> bool + '_ {
    |cost| match left.checked_sub(cost) {
        Some(next) => {
            *left = next;
            true
        }
        None => {
            *left = 0;
            false
        }
    }
}

#[test]
fn prepared_closure_matches_the_original_fixed_point() {
    let x = variable("x");
    let y = variable("y");
    let b = Term::var("b", Sort::Bool);
    let mut terms = vec![
        Term::Bool(true),
        Term::Bool(false),
        Term::Int(0),
        Term::Int(1),
        x.clone(),
        y.clone(),
        b.clone(),
        Term::Not(Box::new(b.clone())),
        Term::Neg(Box::new(x.clone())),
        Term::And(vec![b.clone()]),
        Term::Or(vec![b.clone()]),
        Term::Implies(Box::new(b.clone()), Box::new(Term::Bool(false))),
        Term::Ite(
            Box::new(b.clone()),
            Box::new(x.clone()),
            Box::new(y.clone()),
            Sort::Int,
        ),
        Term::call("f", vec![x.clone()], Sort::Int),
        Term::call("f", vec![y.clone(), x.clone()], Sort::Bool),
        Term::call("g", vec![y.clone()], Sort::Int),
    ];
    for sort in [
        Sort::Bool,
        Sort::Int,
        Sort::Nominal(0),
        Sort::Nominal(1),
        Sort::Poly,
        Sort::TypeId,
        Sort::Decoration,
    ] {
        terms.push(Term::var("same_name", sort));
    }
    for op in [CmpOp::Eq, CmpOp::Le, CmpOp::Lt] {
        terms.push(Term::Cmp(op, Box::new(x.clone()), Box::new(y.clone())));
    }
    for op in [
        ArithOp::Add,
        ArithOp::Sub,
        ArithOp::Mul,
        ArithOp::Div,
        ArithOp::Mod,
    ] {
        terms.push(Term::Arith(op, Box::new(x.clone()), Box::new(y.clone())));
    }
    let mut comparisons = 0;
    for offset in 0..terms.len() {
        let list: Vec<_> = (0..6)
            .map(|row| (row / 2, terms[(offset + row * 7) % terms.len()].clone()))
            .collect();
        let mut left = 2_000_000;
        let prepared =
            fact_closure::Prepared::new(&list, &mut grant(&mut left), &mut |_| {}).unwrap();
        for current in [0, 1, 2, EVERY] {
            for node in &terms {
                let mut left = 2_000_000;
                let expected =
                    fact_closure::close(&list, current, node, &mut grant(&mut left)).unwrap();
                let mut left = 2_000_000;
                let actual = prepared
                    .close(current, node, &mut grant(&mut left), &mut |_| {})
                    .unwrap();
                assert_eq!(
                    actual, expected,
                    "offset={offset} current={current} node={node:?}"
                );
                comparisons += 1;
            }
        }
    }
    assert!(comparisons > 3_000);
}

#[test]
fn prepared_closure_keeps_duplicate_formula_rows_and_contexts_separate() {
    let node = variable("x");
    let list = vec![
        (0, Term::eq(node.clone(), variable("y"))),
        (0, Term::eq(variable("y"), variable("z"))),
        (1, Term::eq(variable("z"), variable("w"))),
        (2, Term::eq(variable("separate"), Term::Int(0))),
    ];
    let mut left = 200_000;
    let prepared = fact_closure::Prepared::new(&list, &mut grant(&mut left), &mut |_| {}).unwrap();
    assert!(prepared
        .close(0, &node, &mut grant(&mut left), &mut |_| {})
        .unwrap()
        .is_empty());
    assert_eq!(
        prepared
            .close(EVERY, &node, &mut grant(&mut left), &mut |_| {})
            .unwrap(),
        vec![0, 1, 2]
    );
    let defs = HashMap::new();
    let role = |_: &str| CallRole::Other;
    let mut analysis = Analysis::new(&role, &defs, 200_000);
    analysis.facts = list[..2].to_vec();
    analysis.current = Some(99);
    assert_eq!(analysis.relevant_facts(&node).unwrap(), vec![0, 1]);
    analysis.every = Some(list);
    analysis.inlined = true;
    assert_eq!(analysis.relevant_facts(&node).unwrap(), vec![0, 1, 2]);
    assert!(analysis.fact_indices.iter().all(Option::is_some));
    analysis.inlined = false;
    assert_eq!(analysis.relevant_facts(&node).unwrap(), vec![0, 1]);
}

#[test]
fn prepared_closure_refuses_unpaid_input_and_output_work() {
    let list = [(0, Term::eq(variable("x"), variable("y")))];
    for mut left in [0, 1, 16] {
        assert!(fact_closure::Prepared::new(&list, &mut grant(&mut left), &mut |_| {}).is_err());
    }
    let mut left = 200_000;
    let prepared = fact_closure::Prepared::new(&list, &mut grant(&mut left), &mut |_| {}).unwrap();
    // Deny the next paid operation after visiting a real adjacency row.
    // A partially traversed index must never return a partial selection.
    let visited = std::cell::Cell::new(false);
    let mut left = 200_000usize;
    let denied = prepared.close(
        EVERY,
        &variable("x"),
        &mut |cost| {
            if visited.get() {
                return false;
            }
            match left.checked_sub(cost) {
                Some(next) => {
                    left = next;
                    true
                }
                None => false,
            }
        },
        &mut |event| {
            if matches!(event, fact_closure::Event::FactRow) {
                visited.set(true);
            }
        },
    );
    assert!(visited.get() && denied.is_err());
    for mut left in [0, 1, 16] {
        assert!(prepared
            .close(EVERY, &variable("x"), &mut grant(&mut left), &mut |_| {})
            .is_err());
    }
    let long = [(0, variable(&"long_name".repeat(10_000)))];
    let mut left = 200_000;
    assert!(fact_closure::Prepared::new(&long, &mut grant(&mut left), &mut |_| {}).is_err());
    let mut deep = Term::var("deep", Sort::Bool);
    for _ in 0..260 {
        deep = Term::Not(Box::new(deep));
    }
    let mut left = 200_000;
    assert!(prepared
        .close(EVERY, &deep, &mut grant(&mut left), &mut |_| {})
        .is_err());
}

#[test]
fn shared_closure_reaches_a_fixed_point_and_keeps_disjoint_facts_out() {
    // Deliberate order: the y/z bridge is later than the z/w fact, so the
    // fixed point needs a second scanning pass. A literal never joins classes.
    let own = less(variable("x"), variable("y"));
    let list = vec![
        (0, own.clone()),
        (1, less(variable("z"), variable("w"))),
        (2, less(variable("y"), variable("z"))),
        (3, less(variable("separate"), Term::Int(0))),
    ];
    let (found, left) = paid_close(&list, 0, &own);
    assert_eq!(found, [1, 2]);
    assert!(left < 200_000);
    let call = |argument: &str| Term::call("actual_function", vec![variable(argument)], Sort::Int);
    let root = less(call("first"), variable("a"));
    let list = vec![
        (0, root.clone()),
        (1, less(call("second"), variable("b"))),
        (2, less(variable("b"), variable("c"))),
        (3, less(variable("unrelated"), Term::Int(0))),
    ];
    assert_eq!(
        paid_close(&list, 0, &root).0,
        [1, 2],
        "the existing actual function-name edge is retained"
    );
}

#[test]
fn cached_fact_indices_still_pay_the_structural_key_and_owned_result_copy() {
    let defs = HashMap::new();
    let role = |_: &str| CallRole::Other;
    let mut analysis = Analysis::new(&role, &defs, 200_000);
    let root = less(variable("source"), variable("shared"));
    analysis.facts = vec![
        (0, root.clone()),
        (1, less(variable("shared"), variable("value"))),
    ];
    analysis.current = Some(0);
    let first = analysis.relevant_facts(&root).unwrap();
    assert_eq!(first, [1]);
    assert_eq!(analysis.fact_closure_calls, 1);
    let after_first = analysis.budget;
    assert_eq!(analysis.relevant_facts(&root).unwrap(), first);
    assert_eq!(
        analysis.fact_closure_calls, 1,
        "the second lookup uses the same scoped cache"
    );
    assert_eq!(analysis.fact_closure_cache_hits, 1);
    assert!(
        analysis.budget < after_first,
        "a cache hit still charges key/hash/equality and Vec clone"
    );
    let saved_cache_len = analysis.relevant.len();
    analysis.budget = 0; // hold the ORIGINAL caller grant, no replacement meter
    assert!(analysis.relevant_facts(&root).is_err());
    assert_eq!(analysis.budget, 0);
    assert_eq!(analysis.relevant.len(), saved_cache_len);
    assert_eq!(
        analysis.fact_closure_cache_hits, 1,
        "denied key admission cannot read/copy a cached result"
    );
}

#[test]
fn cache_growth_admits_existing_keys_before_reserve_can_rehash_them() {
    let mut cache = HashMap::new();
    // Fill the genuine current capacity so the production growth path is
    // necessarily taken, including a structural key with a large payload.
    cache.insert(
        less(variable(&"payload".repeat(1024)), variable("key")),
        0usize,
    );
    let capacity = cache.capacity();
    for i in 1..capacity {
        cache.insert(variable(&format!("entry{i}")), i);
    }
    assert_eq!(cache.len(), cache.capacity());
    let saved = (cache.len(), cache.capacity());
    let mut key_visits = 0;
    let denied = fact_closure::reserve_cache(&mut cache, &mut |_| true, &mut |_, _| {
        key_visits += 1;
        Err(TooBig)
    });
    assert!(denied.is_err() && key_visits == 1);
    assert_eq!(
        (cache.len(), cache.capacity()),
        saved,
        "a refused key census precedes reserve/allocation"
    );
    let mut key_visits = 0;
    fact_closure::reserve_cache(&mut cache, &mut |_| true, &mut |key, pay| {
        key_visits += 1;
        fact_closure::term_work(key, pay)?;
        Ok(())
    })
    .unwrap();
    assert_eq!(key_visits, saved.0);
    assert!(cache.capacity() > saved.1 && cache.len() == saved.0);
    let mut sparse = HashMap::with_capacity(4096);
    sparse.insert(variable("only_current_key"), 0usize);
    let saved = (sparse.len(), sparse.capacity());
    let mut visits = 0;
    fact_closure::reserve_cache(&mut sparse, &mut |_| false, &mut |_, _| {
        visits += 1;
        Err(TooBig)
    })
    .unwrap();
    assert_eq!(
        visits, 0,
        "a spare slot performs no bucket/payload scan or resize"
    );
    assert_eq!((sparse.len(), sparse.capacity()), saved);
}
