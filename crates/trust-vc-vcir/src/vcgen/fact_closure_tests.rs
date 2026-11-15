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
