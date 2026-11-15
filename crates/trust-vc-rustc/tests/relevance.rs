//! Where recursive spec functions unfold: only at the applications Verus's
//! Z3 instantiates on. Z3 rewrites a query before it matches (a comparison
//! of a term with itself, `a == !a` and the like fold away with their
//! terms, and top-level equations are substituted into the other
//! formulas), and it matches only relevant terms (one true disjunct, the
//! branch an `if` takes). Each program has a twin that differs from it in
//! one line.
//!
//! The programs are in `relevance/<name>.rs` and their twins in
//! `relevance/<name>.twin.rs`, from the `verus!` line on (line 1). Every
//! expected verdict, message and line is that of the reference Verus+z3
//! run on the same program. The binary needs the trustc-built
//! `verus_builtin` crates (see `common`).

mod common;

/// A run's outcome and its errors, as message prefixes and the line of their
/// first primary span.
type Expect = (&'static str, &'static [(&'static str, usize)]);

const CHECKED: Expect = ("checked", &[]);

const fn failed(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verification-failed", errors)
}

const fn rejected(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verus-rejected", errors)
}

const TERMINATION: &str = "could not prove termination";
const ASSERT: &str = "assertion failed";
const INVARIANT_BEFORE: &str = "invariant not satisfied before loop";
const PRECONDITION: &str = "precondition not satisfied";

struct Case {
    name: &'static str,
    program: &'static str,
    twin: &'static str,
    expect: Expect,
    twin_expect: Expect,
}

macro_rules! case {
    ($name:literal, $expect:expr, $twin_expect:expr) => {
        Case {
            name: $name,
            program: include_str!(concat!("relevance/", $name, ".rs")),
            twin: include_str!(concat!("relevance/", $name, ".twin.rs")),
            expect: $expect,
            twin_expect: $twin_expect,
        }
    };
}

const CASES: &[Case] = &[
    // `s(0) <= s(0)` folds to `true` with its terms, so neither `s(0)` nor
    // `s(1)` unfolds and `s(2) == 3` is out of reach; the twin asserts
    // their values.
    case!("drop_le_self", failed(&[(ASSERT, 9)]), CHECKED),
    case!("drop_requires", failed(&[(ASSERT, 10)]), CHECKED),
    case!("drop_exec", failed(&[(ASSERT, 9)]), CHECKED),
    // `s(0) >= 0 || (s(0) < 0 && s(1) >= 0) || s(1) < 0` holds by its
    // first disjunct, which leaves `s(1)` irrelevant.
    case!("drop_tautology", failed(&[(ASSERT, 9)]), CHECKED),
    // An inconsistent definition whose termination is admitted: `f(0) ==
    // !f(0)` folds to `false` before `f(0)` can unfold. In the twin `f(0)`
    // stays and unfolds into the contradiction.
    case!("incons_assume_eqneg", failed(&[(ASSERT, 9)]), CHECKED),
    case!("incons_assume_lt_self", failed(&[(ASSERT, 9)]), CHECKED),
    case!("incons_dby_eqneg", failed(&[(ASSERT, 13)]), CHECKED),
    // Termination fails; the assertion fails as well.
    case!(
        "incons_fail_eqneg",
        failed(&[(TERMINATION, 5), (ASSERT, 8)]),
        failed(&[(TERMINATION, 5)])
    ),
    // recursion.rs `lemma_not_proved_by_impossible_fun2` without its call
    // of `bad_lemma` (the twin).
    case!(
        "impossible_fun_no_call",
        failed(&[(TERMINATION, 6), (ASSERT, 16)]),
        rejected(&[("found cyclic dependency in decreases_by function", 9)])
    ),
    // A fact learnt in one branch of an `if` makes its terms relevant only
    // where that branch was taken.
    case!("branch_join", failed(&[(ASSERT, 16)]), CHECKED),
    // `b || s(1) == 1` holds by `b` where `b` is true; the twin requires
    // `!b`.
    case!("disjunct", failed(&[(ASSERT, 10)]), CHECKED),
    // `x == 0` turns `s(x) <= s(0)` into `s(0) <= s(0)`, which folds away.
    case!("propagated", failed(&[(ASSERT, 11)]), CHECKED),
    // The branch an `if` does not take is not relevant; the twin's `if`
    // has equal branches and folds to `s(1)`.
    case!("ite_branch", failed(&[(ASSERT, 10)]), CHECKED),
    // An `if` of numerals compared with a numeral folds where every branch
    // gives the same answer: `!= 3` and `<= 3` against `1` and `2`. The
    // twins compare with `1`, which leaves the condition.
    case!("itev_ne", failed(&[(ASSERT, 12)]), CHECKED),
    case!("itev_le", failed(&[(ASSERT, 12)]), CHECKED),
    // The same with an inconsistent definition: `f(1)` never unfolds into
    // `false`.
    case!("itev_ne_incons_false", failed(&[(ASSERT, 12)]), CHECKED),
    // The folding shape in a loop invariant, a callee's `ensures` and the
    // body of a non-recursive wrapper.
    case!(
        "itev_loop_inv",
        failed(&[(ASSERT, 19)]),
        failed(&[(INVARIANT_BEFORE, 12)])
    ),
    case!("itev_exec_ensures", failed(&[(ASSERT, 16)]), CHECKED),
    case!("itev_wrapper", failed(&[(ASSERT, 13)]), CHECKED),
    // A boolean `if` whose branches are its condition and its negation is
    // `true`; the twins' branches differ.
    case!("bite_self", failed(&[(ASSERT, 12)]), CHECKED),
    case!("bite_self_eq", failed(&[(ASSERT, 12)]), CHECKED),
    // In the body of a recursive spec function, reached through its
    // unfolding.
    case!("bite_rec_body", failed(&[(ASSERT, 16)]), CHECKED),
    // Equations of booleans that differ in the order of their sides or in
    // where the negation sits are one term.
    case!("beq_comm", failed(&[(ASSERT, 12)]), CHECKED),
    case!("bne_vs_eq_not", failed(&[(ASSERT, 12)]), CHECKED),
    // Z3 keeps the numeral on the right of an equation of integers, also
    // after substituting `s(0) == 0`.
    case!("eq_numeral_side", failed(&[(ASSERT, 12)]), CHECKED),
    case!(
        "propagated_eq_orientation",
        failed(&[(ASSERT, 12)]),
        CHECKED
    ),
    // Termination: the folding shape in the path to the recursive call and
    // in a lemma's `requires` leaves `m(n - 1)` alone, so `m(n - 2) <
    // m(n)` is out of reach. The second twin's `requires` holds where
    // termination does, and fails at the recursive call.
    case!(
        "termination_nat_measure",
        failed(&[(TERMINATION, 10)]),
        CHECKED
    ),
    case!(
        "termination_lemma_req",
        failed(&[(TERMINATION, 11)]),
        failed(&[(PRECONDITION, 11)])
    ),
    // Two callee `ensures` fix `s(1)`; it stays relevant, and so does
    // `s(0)` in the assertion beside them. The twin folds `s(0) <= s(0)`.
    case!("pinned_twice", CHECKED, failed(&[(ASSERT, 16)])),
    // Facts from one branch of an `if` do not hide the terms of an
    // assertion after the join; the twin leaves `s(0)` out.
    case!("guarded_join", CHECKED, failed(&[(ASSERT, 15)])),
    // Z3 turns a fact into `x == 1` with a rule the analysis lacks and
    // substitutes it: `s(x) == s(1)` folds and `s(1)` is gone. A boolean
    // `if` whose condition is one of its branches is a conjunction or a
    // disjunction; an `if` with some numeral leaves compared with a numeral
    // is compared leaf by leaf. Each twin's fact leaves `x` open, and
    // `s(1)` relevant.
    case!(
        "subst_ite_partial_numeral",
        failed(&[(ASSERT, 13)]),
        CHECKED
    ),
    case!("subst_ite_numeral_leaf", failed(&[(ASSERT, 13)]), CHECKED),
    case!("subst_ite_self_branch", failed(&[(ASSERT, 13)]), CHECKED),
    case!("subst_ite_self_assert_by", failed(&[(ASSERT, 11)]), CHECKED),
    case!(
        "subst_ite_self_incons_false",
        failed(&[(ASSERT, 13)]),
        CHECKED
    ),
    case!("subst_literal_requires", failed(&[(ASSERT, 13)]), CHECKED),
    case!(
        "subst_literal_exec_assume",
        failed(&[(ASSERT, 14)]),
        CHECKED
    ),
    case!("subst_exec_requires", failed(&[(ASSERT, 13)]), CHECKED),
    case!("subst_loop_invariant", failed(&[(ASSERT, 20)]), CHECKED),
    case!("subst_callee_ensures", failed(&[(ASSERT, 19)]), CHECKED),
    case!("subst_nested_call", failed(&[(ASSERT, 14)]), CHECKED),
    // The same through an instance: Z3 instantiates `w(1)` after the
    // substitution, a non-recursive wrapper or a recursive body alike.
    case!("subst_wrapper_body", failed(&[(ASSERT, 14)]), CHECKED),
    case!(
        "subst_wrapper_incons_false",
        failed(&[(ASSERT, 14)]),
        CHECKED
    ),
    case!("subst_rec_body", failed(&[(ASSERT, 18)]), CHECKED),
    case!(
        "subst_wrapper_in_rec_body",
        failed(&[(ASSERT, 19)]),
        CHECKED
    ),
    // Z3 instantiates at the representatives of its classes: where it has
    // split `x == 1` before it instantiates `r(x)`'s body, the body is
    // built at `1` and `s(1) == s(1)` folds. The twins fix `x` to 2.
    case!("split_rec_body", failed(&[(ASSERT, 18)]), CHECKED),
    case!("split_rec_body_le", failed(&[(ASSERT, 18)]), CHECKED),
    // Z3 makes the definitions' instances one at a time: `v(x)`'s instance
    // merges `x` with 1 before `w(x)`'s is built, at `1`, where `s(1) ==
    // s(1)` folds. The merge comes from `v(x)`, or `u(x) == 1` with `u` the
    // identity, in `requires`, exec `requires`, an `if` condition or a loop
    // invariant, and the wrapper sits there or in a callee's `ensures`;
    // with two arguments, `veq(x, y)` makes `f(x) == f(y)` one term, and
    // the admitted `f(i) == !f(i)` never gives `false`. Each twin leaves `x`
    // open.
    case!("early_def_merge", failed(&[(ASSERT, 22)]), CHECKED),
    case!("early_def_order_vw", failed(&[(ASSERT, 17)]), CHECKED),
    case!("early_def_merge_identity", failed(&[(ASSERT, 37)]), CHECKED),
    case!("early_def_merge_exec", failed(&[(ASSERT, 36)]), CHECKED),
    case!("early_def_merge_ensures", failed(&[(ASSERT, 57)]), CHECKED),
    case!("early_def_merge_if", failed(&[(ASSERT, 37)]), CHECKED),
    case!("early_def_merge_loop", failed(&[(ASSERT, 42)]), CHECKED),
    case!("early_def_merge_false", failed(&[(ASSERT, 18)]), CHECKED),
    case!(
        "early_def_merge_pair_false",
        failed(&[(ASSERT, 15)]),
        CHECKED
    ),
    // Before `w(x)`'s instance Z3 has also instantiated Verus's arithmetic
    // (`x + 1 == 2`, `x - 1 == 0`, `2 * x == 2` or `-x + 2 == 1` makes `x`
    // 1, and so does an `if` of sums whose condition holds), in `requires`,
    // a definition's body (opaque and revealed too), a lemma's `ensures`,
    // an `assume`, exec `requires`, a loop invariant and the negated
    // assertion, and at the argument `x * 1`; with two arguments
    // `wf2(x, y)` holds `f(x) == f(y)` as one term and the admitted
    // `f(i) == !f(i)` never gives `false`. It has also made the instances
    // of the definitions in the wrapper's argument: `u2(x, 1)` is 1, and so
    // is `u(x)` with `x == 1`, in `requires` or a lemma's `ensures`. Each
    // twin leaves `x` open.
    case!("early_arith_req", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_arith_def", failed(&[(ASSERT, 17)]), CHECKED),
    case!(
        "early_arith_opaque_reveal",
        failed(&[(ASSERT, 19)]),
        CHECKED
    ),
    case!("early_arith_lemma", failed(&[(ASSERT, 21)]), CHECKED),
    case!("early_arith_mul_assume", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_arith_exec_req", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_arith_loop_inv", failed(&[(ASSERT, 24)]), CHECKED),
    case!("early_arith_false_pair", failed(&[(ASSERT, 15)]), CHECKED),
    case!("early_arith_neg", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_arith_ite", failed(&[(ASSERT, 17)]), CHECKED),
    case!("early_arith_goal", failed(&[(ASSERT, 15)]), CHECKED),
    case!("early_arith_arg", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_defarg_u2", failed(&[(ASSERT, 16)]), CHECKED),
    case!("early_defarg_req", failed(&[(ASSERT, 20)]), CHECKED),
    case!("early_defarg_lemma", failed(&[(ASSERT, 22)]), CHECKED),
    // A callee with `requires` has its `ensures` instance made where the
    // precondition holds, after Z3 has split `x == 1 || x == 2`. The
    // twins call a lemma without `requires` (whose instance comes before
    // the split), leave `x` apart from 1, or drop the callee's `requires`.
    case!("callee_ens_split", failed(&[(ASSERT, 31)]), CHECKED),
    case!("callee_ens_split_if", failed(&[(ASSERT, 33)]), CHECKED),
    case!("callee_ens_def_merge", failed(&[(ASSERT, 22)]), CHECKED),
    case!(
        "callee_ens_def_merge_exec",
        failed(&[(ASSERT, 22)]),
        CHECKED
    ),
    // Whatever follows an assertion sits behind its split: a wrapper
    // assumed there, or a callee's `ensures`, is instantiated after `x`
    // may be 1. The twins assume the first fact instead of asserting it.
    case!("after_assert_wrapper", failed(&[(ASSERT, 26)]), CHECKED),
    case!("after_assert_callee_ens", failed(&[(ASSERT, 26)]), CHECKED),
];

/// The number of lines in which two programs differ.
fn differing_lines(a: &str, b: &str) -> usize {
    let (a, b): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if a.len() != b.len() {
        return usize::MAX;
    }
    a.iter().zip(&b).filter(|(x, y)| x != y).count()
}

fn check(name: &str, program: &str, (outcome, want): Expect) -> Vec<String> {
    let run = common::run(name, program, &[]);
    let mut problems = Vec::new();
    if run.outcome() != outcome {
        problems.push(format!(
            "{name}: outcome {} instead of {outcome}",
            run.outcome()
        ));
    }
    let errors: Vec<(String, usize)> = run
        .errors()
        .iter()
        .map(|d| {
            (
                d.message.clone(),
                d.primary_lines.first().copied().unwrap_or(0),
            )
        })
        .collect();
    let matches = errors.len() == want.len()
        && errors
            .iter()
            .zip(want)
            .all(|((message, line), (prefix, want_line))| {
                message.starts_with(prefix) && line == want_line
            });
    if !matches {
        problems.push(format!("{name}: errors {errors:?} instead of {want:?}"));
    }
    if !run.raw.is_empty() {
        problems.push(format!("{name}: non-JSON stderr {:?}", run.raw));
    }
    if outcome == "checked" && run.exit != 0 {
        problems.push(format!("{name}: exit {} for a checked run", run.exit));
    }
    problems
}

#[test]
fn relevance_and_its_twins() {
    let mut problems = Vec::new();
    for case in CASES {
        assert_eq!(
            differing_lines(case.program, case.twin),
            1,
            "{}: the twin is not a one-line change",
            case.name
        );
        problems.extend(check(case.name, case.program, case.expect));
        let twin = format!("{}__twin", case.name);
        problems.extend(check(&twin, case.twin, case.twin_expect));
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
