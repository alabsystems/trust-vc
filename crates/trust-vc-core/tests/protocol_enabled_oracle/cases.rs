// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The shapes the ENABLED soundness review cited, in the oracle's variables,
//! each with a twin of the other polarity. Their meaning is the model's, not
//! a hand-written expectation.
//!
//! The review's probes use `VARIABLES x, y, b` with `b' = 0` only to make the
//! witness non-empty, and a pair-valued `y` for R9. Here `z' = <<1, 1>>` plays
//! `b' = 0`, and the pair is `z`.

use super::ast::*;

pub struct Case {
    pub name: &'static str,
    pub module: Module,
    /// TLC gives a verdict here (logged probes): TY must answer too, not
    /// only avoid a wrong answer.
    pub must_answer: bool,
}

fn stutter() -> E {
    and(vec![
        unchanged(Var::X),
        unchanged(Var::Y),
        unchanged(Var::Z),
    ])
}

/// `x = 1, y = {}, z = <<1, 1>>`, stuttering, `Inv == inv`.
fn w(name: &'static str, defs: Vec<Def>, inv: E, must_answer: bool) -> Case {
    Case {
        name,
        module: Module {
            defs,
            init: [int_v(1), set_v(&[]), pair_v(1, 1)],
            next: stutter(),
            inv,
        },
        must_answer,
    }
}

/// `ENABLED (items /\ TypeOK')`.
fn en(items: Vec<E>) -> E {
    let mut all = items;
    all.extend(type_ok_primed());
    enabled(and(all))
}

/// From `x = 0, y = {}, z = <<1, 1>>`: `Next == x = 0 /\ x' = 1 /\ y' = y /\
/// z' = z /\ ~ENABLED inner`, `Inv == x = 0`: violated exactly when
/// `ENABLED inner` is FALSE in the initial state.
fn nested(name: &'static str, defs: Vec<Def>, inner: Vec<E>, must_answer: bool) -> Case {
    Case {
        name,
        module: Module {
            defs,
            init: [int_v(0), set_v(&[]), pair_v(1, 1)],
            next: and(vec![
                eq(x(), int(0)),
                eq(prime(x()), int(1)),
                eq(prime(y()), y()),
                eq(prime(z()), z()),
                not(en(inner)),
            ]),
            inv: eq(x(), int(0)),
        },
        must_answer,
    }
}

fn mark() -> E {
    // `b' = 0` of the review's probes: makes the witness non-empty.
    eq(prime(z()), pair(1, 1))
}

/// `F(n) == {s \in SUBSET (1..3) : x' + n \in s}`.
fn f_def() -> Def {
    def(
        "F",
        &["n"],
        filter(
            one("s"),
            subsets(),
            elem(add(prime(x()), name("n")), name("s")),
        ),
    )
}

/// `K(n) == {s \in SUBSET (1..3) : x + n \in s}`.
fn k_def() -> Def {
    def(
        "K",
        &["n"],
        filter(one("s"), subsets(), elem(add(x(), name("n")), name("s"))),
    )
}

/// `FK(k) == {s \in SUBSET {1, 2} : k \in s /\ x' \in s}`.
fn fk_def() -> Def {
    def(
        "FK",
        &["k"],
        filter(
            one("s"),
            subset(range(1, 2)),
            and(vec![
                elem(name("k"), name("s")),
                elem(prime(x()), name("s")),
            ]),
        ),
    )
}

/// `{s \in SUBSET (1..3) : x \in s}`.
fn x_filter() -> E {
    filter(one("s"), subsets(), elem(x(), name("s")))
}

pub fn all() -> Vec<Case> {
    let mut out = Vec::new();
    let two = || int(2);

    // ---- review blocker 2: a filter reading an unassigned prime ----
    // R8 / R8t: an operator-parameter filter reads x' before x' = 2.
    for (n, missing, ma) in [("R8", 2, false), ("R8t", 1, false)] {
        out.push(w(
            n,
            vec![f_def()],
            en(vec![
                mark(),
                elem(prime(y()), apply("F", vec![int(0)])),
                eq(prime(x()), two()),
                notin(int(missing), prime(y())),
            ]),
            ma,
        ));
    }
    // R2 (K(0)' read before x' = 2), and its assigned-first twin.
    out.push(w(
        "R2",
        vec![k_def()],
        en(vec![
            mark(),
            elem(prime(y()), prime(apply("K", vec![int(0)]))),
            eq(prime(x()), two()),
            notin(two(), prime(y())),
        ]),
        false,
    ));
    for (n, missing) in [("R2a", 2), ("R2at", 1)] {
        out.push(w(
            n,
            vec![k_def()],
            en(vec![
                eq(prime(x()), two()),
                elem(prime(y()), prime(apply("K", vec![int(0)]))),
                notin(int(missing), prime(y())),
            ]),
            true,
        ));
    }
    // R9 / R9t: an inline tuple-pattern filter reads x' before x' = 2.
    for (n, test) in [("R9", false), ("R9t", true)] {
        let last = eq(index(prime(z()), 1), two());
        out.push(w(
            n,
            vec![],
            en(vec![
                eq(prime(y()), set(vec![])),
                elem(
                    prime(z()),
                    filter(tup(&["a", "c"]), pairs(), eq(name("a"), prime(x()))),
                ),
                eq(prime(x()), two()),
                if test { last } else { not(last) },
            ]),
            false,
        ));
    }
    // R1 / R1t / R4 / R5: an inline filter built under a prime.
    out.push(w(
        "R1",
        vec![],
        en(vec![
            mark(),
            elem(prime(y()), prime(x_filter())),
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![int(1)])),
        ]),
        false,
    ));
    for (n, val) in [("R1t", 1), ("R1tt", 2)] {
        out.push(w(
            n,
            vec![],
            en(vec![
                mark(),
                eq(prime(x()), two()),
                elem(prime(y()), prime(x_filter())),
                eq(prime(y()), set(vec![int(val)])),
            ]),
            true,
        ));
    }
    out.push(w(
        "R4",
        vec![],
        en(vec![
            mark(),
            elem(
                prime(y()),
                prime(filter(
                    one("s"),
                    cup(subsets(), set(vec![set(vec![])])),
                    elem(x(), name("s")),
                )),
            ),
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![int(1)])),
        ]),
        false,
    ));
    out.push(w(
        "R5",
        vec![],
        forall(
            one("k"),
            set(vec![int(1)]),
            en(vec![
                mark(),
                elem(
                    prime(y()),
                    prime(filter(
                        one("s"),
                        subsets(),
                        and(vec![elem(x(), name("s")), elem(name("k"), name("s"))]),
                    )),
                ),
                eq(prime(x()), two()),
                eq(prime(y()), set(vec![int(1)])),
            ]),
        ),
        false,
    ));
    // R2 / R2nb of the principle review: FK(1) read before x' = 2, with and
    // without a caller binder named like FK's parameter.
    let r2_body = || {
        en(vec![
            mark(),
            elem(prime(y()), apply("FK", vec![int(1)])),
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![int(1)])),
        ])
    };
    out.push(w(
        "R2p",
        vec![fk_def()],
        forall(one("k"), set(vec![int(2)]), r2_body()),
        false,
    ));
    out.push(w("R2nb", vec![fk_def()], r2_body(), false));
    // The unassigned prime read outside any filter (EUnassignedPrimeRead/In).
    out.push(w(
        "EUnassignedPrimeRead",
        vec![],
        en(vec![
            mark(),
            eq(prime(y()), set(vec![add(prime(x()), int(1))])),
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![int(2)])),
        ]),
        false,
    ));
    out.push(w(
        "EUnassignedPrimeIn",
        vec![],
        en(vec![
            mark(),
            elem(prime(y()), set(vec![set(vec![prime(x())])])),
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![int(1)])),
        ]),
        false,
    ));
    for (n, val) in [("EAssignedPrimeRead", 3), ("EAssignedPrimeReadF", 2)] {
        out.push(w(
            n,
            vec![],
            en(vec![
                mark(),
                eq(prime(x()), two()),
                eq(prime(y()), set(vec![add(prime(x()), int(1))])),
                eq(prime(y()), set(vec![int(val)])),
            ]),
            true,
        ));
    }

    // ---- review blocker 1: ENABLED inside an action ----
    let s12 = || filter(one("s"), subset(range(1, 2)), elem(prime(x()), name("s")));
    for (n, missing) in [("N5", 2), ("N5t", 1)] {
        out.push(nested(
            n,
            vec![],
            vec![let_in(
                vec![def("S", &[], s12())],
                and(vec![
                    eq(prime(x()), two()),
                    elem(prime(y()), name("S")),
                    notin(int(missing), prime(y())),
                ]),
            )],
            true,
        ));
    }
    out.push(nested(
        "N3d",
        vec![],
        vec![
            eq(prime(y()), set(vec![prime(x())])),
            eq(prime(y()), set(vec![int(2)])),
        ],
        false,
    ));
    out.push(nested(
        "N3f",
        vec![],
        vec![
            eq(prime(y()), set(vec![prime(x())])),
            eq(prime(y()), set(vec![int(1)])),
            eq(prime(x()), int(0)),
        ],
        false,
    ));
    out.push(nested(
        "N6",
        vec![],
        vec![
            elem(prime(y()), s12()),
            eq(prime(x()), two()),
            notin(two(), prime(y())),
        ],
        false,
    ));
    for (n, missing) in [("N1", 2), ("N1t", 1)] {
        out.push(nested(
            n,
            vec![f_def()],
            vec![
                eq(prime(x()), two()),
                elem(prime(y()), apply("F", vec![int(0)])),
                notin(int(missing), prime(y())),
            ],
            true,
        ));
    }
    // A definition of the action, expanded inside ENABLED, reads ENABLED's
    // successor; a value bound by the action stays the value.
    for (n, by_value) in [("NL1", false), ("NL1v", true)] {
        let inner = and(vec![
            eq(prime(x()), two()),
            eq(prime(y()), set(vec![name("v")])),
            elem(int(1), prime(y())),
        ]);
        let mut items = vec![
            eq(x(), int(0)),
            eq(prime(x()), int(1)),
            eq(prime(y()), y()),
            eq(prime(z()), z()),
        ];
        let next = if by_value {
            items.push(exists(
                one("v"),
                set(vec![prime(x())]),
                not(en(vec![inner])),
            ));
            and(items)
        } else {
            items.push(not(en(vec![inner])));
            let_in(vec![def("v", &[], prime(x()))], and(items))
        };
        out.push(Case {
            name: n,
            module: Module {
                defs: vec![],
                init: [int_v(0), set_v(&[]), pair_v(1, 1)],
                next,
                inv: eq(x(), int(0)),
            },
            must_answer: true,
        });
    }

    // ---- review major: a LET-bound value primed at use ----
    for (n, missing, ma) in [("P1", 2, true), ("P1t", 1, true)] {
        out.push(w(
            n,
            vec![],
            en(vec![
                eq(prime(x()), two()),
                let_in(
                    vec![def("S", &[], x_filter())],
                    and(vec![
                        elem(prime(y()), prime(name("S"))),
                        notin(int(missing), prime(y())),
                    ]),
                ),
            ]),
            ma,
        ));
    }
    out.push(w(
        "P2",
        vec![k_def()],
        en(vec![
            eq(prime(x()), two()),
            let_in(
                vec![def("S", &[], apply("K", vec![int(0)]))],
                and(vec![
                    elem(prime(y()), prime(name("S"))),
                    notin(two(), prime(y())),
                ]),
            ),
        ]),
        true,
    ));
    // An operator that primes its parameter (`A(S) == y' \in S'`).
    for (n, missing) in [("F2", 2), ("F2t", 1)] {
        let a = def(
            "A",
            &["S"],
            and(vec![
                elem(prime(y()), prime(name("S"))),
                notin(int(missing), prime(y())),
            ]),
        );
        out.push(w(
            n,
            vec![k_def(), a.clone()],
            en(vec![
                eq(prime(x()), two()),
                apply("A", vec![apply("K", vec![int(0)])]),
            ]),
            true,
        ));
        out.push(w(
            if missing == 2 { "L1" } else { "L1t" },
            vec![a],
            en(vec![
                eq(prime(x()), two()),
                let_in(vec![def("S", &[], x_filter())], apply("A", vec![name("S")])),
            ]),
            true,
        ));
    }
    // A LET filter that reads x' built before x' = 2, read after it.
    for (n, missing) in [("LF", 2), ("LFt", 1)] {
        out.push(w(
            n,
            vec![],
            en(vec![let_in(
                vec![def("S", &[], s12())],
                and(vec![
                    eq(prime(x()), two()),
                    elem(prime(y()), name("S")),
                    notin(int(missing), prime(y())),
                ]),
            )]),
            true,
        ));
    }
    // An action-level actual read where its prime is assigned.
    for (n, val) in [("OpActual", 2), ("OpActualF", 3)] {
        out.push(w(
            n,
            vec![def(
                "Op",
                &["e"],
                and(vec![
                    eq(prime(x()), int(1)),
                    eq(prime(y()), set(vec![name("e")])),
                ]),
            )],
            en(vec![
                apply("Op", vec![modulo(add(prime(x()), int(1)), 4)]),
                eq(prime(y()), set(vec![int(val)])),
            ]),
            true,
        ));
    }

    // ---- the original filter-scope classes (captured locals, tuples) ----
    let f12 = || {
        def(
            "FS",
            &["k"],
            filter(one("s"), subset(range(1, 2)), elem(name("k"), name("s"))),
        )
    };
    for (n, arg, want) in [
        ("EOpFilterCapture", 3, vec![2]),
        ("EOpFilterCapture1", 1, vec![2]),
        ("EOpFilterCaptureT", 2, vec![2]),
    ] {
        out.push(w(
            n,
            vec![f12()],
            forall(
                one("k"),
                set(vec![int(2)]),
                en(vec![
                    elem(prime(y()), apply("FS", vec![int(arg)])),
                    eq(prime(y()), set(want.iter().map(|i| int(*i)).collect())),
                ]),
            ),
            true,
        ));
    }
    let pf = || {
        def(
            "PF",
            &["n"],
            filter(tup(&["a", "c"]), pairs(), eq(name("a"), name("n"))),
        )
    };
    for (n, want) in [("TupCapture", (2, 1)), ("TupCaptureF", (1, 1))] {
        out.push(w(
            n,
            vec![pf()],
            forall(
                one("a"),
                set(vec![int(1)]),
                en(vec![
                    elem(prime(z()), apply("PF", vec![int(2)])),
                    eq(prime(z()), pair(want.0, want.1)),
                ]),
            ),
            true,
        ));
    }
    // Nested binders: a tuple-pattern quantifier over a tuple-pattern filter
    // whose predicate reads the outer components.
    for (n, want) in [("TupNested", 2), ("TupNestedF", 1)] {
        out.push(w(
            n,
            vec![],
            en(vec![exists(
                tup(&["a", "c"]),
                pairs(),
                and(vec![
                    eq(name("a"), int(want)),
                    elem(
                        prime(z()),
                        filter(
                            tup(&["k", "n"]),
                            pairs(),
                            and(vec![eq(name("k"), name("c")), eq(name("n"), name("a"))]),
                        ),
                    ),
                    eq(index(prime(z()), 2), int(2)),
                ]),
            )]),
            true,
        ));
    }
    // A LET operator capturing an enclosing binder.
    for (n, want) in [("LetOpCapture", vec![1, 3]), ("LetOpCaptureF", vec![2])] {
        out.push(w(
            n,
            vec![],
            forall(
                one("k"),
                set(vec![int(1)]),
                en(vec![let_in(
                    vec![def(
                        "G",
                        &["n"],
                        filter(
                            one("s"),
                            subsets(),
                            and(vec![elem(name("k"), name("s")), elem(name("n"), name("s"))]),
                        ),
                    )],
                    and(vec![
                        elem(prime(y()), apply("G", vec![int(3)])),
                        eq(prime(y()), set(want.iter().map(|i| int(*i)).collect())),
                    ]),
                )]),
            ),
            true,
        ));
    }
    // A quantifier domain read against the witness.
    for (n, val) in [("ExistsDomainPrime", 2), ("ExistsDomainPrimeF", 3)] {
        out.push(w(
            n,
            vec![],
            en(vec![
                eq(prime(x()), two()),
                exists(
                    one("t"),
                    set(vec![prime(x())]),
                    eq(prime(y()), set(vec![name("t")])),
                ),
                eq(prime(y()), set(vec![int(val)])),
            ]),
            true,
        ));
    }
    out.extend(round_two());
    out
}

/// `x' = 1 \/ x' = 2`: two candidates for the same LET thunk.
fn x_branch() -> E {
    or(vec![eq(prime(x()), int(1)), eq(prime(x()), int(2))])
}

/// `(x' + 1) % 4`: an action-level actual.
fn x_next_plus_one() -> E {
    modulo(add(prime(x()), int(1)), 4)
}

/// `Init` with `x = 0`, the given `next` and `inv`.
fn module_with(
    name: &'static str,
    defs: Vec<Def>,
    init: St,
    next: E,
    inv: E,
    must_answer: bool,
) -> Case {
    Case {
        name,
        module: Module {
            defs,
            init,
            next,
            inv,
        },
        must_answer,
    }
}

/// The second review round's shapes (`reports/perf/2026-10-08-enabled-
/// scoping/round2/`), each with its TLC-logged probe named. `must_answer`
/// where TLC gives a verdict.
fn round_two() -> Vec<Case> {
    let mut out = Vec::new();
    let unchanged_yz = || and(vec![eq(prime(y()), y()), eq(prime(z()), z())]);

    // ---- blocker: a LET thunk over a binding that reads the successor ----
    // A1n / A1: `Op(p) == LET d == p IN /\ (x' = 1 \/ x' = 2) /\ d = 3`,
    // applied to `(x' + 1) % 4`: only `x' = 2` makes `d = 3`.
    let alias_op = |branch: E, test: E| {
        def(
            "Op",
            &["p"],
            let_in(vec![def("d", &[], name("p"))], and(vec![branch, test])),
        )
    };
    for (n, negated) in [("A1n", true), ("A1", false)] {
        let e = en(vec![apply("Op", vec![x_next_plus_one()]), unchanged_yz()]);
        out.push(w(
            n,
            vec![alias_op(x_branch(), eq(name("d"), int(3)))],
            if negated { not(e) } else { e },
            true,
        ));
    }
    // A5 / A6: the branch is `x' \in {1, 2}`, or `\E v \in {1, 2} : x' = v`
    // followed by `x' = 2` with `d = 2` (FALSE: `d` is then 3).
    out.push(w(
        "A5",
        vec![alias_op(
            elem(prime(x()), set(vec![int(1), int(2)])),
            eq(name("d"), int(3)),
        )],
        not(en(vec![
            apply("Op", vec![x_next_plus_one()]),
            unchanged_yz(),
        ])),
        true,
    ));
    out.push(w(
        "A6",
        vec![alias_op(
            exists(
                one("v"),
                set(vec![int(1), int(2)]),
                eq(prime(x()), name("v")),
            ),
            and(vec![eq(name("d"), int(2)), eq(prime(x()), int(2))]),
        )],
        not(en(vec![
            apply("Op", vec![x_next_plus_one()]),
            unchanged_yz(),
        ])),
        true,
    ));
    // A11: `d == F(0)` with the LET operator `F(i) == (p + i) % 4`.
    out.push(w(
        "A11",
        vec![def(
            "Op",
            &["p"],
            let_in(
                vec![
                    def("F", &["i"], modulo(add(name("p"), name("i")), 4)),
                    def("d", &[], apply("F", vec![int(0)])),
                ],
                and(vec![x_branch(), eq(name("d"), int(3))]),
            ),
        )],
        not(en(vec![
            apply("Op", vec![x_next_plus_one()]),
            unchanged_yz(),
        ])),
        true,
    ));
    // A2: the formal is an operator, bound to `LAMBDA v : (x' + v) % 4`.
    out.push(w(
        "A2",
        vec![def_ho(
            "Op",
            &[("F", 1)],
            let_in(
                vec![def("d", &[], apply("F", vec![int(1)]))],
                and(vec![x_branch(), eq(name("d"), int(3))]),
            ),
        )],
        not(en(vec![
            apply(
                "Op",
                vec![lambda(&["v"], modulo(add(prime(x()), name("v")), 4))],
            ),
            unchanged_yz(),
        ])),
        true,
    ));
    // A3: the formal of a LET operator.
    out.push(w(
        "A3",
        vec![],
        not(en(vec![
            let_in(
                vec![def(
                    "P",
                    &["p"],
                    let_in(
                        vec![def("d", &[], name("p"))],
                        and(vec![x_branch(), eq(name("d"), int(3))]),
                    ),
                )],
                apply("P", vec![x_next_plus_one()]),
            ),
            unchanged_yz(),
        ])),
        true,
    ));
    // MemoP: the false-counterexample direction, `b == p` with `p <- x'`.
    out.push(w(
        "MemoP",
        vec![def(
            "Fm",
            &["p"],
            let_in(
                vec![def("b", &[], name("p"))],
                or(vec![
                    and(vec![
                        eq(prime(x()), int(1)),
                        eq(name("b"), int(1)),
                        E::Bool(false),
                    ]),
                    and(vec![eq(prime(x()), int(2)), eq(name("b"), int(2))]),
                ]),
            ),
        )],
        en(vec![apply("Fm", vec![prime(x())]), unchanged_yz()]),
        true,
    ));
    // A7b: `ENABLED Op((x' + 1) % 4)` guards a Next step to `z = <<2, 2>>`.
    out.push(module_with(
        "A7b",
        vec![alias_op(x_branch(), eq(name("d"), int(3)))],
        [int_v(0), set_v(&[]), pair_v(1, 1)],
        or(vec![
            and(vec![
                en(vec![apply("Op", vec![x_next_plus_one()]), unchanged_yz()]),
                eq(prime(z()), pair(2, 2)),
                eq(prime(x()), x()),
                eq(prime(y()), y()),
            ]),
            and(vec![
                unchanged(Var::X),
                unchanged(Var::Y),
                unchanged(Var::Z),
            ]),
        ]),
        eq(z(), pair(1, 1)),
        true,
    ));
    // MemoNX: Next's own memo, an operator name passed to an operator
    // formal (`Op(G)`, `G(k) == (x' + k) % 4`): `z = <<2, 1>>` is reachable.
    out.push(module_with(
        "MemoNX",
        vec![
            def("G", &["k"], modulo(add(prime(x()), name("k")), 4)),
            def_ho(
                "Op",
                &[("F", 1)],
                let_in(
                    vec![def("d", &[], apply("F", vec![int(1)]))],
                    and(vec![
                        x_branch(),
                        eq(
                            prime(z()),
                            tuple(vec![add(modulo(name("d"), 2), int(1)), int(1)]),
                        ),
                    ]),
                ),
            ),
        ],
        [int_v(0), set_v(&[]), pair_v(2, 2)],
        and(vec![apply("Op", vec![name("G")]), eq(prime(y()), y())]),
        not(eq(z(), pair(2, 1))),
        true,
    ));

    // ---- a LET operator's formal primed through the operator it is
    // passed to ----
    let forward = |inner: E| {
        let_in(
            vec![
                def("Q", &["r"], eq(prime(name("r")), int(2))),
                def("P", &["q"], apply("Q", vec![name("q")])),
            ],
            inner,
        )
    };
    for (n, negated) in [("I3", true), ("I3t", false)] {
        let e = en(vec![forward(apply("P", vec![x()])), unchanged_yz()]);
        out.push(w(n, vec![], if negated { not(e) } else { e }, true));
    }
    // I3h: through an enclosing operator's LAMBDA formal.
    out.push(w(
        "I3h",
        vec![def_ho(
            "Oh",
            &[("F", 1)],
            let_in(
                vec![def("P", &["q"], apply("F", vec![name("q")]))],
                apply("P", vec![x()]),
            ),
        )],
        not(en(vec![
            apply("Oh", vec![lambda(&["v"], eq(prime(name("v")), int(2)))]),
            unchanged_yz(),
        ])),
        true,
    ));
    // I3m: module-level operators (the whole-graph summary).
    out.push(w(
        "I3m",
        vec![
            def("Q", &["r"], eq(prime(name("r")), int(2))),
            def("P", &["q"], apply("Q", vec![name("q")])),
        ],
        not(en(vec![apply("P", vec![x()]), unchanged_yz()])),
        true,
    ));

    // ---- UNCHANGED of a defined name or a nested tuple ----
    let vt = || def("VT", &[], tuple(vec![x(), y()]));
    for (n, negated) in [("U1p", false), ("U1", true)] {
        let e = en(vec![
            eq(prime(x()), modulo(add(x(), int(1)), 4)),
            unchanged_e(name("VT")),
            eq(prime(z()), z()),
        ]);
        out.push(w(n, vec![vt()], if negated { not(e) } else { e }, true));
    }
    out.push(w(
        "U3",
        vec![],
        en(vec![
            eq(prime(x()), modulo(add(x(), int(1)), 4)),
            let_in(
                vec![def("W", &[], tuple(vec![x(), y()]))],
                unchanged_e(name("W")),
            ),
            eq(prime(z()), z()),
        ]),
        true,
    ));
    out.push(w(
        "U5",
        vec![def("Rest", &[], tuple(vec![x()]))],
        en(vec![
            eq(prime(y()), set(vec![int(3)])),
            unchanged_e(tuple(vec![z(), name("Rest")])),
            eq(prime(x()), modulo(add(x(), int(1)), 4)),
        ]),
        true,
    ));
    // U7: `~ENABLED Hi` guards a Next step; `Hi` is never enabled (it moves
    // `y` and leaves `VT` unchanged), so `x = 1` is reachable.
    out.push(module_with(
        "U7",
        vec![
            vt(),
            def(
                "Hi",
                &[],
                and(vec![
                    eq(prime(y()), diff(range(1, 3), y())),
                    unchanged_e(name("VT")),
                    eq(prime(z()), z()),
                ]),
            ),
        ],
        [int_v(0), set_v(&[]), pair_v(1, 1)],
        or(vec![
            and(vec![
                not(enabled(name("Hi"))),
                eq(prime(x()), int(1)),
                eq(prime(y()), y()),
                eq(prime(z()), z()),
            ]),
            and(vec![
                unchanged(Var::X),
                unchanged(Var::Y),
                unchanged(Var::Z),
            ]),
        ]),
        eq(x(), int(0)),
        true,
    ));
    // `<<A>>_e` and a negated UNCHANGED read before `e'` is assigned: TLC
    // raises; TY may raise, never contradict TLA+.
    for (n, negated) in [("C3d", true), ("C3e", false)] {
        let e = en(vec![
            angle(eq(prime(x()), x()), tuple(vec![x(), y()])),
            eq(prime(z()), z()),
        ]);
        out.push(w(n, vec![], if negated { not(e) } else { e }, false));
    }
    out.push(w(
        "B1",
        vec![],
        not(en(vec![
            eq(prime(y()), set(vec![int(1)])),
            not(unchanged(Var::X)),
            eq(prime(z()), z()),
        ])),
        false,
    ));
    out.push(w(
        "C3a",
        vec![def("B", &[], eq(prime(x()), int(0)))],
        not(en(vec![
            eq(prime(y()), set(vec![int(3)])),
            not(name("B")),
            eq(prime(x()), int(2)),
            eq(prime(z()), z()),
        ])),
        false,
    ));

    // ---- an assignment through a formal bound by name ----
    out.push(w(
        "PF",
        vec![def("Set", &["v"], eq(prime(name("v")), int(3)))],
        not(en(vec![apply("Set", vec![x()]), unchanged_yz()])),
        true,
    ));
    out.push(w(
        "H1",
        vec![def_ho(
            "Ap",
            &[("F", 1), ("v", 0)],
            apply("F", vec![name("v")]),
        )],
        not(en(vec![
            apply(
                "Ap",
                vec![lambda(&["u"], eq(prime(name("u")), int(2))), x()],
            ),
            unchanged_yz(),
        ])),
        true,
    ));
    out.push(w(
        "H2",
        vec![
            def("IsTwo", &["a"], eq(prime(name("a")), int(2))),
            def_ho(
                "ApplyLet",
                &[("F", 1), ("v", 0)],
                let_in(vec![def("u", &[], name("v"))], apply("F", vec![name("u")])),
            ),
        ],
        not(en(vec![
            apply("ApplyLet", vec![name("IsTwo"), x()]),
            unchanged_yz(),
        ])),
        true,
    ));
    for (n, negated) in [("HM1", true), ("HM1t", false)] {
        let e = en(vec![
            apply("Om", vec![lambda(&["v"], eq(prime(name("v")), int(2)))]),
            unchanged_yz(),
        ]);
        out.push(w(
            n,
            vec![def_ho(
                "Om",
                &[("F", 1)],
                let_in(
                    vec![def("d", &[], x())],
                    and(vec![eq(name("d"), int(1)), apply("F", vec![name("d")])]),
                ),
            )],
            if negated { not(e) } else { e },
            true,
        ));
    }

    // ---- a caller's LET operator must not answer for a callee's ----
    for (n, negated) in [("M4", false), ("M5", true)] {
        let act = def(
            "Act",
            &["c"],
            let_in(
                vec![def("H", &["n"], eq(prime(name("n")), name("c")))],
                apply("H", vec![x()]),
            ),
        );
        let e = en(vec![apply("Act", vec![int(2)]), unchanged_yz()]);
        out.push(w(
            n,
            vec![act],
            let_in(
                vec![def("H", &["a"], E::Bool(negated))],
                if negated {
                    not(en(vec![
                        apply("Act", vec![int(2)]),
                        unchanged_yz(),
                        eq(prime(x()), int(3)),
                    ]))
                } else {
                    e
                },
            ),
            true,
        ));
    }
    out
}
